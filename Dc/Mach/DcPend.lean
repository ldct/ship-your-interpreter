import Dc.Mach.StateOps

/-!
# A pending datum window (M9)

dc frees a datum held inside one of its own nodes (`dc_register_set`'s
`dc_free_num (&r->value)`) and then stores the new datum over it. Between
the two the bytes no longer match any ghost: the old reference has left the
state's references, the node still holds its words.

`Pend G E W Φ` names the *view memory* `Φ M` of a machine memory `M`: `M`
with the window `W` (inside the ghost's blocks `E`, none a string's)
overwritten by bytes `Φ` fixes. The state is `DcAt S (Φ M) …` while the
machine runs on `M`. `Pend.id` is no window, so a spec over a pending state
is also the plain spec.

- `DcAt.machHeap` / `BcHeap.ofMach`: the number heap on the machine memory,
  without `E` among the raw blocks, and back.
- `DcAt.freeP`, `DcAt.outWriteP`, `DcAt.rawWriteP`, `DcAt.storeP`: the
  state ops of `StateOps` with the machine's effect.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Interp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- A byte a store of `w ∈ {4, 8}` bytes wrote depends only on the value. -/
theorem imgM_store_same (M M' : Mem) {a w : Nat} (v : BitVec 64) (hw : w = 4 ∨ w = 8) {x : Nat}
    (hx : a ≤ x ∧ x < a + w) : imgM (writeLog M [(a, w, v)]) x = imgM (writeLog M' [(a, w, v)]) x := by
  have e : imgLE (imgM (writeLog M [(a, w, v)])) a w = imgLE (imgM (writeLog M' [(a, w, v)])) a w := by
    rcases hw with rfl | rfl
    · rw [imgLE_store4_hit, imgLE_store4_hit]
    · rw [imgLE_imgM_store, imgLE_imgM_store]
  have := imgLE_inj e (x - a) (by omega)
  rwa [show a + (x - a) = x by omega] at this

/-- **A pending window** `W` inside the blocks `E` of the ghost `G`: `Φ M` is
`M` off `W`, and `Φ` fixes the bytes of `W`. -/
structure Pend (G : DcG) (E : List Blk) (W : Nat → Prop) (Φ : Mem → Mem) : Prop where
  out : ∀ M x, ¬ W x → imgM (Φ M) x = imgM M x
  fix : ∀ M M' x, W x → imgM (Φ M) x = imgM (Φ M') x
  sub : ∀ e ∈ E, e ∈ G.blocks
  win : ∀ x, W x → InBlocks E x
  nstr : ∀ e ∈ E, ∀ o ∈ G.strs, e ≠ o.hb ∧ e ≠ o.tb

/-- No window. -/
theorem Pend.id (G : DcG) : Pend G [] (fun _ => False) id where
  out _ _ _ := rfl
  fix _ _ _ h := h.elim
  sub _ h := absurd h List.not_mem_nil
  win _ h := h.elim
  nstr _ h := absurd h List.not_mem_nil

section
variable {G : DcG} {E : List Blk} {W : Nat → Prop} {Φ : Mem → Mem}

/-- A machine change off the window is the same change of the view. -/
theorem Pend.memOnly (hp : Pend G E W Φ) {P : Nat → Prop} {M M' : Mem} (hm : MemOnly P M' M) :
    MemOnly P (Φ M') (Φ M) := fun x hx => by
  by_cases hw : W x
  · exact hp.fix M' M x hw
  · rw [hp.out M' x hw, hp.out M x hw]; exact hm x hx

/-- The same, the window's bytes excepted from the change. -/
theorem Pend.memOnlyW (hp : Pend G E W Φ) {P : Nat → Prop} {M M' : Mem} (hm : MemOnly P M' M) :
    MemOnly (fun x => P x ∧ ¬ W x) (Φ M') (Φ M) := fun x hx => by
  by_cases hw : W x
  · exact hp.fix M' M x hw
  · rw [hp.out M' x hw, hp.out M x hw]; exact hm x fun h => hx ⟨h, hw⟩

/-- The window lies in the blocks of `E`, all live: apart from every other
live block. -/
theorem Pend.not_win (hp : Pend G E W Φ) {S : Nat → Prop} {Mt : Mem} {H : Heap}
    (hi : HeapInv S Mt H) (hE : ∀ e ∈ E, e ∈ H.live) {c : Blk} (hc : c ∈ H.live) (hcE : c ∉ E)
    {x : Nat} (hx : c.In x) : ¬ W x := fun hw => by
  obtain ⟨e, he, hex⟩ := hp.win x hw
  exact live_apart hi (hE e he) hc (fun h => hcE (h ▸ he)) hex hx

theorem Pend.not_alloc (hp : Pend G E W Φ) {S : Nat → Prop} {Mt : Mem} {H : Heap}
    (hi : HeapInv S Mt H) (hE : ∀ e ∈ E, e ∈ H.live) {x : Nat} (hw : W x) : ¬ AllocByte H x := by
  obtain ⟨e, he, hex⟩ := hp.win x hw
  exact live_not_alloc hi (hE e he) hex

theorem Pend.inHeap (hp : Pend G E W Φ) {S : Nat → Prop} {Mt : Mem} {H : Heap}
    (hi : HeapInv S Mt H) (hE : ∀ e ∈ E, e ∈ H.live) {x : Nat} (hw : W x) :
    heapStart ≤ x ∧ x < heapEnd := by
  obtain ⟨e, he, hex⟩ := hp.win x hw
  exact live_in_heap hi (hE e he) hex

theorem Pend.not_out (hp : Pend G E W Φ) {S : Nat → Prop} {Mt : Mem} {H : Heap}
    (hi : HeapInv S Mt H) (hE : ∀ e ∈ E, e ∈ H.live) {x : Nat} (ho : OutHeap x) : ¬ W x :=
  fun hw => ho.1 (hp.inHeap hi hE hw)

/-- A store off the window, made on the machine, is the store on the view. -/
theorem Pend.store (hp : Pend G E W Φ) (M : Mem) {a w : Nat} (v : BitVec 64) (hw : w = 4 ∨ w = 8)
    (ha : ∀ x, a ≤ x ∧ x < a + w → ¬ W x) (x : Nat) :
    imgM (Φ (writeLog M [(a, w, v)])) x = imgM (writeLog (Φ M) [(a, w, v)]) x := by
  by_cases hwx : W x
  · rw [hp.fix _ M x hwx, imgM_store_miss _ _
      (Classical.byContradiction fun hc => ha x (by omega) hwx)]
  · rw [hp.out _ x hwx]
    by_cases hx : a ≤ x ∧ x < a + w
    · exact imgM_store_same _ _ v hw hx
    · rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega), hp.out M x hwx]

/-- The raw blocks of the state but `E`, imaged at `img`. -/
def DcG.rawsOff (G : DcG) (E : List Blk) (img : Mem) : Raws :=
  ⟨G.blocks.filter (fun c => decide (c ∉ E)), img⟩

theorem DcG.rawsOff_nil (G : DcG) (img : Mem) : G.rawsOff [] img = G.raws img := by
  simp [DcG.rawsOff, DcG.raws]

theorem DcG.mem_rawsOff {G : DcG} {E : List Blk} {img : Mem} {c : Blk} :
    c ∈ (G.rawsOff E img).bs ↔ c ∈ G.blocks ∧ c ∉ E := by
  simp [DcG.rawsOff]

/-- Raw blocks added, imaged at the memory. -/
theorem BcHeap.addRaws {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S X M H F L) {bs : List Blk} (hl : ∀ b ∈ bs, b ∈ H.live)
    (ho : ∀ b ∈ bs, b ∉ F ++ objBlocks L) : BcHeap S ⟨bs ++ X.bs, M⟩ M H F L :=
  { h with
    raw :=
      ⟨fun c hc => (List.mem_append.mp hc).elim (hl c) (h.raw.live c),
        fun c hc => (List.mem_append.mp hc).elim (ho c) (h.raw.out c),
        fun _ _ _ _ => rfl⟩ }

/-- **The number heap on the machine memory**: `E` leaves the raw blocks. -/
theorem DcAt.machHeap {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {hs : List GV} {st : St} (h : DcAt S (Φ M) H F L C G hs st)
    (hp : Pend G E W Φ) : BcHeap S (G.rawsOff E (Φ M)) M H F L := by
  have hi := h.heap.heap
  have hE : ∀ e ∈ E, e ∈ H.live := fun e he => h.heap.raw.live e (hp.sub e he)
  have hb1 : BcHeap S (G.rawsOff E (Φ M)) (Φ M) H F L :=
    h.heap.subRaw (fun c hc => (DcG.mem_rawsOff.mp hc).1) fun _ _ _ _ => rfl
  refine hb1.transportOwn (fun x hx => (hp.out M x fun hw => hp.not_alloc hi hE hw hx).symm)
    (fun c hc x hx => ?_) fun j hj => (hp.out M _ fun hw => by
      have := hp.inHeap hi hE hw; simp only [bcFreeAddr, heapStart] at this; omega).symm
  have hcE : c ∉ E := by
    rcases List.mem_append.mp hc with hc | hc
    · exact fun he => h.heap.raw.out _ (hp.sub _ he) hc
    · exact (DcG.mem_rawsOff.mp hc).2
  exact (hp.out M x (hp.not_win hi hE (hb1.owned_live hc) hcE hx)).symm

/-- **Back to the view**: the machine heap over the view memory, `E` again
among the raw blocks. -/
theorem BcHeap.ofMach {S : Nat → Prop} {I M' : Mem} {H' : Heap} {F' : List Blk}
    {L' : List NumObj} (hb : BcHeap S (G.rawsOff E I) M' H' F' L') (hp : Pend G E W Φ)
    (hE : ∀ e ∈ E, e ∈ H'.live) (hEo : ∀ e ∈ E, e ∉ F' ++ objBlocks L') :
    BcHeap S (G.raws (Φ M')) (Φ M') H' F' L' := by
  have hi := hb.heap
  have hb1 : BcHeap S (G.rawsOff E I) (Φ M') H' F' L' :=
    hb.transportOwn (fun x hx => hp.out M' x fun hw => hp.not_alloc hi hE hw hx)
      (fun c hc x hx => by
        have hcE : c ∉ E := by
          rcases List.mem_append.mp hc with hc | hc
          · exact fun he => hEo _ he hc
          · exact (DcG.mem_rawsOff.mp hc).2
        exact hp.out M' x (hp.not_win hi hE (hb.owned_live hc) hcE hx))
      fun j hj => hp.out M' _ fun hw => by
        have := hp.inHeap hi hE hw; simp only [bcFreeAddr, heapStart] at this; omega
  refine (hb1.addRaws hE hEo).subRaw (fun c hc => ?_) fun _ _ _ _ => rfl
  by_cases hcE : c ∈ E
  · exact List.mem_append_left _ hcE
  · exact List.mem_append_right _ (DcG.mem_rawsOff.mpr ⟨hc, hcE⟩)

/-- Memories of equal bytes hold the same state. -/
theorem DcAt.congr {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st)
    (he : ∀ x, imgM M' x = imgM M x) : DcAt S M' H F L C G hs st :=
  h.outWrite (P := fun _ => False) (fun x _ => he x) fun _ h => h.elim

/-- The window's blocks are live and none of the number heap's. -/
theorem DcAt.pendLive {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) (hp : Pend G E W Φ) :
    (∀ e ∈ E, e ∈ H.live) ∧ ∀ e ∈ E, e ∉ F ++ objBlocks L :=
  ⟨fun e he => h.heap.raw.live e (hp.sub e he), fun e he => h.heap.raw.out e (hp.sub e he)⟩

/-- **A block outside the state freed** on the machine. -/
theorem DcAt.freeP {S : Nat → Prop} {M M' : Mem} {H H' : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {hs : List GV} {st : St} {c : Blk} {lpre lpost : List Blk}
    (h : DcAt S (Φ M) H F L C G hs st) (hp : Pend G E W Φ) (hf : DcFresh H F L G c)
    (hl : H.live = lpre ++ c :: lpost) (hfp : FreePost S M M' H H' c lpre lpost) :
    DcAt S (Φ M') H' F L C G hs st := by
  have hi := h.heap.heap
  obtain ⟨hE, hEo⟩ := h.pendLive hp
  have hcE : c ∉ E := fun he => hf.notG (hp.sub c he)
  have hno : c ∉ F ++ objBlocks L ++ (G.rawsOff E (Φ M)).bs := fun hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact hf.notNum hc
    · exact hf.notG (DcG.mem_rawsOff.mp hc).1
  have hb := (h.machHeap hp).freeRaw hl hno hfp
  have hE' : ∀ e ∈ E, e ∈ H'.live := fun e he => by
    have := hE e he; rw [hl] at this; rw [hfp.live]
    rcases List.mem_append.mp this with hm | hm
    · exact List.mem_append_left _ hm
    · rcases List.mem_cons.mp hm with e1 | hm
      · exact absurd (e1 ▸ he) hcE
      · exact List.mem_append_right _ hm
  have hm : MemOnly (AllocByte H) (Φ M') (Φ M) :=
    hp.memOnly fun x hx => hfp.frame x hx
  have hblk : ∀ a, InBlocks G.blocks a → imgM (Φ M') a = imgM (Φ M) a := fun a ha =>
    hm a (h.inBlocks_heap ha).2
  exact { h with
    heap := hb.ofMach hp hE' hEo
    view := h.view.frame hblk fun a ha => hm a (OutHeap.not_alloc hi ha.outHeap) }

/-- **Machine stores off the heap and off dc's globals** keep the state. -/
theorem DcAt.outWriteP {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {hs : List GV} {st : St} {P : Nat → Prop}
    (h : DcAt S (Φ M) H F L C G hs st) (hp : Pend G E W Φ) (hm : MemOnly P M' M)
    (hP : ∀ a, P a → OutHeap a ∧ ¬ DcGlob a) : DcAt S (Φ M') H F L C G hs st := by
  exact h.outWrite (hp.memOnly hm) hP

/-- **Machine stores into a block fresh to the state** keep the state. -/
theorem DcAt.rawWriteP {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {hs : List GV} {st : St} {b : Blk}
    (h : DcAt S (Φ M) H F L C G hs st) (hp : Pend G E W Φ) (hf : DcFresh H F L G b)
    (hm : MemOnly b.In M' M) : DcAt S (Φ M') H F L C G hs st := by
  exact h.rawWrite hf (hp.memOnly hm)

end

end Dc.Mach
