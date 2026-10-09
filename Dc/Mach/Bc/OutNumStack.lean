import Dc.Mach.Bc.OutNumSetup

/-! # `bc_out_num` in a base other than 10: the digit stack

The integer digits are pushed on a stack of `malloc (16)` cells
`[digit, next]` (`s5` the head) and popped to print them. The cells are raw
blocks beside the number heap: the heap's raws are `cells ++ X0.bs` imaged at
`Mc`, the memory where the stack was last pushed.

- `OgStk`: the cells from `p` hold the digits `ds` at `Mc`, which agrees with
  the caller's raws `X0`.
- `OgSt.outHeap`: the state through a change of heap bytes only.
- `OgSt.push`: `malloc (16)` and the cell's two stores push a digit.
- `OgSt.pop`: `free` of the head cell pops it.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The stack from `p` of `cells` holding `ds` at `Mc`, and `Mc` agreeing
with the caller's raws `X0` on their bytes. -/
structure OgStk (X0 : Raws) (Mc : Mem) (cells : List Blk) (ds : List Nat) (p : Nat) : Prop where
  cells : Cells Mc X0.bs cells ds p
  agree : ∀ b ∈ X0.bs, ∀ a, b.In a → imgM Mc a = imgM X0.img a

/-- The empty stack over the caller's raws. -/
theorem OgStk.nil (X0 : Raws) : OgStk X0 X0.img [] [] 0 := ⟨rfl, fun _ _ _ _ => rfl⟩

/-- **The state through a change of heap bytes only**, with a new heap. -/
theorem OgSt.outHeap {live S : Nat → Prop} {X X' : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M M' : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H H' : Heap} {F F' : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I)
    (hb : BcHeap S X' M' H' F' (RList hs L)) (hm : ∀ a, OutHeap a → imgM M' a = imgM M a) :
    OgSt S X' G I Mt0 M' R0 R sp W H' F' L hs os sent t := by
  on_facts cx
  have hsf := cx.cc.frame
  have hsl := hsf.lo
  exact
    { on :=
        { st.on with
          saved := st.on.saved.transport (lo := 72) (top := 176) (by decide) (by decide)
            fun a h1 _ => hm a (outHeap_of_ge (by simp only [heapEnd]; omega))
          out := fun a ha hg hf => (hm a ha).trans (st.on.out a ha hg hf) }
      heap := hb
      own := st.own
      words := st.words.transport fun o ho => by
        have := st.offs o ho
        exact ldv_congr .ld fun j hj => hm _ (outHeap_of_ge (by simp only [heapEnd]; omega))
      offs := st.offs
      nd := st.nd
      inv := cb.stab _ _ _ _ st.inv fun a hg => hm a (cb.off a hg).2.1 }

/-- **The callback** from the state: the characters grow by `c`, the heap,
the handles and their words stay. -/
theorem OgSt.call {live S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R : Nat → BitVec 64}
    {sp W d c : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t)
    (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I)
    (h10 : R 10 = BitVec.ofNat 64 c) (hc : c < 256) (h1 : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' t', Keeps cClob R' R →
      OgSt S X G I Mt0 M' R0 R' sp W H F L hs os (sent ++ [c]) t' → DWO live S Q t' (R 1) R' M') :
    DWO live S Q t (R0 12) R M := by
  on_facts cx
  have hsf := cx.cc.frame
  have hsl := hsf.lo
  exact on_call cb cx st.on (by decide) (by decide) st.heap st.inv h10 hc h1
    fun R' M' t' hk' hI' on' hb' hfr => hk R' M' t' hk'
      ⟨on', hb', st.own, st.words.transport fun o ho => by
          have := st.offs o ho
          exact ldv_congr .ld fun j hj => hfr _ (fun hg => by
            have := (cb.off _ hg).1; simp only [heapStart] at this; omega) (.inr (by omega)),
        st.offs, st.nd, hI'⟩

/-- Through register changes off `sp` and `s1`. -/
theorem OgSt.regs {S : Nat → Prop} {X : Raws} {G : Nat → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M : Mem} {R0 R R' : Nat → BitVec 64}
    {sp W : Nat} {H : Heap} {F : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent : List Nat} {t : String}
    (st : OgSt S X G I Mt0 M R0 R sp W H F L hs os sent t) {ks : List Nat} (hk : Keeps ks R' R)
    (hks : ∀ z ∈ ks, z ∈ onAll ∧ z ≠ 2 ∧ z ≠ 9 := by decide) :
    OgSt S X G I Mt0 M R0 R' sp W H F L hs os sent t :=
  ⟨st.on.regs hk hks, st.heap, st.own, st.words, st.offs, st.nd, st.inv⟩

/-- **A digit pushed**: `malloc (16)` returned the block `c`, then the cell's
digit and the old head were stored. -/
theorem OgSt.push {live S : Nat → Prop} {X0 : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M M1 Mc : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H H1 : Heap} {F : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent : List Nat} {t : String} {cells : List Blk} {ds : List Nat} {p : Nat}
    (st : OgSt S ⟨cells ++ X0.bs, Mc⟩ G I Mt0 M R0 R sp W H F L hs os sent t)
    (sk : OgStk X0 Mc cells ds p) (cx : OnCtx S R0 sp W d) (cb : CharFn live S Q (R0 12) d G I)
    {c : Blk} (hp : MallocPost S M M1 H H1 16 (BitVec.ofNat 64 c.pay))
    (hl : H1.live = c :: H.live) (hsz : 16 ≤ c.sz)
    (hal : ∀ a, c.h ≤ a → a < c.fin → AllocByte H a) (hp64 : p < 2 ^ 64) (dg : Nat) :
    OgSt S ⟨(c :: cells) ++ X0.bs,
        writeLog (writeLog M1 [(c.pay, 8, BitVec.ofNat 64 dg)]) [(c.pay + 8, 8, BitVec.ofNat 64 p)]⟩
      G I Mt0
      (writeLog (writeLog M1 [(c.pay, 8, BitVec.ofNat 64 dg)]) [(c.pay + 8, 8, BitVec.ofNat 64 p)])
      R0 R sp W H1 F L hs os sent t ∧
    OgStk X0
      (writeLog (writeLog M1 [(c.pay, 8, BitVec.ofNat 64 dg)]) [(c.pay + 8, 8, BitVec.ofNat 64 p)])
      (c :: cells) (dg :: ds) c.pay := by
  have hb1 := st.heap.malloc hp
  have hcl : c ∈ H1.live := by rw [hl]; exact List.mem_cons_self
  have hfr := st.heap.fresh_not_owned (b := c) (by omega) hal
  have fbb := hp.inv.blk (List.mem_append_right _ hcl)
  have hblo : 2147603920 ≤ c.h := fbb.lo
  have hbhi : c.fin ≤ 2273312768 := Nat.le_trans fbb.fin fbb.top
  have hbp : c.pay = c.h + 16 := rfl
  have hbf : c.fin = c.h + 16 + c.sz := rfl
  -- the two stores change only the cell's bytes
  have hmo : MemOnly c.In
      (writeLog (writeLog M1 [(c.pay, 8, BitVec.ofNat 64 dg)]) [(c.pay + 8, 8, BitVec.ofNat 64 p)])
      M1 := fun a ha => by
    simp only [Blk.In, Blk.pay, Blk.fin] at ha
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
  have hb2 := hb1.rawWrite hcl hfr hmo
  have hb3 := hb2.addRaw hcl (fun h => hfr (List.mem_append_left _ h))
  -- bytes off the cell: `M1` is `M` off allocator bytes, `M` is `Mc` on raws
  have hoff : ∀ b ∈ cells ++ X0.bs, ∀ a, b.In a →
      imgM (writeLog (writeLog M1 [(c.pay, 8, BitVec.ofNat 64 dg)])
        [(c.pay + 8, 8, BitVec.ofNat 64 p)]) a = imgM Mc a := fun b hb a ha => by
    have hbl := st.heap.raw.live b hb
    have hne : b ≠ c := fun e => hfr (List.mem_append_right _ (e ▸ hb))
    have hca : ¬ c.In a := fun hc =>
      live_apart hp.inv (hp.res.live_mono hbl) hcl hne ha hc
    rw [hmo a hca, hp.frame a (live_not_alloc st.heap.heap hbl ha)]
    exact st.heap.raw.img b hb a ha
  refine ⟨st.outHeap cx cb hb3 fun a ha => ?_, ⟨?_, fun b hb a ha => ?_⟩⟩
  · have hna : ¬ c.In a := fun hc => by
      simp only [OutHeap, Blk.In, Blk.pay, Blk.fin, heapStart, heapEnd] at ha hc; omega
    rw [hmo a hna]
    exact hp.frame a (OutHeap.not_alloc st.heap.heap ha)
  · refine Cells.cons hsz ?_ (fun h => hfr (List.mem_append_right _ (by
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ h))) ?_
    · rw [ldv_ld_miss _ _ (by omega)]; exact ldv_store_hit _ _ _
    · rw [ldv_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64]
      exact sk.cells.transport fun b hb a ha => hoff b (List.mem_append_left _ hb) a ha
  · exact (hoff b (List.mem_append_right _ hb) a ha).trans (sk.agree b hb a ha)

/-- The head cell of a nonempty stack, by name. -/
structure CellHead (M : Mem) (Xb : List Blk) (c : Blk) (cs : List Blk) (d : Nat) (ds : List Nat)
    (p : Nat) : Prop where
  p : p = c.pay
  sz : 16 ≤ c.sz
  word : ldv .ld M c.pay = BitVec.ofNat 64 d
  fresh : c ∉ cs ++ Xb
  rest : Cells M Xb cs ds (ldv .ld M (c.pay + 8)).toNat

theorem Cells.head {M : Mem} {Xb : List Blk} {c : Blk} {cs : List Blk} {d : Nat} {ds : List Nat}
    {p : Nat} (h : Cells M Xb (c :: cs) (d :: ds) p) : CellHead M Xb c cs d ds p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **The head cell freed**: the stack is its rest. -/
theorem OgSt.pop {live S : Nat → Prop} {X0 : Raws} {G : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {I : List Nat → String → Mem → Prop} {Mt0 M M' Mc : Mem} {R0 R : Nat → BitVec 64}
    {sp W d : Nat} {H H' : Heap} {F : List Blk} {L : List NumObj} {hs : List RH}
    {os : List Nat} {sent : List Nat} {t : String} {c : Blk} {cells : List Blk} {dg : Nat}
    {ds : List Nat} {q : Nat}
    (st : OgSt S ⟨(c :: cells) ++ X0.bs, Mc⟩ G I Mt0 M R0 R sp W H F L hs os sent t)
    (sk : OgStk X0 Mc (c :: cells) (dg :: ds) q) (cx : OnCtx S R0 sp W d)
    (cb : CharFn live S Q (R0 12) d G I) {lpre lpost : List Blk}
    (hl : H.live = lpre ++ c :: lpost) (hp : FreePost S M M' H H' c lpre lpost) :
    OgSt S ⟨cells ++ X0.bs, Mc⟩ G I Mt0 M' R0 R sp W H' F L hs os sent t ∧
      OgStk X0 Mc cells ds (ldv .ld Mc (c.pay + 8)).toNat := by
  have hh := sk.cells.head
  have hb1 := st.heap.subRaw (X' := ⟨cells ++ X0.bs, Mc⟩) (fun b hb => List.mem_cons_of_mem _ hb)
    fun _ _ _ _ => rfl
  have hno : c ∉ F ++ objBlocks (RList hs L) ++ (cells ++ X0.bs) := fun h => by
    rcases List.mem_append.mp h with h | h
    · exact st.heap.raw.out c List.mem_cons_self h
    · exact hh.fresh h
  exact ⟨st.outHeap cx cb (hb1.freeRaw hl hno hp) fun a ha =>
      hp.frame a (OutHeap.not_alloc st.heap.heap ha), hh.rest, sk.agree⟩

end Dc.Mach
