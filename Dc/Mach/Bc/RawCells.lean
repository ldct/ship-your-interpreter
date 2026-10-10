import Dc.Mach.Bc.Scratch

/-! # Raw blocks entering and leaving the number heap's frame

A caller's raw blocks `X` (`Raws`, `RawOK`) are frozen at an image while the
library runs. A function that allocates its own raw blocks between library
calls (`bc_out_num`'s digit stack) grows and shrinks that set:

- `BcHeap.addRaw`: a fresh live block joins the set, imaged at the current
  memory.
- `BcHeap.subRaw`: the set shrinks to a subset whose image agrees.
- `Cells`: a linked stack of 16-byte `[word, next]` cells, each a raw block,
  read at the image; `Cells.transport` moves it to an agreeing image.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **A fresh block joins the raw set**, imaged at the current memory. -/
theorem BcHeap.addRaw {S : Nat → Prop} {X : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S X M H F L) {b : Blk} (hb : b ∈ H.live)
    (hno : b ∉ F ++ objBlocks L) : BcHeap S ⟨b :: X.bs, M⟩ M H F L :=
  { h with
    raw :=
      ⟨fun c hc => (List.mem_cons.mp hc).elim (fun e => e ▸ hb) (h.raw.live c),
        fun c hc => (List.mem_cons.mp hc).elim (fun e => e ▸ hno) (h.raw.out c),
        fun _ _ _ _ => rfl⟩ }

/-- **The raw set shrinks** to `X'`, its blocks among `X`'s with the same
image on their bytes. -/
theorem BcHeap.subRaw {S : Nat → Prop} {X X' : Raws} {M : Mem} {H : Heap} {F : List Blk}
    {L : List NumObj} (h : BcHeap S X M H F L) (hs : ∀ b ∈ X'.bs, b ∈ X.bs)
    (hi : ∀ b ∈ X'.bs, ∀ a, b.In a → imgM X.img a = imgM X'.img a) : BcHeap S X' M H F L :=
  { h with
    raw :=
      ⟨fun b hb => h.raw.live b (hs b hb), fun b hb => h.raw.out b (hs b hb),
        fun b hb a ha => (h.raw.img b (hs b hb) a ha).trans (hi b hb a ha)⟩ }

/-- The raw set `bs ++ X.bs` imaged at `Mc` back to `X`, given `Mc` agrees
with `X`'s image on `X`'s blocks. -/
theorem BcHeap.dropRaws {S : Nat → Prop} {X : Raws} {bs : List Blk} {Mc M : Mem} {H : Heap}
    {F : List Blk} {L : List NumObj} (h : BcHeap S ⟨bs ++ X.bs, Mc⟩ M H F L)
    (hx : ∀ b ∈ X.bs, ∀ a, b.In a → imgM Mc a = imgM X.img a) : BcHeap S X M H F L :=
  h.subRaw (fun b hb => List.mem_append_right _ hb) hx

/-- **A stack of `[word, next]` cells** from `p` at the image `M`: each cell
a block of at least 16 bytes holding its word at the payload and the next
cell's address at `+8`, distinct from the later cells and from `Xb`; the
address `0` ends the stack. -/
def Cells (M : Mem) (Xb : List Blk) : List Blk → List Nat → Nat → Prop
  | [], [], p => p = 0
  | c :: cs, d :: ds, p =>
      p = c.pay ∧ 16 ≤ c.sz ∧ ldv .ld M c.pay = BitVec.ofNat 64 d ∧ c ∉ cs ++ Xb ∧
        Cells M Xb cs ds (ldv .ld M (c.pay + 8)).toNat
  | _, _, _ => False

/-- The cells at an image agreeing on their bytes. -/
theorem Cells.transport {M M' : Mem} {Xb : List Blk} :
    ∀ {cs : List Blk} {ds : List Nat} {p : Nat}, Cells M Xb cs ds p →
      (∀ c ∈ cs, ∀ a, c.In a → imgM M' a = imgM M a) → Cells M' Xb cs ds p
  | [], [], _, h, _ => h
  | c :: cs, d :: ds, _, ⟨hp, hsz, hd, hn, hr⟩, hm => by
      have hc : ∀ j, j < 16 → imgM M' (c.pay + j) = imgM M (c.pay + j) := fun j hj =>
        hm c List.mem_cons_self _ (by simp only [Blk.In, Blk.pay, Blk.fin]; omega)
      have e0 : ldv .ld M' c.pay = ldv .ld M c.pay :=
        ldv_congr .ld fun j hj => hc j (by simp only [widthOfM] at hj; omega)
      have e8 : ldv .ld M' (c.pay + 8) = ldv .ld M (c.pay + 8) :=
        ldv_congr .ld fun j hj => by
          rw [Nat.add_assoc]; exact hc _ (by simp only [widthOfM] at hj; omega)
      exact ⟨hp, hsz, e0 ▸ hd, hn, e8 ▸ Cells.transport hr fun c' hc' => hm c' (List.mem_cons_of_mem _ hc')⟩
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

/-- The empty stack is the address `0`. -/
theorem Cells.nil {M : Mem} {Xb : List Blk} : Cells M Xb [] [] 0 := rfl

/-- A cell pushed on a stack. -/
theorem Cells.cons {M : Mem} {Xb : List Blk} {cs : List Blk} {ds : List Nat} {c : Blk} {d : Nat}
    (hsz : 16 ≤ c.sz) (hd : ldv .ld M c.pay = BitVec.ofNat 64 d) (hn : c ∉ cs ++ Xb)
    (hr : Cells M Xb cs ds (ldv .ld M (c.pay + 8)).toNat) : Cells M Xb (c :: cs) (d :: ds) c.pay :=
  ⟨rfl, hsz, hd, hn, hr⟩

/-- The stack's blocks and words have one length. -/
theorem Cells.length {M : Mem} {Xb : List Blk} :
    ∀ {cs : List Blk} {ds : List Nat} {p : Nat}, Cells M Xb cs ds p → cs.length = ds.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, ⟨_, _, _, _, hr⟩ => congrArg (· + 1) (Cells.length hr)
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- An empty stack's address is `0`; a nonempty one's is its head's payload. -/
theorem Cells.zero_iff {M : Mem} {Xb : List Blk} {cs : List Blk} {ds : List Nat} {p : Nat}
    (h : Cells M Xb cs ds p) : p = 0 ↔ cs = [] := by
  match cs, ds, h with
  | [], [], h => exact ⟨fun _ => rfl, fun _ => h⟩
  | _ :: _, _ :: _, ⟨hp, _⟩ => exact ⟨fun e => by simp only [Blk.pay] at hp; omega, fun e => by cases e⟩

end Dc.Mach
