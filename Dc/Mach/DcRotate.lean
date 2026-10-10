import Dc.Mach.DcArrSet

/-!
# Rotating the stack (M9)

`dc_stack_rotate (n)` at `0x80003768` moves the node `k = min(|n| - 1,
depth - 1)` positions down to the top (`n > 0`) or the top node down to
position `k` (`n < 0`), relinking the nodes in place (`rotate`).

- `DcAt.permStk`: the stack's nodes relinked into another order; the stores
  touch only the nodes' link words and `dc_stack`.
- `rotate_small`/`rotate_up`/`rotate_down`: the model's three outcomes;
  `absw_pos`/`absw_neg`/`absw_min`: the machine's 32-bit `|n|`.
- `PSeg`: a chain segment between two pointers; `rot_chain_up`/`rot_chain_down`
  relink it through the three stores `rotW`, `DcAt.rotUp`/`.rotDown` lift that
  to the state.
- `dc_stack_rotate_spec`: the function, from `rot_entry`, `rot_walk` and
  `rot_after`.
-/

namespace Dc.Mach

open Vsa.MemRepr Vsa.Sim VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

set_option linter.unusedSimpArgs false

/-- An `LChain` with a weaker node predicate. -/
theorem LChain.imp {α : Type} {Mt : Mem} {off : Nat} {P P' : Blk → α → Prop} :
    ∀ {a : Nat} {l : List (Blk × α)}, LChain Mt off P a l →
      (∀ bx ∈ l, P bx.1 bx.2 → P' bx.1 bx.2) → LChain Mt off P' a l
  | _, _, .nil h, _ => .nil h
  | _, _, .cons h hp hl, hq =>
    .cons h (hq _ List.mem_cons_self hp) (hl.imp fun bx hm => hq bx (List.mem_cons_of_mem _ hm))

theorem DcG.blocks_permStk (G : DcG) {l' : List (Blk × GV)} (hp : l'.Perm G.stk) :
    ({ G with stk := l' } : DcG).blocks.Perm G.blocks := by
  simp only [DcG.blocks]
  exact ((hp.map _).append_right _).append_right _ |>.append_right _

theorem DcG.vals_permStk (G : DcG) {l' : List (Blk × GV)} (hp : l'.Perm G.stk) :
    ({ G with stk := l' } : DcG).vals.Perm G.vals := by
  simp only [DcG.vals]
  exact (hp.map _).append_right _

/-- The bytes `dc_stack_rotate` may store: `dc_stack` and the stack nodes'
link words. -/
def StkLinks (G : DcG) (x : Nat) : Prop :=
  StkWord x ∨ ∃ bg ∈ G.stk, bg.1.pay + 24 ≤ x ∧ x < bg.1.pay + 32

/-- **The stack relinked**: the nodes of `G.stk` in the order `l'`, the
data `m'`; the memory changes only at `dc_stack` and the nodes' link words. -/
theorem DcAt.permStk {S : Nat → Prop} {M M' : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {l' : List (Blk × GV)} {m' : List Val}
    (h : DcAt S M H F L C G hs st) (hp : l'.Perm G.stk) (hm : MemOnly (StkLinks G) M' M)
    (hch : LChain M' 24 (fun _ _ => True) dcStackAddr l')
    (hden : List.Forall₂ (fun (bg : Blk × GV) v => bg.2.Den ⟨L, G.strs⟩ v) l' m') :
    DcAt S M' H F L C { G with stk := l' } hs { st with stack := m' } := by
  have hi := h.heap.heap
  have hsn : ∀ bg ∈ G.stk, SNodeAt M bg.1 bg.2 := fun bg hm' => h.view.stk.forall bg hm'
  have hsl : ∀ bg ∈ G.stk, bg.1 ∈ H.live := fun bg hm' => h.heap.raw.live _ (G.stk_mem hm')
  -- a changed heap byte lies in a stack node, at or above its link word
  have hchg : ∀ x, StkLinks G x → StkWord x ∨ ∃ bg ∈ G.stk, bg.1.In x ∧ bg.1.pay + 24 ≤ x :=
    fun x hx => hx.elim .inl fun ⟨bg, hm', h1, h2⟩ => .inr ⟨bg, hm', by
      have := (hsn bg hm').sz
      simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 this ⊢; omega, h1⟩
  have hsw : ∀ x, StkWord x → ¬ (heapStart ≤ x ∧ x < heapEnd) := fun x hx h' => by
    simp only [StkWord, dc_addrs, heapStart] at hx h'; omega
  -- bytes of a live block other than the stack nodes are unchanged
  have hoff : ∀ c ∈ H.live, (∀ bg ∈ G.stk, bg.1 ≠ c) → ∀ x, c.In x → imgM M' x = imgM M x :=
    fun c hc hn x hx => hm x fun hP => by
      rcases hchg x hP with hw | ⟨bg, hm', hbx, -⟩
      · exact hsw x hw (live_in_heap hi hc hx)
      · exact live_apart hi (hsl bg hm') hc (hn bg hm') hbx hx
  -- the first 24 bytes of a stack node are unchanged
  have hlow : ∀ bg ∈ G.stk, ∀ x, bg.1.pay ≤ x → x < bg.1.pay + 24 → imgM M' x = imgM M x :=
    fun bg hm' x h1 h2 => hm x fun hP => by
      have hsz := (hsn bg hm').sz
      have hbx : bg.1.In x := by simp only [Blk.In, Blk.pay, Blk.fin] at h1 h2 hsz ⊢; omega
      rcases hchg x hP with hw | ⟨bg', hm'', hbx', h3⟩
      · exact hsw x hw (live_in_heap hi (hsl bg hm') hbx)
      · by_cases he : bg'.1 = bg.1
        · rw [he] at h3; omega
        · exact live_apart hi (hsl bg' hm'') (hsl bg hm') he hbx' hbx
  have hnheap : ∀ x, ¬ (heapStart ≤ x ∧ x < heapEnd) → ¬ StkWord x → imgM M' x = imgM M x :=
    fun x hx hs' => hm x fun hP => by
      rcases hchg x hP with hw | ⟨bg, hm', hbx, -⟩
      · exact hs' hw
      · exact hx (live_in_heap hi (hsl bg hm') hbx)
  -- blocks of the state off the stack
  have hstkB : ∀ c ∈ G.blocks, (∃ bg ∈ G.stk, bg.1 = c) ∨ ∀ bg ∈ G.stk, bg.1 ≠ c := fun c _ => by
    by_cases hc : ∃ bg ∈ G.stk, bg.1 = c
    · exact .inl hc
    · exact .inr fun bg hm' e => hc ⟨bg, hm', e⟩
  have hnd := h.nodup
  have hsplit : ∀ c, c ∈ G.stk.map (·.1) → ∀ c' ∈ G.blocks, c' ∉ G.stk.map (·.1) → c ≠ c' :=
    fun c hc c' _ hc' e => hc' (e ▸ hc)
  have hblkP := G.blocks_permStk hp
  -- the number heap
  have hb0 : BcHeap S (G.rawsOff (G.stk.map (·.1)) M) M H F L :=
    h.heap.subRaw (fun c hc => (DcG.mem_rawsOff.mp hc).1) fun _ _ _ _ => rfl
  have hb1 : BcHeap S (G.rawsOff (G.stk.map (·.1)) M) M' H F L :=
    hb0.transportOwn (fun x hx => hm x fun hP => by
        rcases hchg x hP with hw | ⟨bg, hm', hbx, -⟩
        · rcases AllocByte.glob_or_heap hi hx with h1 | h1
          · simp only [StkWord, dc_addrs, freeListAddr] at hw h1; omega
          · exact hsw x hw h1
        · exact live_not_alloc hi (hsl bg hm') hbx hx)
      (fun c hc x hx => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hoff c (h.heap.owned_live (List.mem_append_left _ hc))
            (fun bg hm' e => h.heap.raw.out _ (G.stk_mem hm') (e ▸ hc)) x hx
        · obtain ⟨hcG, hcE⟩ := DcG.mem_rawsOff.mp hc
          exact hoff c (h.heap.raw.live c hcG)
            (fun bg hm' e => hcE (e ▸ List.mem_map.mpr ⟨bg, hm', rfl⟩)) x hx)
      fun j hj => hnheap _ (fun h' => by simp only [bcFreeAddr, heapStart] at h'; omega)
        fun h' => by simp only [StkWord, bcFreeAddr, dc_addrs] at h'; omega
  have hb2 := hb1.addRaws (bs := G.stk.map (·.1))
    (fun c hc => by obtain ⟨bg, hm', rfl⟩ := List.mem_map.mp hc; exact hsl bg hm')
    fun c hc => by
      obtain ⟨bg, hm', rfl⟩ := List.mem_map.mp hc
      exact h.heap.raw.out _ (G.stk_mem hm')
  -- unchanged blocks of the state
  have hGoff : ∀ c ∈ G.blocks, (∀ bg ∈ G.stk, bg.1 ≠ c) → ∀ x, c.In x → imgM M' x = imgM M x :=
    fun c hc hn => hoff c (h.heap.raw.live c hc) hn
  have hnotStk : ∀ c ∈ G.blocks, c ∉ G.stk.map (·.1) → ∀ bg ∈ G.stk, bg.1 ≠ c :=
    fun c _ hc bg hm' e => hc (List.mem_map.mpr ⟨bg, hm', e⟩)
  -- stack blocks are not register or string blocks
  have hdisj : ∀ c ∈ G.stk.map (·.1), c ∉ (List.range 256).flatMap
      (fun r => (G.regs r).flatMap RLev.blocks) ++ G.strs.flatMap (fun o => [o.hb, o.tb]) ++
        G.lbuf.toList := fun c hc hc' => by
    simp only [DcG.blocks, List.append_assoc] at hnd
    exact (List.nodup_append.mp hnd).2.2 c hc c (by simpa [List.append_assoc] using hc') rfl
  have hglob : ∀ x, DcGlob x → ¬ ChainWords x → imgM M' x = imgM M x := fun x hx hc =>
    hnheap x (fun h' => by have := hx.lt; omega) fun hs' => hc (.inl hs')
  refine
    { heap := hb2.subRaw (fun c hc => ?_) fun _ _ _ _ => rfl
      nodup := hblkP.nodup_iff.mpr hnd
      view := h.view.withChains rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun o ho x hx => hx.elim
          (fun hx => hGoff _ (G.str_mem ho).1 (fun bg hm' e => hdisj _
            (List.mem_map.mpr ⟨bg, hm', rfl⟩) (by
              rw [e]; simp only [List.mem_append, List.mem_flatMap]
              exact .inl (.inr ⟨o, ho, by simp⟩))) x hx)
          fun hx => hGoff _ (G.str_mem ho).2 (fun bg hm' e => hdisj _
            (List.mem_map.mpr ⟨bg, hm', rfl⟩) (by
              rw [e]; simp only [List.mem_append, List.mem_flatMap]
              exact .inl (.inr ⟨o, ho, by simp⟩))) x hx)
        hglob ?_ fun r hr => ?_
      den := ?_
      glob := h.glob
      col := h.col }
  · have hc' := hblkP.mem_iff.mp hc
    by_cases hcS : c ∈ G.stk.map (·.1)
    · exact List.mem_append_left _ hcS
    · exact List.mem_append_right _ (DcG.mem_rawsOff.mpr ⟨hc', hcS⟩)
  · refine hch.imp fun bg hm' _ => ?_
    have hm0 := hp.mem_iff.mp hm'
    have hq := hsn bg hm0
    exact ⟨DatAt.congr16 (fun x h1 h2 => hlow bg hm0 x h1 (by omega)) hq.dat,
      (ldv_congr .ld fun j hj => hlow bg hm0 _ (by omega) (by simp only [widthOfM] at hj; omega)).trans
        hq.arr, hq.sz⟩
  · exact regChain_frame (h.view.regs r hr) (ldv_congr .ld fun j hj => hnheap _ (by
      simp only [widthOfM, heapStart, regAddr, dc_addrs] at hj ⊢; omega) fun hc => by
        simp only [widthOfM, StkWord, regAddr, dc_addrs] at hj hc; omega)
      fun be hmm c hc x hx => hGoff c (G.lev_mem hr hmm hc) (fun bg hm' e => hdisj _
        (List.mem_map.mpr ⟨bg, hm', rfl⟩) (by
          rw [e]; simp only [List.mem_append, List.mem_flatMap]
          exact .inl (.inl ⟨r, List.mem_range.mpr hr, be, hmm, hc⟩))) x hx
  · have hd := h.den
    have hcount : ∀ y, (({ G with stk := l' } : DcG).vals ++ hs).count y = (G.vals ++ hs).count y :=
      fun y => by
        have := List.perm_iff_count.mp (G.vals_permStk hp) y
        simp only [List.count_append] at this ⊢; omega
    exact
      { hd with
        stk := hden
        numRefs := fun x hx => by rw [hcount]; exact hd.numRefs x hx
        strRefs := fun o ho => by rw [hcount]; exact hd.strRefs o ho }

/-! ## The model and the word `|n|` -/

/-- The stack unchanged: `|n| < 2`, `n = -2^31` or at most one entry. -/
theorem rotate_small {n : Int} {s : List Val} (h : n.natAbs < 2 ∨ n = -2147483648 ∨ s.length ≤ 1) :
    rotate n s = s := by
  unfold rotate
  rcases h with h | h | h
  · simp [h]
  · simp [h]
  · match s, h with
    | [], _ => simp
    | [a], _ => simp

/-- `n > 0`: the entry at depth `|m1|` moves to the top. -/
theorem rotate_up {n : Int} {m1 m2 : List Val} {x : Val} (hn : 0 < n)
    (hl : m1.length = min (n.natAbs - 1) (m1.length + m2.length)) (h1 : m1 ≠ []) :
    rotate n (m1 ++ x :: m2) = x :: (m1 ++ m2) := by
  have hp : 0 < m1.length := List.length_pos_iff.mpr h1
  unfold rotate
  have hi : min (n.natAbs - 1) ((m1 ++ x :: m2).length - 1) = m1.length := by
    simp only [List.length_append, List.length_cons]; omega
  simp only [hi]
  have hne : n ≠ -2147483648 := by omega
  simp [hne, hn]
  have h2 : ¬ n.natAbs < 2 := by omega
  simp only [h2, h1, ite_false, List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

/-- `n < 0`: the top moves down to depth `|mid| + 1`. -/
theorem rotate_down {n : Int} {top : Val} {mid m2 : List Val} {x : Val} (hn : n < 0)
    (hmin : n ≠ -2147483648)
    (hl : mid.length + 1 = min (n.natAbs - 1) (mid.length + 1 + m2.length)) :
    rotate n (top :: mid ++ x :: m2) = mid ++ x :: top :: m2 := by
  unfold rotate
  have hi : min (n.natAbs - 1) ((top :: mid ++ x :: m2).length - 1) = mid.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  simp only [hi]
  simp [hmin, show ¬ 0 < n by omega]
  have h2 : ¬ n.natAbs < 2 := by omega
  simp only [h2, ite_false, show mid ++ x :: m2 = (mid ++ [x]) ++ m2 by simp,
    List.take_left' (show (mid ++ [x]).length = mid.length + 1 by simp)]
  simp


/-- `dc_stack_rotate`'s `|n|` in 32 bits (`sraiw`, `xor`, `subw`). -/
def absw (x : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64
    (BitVec.extractLsb 31 0
        (x ^^^ BitVec.signExtend 64 (shift_bits_right_arith (BitVec.extractLsb 31 0 x) 31#5)) -
      BitVec.extractLsb 31 0 (BitVec.signExtend 64 (shift_bits_right_arith (BitVec.extractLsb 31 0 x) 31#5)))

theorem exw_ofInt_neg {k : Nat} (h1 : 0 < k) (h2 : k ≤ 2 ^ 31) :
    BitVec.extractLsb 31 0 (BitVec.ofInt 64 (-(k : Int))) = BitVec.ofNat 32 (2 ^ 32 - k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  omega

theorem sra31_neg {x : Nat} (h1 : 2 ^ 31 ≤ x) (h2 : x < 2 ^ 32) :
    shift_bits_right_arith (BitVec.ofNat 32 x) 31#5 = BitVec.allOnes 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [shift_bits_right_arith, BitVec.toNatInt, BitVec.toNat_sshiftRight,
      BitVec.msb_eq_decide, Nat.mod_eq_of_lt h2]
  split <;> rw [Nat.shiftRight_eq_div_pow] <;> omega

theorem sra31_pos {x : Nat} (h2 : x < 2 ^ 31) :
    shift_bits_right_arith (BitVec.ofNat 32 x) 31#5 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  simp [shift_bits_right_arith, BitVec.toNatInt, BitVec.toNat_sshiftRight,
      BitVec.msb_eq_decide, Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega)]
  split <;> rw [Nat.shiftRight_eq_div_pow] <;> omega

theorem absw_pos {k : Nat} (hk : k < 2 ^ 31) : absw (BitVec.ofNat 64 k) = BitVec.ofNat 64 k := by
  unfold absw
  rw [exw_ofNat (by omega), sra31_pos hk, show BitVec.signExtend 64 (0#32) = 0#64 by decide,
    BitVec.xor_zero, show BitVec.extractLsb 31 0 (0#64) = 0#32 by decide, BitVec.sub_zero,
    exw_ofNat (by omega)]
  exact sext32_ofNat hk

theorem absw_neg {k : Nat} (h1 : 0 < k) (hk : k < 2 ^ 31) :
    absw (BitVec.ofInt 64 (-(k : Int))) = BitVec.ofNat 64 k := by
  unfold absw
  rw [exw_ofInt_neg h1 (by omega), sra31_neg (by omega) (by omega),
    show BitVec.signExtend 64 (BitVec.allOnes 32) = BitVec.allOnes 64 by decide,
    show BitVec.extractLsb 31 0 (BitVec.allOnes 64) = BitVec.allOnes 32 by decide]
  have e1 : BitVec.ofInt 64 (-(k : Int)) ^^^ BitVec.allOnes 64 = BitVec.ofNat 64 (k - 1) := by
    rw [BitVec.xor_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_not, BitVec.toNat_ofInt]
    omega
  rw [e1, exw_ofNat (by omega)]
  have e2 : BitVec.ofNat 32 (k - 1) - BitVec.allOnes 32 = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub]
    omega
  rw [e2]
  exact sext32_ofNat hk

/-- `-2^31` stays negative. -/
theorem absw_min : absw (BitVec.ofInt 64 (-2147483648)) = 0xffffffff80000000#64 := by decide

/-! ## Chain segments -/

/-- A chain segment from the pointer `p` through the blocks `l`, linked
through the word at `+off`, the last link word holding `e`. -/
inductive PSeg {α : Type} (Mt : Mem) (off : Nat) : BitVec 64 → List (Blk × α) → BitVec 64 → Prop
  | nil {p : BitVec 64} : PSeg Mt off p [] p
  | cons {b : Blk} {x : α} {l : List (Blk × α)} {e : BitVec 64} :
      PSeg Mt off (ldv .ld Mt (b.pay + off)) l e → PSeg Mt off (BitVec.ofNat 64 b.pay) ((b, x) :: l) e

theorem PSeg.append {α : Type} {Mt : Mem} {off : Nat} :
    ∀ {p q e : BitVec 64} {l1 l2 : List (Blk × α)}, PSeg Mt off p l1 q → PSeg Mt off q l2 e →
      PSeg Mt off p (l1 ++ l2) e
  | _, _, _, _, _, .nil, h2 => h2
  | _, _, _, _, _, .cons h1, h2 => .cons (h1.append h2)

theorem PSeg.split {α : Type} {Mt : Mem} {off : Nat} :
    ∀ {l1 l2 : List (Blk × α)} {p e : BitVec 64}, PSeg Mt off p (l1 ++ l2) e →
      ∃ q, PSeg Mt off p l1 q ∧ PSeg Mt off q l2 e
  | [], _, p, _, h => ⟨p, .nil, h⟩
  | (b, x) :: l1, l2, _, _, h => by
    cases h with
    | cons h' =>
      obtain ⟨q, h1, h2⟩ := PSeg.split (l1 := l1) h'
      exact ⟨q, .cons h1, h2⟩

theorem PSeg.uncons {α : Type} {Mt : Mem} {off : Nat} {p e : BitVec 64} {b : Blk} {x : α}
    {l : List (Blk × α)} (h : PSeg Mt off p ((b, x) :: l) e) :
    p = BitVec.ofNat 64 b.pay ∧ PSeg Mt off (ldv .ld Mt (b.pay + off)) l e := by
  cases h with
  | cons h' => exact ⟨rfl, h'⟩

theorem PSeg.nil_eq {α : Type} {Mt : Mem} {off : Nat} {p e : BitVec 64}
    (h : PSeg Mt off p ([] : List (Blk × α)) e) : p = e := by
  cases h; rfl

theorem PSeg.frame {α : Type} {M M' : Mem} {off : Nat} :
    ∀ {p e : BitVec 64} {l : List (Blk × α)}, PSeg M off p l e →
      (∀ bx ∈ l, ldv .ld M' (bx.1.pay + off) = ldv .ld M (bx.1.pay + off)) → PSeg M' off p l e
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h, hw => by
    refine .cons ?_
    rw [hw _ List.mem_cons_self]
    exact h.frame fun bx hm => hw bx (List.mem_cons_of_mem _ hm)

theorem PSeg.cast {α : Type} {Mt : Mem} {off : Nat} {p p' e : BitVec 64} {l : List (Blk × α)}
    (hp : p = p') (h : PSeg Mt off p l e) : PSeg Mt off p' l e := hp ▸ h

/-- A segment ending in a null link starts at its first node. -/
theorem PSeg.head {α : Type} {Mt : Mem} {off : Nat} {p : BitVec 64} :
    ∀ {l : List (Blk × α)}, PSeg Mt off p l 0#64 → p = headPtr l
  | [], h => h.nil_eq
  | (_, _) :: _, h => h.uncons.1

theorem LChain.toSeg {α : Type} {Mt : Mem} {off : Nat} {P : Blk → α → Prop} :
    ∀ {a : Nat} {l : List (Blk × α)}, LChain Mt off P a l → PSeg Mt off (ldv .ld Mt a) l 0#64
  | _, _, .nil h => by rw [h]; exact .nil
  | _, _, .cons h _ hl => by rw [h]; exact .cons hl.toSeg

theorem PSeg.toL {α : Type} {Mt : Mem} {off : Nat} :
    ∀ {a : Nat} {l : List (Blk × α)}, PSeg Mt off (ldv .ld Mt a) l 0#64 →
      LChain Mt off (fun _ _ => True) a l
  | _, [], h => .nil h.nil_eq
  | _, (_, _) :: _, h => .cons h.uncons.1 trivial (PSeg.toL h.uncons.2)

/-- In a list whose images are distinct, an element's image differs from the
others'. -/
theorem nd_mid {α β : Type} {f : α → β} {A B : List α} {x : α} (h : ((A ++ x :: B).map f).Nodup) :
    ∀ y ∈ A ++ B, f y ≠ f x := fun y hy e => by
  have h' := (List.perm_middle.map f).nodup_iff.mp h
  simp only [List.map_cons] at h'
  exact (List.nodup_cons.mp h').1 (List.mem_map.mpr ⟨y, hy, e⟩)

/-! ## The relinking stores -/

/-- `dc_stack_rotate`'s three stores: two link words and `dc_stack`. -/
abbrev rotW (M : Mem) (a1 : Nat) (v1 : BitVec 64) (a2 : Nat) (v2 v3 : BitVec 64) : Mem :=
  writeLog (writeLog (writeLog M [(a1, 8, v1)]) [(a2, 8, v2)]) [(dcStackAddr, 8, v3)]

theorem rotW_miss {M : Mem} {x a1 a2 : Nat} {v1 v2 v3 : BitVec 64} (h1 : x + 8 ≤ a1 ∨ a1 + 8 ≤ x)
    (h2 : x + 8 ≤ a2 ∨ a2 + 8 ≤ x) (h3 : dcStackAddr + 8 ≤ x) :
    ldv .ld (rotW M a1 v1 a2 v2 v3) x = ldv .ld M x := by
  simp only [rotW]
  rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ h2, ldv_ld_miss _ _ h1]

theorem rotW_ld1 {M : Mem} {a1 a2 : Nat} {v1 v2 v3 : BitVec 64} (h2 : a1 + 8 ≤ a2 ∨ a2 + 8 ≤ a1)
    (h3 : dcStackAddr + 8 ≤ a1) : ldv .ld (rotW M a1 v1 a2 v2 v3) a1 = v1 := by
  simp only [rotW]
  rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ h2, ldv_store_hit]

theorem rotW_ld2 {M : Mem} {a1 a2 : Nat} {v1 v2 v3 : BitVec 64} (h3 : dcStackAddr + 8 ≤ a2) :
    ldv .ld (rotW M a1 v1 a2 v2 v3) a2 = v2 := by
  simp only [rotW]
  rw [ldv_ld_miss _ _ (by omega), ldv_store_hit]

theorem rotW_ld3 {M : Mem} {a1 a2 : Nat} {v1 v2 v3 : BitVec 64} :
    ldv .ld (rotW M a1 v1 a2 v2 v3) dcStackAddr = v3 := by
  simp only [rotW]; rw [ldv_store_hit]

/-- The bytes the three stores change are `StkLinks`. -/
theorem rotW_only {G : DcG} {M : Mem} {b1 b2 : Blk} {v1 v2 v3 : BitVec 64}
    (h1 : ∃ bg ∈ G.stk, bg.1 = b1) (h2 : ∃ bg ∈ G.stk, bg.1 = b2) :
    MemOnly (StkLinks G) (rotW M (b1.pay + 24) v1 (b2.pay + 24) v2 v3) M := fun x hx => by
  obtain ⟨g1, m1, e1⟩ := h1
  obtain ⟨g2, m2, e2⟩ := h2
  have n1 : x < b1.pay + 24 ∨ b1.pay + 24 + 8 ≤ x := by
    refine (Classical.em _).elim id fun hc => (hx (.inr ⟨g1, m1, by rw [e1]; omega, by rw [e1]; omega⟩)).elim
  have n2 : x < b2.pay + 24 ∨ b2.pay + 24 + 8 ≤ x := by
    refine (Classical.em _).elim id fun hc => (hx (.inr ⟨g2, m2, by rw [e2]; omega, by rw [e2]; omega⟩)).elim
  have n3 : x < dcStackAddr ∨ dcStackAddr + 8 ≤ x := by
    refine (Classical.em _).elim id fun hc => (hx (.inl (by simp only [StkWord]; omega))).elim
  simp only [rotW]
  rw [imgM_store_miss _ _ n3, imgM_store_miss _ _ n2, imgM_store_miss _ _ n1]

/-- **Up**: the node `c` after `pre0 ++ [lb]` unlinked and linked in at the
top. -/
theorem rot_chain_up {α : Type} {M : Mem} {w : BitVec 64} {pre0 post : List (Blk × α)} {lb c : Blk}
    {lg g : α} (hch : PSeg M 24 w (pre0 ++ (lb, lg) :: (c, g) :: post) 0#64)
    (hgeo : ∀ bx ∈ pre0 ++ (lb, lg) :: (c, g) :: post, dcStackAddr + 8 ≤ bx.1.pay ∧ bx.1.pay % 16 = 0)
    (hnd : ((pre0 ++ (lb, lg) :: (c, g) :: post).map (·.1.pay)).Nodup) :
    PSeg (rotW M (lb.pay + 24) (headPtr post) (c.pay + 24) w (BitVec.ofNat 64 c.pay)) 24
      (BitVec.ofNat 64 c.pay) ((c, g) :: (pre0 ++ (lb, lg) :: post)) 0#64 := by
  obtain ⟨q, h1, h2⟩ := PSeg.split hch
  obtain ⟨e1, h3⟩ := h2.uncons
  obtain ⟨e2, h4⟩ := h3.uncons
  subst e1
  have hq := h4.head
  have glb := hgeo (lb, lg) (by simp)
  have gc := hgeo (c, g) (by simp)
  dsimp only at glb gc
  have nlb := nd_mid (f := fun x : Blk × α => x.1.pay) (A := pre0) (B := (c, g) :: post) hnd
  have nc := nd_mid (f := fun x : Blk × α => x.1.pay) (A := pre0 ++ [(lb, lg)]) (B := post)
    (by rw [show pre0 ++ [(lb, lg)] ++ (c, g) :: post = pre0 ++ (lb, lg) :: (c, g) :: post by simp]
        exact hnd)
  have dlb : ∀ bx ∈ pre0 ++ post, bx.1.pay ≠ lb.pay := fun bx hm =>
    nlb bx (by rcases List.mem_append.mp hm with h | h <;> simp [h])
  have dc : ∀ bx ∈ pre0 ++ post, bx.1.pay ≠ c.pay := fun bx hm =>
    nc bx (by rcases List.mem_append.mp hm with h | h <;> simp [h])
  have hlc : lb.pay ≠ c.pay := nc (lb, lg) (by simp)
  have hfr : ∀ bx ∈ pre0 ++ post, ldv .ld (rotW M (lb.pay + 24) (headPtr post) (c.pay + 24) w
      (BitVec.ofNat 64 c.pay)) (bx.1.pay + 24) = ldv .ld M (bx.1.pay + 24) := fun bx hm => by
    have gb := hgeo bx (by rcases List.mem_append.mp hm with h | h <;> simp [h])
    have := dlb bx hm; have := dc bx hm
    exact rotW_miss (by omega) (by omega) (by omega)
  refine .cons ?_
  rw [rotW_ld2 (by omega)]
  refine PSeg.append (h1.frame fun bx hm => hfr bx (List.mem_append_left _ hm)) (.cons ?_)
  rw [rotW_ld1 (by omega) (by omega)]
  exact PSeg.cast hq (h4.frame fun bx hm => hfr bx (List.mem_append_right _ hm))

/-- **Down**: the top node `top` linked in after `mid ++ [c]`. -/
theorem rot_chain_down {α : Type} {M : Mem} {mid post : List (Blk × α)} {top c : Blk}
    {gt g : α} (hch : PSeg M 24 (BitVec.ofNat 64 top.pay) ((top, gt) :: (mid ++ (c, g) :: post)) 0#64)
    (hgeo : ∀ bx ∈ (top, gt) :: (mid ++ (c, g) :: post), dcStackAddr + 8 ≤ bx.1.pay ∧ bx.1.pay % 16 = 0)
    (hnd : (((top, gt) :: (mid ++ (c, g) :: post)).map (·.1.pay)).Nodup) :
    PSeg (rotW M (top.pay + 24) (headPtr post) (c.pay + 24) (BitVec.ofNat 64 top.pay)
        (ldv .ld M (top.pay + 24))) 24
      (ldv .ld M (top.pay + 24)) (mid ++ (c, g) :: (top, gt) :: post) 0#64 := by
  obtain ⟨-, h0⟩ := hch.uncons
  obtain ⟨q, h1, h2⟩ := PSeg.split h0
  obtain ⟨e1, h4⟩ := h2.uncons
  subst e1
  have hq := h4.head
  have gt' := hgeo (top, gt) (by simp)
  have gc := hgeo (c, g) (by simp)
  dsimp only at gt' gc
  have ntop := nd_mid (f := fun x : Blk × α => x.1.pay) (A := []) (B := mid ++ (c, g) :: post) hnd
  have nc := nd_mid (f := fun x : Blk × α => x.1.pay) (A := (top, gt) :: mid) (B := post) hnd
  have dt : ∀ bx ∈ mid ++ post, bx.1.pay ≠ top.pay := fun bx hm =>
    ntop bx (by rcases List.mem_append.mp hm with h | h <;> simp [h])
  have dc : ∀ bx ∈ mid ++ post, bx.1.pay ≠ c.pay := fun bx hm =>
    nc bx (by rcases List.mem_append.mp hm with h | h <;> simp [h])
  have htc : top.pay ≠ c.pay := nc (top, gt) (by simp)
  have hfr : ∀ bx ∈ mid ++ post, ldv .ld (rotW M (top.pay + 24) (headPtr post) (c.pay + 24)
      (BitVec.ofNat 64 top.pay) (ldv .ld M (top.pay + 24))) (bx.1.pay + 24) =
        ldv .ld M (bx.1.pay + 24) := fun bx hm => by
    have gb := hgeo bx (by rcases List.mem_append.mp hm with h | h <;> simp [h])
    have := dt bx hm; have := dc bx hm
    exact rotW_miss (by omega) (by omega) (by omega)
  refine PSeg.append (h1.frame fun bx hm => hfr bx (List.mem_append_left _ hm)) (.cons ?_)
  rw [rotW_ld2 (by omega)]
  refine .cons ?_
  rw [rotW_ld1 (by omega) (by omega)]
  exact PSeg.cast hq (h4.frame fun bx hm => hfr bx (List.mem_append_right _ hm))

/-! ## The machine spans -/

/-- `slti`'s result is zero exactly when the comparison fails. -/
theorem sltiV_zero (a b : BitVec 64) : sltiV a b = 0#64 ↔ ¬ (a.toInt < b.toInt) := by
  unfold sltiV
  by_cases h : a.toInt < b.toInt <;>
    simp [LeanRV64DExecutable.Functions.zopz0zI_s, h,
      LeanRV64DExecutable.Functions.bool_to_bit, LeanRV64DExecutable.zero_extend,
      LeanRV64DExecutable.Functions.bool_bit_forwards, Sail.BitVec.zeroExtend]

/-- The registers `dc_stack_rotate` may change. -/
abbrev rotClob : List Nat := [11, 12, 13, 14, 15]

/-- `dc_stack_rotate`'s entry: `a1` the top, `a5` the word `|n|`; it returns
at once for an empty stack or `|n| < 2`, else enters the walk at
`0x800037a0`. -/
theorem rot_entry {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) (hG : ∀ a, DcGlob a → S a) {M : Mem}
    {a w : BitVec 64} (R : Nat → BitVec 64) (habs : absw (R 10) = a)
    (hw : ldv .ld M dcStackAddr = w) (hal : (R 1).toNat % 4 = 0)
    (hret : ∀ R', w = 0#64 ∨ a.toInt < 2 → Keeps rotClob R' R → DW live S Q (R 1) R' M)
    (hgo : ∀ R', w ≠ 0#64 → ¬ a.toInt < 2 → Keeps rotClob R' R → R' 11 = w → R' 14 = w →
      R' 12 = 0#64 → R' 15 = a → DW live S Q 0x800037a0#64 R' M) :
    DW live S Q 0x80003768#64 R M := by
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hown : ∀ b ∈ accAddrs dcStackAddr 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs] at this ⊢; omega)
  unfold absw at habs
  bc_run hlive hS [habs, hw] at 0x80003780
  all_goals first | exact hown | (simp only [LdOK, dc_addrs, htx]; omega) | skip
  · intro h0
    bc_run hlive hS []
    first | exact hal | skip
    exact hret _ (.inl h0) (by keeps_tac Keeps.refl _ _)
  intro h0
  bc_run hlive hS [habs, hw] at 0x80003788
  · intro h1
    have h2 : a.toInt < (2#64).toInt := Classical.byContradiction fun hc => h1 ((sltiV_zero _ _).mpr hc)
    have e2 : (2#64).toInt = 2 := by decide
    bc_run hlive hS []
    first | exact hal | skip
    exact hret _ (.inr (by omega)) (by keeps_tac Keeps.refl _ _)
  · intro h1
    have h2 : ¬ a.toInt < (2#64).toInt := (sltiV_zero _ _).mp (Classical.byContradiction h1)
    have e2 : (2#64).toInt = 2 := by decide
    bc_run hlive hS [] at 0x800037a0
    refine hgo _ h0 (by omega) ?_ ?_ ?_ ?_ ?_
    · keeps_tac Keeps.refl _ _
    all_goals bsimp []


/-- `dc_stack_rotate`'s walk (`0x800037a0`, `a4` the node `c`, `a2` the node
before, `a5` the count `t`): it stops at the node `min (t - 1) |post|` further
down, `a3` naming the node after it. -/
theorem rot_walk {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} {P : Blk → GV → Prop}
    {all : List (Blk × GV)} :
    ∀ {post : List (Blk × GV)} {c : Blk} {g : GV} {pre : List (Blk × GV)} {t : Nat},
    all = pre ++ (c, g) :: post →
    PChain M 24 P (BitVec.ofNat 64 c.pay) ((c, g) :: post) →
    (∀ bx ∈ (c, g) :: post, heapStart + 16 ≤ bx.1.pay ∧ bx.1.pay + 32 ≤ heapEnd ∧ bx.1.pay % 16 = 0) →
    1 ≤ t → t < 2 ^ 31 →
    ∀ (R : Nat → BitVec 64), R 14 = BitVec.ofNat 64 c.pay → R 12 = lastPtr pre →
    R 15 = BitVec.ofNat 64 t →
    (∀ R' pre' c' g' post', all = pre' ++ (c', g') :: post' →
      pre'.length = pre.length + min (t - 1) post.length → Keeps [12, 13, 14, 15] R' R →
      R' 14 = BitVec.ofNat 64 c'.pay → R' 12 = lastPtr pre' → R' 13 = headPtr post' →
      DW live S Q 0x800037ac#64 R' M) →
    DW live S Q 0x800037a0#64 R M := by
  intro post
  induction post with
  | nil => ?_
  | cons y post ih => ?_
  all_goals
    intro c g pre t hall hc hb ht1 ht2 R h14 h12 h15 hk
    have htx : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨hb1, hb2, hb3⟩ := hb (c, g) List.mem_cons_self
    simp only [heapStart, heapEnd] at hb1 hb2
    obtain ⟨-, hl⟩ := hc.uncons
    have wp : BitVec.ofNat 64 t + 18446744073709551615#64 = BitVec.ofNat 64 (t - 1) := word_pred ht1
    have wq : BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (t - 1))) =
        BitVec.ofNat 64 (t - 1) := sxw_ofNat (by omega)
  -- the last node: the link is null
  · have hz := hl.nil_eq
    bc_run hlive hS [h14, h15, hz, wp, wq, se12_fff] at 0x800037ac
    all_goals try (intro hc; exact (hc rfl).elim)
    try intro _
    try bc_run hlive hS [] at 0x800037ac
    refine hk _ pre c g [] hall (by simp) ?_ ?_ ?_ ?_
    · keeps_tac Keeps.refl _ _
    all_goals bsimp [h12, h14, headPtr]
  · obtain ⟨b', x'⟩ := y
    have he := hl.head_eq
    obtain ⟨hb1', hb2', -⟩ := hb (b', x') (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [heapStart, heapEnd] at hb1' hb2'
    have hnz : BitVec.ofNat 64 b'.pay ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
    bc_run hlive hS [h14, h15, he, wp, wq, se12_fff] at 0x80003794
    all_goals try (intro hc; exact (hc hnz).elim)
    try intro _
    try bc_run hlive hS [] at 0x80003794
    by_cases ht : t = 1
    · have h0 : BitVec.ofNat 64 (t - 1) = 0#64 := by rw [ht]
      bc_run hlive hS [h0] at 0x800037ac
      try bc_run hlive hS [] at 0x800037ac
      refine hk _ pre c g ((b', x') :: post) hall (by subst ht; simp) ?_ ?_ ?_ ?_
      · keeps_tac Keeps.refl _ _
      all_goals bsimp [h12, h14, he, headPtr]
    · have h0 : BitVec.ofNat 64 (t - 1) ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
      bc_run hlive hS [] at 0x800037a0
      all_goals try (intro hc; exact (h0 hc).elim)
      try intro _
      try bc_run hlive hS [] at 0x800037a0
      rw [he] at hl
      refine ih (pre := pre ++ [(c, g)]) (t := t - 1) (by rw [hall, List.append_assoc]; rfl) hl
        (fun bx hm => hb bx (List.mem_cons_of_mem _ hm)) (by omega) (by omega) _ ?_ ?_ ?_
        (fun R' pre' c' g' post' e1 e2 hk1 e4 e5 e6 => hk R' pre' c' g' post' e1 ?_
          (hk1.trans (by keeps_tac Keeps.refl _ _)) e4 e5 e6)
      · bsimp []
      · rw [lastPtr_concat]; bsimp [h14]
      · bsimp []
      · rw [e2]; simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- The walk stopped at the top node: `dc_stack_rotate` returns. -/
theorem rot_top {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) {M : Mem} (R : Nat → BitVec 64)
    (h12 : R 12 = 0#64) (hal : (R 1).toNat % 4 = 0) (hk : DW live S Q (R 1) R M) :
    DW live S Q 0x800037ac#64 R M := by
  bc_run hlive hS [h12] at 0x800037dc
  bc_run hlive hS []
  first | exact hal | exact hk

/-- `n > 0`: the node `c` after `p` moves to the top. -/
theorem rot_up_st {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) (hG : ∀ a, DcGlob a → S a) {M : Mem} {p c : Nat}
    (hp : heapStart + 16 ≤ p ∧ p + 32 ≤ heapEnd ∧ p % 16 = 0)
    (hc : heapStart + 16 ≤ c ∧ c + 32 ≤ heapEnd ∧ c % 16 = 0)
    (R : Nat → BitVec 64) (h10 : 0 < (R 10).toInt) (h12 : R 12 = BitVec.ofNat 64 p)
    (h14 : R 14 = BitVec.ofNat 64 c) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [15] R' R →
      DW live S Q (R 1) R' (rotW M (p + 24) (R 13) (c + 24) (R 11) (BitVec.ofNat 64 c))) :
    DW live S Q 0x800037ac#64 R M := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hc1, hc2, hc3⟩ := hc
  simp only [heapStart, heapEnd] at hp1 hp2 hc1 hc2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hnz : BitVec.ofNat 64 p ≠ 0#64 := ofNat_ne_small (by omega) (by decide) (by omega)
  have hpw : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have hcw : (BitVec.ofNat 64 c).toNat = c := by simp only [BitVec.toNat_ofNat]; omega
  have hpS : ∀ b ∈ accAddrs (p + 24) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hcS : ∀ b ∈ accAddrs (c + 24) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hown : ∀ b ∈ accAddrs dcStackAddr 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs] at this ⊢; omega)
  have e0 : (0#64).toInt = 0 := by decide
  bc_run hlive hS [h12, h14, hpw, hcw] at 0x800037b0
  all_goals try (intro hc; exact (hnz hc).elim)
  try intro _
  bc_run hlive hS [h12, h14, hpw, hcw] at 0x800037b4
  all_goals try (intro hc; exact absurd hc (by omega))
  try intro _
  bc_run hlive hS [h12, h14, hpw, hcw]
  all_goals first | exact hpS | exact hcS | exact hown | (simp only [StOK, dc_addrs, htx]; omega) | exact hal | skip
  exact hk _ (by keeps_tac Keeps.refl _ _)

/-- `n < 0`: the top node `p` moves down after the node `c`. -/
theorem rot_down_st {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) (hS : HeapOwn S) (hG : ∀ a, DcGlob a → S a) {M : Mem} {p c : Nat}
    (hp : heapStart + 16 ≤ p ∧ p + 32 ≤ heapEnd ∧ p % 16 = 0)
    (hc : heapStart + 16 ≤ c ∧ c + 32 ≤ heapEnd ∧ c % 16 = 0)
    (R : Nat → BitVec 64) (h10 : (R 10).toInt ≤ 0) (hnz : R 12 ≠ 0#64) (h11 : R 11 = BitVec.ofNat 64 p)
    (h14 : R 14 = BitVec.ofNat 64 c) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R', Keeps [14, 15] R' R →
      DW live S Q (R 1) R' (rotW M (p + 24) (R 13) (c + 24) (BitVec.ofNat 64 p)
        (ldv .ld M (p + 24)))) :
    DW live S Q 0x800037ac#64 R M := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hc1, hc2, hc3⟩ := hc
  simp only [heapStart, heapEnd] at hp1 hp2 hc1 hc2
  have htx : tohostAddr = 0x8001ad00 := rfl
  have hpw : (BitVec.ofNat 64 p).toNat = p := by simp only [BitVec.toNat_ofNat]; omega
  have hcw : (BitVec.ofNat 64 c).toNat = c := by simp only [BitVec.toNat_ofNat]; omega
  have hpS : ∀ b ∈ accAddrs (p + 24) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hcS : ∀ b ∈ accAddrs (c + 24) 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hS b (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hown : ∀ b ∈ accAddrs dcStackAddr 8, S b := fun b hb => by
    have := of_mem_accAddrs hb
    exact hG b (by simp only [DcGlob, dc_addrs] at this ⊢; omega)
  have e0 : (0#64).toInt = 0 := by decide
  bc_run hlive hS [h11, h14, hpw, hcw] at 0x800037b0
  all_goals try (intro hc; exact (hnz hc).elim)
  try intro _
  bc_run hlive hS [h11, h14, hpw, hcw] at 0x800037c8
  all_goals try (intro hc; exact absurd h10 (by omega))
  try intro _
  try bc_run hlive hS [h11, h14, hpw, hcw] at 0x800037c8
  bc_run hlive hS [h11, h14, hpw, hcw]
  all_goals first | exact hpS | exact hcS | exact hown | (simp only [StOK, LdOK, dc_addrs, htx]; omega) | exact hal | skip
  exact hk _ (by keeps_tac Keeps.refl _ _)

/-! ## The relinked state -/

/-- The stack nodes' payloads: in the heap, 16-aligned, distinct. -/
structure StkGeo (G : DcG) : Prop where
  bnd : ∀ bg ∈ G.stk, heapStart + 16 ≤ bg.1.pay ∧ bg.1.pay + 32 ≤ heapEnd ∧ bg.1.pay % 16 = 0
  nd : (G.stk.map (·.1.pay)).Nodup

theorem DcAt.stkGeo {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) : StkGeo G := by
  have hi := h.heap.heap
  have hsz : ∀ bg ∈ G.stk, 32 ≤ bg.1.sz := fun bg hm => (h.view.stk.forall bg hm).sz
  refine ⟨fun bg hm => h.node_bounds (G.stk_mem hm) (hsz bg hm), ?_⟩
  have hnd := h.nodup
  simp only [DcG.blocks, List.append_assoc] at hnd
  have h1 := (List.nodup_append.mp hnd).1
  have e : G.stk.map (·.1.pay) = (G.stk.map (·.1)).map Blk.pay := by simp [List.map_map]
  rw [e]
  refine nodup_map_on (fun x hx y hy he => Classical.byContradiction fun hne => ?_) h1
  obtain ⟨bx, hbx, rfl⟩ := List.mem_map.mp hx
  obtain ⟨by', hby, rfl⟩ := List.mem_map.mp hy
  have s1 := hsz bx hbx; have s2 := hsz by' hby
  exact live_apart hi (h.heap.raw.live _ (G.stk_mem hbx)) (h.heap.raw.live _ (G.stk_mem hby)) hne
    (a := bx.1.pay) (by simp only [Blk.In, Blk.pay, Blk.fin] at s1 ⊢; omega)
    (by simp only [Blk.In, Blk.pay, Blk.fin] at he s2 ⊢; omega)

theorem StkGeo.seg (g : StkGeo G) : ∀ bx ∈ G.stk, dcStackAddr + 8 ≤ bx.1.pay ∧ bx.1.pay % 16 = 0 :=
  fun bx hm => by
    obtain ⟨h1, -, h3⟩ := g.bnd bx hm
    simp only [heapStart, dcStackAddr] at h1 ⊢; omega

/-- **Up** at the state: the node `c` after `pre0 ++ [lb]` moved to the top. -/
theorem DcAt.rotUp {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {n : Int} {pre0 post : List (Blk × GV)}
    {lb c : Blk} {lg g : GV} (h : DcAt S M H F L C G hs st)
    (hall : G.stk = pre0 ++ (lb, lg) :: (c, g) :: post) (hn : 0 < n)
    (hlen : pre0.length + 1 = min (n.natAbs - 1) (G.stk.length - 1)) :
    DcAt S (rotW M (lb.pay + 24) (headPtr post) (c.pay + 24) (ldv .ld M dcStackAddr)
        (BitVec.ofNat 64 c.pay)) H F L C { G with stk := (c, g) :: (pre0 ++ (lb, lg) :: post) } hs
      { st with stack := rotate n st.stack } := by
  have geo := h.stkGeo
  have hseg := h.view.stk.toSeg
  rw [hall] at hseg
  have hgeo := geo.seg
  have hnd := geo.nd
  rw [hall] at hgeo hnd
  have hp : ((c, g) :: (pre0 ++ (lb, lg) :: post)).Perm G.stk := by
    rw [hall, show pre0 ++ (lb, lg) :: (c, g) :: post = (pre0 ++ [(lb, lg)]) ++ (c, g) :: post by simp,
      show pre0 ++ (lb, lg) :: post = (pre0 ++ [(lb, lg)]) ++ post by simp]
    exact List.perm_middle.symm
  have hch := PSeg.toL (a := dcStackAddr) (by rw [rotW_ld3]; exact rot_chain_up hseg hgeo hnd)
  have hd := h.den.stk
  rw [hall, show pre0 ++ (lb, lg) :: (c, g) :: post = (pre0 ++ [(lb, lg)]) ++ (c, g) :: post by simp]
    at hd
  obtain ⟨m1, m2, e, h1, h2⟩ := forall₂_split hd
  cases h2 with
  | cons hc h2' =>
  rename_i vc m2'
  have l1 := h1.length_eq
  have l2 := h2'.length_eq
  simp only [List.length_append, List.length_cons, List.length_nil] at l1
  have hrot : rotate n st.stack = vc :: (m1 ++ m2') := by
    rw [e]
    refine rotate_up hn ?_ (List.length_pos_iff.mp (by omega))
    rw [hall] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    omega
  rw [hrot]
  exact h.permStk hp (rotW_only ⟨(lb, lg), by rw [hall]; simp, rfl⟩ ⟨(c, g), by rw [hall]; simp, rfl⟩)
    hch (.cons hc (by
      rw [show pre0 ++ (lb, lg) :: post = (pre0 ++ [(lb, lg)]) ++ post by simp]
      exact forall₂_append h1 h2'))

/-- **Down** at the state: the top node `top` moved after `mid ++ [c]`. -/
theorem DcAt.rotDown {S : Nat → Prop} {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} {n : Int} {mid post : List (Blk × GV)}
    {top c : Blk} {gt g : GV} (h : DcAt S M H F L C G hs st)
    (hall : G.stk = (top, gt) :: (mid ++ (c, g) :: post)) (hn : n < 0) (hmin : n ≠ -2147483648)
    (hlen : mid.length + 1 = min (n.natAbs - 1) (G.stk.length - 1)) :
    DcAt S (rotW M (top.pay + 24) (headPtr post) (c.pay + 24) (BitVec.ofNat 64 top.pay)
        (ldv .ld M (top.pay + 24))) H F L C { G with stk := mid ++ (c, g) :: (top, gt) :: post } hs
      { st with stack := rotate n st.stack } := by
  have geo := h.stkGeo
  have hseg := h.view.stk.toSeg
  rw [hall] at hseg
  have hw := hseg.uncons.1
  rw [hw] at hseg
  have hgeo := geo.seg
  have hnd := geo.nd
  rw [hall] at hgeo hnd
  have hp : (mid ++ (c, g) :: (top, gt) :: post).Perm G.stk := by
    rw [hall, show mid ++ (c, g) :: (top, gt) :: post = (mid ++ [(c, g)]) ++ (top, gt) :: post by simp,
      show mid ++ (c, g) :: post = (mid ++ [(c, g)]) ++ post by simp]
    exact List.perm_middle
  have hch := PSeg.toL (a := dcStackAddr) (by rw [rotW_ld3]; exact rot_chain_down hseg hgeo hnd)
  have hd := h.den.stk
  rw [hall] at hd
  generalize hsk : st.stack = sk at hd
  cases hd with
  | cons ht hd' =>
  rename_i vt ms
  obtain ⟨m1, m2, e, h1, h2⟩ := forall₂_split hd'
  cases h2 with
  | cons hc h2' =>
  rename_i vc m2'
  have l1 := h1.length_eq
  have l2 := h2'.length_eq
  have hrot : rotate n (vt :: ms) = m1 ++ vc :: vt :: m2' := by
    rw [e]
    refine rotate_down hn hmin ?_
    rw [hall] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    omega
  rw [hrot]
  exact h.permStk hp (rotW_only ⟨(top, gt), by rw [hall]; simp, rfl⟩ ⟨(c, g), by rw [hall]; simp, rfl⟩)
    hch (forall₂_append h1 (.cons hc (.cons ht h2')))

theorem toInt_ofInt32 {n : Int} (h1 : -2147483648 ≤ n) (h2 : n < 2147483648) :
    (BitVec.ofInt 64 n).toInt = n := by
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem absw_int {n : Int} (h1 : -2147483648 < n) (h2 : n < 2147483648) :
    absw (BitVec.ofInt 64 n) = BitVec.ofNat 64 n.natAbs := by
  obtain ⟨k, e | e⟩ := Int.eq_nat_or_neg n <;> subst e
  · have e1 : BitVec.ofInt 64 (k : Int) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [e1, Int.natAbs_natCast]; exact absw_pos (by omega)
  · rw [Int.natAbs_neg, Int.natAbs_natCast]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absw_pos (k := 0) (by decide)
    · exact absw_neg hk (by omega)

/-! ## The function -/

/-- After the walk (`0x800037ac`): the node `c'` after `pre'` is the one to
move; the stores relink the stack as `rotate n` says. -/
theorem rot_after {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) {n : Int}
    (hn1 : -2147483648 < n) (hn2 : n < 2147483648) (ht : 2 ≤ n.natAbs)
    {pre' post' : List (Blk × GV)} {c' : Blk} {g' : GV} (hall : G.stk = pre' ++ (c', g') :: post')
    (hl : pre'.length = min (n.natAbs - 1) (G.stk.length - 1))
    (R R2 : Nat → BitVec 64) (hk2 : Keeps rotClob R2 R) (e10 : R2 10 = BitVec.ofInt 64 n)
    (e11 : R2 11 = ldv .ld M dcStackAddr) (e12 : R2 12 = lastPtr pre') (e13 : R2 13 = headPtr post')
    (e14 : R2 14 = BitVec.ofNat 64 c'.pay) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' l', Keeps rotClob R' R → l'.Perm G.stk → MemOnly (StkLinks G) M' M →
      DcAt S M' H F L C { G with stk := l' } hs { st with stack := rotate n st.stack } →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x800037ac#64 R2 M := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have geo := h.stkGeo
  have e1 : R2 1 = R 1 := hk2 1 (by decide)
  have hal2 : (R2 1).toNat % 4 = 0 := by rw [e1]; exact hal
  have hti := toInt_ofInt32 (by omega) hn2
  have hlen := h.den.stk.length_eq
  have hmem : ∀ bx ∈ pre' ++ (c', g') :: post', bx ∈ G.stk := fun bx hm => by rw [hall]; exact hm
  have gc := geo.bnd (c', g') (hmem _ (by simp))
  dsimp only at gc
  rcases List.eq_nil_or_concat pre' with hp0 | ⟨pre0, ⟨lb, lg⟩, hp0⟩
  -- the top node: nothing moves
  · subst hp0
    refine rot_top hlive hS R2 (by rw [e12]; rfl) hal2 ?_
    rw [e1]
    refine hk R2 M G.stk hk2 (List.Perm.refl _) (fun _ _ => rfl) ?_
    rw [rotate_small (.inr (.inr (by simp only [List.length_nil] at hl; omega)))]
    exact h
  simp only [List.concat_eq_append] at hp0
  subst hp0
  have glb := geo.bnd (lb, lg) (hmem _ (by simp))
  dsimp only at glb
  simp only [heapStart, heapEnd] at glb
  have hall' : G.stk = pre0 ++ (lb, lg) :: (c', g') :: post' := by rw [hall]; simp
  have hlen' : pre0.length + 1 = min (n.natAbs - 1) (G.stk.length - 1) := by
    rw [← hl]; simp
  rcases Int.lt_or_gt_of_ne (show n ≠ 0 by omega) with hneg | hpos
  -- `n < 0`: the top node moves down
  · obtain ⟨⟨top, gt⟩, mid, hpm⟩ : ∃ tg mid, pre0 ++ [(lb, lg)] = tg :: mid :=
      List.exists_cons_of_ne_nil (by simp)
    have hall2 : G.stk = (top, gt) :: (mid ++ (c', g') :: post') := by rw [hall, hpm]; rfl
    have gt' := geo.bnd (top, gt) (by rw [hall2]; simp)
    dsimp only at gt'
    have hw : ldv .ld M dcStackAddr = BitVec.ofNat 64 top.pay := by
      rw [h.view.stk.toSeg.head, hall2]; rfl
    have hlen2 : mid.length + 1 = min (n.natAbs - 1) (G.stk.length - 1) := by
      rw [← hlen', ← List.length_cons, ← hpm]; simp
    refine rot_down_st hlive hS hG gt' gc R2 (by rw [e10, hti]; omega)
      (by
        rw [e12, lastPtr_concat]
        exact (ofNat_ne_small (b := 0) (by omega) (by decide) (by omega) : BitVec.ofNat 64 lb.pay ≠ _))
      (by rw [e11, hw]) e14 hal2 fun R3 hk3 => ?_
    rw [e1, e13]
    refine hk R3 _ (mid ++ (c', g') :: (top, gt) :: post') ((hk3.mono (by decide)).trans hk2) ?_
      (rotW_only ⟨(top, gt), by rw [hall2]; simp, rfl⟩ ⟨(c', g'), by rw [hall2]; simp, rfl⟩)
      (h.rotDown hall2 hneg (by omega) hlen2)
    rw [hall2, show mid ++ (c', g') :: (top, gt) :: post' = (mid ++ [(c', g')]) ++ (top, gt) :: post' by simp,
      show mid ++ (c', g') :: post' = (mid ++ [(c', g')]) ++ post' by simp]
    exact List.perm_middle
  -- `n > 0`: the node `c'` moves to the top
  · refine rot_up_st hlive hS hG glb gc R2 (by rw [e10, hti]; omega) (by rw [e12, lastPtr_concat]) e14
      hal2 fun R3 hk3 => ?_
    rw [e1, e13, e11]
    refine hk R3 _ ((c', g') :: (pre0 ++ (lb, lg) :: post')) ((hk3.mono (by decide)).trans hk2) ?_
      (rotW_only ⟨(lb, lg), by rw [hall']; simp, rfl⟩ ⟨(c', g'), by rw [hall']; simp, rfl⟩)
      (h.rotUp hall' hpos hlen')
    rw [hall', show pre0 ++ (lb, lg) :: (c', g') :: post' = (pre0 ++ [(lb, lg)]) ++ (c', g') :: post' by simp,
      show pre0 ++ (lb, lg) :: post' = (pre0 ++ [(lb, lg)]) ++ post' by simp]
    exact List.perm_middle.symm

/-- **`dc_stack_rotate (n)`** at `0x80003768`, `n` an `int` in `a0`: the
stack becomes `rotate n`, its nodes relinked in place; only `dc_stack` and the
nodes' link words change. -/
theorem dc_stack_rotate_spec {live S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ dcText, live p.1) {M : Mem} {H : Heap} {F : List Blk} {L : List NumObj}
    {C : BcConsts} {G : DcG} {hs : List GV} {st : St} (h : DcAt S M H F L C G hs st) {n : Int}
    (hn1 : -2147483648 ≤ n) (hn2 : n < 2147483648)
    (R : Nat → BitVec 64) (h10 : R 10 = BitVec.ofInt 64 n) (hal : (R 1).toNat % 4 = 0)
    (hk : ∀ R' M' l', Keeps rotClob R' R → l'.Perm G.stk → MemOnly (StkLinks G) M' M →
      DcAt S M' H F L C { G with stk := l' } hs { st with stack := rotate n st.stack } →
      DW live S Q (R 1) R' M') :
    DW live S Q 0x80003768#64 R M := by
  have hS : HeapOwn S := fun a h1 h2 => h.heap.heap.own a h1 h2
  have hG := h.glob
  have geo := h.stkGeo
  have hlen := h.den.stk.length_eq
  have hhd := h.view.stk.toSeg.head
  have hsame : ∀ R', Keeps rotClob R' R → rotate n st.stack = st.stack → DW live S Q (R 1) R' M :=
    fun R' hk1 he => hk R' M G.stk hk1 (List.Perm.refl _) (fun _ _ => rfl) (by rw [he]; exact h)
  by_cases hmin : n = -2147483648
  · subst hmin
    refine rot_entry hlive hS hG R (a := 0xffffffff80000000#64) (by rw [h10]; exact absw_min) rfl hal
      (fun R' _ hk1 => hsame R' hk1 (rotate_small (.inr (.inl rfl)))) fun R' _ hc _ _ _ _ _ => ?_
    exact absurd (by decide) hc
  have hti : n.natAbs < 2 ^ 31 := by omega
  have ctn : (BitVec.ofNat 64 n.natAbs).toInt = n.natAbs := toInt_ofNat_small (by omega)
  refine rot_entry hlive hS hG R (a := BitVec.ofNat 64 n.natAbs)
    (by rw [h10]; exact absw_int (by omega) hn2) rfl hal
    (fun R' hc hk1 => hsame R' hk1 (rotate_small ?_)) fun R' hw0 hc hk1 h11 h14 h12 h15 => ?_
  · rcases hc with hc | hc
    · refine .inr (.inr ?_)
      rw [hhd] at hc
      cases hgs : G.stk with
      | nil => rw [hgs] at hlen; simp at hlen; omega
      | cons bx post0 =>
        have gb := geo.bnd bx (by rw [hgs]; simp)
        rw [hgs] at hc
        exact absurd hc (ofNat_ne_small (b := 0) (by simp only [heapEnd] at gb; omega) (by decide)
          (by simp only [heapStart] at gb; omega))
    · rw [ctn] at hc; exact .inl (by omega)
  rw [ctn] at hc
  rw [hhd] at hw0 h11 h14
  cases hgs : G.stk with
  | nil => rw [hgs] at hw0; exact absurd rfl hw0
  | cons bx post0 =>
  obtain ⟨c0, g0⟩ := bx
  rw [hgs] at h11 h14
  have hch := h.view.stk.toP
  rw [hhd, hgs] at hch
  refine rot_walk hlive hS (all := G.stk) (pre := []) (hgs.trans rfl) hch
    (fun bx hm => geo.bnd bx (by rw [hgs]; exact hm)) (by omega) (by omega) R' h14 h12 h15
    fun R2 pre' c' g' post' hall hl hk2 e14 e12 e13 => ?_
  have e2 : ∀ z ∈ [10, 11], R2 z = R' z := fun z hz => hk2 z (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; rcases hz with rfl | rfl <;> decide)
  refine rot_after hlive h (by omega) hn2 (by omega) hall (by rw [hl, hgs]; simp) R R2
    ((hk2.mono (by decide)).trans hk1) (by rw [e2 10 (by simp), hk1 10 (by decide), h10])
    (by rw [e2 11 (by simp), h11, hhd, hgs]) e12 e13 e14 hal hk

end Dc.Mach
