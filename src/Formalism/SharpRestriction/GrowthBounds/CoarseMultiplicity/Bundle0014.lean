module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0013
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0010

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFTrueDeg
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem ioBlock_wh' (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (b : SegBlock (segS X.TT j) X.m)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ l : Fin (X.seg C0 CE1 CE2 j).t,
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) + ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), 0) =
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), Fin.succ 0) +
        ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0))
    (s : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O))
    (hs : ∀ (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ),
      Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL → IsWeightedHomogeneous ω' s
        (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω' ωL)) :
    IsWeightedHomogeneous ω (ioBlock (KK O) X.p C0 CE1 CE2 X j b s) (TD C0 CE1 CE2 X j b ω) := by
  let ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ := fun v => symLev X.p C0 CE1 CE2 X j v * ω (symVar C0 CE1 CE2 X j v)
  let ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => ω' (Sum.inl (a, 0))
  have h1 : ∀ a c, ω' (Sum.inl (a, c)) = ωL a := by
    intro a c
    simp only [ω', ωL, symLev, symVar]
    split_ifs <;> rw [hc _ c 0]
  have e0 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ)) =
      Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val) (2 * segS X.TT j + 1) = 2 * i.val
    omega
  have e1 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ) + 1) =
      Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val + 1) (2 * segS X.TT j + 1) = 2 * i.val + 1
    omega
  have hW : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [symbol_variable_lower_letter, symbol_level_lower_letter]
  have hE : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [sv_E, sl_E]
  have hUU : ωL (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      ω ((topEnd X j, true), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_U, sl_U, one_mul]
  have hXi : ωL (Fin.last _) = ω ((topEnd X j, false), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_xi, sl_xi, one_mul]
  have hZ : ∀ (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool), ω' (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) * ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
    intro l β
    simp only [ω']
    rw [sv_Z, sl_Z]
  have hx : ∀ β : Bool, ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, β)) = ω ((topEnd X j, !β), 0) := by
    intro β
    simp only [ω']
    rw [symbol_variable_last, symbol_level_last, one_mul]
  have h2 : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, ω' (Sum.inr (Fin.castSucc l, false)) + ω' (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) + ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1)) := by
    intro l
    rw [hZ, hZ, e0, e1, hW, hE, ← mul_add, ← mul_add]
    congr 1
    exact hU l
  have h3 : ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) + ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, true)) =
      ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _) := by
    rw [hx, hx, hUU, hXi]
    exact hP
  have hS := hs ω' ωL ⟨h1, h2, h3⟩
  have hA := wh_aeval ω (symVar C0 CE1 CE2 X j) (symLev X.p C0 CE1 CE2 X j) s _ hS
  have hDg : IsWeightedHomogeneous ω (digitMon (KK O) C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
        (b.rz i c • ω ((topOdd X j i, true), c) + b.ry i c • ω ((topOdd X j i, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)))
  have hSt : IsWeightedHomogeneous ω (sTopMon (KK O) X.p C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) • ω ((topOdd X j i, true), 0) +
          ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i) • ω ((topOdd X j i, false), 0) else 0) := by
    refine IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?_)
    split_ifs
    · exact ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)
    · exact isWeightedHomogeneous_one _ _
  have hall := (hDg.mul hSt).mul hA
  refine wh_congr hall ?_
  have E1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) - b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ω' (Sum.inr (Fin.castSucc l, false)) =
      ∑ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0 := by
    rw [← sum_uTop (X.seg C0 CE1 CE2 j) (fun i => (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hZ]
    rfl
  have E3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      b.oPlus * ω ((topEnd X j, true), Fin.succ 0) := by
    rw [sum_chain, hUU, chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE, segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl, chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl]
  unfold OmB TD
  rw [E1, E3, hx, hXi]
  simp only [smul_eq_mul, Bool.not_false]
  have key : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0))) =
      (∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          (X.seg C0 CE1 CE2 j).P X.p i * b.sg i * ω ((topOdd X j i, false), 0) else 0) +
      (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0) +
      ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    intro i
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, if_neg (not_le.2 h), if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_pos (not_lt.1 h), if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp only [Finset.sum_add_distrib]
  ring

theorem leading_exponent_weighted_homog (b : SegBlock (segS X.TT j) X.m) (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ)
    (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ) (hB : Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL) :
    IsWeightedHomogeneous ω' (monomial (mu0 C0 CE1 CE2 X j b) (1 : KK ℤ))
      (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω' ωL) := by
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω' i) (fun _ => zero_smul _ _)]
  simpa [smul_eq_mul] using leading_exponent_homogeneous C0 CE1 CE2 X j b ω' ωL hB

theorem tdeg_eq (b : SegBlock (segS X.TT j) X.m) (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (ho : b.oPlus ≤ segAPlus X.TT X.aT j) (x : X.TT × Bool) :
    tdeg C0 CE1 CE2 X j b x = (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  have hwh := ioBlock_wh' C0 CE1 CE2 X j ℤ 0 b (wLet X x) (fun _ _ _ => rfl) (fun _ => rfl) rfl
    (monomial (mu0 C0 CE1 CE2 X j b) 1) (fun ω' ωL hB => leading_exponent_weighted_homog C0 CE1 CE2 X j b ω' ωL hB)
  rw [ioBlock_monomial] at hwh
  have h1 := hwh (by rw [coeff_monomial, if_pos rfl]; exact one_ne_zero)
  rw [weight_wLet] at h1
  unfold tdeg
  rw [h1, TD_wLet C0 CE1 CE2 X j x b hk ho]

theorem segPos_inj : Function.Injective (segPos X.TT j) := by
  intro i i' h
  exact topOdd_inj X j (Subtype.ext h)

@[to_additive]
theorem prod_tdeg {M : Type} [CommMonoid M] (g : ℕ → M) (hg : g 0 = 1) (b : SegBlock (segS X.TT j) X.m)
    (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (ho : b.oPlus ≤ segAPlus X.TT X.aT j) :
    ∏ x : X.TT × Bool, g (tdeg C0 CE1 CE2 X j b x) =
      (∏ i : Fin (segS X.TT j), g (X.bT (segPos X.TT j i)) * g (X.aT (segPos X.TT j i))) *
        g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j)) := by
  classical
  set T : Fin X.n' → Bool → ℕ := fun t β => (if segNext X.TT j = t then hhDeg X.aT X.bT t β else 0) +
    ∑ i, (if segPos X.TT j i = t then hhDeg X.aT X.bT t β else 0) with hT
  have e : ∀ x : X.TT × Bool, tdeg C0 CE1 CE2 X j b x = T x.1.val x.2 := fun x => tdeg_eq C0 CE1 CE2 X j b hk ho x
  simp only [e]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  rw [Finset.prod_coe_sort X.TT (fun t => g (T t true) * g (T t false))]
  have hnp : ∀ i, segPos X.TT j i ≠ segNext X.TT j := fun i h => (pos_mem X.TT j i).2 (h ▸ (next_mem X.TT j).2)
  have hS : insert (segNext X.TT j) (Finset.univ.image (segPos X.TT j)) ⊆ X.TT := by
    intro t ht
    rcases Finset.mem_insert.1 ht with h | h
    · rw [h]; exact (next_mem X.TT j).1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 h
      exact (pos_mem X.TT j i).1
  rw [← Finset.prod_subset hS (fun t _ ht => by
    have h1 : segNext X.TT j ≠ t := fun h => ht (h ▸ Finset.mem_insert_self _ _)
    have h2 : ∀ i, segPos X.TT j i ≠ t := fun i h => ht (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩))
    simp only [hT, if_neg h1, if_neg (h2 _), Finset.sum_const_zero, add_zero, hg, mul_one])]
  rw [Finset.prod_insert (fun h => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
    exact hnp i hi), Finset.prod_image (fun i _ i' _ h => segPos_inj X j h)]
  have hnext : ∀ β, T (segNext X.TT j) β = hhDeg X.aT X.bT (segNext X.TT j) β := by
    intro β
    show (if segNext X.TT j = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) +
      ∑ i, (if segPos X.TT j i = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) = _
    rw [if_pos rfl, Finset.sum_eq_zero (fun i _ => if_neg (hnp i)), add_zero]
  have hpos : ∀ i β, T (segPos X.TT j i) β = hhDeg X.aT X.bT (segPos X.TT j i) β := by
    intro i β
    show (if segNext X.TT j = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) +
      ∑ i', (if segPos X.TT j i' = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) = _
    rw [if_neg (fun h : segNext X.TT j = segPos X.TT j i => hnp i h.symm), zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (fun h => hi' (segPos_inj X j h))) (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl]
  have hev := (next_mem X.TT j).2
  simp only [hnext, hpos, hhDeg, if_true, Bool.false_eq_true, if_false, if_pos hev]
  have hodd : ∀ i, ¬ Even (segPos X.TT j i).val := fun i => (pos_mem X.TT j i).2
  simp only [hodd, if_false]
  rw [mul_comm (g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j))), mul_assoc]

end

theorem trueDegAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD1 hH hc j b hb
  have ho := hO X hD1 hH hc j b hb
  constructor
  · rw [prod_tdeg C0 CE1 CE2 X j Nat.factorial rfl b hb ho]
    rfl
  · rw [sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]
    unfold lgSeg
    rw [Finset.sum_add_distrib]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Imports
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def ωoL (l0 : Fin (X.seg C0 CE1 CE2 j).t) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if (a : ℕ) = 2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ) then 1 else 0

def ωo (l0 : Fin (X.seg C0 CE1 CE2 j).t) : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωoL C0 CE1 CE2 X j l0 a
  | Sum.inr (l, β) => if (l : ℕ) = (l0 : ℕ) ∧ β = true then 1 else 0

def ωpL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => if (a : ℕ) = 2 * segS X.TT j then 1 else 0

def ωp : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωpL X j a
  | Sum.inr (l, β) => if (l : ℕ) = (X.seg C0 CE1 CE2 j).t ∧ β = true then 1 else 0

theorem ωo_bal (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    Balanced X.m (X.seg C0 CE1 CE2 j) (ωo C0 CE1 CE2 X j l0) (ωoL C0 CE1 CE2 X j l0) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have hu : ∀ l' : Fin (X.seg C0 CE1 CE2 j).t, ((uTop (X.seg C0 CE1 CE2 j) l' : Fin _) : ℕ) =
        (X.seg C0 CE1 CE2 j).sigma + l' := fun _ => rfl
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωo, ωoL, v0, v1, Fin.val_castSucc]
    by_cases hl : (l : ℕ) = (l0 : ℕ)
    · rw [if_neg (by simp), if_pos (by simp [hl]), if_pos (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
    · rw [if_neg (by simp), if_neg (by simp [hl]), if_neg (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
    simp only [ωo, ωoL, Fin.val_castSucc, Fin.val_last]
    rw [if_neg (by simp), if_neg (by intro h; have := l0.2; omega), if_neg (by omega), if_neg (by omega)]

theorem ωp_bal : Balanced X.m (X.seg C0 CE1 CE2 j) (ωp C0 CE1 CE2 X j) (ωpL X j) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωp, ωpL, v0, v1, Fin.val_castSucc]
    rw [if_neg (by simp), if_neg (by intro h; have := l.2; omega), if_neg (by omega), if_neg (by omega)]
  · simp only [ωp, ωpL, Fin.val_castSucc, Fin.val_last]
    simp

theorem omB_ωo (b : SegBlock (segS X.TT j) X.m) (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωo C0 CE1 CE2 X j l0)
      (ωoL C0 CE1 CE2 X j l0) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
  classical
  have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωo]
  have s2 : ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.last _, false)) = 0 := by simp [ωo]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωoL C0 CE1 CE2 X j l0 (Fin.castSucc a) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
    rw [Finset.sum_eq_single (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ), by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωoL, Fin.val_castSucc, if_true, mul_one]
      rw [segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ (uTop (X.seg C0 CE1 CE2 j) l0) rfl,
        if_neg (by show ¬ ((X.seg C0 CE1 CE2 j).sigma + (l0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma); omega)]
    · intro a _ ha
      simp only [ωoL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωoL C0 CE1 CE2 X j l0 (Fin.last _) = 0 := by
    simp only [ωoL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

theorem omB_ωp (b : SegBlock (segS X.TT j) X.m) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωp C0 CE1 CE2 X j) (ωpL X j) = b.oPlus := by
  classical
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωp C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωp]
  have s2 : ωp C0 CE1 CE2 X j (Sum.inr (Fin.last _, false)) = 0 := by simp [ωp]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωpL X j (Fin.castSucc a) = b.oPlus := by
    rw [Finset.sum_eq_single (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωpL, Fin.val_castSucc, if_true, mul_one]
      exact chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl
    · intro a _ ha
      simp only [ωpL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωpL X j (Fin.last _) = 0 := by
    simp only [ωpL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Loc4DivOf
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def psiRes (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    O ⧸ Ideal.span {w} :=
  Ideal.Quotient.mk (Ideal.span {w}) (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ 0 a))

def LocalResidueBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      psiRes X O S.w g j0 0 = 0 ∨ ∃ c : Fin X.m,
        ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j 0 ^ (X.p ^ segG X.TT j - 1) =
          ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j c.succ ^ (X.p ^ segG X.TT j - 1)

theorem map_xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    map (Ideal.Quotient.mk (Ideal.span {w})) (xvL X O w g j a) =
      C (psiRes X O w g j a) * MvPolynomial.X ((topStart X j, true), 0) := by
  have hw0 : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
  unfold xvL psiRes
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single 0]
  · simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters]
    try ring
  · intro b _ hb
    have hb1 : 1 ≤ b.val := Nat.one_le_iff_ne_zero.mpr (fun h => hb (Fin.ext h))
    simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters, hb1, hw0]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem loc4Div_of (h : LocalResidueBound) : LocalDivisibilityBound := by
  intro X _ O _ _ _ _ S hS hD hn j0 g hg hne
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk (Ideal.span {S.w})) S.w
    (fun x => by rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton])]
  unfold locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, map_xvL]
  rcases h X O S hS hD hn j0 g hg hne with h0 | ⟨c, hc⟩
  · rw [h0]
    simp
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [hc, sub_self]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

