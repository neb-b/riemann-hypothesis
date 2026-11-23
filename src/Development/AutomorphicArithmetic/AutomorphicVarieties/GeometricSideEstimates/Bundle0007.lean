module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianGaussianMomentBound
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem entry_mem {E : Type} [Field E] [NumberField E] {a : ℕ} (l m : Fin a) (w : InfinitePlace E) :
    (fun x : Fin a → Cinf E => star (x l w) * x m w) ∈ poly E a := by
  have h1 : (fun x : Fin a → Cinf E => star (x l w)) ∈ poly E a :=
    Algebra.subset_adjoin ⟨⟨⟨fun x => star (x l w), fun x y => by simp⟩, fun c x => by simp⟩, rfl⟩
  have h2 : (fun x : Fin a → Cinf E => x m w) ∈ poly E a :=
    Algebra.subset_adjoin ⟨⟨⟨fun x => x m w, fun x y => by simp⟩, fun c x => by simp⟩, rfl⟩
  exact Subalgebra.mul_mem _ h1 h2

private theorem gauss_unit {E : Type} [Field E] [NumberField E] {a : ℕ} (k : Kinf E a) (x : Fin a → Cinf E) :
    gauss (x ᵥ* k.1) = gauss x := by
  obtain ⟨h1, -, h3, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  unfold gauss
  rw [h3, k.2.2, h1]

private theorem mom_cpt {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a)
    (L : AddSubgroup (Fin a → Af E)) (hL : IsLat L) (k : Kinf E a) (g : GA E a) :
    (mom L (g * infGL E a (Unitary.toUnits k))).1 = star k.1 * (mom L g).1 * k.1 := by
  ext i j w
  have hs := fun l m => ((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).2 _ (entry_mem l m w)).1 g
  have hT := (UpperTheory.lattice_point_count_bound E a ha L).2.2 k g
  have hg := (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ (pg fun x => star (x i w) * x j w)).2.1 g (Unitary.toUnits k)
  have hk : sc (Unitary.toUnits k).val = 1 := (UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k
  have hv : (Unitary.toUnits k).val = k.1 := rfl
  have hp : ∀ x : Fin a → Cinf E, pg (fun x => star (x i w) * x j w) (x ᵥ* k.1) =
      ∑ m, ∑ l, star (k.1 l i w) * pg (fun x => star (x l w) * x m w) x * k.1 m j w := fun x => by
    simp only [pg, gauss_unit, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.mul_apply, star_sum, star_mul',
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hk, hv] at hg
  simp only [one_smul, hp] at hg
  rw [Summable.tsum_finsetSum fun m _ => summable_sum fun l _ => ((hs l m).mul_left _).mul_right _] at hg
  change mean L (fun x => star (x i w) * x j w) _ = _
  rw [mean, hT, hg]
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Finset.sum_mul, Finset.sum_div, Matrix.star_apply,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Summable.tsum_finsetSum fun l _ => ((hs l m).mul_left _).mul_right _, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_right, tsum_mul_left]
  change _ = _ * (gsum L (pg fun x => star (x l w) * x m w) g / _) * _
  rw [gsum]
  ring

private theorem ell_toL {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

theorem UpperTheory.hermitian_gaussian_moment_bound :
    DevCpt := by
  intro E _ _ _ a ha L hL k g
  have hm := mom_cpt ha L hL k g
  have hk : k.1 * star k.1 = 1 := k.2.2
  have he : ell E a (toL (mom L (g * infGL E a (Unitary.toUnits k))).1) = ell E a (toL (mom L g).1) := by
    rw [hm, ell_toL, ell_toL, Matrix.trace_mul_cycle, hk, one_mul]
  apply Subtype.ext
  change k.1 * ((mom L _).1 - _ • (1 : Matrix (Fin a) (Fin a) (Cinf E))) * star k.1 =
    (mom L g).1 - _ • (1 : Matrix (Fin a) (Fin a) (Cinf E))
  rw [he, hm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hk, ← mul_assoc, ← mul_assoc, hk, one_mul,
    mul_assoc, hk, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceLogEstimate
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic

private theorem log_bound {T D C H q : ℝ} {N M : ℕ} (hT : 1 ≤ T) (hC : 1 ≤ C) (hH : 1 ≤ H) (hq : 1 ≤ q)
    (hHq : H ≤ 2 * q) (h : T ≤ D / ((C * H ^ N)⁻¹) ^ M) :
    Real.log T ≤ (|Real.log D| + M * Real.log C + M * N) * (1 + Real.log q) := by
  have hC0 : 0 < C := one_pos.trans_le hC
  have hH0 : 0 < H := one_pos.trans_le hH
  have hq0 : 0 < q := one_pos.trans_le hq
  rw [inv_pow, div_inv_eq_mul] at h
  have hp : 0 < (C * H ^ N) ^ M := by positivity
  have hD : 0 < D := (mul_pos_iff_of_pos_right hp).1 (one_pos.trans_le (hT.trans h))
  have h1 : Real.log T ≤ Real.log D + M * (Real.log C + N * Real.log H) := by
    have := Real.log_le_log (one_pos.trans_le hT) h
    rwa [Real.log_mul hD.ne' hp.ne', Real.log_pow, Real.log_mul hC0.ne' (by positivity), Real.log_pow] at this
  have h2 : Real.log H ≤ 1 + Real.log q := by
    have := Real.log_le_log hH0 hHq
    rw [Real.log_mul two_ne_zero hq0.ne'] at this
    have h3 := Real.log_le_sub_one_of_pos (two_pos (α := ℝ))
    linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  have h4 : (M : ℝ) * N * Real.log H ≤ M * N * (1 + Real.log q) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : 0 ≤ (|Real.log D| + M * Real.log C) * Real.log q := by positivity
  have h6 := le_abs_self (Real.log D)
  nlinarith

theorem UpperTheory.hermitian_space_log_estimate :
    FnLe := by
  intro E _ _ _ a ha L hL
  obtain ⟨C, N, hC, hmin⟩ := UpperTheory.global_geometric_estimate_of_local E a ha L hL
  obtain ⟨M, hsc⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨D, -, hup⟩ := UpperTheory.geometric_side_upper_bound M
  obtain ⟨-, hrt, hγ, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  obtain ⟨hTh, -⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  refine ⟨|Real.log D| + M * Real.log C + M * N, fun g => ?_⟩
  have hq : 1 ≤ qht g := (UpperTheory.V.Lit.Geo.qhtFacts E a).1 g
  obtain ⟨γ, hlt⟩ := exists_lt_of_ciInf_lt (show qht g < 2 * qht g by linarith)
  change AutomorphicForm.height (K := E) (ratGL E a γ * rt g) < _ at hlt
  have hH := AutomorphicForm.one_le_height (K := E) (ratGL E a γ * rt g)
  have hCH : 1 ≤ C * AutomorphicForm.height (K := E) (ratGL E a γ * rt g) ^ N :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hH)
  refine log_bound (hTh g).1 hC hH hq hlt.le ?_
  refine hup _ _ (0 : lat L g) _ (hsc g) (inv_pos.2 (one_pos.trans_le hCH)) (inv_le_one_of_one_le₀ hCH) fun v hv => ?_
  have e : (v.1 ᵥ* (γ⁻¹).val) ᵥ* γ.val = v.1 := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hw := hγ γ (rt g) (v.1 ᵥ* (γ⁻¹).val)
  rw [e, (hrt g).2.2] at hw
  have h1 := hmin (ratGL E a γ * rt g) (v.1 ᵥ* (γ⁻¹).val)
    (by
      change ptF _ _ ∈ L
      rw [hw.1]
      exact v.2)
    (fun h0 => hv (Subtype.ext (by
      rw [← e, h0, Matrix.zero_vecMul]
      rfl)))
  rw [hw.2] at h1
  rw [inv_le_iff_one_le_mul₀' (one_pos.trans_le hCH)]
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity
section
open UpperTheory.V.Lit.Geo
open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

theorem UpperTheory.hermitian_space_moment_identity :
    MomQuad := by
  intro E _ _ _ a ha L hL g p
  obtain ⟨-, h2⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  have hP : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E),
      (fun x : Fin a → Cinf E => star (x i w) * x j w) ∈ poly E a := by
    intro i j w
    have h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => star (x i w)
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }, rfl⟩
    have h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a :=
      Algebra.subset_adjoin ⟨
        { toFun := fun x => x j w
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl }, rfl⟩
    exact (poly E a).mul_mem h1 h2
  have hS : ∀ (w : NumberField.InfinitePlace E) (i j : Fin a), HasSum
      (fun v : lat L g => (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) (pt (rt g) v.1) * p j i w).re)
      (gsum L (pg (fun x : Fin a → Cinf E => star (x i w) * x j w)) g * p j i w).re := by
    intro w i j
    exact Complex.hasSum_re ((((h2 _ (hP i j w)).1 g).hasSum).mul_right (p j i w))
  have hT := hasSum_sum (s := Finset.univ) fun w _ => hasSum_sum (s := Finset.univ) fun i _ =>
    hasSum_sum (s := Finset.univ) fun j _ => hS w i j
  have hq : ∀ x : Fin a → Cinf E, quad p x * gauss x = ∑ w : NumberField.InfinitePlace E, ∑ i, ∑ j,
      (pg (fun x : Fin a → Cinf E => star (x i w) * x j w) x * p j i w).re := by
    intro x
    simp only [quad, Finset.sum_mul, pg, dotProduct, Matrix.vecMul, Finset.sum_apply, Complex.re_sum, Pi.mul_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.re_mul_ofReal]
    congr 1
    ring
  simp only [hq]
  rw [hT.tsum_eq]
  simp only [UpperTheory.V.Lit.Bor.trF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Complex.re_sum, Finset.sum_div, Pi.mul_apply]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.div_ofReal_re]
  congr 1
  change mean L _ g * _ = _
  rw [mean]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEstimate
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem ell_toL' (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

private theorem mono_mem (i j : Fin a) (w : InfinitePlace E) :
    (fun x : Fin a → Cinf E => star (x i w) * x j w) ∈ poly E a := by
  have h1 : (fun x : Fin a → Cinf E => star (x i w)) ∈ poly E a :=
    Algebra.subset_adjoin ⟨{ toFun := fun x => star (x i w), map_add' := fun x y => by simp, map_smul' := fun c x => by simp }, rfl⟩
  have h2 : (fun x : Fin a → Cinf E => x j w) ∈ poly E a :=
    Algebra.subset_adjoin ⟨{ toFun := fun x => x j w, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }, rfl⟩
  exact mul_mem h1 h2

private theorem herm_trace (M : Herm E a) (w : InfinitePlace E) : (((M.1.trace w).re : ℝ) : ℂ) = ∑ i, M.1 i i w := by
  have h : star M.1 = M.1 := M.2
  have h2 : ∀ i, ((M.1 i i w).re : ℂ) = M.1 i i w := fun i => by
    have := congrFun (congrFun (congrFun h i) i) w
    exact Complex.conj_eq_iff_re.1 this
  simp only [Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum, Complex.ofReal_sum, h2]

private theorem trF_bd (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    |trF X X| ≤ (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (‖toL X‖ * ‖toL X‖))) := by
  have hX : ∀ i j w, ‖X i j w‖ ≤ ‖toL X‖ := fun i j w =>
    ((norm_le_pi_norm (toL X i j) w).trans (norm_le_pi_norm (toL X i) j)).trans (norm_le_pi_norm (toL X) i)
  unfold trF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (a * (‖toL X‖ * ‖toL X‖))) fun w _ => ?_).trans (by simp)
  refine (Complex.abs_re_le_norm _).trans ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (‖toL X‖ * ‖toL X‖)) fun i _ => ?_).trans (by simp)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((‖toL X‖ * ‖toL X‖)) fun j _ => ?_).trans (by simp)
  rw [norm_mul]
  exact mul_le_mul (hX _ _ _) (hX _ _ _) (norm_nonneg _) (norm_nonneg _)

end

theorem UpperTheory.hermitian_trace_form_estimate :
    DevFacts := by
  intro E _ _ _ a ha L hL
  obtain ⟨-, hM⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hone : ell E a (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = 1 := (UpperTheory.V.Lit.Bor.ellFacts E a).1 ha
  have hdev : ∀ g, (dev L g).1 = (mom L g).1 - ell E a (toL (mom L g).1) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := fun g => rfl
  have hdevL : ∀ g, toL (dev L g).1 = toL (mom L g).1 - ell E a (toL (mom L g).1) • toL (1 : Matrix (Fin a) (Fin a) (Cinf E)) := fun g => rfl
  have hmom : ∀ i j w, (fun g => (mom L g).1 i j w) ∈ meanAlg L := fun i j w =>
    Algebra.subset_adjoin ⟨_, mono_mem i j w, rfl⟩
  have hell : ∀ g, ell E a (toL (dev L g).1) = 0 := fun g => by
    rw [hdevL, map_sub, map_smul, hone, smul_eq_mul, mul_one, sub_self]
  refine ⟨fun i j w => ?_, ?_, fun g => ⟨hell g, ?_⟩⟩
  · have e : (fun g => (dev L g).1 i j w) = (fun g => (mom L g).1 i j w) -
        ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w / ((a : ℂ) * Fintype.card (InfinitePlace E))) •
          ∑ w' : InfinitePlace E, ∑ k, fun g => (mom L g).1 k k w' := by
      funext g
      simp only [hdev, ell_toL', Matrix.sub_apply, Matrix.smul_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
        ← herm_trace, Complex.real_smul, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact sub_mem (hmom i j w) (Subalgebra.smul_mem _ (sum_mem fun w' _ => sum_mem fun k _ => hmom k k w') _)
  · choose C hC using fun (p : Fin a × Fin a × InfinitePlace E) => (hM _ (mono_mem p.1 p.2.1 p.2.2)).2
    obtain ⟨B₀, hB₀⟩ := (Set.finite_range C).bddAbove
    have hB : ∀ g, ‖toL (mom L g).1‖ ≤ |B₀| := fun g => by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j =>
        (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun w => ?_
      exact ((hC (i, j, w) g).trans (hB₀ ⟨_, rfl⟩)).trans (le_abs_self _)
    obtain ⟨K, hK, hKb⟩ := (LinearMap.toContinuousLinearMap (ell E a)).bound
    set B₁ : ℝ := |B₀| + K * |B₀| * ‖toL (1 : Matrix (Fin a) (Fin a) (Cinf E))‖ with hB₁
    have hD : ∀ g, ‖toL (dev L g).1‖ ≤ B₁ := fun g => by
      rw [hdevL]
      refine (norm_sub_le _ _).trans (add_le_add (hB g) ?_)
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ((hKb _).trans ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (hB g) hK.le
    have hB1 : 0 ≤ B₁ := by positivity
    set B₂ : ℝ := (Fintype.card (InfinitePlace E) : ℝ) * (a * (a * (B₁ * B₁))) with hB₂
    have hB2 : 0 ≤ B₂ := by positivity
    have hB0 := abs_nonneg B₀
    refine ⟨|B₀| + B₁ + B₂ + 1, by positivity, fun g => ⟨by linarith [hB g], by linarith [hD g], ?_⟩⟩
    have : |trF (dev L g).1 (dev L g).1| ≤ B₂ := by
      refine (trF_bd _).trans ?_
      have := hD g
      rw [hB₂]
      gcongr
    linarith
  · have h0 := hell g
    rw [ell_toL', div_eq_zero_iff] at h0
    have h0' := h0.resolve_right (mul_ne_zero h1 h2)
    have e : (dev L g).1 * (dev L g).1 = (mom L g).1 * (dev L g).1 - ell E a (toL (mom L g).1) • (dev L g).1 := by
      conv_lhs => rw [hdev g]
      rw [sub_mul, smul_mul_assoc, one_mul, ← hdev]
    unfold trF
    rw [e]
    simp only [Matrix.trace_sub, Matrix.trace_smul, Pi.sub_apply, Pi.smul_apply, Complex.sub_re, Complex.smul_re,
      smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h0', mul_zero, sub_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SmoothSumLeftRightMulOrder
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep
open scoped ContDiff

noncomputable section

namespace UpperTheory.V.Geo.SmoothSumOrder

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem smooth_inv (l : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (fun y : Lie E a => l (Ring.inverse (Matrix.of y))) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  intro y hy
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hu : IsUnit (S y) := hy
  have h : ContDiffAt ℝ ∞ Ring.inverse (S y) := by
    simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  exact ((LinearMap.toContinuousLinearMap l).contDiff.contDiffAt.comp y
    (h.comp y S.contDiff.contDiffAt)).contDiffWithinAt

end

private def rmul (M : Matrix (Fin a) (Fin a) (Cinf E)) : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E) where
  toFun v := v ᵥ* M
  map_add' v w := Matrix.add_vecMul _ _ _
  map_smul' c v := Matrix.smul_vecMul _ _ _

private def lmul (v : Fin a → Cinf E) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] (Fin a → Cinf E) where
  toFun M := v ᵥ* M
  map_add' M M' := Matrix.vecMul_add _ _ _
  map_smul' c M := Matrix.vecMul_smul _ _ _

private theorem order (ι : Type) (x : ι → Fin a → Cinf E) (N : ℕ) (hx : Scale (fun i => qf (x i)) N) (n : ℕ) :
    ∀ P ∈ poly E a, ContDiffOn ℝ n (msum x P) (invSet E a) := by
  induction n with
  | zero =>
    intro P hP
    exact contDiffOn_zero.2 fun y hy =>
      (UpperTheory.sum_der E a ι x N hx P hP y hy).2.1.continuousAt.continuousWithinAt
  | succ n ih =>
    intro P hP
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (UpperTheory.sum_der E a ι x N hx P hP y hy).2.1.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_clm_apply]
    intro Z
    let b := Module.finBasis ℝ (Matrix (Fin a) (Fin a) (Cinf E))
    choose Q hQ hQ' using fun j => (UpperTheory.quadratic_form_gradient_formula E a P hP).2.2 (rmul (b j))
    let l := fun j => (b.coord j).comp (LinearMap.mulRight ℝ (Matrix.of Z))
    have hs : ContDiffOn ℝ n (fun y : Lie E a => ∑ j, l j (Ring.inverse (Matrix.of y)) • msum x (Q j) y)
        (invSet E a) :=
      ContDiffOn.sum fun j _ => ((smooth_inv (l j)).of_le (by exact_mod_cast le_top)).smul (ih _ (hQ j))
    refine hs.congr fun y hy => ?_
    have hu : IsUnit (Matrix.of y) := hy
    have hterm : ∀ i, fderiv ℝ (pg P) (x i ᵥ* Matrix.of y) (x i ᵥ* Matrix.of Z) =
        ∑ j, l j (Ring.inverse (Matrix.of y)) • pg (Q j) (x i ᵥ* Matrix.of y) := by
      intro i
      have e1 : x i ᵥ* Matrix.of Z = lmul (x i ᵥ* Matrix.of y) (Ring.inverse (Matrix.of y) * Matrix.of Z) := by
        change _ = (x i ᵥ* Matrix.of y) ᵥ* _
        rw [Matrix.vecMul_vecMul, ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, ← b.sum_repr (Ring.inverse (Matrix.of y) * Matrix.of Z), map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, ← hQ' j]
      rfl
    rw [(UpperTheory.sum_der E a ι x N hx P hP y hy).2.2 Z, tsum_congr hterm,
      Summable.tsum_finsetSum fun j _ => (UpperTheory.sum_der E a ι x N hx _ (hQ j) y hy).1.const_smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (UpperTheory.sum_der E a ι x N hx _ (hQ j) y hy).1.tsum_const_smul _

end UpperTheory.V.Geo.SmoothSumOrder

theorem UpperTheory.smooth_sum_left_right_mul_order :
    SumSm := fun _ _ _ _ ι x N hx P hP =>
  contDiffOn_infty.2 fun n => UpperTheory.V.Geo.SmoothSumOrder.order ι x N hx n P hP
end
end

