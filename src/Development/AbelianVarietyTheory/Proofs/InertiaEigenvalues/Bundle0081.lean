module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0063
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
section
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory


open MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  haveI : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨⟨Units.isOpenEmbedding_val⟩, ?_⟩
  have hd := hasStrictFDerivAt_pow (𝕜 := F) 2 (x := (1 : R))
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hsurj : LinearMap.range
      ((((2 : ℕ) • (1 : R) ^ (2 - 1)) • ContinuousLinearMap.id F R : R →L[F] R) : R →ₗ[F] R)
        = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ⟨(2 : F)⁻¹ • v, ?_⟩
    have hc : ((2 : ℕ) • (1 : R) ^ (2 - 1)) = algebraMap F R 2 := by
      simp [two_smul, map_ofNat, one_add_one_eq_two]
    simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply,
      id_eq, hc, ContinuousLinearMap.coe_coe, smul_eq_mul]
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have hmap := hd.map_nhds_eq_of_surj hsurj
  rw [one_pow] at hmap
  rw [← hmap, Filter.eventually_map]
  exact Filter.Eventually.of_forall fun s => ⟨s, rfl⟩


open MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [N : NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R := by
  haveI : IsModuleTopology F R := isModuleTopologyOfFiniteDimensional
  exact eq_moduleTopology F R


open MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  classical
  have h := eq_moduleTopology F R
  let b := Module.finBasis F R
  letI : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  letI N : NormedCommRing R :=
    NormedCommRing.induced R _ (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)
  letI : NormedAlgebra F R := NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed F R
  have h2 := _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology F R
  have h3 : τ = N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
    h.trans h2.symm
  rw [h3]
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourBProdIterated
section
open GlobalTheory.JR MeasureTheory

theorem GlobalTheory.JR.fourB_prod_iterated : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  intro V V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he hes B B₁ B₂ hB₁ hB₂ hB μ μ₁ μ₂ hμ hμ₁ hμ₂
  let h : V ≃ₜ V₁ × V₂ := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  let hm : V ≃ᵐ V₁ × V₂ := h.toMeasurableEquiv
  haveI : (Measure.map e μ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e he hes
  haveI : (μ₁.prod μ₂).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ₁ μ₂
  set k := Measure.addHaarScalarFactor (Measure.map e μ) (μ₁.prod μ₂) with hk
  have hkeq : Measure.map e μ = k • (μ₁.prod μ₂) := Measure.isAddLeftInvariant_eq_smul _ _
  have hkpos : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨((k : ℝ) : ℂ), by exact_mod_cast hkpos.ne', fun φ hφ y => ?_⟩
  have hmap : Measure.map hm μ = Measure.map e μ := rfl
  have step1 : fourB μ B φ y = ∫ q, φ (e.symm q) * B (e.symm q) y ∂(Measure.map e μ) := by
    rw [← hmap, hm.measurableEmbedding.integral_map]
    simp [fourB, hm, h]
  rw [step1, hkeq, integral_smul_nnreal_measure]
  have hcont : Continuous fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) :=
    (hφ.1.continuous.comp hes).mul ((hB₁.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.1, (e y).1))).mul
      (hB₂.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.2, (e y).2))))
  have hsupp : HasCompactSupport fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    have : HasCompactSupport (φ ∘ h.symm) := hφ.2.comp_homeomorph h.symm
    exact this.mul_right
  have hint := hcont.integrable_of_hasCompactSupport hsupp (μ := μ₁.prod μ₂)
  have e2 : (fun q : V₁ × V₂ => φ (e.symm q) * B (e.symm q) y) =
      fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    ext q; rw [hB]; simp
  rw [e2, integral_prod _ hint]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  congr 1; ext v; ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBound
section
noncomputable section

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem pow_iter_frobeniusEquiv_symm {F : Type} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (x : F) (m : ℕ) : (((frobeniusEquiv F p).symm)^[m] x) ^ p ^ m = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have h := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[m] x)
    rw [frobenius_def] at h
    rw [h, ih]

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem norm_pw (k : ℤ) (x : F) : ‖pw p k x‖ = ‖x‖ ^ ((p : ℝ) ^ k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold pw
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [norm_pow, Int.toNat_natCast, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hm
    rw [neg_neg, Int.toNat_natCast]
    have hy := pow_iter_frobeniusEquiv_symm p x m
    conv_rhs => rw [← hy]
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (by positivity), Real.rpow_one]

theorem norm_term (k : ℕ) (ϖ : F) (hϖ : ‖ϖ‖ = (p : ℝ)⁻¹) (lam π : Fin (k + 1) → F) (r j : Fin (k + 1)) (n : ℤ) :
    ‖term p ϖ lam π r j n‖ = ‖lam j‖ * (p : ℝ) ^ n * ‖π j‖ ^ ((p : ℝ) ^ (((r : ℕ) : ℤ) + n * ((k : ℤ) + 1))) := by
  unfold term
  rw [norm_mul, norm_mul, norm_zpow, hϖ, norm_pw, inv_zpow', neg_neg]
  push_cast
  rfl

def idx (k : ℕ) (J : ℤ) : Fin (k + 1) :=
  ⟨(J % ((k : ℤ) + 1)).toNat, by
    have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos J (show (0 : ℤ) < (k : ℤ) + 1 by omega)
    omega⟩

theorem idx_spec (k : ℕ) (j : Fin (k + 1)) (m : ℤ) :
    idx k (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = j ∧ (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) / ((k : ℤ) + 1) = m := by
  have hj := j.isLt
  have h0 : ((j : ℕ) : ℤ) / ((k : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h1 : ((j : ℕ) : ℤ) % ((k : ℤ) + 1) = j := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · ext
    simp [idx, Int.add_mul_emod_self_left, h1]
  · rw [Int.add_mul_ediv_left _ _ (by omega), h0, zero_add]

theorem decomp (k : ℕ) (J : ℤ) : ∃ j : Fin (k + 1), ∃ m : ℤ, J = ((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
  refine ⟨idx k J, J / ((k : ℤ) + 1), ?_⟩
  have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
  have h2 : J % ((k : ℤ) + 1) = J - ((k : ℤ) + 1) * (J / ((k : ℤ) + 1)) := Int.emod_def _ _
  show J = (((J % ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + _
  rw [Int.toNat_of_nonneg h1]
  linarith

def aW (k : ℕ) (lam : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖lam (idx k J)‖ * (p : ℝ) ^ (-(J / ((k : ℤ) + 1)))

def rW (k : ℕ) (π : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖π (idx k J)‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * (J / ((k : ℤ) + 1)))))

theorem aW_at (k : ℕ) (lam : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    aW p k lam (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖lam j‖ * (p : ℝ) ^ (-m) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [aW, h1, h2]

theorem rW_at (k : ℕ) (π : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    rW p k π (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * m))) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [rW, h1, h2]

end GlobalTheory.PMonE.WinBounds

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem term_le_bound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  intro F _ p _ _ _ k ϖ hϖ lam π hlam hanti hratio hπ hrel1 hrel2 r j n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  have ha : ∀ J, 0 < aW p k lam J := by
    intro J; unfold aW; exact mul_pos (norm_pos_iff.2 (hlam _)) (zpow_pos hp0 _)
  have hρ : ∀ J, 0 < rW p k π J := by
    intro J; unfold rW; exact Real.rpow_pos_of_pos (norm_pos_iff.2 (hπ _).1) _
  have hrp : ∀ (x : ℝ), 0 ≤ x → ∀ c d : ℤ, (x ^ ((p : ℝ) ^ c)) ^ ((p : ℝ) ^ d) = x ^ ((p : ℝ) ^ (c + d)) := by
    intro x hx c d; rw [← Real.rpow_mul hx, zpow_add₀ hpne]
  have hnat : ∀ (x : ℝ) (e : ℕ), x ^ ((p : ℝ) ^ (e : ℤ)) = x ^ (p ^ e) := by
    intro x e; rw [zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  have hstep : ∀ J, aW p k lam (J + 1) ≤ aW p k lam J := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
      have h1 := hratio 0 (Fin.last k)
      have hz := zpow_pos hp0 (-m)
      calc ‖lam 0‖ * ((p : ℝ) ^ (-m) * (p : ℝ)⁻¹) = (‖lam 0‖ / p) * (p : ℝ) ^ (-m) := by ring
        _ ≤ ‖lam (Fin.last k)‖ * (p : ℝ) ^ (-m) := by
          gcongr
          rw [div_le_iff₀ hp0]; linarith
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at]
      have h1 : ‖lam i.succ‖ ≤ ‖lam (Fin.castSucc i)‖ := hanti (Fin.castSucc_lt_succ (i := i)).le
      have hz := zpow_pos hp0 (-m)
      gcongr
  have hA : Antitone (aW p k lam) := antitone_int_of_succ_le hstep
  have hA0 : aW p k lam 0 < (p : ℝ) * aW p k lam (((k + 1 : ℕ) : ℤ) - 1) := by
    have h1 : aW p k lam 0 = ‖lam 0‖ := by simpa using aW_at p k lam 0 0
    have h2 : aW p k lam (k : ℤ) = ‖lam (Fin.last k)‖ := by simpa using aW_at p k lam (Fin.last k) 0
    rw [h1, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, h2]
    exact hratio 0 (Fin.last k)
  have hperA : ∀ J, aW p k lam (J + ((k + 1 : ℕ) : ℤ)) = aW p k lam J / p := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
    ring
  have hperR : ∀ J, rW p k π (J + ((k + 1 : ℕ) : ℤ)) = rW p k π J ^ (((p : ℝ) ^ (k + 1))⁻¹) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, rW_at, rW_at]
    have e3 : ((p : ℝ) ^ (k + 1))⁻¹ = (p : ℝ) ^ (-((k : ℤ) + 1)) := by
      rw [zpow_neg]; norm_cast
    rw [e3, hrp _ (norm_nonneg _), show -(((k : ℤ) + 1) * (m + 1)) = -(((k : ℤ) + 1) * m) + -((k : ℤ) + 1) by ring]
  have hrelW : ∀ J, aW p k lam (J + 1) * rW p k π (J + 1) ^ ((p : ℝ) ^ J)
      = aW p k lam J * rW p k π J ^ ((p : ℝ) ^ J) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * (m + 1)) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = -1 := by
        push_cast [Fin.val_last]; ring
      have e3 : -(((k : ℤ) + 1) * m) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((k : ℕ) : ℤ) := by
        push_cast [Fin.val_last]; ring
      rw [e2, e3, hnat, zpow_neg_one]
      have hXY : ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) = ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by
        have hx : 0 ≤ ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) := by positivity
        have hy : 0 ≤ ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by positivity
        refine (pow_left_inj₀ hx hy (Fact.out : p.Prime).ne_zero).1 ?_
        rw [mul_pow, ← hrel2, ← Real.rpow_natCast (‖π 0‖ ^ ((p : ℝ)⁻¹)) p, ← Real.rpow_mul (norm_nonneg _),
          inv_mul_cancel₀ hpne, Real.rpow_one]
      rw [neg_add, zpow_add₀ hpne, zpow_neg_one]
      linear_combination (p : ℝ) ^ (-m) * hXY
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * m) + ((((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((i : ℕ) : ℤ) := by
        push_cast [Fin.coe_castSucc]; ring
      rw [e2, hnat, hnat]
      have h := hrel1 i
      linear_combination (p : ℝ) ^ (-m) * h
  have hJ := window_ineq p (k + 1) (by exact_mod_cast (Fact.out : p.Prime).one_lt) (Nat.succ_pos k) (aW p k lam)
    (rW p k π) ha hρ hA hA0 hperA hperR hrelW (r : ℕ) r.isLt (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * (-n))
  rw [aW_at p k lam j (-n), rW_at p k π j (-n)] at hJ
  have hR1 : aW p k lam ((r : ℕ) : ℤ) = ‖lam r‖ := by simpa using aW_at p k lam r 0
  have hR2 : rW p k π ((r : ℕ) : ℤ) = ‖π r‖ := by simpa using rW_at p k π r 0
  rw [hR1, hR2] at hJ
  have hT : ‖term p ϖ lam π r j n‖
      = ‖lam j‖ * (p : ℝ) ^ (-(-n)) * (‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * -n)))) ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_term p k ϖ hϖ, ← zpow_natCast (p : ℝ) (r : ℕ), hrp _ (norm_nonneg _), neg_neg,
      show -(((k : ℤ) + 1) * -n) + ((r : ℕ) : ℤ) = ((r : ℕ) : ℤ) + n * ((k : ℤ) + 1) by ring]
  have hRt : ‖lam r * π r ^ p ^ (r : ℕ)‖ = ‖lam r‖ * ‖π r‖ ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖π r‖ (p ^ (r : ℕ)), Nat.cast_pow]
  rw [hT, hRt]
  obtain ⟨W1, W2, W3, W4⟩ := hJ
  have hj1 : ((j : ℕ) : ℤ) < (k : ℤ) + 1 := by exact_mod_cast j.isLt
  have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
  refine ⟨W1, fun hn => W2 (by nlinarith), fun hn => ?_⟩
  rcases lt_abs.1 hn with hn | hn
  · exact W3 (by push_cast; nlinarith)
  · exact W4 (by push_cast; nlinarith)

end GlobalTheory.PMonE.WinBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaConditionShiftAndDivVariableMem
section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem condC_sh_and_nab_mem : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ a : ℤ, CondC g (sh a N) ∧ ∀ x ∈ sh a N, nab g x ∈ sh a N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hC a
  have h : ∀ x ∈ sh a N, nab g x ∈ sh a N := fun x hx => Window.nab_mem_sh R hg hC a hx
  exact ⟨(condC_iff_nab_mem g _).2 h, h⟩

end GlobalTheory.PhiGam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultEqZeroOfInj
section
noncomputable section
namespace GlobalTheory.PhiGam.Compare
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem inj_iff_surj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, S p ∈ P) (hQ : ∀ p ∈ Q, S p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] :
    (∀ p ∈ P, S p ∈ Q → p ∈ Q) ↔ ∀ y ∈ P, ∃ p ∈ P, y - S p ∈ Q := by
  have hSQ : Q ≤ Q.comap S := fun p hp => hQ p hp
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, hP p hp, rfl⟩
  constructor
  · intro hinj
    have hi : Function.Injective (Sq.restrict hSq) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨_, p, hp, rfl⟩ hz
      have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
      have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
    have hs := LinearMap.injective_iff_surjective.mp hi
    intro y hy
    obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
    have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
    exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩
  · intro hsur
    have hs : Function.Surjective (Sq.restrict hSq) := by
      rintro ⟨_, y, hy, rfl⟩
      obtain ⟨p, hp, h⟩ := hsur y hy
      refine ⟨⟨Q.mkQ p, p, hp, rfl⟩, Subtype.ext ?_⟩
      exact ((Submodule.Quotient.eq _).mpr h).symm
    have hi := LinearMap.injective_iff_surjective.mpr hs
    intro p hp h
    have h0 : Sq.restrict hSq ⟨Q.mkQ p, p, hp, rfl⟩ = 0 :=
      Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)
    have h1 := (injective_iff_map_eq_zero _).mp hi _ h0
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h1)

theorem gmult_eq_zero_of_inj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (x : k)
    (hP : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ P)
    (hQ : ∀ p ∈ Q, (T - algebraMap k (Module.End k U) x) p ∈ Q)
    (h : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ Q → p ∈ Q) : gmult T P Q x = 0 := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) x with hS
  have h1 : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      exact h p hp (ih _ (hP p hp) hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  have htop : Q.submoduleOf (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨p, hp, hp'⟩ _
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hp'
    exact h1 m p hp hm
  rw [htop]
  exact Module.finrank_zero_of_subsingleton

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (y : k) (h : sen g N (y + b) = 0) :
    ∀ x ∈ sh b N, nab g x - y • x ∈ sh (b + 1) N → x ∈ sh (b + 1) N := by
  haveI := Window.finite_quot hN
  obtain ⟨h1, -⟩ := Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (y + b) h
  have hv : vv k ≠ 0 := vv_ne_zero k
  intro x hx hx'
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff_exists.mp hx
  obtain ⟨n', hn', e⟩ := Window.nab_shift R hg hC b hn
  obtain ⟨t, ht, e'⟩ := mem_sh_iff_exists.mp hx'
  have hc : y • vv k ^ b • n = vv k ^ b • y • n := by
    rw [← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ y), ← const_smul_eq,
      smul_assoc, one_smul]
  rw [e, hc, ← smul_sub, zpow_add_one₀ hv, mul_smul] at e'
  have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
  have : n ∈ sh 1 N := h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by
    rw [zpow_one, smul_sub, e2, add_smul]; abel⟩)
  obtain ⟨r, hr, rfl⟩ := mem_sh_iff_exists.mp this
  exact mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩

theorem sen_compare : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N₁ N₂ : Submodule k⟦X⟧ V, IsLat N₁ → IsLat N₂ → CondC g N₁ → CondC g N₂ → ∀ s : ℕ, sh s N₁ ≤ N₂ → N₂ ≤ sh (-s) N₁ → ∀ y : k, sen g N₂ y ≠ 0 → ∃ j : ℤ, |j| ≤ s ∧ sen g N₁ (y + j) ≠ 0 := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N₁ N₂ h₁ h₂ c₁ c₂ s lo hi y hy
  by_contra hcon
  push_neg at hcon
  apply hy
  set S : Module.End k V := nab g - algebraMap k (Module.End k V) y with hSdef
  have hS : ∀ p, S p = nab g p - y • p := fun p => rfl
  have st : ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ b : ℤ, ∀ p ∈ sh b N, S p ∈ sh b N := fun N c b p hp => by
    rw [hS]
    exact (sh b N).sub_mem (Window.nab_mem_sh R hg c b hp) (((sh b N).restrictScalars k).smul_mem y hp)
  have st2 : ∀ p ∈ N₂, S p ∈ N₂ := by
    have := st N₂ c₂ 0
    rwa [sh_zero_eq] at this
  have key : ∀ m : ℕ, m ≤ 2 * s + 1 → ∀ x ∈ N₂, ∃ p ∈ N₂, x - S p ∈ sh (-s + m) N₁ := by
    intro m
    induction m with
    | zero => intro _ x hx; exact ⟨0, N₂.zero_mem, by simpa using hi hx⟩
    | succ m ih =>
      intro hm x hx
      obtain ⟨p, hp, hp'⟩ := ih (by omega) x hx
      set b : ℤ := -s + m with hb
      have hsen := hcon b (by rw [abs_le]; omega)
      have hf := Window.finite_quot (h₁.shift b).1
      rw [sh_sh_eq, add_comm] at hf
      haveI : FiniteDimensional k (((N₂ ⊓ sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) :=
        Submodule.finiteDimensional_of_le (S₂ := ((sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) (Submodule.map_mono fun z hz => hz.2)
      obtain ⟨q, hq, hq'⟩ := (inj_iff_surj S ((N₂ ⊓ sh b N₁).restrictScalars k)
        ((sh (b + 1) N₁).restrictScalars k) (fun z hz => ⟨st2 z hz.1, st N₁ c₁ b z hz.2⟩)
        (fun z hz => st N₁ c₁ _ z hz)).mp
        (fun z hz hz' => graded_inj R hg h₁.1 c₁ b y hsen z hz.2 hz') (x - S p)
        ⟨N₂.sub_mem hx (st2 p hp), hp'⟩
      refine ⟨p + q, N₂.add_mem hp hq.1, ?_⟩
      rw [map_add (f := _), ← sub_sub, Nat.cast_succ, ← add_assoc]
      exact hq'
  haveI := Window.finite_quot h₂.1
  refine gmult_eq_zero_of_inj (nab g) _ _ y st2 (st N₂ c₂ 1) ?_
  refine (inj_iff_surj S (N₂.restrictScalars k) ((sh 1 N₂).restrictScalars k) st2 (st N₂ c₂ 1)).mpr ?_
  intro x hx
  obtain ⟨p, hp, hp'⟩ := key (2 * s + 1) le_rfl x hx
  refine ⟨p, hp, sh_le_sh 1 lo ?_⟩
  rw [sh_sh_eq]
  convert hp' using 2
  push_cast; ring

end GlobalTheory.PhiGam.Compare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralAdjoinOfForallCdvrStatement
section
open Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (gens : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → ∀ x : Ω, (∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr, (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) → (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) → IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  first | exact @GlobalTheory.isIntegral_adjoin_of_forall_cdvr | exact GlobalTheory.isIntegral_adjoin_of_forall_cdvr | (intros; apply GlobalTheory.isIntegral_adjoin_of_forall_cdvr <;> assumption)
end

