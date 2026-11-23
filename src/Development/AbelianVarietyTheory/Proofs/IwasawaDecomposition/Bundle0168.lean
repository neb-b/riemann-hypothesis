module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite
section
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.DefiniteUnitaryCasimir

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UnitaryLieComplexification

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

theorem exists_linear_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this

theorem mul_single_mul (U V : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    U * single a b (1 : ℂ) * V = ∑ c, ∑ d, (U c a * V b d) • single c d (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (U * single a b (1 : ℂ) * V)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem casimir_move {A : Type} [Ring A] [Algebra ℂ A] (R R' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (U V : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, R (U * single a b 1 * V) * R' (single b a 1) =
      ∑ c, ∑ d, R (single c d 1) * R' (V * single d c 1 * U) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mul_single_mul, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (f := fun c d => ∑ b, ∑ a, (V b d * U c a) • (R (single c d 1) * R' (single b a 1)))]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))) _ _
    fun q => ?_
  simp [mul_comm]

theorem casimir_conj {A : Type} [Ring A] [Algebra ℂ A] (R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    ∑ a, ∑ b, R (single a b 1) * R (single b a 1) =
      ∑ a, ∑ b, R (B⁻¹ * single a b 1 * B) * R (B⁻¹ * single b a 1 * B) := by
  have := casimir_move R (R ∘ₗ (LinearMap.mulRight ℂ B) ∘ₗ (LinearMap.mulLeft ℂ B⁻¹)) B⁻¹ B
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul B hB, Matrix.mul_one]

theorem cj_conj_single (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) (h : J = Bᴴ * B ∨ J = -(Bᴴ * B))
    (a b : Fin n) : cj J (B⁻¹ * single a b 1 * B) = -(B⁻¹ * single b a 1 * B) := by
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have key : (Bᴴ * B)⁻¹ * (B⁻¹ * single a b (1 : ℂ) * B)ᴴ * (Bᴴ * B) = B⁻¹ * single b a 1 * B := by
    rw [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_single,
      star_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ B, ← Matrix.mul_assoc Bᴴ⁻¹ Bᴴ, Matrix.nonsing_inv_mul _ hBH, Matrix.one_mul,
      Matrix.one_mul]
  rcases h with rfl | rfl
  · rw [cj, key]
  · have hu : IsUnit (Bᴴ * B).det := by rw [det_mul]; exact hBH.mul hB
    have : (-(Bᴴ * B))⁻¹ = -(Bᴴ * B)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hu]
    rw [cj, this, neg_mul, neg_mul_neg, key]

theorem sum_squares {A : Type} [Ring A] [Algebra ℂ A] (F : Fin n → Fin n → A) :
    ∑ a, ∑ b, F a b * F b a =
      -∑ a, ∑ b, (((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a))) := by
  have h : (1 / (2 * Complex.I) : ℂ) * (1 / (2 * Complex.I)) = -(1 / 4) := by
    field_simp
    simp
    norm_num
  have h1 : ∀ a b, ((1 / 2 : ℂ) • (F a b - F b a)) * ((1 / 2 : ℂ) • (F a b - F b a)) +
        ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) * ((1 / (2 * Complex.I) : ℂ) • (F a b + F b a)) =
        -((1 / 2 : ℂ) • (F a b * F b a) + (1 / 2 : ℂ) • (F b a * F a b)) := by
    intro a b
    simp only [smul_mul_smul_comm, h, mul_add, add_mul, mul_sub, sub_mul]
    module
  simp only [h1, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => F b a * F a b)]
  module

theorem casimir_eq_neg_sum_sq : ∀ (n : ℕ) (J B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det → (J = Bᴴ * B ∨ J = -(Bᴴ * B)) → ∃ X : Fin n × Fin n × Bool → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ Y Z, ρ (Y + Z) = ρ Y + ρ Z) → (∀ (c : ℝ) Y, ρ (c • Y) = (c : ℂ) • ρ Y) → ∑ a, ∑ b, (ρ (P a b) + Complex.I • ρ (Q a b)) * (ρ (P b a) + Complex.I • ρ (Q b a)) = -∑ i, ρ (X i) * ρ (X i) := by
  intro n J B hB h
  have hBH : IsUnit Bᴴ.det := by rw [det_conjTranspose]; exact hB.star
  have hJ : Jᴴ = J := by
    rcases h with rfl | rfl <;> simp
  have hu : IsUnit J.det := by
    rcases h with rfl | rfl
    · rw [det_mul]; exact hBH.mul hB
    · rw [det_neg, det_mul]; exact (isUnit_one.neg.pow _).mul (hBH.mul hB)
  let F : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ := fun a b => B⁻¹ * single a b 1 * B
  let X : Fin n × Fin n × Bool → lieU J := fun p =>
    if p.2.2 then rePart hJ hu (F p.1 p.2.1) else imPart hJ hu (F p.1 p.2.1)
  refine ⟨X, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro Y -
    let S : Submodule ℝ (lieU J) := Submodule.span ℝ (Set.range X)
    have hS : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) →
        ∃ U ∈ S, ∃ V ∈ S, Z = U.1 + Complex.I • V.1 := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨⟨a, b⟩, rfl⟩ := hZ
        exact ⟨_, Submodule.subset_span ⟨(a, b, true), rfl⟩, _, Submodule.subset_span ⟨(a, b, false), rfl⟩,
          (re_add_im hJ hu _).symm⟩
      | zero => exact ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
      | add Z W _ _ hZ hW =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        obtain ⟨U', hU', V', hV', rfl⟩ := hW
        refine ⟨U + U', S.add_mem hU hU', V + V', S.add_mem hV hV', ?_⟩
        change _ = (U.1 + U'.1) + Complex.I • (V.1 + V'.1)
        module
      | smul c Z _ hZ =>
        obtain ⟨U, hU, V, hV, rfl⟩ := hZ
        have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
        generalize c.re = a at hc
        generalize c.im = b at hc
        subst hc
        refine ⟨a • U - b • V, S.sub_mem (S.smul_mem _ hU) (S.smul_mem _ hV), b • U + a • V,
          S.add_mem (S.smul_mem _ hU) (S.smul_mem _ hV), ?_⟩
        have hII : ∀ (m : Matrix (Fin n) (Fin n) ℂ), Complex.I • Complex.I • m = -m := by
          intro m
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        change _ = ((a : ℂ) • U.1 - (b : ℂ) • V.1) + Complex.I • ((b : ℂ) • U.1 + (a : ℂ) • V.1)
        simp only [add_smul, smul_add, mul_smul, hII]
        module
    have hY : Y.1 ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => F p.1 p.2) := by
      have : Y.1 = B⁻¹ * (B * Y.1 * B⁻¹) * B := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hB, Matrix.one_mul, Matrix.mul_assoc,
          Matrix.nonsing_inv_mul B hB, Matrix.mul_one]
      rw [this, Matrix.matrix_eq_sum_single (B * Y.1 * B⁻¹)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      have : Matrix.single a b ((B * Y.1 * B⁻¹) a b) = (B * Y.1 * B⁻¹) a b • Matrix.single a b (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [this, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
    obtain ⟨U, hU, V, -, hUV⟩ := hS _ hY
    have h1 := rePart_mk hJ hu U V
    have h2 := rePart_mk hJ hu Y 0
    have h3 : Y.1 + Complex.I • (0 : lieU J).1 = Y.1 := by simp
    rw [h3, hUV, h1] at h2
    rw [← h2]
    exact hU
  · intro P Q hPQ A _ _ ρ hadd hsm
    obtain ⟨R, hR, hX⟩ := exists_linear_extension hJ hu ρ hadd hsm
    have hP : ∀ a b, P a b = rePart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).1
    have hQ : ∀ a b, Q a b = imPart hJ hu (single a b 1) := fun a b => Subtype.ext (hPQ a b).2
    simp only [hP, hQ, ← hR]
    rw [casimir_conj R B hB, sum_squares (fun a b => R (F a b))]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e1 : ρ (X (a, b, true)) = (1 / 2 : ℂ) • (R (F a b) - R (F b a)) := by
      rw [← hX]
      change R ((1 / 2 : ℂ) • (F a b + cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_add (f := _), map_neg, ← sub_eq_add_neg]
    have e2 : ρ (X (a, b, false)) = (1 / (2 * Complex.I) : ℂ) • (R (F a b) + R (F b a)) := by
      rw [← hX]
      change R ((1 / (2 * Complex.I) : ℂ) • (F a b - cj J (F a b))) = _
      rw [cj_conj_single B hB h, map_smul, map_sub, map_neg, sub_neg_eq_add]
    rw [Fintype.sum_bool, e1, e2]

end GlobalTheory.DefiniteUnitaryCasimir
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdInt

theorem map_eq_smul_prod {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c) :
    ρ.map (fun X => (pi X, fun v : S => pv v X)) = c • mi.prod (Measure.pi fun v : S => mv v) := by
  classical
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  by_cases hc0 : c = 0
  · have := h (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
    simp only [hc0, mul_zero, Finset.prod_const_one, mul_one, lintegral_const, one_mul,
      Measure.measure_univ_eq_zero] at this
    simp [this, hc0]
  have key : mi.prod (Measure.pi fun v : S => mv v) =
      c⁻¹ • ρ.map (fun X => (pi X, fun v : S => pv v X)) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := Set.pi Set.univ '' Set.pi Set.univ fun v : S => {s : Set (Zv v) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi mi.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun v : S => (mv v).toFiniteSpanningSetsIn) ?_
    rintro s hs _ ⟨t, ht, rfl⟩
    have hs' : MeasurableSet s := hs
    have ht' : ∀ v : S, MeasurableSet (t v) := fun v => ht v (Set.mem_univ _)
    let fv : ∀ v, Zv v → ℝ≥0∞ := fun v => if hv : v ∈ S then (t ⟨v, hv⟩).indicator 1 else 0
    have hfv : ∀ v, Measurable (fv v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [fv, dif_pos hv]
        exact measurable_one.indicator (ht' _)
      · simp only [fv, dif_neg hv]
        exact measurable_zero
    have hfv' : ∀ v : S, fv v = (t v).indicator 1 := fun v => by simp only [fv, dif_pos v.2]
    have h1 := h (s.indicator 1) fv (measurable_one.indicator hs') hfv
    have hm : MeasurableSet (s ×ˢ Set.pi Set.univ t) :=
      hs'.prod (MeasurableSet.univ_pi ht')
    rw [Measure.smul_apply, Measure.map_apply hT hm, ← lintegral_indicator_one (hT hm), Measure.pi_pi]
    have h2 : ∀ X, ((fun X => (pi X, fun v : S => pv v X)) ⁻¹' (s ×ˢ Set.pi Set.univ t)).indicator
        (1 : Z → ℝ≥0∞) X = s.indicator 1 (pi X) * ∏ v ∈ S, fv v (pv v X) := by
      intro X
      rw [← Finset.prod_coe_sort S]
      simp only [hfv']
      by_cases hX : pi X ∈ s
      · by_cases hY : ∀ v : S, pv v X ∈ t v
        · rw [Set.indicator_of_mem (by simpa [hX] using hY)]
          simp [hX, hY]
        · rw [Set.indicator_of_notMem (by simpa [hX] using hY)]
          push_neg at hY
          obtain ⟨v, hv⟩ := hY
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])]
          simp
      · rw [Set.indicator_of_notMem (by simp [hX])]
        simp [hX]
    simp_rw [h2]
    rw [h1, ← Finset.prod_coe_sort S]
    simp only [hfv', lintegral_indicator_one hs', lintegral_indicator_one (ht' _), smul_eq_mul]
    rw [mul_comm c⁻¹, mul_assoc, ENNReal.mul_inv_cancel hc0 hc, mul_one]
  rw [key, smul_smul, ENNReal.mul_inv_cancel hc0 hc, one_smul]

theorem integral_tensor {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c)
    (Φi : Zi → ℂ) (Φv : ∀ v, Zv v → ℂ) (hi : Integrable Φi mi) (hv : ∀ v, Integrable (Φv v) (mv v)) :
    Integrable (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) ρ ∧
      ∫ X, Φi (pi X) * ∏ v ∈ S, Φv v (pv v X) ∂ρ =
        (∫ Y, Φi Y ∂mi) * ((∏ v ∈ S, ∫ Y, Φv v Y ∂(mv v)) * (c.toReal : ℂ)) := by
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  have hmap := map_eq_smul_prod ρ mi mv pi pv hpi hpv S c hc h
  let G : Zi × (∀ v : S, Zv v) → ℂ := fun Y => Φi Y.1 * ∏ v : S, Φv v (Y.2 v)
  have hG : Integrable G (mi.prod (Measure.pi fun v : S => mv v)) :=
    hi.mul_prod (Integrable.fintype_prod_dep (f := fun v : S => Φv v) fun v => hv v)
  have hG' : Integrable G (ρ.map (fun X => (pi X, fun v : S => pv v X))) := by
    rw [hmap]; exact hG.smul_measure hc
  have he : (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) =
      G ∘ (fun X => (pi X, fun v : S => pv v X)) := by
    funext X
    simp only [G, Function.comp]
    rw [← Finset.prod_coe_sort S]
  rw [he]
  refine ⟨(integrable_map_measure hG'.aestronglyMeasurable hT.aemeasurable).1 hG', ?_⟩
  have := integral_map hT.aemeasurable hG'.aestronglyMeasurable
  simp only [Function.comp_def]
  rw [← this, hmap, integral_smul_measure]
  simp only [G]
  rw [integral_prod_mul Φi (fun Y : ∀ v : S, Zv v => ∏ v : S, Φv v (Y v)),
    integral_fintype_prod_eq_prod (fun v : S => Φv v), ← Finset.prod_coe_sort S, Complex.real_smul]
  ring

theorem hasProd_of_tail {ι : Type} (f : ι → ℂ) (a : ι → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hs : Summable fun v => |a v - 1|) (S : Finset ι) (hf : ∀ v ∉ S, f v = a v) :
    HasProd f ((∏ v ∈ S, f v) *
      (((ENNReal.ofReal (∏' v : {v // v ∉ S}, a v.1)).toReal : ℝ) : ℂ)) := by
  have hm : Multipliable fun v : {v // v ∉ S} => a v.1 := by
    have h1 : Summable fun v : {v // v ∉ S} => ‖a v.1 - 1‖ := hs.subtype _
    simpa using multipliable_one_add_of_summable h1
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, a v.1 :=
    ge_of_tendsto' hm.hasProd fun s => Finset.prod_nonneg fun v _ => ha _
  rw [ENNReal.toReal_ofReal h0]
  have h2 := hm.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  refine (S.hasProd f).mul_compl ?_
  have h3 : (f ∘ Subtype.val : {v // v ∉ S} → ℂ) = Complex.ofRealHom ∘ fun v : {v // v ∉ S} => a v.1 :=
    funext fun v => hf v.1 v.2
  have h4 : HasProd (f ∘ Subtype.val : {v // v ∉ S} → ℂ)
      ((∏' v : {v // v ∉ S}, a v.1 : ℝ) : ℂ) := by rw [h3]; exact h2
  exact h4

theorem integral_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Multipliable (fun v => ∫ X, Φv v X ∂(mv v)) ∧ ∫ X, Φ X ∂ν = (∫ X, Φinf X ∂mi) * ∏' v, ∫ X, Φv v X ∂(mv v) := by
  intro F E _ _ _ _ _ d b n M ν mi mv hP d' b' Φ Φinf Φf Φv hc hcs hpure hΦ
  obtain ⟨⟨hmi, hmv, hsum⟩, hP⟩ := hP
  obtain ⟨hsb, hae, hfin⟩ := hpure
  obtain ⟨hco, -, hint, hbb⟩ := GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b
  obtain ⟨-, -, hci, hcv⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hae' : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 := by
    filter_upwards [hae, hbb d' b'] with v h1 h2
    rw [h1]
    congr 1
    ext Y
    rw [mem_latV_iff, mem_latV_iff, h2]
  have hfinS := Filter.eventually_cofinite.1 hae'
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hlat : ∀ v : HeightOneSpectrum (𝓞 F),
      IsClosed (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
        ⋂ a, ⋂ i, (fun Y => Y a i) ⁻¹' intV b v := by
      ext Y; simp [mem_latV_iff]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun i =>
      (hco v).1.isClosed.preimage (by fun_prop)
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) := {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ v, ⋂ (_ : v ∉ S), (fun X => projV v (projFin X)) ⁻¹' latV b v := by
      ext X; simp [hB]
    rw [this]
    exact (isClosed_iInter fun v => isClosed_iInter fun _ => (hlat v).preimage (hcv v)).measurableSet
  have hΦB : Φ = B.indicator fun X => Φinf (projInf X) * ∏ v ∈ S, Φv v (projV v (projFin X)) := by
    funext X
    rw [hΦ X, hfin]
    by_cases hX : X ∈ B
    · rw [Set.indicator_of_mem hX, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      have hvS' : v ∉ S := hvS
      apply hv
      simp only [hout v hvS']
      exact Set.indicator_of_mem (hX v hvS') _
    · rw [Set.indicator_of_notMem hX]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hX
      obtain ⟨v, hvS, hv⟩ := hX
      have hev : ∀ᶠ v in Filter.cofinite, Φv v (projV v (projFin X)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ a i, prV v (X a i) ∈ intV b v :=
          Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => hint _
        filter_upwards [hae', h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show projV w (projFin X) ∈ latV b w from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem hv _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  haveI : SigmaFinite mi := inferInstance
  haveI : ∀ v, SigmaFinite (mv v) := fun v => inferInstance
  obtain ⟨h1, h2⟩ := integral_tensor (ν.restrict B) mi mv projInf (fun v X => projV v (projFin X))
    hci.measurable (fun v => (hcv v).measurable) S (tailProd b mv S) ENNReal.ofReal_ne_top (hP S)
    Φinf Φv (hc.integrable_of_hasCompactSupport hcs)
    (fun v => (hsb v).1.continuous.integrable_of_hasCompactSupport (hsb v).2)
  have h3 := hasProd_of_tail (fun v => ∫ X, Φv v X ∂(mv v)) (fun v => (mv v (latV b v)).toReal)
    (fun v => ENNReal.toReal_nonneg) hsum S (by
      intro v hv
      rw [hout v hv]
      have := integral_indicator_const (μ := mv v) (1 : ℂ) (hlat v).measurableSet
      simpa [Measure.real, Pi.one_def] using this)
  refine ⟨?_, h3.multipliable, ?_⟩
  · rw [hΦB]; exact (integrable_indicator_iff hBm).2 h1
  · rw [h3.tprod_eq, hΦB, integral_indicator hBm, h2]
    rfl

end GlobalTheory.GaugeEx.ProdInt
end

