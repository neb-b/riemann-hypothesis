module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
section
noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff

namespace GlobalTheory.WeightTwoSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def risingS (σ : ℂ) (m : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j))

def eTerm (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (2 + m i) * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))

def dz (j : I) : (I → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℂ) j

def dzbar (j : I) : (I → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (dz j)

def homFac (z : I → ℂ) : ℂ := ∏ i, ((1 + z i) / (2 * (Real.pi : ℂ) * Complex.I))

def logFac (z : I → ℂ) : ℂ := ((Real.log (Complex.normSq (homFac z)) : ℝ) : ℂ)

def modPt {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (z : I → ℂ) : Φ → ℂ :=
  fun τ => defCoord φ z θ (e.symm τ) / (1 + z (e.symm τ))

@[simp] theorem dz_apply (j : I) (v : I → ℂ) : dz j v = v j := rfl

@[simp] theorem dzbar_apply (j : I) (v : I → ℂ) : dzbar j v = starRingEnd ℂ (v j) := rfl

theorem eTerm_zero (φ : I → E →+* ℂ) (σ : ℂ) (z : I → ℂ) (x : E) : eTerm φ 0 σ z x = defTerm φ 2 z σ x := by
  simp [eTerm, defTerm]

theorem eTerm_origin (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E) :
    eTerm φ m σ 0 x = risingS σ m * term φ 2 m σ x := by
  unfold eTerm risingS term
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

theorem risingS_zero (m : I → ℕ) : risingS 0 m = risingFactor 2 m := by
  simp [risingS, risingFactor]

theorem differentiable_risingS (m : I → ℕ) : Differentiable ℂ fun σ => risingS σ m := by
  unfold risingS
  fun_prop

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

omit [Fintype I] in
theorem one_add_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) (i : I) : 1 + z i ≠ 0 := by
  intro h
  have h1 : z i = -1 := by linear_combination h
  have h2 := hz i
  rw [h1] at h2
  simp at h2

theorem homFac_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) : homFac z ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ => div_ne_zero (one_add_ne_zero hz i)
    (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)

theorem contDiff_homFac : ContDiff ℂ ∞ (homFac : (I → ℂ) → ℂ) := by
  unfold homFac
  exact contDiff_prod fun i _ => (contDiff_const.add (contDiff_apply ℂ (fun _ => ℂ) i)).div_const _

theorem contDiffOn_logFac : ContDiffOn ℝ ∞ (logFac : (I → ℂ) → ℂ) (polydisc I) := by
  have h1 : ContDiff ℝ ∞ (homFac : (I → ℂ) → ℂ) := contDiff_homFac.restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun z : I → ℂ => Complex.normSq (homFac z)) := by
    simp only [Complex.normSq_apply]
    exact ((Complex.reCLM.contDiff.comp h1).mul (Complex.reCLM.contDiff.comp h1)).add
      ((Complex.imCLM.contDiff.comp h1).mul (Complex.imCLM.contDiff.comp h1))
  have h3 : ContDiffOn ℝ ∞ (fun z : I → ℂ => Real.log (Complex.normSq (homFac z))) (polydisc I) :=
    h2.contDiffOn.log fun z hz => (Complex.normSq_pos.2 (homFac_ne_zero hz)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h3

theorem contDiffOn_modPt {Φ : Type} [Fintype Φ] (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) :
    ContDiffOn ℂ ∞ (modPt φ e θ) (polydisc I) := by
  refine contDiffOn_pi.2 fun τ => ?_
  unfold modPt defCoord
  refine ContDiffOn.div ?_ ?_ fun z hz => one_add_ne_zero hz _
  · exact (contDiff_const.add ((contDiff_apply ℂ (fun _ => ℂ) _).mul contDiff_const)).contDiffOn
  · exact (contDiff_const.add (contDiff_apply ℂ (fun _ => ℂ) _)).contDiffOn


omit [Fintype I] in
theorem modPt_im_pos {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (hθ : ∀ i, 0 < (φ i θ).im)
    {z : I → ℂ} (hz : z ∈ polydisc I) (τ : Φ) : 0 < (modPt φ e θ z τ).im := by
  unfold modPt defCoord
  set i := e.symm τ
  have h0 : 0 < Complex.normSq (1 + z i) := Complex.normSq_pos.2 (one_add_ne_zero hz i)
  have h1 : Complex.normSq (z i) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := hz i
    nlinarith [norm_nonneg (z i)]
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ h0
  rw [Complex.normSq_apply] at h1
  have h2 := hθ i
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  nlinarith [mul_pos h2 (sub_pos.2 h1)]

end GlobalTheory.WeightTwoSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormBaseOfValue
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualBase

theorem dualFormBase_of_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → DualFormValue φ → DualFormBase φ := by
  intro E _ _ _ I _ _ φ hcm hval d δ hd hδ hφ η
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have : (d : E) = 0 := by simpa using hδ.symm
    have : d = 0 := by exact_mod_cast this
    omega
  obtain ⟨i0, -⟩ := hcm (Classical.choice (inferInstance : Nonempty (E →+* ℂ)))
  have hconj : IsCMField.complexConj E δ = -δ := by
    apply (φ i0).injective
    rw [IsCMField.complexEmbedding_complexConj, hφ, map_neg, hφ]
    simp [Complex.conj_ofReal]
  have hξ0 : ((η : ℤ) : E) * δ⁻¹ ≠ 0 := mul_ne_zero (by simp) (inv_ne_zero hδ0)
  have hξc : IsCMField.complexConj E (((η : ℤ) : E) * δ⁻¹) = -(((η : ℤ) : E) * δ⁻¹) := by
    rw [map_mul, map_inv₀, hconj, map_intCast, inv_neg, mul_neg]
  obtain ⟨h1, h2⟩ := hval _ hξ0 hξc
  refine ⟨h1, fun B hB ε => ?_⟩
  obtain ⟨h3, h4⟩ := h2 B hB ε
  refine ⟨h3, fun i => ?_⟩
  rw [h4 i, map_mul, map_inv₀, map_intCast, hφ]
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or ε with rfl | rfl <;>
    · push_cast
      field_simp

end GlobalTheory.DualBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormExistsUnique
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

noncomputable section

namespace GlobalTheory.DualFormExists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def riemannBil (ξ : E) : LinearMap.BilinForm ℚ E :=
  LinearMap.mk₂ ℚ (riemann ξ)
    (fun x x' y => by simp [riemann, mul_add, add_mul, map_add (f := _)])
    (fun q x y => by
      simp only [riemann, smul_eq_mul]
      rw [show ξ * (q • x) * IsCMField.complexConj E y = q • (ξ * x * IsCMField.complexConj E y) by
        rw [mul_smul_comm, smul_mul_assoc], map_smul, smul_eq_mul])
    (fun x y y' => by simp [riemann, mul_add, map_add (f := _)])
    (fun q x y => by
      have h : IsCMField.complexConj E (q • y) = q • IsCMField.complexConj E y := map_rat_smul _ q y
      simp only [riemann, smul_eq_mul, h]
      rw [mul_smul_comm, map_smul, smul_eq_mul])

theorem riemannBil_apply (ξ x y : E) : riemannBil ξ x y = riemann ξ x y := rfl

theorem riemann_left_nondeg (ξ : E) (hξ : ξ ≠ 0) (x : E) (hx : ∀ y, riemann ξ x y = 0) : x = 0 := by
  by_contra h0
  have h1 := hx (IsCMField.complexConj E (ξ * x)⁻¹)
  rw [riemann, IsCMField.complexConj_apply_apply,
    mul_inv_cancel₀ (mul_ne_zero hξ h0)] at h1
  rw [show (1 : E) = algebraMap ℚ E 1 by simp, Algebra.trace_algebraMap] at h1
  have := Module.finrank_pos (R := ℚ) (M := E)
  simp at h1
  omega

def riemannClL (ξ : E) : E →ₗ[ℚ] Coh E where
  toFun := riemannCl ξ
  map_add' x x' := by
    ext y; simp [riemannCl, riemann, mul_add, add_mul, map_add (f := _)]
  map_smul' q x := by
    ext y
    show ((riemann ξ (q • x) y : ℚ) : ℂ) = q • ((riemann ξ x y : ℚ) : ℂ)
    rw [← riemannBil_apply, LinearMap.map_smul₂, riemannBil_apply, smul_eq_mul, Rat.cast_mul, Rat.smul_def]

theorem riemannClL_apply (ξ x : E) : riemannClL ξ x = riemannCl ξ x := rfl

theorem riemannCl_apply (ξ x y : E) : riemannCl ξ x y = (riemann ξ x y : ℂ) := rfl

def gram (ξ : E) : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℚ :=
  LinearMap.toMatrix₂ (Module.finBasis ℚ E) (Module.finBasis ℚ E) (riemannBil ξ)

theorem gram_apply (ξ : E) (i j) : gram ξ i j = riemann ξ (Module.finBasis ℚ E i) (Module.finBasis ℚ E j) := by
  simp [gram, LinearMap.toMatrix₂_apply, riemannBil_apply]

theorem gram_det_ne_zero (ξ : E) (hξ : ξ ≠ 0) : (gram ξ).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  apply hv
  set b := Module.finBasis ℚ E
  have hx : (∑ i, v i • b i) = 0 := by
    apply riemann_left_nondeg ξ hξ
    intro y
    rw [← riemannBil_apply, ← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j _
    have := congrFun hv0 j
    simp only [Matrix.vecMul, dotProduct, gram_apply, Pi.zero_apply] at this
    exact mul_eq_zero_of_right _ this
  have := b.linearIndependent
  exact Fintype.linearIndependent_iff.mp this v hx |> funext

end GlobalTheory.DualFormExists

namespace GlobalTheory.DualFormExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_coh : Module.finrank ℂ (Coh E) = Module.finrank ℚ E := by
  rw [← ((Module.finBasis ℚ E).constr ℂ).finrank_eq, Module.finrank_fin_fun]

theorem riemannCl_linInd (ξ : E) (hξ : ξ ≠ 0) :
    LinearIndependent ℂ (fun i => riemannCl ξ (Module.finBasis ℚ E i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set Gc := (gram ξ).map (Rat.castHom ℂ)
  have hdet : Gc.det ≠ 0 := by
    rw [show Gc = (Rat.castHom ℂ).mapMatrix (gram ξ) from rfl, ← RingHom.map_det]
    simpa using gram_det_ne_zero ξ hξ
  have hv : Matrix.vecMul c Gc = 0 := by
    funext j
    have := LinearMap.congr_fun hc (Module.finBasis ℚ E j)
    simpa [Matrix.vecMul, dotProduct, Gc, gram_apply, riemannCl_apply] using this
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ := h
  exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, fun h0 => hi (by simp [h0]), hv⟩)

def clBasis (ξ : E) (hξ : ξ ≠ 0) : Module.Basis (Fin (Module.finrank ℚ E)) ℂ (Coh E) :=
  haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (riemannCl_linInd ξ hξ) (by simp [finrank_coh])

theorem clBasis_apply (ξ : E) (hξ : ξ ≠ 0) (i) : clBasis ξ hξ i = riemannCl ξ (Module.finBasis ℚ E i) := by
  simp [clBasis]

theorem clBasis_repr (ξ : E) (hξ : ξ ≠ 0) (x : E) (i) :
    (clBasis ξ hξ).repr (riemannCl ξ x) i = (((Module.finBasis ℚ E).repr x i : ℚ) : ℂ) := by
  have h : riemannCl ξ x = (clBasis ξ hξ).equivFun.symm (fun i => (((Module.finBasis ℚ E).repr x i : ℚ) : ℂ)) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← riemannClL_apply, ← (Module.finBasis ℚ E).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, clBasis_apply, riemannClL_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext y
    simp [Rat.smul_def]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.DualFormExists

namespace GlobalTheory.DualFormExists

theorem dualForm_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ : E), ξ ≠ 0 →
    ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B := by
  intro E _ _ _ ξ hξ
  set b := Module.finBasis ℚ E
  set cb := clBasis ξ hξ
  set Gc : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ := fun i j => ((gram ξ i j : ℚ) : ℂ)
  refine ⟨Matrix.toLinearMap₂ cb cb Gc, ?_, ?_⟩
  · intro x y
    rw [Matrix.toLinearMap₂_apply]
    simp only [cb, clBasis_repr]
    rw [← riemannBil_apply, ← Matrix.toLinearMap₂_toMatrix₂ b b (riemannBil ξ), Matrix.toLinearMap₂_apply]
    push_cast
    simp [Gc, gram, b]
  · intro B' hB'
    apply LinearMap.ext_basis cb cb
    intro i j
    rw [Matrix.toLinearMap₂_apply_basis, clBasis_apply, clBasis_apply, hB']
    simp [Gc, gram_apply, b]

end GlobalTheory.DualFormExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormValueOfValues
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualFormOrtho

theorem bilin_eq_zero_of_span {V : Type} [AddCommGroup V] [Module ℂ V] (B : LinearMap.BilinForm ℂ V) {s t : Set V}
    (h : ∀ u ∈ s, ∀ v ∈ t, B u v = 0) {a b : V} (ha : a ∈ Submodule.span ℂ s) (hb : b ∈ Submodule.span ℂ t) : B a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem dualFormValue_of_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ ξ : E, ξ ≠ 0 → ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B) →
    (∀ ξ : E, ξ ≠ 0 → IsCMField.complexConj E ξ = -ξ → ∀ B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B →
      ∀ ρ ρ' : E →+* ℂ, (ρ' = ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = (ρ ξ)⁻¹) ∧
        (ρ' ≠ ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = 0)) →
    DualFormValue φ := by
  intro E _ _ _ I _ _ φ hφ hex hval ξ hξ hc
  refine ⟨hex ξ hξ, fun B hB ε => ?_⟩
  have hv := hval ξ hξ hc B hB
  have key : ∀ i j, i ≠ j → ∀ σ : E →+* ℂ, (σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)) →
      (σ = φ j ∨ σ = ComplexEmbedding.conjugate (φ j)) → False :=
    fun i j hij σ h1 h2 => hij ((hφ σ).unique h1 h2)
  have gen : ∀ i j, i ≠ j → ∀ u ∈ ({eCl φ i, fCl φ i} : Set (Coh E)), ∀ v ∈ ({eCl φ j, fCl φ j} : Set (Coh E)), B u v = 0 := by
    rintro i j hij u (rfl | rfl) v (rfl | rfl)
    · exact (hv (φ i) (φ j)).2 fun h => key i j hij (φ j) (Or.inr h) (Or.inl rfl)
    · exact (hv (φ i) (ComplexEmbedding.conjugate (φ j))).2 fun h =>
        key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inr h) (Or.inr rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (φ j)).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (φ j) (Or.inl h) (Or.inl rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (ComplexEmbedding.conjugate (φ j))).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inl h) (Or.inr rfl)
  refine ⟨fun i j hij a ha b hb => ?_, fun i => ?_⟩
  · have h0 : B a b = 0 := bilin_eq_zero_of_span B (gen i j hij) ha hb
    rw [pairing, h0, mul_zero]
  · have h1 : B (eCl φ i) (fCl φ i) = (φ i ξ)⁻¹ := (hv (φ i) (ComplexEmbedding.conjugate (φ i))).1 rfl
    rw [pairing, h1, div_eq_mul_inv]
    ring

end GlobalTheory.DualFormOrtho
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfAgreeOnAffineOpenGenerators
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.AffineOpenAgree

theorem app_restrict_eq (X W : Scheme.{0}) (N : X.Opens) (c : W ⟶ N.toScheme) (hc : ⊤ ≤ (c ≫ N.ι) ⁻¹ᵁ N) :
    (c ≫ N.ι).app N ≫ W.presheaf.map (homOfLE hc).op = N.topIso.inv ≫ c.appTop := by
  have h0 : (⊤ : N.toScheme.Opens) ≤ N.ι ⁻¹ᵁ N := by simp
  have e1 : N.topIso.inv = N.ι.app N ≫ N.toScheme.presheaf.map (homOfLE h0).op := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_app]
    change _ = X.presheaf.map _ ≫ X.presheaf.map _
    exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)
  have e2 := c.naturality (homOfLE h0).op
  rw [e1, Scheme.Hom.comp_app]
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_).symm |>.symm
  refine congrArg (N.ι.app N ≫ ·) ?_
  refine Eq.trans ?_ e2.symm
  rfl

theorem cst_pull {R : Type} [CommRing R] {X W : Scheme.{0}} (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens)
    (c : W ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ N) (x : R) :
    (W.presheaf.map (homOfLE hc).op).hom ((c.app N).hom (GlobalTheory.AbLaw.cst sm N x)) =
      (c ≫ sm).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := by
  have e := c.naturality (homOfLE (le_top : N ≤ ⊤)).op
  have e' := congrArg (fun f => (f ≫ W.presheaf.map (homOfLE hc).op).hom (sm.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))) e
  simp only [Category.assoc, ← Functor.map_comp] at e'
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  refine (e'.trans ?_)
  rw [Scheme.Hom.comp_appTop]
  have : ((TopologicalSpace.Opens.map c.base).map (homOfLE (le_top : N ≤ ⊤)).op.unop).op ≫ (homOfLE hc).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [W.presheaf.map_id, Category.comp_id]
  rfl

end GlobalTheory.AffineOpenAgree

namespace GlobalTheory
open AffineOpenAgree

theorem eq_of_agree_on_generators (R : Type) [CommRing R] (X W : Scheme.{0}) (sm : X ⟶ Spec (CommRingCat.of R))
    (N : X.Opens) (hN : IsAffineOpen N) (m : ℕ) (r : Fin m → Γ(X, N))
    (hgen : ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q) ∧
        g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P)
    (a b : W ⟶ X) (hab : a ≫ sm = b ≫ sm) (ha : ⊤ ≤ a ⁻¹ᵁ N) (hb : ⊤ ≤ b ⁻¹ᵁ N)
    (hr : ∀ l, (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom (r l)) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom (r l))) : a = b := by

  have hφ : ∀ g : Γ(X, N), (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom g) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom g) := by
    let φa : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE ha).op).hom.comp (a.app N).hom
    let φb : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE hb).op).hom.comp (b.app N).hom
    have hc : φa.comp (GlobalTheory.AbLaw.cst sm N) = φb.comp (GlobalTheory.AbLaw.cst sm N) := by
      ext x
      simp only [RingHom.comp_apply, φa, φb]
      rw [cst_pull sm N a ha, cst_pull sm N b hb, hab]
    have hrr : (⇑φa ∘ r) = (⇑φb ∘ r) := funext hr
    have hev : ∀ P : MvPolynomial (Fin m) R, φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) =
        φb (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) := by
      intro P
      rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hc, hrr]
    intro g
    obtain ⟨P, Q, hQ, hg⟩ := hgen g
    have h1 := congrArg φa hg
    have h2 := congrArg φb hg
    rw [map_mul] at h1 h2
    have hu : IsUnit (φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q)) := hQ.map φa
    change φa g = φb g
    refine hu.mul_left_injective ?_
    simp only
    rw [h1, hev P, ← h2, ← hev Q]
  haveI : IsAffine N := hN
  have hra : Set.range a ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact ha trivial
  have hrb : Set.range b ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact hb trivial
  obtain ⟨a', rfl⟩ : ∃ a', a' ≫ N.ι = a := ⟨_, IsOpenImmersion.lift_fac N.ι a hra⟩
  obtain ⟨b', rfl⟩ : ∃ b', b' ≫ N.ι = b := ⟨_, IsOpenImmersion.lift_fac N.ι b hrb⟩
  refine congrArg (· ≫ N.ι) (ext_of_isAffine ?_)
  ext x
  have ea := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N a' ha)
  have eb := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N b' hb)
  have key := ea.symm.trans ((hφ _).trans eb)
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateQuotientRegular
section
open MvPolynomial TensorProduct

namespace GlobalTheory

theorem isRegularRing_quotient_etaleCoordinate : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale →
    ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  intro p _ A _ _ n t het j
  let B := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra B A := (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
  have : Algebra.Etale B A := het
  let I : Ideal B := Ideal.span (X '' ({j} : Set (Fin n)))
  have hQ : IsRegularRing (B ⧸ I) :=
    IsRegularRing.of_ringEquiv (quotientSpanXEquiv (ZMod p) ({j} : Set (Fin n))).symm.toRingEquiv
  have : IsRegularRing (TensorProduct B (B ⧸ I) A) := isRegularRing_of_etale (B ⧸ I) _
  have hI : I.map (algebraMap B A) = Ideal.span {t j} := by
    simp only [I, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    congr 2
    show MvPolynomial.aeval t (X j) = t j
    simp
  have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv.trans
    (Algebra.TensorProduct.comm B A (B ⧸ I)).toRingEquiv
  rw [hI] at e
  exact IsRegularRing.of_ringEquiv e.symm

end GlobalTheory
end

