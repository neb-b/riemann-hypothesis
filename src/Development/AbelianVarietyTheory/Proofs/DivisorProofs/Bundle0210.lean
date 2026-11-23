module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTensorLocalizationInjective
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

theorem integralClosure_tensor_localization_injective : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Function.Injective
      (@algebraMap (Localization.AtPrime (Q.under (integralClosure S L))) (Localization.AtPrime Q)
        _ _ (Localization.AtPrime.algebraOfLiesOver (Q.under (integralClosure S L)) Q)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ _ _ _ _ _ Q _
  set P := Q.under (integralClosure S L) with hP
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
  have h1 : algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (Localization.AtPrime P) x) = 0 := by
    rw [← IsLocalization.mk'_spec (Localization.AtPrime P) x s, map_mul, hz, zero_mul]
  have h2 : algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) x) = 0 := by
    rw [← h1]
    exact (Localization.localRingHom_to_map _ _ _ _ x).symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).1 h2
  have hx : x = 0 := by
    by_contra hx0
    have hxL : (x : L) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have ht' : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) *
        ((1 : D) ⊗ₜ[S] (x : L)) = 0 := by
      have := congrArg (fun y : integralClosure D (TensorProduct S D L) => (y : TensorProduct S D L)) ht
      simpa [algebraMap_integralClosure_tensor_eq] using this
    have hu : ((1 : D) ⊗ₜ[S] (x : L)) * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hxL]
      rfl
    have ht0 : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = 0 := by
      have := congrArg (· * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹))) ht'
      simpa [mul_assoc, hu] using this
    have : (t : integralClosure D (TensorProduct S D L)) = 0 := Subtype.ext ht0
    exact t.2 (this ▸ Q.zero_mem)
  subst hx
  exact IsLocalization.mk'_zero _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralComplexGaussianPosDefHermitianPartStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ), (A + Aᴴ).PosDef → A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧ ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  first | exact @GlobalTheory.MatrixGaussian.integral_gaussian | exact GlobalTheory.MatrixGaussian.integral_gaussian | (intros; apply GlobalTheory.MatrixGaussian.integral_gaussian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFormsEqSpanIntegralRationalForms
section
open NumberField

namespace GlobalTheory
open Formalism.IndefR.Arith

theorem mall_eq_span_rat (LL Ks WL G0 : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (hK : A.IsKsForm) (hρ : ∀ u : J0, ∀ f ∈ A.WK, A.ρ u f ∈ A.WK) (hc : ∀ u : J0, ((A.chi u * lam0 u : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)) : A.Mall J0 lam0 = Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0} := by
  apply le_antisymm
  swap
  · rw [Submodule.span_le]
    rintro y ⟨hy1, hy2⟩
    exact ⟨Submodule.subset_span hy1, hy2⟩
  obtain ⟨n, b, hbK, _, hspK, hliL, hspL⟩ := hK

  set ψ : (Fin n → LL) →ₗ[LL] WL := Fintype.linearCombination LL b with hψdef
  have hψ : ∀ y, ψ y = ∑ k, y k • b k := fun y => by simp [hψdef, Fintype.linearCombination_apply]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hψ] at hy
    funext i
    exact Fintype.linearIndependent_iff.1 hliL y hy i
  set e : (Fin n → Ks) → (Fin n → LL) := fun x i => algebraMap Ks LL (x i) with he
  have hψe : ∀ x, ψ (e x) = ∑ k, x k • b k := fun x => by
    rw [hψ]; simp [he, algebraMap_smul]

  have hex : ∀ (p : J0) (k : Fin n), ∃ c : Fin n → Ks, ∑ i, c i • b i = A.ρ p (b k) := by
    intro p k
    have : A.ρ p (b k) ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact hρ p _ (hbK k)
    exact (Submodule.mem_span_range_iff_exists_fun Ks).1 this
  choose cc hcc using hex
  let Am : J0 → Matrix (Fin n) (Fin n) Ks := fun p => Matrix.of fun i k => cc p k i
  choose lamK hlamK using hc
  have hρψ : ∀ (p : J0) y, A.ρ p (ψ y) = ψ (((Am p).map (algebraMap Ks LL)).mulVec y) := by
    intro p y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hψ, hψ, map_sum]
    simp only [LinearMap.map_smul, ← hcc, Finset.smul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Am, Finset.sum_smul, mul_smul, algebraMap_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact smul_comm _ _ _
  have hmemT : ∀ y, ψ y ∈ A.typeP J0 lam0 ↔ ∀ p : J0, ((Am p).map (algebraMap Ks LL)).mulVec y = algebraMap Ks LL (lamK p) • y := by
    intro y
    rw [FormsL.mem_typeP]
    refine forall_congr' fun p => ?_
    rw [hρψ, hlamK p, ← LinearMap.map_smul]
    exact hψinj.eq_iff
  let Wt : Submodule Ks (Fin n → Ks) :=
    { carrier := {x | ∀ p, (Am p).mulVec x = lamK p • x}
      zero_mem' := fun p => by simp
      add_mem' := fun {x y} hx hy p => by simp [Matrix.mulVec_add, hx p, hy p, smul_add]
      smul_mem' := fun a x hx p => by
        show (Am p).mulVec (a • x) = lamK p • (a • x)
        rw [Matrix.mulVec_smul, hx p, smul_smul, smul_smul, mul_comm] }
  let φ : (Fin n → Ks) →ₗ[𝓞 Ks] WL := (Fintype.linearCombination Ks b).restrictScalars (𝓞 Ks)
  let M : Submodule (𝓞 Ks) (Fin n → Ks) := A.MK.comap φ
  have hMmem : ∀ x, x ∈ M ↔ ∑ k, x k • b k ∈ A.MK := fun x => by simp [M, φ, Fintype.linearCombination_apply]
  have hI1 := (_root_.GlobalTheory.rational_eigen_image_span Ks LL n J0 Am lamK 0).1
  have hI2 := _root_.GlobalTheory.span_inf_span_eq_span_inf_of_rational Ks LL n M Wt
  let ψO : (Fin n → LL) →ₗ[𝓞 LL] WL := ψ.restrictScalars (𝓞 LL)
  rintro y ⟨hy1, hy2⟩
  have hle : Submodule.span (𝓞 LL) (A.MK : Set WL) ≤ (Submodule.span (𝓞 LL) (e '' (M : Set _))).map ψO := by
    rw [Submodule.span_le]
    intro m hm
    have hmK : m ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact A.MK_le_WK hm
    obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).1 hmK
    refine ⟨e x, Submodule.subset_span ⟨x, (hMmem x).2 (hx ▸ hm), rfl⟩, ?_⟩
    show ψ (e x) = m
    rw [hψe, hx]
  obtain ⟨z, hz, rfl⟩ := hle hy1
  have hzW : z ∈ Submodule.span LL (e '' (Wt : Set _)) := (hI1 z).1 ((hmemT z).1 hy2)
  have hz2 : z ∈ Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) := by
    rw [← hI2]; exact ⟨hz, hzW⟩
  have hle2 : Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) ≤ (Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0}).comap ψO := by
    rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxM, hxW⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, ?_⟩
    · show ψ (e x) ∈ A.MK
      rw [hψe]; exact (hMmem x).1 hxM
    · show ψ (e x) ∈ A.typeP J0 lam0
      rw [hmemT]; exact (hI1 (e x)).2 (Submodule.subset_span ⟨x, hxW, rfl⟩)
  exact hle2 hz2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwinerEq
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem invariantForm_translate_eq_zero (h : IsHeis σ w γ W) {P Q : X →ₗ[R] X} (hPP : ∀ x, P (P x) = P x)
    (hadj : ∀ x y, γ (P x) y = γ x (Q y)) {C : Submodule R X} (hC : SelfDual γ C) (hQC : ∀ a ∈ C, Q a ∈ C)
    (ℓ : M →ₗ[ℂ] ℂ) (hl : ∀ u m, ℓ (W (Q u) m) = ℓ m) {e : M} (he : Fixes W C e) {z : X} (hz : P z ∉ C) :
    ℓ (W (P z) e) = 0 := by
  have hex : ¬ ∀ a ∈ C, γ (P z) a = 1 := fun H => hz ((hC (P z)).2 H)
  push Not at hex
  obtain ⟨a, ha, hne⟩ := hex
  have hQa : W (Q a) e = e := he _ (hQC a ha)
  have hg : γ (P z) (Q a) = γ (P z) a := by rw [← hadj, hPP]
  have hc : W (Q a) (W (P z) e) = γ (Q a) (P z) • W (P z) e := by rw [h.comm, hQa]
  have key := hl a (W (P z) e)
  rw [hc, map_smul, smul_eq_mul] at key
  have hs : γ (Q a) (P z) ≠ 1 := by
    rw [h.swap, hg]
    intro h1
    exact hne (inv_eq_one.1 h1)
  by_contra h0
  exact hs (mul_right_cancel₀ h0 (key.trans (one_mul _).symm))

end

theorem invariantForm_normOp_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ P Q : X →ₗ[R] X, (∀ x, P (P x) = P x) → (∀ x, Q (Q x) = Q x) → (∀ x, P (Q x) = 0) → (∀ x, Q (P x) = 0) → (∀ x y, γ (P x) y = γ x (Q y)) → (∀ a ∈ A, P a ∈ A) → (∀ a ∈ A, Q a ∈ A) → (∀ x, φ (P x) = P (φ x)) → (∀ x, φ (Q x) = Q (φ x)) → (∀ x, φ x - P (φ x) - Q (φ x) = x - P x - Q x) → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ m, ℓ (T m) = (lam (idx A (A.map φ)))⁻¹ * (n : ℂ) * ℓ m := by
  intro R X M _ _ _ _ _ σ w γ W h lam A hA hspan φ hφ hφA hidx T hT hTe P Q hPP hQQ hPQ hQP hadj hPA hQA hφP hφQ hφr
  have hQadj : ∀ u v, γ (Q u) v = γ u (P v) := fun u v => by
    rw [h.swap, ← hadj, ← h.swap]
  have hPr : ∀ u y, γ (P u) (y - P y - Q y) = 1 := fun u y => by
    rw [hadj, map_sub, map_sub, hQP, hQQ, sub_zero, sub_self, h.zero_right]
  have hQr : ∀ u y, γ (Q u) (y - P y - Q y) = 1 := fun u y => by
    rw [hQadj, map_sub, map_sub, hPP, hPQ, sub_self, sub_zero, h.zero_right]
  have hrP : ∀ u y, γ (y - P y - Q y) (P u) = 1 := fun u y => by
    rw [h.swap, hPr, inv_one]
  have hsm : ∀ y : X, w • (y - P y - Q y) = w • y - P (w • y) - Q (w • y) := fun y => by
    simp only [smul_sub, map_smul]

  have hsplit : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ (y : X) (v : M),
      γ (w • Q y) (y - Q y) * ℓ (W y v) = ℓ (W (y - P y - Q y) (W (P y) v)) := by
    intro ℓ hl y v
    have e1 := hl y (W (y - Q y) v)
    rw [h.comp, show Q y + (y - Q y) = y by abel, map_smul, smul_eq_mul] at e1
    rw [e1, h.comp, hsm, hrP, one_smul, show y - P y - Q y + P y = y - Q y by abel]
  have hinvρ : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ y : X,
      ∀ u m, (ℓ.comp (W (y - P y - Q y))) (W (Q u) m) = (ℓ.comp (W (y - P y - Q y))) m := by
    intro ℓ hl y u m
    simp only [LinearMap.comp_apply]
    rw [h.comm, map_smul, smul_eq_mul, h.swap, hQr, inv_one, one_mul, hl]
  have hinvT : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) →
      ∀ u m, (ℓ.comp T) (W (Q u) m) = (ℓ.comp T) m := by
    intro ℓ hl u m
    simp only [LinearMap.comp_apply]
    rw [hT, hφQ, hl]

  have hterm : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ e, Fixes W A e →
      ∀ b ∈ A.map φ, ℓ (W b e) = ℓ (W (P b) e) := by
    intro ℓ hl e he b hb
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hb
    have hQb : Q (φ a) ∈ A.map φ := by
      rw [← hφQ]; exact Submodule.mem_map_of_mem (hQA a ha)
    have hd : φ a - Q (φ a) ∈ A.map φ := Submodule.sub_mem _ hb hQb
    have hr : φ a - P (φ a) - Q (φ a) ∈ A := by
      rw [hφr]; exact Submodule.sub_mem _ (Submodule.sub_mem _ ha (hPA a ha)) (hQA a ha)
    have h1 : W (Q (φ a)) (W (φ a - Q (φ a)) e) = W (φ a) e := by
      rw [h.comp, h.iso hφA (Submodule.smul_mem _ w hQb) hd, one_smul,
        show Q (φ a) + (φ a - Q (φ a)) = φ a by abel]
    have h2 : W (P (φ a)) (W (φ a - P (φ a) - Q (φ a)) e) = W (φ a - Q (φ a)) e := by
      rw [h.comp, ← map_smul P w (φ a), hPr, one_smul,
        show P (φ a) + (φ a - P (φ a) - Q (φ a)) = φ a - Q (φ a) by abel]
    rw [← h1, hl, ← h2, he _ hr]
  obtain ⟨k, f, hf, ht⟩ := exists_transversal_of_idx_ne_zero A (A.map φ) hidx

  have hE : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ e, Fixes W A e →
      ℓ (T e) = (lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ) * ℓ e := by
    intro ℓ hl e he
    rw [hTe e he]
    unfold normOp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(sumOp_eq_sum_transversal h A (A.map φ) hφA e he (Fin k) f hf ht).1, map_smul, map_sum,
      smul_eq_mul, mul_assoc]
    congr 1
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hterm ℓ hl e he (f i) (hf i)]
    by_cases hm : P (f i) ∈ A
    · simp [hm, he _ hm]
    · rw [invariantForm_translate_eq_zero h hPP hadj hA hQA ℓ hl he hm]
      simp [hm]

  have hmain : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ x e, Fixes W A e →
      ℓ (T (W x e)) = (lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ) * ℓ (W x e) := by
    intro ℓ hl x e he
    have hs0 := h.ne_zero (w • Q x) (x - Q x)
    have hA1 := hsplit ℓ hl x e
    have hB1 := hsplit ℓ hl (φ x) (T e)
    rw [hφr, ← hφQ, ← hφP, ← map_smul φ w (Q x), ← map_sub φ x (Q x), hφ, ← hT, ← hT] at hB1
    by_cases hp : P x ∈ A
    · rw [he _ hp] at hA1 hB1
      have h3 := hE (ℓ.comp (W (x - P x - Q x))) (hinvρ ℓ hl x) e he
      simp only [LinearMap.comp_apply] at h3
      rw [h3, ← hA1] at hB1
      apply mul_left_cancel₀ hs0
      rw [hB1]
      ring
    · have z1 := invariantForm_translate_eq_zero h hPP hadj hA hQA _ (hinvρ ℓ hl x) he hp
      have z2 := invariantForm_translate_eq_zero h hPP hadj hA hQA _ (hinvT _ (hinvρ ℓ hl x)) he hp
      simp only [LinearMap.comp_apply] at z1 z2
      rw [z1] at hA1
      rw [z2] at hB1
      rw [(mul_eq_zero.1 hA1).resolve_left hs0, (mul_eq_zero.1 hB1).resolve_left hs0, mul_zero]
  refine ⟨(Finset.univ.filter (fun i => P (f i) ∈ A)).card, ?_, ?_⟩
  · obtain ⟨i, hi, -⟩ := ht 0 (Submodule.zero_mem _)
    refine Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hPA _ ?_⟩⟩
    simpa using A.neg_mem hi
  · intro ℓ hl m
    have hle : (⊤ : Submodule ℂ M) ≤ LinearMap.ker (ℓ.comp T - ((lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ)) • ℓ) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨x, e, he, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hmain ℓ hl x e he, sub_self]
    have hm := hle (Submodule.mem_top (x := m))
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul] at hm
    exact sub_eq_zero.1 hm

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpacePullbackAffineOpenOfIsDomainTensStatement
section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    (letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f))) := by
  intro F _ X g V hV k _ f
  let : Algebra F Γ(X, V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let : Algebra F k := f.toAlgebra
  intro hdom
  have hSpec : hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hComp : V.ι ≫ g = hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← hSpec, IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  let m := pullback.map (V.ι ≫ g) (spMap f) (Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))))
    (Spec.map (CommRingCat.ofHom (algebraMap F k))) hV.isoSpec.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hComp]) (by simp only [Category.comp_id, Category.id_comp]; rfl)
  let e : pullback (V.ι ≫ g) (spMap f) ≅ Spec (CommRingCat.of (Γ(X, V) ⊗[F] k)) :=
    asIso m ≪≫ pullbackSpecIso F Γ(X, V) k
  have : IsDomain (Γ(X, V) ⊗[F] k) :=
    MulEquiv.isDomain (k ⊗[F] Γ(X, V)) (Algebra.TensorProduct.comm F Γ(X, V) k).toRingEquiv.toMulEquiv
  have : IrreducibleSpace (Spec (CommRingCat.of (Γ(X, V) ⊗[F] k))) :=
    PrimeSpectrum.irreducibleSpace (R := Γ(X, V) ⊗[F] k)
  exact Function.Surjective.irreducibleSpace e.inv.homeomorph.continuous e.inv.homeomorph.surjective
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeMaximalIdeal
section
open IsLocalRing

namespace GlobalTheory

theorem isAdicComplete_of_le_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R →
        IsAdicComplete I R := by
  intro R _ _ _ hm I hI
  exact isAdicComplete_of_le_of_isNoetherianRing R I (maximalIdeal R) hI hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

def chartHom {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] (u : Sp S ⟶ Y)
    (h : u ⁻¹ᵁ V = ⊤) : Γ(Y, V) →+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (u.appLE V ⊤ h.ge).hom

def IsCombIn {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) : Prop :=
  ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw : ∀ i, w i ⁻¹ᵁ V = ⊤), ∀ x : Γ(Y, V),
    chartHom V c hc x = chartHom V u hu x + ∑ i, a i * (chartHom V (w i) (hw i) x - chartHom V u hu x)

end GlobalTheory.SecGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlace
section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace GlobalTheory.BoundedGL

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem isCompact_le (c : WithZero (Multiplicative ℤ)) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ c} := by
  by_cases hc : c = 0
  · have e : {x : w.adicCompletion E | Valued.v x ≤ c} = {0} := by
      ext x
      simp [hc]
    rw [e]
    exact isCompact_singleton
  · obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
    set u : w.adicCompletion E := ((π ^ (-WithZero.log c) : E) : w.adicCompletion E) with hu
    have hvu : Valued.v u = c := by
      rw [hu, valuedAdicCompletion_eq_valuation', map_zpow₀, hπ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hc]
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, map_zero] at hvu
      exact hc hvu.symm
    have hO : IsCompact {x : w.adicCompletion E | Valued.v x ≤ 1} := by
      have := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers w
      convert this using 1
      ext x
      simp [mem_adicCompletionIntegers]
    have e : {x : w.adicCompletion E | Valued.v x ≤ c} = (fun y => u * y) '' {x | Valued.v x ≤ 1} := by
      ext x
      constructor
      · intro hx
        refine ⟨u⁻¹ * x, ?_, by simp [hu0]⟩
        show Valued.v (u⁻¹ * x) ≤ 1
        rw [map_mul, map_inv₀, hvu]
        exact inv_mul_le_one_of_le₀ hx zero_le'
      · rintro ⟨y, hy, rfl⟩
        show Valued.v (u * y) ≤ c
        rw [map_mul, hvu]
        exact mul_le_of_le_one_right' hy
    rw [e]
    exact hO.image (continuous_const_mul u)

theorem isCompact_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  intro E _ _ w n c
  set K := w.adicCompletion E
  set S : Set (Matrix (Fin n) (Fin n) K) := {A | ∀ i j, Valued.v (A i j) ≤ c} with hS
  have hK : IsCompact S := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_le w c
    have e : S = (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) K)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

end GlobalTheory.BoundedGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldAStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt : (∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R) → (∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (h : A), IsExcisionNbhd A A' h → ∀ a b : A', a * b - 1 ∈ Ideal.span {algebraMap A A' h} → IsExcisionNbhd A (Localization.Away a) h := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away) | (exact GlobalTheory.EtC.isExcisionNbhd_away) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away  <;> assumption)
end

