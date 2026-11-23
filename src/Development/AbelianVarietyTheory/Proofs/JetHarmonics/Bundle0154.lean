module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotAntiIsometryOfTriangularRelatedPeriods
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.AntiIsom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem exists_emb_not_mem_conjEmb_mem_Ψ (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    ∃ σ τ : E →+* ℂ, σ ∉ X.Ψ ∧ τ ∈ X.Ψ ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = τ := by
  have hconj : ∀ σ : E →+* ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = ComplexEmbedding.conjugate σ := fun σ => by
    ext t; simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, ComplexEmbedding.conjugate_coe_eq]
  obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hρ : ρ ∈ X.Ψ
  · refine ⟨ComplexEmbedding.conjugate ρ, ρ, (X.cmType ρ).1 hρ, hρ, ?_⟩
    ext t
    simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, ComplexEmbedding.conjugate_coe_eq]
  · refine ⟨ρ, _, hρ, ?_, rfl⟩
    rw [hconj]
    by_contra h
    exact hρ ((X.cmType ρ).2 h)

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h0 : X.p0 = 0) (τ : X.Ψ) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ∀ p : Fin r → ℂ,
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm p p).re = -∑ a, Complex.normSq ((P⁻¹ *ᵥ p) a) := by
  obtain ⟨P, hP, hG⟩ := X.signature τ
  refine ⟨P, hP, fun p => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.hermC_normal X hP _ hG p p]
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, h0, mul_assoc, Complex.mul_conj, Complex.re_sum]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_col_emb_eq_of_not_mem_Ψ (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    {σ τ : E →+* ℂ} (hσ : σ ∉ X.Ψ) (hτ : τ ∈ X.Ψ) (hστ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = τ) (i : ℕ)
    (hi : X.p0 - 1 - i < r) :
    _root_.Formalism.L2.PjFree.perFr X x v σ i =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨X.p0 - 1 - i, hi⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
  subst hστ
  unfold _root_.Formalism.L2.PjFree.perFr
  rw [dite_eq_right hσ, dite_eq_left hτ, dite_eq_left hi]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_first_col_self_re_pos (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (τ : X.Ψ) (hp : 0 < X.p0) (hr : 0 < r) :
    0 < (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) ⟨0, hr⟩)
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) ⟨0, hr⟩)).re := by
  have hx' : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG X.Ψ X.Gm X.p0 := hx
  have h := (hx' τ).2 ⟨1, by omega⟩
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 1 = 1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, hp]
  simp only [h1, one_mul] at h
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.det_fin_one] at h
  exact h


open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.AntiIsom.not_antiIsometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → 1 ≤ r → ∀ (a : GL (Fin r) E), (∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = -1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, _root_.Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * _root_.Formalism.L2.PjFree.perFr X x v τ j) → False := by
  intro E _ _ _ r X X' hΨ hp r1 a ha m _ hmout x hx x' hx' A hA hrel
  have hr : 0 < r := r1
  have hiso : ∀ (τ : E →+* ℂ) (u v : Fin r → ℂ),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (((a : Matrix (Fin r) (Fin r) E).map τ) *ᵥ u)
        (((a : Matrix (Fin r) (Fin r) E).map τ) *ᵥ v) = -_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm u v := by
    intro τ u v
    have h := _root_.GlobalTheory.LevelCusp.hermC_of_herm (ε := -1) ha τ u v
    simpa using h
  obtain ⟨σ, τ, hσ, hτ, hστ⟩ := exists_emb_not_mem_conjEmb_mem_Ψ X
  have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
  have hσ' : σ ∉ X'.Ψ := hΨ ▸ hσ
  rcases Nat.eq_zero_or_pos X.p0 with h0 | hp0
  · obtain ⟨P, hP, hPf⟩ := hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero X h0 ⟨τ, hτ⟩
    obtain ⟨P', _, hPf'⟩ := hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero X' (hp ▸ h0) ⟨τ, hτ'⟩
    let p : Fin r → ℂ := Pi.single ⟨0, hr⟩ 1
    have e1 := hPf p
    have e2 := hPf' ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ p)
    simp only at e1 e2
    rw [hiso, Complex.neg_re, e1] at e2
    have s1 : 0 ≤ ∑ i, Complex.normSq ((P⁻¹ *ᵥ p) i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have s2 : 0 ≤ ∑ i, Complex.normSq ((P'⁻¹ *ᵥ ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ p)) i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hzero : ∑ i, Complex.normSq ((P⁻¹ *ᵥ p) i) = 0 := by linarith
    have hw : P⁻¹ *ᵥ p = 0 := by
      funext i
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1
        hzero i (Finset.mem_univ _)
      simpa using h
    have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
    have hp0 : p = 0 := by
      calc p = (P * P⁻¹) *ᵥ p := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    have h := congrFun hp0 ⟨0, hr⟩
    simp [p] at h
  · have hi : X.p0 - 1 - (X.p0 - 1) < r := by omega
    have hi' : X'.p0 - 1 - (X.p0 - 1) < r := by omega
    have hlat : ∀ v ∈ X.Λ,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
      intro v hv
      have h := hrel σ (X.p0 - 1) (by rw [hmout σ hσ]; omega) v hv
      rw [hmout σ hσ, Finset.sum_eq_single (X.p0 - 1)] at h
      · rw [hermC_col_emb_eq_of_not_mem_Ψ X' x' _ hσ' hτ' hστ _ hi', hermC_col_emb_eq_of_not_mem_Ψ X x v hσ hτ hστ _ hi] at h
        have e1 : (⟨X.p0 - 1 - (X.p0 - 1), hi⟩ : Fin r) = ⟨0, hr⟩ := Fin.ext (by simp)
        have e2 : (⟨X'.p0 - 1 - (X.p0 - 1), hi'⟩ : Fin r) = ⟨0, hr⟩ := Fin.ext (by simp; omega)
        have emb_mul : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
            (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
          funext k
          exact RingHom.map_mulVec τ (a : Matrix (Fin r) (Fin r) E) v k
        rw [e1, e2, emb_mul] at h
        exact h
      · intro j hj hne
        rw [hA σ _ _ (by simp at hj; omega), zero_mul]
      · intro h
        simp at h
        omega
    have emb_add : ∀ v w : Fin r → E,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (v + w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v + _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ w := by
      intro v w; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
    have emb_smul : ∀ (e : E) (v : Fin r → E),
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (e • v) = τ e • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
      intro e v; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
    have hE : ∀ v : Fin r → E,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
      intro v
      have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
        rw [X.Λ_span]; trivial
      induction hv using Submodule.span_induction with
      | mem v hv => exact hlat v hv
      | zero =>
        have h0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (0 : Fin r → E) = (0 : ℂ) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ 0 := by
          funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        rw [h0, Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right]
        simp
      | add v w _ _ h1 h2 =>
        rw [emb_add, Matrix.mulVec_add, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_add_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_add_right, h1, h2, mul_add]
      | smul e v _ h =>
        rw [emb_smul, Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, h]
        ring
    have hC : ∀ z : Fin r → ℂ,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ z) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) z := by
      intro z
      rw [pi_eq_sum_univ z, Matrix.mulVec_sum, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.hC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.hC_sum_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right]
      have h := hE (Pi.single k 1)
      have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (Pi.single k (1 : E)) = fun j => if k = j then (1 : ℂ) else 0 := by
        funext j
        by_cases hkj : k = j
        · subst hkj; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        · simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Pi.single_apply, hkj, Ne.symm hkj]
      rw [hs] at h
      rw [h]
      ring
    obtain ⟨u, hu⟩ : ∃ u, (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩ := by
      refine ⟨((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
        Units.mul_inv, map_one, Matrix.one_mulVec]
    have k1 := hC (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    have k2 := hiso τ u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    rw [hu] at k2
    have k3 := hC u
    rw [hu] at k3
    have k4 := _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_symm τ X.Gm X.Gm_herm u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    have k5 : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) =
        -(A σ (X.p0 - 1) (X.p0 - 1) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)) := by
      linear_combination k2 - k1
    rw [k4, k5] at k3
    have hd := hermC_first_col_self_re_pos X hx ⟨τ, hτ⟩ hp0 hr
    have hd' := hermC_first_col_self_re_pos X' hx' ⟨τ, hτ'⟩ (hp ▸ hp0) hr
    simp only at hd hd'
    rw [k3] at hd'
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hd'
    nlinarith [Complex.normSq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)), Complex.normSq_apply (A σ (X.p0 - 1) (X.p0 - 1)),
      sq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)).re, sq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)).im]

end GlobalTheory.AntiIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrame_expansion_framedPoint_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y yF → ∀ (σ : P.U.toUnifPre.SecGF F 1) (θ : Fam P.D.toPre F 1), SecTieF I P F yF.x 1 σ yF.s → P.U.toUnifPre.ExpandsG F 1 σ θ → ThFrame P.D ϖ F θ := by
  first | exact @GlobalTheory.GeneratorFrame.main | exact GlobalTheory.GeneratorFrame.main | (intros; apply GlobalTheory.GeneratorFrame.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem evI_eq_thExpr_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y.1 yF → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ) (xx : Fin n → Dw.La) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x)), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) → ∀ f, IsThRule Xo c nab xx Pp f → algebraMap T.Fr F (evI y f) = thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c nab hnab T io y F _ _ φ hφ yF hm a n xx Pp hP Fs hFs f hf
  letI := H.starRing
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  have hyT := y.2.1
  unfold evI evR evalAt
  rw [dite_eq_left hyT]
  have hm0 := hyT.choose_spec.choose_spec.choose_spec
  have hv0 := hf hyT.choose hyT.choose_spec.choose_spec.choose
  have hvF : ThValAt Xo c nab yF xx Pp (thExpr Xo c nab yF Pp Fs) :=
    ⟨F, inferInstance, inferInstance, AlgHom.id c.F F, yF, Fs, ?_, GlobalTheory.FramedBaseChange.refl yF, hFs, rfl⟩
  · have key := GlobalTheory.ThetaField.thetaValue_natural_field E H Dw l Xo c nab hnab _ F (φ.comp _) _ yF
      (GlobalTheory.FramedBaseChange.trans _ φ hm0 hm) a n xx Pp hP _ _ hv0 hvF
    refine Eq.trans ?_ key
    exact (congrArg (fun g : T.Fr →+* F => g _) hφ).symm
  · exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id

end GlobalTheory.PtTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateThetaFrameGermEqUnitMulBoxProduct
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ColumnSplit

theorem val_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {u : F} {m : ℕ} (hm : 0 < m)
    (h : u ^ m = 1) : v u = 0 := by
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, h, AddValuation.map_one]
  induction hv : v u using WithTop.recTopCoe with
  | top =>
    rw [hv] at h1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp [succ_nsmul] at h1
  | coe a =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero] at h1
    simpa [hm.ne'] using h1

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT, τ.Gen → IsEL P C.xT C.actT C.eT C.wPT τ → ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → ∀ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ → PullAl P.D F P.oD α 1 N θ₁ θα₁ → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → ∃ (u : F) (p₁ : Fin n → QkPt P.D.toPre F (1 * N)) (w₁ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b) (DegPre.lineε (1 * N)))) (ζ₁ : Fin n → F) (r₀ r : Fin n → Fam P.D.toPre F (1 * N)) (σ₁ : Fin n → P.U.toUnifPre.SecGF F q) (f : Fin n → PS F 1 (chD C.ch)), v u = 0 ∧ h = u • boxSer f ∧ ∀ i, (w₁ i).IsGen ∧ FinOrd P.D F (1 * N) (p₁ i) (w₁ i) (ζ₁ i) ∧ P.ToA F (1 * N) (p₁ i) (x ≫ pA.pr i) ∧ PhiRel P.D.toPre F (1 * N) (p₁ i) (w₁ i) θα₁ (r₀ i) ∧ Fam.IsSmul P.D.toPre F (ζ₁ i) (r₀ i) (r i) ∧ P.U.toUnifPre.ExpandsG F q (σ₁ i) (PowGerm.famCast (Dp := P.D.toPre) (F := F) e (r i)) ∧ GermA P.U.toUnifPre (κ := Fin 1 × Fin (chD C.ch)) C.xT τ F q (σ₁ i) (f i) := by
  obtain ⟨hL, hL2, -, hL4, -⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hTr P hTor _ ϖ hϖ Q _ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact τ hτ hEL
    α N hN hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀ t q e σ' h hw _ hfin hpx hΦt hsm hexp hgerm
  subst e
  have hG := hL.globalFns
  have hk : 1 ≤ 1 * N := by omega
  haveI : CharZero T.V := (algebraMap T.V F).charZero
  obtain ⟨p₁, hp, hp₁⟩ := UnboxQk.exists_isBoxQk_toA hL hL2 hL4 hT T.V E H C.I.G P hTor n D' A' G' pD pA pG U' PU F
    (1 * N) hk p
  have hw₁ : ∀ i, ∃ w₁ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b)
      (DegPre.lineε (1 * N))), w₁.IsGen := fun i =>
    H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  choose w₁ hw₁ using hw₁
  choose ζ₁ _ hζ₁ using fun i => H1.finOrdExists_of (phiFun_of hL) (H1.phiPow_of hL) T.V P.D F (1 * N) hk (p₁ i) (w₁ i)
    (hw₁ i)
  choose Φ₁ hΦ₁ using fun i => phiFun_of hL T.V _ P.D F (1 * N) hk (p₁ i) (w₁ i) (hw₁ i)
  obtain ⟨τ₀, hτ₀, hEL₀, hT₀⟩ := frame1St_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT
  have hLB : P.U.LG.L.IsLB := (congrArg RigLB.L P.bundle).symm ▸ C.I.G.PP.isLB
  obtain rfl : τ = τ₀ := funext fun m => TorusExt.gen_ext_val hLB (hτ m) (hτ₀ m) fun y J hJ =>
    (hEL m y J hJ).trans (hEL₀ m y J hJ).symm
  have hz₁ := _root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C
  obtain ⟨gm₁, -, hgm₁⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V P.D P.A C.I.G.G P.U _ _ hz₁ τ hτ
    (hT₀ hTr) F (1 * N) hk
  choose σ₁ hσ₁ hf using fun i => hgm₁ (ζ₁ i • Φ₁ i θα₁)
  have exists_boxFam_multilinear : ∀ k : ℕ, ∃ bx : ((i : Fin n) → Fam P.D.toPre F k) →ₘₗ[F] Fam D'.toPre F k, ∀ (s : Fin n → Fam P.D.toPre F k) (S : Fam D'.toPre F k), IsBoxFam pD F k S s ↔ S = bx s := by
    intro k
    choose bx hbx using BoxFamily.exists_isBoxFam hG T.V n P.D.toPre D'.toPre pD F k
    refine ⟨⟨bx, fun s i a b => BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
      fun s i c a => BoxLinear.box_smul pD (hbx _) (hbx _)⟩, fun s S => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact BoxLinear.box_unique pD h (hbx s)
    · rw [h]; exact hbx s
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear 1
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear (1 * N)
  obtain ⟨u₀, hu₀, hθu⟩ := _root_.GlobalTheory.ThetaFrameLine.main T.V ϖ hϖ D' F v hv _ θ
    (BoxFrame.main T.V ϖ hϖ n P.D D' pD F θ₁ _ hθ₁ ((hbx₁ _ _).2 rfl)) hθ
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 α N 1 hN le_rfl hα
  have hpull := BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact α N 1 hN le_rfl hα
    (fun _ => θ₁) (fun _ => θα₁) _ _ (fun _ => hθα₁) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  have hθα' : θα = u₀ • bx fun _ => θα₁ := by
    rw [(hpl _ _).1 hθα, (hpl _ _).1 hpull, (isSmul_iff _ _ _).1 hθu, map_smul]
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (1 * N) p p₁ hp w₁ hw₁
  have hfin' := finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (1 * N) hk p p₁ hp w₁ w' hw₁ hw' hΦ ζ₁ hζ₁
  obtain ⟨u₁, ⟨m, hm, hum⟩, hu₁⟩ := _root_.GlobalTheory.finOrd_ratio_rootOfUnity T.V ϖ hϖ D' F (1 * N) hk p w' w (∏ i, ζ₁ i) ζ hw' hw hfin' hfin
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL T.V _ D' F (1 * N) hk p w' hw'
  have hbΦ : bx (fun i => Φ₁ i θα₁) = Φ' (bx fun _ => θα₁) :=
    (hΦ' _ _).1 (hΦ _ _ _ _ (fun i => (hΦ₁ i _ _).2 rfl) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  have ht : t = (u₁ * u₀) • bx fun i => ζ₁ i • Φ₁ i θα₁ := by
    rw [(isSmul_iff _ _ _).1 (hu₁ θα _ _ t₀ t ((hΦ' _ _).2 rfl) ((isSmul_iff _ _ _).2 rfl) hΦt hsm), hθα', map_smul,
      MultilinearMap.map_smul_univ, hbΦ, smul_comm (∏ i, ζ₁ i) u₀, smul_smul]
    rfl
  obtain ⟨τn, hτn, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := _root_.GlobalTheory.PowGerm.univPow T.V C.I.G.G G' n _ pG C.xT hz₁
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τn hτn (hτT hTr)
    F (1 * N) hk
  obtain ⟨σb, hσb, -⟩ := hgmex (bx fun i => ζ₁ i • Φ₁ i θα₁)
  have hbox := boxGermSt_holds hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT
    C.eT C.wPT C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (1 * N) hk σ₁ _ _ σb _
    (fun i => ⟨hσ₁ i, hf i⟩) ((hbx _ _).2 rfl) hσb
  refine ⟨u₁ * u₀, p₁, w₁, ζ₁, fun i => Φ₁ i θα₁, fun i => ζ₁ i • Φ₁ i θα₁, σ₁, fun i => gm₁ (ζ₁ i • Φ₁ i θα₁), ?_, ?_,
    fun i => ⟨hw₁ i, hζ₁ i, hp₁ x hpx i, (hΦ₁ i _ _).2 rfl, (isSmul_iff _ _ _).2 rfl, hσ₁ i, hf i⟩⟩
  · rw [AddValuation.map_mul, hu₀, val_eq_zero_of_pow_eq_one v hm hum, add_zero]
  · rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), hgm _ σb _ hσb ((hiff F _ σb _).1 hbox), ht, map_smul]

end GlobalTheory.ColumnSplit
end
end

