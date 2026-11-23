module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHe
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonFrameChange

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

variable {r : ℕ}

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma det_ne_zero_of_form_eq {K G M : Matrix (Fin r) (Fin r) ℂ} (hK : K.det ≠ 0)
    (h : Mᵀ * G * M.map (starRingEnd ℂ) = K) : M.det ≠ 0 := by
  intro hM0
  apply hK
  rw [← h, det_mul, det_mul, det_transpose, hM0, zero_mul, zero_mul]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_smul_left_automorphic_membership (c : ℂ) (K A : Matrix (Fin r) (Fin r) ℂ) :
    Aᵀ * (c • K) * A.map (starRingEnd ℂ) = c • (Aᵀ * K * A.map (starRingEnd ℂ)) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_smul_right_automorphic_membership (a : ℝ) (K A : Matrix (Fin r) (Fin r) ℂ) :
    ((a : ℂ) • A)ᵀ * K * ((a : ℂ) • A).map (starRingEnd ℂ) =
      ((a ^ 2 : ℝ) : ℂ) • (Aᵀ * K * A.map (starRingEnd ℂ)) := by
  rw [transpose_smul]
  have : ((a : ℂ) • A).map (starRingEnd ℂ) = (a : ℂ) • A.map (starRingEnd ℂ) := by
    ext i j
    simp
  rw [this, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  push_cast
  ring

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_mul' (K A B : Matrix (Fin r) (Fin r) ℂ) :
    (A * B)ᵀ * K * (A * B).map (starRingEnd ℂ) =
      Bᵀ * (Aᵀ * K * A.map (starRingEnd ℂ)) * B.map (starRingEnd ℂ) := by
  rw [transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_one' (K : Matrix (Fin r) (Fin r) ℂ) :
    (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * K * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = K := by
  simp [Matrix.map_one]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_conj_eq_of_similitude {J B g : Matrix (Fin r) (Fin r) ℂ} {c : ℂ} (hc : c ≠ 0) (hB : B.det ≠ 0)
    (hsim : Bᵀ * J * B.map (starRingEnd ℂ) = c • J) (hg : gᵀ * J * g.map (starRingEnd ℂ) = J) :
    (B⁻¹ * g * B)ᵀ * J * (B⁻¹ * g * B).map (starRingEnd ℂ) = J := by
  have hinv : (B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ) = c⁻¹ • J := by
    have h1 : (B * B⁻¹)ᵀ * J * (B * B⁻¹).map (starRingEnd ℂ) = J := by
      rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB), form_one']
    rw [form_mul', hsim, form_smul_left_automorphic_membership] at h1
    calc (B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ)
        = c⁻¹ • (c • ((B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ))) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • J := by rw [h1]
  rw [form_mul', form_mul', hinv, form_smul_left_automorphic_membership, hg, form_smul_left_automorphic_membership, hsim, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma exists_transport_haarU_pi {ι : Type} (Ψ Ψ' : Finset ι) (p p' : ℕ) (hΨ : Ψ = Ψ')
    (hp : p = p') :
    ∃ e : (Ψ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p) ≃ᵐ (Ψ' → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p'),
      MeasurePreserving e (Measure.pi fun _ => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarU r p)
        (Measure.pi fun _ => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarU r p') ∧
      ∀ t (τ : Ψ) (τ' : Ψ'), τ.1 = τ'.1 → ((e t τ' : GL (Fin r) ℂ)) = (t τ : GL (Fin r) ℂ) := by
  subst hΨ hp
  refine ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, fun t τ τ' h => ?_⟩
  rw [Subtype.ext h]
  rfl

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
theorem _root_.GlobalTheory.PeterssonFrameChange.frame_change : ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (y' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X →
    y' ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X' →
    (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) →
    ∃ (e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X ≃ᵐ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X')
      (α : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X)
      (u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X),
      MeasurePreserving e (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarR X) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarR X') ∧
      Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧
      ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 →
        _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
            (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ')⁻¹ =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ := by
  intro E _ _ _ r X X' y y' hΨ hp hy hy' hG
  choose tf htf hGt using hG
  set J := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r X.p0 with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  have hJdet : J.det ≠ 0 := by
    intro h
    have := congrArg det hJJ
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  let τ' : X.Ψ → X'.Ψ := fun τ => ⟨τ.1, hΨ ▸ τ.2⟩
  have hy0 : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) = J := hy
  have hy0' : ∀ τ : X'.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r X'.p0 := hy'
  have hM : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)ᵀ * X.Gm.map τ.1 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ).map (starRingEnd ℂ) = J := by
    intro τ
    have := hy0 τ
    rwa [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq] at this
  have hM' : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))ᵀ * X'.Gm.map τ.1 *
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).map (starRingEnd ℂ) = J := by
    intro τ
    have := hy0' (τ' τ)
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, ← hp] at this
    exact this
  have hMdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ).det ≠ 0 := fun τ => det_ne_zero_of_form_eq hJdet (hM τ)
  have hM'det : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).det ≠ 0 := fun τ => det_ne_zero_of_form_eq hJdet (hM' τ)
  set B : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    ((Real.sqrt |tf τ| : ℝ) : ℂ) • ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)) with hBdef
  set s : X.Ψ → ℂ := fun τ => ((|tf τ| / tf τ : ℝ) : ℂ) with hsdef
  have hs0 : ∀ τ, s τ ≠ 0 := by
    intro τ
    simp only [hsdef]
    exact_mod_cast div_ne_zero (abs_ne_zero.mpr (htf τ)) (htf τ)
  have hs2 : ∀ τ, s τ * s τ = 1 := by
    intro τ
    simp only [hsdef]
    rw [← Complex.ofReal_mul, ← sq, div_pow, sq_abs, div_self (pow_ne_zero _ (htf τ)), Complex.ofReal_one]
  have hsim : ∀ τ : X.Ψ, (B τ)ᵀ * J * (B τ).map (starRingEnd ℂ) = s τ • J := by
    intro τ
    have ht := htf τ
    have h1 : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))ᵀ * X.Gm.map τ.1 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).map (starRingEnd ℂ) =
        ((tf τ : ℝ) : ℂ)⁻¹ • J := by
      have := hM' τ
      rw [hGt τ, form_smul_left_automorphic_membership] at this
      rw [← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht), one_smul]
    simp only [hBdef, hsdef]
    rw [form_smul_right_automorphic_membership, Real.sq_sqrt (abs_nonneg _)]
    conv_lhs => rw [← hM τ]
    rw [← form_mul', mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hMdet τ)), h1, smul_smul]
    congr 1
    push_cast
    ring
  have hBdet : ∀ τ, (B τ).det ≠ 0 := by
    intro τ
    refine det_ne_zero_of_form_eq ?_ (hsim τ)
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (hs0 τ)) hJdet
  let Bu : X.Ψ → GL (Fin r) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (B τ) (hBdet τ)
  have hBu : ∀ τ, ((Bu τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B τ := fun τ => rfl
  have hBuinv : ∀ τ, (((Bu τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (B τ)⁻¹ := by
    intro τ
    rw [Matrix.coe_units_inv, hBu]
  have hmem : ∀ g : GL (Fin r) ℂ, g ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 ↔
      (g : Matrix (Fin r) (Fin r) ℂ)ᵀ * J * (g : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = J :=
    fun g => Iff.rfl
  have hαmem : ∀ (g : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0) (τ : X.Ψ),
      (Bu τ)⁻¹ * (g : GL (Fin r) ℂ) * Bu τ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 := by
    intro g τ
    rw [hmem, Units.val_mul, Units.val_mul, hBuinv, hBu]
    exact form_conj_eq_of_similitude (hs0 τ) (hBdet τ) (hsim τ) ((hmem g).mp g.2)
  have humem : ∀ τ : X.Ψ, Bu τ * Bu τ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 := by
    intro τ
    rw [hmem, Units.val_mul, hBu, form_mul', hsim, form_smul_left_automorphic_membership, hsim, smul_smul, hs2, one_smul]
  let α : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X :=
    fun t τ => ⟨(Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ, hαmem (t τ) τ⟩
  let u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X := fun τ => ⟨Bu τ * Bu τ, humem τ⟩
  obtain ⟨e, he, hecoe⟩ := exists_transport_haarU_pi (r := r) X.Ψ X'.Ψ X.p0 X'.p0 hΨ hp
  refine ⟨e, α, u, he, ?_, ?_, ?_⟩
  · have hcont : Continuous α := by
      refine continuous_pi fun τ => Continuous.subtype_mk ?_ _
      exact (continuous_const.mul ((continuous_apply τ).subtype_val)).mul continuous_const
    exact hcont.measurable
  · intro t
    funext τ
    apply Subtype.ext
    show (Bu τ)⁻¹ * ((Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ) * Bu τ =
      (Bu τ * Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * (Bu τ * Bu τ)
    group
  · intro t τ σ hτσ
    obtain rfl : σ = τ' τ := Subtype.ext hτσ.symm
    rw [hecoe (α t) τ (τ' τ) rfl]
    show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (((Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹ = _
    rw [Units.val_mul, Units.val_mul, hBuinv, hBu]
    set c : ℂ := ((Real.sqrt |tf τ| : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by
      simp only [hc]
      exact_mod_cast (Real.sqrt_pos.mpr (abs_pos.mpr (htf τ))).ne'
    have hMB : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * B τ = c • _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) := by
      simp only [hBdef]
      rw [Matrix.mul_smul, mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hMdet τ))]
    have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (B τ)⁻¹ = c⁻¹ • _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ := by
      have : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) = c⁻¹ • (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * B τ) := by
        rw [hMB, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this, Matrix.smul_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hBdet τ)), Matrix.mul_one]
    have h2 : B τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹ = c • (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ := by
      simp only [hBdef]
      rw [Matrix.smul_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hM'det τ)), Matrix.mul_one]
    calc _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * ((B τ)⁻¹ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * B τ) *
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹
        = (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (B τ)⁻¹) * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          (B τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h1, h2]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, inv_mul_cancel₀ hc0,
          one_smul]

end GlobalTheory.PeterssonFrameChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExpUniqFamily

theorem linear_eq_zero_of_discrete {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ]
    (f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, f z ∈ Λ) (z : Fin g → ℂ) : f z = 0 := by
  have hc : Continuous (fun z => (⟨f z, hf z⟩ : Λ)) :=
    f.continuous_of_finiteDimensional.subtype_mk _
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa using this

theorem eq_iff_sub {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  have h := he (z - w) w
  rw [sub_add_cancel] at h
  rw [h]
  exact mul_eq_right

theorem int_eq_of_exp (n n' : ℤ)
    (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n' : ℂ) / k)) : n = n' := by
  have hk : 0 < (n' - n).natAbs + 1 := Nat.succ_pos _
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  generalize hkk : (n' - n).natAbs + 1 = k at hk hm
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : ((n' - n : ℤ) : ℂ) = ((k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hm ⊢
    linear_combination hm
  have h4 : n' - n = k * m := Int.cast_injective h3
  have h5 : n' - n = 0 := Int.eq_zero_of_abs_lt_dvd (m := k) ⟨m, h4⟩ (by
    rw [← hkk, Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem algebraic {O Q L L' : Type} [CommRing O] [Group Q] [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {g : ℕ} (χ : Fin g → O → ℂ) (P : L →+ (Fin g → ℂ)) (P' : L' →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x i, P (a • x) i = χ i a * P x i) (hP' : ∀ (a : O) x i, P' (a • x) i = χ i a * P' x i)
    (iP : Function.Injective P) (iP' : Function.Injective P')
    (dP : DiscreteTopology P.range) (dP' : DiscreteTopology P'.range)
    (e e' : (Fin g → ℂ) → Q) (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (act : O → Q → Q) (hl : ∀ a z, e (fun k => χ k a * z k) = act a (e z))
    (hl' : ∀ a z, e' (fun k => χ k a * z k) = act a (e' z))
    (f f' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, e' (f z) = e z) (hf' : ∀ z, e (f' z) = e' z) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : L ≃ₗ[O] L'), (∀ z, e' (h z) = e z) ∧
      (∀ a, P' (gam a) = h (P a)) ∧
      ∀ (k : ℕ) a b, 0 < k → e ((k : ℂ)⁻¹ • P a) = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  have h1 : ∀ z, f' (f z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P.range (f' ∘ₗ f - LinearMap.id) (fun z => (hk _).1 <|
      (eq_iff_sub e ha _ _).1 (by simp [hf, hf'])) z
  have h2 : ∀ z, f (f' z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ f' - LinearMap.id) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp [hf, hf'])) z
  let d : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => LinearMap.pi fun k => χ k a • LinearMap.proj k
  have hd : ∀ a z, d a z = fun k => χ k a * z k := fun a z => rfl
  have h3 : ∀ a z, f (d a z) = d a (f z) := fun a z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ d a - d a ∘ₗ f) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp only [LinearMap.comp_apply, hf, hd, hl, hl'])) z
  have m1 : ∀ a, ∃ b, P' b = f (P a) := fun a => (hk' _).1 (by rw [hf]; exact (hk _).2 ⟨a, rfl⟩)
  have m2 : ∀ b, ∃ a, P a = f' (P' b) := fun b => (hk _).1 (by rw [hf']; exact (hk' _).2 ⟨b, rfl⟩)
  choose ga hga using m1
  choose de hde using m2
  let gam : L ≃ₗ[O] L' :=
    { toFun := ga
      invFun := de
      map_add' := fun a b => iP' (by simp [hga])
      map_smul' := fun c a => iP' (by
        have e1 : P (c • a) = d c (P a) := funext fun i => hP c a i
        have e2 : P' (c • ga a) = d c (P' (ga a)) := funext fun i => hP' c _ i
        rw [RingHom.id_apply, hga, e1, e2, hga, h3])
      left_inv := fun a => iP (by rw [hde, hga, h1])
      right_inv := fun b => iP' (by rw [hga, hde, h2]) }
  refine ⟨LinearEquiv.ofLinear f f' (LinearMap.ext h2) (LinearMap.ext h1), gam, hf, hga, ?_⟩
  intro k a b hk0 hab
  have hk1 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  rw [← hf, map_smul, ← hga, eq_iff_sub e' ha', hk'] at hab
  obtain ⟨c, hc⟩ := hab
  refine ⟨c, iP' ?_⟩
  show P' (ga a) = _
  rw [map_add (f := _), map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hk1, one_smul]
  abel

theorem isHolTo_fibre {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} (y : V × W → (Sp ℂ ⟶ X)) (h : IsHolTo (Set.univ ×ˢ Set.univ) y) (b : V) :
    IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hd : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have := h1.preimage hd.continuous
    convert this using 1
    ext z
    simp
  · exact h2.comp hd.differentiableOn (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_ex {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (U.Di i) ty P) : IsHolTo Set.univ (fun z => (U.ex i P z).left) :=
  isHolTo_fibre _ (U.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 0

theorem fibrewise {X : Scheme.{0}} (t : SAB H X) (D₁ D₂ : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (hy : y = y') (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd : (∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
      ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
        ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e' (h z)).left = (e z).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') ∧
      ∀ (k : ℕ) (s : 𝟙_ (Over X) ⟶ t.G) a b, 0 < k → toUnit _ ≫ s = e ((k : ℂ)⁻¹ • P a) →
        toUnit _ ≫ s = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  subst hy
  have dk : DiscreteTopology {z // e z = 1} := by
    have h0 : (fun z => e z = 1) = fun z => z ∈ P.range := funext fun z => propext (hk z)
    show DiscreteTopology (Subtype fun z => e z = 1)
    rw [h0]
    exact hP.2.2.1
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  obtain ⟨f, hf, -⟩ := _root_.GlobalTheory.existsUnique_linear_lift_fibre X X t.G t.G y y g g e e' (𝟙 _) (MonoidHom.id _) t.semi.smooth ha ha' hh hh' hd' dk'
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨f', hf', -⟩ := _root_.GlobalTheory.existsUnique_linear_lift_fibre X X t.G t.G y y g g e' e (𝟙 _) (MonoidHom.id _) t.semi.smooth ha' ha hh' hh hd dk
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨h, gam, h1, h2, h3⟩ := algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1 hP.2.1 hP'.2.1
    hP.2.2.1 hP'.2.2.1 e e' ha ha' hk hk' (fun a x => x ≫ t.act.act a) hl hl' f f' hf hf'
  refine ⟨h, gam, fun z => by rw [h1], h2, fun a a' => ?_, fun k s a b hk0 e1 e2 => h3 k a b hk0 (e1.symm.trans e2)⟩
  refine int_eq_of_exp _ _ fun k hk0 => ?_
  have w1 := hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t.G t.PP.L t.PP.isLB ℂ y k _ _ _ _ w2 w1)

end ExpUniqFamily

theorem familyUnif_exp_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i j P P' hP hP' hu
  obtain ⟨h, gam, h1, h2, h3, h4⟩ := ExpUniqFamily.fibrewise Xo.univ.t (U.Di i) (U.Di j) ty P P' hP hP' _ _ hu
    (U.ex i P) (U.ex j P') (U.ex_add i P hP) (U.ex_add j P' hP') (U.ex_ker i P hP) (U.ex_ker j P' hP')
    (U.ex_lin i P hP) (U.ex_lin j P' hP') (U.ex_weil i P hP) (U.ex_weil j P' hP')
    (ExpUniqFamily.isHolTo_ex U i P hP) (ExpUniqFamily.isHolTo_ex U j P' hP') (U.ex_diff i P hP) (U.ex_diff j P' hP')
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  exact ⟨h, gam, h1, h2, h3,
    fun a ha => h4 l.M _ _ _ hM (U.ex_eta i P hP a ha) (U.ex_eta j P' hP' a ha),
    fun a => h4 l.A _ _ _ l.A_pos (U.ex_etaA i P hP a) (U.ex_etaA j P' hP' a)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesOnPeriodSpace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem valAt_eq_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty _ c j f S hS hval i P P' hP hP' x x' hx1 hx2 hx1' hx2'
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hcont : ContinuousOn (fun b => valAt' (y b) ⊤ f) B :=
    ((hhol ⊤ f).2.mono fun b hb => ⟨hb, le_of_eq rfl⟩).continuousOn
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  rw [← e, ← e']
  exact hBc.isPreconnected.constant_of_mapsTo hS.isDiscrete hcont (fun a ha => hval _ (hy2 a ha)) hb hb'

end GlobalTheory.CompRat
end

