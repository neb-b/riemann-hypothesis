module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.NormRepStepOfTrace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.StarSqrtMinusD

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ConjEApply
section
noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

theorem cont_conj (A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous fun x : Mt k r => (fun i j => (A * Matrix.of x * B) i j : Mt k r) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply_apply i j).comp ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

def conjE {μ : ℂ} (hμ : μ ≠ 0) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (torS μ⁻¹ k r * Matrix.of x * torS μ k r) i j
  invFun x := fun i j => (torS μ k r * Matrix.of x * torS μ⁻¹ k r) i j
  left_inv x := by
    funext i j
    show (torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r) i j = x i j
    rw [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  right_inv x := by
    funext i j
    show (torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r) i j = x i j
    rw [show torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r =
      (torS μ⁻¹ k r * torS μ k r) * Matrix.of x * (torS μ⁻¹ k r * torS μ k r) by simp only [Matrix.mul_assoc],
      torS_inv_mul μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  measurable_toFun := (cont_conj _ _).measurable
  measurable_invFun := (cont_conj _ _).measurable

theorem conjE_apply {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) = torS μ⁻¹ k r * Matrix.of x * torS μ k r := rfl

theorem conjE_mem_N {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) ∈ Nset k r ↔ Matrix.of x ∈ Nset k r := by
  rw [conjE_apply]
  constructor
  · intro h
    have := tor_conj_N hμ h
    rwa [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one] at this
  · intro h
    have := tor_conj_N (inv_ne_zero hμ) h
    rwa [inv_inv] at this

theorem haarN_tor {μ : ℂ} (hμ : μ ≠ 0) {μN : Measure (Mt k r)} (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) :
    Formalism.MainNotions.S.IsHaarOn (Nset k r) (μN.map (conjE hμ)) := by
  obtain ⟨hsf, hne, hconc, hleft⟩ := hN
  refine ⟨(conjE hμ).sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h0
    apply hne
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h1
    rw [MeasurableEquiv.map_apply, Set.preimage_univ] at h1
    exact Measure.measure_univ_eq_zero.mp h1
  · rw [MeasurableEquiv.map_apply]
    have e : (conjE (k := k) (r := r) hμ) ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} =
        {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq, conjE_mem_N]
    rw [e]; exact hconc
  · have hs' : torS μ k r * s * torS μ⁻¹ k r ∈ Nset k r := tor_conj_N hμ hs
    have hmeas : Measurable (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    have hmeas' : Measurable (lmulM (k := k) (r := r) (torS μ k r * s * torS μ⁻¹ k r)) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    rw [Measure.map_map hmeas (conjE hμ).measurable]
    have e : lmulM (k := k) (r := r) s ∘ (conjE hμ) = (conjE hμ) ∘ lmulM (torS μ k r * s * torS μ⁻¹ k r) := by
      funext x
      simp only [Function.comp_apply]
      change (s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        (torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      calc s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r)
          = (torS μ⁻¹ k r * torS μ k r) * s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) := by
            rw [torS_inv_mul μ hμ, Matrix.one_mul]
        _ = torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r := by
            simp only [Matrix.mul_assoc]
    rw [e, ← Measure.map_map (conjE hμ).measurable hmeas', hleft _ hs']

theorem be_tor {μ : ℂ} (hμ : μ ≠ 0) {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (π π' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (σ σ' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H))
    (hσ : ∀ m, σ' m = σ (torS μ k r * m * torS μ⁻¹ k r)) (hπ : ∀ h ∈ UWset k r z, π' h = π h)
    (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hW : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0) (x y : H) :
    Formalism.FourierDecayAlt.ThreeDimData.be z (c * μ) π' σ' μW (μN.map (conjE hμ)) x y = Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN x y := by
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  have : SigmaFinite (μN.map (conjE hμ)) := (conjE hμ).sigmaFinite_map
  have e : (μW.prod μN).map (Prod.map id (conjE hμ)) = μW.prod (μN.map (conjE hμ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (conjE hμ).measurable, Measure.map_id]
  have hme : MeasurableEmbedding (Prod.map id (conjE (k := k) (r := r) hμ)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Mt k r)) (conjE hμ)).measurableEmbedding
  rw [← e, hme.integral_map]
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p; simp
    rw [es, Measure.prod_prod, hW, zero_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with p hp
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [Prod.map, id]
  have h1 : σ' (Matrix.of p.1 * Matrix.of (conjE hμ p.2)) = σ (Matrix.of p.1 * Matrix.of p.2) := by
    rw [hσ, conjE_apply]
    congr 1
    calc torS μ k r * (Matrix.of p.1 * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r)) * torS μ⁻¹ k r
        = (torS μ k r * Matrix.of p.1 * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.1 * Matrix.of p.2 := by rw [tor_conj_uw hμ hp, torS_mul_inv μ hμ, Matrix.mul_one]
  have h2 : psi k r z (c * μ) (Matrix.of (conjE hμ p.2)) = psi k r z c (Matrix.of p.2) := by
    rw [← psi_tor hμ hz c, conjE_apply]
    congr 1
    calc torS μ k r * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r) * torS μ⁻¹ k r
        = (torS μ k r * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.2 := by rw [torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
  have h3 : π' (Matrix.of p.1)⁻¹ = π (Matrix.of p.1)⁻¹ := hπ _ (PI.UnitaryGroupMassFormula.JCC.uwset_inv hp)
  rw [h1, h2, h3]

end Formalism.L2.SG.RealObj.EnergyIntTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem hJ_adj {n : ℕ} {ε : Fin n → Bool} (s : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat s *ᵥ y) = hJ ε (uMat s⁻¹ *ᵥ x) y := by
  have hU : (uMat s)ᴴ * Formalism.REAL.Jm ε * uMat s = Formalism.REAL.Jm ε := s.2
  have hinv : uMat s * uMat s⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  have hJc : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  have h1 : (uMat s)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s⁻¹ := by
    calc (uMat s)ᴴ * Formalism.REAL.Jm ε = (uMat s)ᴴ * Formalism.REAL.Jm ε * (uMat s * uMat s⁻¹) := by
          rw [hinv, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * uMat s⁻¹ := by rw [← Matrix.mul_assoc, hU]
  have key : (uMat s⁻¹)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s := by
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJc] at h2
    exact h2.symm
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tauU {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) : X.Vpi u →L[ℂ] X.Vpi u :=
  X.psiInfU u s • X.piU u s

def StepSchurG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    IsUnitRep X.B.σs ∧ IsSchur (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) ∧ ‖X.B.tens X.B.w‖ = 1 ∧
      ∀ y : X.B.I.Ginf, (Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y) =
        ((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ

def StepSubG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarSub (X.SinfU u) (muS X u) ∧ IsFolner (X.SinfU u) (muS X u) ∧
      tauU X u 1 = 1 ∧ (∀ s ∈ X.SinfU u, ∀ t ∈ X.SinfU u, tauU X u (s * t) = tauU X u s * tauU X u t) ∧
      SFinite (X.nuQ u)

def StepSection : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∃ h : Cinf X → X.B.I.Ginf, Measurable h ∧ ∀ c ∈ Good X u u', HasDiag X u u' sc c (h c)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem tauU_unit (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) (a b : X.Vpi u) :
    ⟪tauU X u s a, tauU X u s b⟫_ℂ = ⟪a, b⟫_ℂ := by
  simp only [tauU, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, (X.piU_rep u).2.2.1 s hs]
  rw [← mul_assoc, Complex.mul_conj', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU]
  simp

theorem isWAbs_of (hS : StepSchurG) (hG : StepSubG) (u : D.what₂.Word) :
    IsWAbs (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) (X.B.tens X.B.w) (X.SinfU u) (tauU X u)
      (X.nuQ u) (X.Wu u) := by
  obtain ⟨-, -, -, hph⟩ := hS D X
  obtain ⟨-, -, h1, hmul, -⟩ := hG D X u
  have hW := X.Wu_spec u
  refine ⟨h1, hmul, fun s hs a b => tauU_unit X u s hs a b, fun s hs x => ?_, hW.2.2.1, fun x => ?_,
    hW.2.2.2.1, hW.2.2.2.2⟩
  · rw [hW.1 s hs x]; rfl
  · obtain ⟨hi, he⟩ := hW.2.1 x
    have e : (fun y => (((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ) • X.Wu u (x * y)) =
        fun y => Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y • X.Wu u (x * y) :=
      funext fun y => by rw [hph y]
    rw [e]
    exact ⟨hi, he⟩

theorem inner_transfer (hG : StepSubG) (u u' : D.what₂.Word) (φ : X.B.I.Ginf → ℝ≥0∞) (hφ : Measurable φ)
    (γ γ' : X.B.I.Ginf) (a : X.B.I.Ginf) (ha : a ∈ X.SinfU u) (b : X.B.I.Ginf) (hb : b ∈ X.SinfU u')
    (hγ : γ' = a * γ * b⁻¹) :
    ∫⁻ s, ∫⁻ s', φ (s * γ' * s'⁻¹) ∂(muS X u') ∂(muS X u) = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂(muS X u') ∂(muS X u) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hR, -⟩ := (hG D X u).1
  obtain ⟨-, -, -, -, -, -, -, -, -, hR', -⟩ := (hG D X u').1
  subst hγ
  have hin : ∀ s, ∫⁻ s', φ (s * (a * γ * b⁻¹) * s'⁻¹) ∂(muS X u') = ∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u') := by
    intro s
    have e : ∀ s', s * (a * γ * b⁻¹) * s'⁻¹ = s * a * γ * (MeasurableEquiv.mulRight b s')⁻¹ := by
      intro s'
      simp only [MeasurableEquiv.coe_mulRight]
      group
    simp_rw [e]
    rw [← lintegral_map_equiv (fun t => φ (s * a * γ * t⁻¹)) (MeasurableEquiv.mulRight b),
      MeasurableEquiv.coe_mulRight, hR' b hb]
  simp_rw [hin]
  have e2 : ∀ s, (∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u')) =
      (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a s) := by
    intro s
    simp only [MeasurableEquiv.coe_mulRight]
  simp_rw [e2]
  rw [← lintegral_map_equiv (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a),
    MeasurableEquiv.coe_mulRight, hR a ha]

end Formalism.L2.SG.RealObj.EnergyInst
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntOm
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.EnergyIntOm

variable {D : D7} (X : HidaSetting D)

def dsc (lam : ℂ) (sc : ℝ) (a : Fin (D.R.rS + 1)) : ℂ := (lam * (sc : ℂ)) ^ (D.R.rS - a.val)

theorem dsc_ne {lam : ℂ} (hl : lam ≠ 0) {sc : ℝ} (hsc : sc ≠ 0) (a : Fin (D.R.rS + 1)) : dsc (D := D) lam sc a ≠ 0 := by
  unfold dsc
  exact pow_ne_zero _ (mul_ne_zero hl (by exact_mod_cast hsc))

theorem dsc_last (lam : ℂ) (sc : ℝ) : dsc (D := D) lam sc (Fin.last D.R.rS) = 1 := by
  unfold dsc
  simp

theorem q_fvec {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u : D.what₂.Word) (a : Fin (D.R.rS + 1)) :
    Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) a = dsc (D := D) lam sc a • frm X u sc v a := by
  obtain ⟨-, h2, -, h4⟩ := hQ
  have hsc' : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc
  induction a using Fin.lastCases with
  | last =>
    have hl : ¬ (Fin.last D.R.rS).val < D.R.rS := by simp
    unfold Formalism.QuantumDeterminants.fvec
    rw [dite_eq_right hl, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, dsc_last, one_smul]
    unfold frm famSc fam
    simp [Fin.snoc_last]
  | cast b =>
    have hb : (Fin.castSucc b).val < D.R.rS := b.isLt
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    rw [dite_eq_left hb]
    have hbb : (⟨(Fin.castSucc b).val, hb⟩ : Fin D.R.rS) = b := Fin.ext rfl
    rw [hbb, (h4 b b rfl).1]
    unfold dsc frm famSc fam
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc]
    rw [smul_smul, mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hsc'), mul_one]

theorem zhat_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) (trG Q Qi (γ v)) a b =
      star (dsc (D := D) lam sc a) * dsc (D := D) lam sc b * ZX X u u' sc γ v a b := by
  obtain ⟨-, h2, h3, -⟩ := id hQ
  have ea := q_fvec X hQ hsc u a
  have eb := q_fvec X hQ hsc u' b
  unfold ZX Formalism.QuantumDeterminants.Zhat trG
  unfold Formalism.L2.SG.RealObj.Zhat
  beta_reduce
  unfold Formalism.QuantumDeterminants.herm Formalism.L2.SG.HidaSetting.hJ
  rw [← h3]
  have hm : Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q * (Qi * uMat (γ v) * Q) =
      Qᴴ * (Formalism.REAL.Jm (X.B.I.ε v) * (uMat (γ v) * Q)) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ea,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_smul, smul_eq_mul]
  ring

theorem dmin_diag (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (d : Fin (D.R.rS + 1) → ℂ)
    (h : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' g = Matrix.diagonal d) (l : Fin (D.R.rS + 2)) :
    Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' g l = ∏ i : Fin l.val, d (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Formalism.QuantumDeterminants.Dmin
  rw [h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  rfl

theorem mem_om {v : InfinitePlace X.B.I.F} {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : 0 < sc) (u u' : D.what₂.Word) (c : Cinf X) (hc : c ∈ Good X u u') (γ : X.B.I.Ginf)
    (hγ : HasDiag X u u' sc c γ) :
    trG Q Qi (γ v) ∈ Formalism.FourierDecayAlt.JF.Om D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) := by
  have hsc0 : sc ≠ 0 := hsc.ne'
  have hc' : ∀ w, (∀ l, c w l ≠ 0) ∧ 0 < Gv (Tw u) (Tw u') (Matrix.diagonal (c w)) := hc
  have hγ' : ∀ w, ZX X u u' sc γ w = Matrix.diagonal (c w) := hγ
  obtain ⟨dd, hdd⟩ : ∃ dd : Fin (D.R.rS + 1) → ℂ,
      dd = fun a => star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a * c v a := ⟨_, rfl⟩
  have hdiag : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
      (trG Q Qi (γ v)) = Matrix.diagonal dd := by
    ext a b
    rw [zhat_tr X hQ hsc0 u u' γ a b, hγ' v, hdd]
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hdsc : ∀ a, star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a ≠ 0 := fun a =>
    mul_ne_zero (star_ne_zero.mpr (dsc_ne (D := D) hl hsc0 a)) (dsc_ne (D := D) hl hsc0 a)
  have hd0 : ∀ a, dd a ≠ 0 := by
    intro a
    rw [hdd]
    exact mul_ne_zero (hdsc a) ((hc' v).1 a)
  have hDmin := fun l => dmin_diag (D := D) _ _ _ _ hdiag l
  have hTz : ∀ w : D.what₂.Word, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR w)) = Tw w := by
    intro w
    have hQz : Q *ᵥ (Qi *ᵥ rv X.B.I v (X.zR w)) = rv X.B.I v (X.zR w) := by
      rw [Matrix.mulVec_mulVec, hQ.2.1, Matrix.one_mulVec]
    have hJ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v w
    unfold Formalism.L2.SG.HidaSetting.hJ at hJ
    unfold Formalism.QuantumDeterminants.Tz Formalism.QuantumDeterminants.herm
    rw [← hQ.2.2.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Formalism.L2.SG.Pf.LTL.star_dot_conjT, hQz, hJ]
    simp
  unfold Formalism.FourierDecayAlt.JF.Om
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem Q Qi _ hQ.2.1 hQ.2.2.1 (γ v), ?_⟩
  rw [Formalism.FourierDecayAlt.Q.OmPlus, Set.mem_ofPred_eq]
  refine ⟨fun l _ => ?_, ?_⟩
  · rw [hDmin l]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
  · have hlast : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) (Fin.last (D.R.rS + 1)) =
        (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := by
      rw [hDmin]
      have h : ∏ i : Fin (D.R.rS + 1), dd i =
          (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := Fin.prod_univ_castSucc _
      exact h
    have hr : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) ⟨D.R.rS, by omega⟩ = ∏ i : Fin D.R.rS, dd (Fin.castSucc i) := by
      rw [hDmin]
      rfl
    have hsplit : ∏ i : Fin D.R.rS, dd (Fin.castSucc i) =
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) *
          ∏ i : Fin D.R.rS, c v (Fin.castSucc i) := by
      rw [hdd, ← Finset.prod_mul_distrib]
    have hlastd : dd (Fin.last D.R.rS) = c v (Fin.last D.R.rS) := by
      rw [hdd]
      simp [dsc_last]
    have hG := (hc' v).2
    unfold Gv at hG
    rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_last, Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_r,
      Complex.sq_norm, Complex.sq_norm] at hG
    have hE : 0 < Complex.normSq
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) :=
      Complex.normSq_pos.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hdsc _)
    unfold Formalism.QuantumDeterminants.Gf
    rw [hlast, hr, hTz u, hTz u', hsplit, hlastd]
    simp only [Complex.normSq_mul] at hG ⊢
    nlinarith [mul_pos hE hG]

end Formalism.L2.SG.RealObj.EnergyIntOm
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationOfLocal
section
namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

theorem haar_disintegration_of_local (h5 : JacobianCoordinates.P5) (hJ : JacobianCoordinates.JacLoc) (hS : JacobianCoordinates.SecMeasLoc) (hU : JacobianCoordinates.UnimodLoc)
    (hN : JacobianCoordinates.NHLoc) (hR : StepReal) : HaarDisintegrationReal :=
  h5 hJ DiagDCLoc_holds hS hU hN hR

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstAll
section
noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.GE

theorem bruhatHaar_of_sandwich_volLim (hS : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_rhsHaar rhsHaar gaugeShift hS hV

theorem wbHaar_of_rhsWLim (hL : RhsWLim) : WbHaar :=
  wbHaar_of_rhsWHaar rhsWHaar gaugeShiftW hL

theorem gaugeExists_of_sandwich_rhsWLim (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : GaugeExists :=
  gaugeExists_of rhsHaar rhsWHaar wbDataEx hU gaugeShift gaugeShiftW (rhsLim_of hS hV) hL

theorem jacGauge_of_sandwich_gaugeMeasure (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : JacGauge :=
  jacGauge_of (bruhatHaar_of_sandwich_volLim hS hV) (wbHaar_of_rhsWLim hL) (gaugeExists_of_sandwich_rhsWLim hS hV hU hL)

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormRepX
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.SG.Pf.NormRepX

theorem norm_representative_holds (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word)
    (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) : Formalism.L2.SG.Pf.NormRepStep D u u' :=
  PI.NRL.normRepStep_of_trace D u u' (Formalism.L2.SG.Closed.TermStable_holds D u u') hP (Or.inr (PI.NRL.traceOne D))

end Formalism.L2.SG.Pf.NormRepX
end

