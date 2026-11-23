module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0025

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HpkExHolds
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem meas_invM : Measurable (invM : Mt k r → Mt k r) := by
  unfold invM
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hc : Continuous fun x : Mt k r => ((Matrix.of x).adjugate : Mt k r) := hof.matrix_adjugate
  have hdc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r).det := hof.matrix_det
  have hd : Measurable fun x : Mt k r => Ring.inverse (Matrix.of x : Mat k r).det := by
    simp only [Ring.inverse_eq_inv']
    exact hdc.measurable.inv
  have he : (fun x : Mt k r => (((Matrix.of x : Mat k r)⁻¹ : Mat k r) : Mt k r)) =
      fun x : Mt k r => (Ring.inverse (Matrix.of x).det • (Matrix.of x).adjugate : Mt k r) := by
    funext x
    rw [Matrix.inv_def]
  have hc' : Measurable (β := Mt k r) fun x : Mt k r => ((Matrix.of x).adjugate : Mt k r) :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable
  rw [he]
  exact hd.smul hc'

theorem meas_mulM : Measurable (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  have hc : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r)) :=
    Continuous.matrix_mul continuous_fst continuous_snd
  exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
    ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable

def Cm (g : Mt k r) (p : SS k r) : Mt k r := mulM (mulM (mulM (mulM (p.1.1, p.1.2), g), p.2.2), p.2.1)

def Tm (g : Mt k r) (p : Mt k r × Mt k r) : Mt k r := mulM (mulM (p.1, g), invM p.2)

theorem meas_Cm (g : Mt k r) : Measurable (Cm g) := by
  unfold Cm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp ((hm.comp ((hm.comp (measurable_fst.fst.prodMk measurable_fst.snd)).prodMk
    measurable_const)).prodMk measurable_snd.snd)).prodMk measurable_snd.fst)

theorem meas_Tm (g : Mt k r) : Measurable (Tm g) := by
  unfold Tm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp (measurable_fst.prodMk measurable_const)).prodMk (meas_invM.comp measurable_snd))

theorem tgt_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hB : B.map invM = B) (hA' : A'.map invM = A') (g : Mt k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ s, ∫⁻ s', φ (Tm g (s, s')) ∂(Formalism.MainNotions.S.muS A' B) ∂(Formalism.MainNotions.S.muS A B) =
      ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hm := meas_mulM (k := k) (r := r)
  have hi := meas_invM (k := k) (r := r)
  have hT := meas_Tm g
  have hmu : ∀ X Y : Measure (Mt k r), Formalism.MainNotions.S.muS X Y = (X.prod Y).map mulM := fun _ _ => rfl
  rw [hmu, hmu]
  have step1 : ∀ s, ∫⁻ s', φ (Tm g (s, s')) ∂((A'.prod B).map mulM) =
      ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) := fun s =>
    lintegral_map (hφ.comp (hT.comp (measurable_const.prodMk measurable_id))) hm
  rw [lintegral_congr step1]
  have hH : Measurable fun s => ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) :=
    Measurable.lintegral_prod_right' (f := fun q : Mt k r × (Mt k r × Mt k r) => φ (Tm g (q.1, mulM q.2)))
      (hφ.comp (hT.comp (measurable_fst.prodMk (hm.comp measurable_snd))))
  rw [lintegral_map hH hm]
  have hF : Measurable fun p : (Mt k r × Mt k r) × (Mt k r × Mt k r) => φ (Tm g (mulM p.1, mulM p.2)) :=
    hφ.comp (hT.comp ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)))
  rw [← lintegral_prod _ hF.aemeasurable]
  have hpt : ∀ p : (Mt k r × Mt k r) × (Mt k r × Mt k r),
      Tm g (mulM p.1, mulM p.2) = Cm g (Prod.map id (Prod.map invM invM) p) := by
    intro p
    show (Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.1 * Matrix.of p.2.2)⁻¹ : Mat k r) =
      Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹
    rw [Matrix.mul_inv_rev]
    exact (mul_assoc _ _ _).symm
  simp only [hpt]
  have h2 : (A'.prod B).map (Prod.map invM invM) = A'.prod B := by
    rw [← Measure.map_prod_map A' B hi hi, hA', hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map id (Prod.map invM invM)) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ measurable_id (hi.prodMap hi), Measure.map_id, h2]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) (measurable_id.prodMap (hi.prodMap hi))).symm.trans ?_
  rw [hP]
  rfl

theorem src_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hA : A.map invM = A) (hB : B.map invM = B) (g : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ p, φ (sgs p g) ∂((A.prod B).prod (A'.prod B)) = ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hi := meas_invM (k := k) (r := r)
  have hpt : ∀ p : SS k r, (sgs p g : Mt k r) = Cm g (Prod.map (Prod.map invM invM) id p) := fun _ => rfl
  simp only [hpt]
  have h1 : (A.prod B).map (Prod.map invM invM) = A.prod B := by
    rw [← Measure.map_prod_map A B hi hi, hA, hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map (Prod.map invM invM) id) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ (hi.prodMap hi) measurable_id, Measure.map_id, h1]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) ((hi.prodMap hi).prodMap measurable_id)).symm.trans ?_
  rw [hP]
  rfl

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 HaarTranslationMeasurability

theorem hpkEx_holds : HpkEx := by
  intro k r z z' hk hz hz' hT hT' μ μW μW' μN hμ hW hW' hN μsec hsec
  obtain ⟨μG0, hG0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨μW0, hW0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μW0', hW0'⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z' hz' hT'
  obtain ⟨μN0, hN0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have hD : IsMeasData k r z z' μsec μG0 μW0 μN0 μW0' := ⟨hk, hz, hz', hT, hT', hG0, hW0, hN0, hW0', hsec⟩
  obtain ⟨C, hC, hInt⟩ := Formalism.FourierDecayAlt.P.integration_formula_constant k r z z' μsec μG0 μW0 μN0 μW0' hD
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  obtain ⟨a, ha0, hat, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cG hG0 hμ
  obtain ⟨b, hb0, hbt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW hW0 hW
  obtain ⟨b', hb0', hbt', rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW' hW0' hW'
  obtain ⟨d, hd0, hdt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cN hN0 hN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0'
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN0
  have iW := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0 cW hW0
  have iW' := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0' cW' hW0'
  have iN := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μN0 cN hN0
  have jW' : (b' • μW0').map invM = b' • μW0' := by
    rw [Measure.map_smul b' meas_invM.aemeasurable, iW']
  have jN : (d • μN0).map invM = d • μN0 := by
    rw [Measure.map_smul d meas_invM.aemeasurable, iN]
  set κ : ℝ≥0∞ := b * d * (b' * d) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ, hb0, hd0, hb0']
  have hκt : κ ≠ ⊤ := by simp [hκ, ENNReal.mul_eq_top, hbt, hdt, hbt']
  have key : ∀ (g : Mat k r) (φ : Mt k r → ℝ≥0∞), Measurable φ →
      ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * g * (Matrix.of s')⁻¹) i j)
          ∂(Formalism.MainNotions.S.muS (b' • μW0') (d • μN0)) ∂(Formalism.MainNotions.S.muS (b • μW0) (d • μN0)) =
        κ * ∫⁻ p, φ (sgs p g) ∂((μW0.prod μN0).prod (μW0'.prod μN0)) := by
    intro g φ hφ
    have := tgt_eq (b • μW0) (d • μN0) (b' • μW0') jN jW' g φ hφ
    refine this.trans ?_
    rw [src_eq μW0 μN0 μW0' iW iN g φ hφ]
    simp only [Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, smul_eq_mul, hκ]
    ring
  have hne : a * (C : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hat ENNReal.coe_ne_top
  have hne0 : a * (C : ℝ≥0∞) ≠ 0 := mul_ne_zero ha0 (by exact_mod_cast hC.ne')
  refine ⟨(a * C / κ).toReal, ENNReal.toReal_pos (by simp [ENNReal.div_eq_zero_iff, hne0, hκt])
    (ENNReal.div_lt_top hne hκ0).ne, fun φ hφ => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_lt_top hne hκ0).ne, lintegral_smul_measure, hInt φ hφ, smul_eq_mul]
  simp_rw [key _ φ hφ]
  have hc : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
      (κ * ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) =
      κ * (ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
        ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) := fun q => by ring
  simp_rw [hc]
  rw [lintegral_const_mul' _ _ hκt, ← mul_assoc, ← mul_assoc, ENNReal.div_mul_cancel hκ0 hκt]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstSandwich
section
namespace Formalism.L2.SG.Pf.BH

theorem sandwich' : Sandwich := by
  refine sandwich_of_chart Sw.lieG' Sw.lieWb' gauss_sum_unique phi_form' big_cell_g
    (phiDeriv_of Sw.w0Sq) Sw.lIso Sw.w0Sq ?_ ?_
  · unfold PI.SwSand.LieEN
    intros
    exact Formalism.MainNotions.BridgeCSB.lieE_N
  · intros
    apply Formalism.MainNotions.BridgeCSB.exp_mem_N

end Formalism.L2.SG.Pf.BH
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def coordSc (r : ℕ) (sc : ℝ) (q : (Fin r → ℂ) × ℂ) : Fin (r + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) (fun a : Fin r => (((sc : ℂ) ^ (r - a.1))⁻¹) ^ 2 * q.1 a) q.2

def psiP {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (u : Formalism.REAL.UJ ε) : Formalism.QuantumDeterminants.Mt k r :=
  fun i j => (P⁻¹ * uMat u * P) i j

def PFrame : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' →
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r ∧ IsUnit P.det ∧
      (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) ∧
      ∃ zH zH' : Fin (2 * r + k + 1) → ℂ, Formalism.QuantumDeterminants.inWb k r zH ∧ Formalism.QuantumDeterminants.inWb k r zH' ∧
        P *ᵥ zH = z ∧ P *ᵥ zH' = z' ∧ Formalism.QuantumDeterminants.Tz k r zH = T ∧ Formalism.QuantumDeterminants.Tz k r zH' = T'

def SetCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH →
    ∀ u : Formalism.REAL.UJ ε, u ∈ SLoc ε e z ↔ P⁻¹ * uMat u * P ∈ Formalism.QuantumDeterminants.Sset k r zH

def HaarCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH → 1 ≤ k →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ((Formalism.REAL.muG ε).map (psiP P)) ∧
    ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r zH) μW →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
      ∀ μS : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS →
        ∃ c : ℝ, 0 < c ∧ μS.map (psiP P) = ENNReal.ofReal c • Formalism.MainNotions.S.muS μW μN

def ZBig : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ)
    (z z' zH zH' : Fin (2 * r + k + 1) → ℂ) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (sc : ℝ),
    Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r → IsUnit P.det → (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) →
    Formalism.QuantumDeterminants.inWb k r zH → Formalism.QuantumDeterminants.inWb k r zH' → P *ᵥ zH = z → P *ᵥ zH' = z' → 0 < sc →
    ∀ μsec, Formalism.QuantumDeterminants.IsSection k r zH zH' μsec →
    ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) → Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq q.2 →
      Formalism.REAL.inUJ ε (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) ∧
      Zhat ε (famSc sc e z) (famSc sc e z') (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) =
        Matrix.diagonal (coordSc r sc q)

def BigMem : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

def CoordW : Prop :=
  ∀ (r k : ℕ) (T T' sc : ℝ), 1 ≤ k → 0 < T → 0 < T' → 0 < sc →
    ∃ κ : ℝ, 0 < κ ∧ ∀ F : (Fin (r + 1) → ℂ) → ℝ≥0∞,
      ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
        ENNReal.ofReal κ * ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))

def SecWb : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' → ∃ μsec, Formalism.QuantumDeterminants.IsSection k r z z' μsec

def JacExGoodN : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' sc : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

theorem jacExGood_of_N (H : JacExGoodN) : JacExGood := by
  intro n r k ε e z z' T T' sc hF hG hsc
  have hn : n = 2 * r + k + 1 := by have := hF.dim; omega
  subst hn
  exact H r k ε e z z' T T' sc hF hG hsc

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfM
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenericX

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem identResp_generic {r : ℕ} (abelian₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hL : ∀ x ∈ abelian₂, e x ∈ abelian₂) (hL' : ∀ x ∈ abelian₂, e.symm x ∈ abelian₂)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂)
    (hI : ∀ g, M.split = some g → IotaG H (algebraMap F E (g.q : F)) abelian₂ f₀ f₁ f₂ e) :
    H.Ident (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.Respects (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · ext w
    simp
  · intro x x₂ hx hx₂
    have : x = x₂ := Subtype.ext (hx.trans hx₂.symm)
    rw [this]
    rfl
  · ext w
    constructor
    · rintro ⟨_, ⟨x, hxΛ, rfl⟩, rfl⟩
      exact ⟨perpEquiv H e hiso _ _ h12 h21 x, hL _ hxΛ, rfl⟩
    · rintro ⟨x₂, hx₂Λ, rfl⟩
      refine ⟨H.mkW _ ⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩,
        ⟨⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩, hL' _ hx₂Λ, rfl⟩, ?_⟩
      show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x₂
      rw [qEquiv_mk]
      congr 1
      exact Subtype.ext (e.apply_symm_apply x₂)
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz
  · intro g hg
    obtain ⟨hA, hB⟩ := hI g hg
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨a0, b0⟩, ⟨x', x, hx'Λ, hxΛ, hq, heq⟩, hmap⟩
      obtain ⟨y, y'', hyΛ, hy''Λ, hyp, hy''p, hxy, hxy'', hyq⟩ := hA x x' hxΛ hx'Λ x.2 x'.2 hq
      refine ⟨⟨y'', hy''p⟩, ⟨y, hyp⟩, hy''Λ, hyΛ, hyq, ?_⟩
      simp only [Prod.map, Prod.mk.injEq] at hmap heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := hmap
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk x') = Submodule.Quotient.mk _
        rw [qEquiv_mk, mk_eq_iff]
        exact hxy''
      · show Submodule.Quotient.mk x = Submodule.Quotient.mk _
        rw [mk_eq_iff]
        exact hxy
    · rintro ⟨x'', x, hx''Λ, hxΛ, hq, heq⟩
      obtain ⟨y, y', hyΛ, hy'Λ, hyp, hy'p, hxy, hxy', hyq⟩ := hB x x'' hxΛ hx''Λ x.2 x''.2 hq
      refine ⟨(H.mkW _ ⟨y', hy'p⟩, H.mkW _ ⟨y, hyp⟩), ⟨⟨y', hy'p⟩, ⟨y, hyp⟩, hy'Λ, hyΛ, hyq, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x''
        rw [qEquiv_mk, mk_eq_iff]
        have h := h12 _ hxy'
        rw [map_sub, LinearEquiv.apply_symm_apply] at h
        have h' := Submodule.neg_mem _ h
        rwa [neg_sub] at h'
      · show Submodule.Quotient.mk _ = Submodule.Quotient.mk x
        rw [mk_eq_iff]
        have h' := Submodule.neg_mem _ hxy
        rwa [neg_sub] at h'

end GenericX

section ConcreteX

variable {D : D7} (Z : LocDat D) (p : PlF D)

def phiP (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hG : GFacts Λ f g1 g2 β) :
    (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g1 b)) ≃ₗ[(D.s.atP p).Ep]
      (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g2 b)) :=
  qEquiv (locH Z p) (betaP p β) (betaP_iso Z p β hG.iso) _ _
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy)

theorem identResp_lt (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Tn T'n : ℕ) (hG : GFacts Λ f g1 g2 β)
    (hI : IotaEl Z p Λ f g1 g2 β) :
    (locH Z p).Ident (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _) (phiP Z p Λ f g1 g2 β hG) ∧
      (locH Z p).Respects (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _)
        (phiP Z p Λ f g1 g2 β hG) := by
  have hiso : ∀ v w, (locH Z p).h (betaP p β v) (betaP p β w) = (locH Z p).h v w := betaP_iso Z p β hG.iso
  refine identResp_generic (locH Z p) (lattice₂ D Z.M p Λ) (fun a => sF Z p a • baseChange₂ D p (f a))
    (fun b => sF' Z p b • baseChange₂ D p (g1 b)) (fun b => sF' Z p b • baseChange₂ D p (g2 b)) _ _ (betaP p β) hiso
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy) ?_ ?_
    (fun x hx => betaP_lat Z p β Λ hG.lam hx) (fun x hx => betaP_symm_lat Z p β Λ hG.lam' hx)
    (fun w hw => scalar_frame_w_zero_exists Z p Λ f g1 g2 β hG hw) ?_ ?_ ?_ ?_ hI
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.fiso j i, map_zero, mul_zero]
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.g2iso j i, map_zero, mul_zero]
  ·
    rw [om'_loc, om'_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    rw [omp_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p f (sF Z p) (isUnit_sF Z p) hG.omp)
  ·
    rw [om_loc, om_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl, map_smul, betaP_bc]
    rw [om_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.om)
  ·
    rw [dl_loc Z p f g1 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g2 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    have h := congrArg (D.s.atP p).ιE hG.ratio
    rw [map_mul, map_mul] at h
    linear_combination ((∏ i : Fin D.R.rS, (Z.M p).L.cj (sF Z p (Fin.castLE (Nat.le_succ _) i))) *
      (∏ i : Fin D.R.rS, sF' Z p (Fin.castLE (Nat.le_succ _) i)) *
      ((∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (sF Z p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Z p (Fin.castLE le_rfl i)))) * h
  ·
    show betaP p β (sF' Z p (Fin.last _) • baseChange₂ D p (g1 (Fin.last _))) -
      sF' Z p (Fin.last _) • baseChange₂ D p (g2 (Fin.last _)) ∈ _
    rw [map_smul, betaP_bc, ← smul_sub, ← map_sub]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.zmap)

end ConcreteX

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

end Formalism.L2.SG.Pf
end
end

