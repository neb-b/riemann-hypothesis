module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqAmpJAndBesselEqDoubleIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNonzeroFixedOfSquareIntegrableBessel
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0360
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHilbertSchmidtNormSqBesselAmplitudeLe
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SchurNorm

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

theorem ampJ_of_smul {k r : ℕ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ)
    (c : ℝ) (t t' : ℂ) {Φ Ψ : Mat k r → Wp} {Φ' Ψ' : Mat k r → Wq} (h : ∀ g ∈ GG k r, Φ g = t • Ψ g)
    (h' : ∀ g ∈ GG k r, Φ' g = t' • Ψ' g) {γ : Mat k r} (hγ : γ ∈ GG k r) :
    ampJ μ c Φ Φ' γ = ((c : ℂ)⁻¹ * (t * star t')) • ampJ μ 1 Ψ Ψ' γ := by
  unfold ampJ
  rw [Complex.ofReal_one, inv_one, one_smul, mul_smul, ← integral_smul (t * star t')]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [show ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r from hμ.2.2.1] with x hx
  rw [h _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hγ hx), h' _ hx]
  ext η
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, smul_smul, Complex.star_def]
  congr 1
  ring

theorem exists_isEll_smul (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
    (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS νS : Measure (Mt k r))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (B : H → Wp) (hv : v₀ ≠ 0)
    (hS : StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d) (hz : SideIrr z π μS) (hq : IsQuotMeas μG μS νS)
    (hm : MultOne z (psiGen k r z c) σ π) (hB : IsBesselMapSm z (psiGen k r z c) σ π B) (hc : 0 < c₀)
    (h0 : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp))
    (h1 : ∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 =
      l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) :
    ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) l ∧
      ∃ t : ℂ, ‖t‖ ^ 2 = c₀ * Module.finrank ℂ Wp * d ∧
        ∀ g ∈ GG k r, B (σ g v₀) = t • l (σ g (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) := by
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hn : ((‖v₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv
  have hvw : v₀ = ((‖v₀‖ : ℝ) : ℂ) • w := by rw [hw, smul_smul, mul_inv_cancel₀ hn, one_smul]
  obtain ⟨hStd, hsm⟩ := hS
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hw1' : ‖w‖₊ = 1 := NNReal.eq hw1
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  obtain ⟨-, -, hle, hact, hinf⟩ := _root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hU
  have hgw : ∀ g ∈ GG k r, σ g w ∈ smoothVecs (k := k) (r := r) σ := (hact w hsm).1
  haveI : Nontrivial Wp := hz.2.2
  have hdim : (0 : ℝ) < Module.finrank ℂ Wp := by exact_mod_cast Module.finrank_pos
  have hn0 : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hv)
  have hnt : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hLw : l2SG νS (fun g => B (σ g w)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) := by
    rw [h1 w hsm, hw1']; simp
  have hnv : NonVan z (psiGen k r z c) σ π w μG νS := by
    refine _root_.GlobalTheory.BesselFixed.nonVan_of_bessel k r σ w a d μG μS νS z c π B ⟨hStd, hsm⟩ hz.1 hq hB ?_ ?_ ?_
    · intro h
      rw [h, zero_mul, h0] at hLw
      exact (ENNReal.ofReal_pos.2 (mul_pos hc hdim)).ne hLw
    · intro h
      rw [h, ENNReal.top_mul hn0, h0] at hLw
      exact ENNReal.ofReal_ne_top hLw.symm
    · intro v hv'
      refine (ENNReal.mul_left_inj hn0 hnt).1 ?_
      rw [h1 v hv', ← hLw]; ring
  obtain ⟨l, hl⟩ := _root_.GlobalTheory.SgInf.exists_isEll_DD k r σ w a μG d z c π μS hStd hz.1 hsm hm νS hq hnv
  refine ⟨l, hl, ?_⟩
  have hs : ∃ s : ℂ, ∀ x ∈ smoothVecs (k := k) (r := r) σ, B x = s • l x := by
    obtain ⟨s, hs | hs⟩ := hm B l hB hl.1
    · exact ⟨s, hs⟩
    · obtain ⟨u, hu, hu0⟩ := hl.2.1
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hu0 ((hs u ((hinf hsm).1 u (hle hu))).trans (zero_smul _ _))
      exact ⟨s⁻¹, fun x hx => by rw [hs x hx, smul_smul, inv_mul_cancel₀ hs0, one_smul]⟩
  obtain ⟨s, hs⟩ := hs
  have key : ∀ g ∈ GG k r, B (σ g v₀) = (((‖v₀‖ : ℝ) : ℂ) * s) • l (σ g w) := by
    intro g hg
    have e : σ g v₀ = ((‖v₀‖ : ℝ) : ℂ) • σ g w := by rw [← map_smul, ← hvw]
    rw [e, hB.2.1 _ _ (hgw g hg), hs _ (hgw g hg), smul_smul]
  refine ⟨_, ?_, key⟩
  generalize ((‖v₀‖ : ℝ) : ℂ) * s = t at key
  have hone : (1 : Mat k r) ∈ GG k r := by simp [UH]
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hU.1.1] at this
  have hlw := (_root_.GlobalTheory.SgInf.ProjLine.projector_line k r σ w a μG d z c π μS hStd hz.1 νS hq l hl).1 w hwD
  have hμS : IsHaarOn (Sset k r z) μS := hz.1.2.2.2.1
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hμS.2.1 (measure_mono_null (by
    rintro x hx ⟨h, hh, m, hm', e⟩
    exact hx (e ▸ Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hm'.1)) hμS.2.2.1) hq
  have e : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (‖t‖ ^ 2) * l2SG νS (fun x => l (σ x w)) := by
    unfold l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [key _ hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  rw [h0, hlw, hw1, ← ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e
  rw [e]; field_simp

theorem lintegral_hsNormSq_ampJ_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS μS' νS νS' ν : Measure (Mt k r)) (z z' : (Fin (2 * r + k + 1) → ℂ)) (c c' : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (B : H → Wp) (B' : H → Wq), v₀ ≠ 0 → StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d → SideIrr z π μS → SideIrr z' π' μS' → IsQuotMeas μG μS νS → IsQuotMeas μG μS' νS' → MultOne z (psiGen k r z c) σ π → MultOne z' (psiGen k r z' c') σ π' → IsBesselMapSm z (psiGen k r z c) σ π B → IsBesselMapSm z' (psiGen k r z' c') σ π' B' → 0 < c₀ → l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp) → l2SG νS' (fun g => B' (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wq) → (∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → (∀ v ∈ smoothVecs σ, l2SG νS' (fun g => B' (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS' (fun g => B' (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → IsDis (Greg k r z z') μG μS μS' ν → ∫⁻ γ, ENNReal.ofReal (hsNormSq (ampJ μG c₀ (fun g => B (σ g v₀)) (fun g => B' (σ g v₀)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal ((Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq / d) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ v₀ a d c₀ μG μS μS' νS νS' ν z z' c c' π π' B B' hv hS hz hz' hq hq'
    hm hm' hB hB' hc h0 h0' h1 h1' hν
  obtain ⟨l, hl, t, ht, key⟩ := exists_isEll_smul k r σ v₀ a d c₀ μG μS νS z c π B hv hS hz hq hm hB hc h0 h1
  obtain ⟨l', hl', t', ht', key'⟩ :=
    exists_isEll_smul k r σ v₀ a d c₀ μG μS' νS' z' c' π' B' hv hS hz' hq' hm' hB' hc h0' h1'
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hG : IsHaarOn (GG k r) μG := hS.1.2.2.2.2.1
  have hd : 0 < d := hS.1.2.2.2.2.2.1.1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h5 := _root_.GlobalTheory.SgInf.EllBound.lintegral_hsNormSq_ell_le k r σ w a μG d z c π μS z' c' π' μS' hS.1 hz.1 hz'.1 ν hν l l' hl hl'
  have hJ := (_root_.GlobalTheory.SgInf.AmpJ.oo_eq_ampJ_and_besselJ_eq_Iint k r (H := H) (Wp := Wp) (Wq := Wq)).1 μG (fun x => l (σ x w)) (fun x => l' (σ x w)) hG
  have hD : (0 : ℝ) ≤ (Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq := by positivity
  rw [div_eq_mul_inv, ENNReal.ofReal_mul hD]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right h5 _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [show ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' from hν.2.1] with γ hγ
  rw [ampJ_of_smul hG c₀ t t' (Ψ := fun x => l (σ x w)) (Ψ' := fun x => l' (σ x w)) key key' hγ.1,
    ← hJ _ hγ.1, ← ENNReal.ofReal_mul hD, hsNormSq_smul, hsNormSq_smul]
  congr 1
  rw [norm_mul, norm_mul, norm_star, norm_inv, mul_pow, mul_pow, ht, ht', Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd.le]
  field_simp

end GlobalTheory.Amp.SchurNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.MassAtRecord

theorem massRatio_at_record : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := fun D => by
  letI := D.host.cmStar
  exact fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
    _root_.GlobalTheory.Mass.siegelMassRatio_holds D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

end GlobalTheory.MassAtRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCell
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section
namespace GlobalTheory.BigConv

theorem good_point (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (hk : 1 ≤ k) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k ∧
      0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) := by
  obtain ⟨μs, -, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r L.z L.z' hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  set τ := Formalism.QuantumDeterminants.Tz k r L.z * Formalism.QuantumDeterminants.Tz k r L.z' with hτ
  have hτ0 : 0 < τ := mul_pos L.hz.2 L.hz'.2
  set ζ : ℂ := ((τ + 1 : ℝ) : ℂ) with hζ
  have hn : τ < Complex.normSq ζ := by
    rw [hζ, Complex.normSq_ofReal]; nlinarith
  obtain ⟨hU, hzz⟩ := hμ ζ hn
  refine ⟨μs ζ, hU, ?_⟩
  have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c (μs ζ) L.hz.1 L.hz'.1
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ L.hz.1 L.hz'.1, hzz] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) ⟨r, by omega⟩ with hP
  have hP0 : P ≠ 0 := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
    rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1)) = ζ * P := by
    unfold Formalism.QuantumDeterminants.zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul]
  have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
  nlinarith


open Formalism.FourierDecayAlt in
theorem conv_good (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hgap : GlobalTheory.CellAmp.GapCell k r h) (hκ : L.κN ≠ ⊤) (c : Fin r → ℂ)
    (μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hc : ∀ a, c a ≠ 0) (hμ₁ : μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k)
    (hG : 0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) :
    ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧
      MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ₁) b) (Formalism.MainNotions.S.pairMeas L) := by
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hinv : (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ₁ = 1 := Matrix.nonsing_inv_mul _ hu
  have hZ := Formalism.QuantumDeterminants.bigCellZhat k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
  set ζ := Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bigCell k r c μ₁ *ᵥ L.z') L.z with hζ
  have hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) := by
    have hζ0 : ζ ≠ 0 := by
      intro h0
      have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
      have hz := hmin.2.2 hc
      set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) ⟨r, by omega⟩ with hP
      have hr := hmin.1 (Fin.last r)
      have hP0 : P ≠ 0 := by
        have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
        rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
      unfold Formalism.QuantumDeterminants.zeta at hz
      rw [← hP, ← hζ, h0, div_eq_zero_iff] at hz
      have hD : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) (Fin.last (r + 1)) = 0 :=
        hz.resolve_right hP0
      unfold Formalism.QuantumDeterminants.Gf at hG
      rw [hD, ← hP] at hG
      have : 0 ≤ Complex.normSq P := Complex.normSq_nonneg _
      have := mul_pos L.hz.2 L.hz'.2
      simp at hG
      nlinarith
    refine ⟨1, fun a => if h : a.val < r then c ⟨a.val, h⟩ else ζ, fun a => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact hc _
      · exact hζ0
    · refine hZ.trans ?_
      ext i j
      rw [Matrix.diagonal_apply]
      show _ = if i = j then _ else _
      by_cases h : i = j
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h]
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ₁ hc hg
  have hcd := GlobalTheory.CellAmp.Model.cellData_open L 0 _ hg hinv hG hmono hR
  exact GlobalTheory.CellMaj.cellConv k r L h 0 _ _ _ _ hκ hok hgap hcd hmono

theorem bigConv : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L h hok hgap hκ hκ0 hcL c μ hc hμ
  obtain ⟨μ₁, hμ₁, hG⟩ := good_point k r L hok.1 c hc
  obtain ⟨b, hb0, hb1, hint⟩ := conv_good k r L h hok hgap hκ c μ₁ hc hμ₁ hG
  have hg₁ := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ hc hμ
  have hu₁ := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg₁
  set a := (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ with ha
  have haU : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg₁) hg
  have hN := _root_.GlobalTheory.BigConvLevi.levi_conj_mem_iff k r c μ₁ μ hc hμ₁ hμ
  obtain ⟨C, hC, hmap⟩ := _root_.GlobalTheory.NConjHaar.map_conj_eq_smul k r L hκ0 hκ a haU hN
  refine ⟨b, hb0, hb1, ?_⟩
  have e : Formalism.QuantumDeterminants.bigCell k r c μ₁ * a = Formalism.QuantumDeterminants.bigCell k r c μ := by
    rw [ha, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁]
  rw [← e]
  exact _root_.GlobalTheory.CellMajTransfer.integrable_mul_right k r L _ a b C hκ0 hκ hb0 hg₁ haU hC hmap hint

end GlobalTheory.BigConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.PoincareInHH.Cut
open Matrix

variable {D : D7} (X : HidaSetting D)

theorem crd_injective' {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  rw [← toV_crd X y, ← toV_crd X y', h]

theorem eq_matEC {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {M : GL (Fin X.B.I.n) X.B.I.E}
    (h3 : ∀ y, X.crd (n y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) : n = matEC X M := by
  ext y
  exact crd_injective' X (by rw [h3, matE_crdC])

theorem nrat_iff (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n) :
    n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u := by
  constructor
  · intro hn
    have hgtop : Formalism.HermitianLatticesTheory.gmap n (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
      unfold Formalism.HermitianLatticesTheory.gmap; rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 n.surjective
    exact nLamNinf_holds D X u ⊤ x n hx ⟨⟨hn.1, hgtop⟩, hn.2.1, hn.2.2⟩
  · intro hν1
    obtain ⟨M, hM, hinf, -, h3⟩ := hx
    have hn := eq_matEC X h3
    subst hn
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have hGv : ∀ y, uMat (x.1 v) *ᵥ Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v y = Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
      intro y
      rw [Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.Pf.Vanish2.rvHom_apply, hinf v]
      exact rv_mulVec X v _ y
    have hsub : ∀ y, (uMat (x.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y) :=
      fun y => tr_sub (Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v) _ _ hGv y
    have hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y := by
      intro y
      rw [crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)),
        ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) →
        matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T) := by
      intro y T hy
      rw [← hcrdn] at hy
      have := toV_span X hy
      rwa [toV_crd] at this
    have hInN := hν1 v
    refine ⟨matE_isomC X M hM, ?_, ?_⟩
    · intro j x hx
      change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
      change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
      rw [X.Fu_e] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        have h1 := hInN.1.1 a
        rw [hsub] at h1
        have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈
            Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1})) := by
          rw [Set.image_image]; exact h1
        have h3 := rv_desc X v _ _ h2
        have h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈
            Submodule.span X.B.I.E (X.eR '' {b | b.1 < j}) := by
          refine Submodule.span_mono (Set.image_mono fun b hb => ?_) h3
          have : a.1 < j + 1 := ha
          show b.1 < j
          have : b.1 < a.1 := hb
          omega
        exact hback _ _ h4
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add (f := _), add_sub_add_comm]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ ha
    · intro x hx
      change x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx
      change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e] at hx ⊢
      have hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0 := by
        intro a
        rw [hJ_rv]
        have h0 : hE X (X.eR a) (X.crd x) = 0 := by
          apply X.ιE.injective
          rw [iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]
          exact (mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
        rw [h0, map_zero]
      have h1 := hInN.2 _ hzero
      rw [hsub] at h1
      have huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
      have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈
          Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS})) := by
        rw [Set.image_image]; exact h1
      have h3 := hback x _ (rv_desc X v _ _ h2)
      rwa [huniv, Set.image_univ] at h3

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.NonRelPf

variable {D : D7} (X : HidaSetting D)

theorem sgUp_eq {E : Type} [Field E] [NumberField E] {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Formalism.L2.SG.PairVal.sgUp A = ∑ a : Fin r, A a.castSucc a.succ := by
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (by omega)]
  rfl

theorem root_entry (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) (a : Fin D.R.rS) :
    (VS D).hT (X.fY a) (n (nxt X.eX (X.zu u) a)) = A a.castSucc a.succ := by
  have e : nxt X.eX (X.zu u) a = frame (lf D (X.Fu u)) a.succ := by
    show _ = (X.Fu u).fvec a.succ
    rw [fvec_succ, X.Fu_e, X.flagZVector]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, hA, map_sum, Fin.sum_univ_castSucc]
  have h1 : ∀ b : Fin D.R.rS, frame (lf D (X.Fu u)) b.castSucc = X.eX b := by
    intro b
    show (X.Fu u).fvec b.castSucc = _
    simp only [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
  have h2 : frame (lf D (X.Fu u)) (Fin.last D.R.rS) = X.zu u := by
    show (X.Fu u).fvec (Fin.last _) = _
    simp only [FlagG.fvec, Fin.snoc_last, X.flagZVector]
  simp only [map_smul, smul_eq_mul, h1, h2, hTfe, (X.zu_orth u a).2, mul_zero, add_zero, mul_ite, mul_one]
  rw [Finset.sum_ite_eq']
  simp

theorem psi_eq (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A) := by
  rw [psi_rat X u hx]
  simp only [root_entry X u n A hA]
  have hs : ∀ v, (∑ a : Fin D.R.rS, (Φ X v (A a.castSucc a.succ) + star (Φ X v (A a.castSucc a.succ)))) =
      X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A)) +
        star (X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A))) := by
    intro v
    rw [Finset.sum_add_distrib, ← star_sum, ← Φ_sum, ← sgUp_eq]
    rfl
  simp only [hs]
  rw [Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm _), RingEquiv.apply_symm_apply, X.g_eq]
  rfl

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

theorem ratLink_points : ∀ (D : D7) (X : HidaSetting D), (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃! x : X.B.I.GA, RatLink X x γ) ∧ (∀ x y γ δ, RatLink X x γ → RatLink X y δ → RatLink X (x * y) (γ * δ) ∧ RatLink X x⁻¹ γ⁻¹ ∧ (x.1 = y.1 → γ = δ)) ∧ ∀ (u : D.what₂.Word) x n, RatLink X x n → (n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u) ∧ (n ∈ NRat (lf D (X.Fu u)) → ∀ A : Formalism.L2.SG.PairVal.MatR D, (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) → X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A)) := by
  intro D X
  refine ⟨fun γ hγ => ?_, fun x y γ δ hx hy => ?_, fun u x n hx => ?_⟩
  · obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X γ hγ
    exact ⟨x, hx, fun y hy => Formalism.L2.SG.TermOp.Vanish.ratLink_unique X hy hx⟩
  · exact ⟨Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hx hy, Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx,
      Formalism.L2.SG.Pf.IdMeet.lin_eq_of_fst X hx hy⟩
  · exact ⟨nrat_iff X u hx, fun _ A hA => psi_eq X u hx A hA⟩

end GlobalTheory.RatIsomPoint
end
end

