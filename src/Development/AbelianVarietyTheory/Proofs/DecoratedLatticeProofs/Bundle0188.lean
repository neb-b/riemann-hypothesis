module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetDisint

theorem integral_eq_of_lintegral_eq {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (m : Measure Y)
    (f : X → ℂ) (g : Y → ℂ) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ c : ℂ → ENNReal, Measurable c → ∫⁻ x, c (f x) ∂μ = ∫⁻ y, c (g y) ∂m) (hi : Integrable f μ) :
    Integrable g m ∧ ∫ x, f x ∂μ = ∫ y, g y ∂m := by
  have e : μ.map f = m.map g := by
    ext S hS
    rw [Measure.map_apply hf hS, Measure.map_apply hg hS]
    have h1 := h (S.indicator 1) (measurable_one.indicator hS)
    have e1 : ∀ x, S.indicator (1 : ℂ → ENNReal) (f x) = (f ⁻¹' S).indicator 1 x := fun x => by
      by_cases hx : f x ∈ S <;> simp [Set.indicator, hx]
    have e2 : ∀ y, S.indicator (1 : ℂ → ENNReal) (g y) = (g ⁻¹' S).indicator 1 y := fun y => by
      by_cases hy : g y ∈ S <;> simp [Set.indicator, hy]
    simp only [e1, e2] at h1
    rwa [lintegral_indicator_one (hf hS), lintegral_indicator_one (hg hS)] at h1
  refine ⟨?_, ?_⟩
  · have h1 : Integrable (fun z : ℂ => z) (μ.map f) :=
      (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).2 hi
    rw [e] at h1
    exact (integrable_map_measure aestronglyMeasurable_id hg.aemeasurable).1 h1
  · have a1 := integral_map (μ := μ) hf.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    have a2 := integral_map (μ := m) hg.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    rw [← a1, ← a2, e]

variable {D : D7}

theorem continuous_realPt {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} (hW : W.SigOK) {Fr : Frames W}
    (hFr : IsFrames W Fr) : Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  obtain ⟨h1, h2, h3⟩ := Formalism.IndefR.Eqv.G5.af_facts D.host.F
  obtain ⟨h1, -, -, -, -⟩ := Formalism.IndefR.Eqv.G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig W.gram
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hm : Continuous fun b : (∀ ρ, Upq W ρ) => UpqT.mat (b ρ) :=
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply ρ)
  refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous
    (continuous_const.matrix_mul ((continuous_const.matrix_mul hm).matrix_mul continuous_const)) fun b => ?_
  refine conjFrame_mem_UH _ _ _ (sig_sum W hW (tauE D ρ)) _ _ (hFr ρ) ?_ (b ρ)
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND W).2).isUnit

theorem finE_toFin (W : HSp D) (h : GA D W) : finE W h = finE W (GlobalTheory.AutMult.toFin W h : GA D W) := by
  conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin h]
  rw [map_mul]
  have : finE W (GlobalTheory.AutMult.toInf W h : GA D W) = 1 := by
    show Formalism.UG.bc (swapAE D) (finHom W _) = 1
    rw [MonoidHom.mem_ker.1 (GlobalTheory.AutMult.toInf W h).2, map_one]
  rw [this, one_mul]

end GlobalTheory.CosetDisint

end

namespace GlobalTheory.CosetDisint

theorem integral_eq_cosetSum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → IsOpen {h : GA D W | finE W h ∈ K} → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ℂ, Continuous Z → Integrable Z ν → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ))‖ₑ ∂(Measure.pi mR) < ⊤ ∧ ∫ g, Z g ∂ν = ∫ b, ∑' x : FinCos W (levA W K), Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν hO Fr hFr mR hmR Z hZc hZi hZinv
  obtain ⟨h1, h2, h3⟩ := Formalism.IndefR.Eqv.G5.af_facts D.host.F
  obtain ⟨i0, -, -, i3, i4⟩ := Formalism.IndefR.Eqv.G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig W.gram
  haveI := i0; haveI := i3; haveI := i4
  haveI : ν.IsHaarMeasure := hν.1
  haveI : SecondCountableTopology (GfC W) := Topology.IsInducing.subtypeVal.secondCountableTopology
  set O : Set (GA D W) := {h | finE W h ∈ K} with hOdef
  have hOm : MeasurableSet O := hO.measurableSet
  set φ : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hφdef
  have hφ : Continuous φ := continuous_realPt hθ hW hFr
  have hZm : Measurable Z := hZc.measurable
  set L' := (levA W K).subgroupOf (GfC W) with hL'
  have hmemL : ∀ y : GfC W, y ∈ L' ↔ finE W (y : GA D W) ∈ K := fun y => by
    rw [hL', Subgroup.mem_subgroupOf, mem_levA]
    exact and_iff_right y.2
  have hL'o : IsOpen (L' : Set (GfC W)) := by
    have : (L' : Set (GfC W)) = Subtype.val ⁻¹' O := Set.ext fun y => hmemL y
    rw [this]; exact hO.preimage continuous_subtype_val

  haveI : Countable (GfC W ⧸ L') := by
    have hpd : (Set.univ : Set (GfC W ⧸ L')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (L' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hL'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [L'.one_mem]⟩))

  let s : GfC W ⧸ L' → Set (GA D W) := fun q => (fun g => (FinCos.rep q)⁻¹ * g) ⁻¹' O
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (GlobalTheory.AutMult.toFin W g) := by
    intro q g
    show finE W ((FinCos.rep q)⁻¹ * g) ∈ K ↔ _
    rw [finE_toFin, map_mul, map_inv, FinCos.rep, GlobalTheory.AutMult.toFin_coe, ← hmemL]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hOm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  have key : ∀ q : GfC W ⧸ L', ∀ G : GA D W → ENNReal, Measurable G → (∀ g, ∀ k ∈ levA W K, G (g * k) = G g) →
      ∫⁻ g in s q, G g ∂ν = ∫⁻ b, G (FinCos.rep q * φ b) ∂(Measure.pi mR) := by
    intro q G hG hGi
    have hpre : (fun h => FinCos.rep q * h) ⁻¹' s q = O := by
      ext h; simp [s]
    rw [← (measurePreserving_mul_left ν (FinCos.rep q)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft _) G (s q), hpre]
    exact _root_.GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi D θ hθ W hW K ν hν Fr hFr mR hmR (fun h => G (FinCos.rep q * h)) (hG.comp (measurable_const_mul _))
      (fun g k hk => by simp only [← mul_assoc]; exact hGi _ k hk) hOm
  have hcm : ∀ q : GfC W ⧸ L', Continuous fun b => Z (FinCos.rep q * φ b) := fun q =>
    hZc.comp (continuous_const.mul hφ)

  have hlin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) = ∫⁻ g, ‖Z g‖ₑ ∂ν := by
    rw [lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]
    rw [← Measure.restrict_univ (μ := ν), ← hU, lintegral_iUnion hsm hd]
    refine tsum_congr fun q => (key q (fun g => ‖Z g‖ₑ) hZm.enorm fun g k hk => by rw [hZinv g k hk]).symm
  have hfin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) < ⊤ := by
    rw [hlin]; exact hZi.2
  refine ⟨hfin, ?_⟩

  have hint : ∀ q : GfC W ⧸ L', ∫ g in s q, Z g ∂ν = ∫ b, Z (FinCos.rep q * φ b) ∂(Measure.pi mR) := fun q =>
    (integral_eq_of_lintegral_eq (ν.restrict (s q)) (Measure.pi mR) Z _ hZm (hcm q).measurable
      (fun c hc => key q (fun g => c (Z g)) (hc.comp hZm) fun g k hk => by simp only [hZinv g k hk])
      hZi.integrableOn).2
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hZi.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  rw [← hsum.tsum_eq, integral_tsum (fun q => (hcm q).aestronglyMeasurable)
    (by rw [← lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]; exact hfin.ne)]
  exact tsum_congr hint

end GlobalTheory.CosetDisint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvolutionOrthDecBlockSumRealMat
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox


open Matrix ComplexOrder in
theorem isCartanInv_blockSum {k k₁ k₂ : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (GW : Matrix (Fin k₁) (Fin k₁) ℂ)
    (GH : Matrix (Fin k₂) (Fin k₂) ℂ) (iW : Matrix (Fin k) (Fin k₁) ℂ) (iH : Matrix (Fin k) (Fin k₂) ℂ)
    (pW : Matrix (Fin k₁) (Fin k) ℂ) (pH : Matrix (Fin k₂) (Fin k) ℂ) (sW : Matrix (Fin k₁) (Fin k₁) ℂ)
    (sH : Matrix (Fin k₂) (Fin k₂) ℂ) (hGh : Gᴴ = G) (hWW : iWᴴ * G * iW = GW) (hHH : iHᴴ * G * iH = GH)
    (hHW : iHᴴ * G * iW = 0) (h1 : pW * iW = 1) (h2 : pW * iH = 0) (h3 : pH * iH = 1) (h4 : pH * iW = 0)
    (hsum : iW * pW + iH * pH = 1) (hW : IsCartanInv GW sW) (hH : IsCartanInv GH sH) :
    IsCartanInv G (iW * sW * pW + iH * sH * pH) := by
  have hWH : iWᴴ * G * iH = 0 := by
    have := congrArg Matrix.conjTranspose hHW
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have c1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pW * (iW * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have c2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pW * (iH * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have c3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pH * (iH * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  have c4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pH * (iW * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  have g1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (G * (iW * X)) = GW * X := fun X => by
    simp only [← Matrix.mul_assoc, hWW]
  have g2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (G * (iH * X)) = 0 := fun X => by
    simp only [← Matrix.mul_assoc, hWH, Matrix.zero_mul]
  have g3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (G * (iH * X)) = GH * X := fun X => by
    simp only [← Matrix.mul_assoc, hHH]
  have g4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (G * (iW * X)) = 0 := fun X => by
    simp only [← Matrix.mul_assoc, hHW, Matrix.zero_mul]

  have hG : G = pWᴴ * GW * pW + pHᴴ * GH * pH := by
    calc G = (iW * pW + iH * pH)ᴴ * G * (iW * pW + iH * pH) := by
            rw [hsum, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by
        simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, g1, g2,
          g3, g4, Matrix.mul_zero, add_zero, zero_add]
  have hGs : G * (iW * sW * pW + iH * sH * pH) = pWᴴ * (GW * sW) * pW + pHᴴ * (GH * sH) * pH := by
    rw [hG]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, Matrix.mul_zero, add_zero, zero_add]
  have d1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (pWᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one, Matrix.one_mul]
  have d2 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (pWᴴ * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h2, conjTranspose_zero, Matrix.zero_mul]
  have d3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (pHᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h3, conjTranspose_one, Matrix.one_mul]
  have d4 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (pHᴴ * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h4, conjTranspose_zero, Matrix.zero_mul]
  have e1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sWᴴ * (GW * (sW * X)) = GW * X := fun X => by
    simp only [← Matrix.mul_assoc, hW.2.1]
  have e2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sHᴴ * (GH * (sH * X)) = GH * X := fun X => by
    simp only [← Matrix.mul_assoc, hH.2.1]
  have f1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sW * (sW * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hW.1, Matrix.one_mul]
  have f2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sH * (sH * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hH.1, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, f1, f2, Matrix.mul_zero, add_zero,
      zero_add]
    simpa only [Matrix.mul_assoc] using hsum
  · rw [Matrix.mul_assoc, hGs]
    conv_rhs => rw [hG]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d1, d2, d3, d4,
      e1, e2, Matrix.mul_zero, add_zero, zero_add]
  · rw [hGs]
    have hPW := hW.2.2
    have hPH := hH.2.2
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      ((hPW.posSemidef.conjTranspose_mul_mul_same pW).add (hPH.posSemidef.conjTranspose_mul_mul_same pH)).1
      fun x hx => ?_
    have key : ∀ {n} (P : Matrix (Fin n) (Fin k) ℂ) (M : Matrix (Fin n) (Fin n) ℂ),
        star x ⬝ᵥ ((Pᴴ * M * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x)) := fun P M => by
      simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
    rw [Matrix.add_mulVec, dotProduct_add, key, key]
    have hx' : iW *ᵥ (pW *ᵥ x) + iH *ᵥ (pH *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
    by_cases hw : pW *ᵥ x = 0
    · have hh : pH *ᵥ x ≠ 0 := fun hh => hx (by rw [← hx', hw, hh, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero])
      rw [hw]
      simpa using hPH.dotProduct_mulVec_pos hh
    · exact add_pos_of_pos_of_nonneg (hPW.dotProduct_mulVec_pos hw)
        (hPH.posSemidef.dotProduct_mulVec_nonneg _)


open Matrix in
theorem isCartanInv_sumMat : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H), (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∀ τ, IsCartanInv (gramAt D B τ) (sumMat o sW sH τ) := by
  intro D B W H o sW sH hW hH τ
  have hc : Function.Semiconj (tauE D τ) star star := fun x => GlobalTheory.FockCompare.tauE_star τ x
  have mm : ∀ {a b d : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) (N : Matrix (Fin b) (Fin d) D.host.E),
      (M * N).map (tauE D τ) = M.map (tauE D τ) * N.map (tauE D τ) := fun M N => Matrix.map_mul
  have ct : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), Mᴴ.map (tauE D τ) = (M.map (tauE D τ))ᴴ :=
    fun M => Matrix.conjTranspose_map _ hc
  have m1 : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) D.host.E).map (tauE D τ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have m0 : ∀ {a b : ℕ}, (0 : Matrix (Fin a) (Fin b) D.host.E).map (tauE D τ) = 0 := Matrix.map_zero _ (map_zero _)
  rw [sumMat_apply]
  refine isCartanInv_blockSum (gramAt D B τ) (gramAt D W τ) (gramAt D H τ) (o.iA.map (tauE D τ))
    (o.iB.map (tauE D τ)) (o.qA.map (tauE D τ)) (o.qB.map (tauE D τ)) (sW τ) (sH τ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hW τ) (hH τ)
  · show ((HSpace.gram B).map (tauE D τ))ᴴ = (HSpace.gram B).map (tauE D τ)
    rw [← ct, gram_conjTranspose]
  · show (o.iA.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = (HSpace.gram W).map (tauE D τ)
    rw [← ct, ← mm, ← mm, o.isoA]
  · show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iB.map (tauE D τ) = (HSpace.gram H).map (tauE D τ)
    rw [← ct, ← mm, ← mm, o.isoB]
  · show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = 0
    rw [← ct, ← mm, ← mm, o.orth, m0]
  · rw [← mm, o.qA_iA, m1]
  · rw [← mm, o.qA_iB, m0]
  · rw [← mm, o.qB_iB, m1]
  · rw [← mm, o.qB_iA, m0]
  · rw [← mm, ← mm, ← Matrix.map_add _ (map_add _), o.iA_qA_add, m1]

end GlobalTheory.Core.Rk.SumBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open GlobalTheory.OrientedHeis GlobalTheory.Core.Rk.FockBox

noncomputable section

namespace GlobalTheory.Core.Rk.FockBoxT

theorem killed_of_leibniz₂ {P₁ P₂ Q U₁ U₂ V : Type} [Zero U₁] [Zero U₂] [AddCommGroup V] (a₁ : P₁ → U₁ → U₁)
    (a₂ : P₂ → U₂ → U₂) (b : Q → V → V) (T₁ : U₁ → Prop) (T₂ : U₂ → Prop)
    (TV : V → Prop) (δ : U₁ → U₂ → V) (c₁ : Q → P₁) (c₂ : Q → P₂) (ha₁ : ∀ p f, T₁ f → T₁ (a₁ p f))
    (ha₂ : ∀ p f, T₂ f → T₂ (a₂ p f)) (hb : ∀ q f, TV f → TV (b q f))
    (hadd : ∀ q f g, TV f → TV g → b q (f + g) = b q f + b q g) (hb0 : ∀ q, b q 0 = 0)
    (hδ : ∀ f g, T₁ f → T₂ g → TV (δ f g)) (h1 : ∀ g, δ 0 g = 0) (h2 : ∀ f, δ f 0 = 0)
    (hL : ∀ q f g, T₁ f → T₂ g → b q (δ f g) = δ (a₁ (c₁ q) f) g + δ f (a₂ (c₂ q) g)) (N : ℕ) :
    ∀ (N₁ N₂ : ℕ) (f : U₁) (g : U₂), N₁ + N₂ ≤ N → T₁ f → T₂ g →
      (∀ l : List P₁, l.length = N₁ → l.foldr a₁ f = 0) → (∀ l : List P₂, l.length = N₂ → l.foldr a₂ g = 0) →
      ∀ l : List Q, l.length = N → l.foldr b (δ f g) = 0 := by
  have w0 : ∀ l : List Q, l.foldr b 0 = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hb0]
  have wT : ∀ (l : List Q) f, TV f → TV (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, TV f → TV g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have step : ∀ {P U : Type} [Zero U] (a : P → U → U) (M : ℕ) (f : U) (p : P),
      (∀ l : List P, l.length = M + 1 → l.foldr a f = 0) →
      ∀ l : List P, l.length = M → l.foldr a (a p f) = 0 := fun a M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.foldr_append] at this
  induction N with
  | zero =>
    intro N₁ N₂ f g hN _ _ k₁ _ l _
    have : f = 0 := k₁ [] (by simp; omega)
    rw [this, h1, w0]
  | succ N ih =>
    intro N₁ N₂ f g hN hf hg k₁ k₂ l hl
    rcases N₁ with _ | M₁
    · have : f = 0 := k₁ [] rfl
      rw [this, h1, w0]
    rcases N₂ with _ | M₂
    · have : g = 0 := k₂ [] rfl
      rw [this, h2, w0]
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, hL q f g hf hg,
      wadd _ _ _ (hδ _ _ (ha₁ _ _ hf) hg) (hδ _ _ hf (ha₂ _ _ hg)),
      ih M₁ (M₂ + 1) _ _ (by omega) (ha₁ _ _ hf) hg (step _ _ _ _ k₁) k₂ l' hl',
      ih (M₁ + 1) M₂ _ _ (by omega) hf (ha₂ _ _ hg) k₁ (step _ _ _ _ k₂) l' hl', add_zero]

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}

theorem lineAt_mul_left (hθ : IsInfFam θ) {k m n : ℕ} (p : Mx D k m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) t = (HMul.hMul p (lineAt θ τ z t) : Mx D k n) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k n :=
    { toFun := fun t => HMul.hMul p (lineAt θ τ z t)
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero]
      map_add' := fun s t => by rw [AddMonoidHom.map_add (f := _), Matrix.mul_add] }
  have hL' : IsLineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) L := by
    refine ⟨continuous_const.matrix_mul hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul p (lineAt θ τ z t) : Mx D k n).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1, Matrix.mul_zero]
    · show Formalism.IndefR.Datum.compAt θ τ' (HMul.hMul p (lineAt θ τ z t) : Mx D k n) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul]
      · rw [Matrix.mul_zero]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

variable {A B W H : HSp D} (o : OrthDec B W H)

theorem compAt_pA (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem compAt_pB (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pB = o.qB.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem dRho_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    Formalism.IndefR.Datum.dRho (heisO ψ A B) θ τ z (o.boxT A f g) =
      o.boxT A (Formalism.IndefR.Datum.dRho (heisO ψ A W) θ τ (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (Formalism.IndefR.Datum.dRho (heisO ψ A H) θ τ (o.qB.map (tauE D τ) * z) g) := by
  funext x
  have d := (hasDerivAt_dRho hθ hψ τ (o.qA.map (tauE D τ) * z) hf (o.resT A x).1).mul
    (hasDerivAt_dRho hθ hψ τ (o.qB.map (tauE D τ) * z) hg (o.resT A x).2)
  simp only [map_zero, heisO_zero] at d
  refine Eq.trans ?_ d.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [o.heisO_boxT, Pi.mul_apply, ← compAt_pA o hθ, ← compAt_pB o hθ, lineAt_mul_left hθ, lineAt_mul_left hθ]
  rfl

theorem qA_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qA.map (tauE D τ) * sumMat o sW sH τ = sW τ * o.qA.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qA_iA, o.qA_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem qB_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qB.map (tauE D τ) * sumMat o sW sH τ = sH τ * o.qB.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA, o.qB_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem mul_cplxO {k m n : ℕ} {q : Matrix (Fin k) (Fin m) ℂ} {s : Matrix (Fin m) (Fin m) ℂ}
    {s' : Matrix (Fin k) (Fin k) ℂ} (h : q * s = s' * q) (r : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    q * cplxO r s z = cplxO r s' (q * z) := by
  unfold cplxO
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc s']

theorem annih_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (sW : RealMat W) (sH : RealMat H)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    annih (heisO ψ A B) θ τ (cplxO s (sumMat o sW sH τ)) z (o.boxT A f g) =
      o.boxT A (annih (heisO ψ A W) θ τ (cplxO s (sW τ)) (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (annih (heisO ψ A H) θ τ (cplxO s (sH τ)) (o.qB.map (tauE D τ) * z) g) := by
  unfold annih
  rw [dRho_boxT o hθ hψ τ _ hf hg, dRho_boxT o hθ hψ τ _ hf hg, mul_cplxO (qA_sumMat o sW sH τ),
    mul_cplxO (qB_sumMat o sW sH τ)]
  funext x
  simp only [OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA (sumMat o sW sH) (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ Φ₁ Φ₂ ⟨t₁, N₁, k₁⟩ ⟨t₂, N₂, k₂⟩
  have hT : ∀ (S : HSp D) τ J z f, IsThetaFunO ψ A S f → IsThetaFunO ψ A S (annih (heisO ψ A S) θ τ J z f) :=
    fun S τ J z f hf => theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf))
  refine ⟨o.isThetaFunO_boxT t₁ t₂, N₁ + N₂, ?_⟩
  refine killed_of_leibniz₂ (P₁ := D.what₂.Tau × Matrix (Fin W.rank) (Fin A.rank) ℂ)
    (P₂ := D.what₂.Tau × Matrix (Fin H.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (fun p f => annih (heisO ψ A W) θ p.1 (cplxO (sA p.1) (sW p.1)) p.2 f)
    (fun p f => annih (heisO ψ A H) θ p.1 (cplxO (sA p.1) (sH p.1)) p.2 f)
    (fun p f => annih (heisO ψ A B) θ p.1 (cplxO (sA p.1) (sumMat o sW sH p.1)) p.2 f)
    (IsThetaFunO ψ A W) (IsThetaFunO ψ A H) (IsThetaFunO ψ A B) (o.boxT A)
    (fun q => (q.1, o.qA.map (tauE D q.1) * q.2)) (fun q => (q.1, o.qB.map (tauE D q.1) * q.2))
    (fun p f hf => hT W _ _ _ f hf) (fun p f hf => hT H _ _ _ f hf) (fun p f hf => hT B _ _ _ f hf)
    (fun q f g hf hg => ?_) (fun q => ?_)
    (fun f g hf hg => o.isThetaFunO_boxT hf hg) (fun g => ?_) (fun f => ?_)
    (fun q f g hf hg => annih_boxT o hθ hψ q.1 (sA q.1) sW sH q.2 hf hg)
    _ N₁ N₂ Φ₁ Φ₂ le_rfl t₁ t₂ k₁ k₂
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, smul_add]
    abel
  · funext x
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]
  · funext x
    simp [OrthDec.boxT]
  · funext x
    simp [OrthDec.boxT]

end GlobalTheory.Core.Rk.FockBoxT

end
end

