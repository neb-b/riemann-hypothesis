module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPairingLaws

theorem ipO_self {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  unfold ipO nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem countable_ratL' {D : D7} (S T : HSp D) : Countable ↥(ratL T S) := by
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := D.host.E)
  haveI : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have h : (ratL T S : Set (WO S T)).Countable := by
    rw [ratL, AddMonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem ipO_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IntegrableOn (fun w => f w * (starRingEnd ℂ) (g w)) 𝓕 μ ∧ ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) ∧ (∀ c : ℂ, ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g ∧ ipO μ 𝓕 f (c • g) = (starRingEnd ℂ) c * ipO μ 𝓕 f g) ∧ (∀ f', IsThetaFunO ψ S T f' → ipO μ 𝓕 (f + f') g = ipO μ 𝓕 f g + ipO μ 𝓕 f' g ∧ ipO μ 𝓕 g (f + f') = ipO μ 𝓕 g f + ipO μ 𝓕 g f') ∧ ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) ∧ (nrm2 μ 𝓕 f = 0 → f = 0) ∧ (∀ w, ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w g) = ipO μ 𝓕 f g ∧ ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g)) ∧ ∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f g = ipO μ 𝓕 f g := by
  intro D ψ S T μ 𝓕 hψ hμ f g hf hg
  have hμ₀ := hμ
  unfold IsCovolOne at hμ₀
  obtain ⟨hHaar, hFD, -⟩ := hμ₀
  haveI := hHaar
  obtain ⟨-, hL2⟩ := GlobalTheory.ThetaSquare.theta_square_integrable D S T
  obtain ⟨hSq, hHeis, -⟩ := hL2 ψ hψ
  obtain ⟨-, hInvol, hPres, hUnit, -⟩ := hHeis
  obtain ⟨-, -, ⟨-, hHL⟩, -⟩ := (GlobalTheory.ThetaAllChar.thetaFacts D).std hψ S T

  have hInt : ∀ a b : WO S T → ℂ, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b →
      IntegrableOn (fun w => a w * (starRingEnd ℂ) (b w)) 𝓕 μ :=
    fun a b ha hb => (hHL μ μ 𝓕 𝓕 hμ hμ a b ha hb).2.1
  refine ⟨hInt f g hf hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    unfold ipO
    rw [← integral_conj]
    congr 1
    funext w
    rw [map_mul, Complex.conj_conj, mul_comm]
  · intro c
    constructor
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
  · intro f' hf'
    constructor
    · unfold ipO
      rw [← integral_add (hInt f g hf hg) (hInt f' g hf' hg)]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
    · unfold ipO
      rw [← integral_add (hInt g f hg hf) (hInt g f' hg hf')]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
  · exact ipO_self μ 𝓕 f
  ·

    intro h0
    haveI := countable_ratL' S T
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : MeasurableConstVAdd ↥(ratL T S) (WO S T) := ⟨fun γ => measurable_const_add (γ : WO S T)⟩
    haveI : VAddInvariantMeasure ↥(ratL T S) (WO S T) μ :=
      ⟨fun γ s _ => measure_preimage_add μ (γ : WO S T) s⟩
    unfold nrm2 at h0
    have hI : IntegrableOn (fun w => ‖f w‖ ^ 2) 𝓕 μ := by
      refine (hInt f f hf hf).norm.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    have hae : (fun w => ‖f w‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg ‖f w‖) hI).1 h0
    have hae' : ∀ᵐ w ∂μ.restrict 𝓕, f w = 0 :=
      hae.mono fun w hw => by simpa using hw
    have htopen : IsOpen {x : WO S T | f x ≠ 0} := isOpen_ne_fun hf.cont continuous_const
    have hts : μ ({x : WO S T | f x ≠ 0} ∩ 𝓕) = 0 := by
      rw [← Measure.restrict_apply₀' hFD.nullMeasurableSet]
      exact ae_iff.1 hae'
    have hzero : μ {x : WO S T | f x ≠ 0} = 0 := by
      refine hFD.measure_zero_of_invariant _ (fun γ => ?_) hts
      ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change f ((↑(-γ) : WO S T) + y) ≠ 0 ↔ f y ≠ 0
      rw [← norm_ne_zero_iff, (hSq f hf).1 (↑(-γ)) (-γ).2 y, norm_ne_zero_iff]
    have hempty := (htopen.measure_eq_zero_iff μ).1 hzero
    funext x
    by_contra hx
    have hmem : x ∈ {x : WO S T | f x ≠ 0} := hx
    rw [hempty] at hmem
    exact hmem
  · intro w
    refine ⟨hUnit μ 𝓕 hHaar hFD w f g hf hg, ?_⟩
    have hg' : IsThetaFunO ψ S T (heisO ψ S T (-w) g) := hPres (-w) g hg
    have e := hInvol (-w) g
    rw [neg_neg] at e
    calc ipO μ 𝓕 (heisO ψ S T w f) g
        = ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w (heisO ψ S T (-w) g)) := by rw [e]
      _ = ipO μ 𝓕 f (heisO ψ S T (-w) g) := hUnit μ 𝓕 hHaar hFD w f _ hf hg'
  ·
    intro μ' 𝓕' h'
    have a := (hHL μ' μ 𝓕' 𝓕 h' hμ f g hf hg).2.2
    have b := (hHL μ μ 𝓕 𝓕 hμ hμ f g hf hg).2.2
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero.heisO_apply_zero] at a b
    unfold ipO
    rw [a, b]

end GlobalTheory.ThetaPairingLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistThetaMean

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a b : Mx D W.rank r) :
    isoPart V W C (a + b) = isoPart V W C a + isoPart V W C b :=
  Matrix.add_mul _ _ _

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {γ : Mx D W.rank r}
    (hγ : γ ∈ ratMx D W.rank r) : isoPart V W C γ ∈ ratL W V := by
  obtain ⟨g, rfl⟩ := hγ
  refine ⟨g * (adj D C * V.gram), ?_⟩
  show (g * (adj D C * V.gram)).map (incA D) = g.map (incA D) * (adj D C * V.gram).map (incA D)
  exact Matrix.map_mul

theorem isoPart_continuous (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) :=
  continuous_id.matrix_mul continuous_const

theorem midPart_continuous (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    Continuous (midPart V V' W B) :=
  continuous_id.matrix_mul continuous_const

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean

theorem integral_continuous_of_bounded {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : X × Y → ℂ) (hk : Continuous k) (b : ℝ) (hb : ∀ q, ‖k q‖ ≤ b) :
    Continuous (fun p => ∫ y, k (p, y) ∂ν) ∧ ∀ p, ‖∫ y, k (p, y) ∂ν‖ ≤ b * ν.real Set.univ := by
  refine ⟨continuous_of_dominated (bound := fun _ => b) (fun p => ?_) (fun p => ?_) (integrable_const _) ?_,
    fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => hb _)⟩
  · exact (hk.comp (Continuous.prodMk_right p)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hb _
  · exact Filter.Eventually.of_forall fun y => hk.comp (Continuous.prodMk_left y)

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean


open TopologicalSpace in
theorem mean_continuous_periodic : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B _hs C' _h1 _h2 _h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' h𝓕' P G hP hG
  haveI hAE : SecondCountableTopology (AE D) := by
    have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E)
      (AF D.host.F)
    exact e.secondCountableTopology
  haveI hM : SecondCountableTopology (Mx D W.rank r) :=
    inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin r → AE D))
  haveI hM2 : SecondCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    @instSecondCountableTopologyProd _ _ _ _ hM hM
  haveI : FirstCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    SecondCountableTopology.to_firstCountableTopology _
  haveI : FirstCountableTopology (Mx D W.rank r) := SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V'
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO V' W) (ratL W V') hK hKc μ' h𝓕'⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by
    rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b1, hb1⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hP
  obtain ⟨b2, hb2⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hh : Continuous fun w => P w * star (G w) := hP.cont.mul hG.cont.star
  have hhb : ∀ w, ‖P w * star (G w)‖ ≤ b1 * b2 := fun w => by
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb1 w) (hb2 w) (norm_nonneg _) ((norm_nonneg _).trans (hb1 w))
  have hu : Continuous fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2 :=
    (((isoPart_continuous V W C').comp (continuous_fst.comp continuous_fst)).add
      ((isoPart_continuous V W C).comp (continuous_snd.comp continuous_fst))).add
      ((midPart_continuous V V' W B).comp continuous_snd)
  obtain ⟨hin, hinb⟩ := integral_continuous_of_bounded (μ'.restrict 𝓕')
    (fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      P (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2) *
        star (G (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2))) (hh.comp hu) (b1 * b2)
    (fun q => hhb _)
  refine ⟨?_, ?_⟩
  · exact (integral_continuous_of_bounded (μ.restrict 𝓨)
      (fun q : Mx D W.rank r × Mx D W.rank r => ∫ x in 𝓕',
        P (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x) *
          star (G (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x)) ∂μ') hin _ hinb).1
  · intro γ hγ t
    have key : ∀ y x, P (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x)) =
        P (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' t + isoPart V W C y + midPart V V' W B x)) := fun y x => by
      rw [isoPart_add, add_assoc (isoPart V W C' γ) (isoPart V W C' t),
        add_assoc (isoPart V W C' γ) (isoPart V W C' t + isoPart V W C y)]
      exact GlobalTheory.ThetaSchur.prod_periodic hψ hP hG (isoPart_rat V W C' hγ) _
    simp_rw [key]

end GlobalTheory.TwistThetaMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScaling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviRes

variable {D : D7}

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat M) = GlobalTheory.MixModel.rat Mᴴ := by
  rw [← GlobalTheory.MixModel.cT_sig]
  ext i j
  simp [GlobalTheory.MixModel.adj, GlobalTheory.MixModel.rat, Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem symplOH_add_right (S T : HSp D) (x y z : WO S T) :
    symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add, map_add]

theorem symplOH_mul_rat (V W : HSp D) {s t : ℕ} (X : Matrix (Fin s) (Fin V.rank) D.host.E)
    (Y : Matrix (Fin t) (Fin V.rank) D.host.E) (hXY : X * V.gram⁻¹ * Yᴴ = 0) (q : Mx D W.rank s) (a : Mx D W.rank t) :
    symplOH V W (q * GlobalTheory.MixModel.rat X) (a * GlobalTheory.MixModel.rat Y) = 0 := by
  have hz : GlobalTheory.MixModel.rat X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Yᴴ = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hXY, GlobalTheory.MixModel.rat_zero]
  have hre : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (a * GlobalTheory.MixModel.rat Y) * (GlobalTheory.MixModel.gA W * (q * GlobalTheory.MixModel.rat X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Yᴴ * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q)) * GlobalTheory.MixModel.rat X := by
    rw [GlobalTheory.MixModel.adj_mul, adj_rat]
    simp only [Matrix.mul_assoc]
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, hre, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero, map_zero]

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem iso_iso (hs : IsIsoSplit V V' C B) : (adj D C * V.gram) * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, h0]

theorem iso_mid (hs : IsIsoSplit V V' C B) :
    (adj D C * V.gram) * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * B = 0 := hs.orth
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

theorem periodic (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ y : Mx D W.rank r,
      f (isoPart V W C (γ + y) + midPart V V' W B x) = f (isoPart V W C y + midPart V V' W B x) := by
  intro γ hγ y
  obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
  have e1 : ∀ z : Mx D W.rank r, isoPart V W C z = z * GlobalTheory.MixModel.rat (adj D C * V.gram) := fun z => rfl
  have e2 : midPart V V' W B x = (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) := rfl
  have h0 : symplOH V W (GlobalTheory.MixModel.rat γ0 * GlobalTheory.MixModel.rat (adj D C * V.gram))
      (isoPart V W C y + midPart V V' W B x) = 0 := by
    rw [symplOH_add_right, e1, e2,
      symplOH_mul_rat V W (adj D C * V.gram) (adj D C * V.gram) (iso_iso hs) (GlobalTheory.MixModel.rat γ0) y,
      symplOH_mul_rat V W (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (iso_mid hs) (GlobalTheory.MixModel.rat γ0) x,
      add_zero]
  have hq : f (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram)) + (isoPart V W C y + midPart V V' W B x)) =
      ψ (-(symplOH V W (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram))) (isoPart V W C y + midPart V V' W B x))) *
        f (isoPart V W C y + midPart V V' W B x) :=
    hf.quasi (γ0 * (adj D C * V.gram)) (isoPart V W C y + midPart V V' W B x)
  rw [e1 (GlobalTheory.MixModel.rat γ0 + y), Matrix.add_mul, add_assoc, ← e1 y, ← GlobalTheory.MixModel.rat_mul, hq,
    GlobalTheory.MixModel.rat_mul, h0, neg_zero, AddChar.map_zero_eq_one, one_mul]

end Split

theorem mt_unitary (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.gA V := by
  rw [Matrix.mul_assoc]
  exact GlobalTheory.MixModel.mt_unitary V a

theorem mt_mul (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_mul_mt (S T : HSp D) (g : GA D S) (w : WO S T) :
    actO S T g 1 (HMul.hMul (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g)) = w := by
  rw [GlobalTheory.MixModel.actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.mul_one]

private lemma rat_adj_mul_gram_eq (V : HSp D) {s : ℕ} (B : Matrix (Fin V.rank) (Fin s) D.host.E) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) = GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.gA V := by
  rw [GlobalTheory.MixModel.rat_mul, adj_rat, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig, GlobalTheory.MixModel.gA]

private lemma gA_mul_mt_eq_adj_mt_inv_mul (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V := by
  calc GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a
      = (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a⁻¹) * Formalism.L2.Theta.mt V a := by
        rw [mt_unitary]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V * (Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a) := by
        rw [Matrix.mul_assoc]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V := by
        rw [← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem form_fix (V : HSp D) {s : ℕ} (a : GA D V) (B : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.rat (adj D B * V.gram) := by
  have hinv : Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv]

theorem form_scale (V : HSp D) {s : ℕ} (a : GA D V) (C : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C) :
    GlobalTheory.MixModel.rat (adj D C * V.gram) * Formalism.L2.Theta.mt V a =
      incA D (1 / 2) • GlobalTheory.MixModel.rat (adj D C * V.gram) := by
  have h2 : incA D (1 / 2) * (2 : AE D) = 1 := by
    rw [← map_ofNat (incA D) 2, ← map_mul]
    norm_num
  have hinv : Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
    calc Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C
        = (incA D (1 / 2) * (2 : AE D)) • (Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C) := by rw [h2, one_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ * ((2 : AE D) • GlobalTheory.MixModel.rat C)) := by
        rw [mul_smul, Matrix.mul_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C)) := by rw [h]
      _ = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
        rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  have hc : cA D (incA D (1 / 2)) = incA D (1 / 2) := GlobalTheory.MixModel.cA_half
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv,
    GlobalTheory.MixModel.adj_smul, hc, Matrix.smul_mul]

theorem res_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ a : GA D V, a ∈ GQ V → HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ l : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (a, 1) f) = l • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hcov
  refine ⟨1, fun f hf => ?_⟩
  have hC' : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C := haC
  have hB' : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := haB
  have hsub : ∀ w : WO V W,
      ω (a, 1) f w = f (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a)) := by
    intro w
    have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω a haQ 1 (one_mem _) f hf
      (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a))
    rwa [actO_mul_mt] at h1
  have hiso : ∀ y : Mx D W.rank r,
      HMul.hMul (isoPart V W C y : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
        isoPart V W C (incA D (1 / 2) • y) := by
    intro y
    show y * GlobalTheory.MixModel.rat (adj D C * V.gram) * Formalism.L2.Theta.mt V a =
      (incA D (1 / 2) • y) * GlobalTheory.MixModel.rat (adj D C * V.gram)
    rw [Matrix.mul_assoc, form_scale V a C hC', Matrix.mul_smul, Matrix.smul_mul]
  rw [one_smul]
  funext x
  have hmid : HMul.hMul (midPart V V' W B x : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
      midPart V V' W B x := by
    show (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) * Formalism.L2.Theta.mt V a =
      (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram)
    rw [Matrix.mul_assoc V'.gram⁻¹ (adj D B) V.gram, GlobalTheory.MixModel.rat_mul]
    simp only [Matrix.mul_assoc]
    rw [form_fix V a B hB']
  calc res V V' W C B μ 𝓨 (ω (a, 1) f) x
      = ∫ y in 𝓨, f (isoPart V W C (incA D (1 / 2) • y) + midPart V V' W B x) ∂μ := by
        show ∫ y in 𝓨, ω (a, 1) f (isoPart V W C y + midPart V V' W B x) ∂μ = _
        congr 1
        funext y
        rw [hsub, Matrix.add_mul, hiso, hmid]
    _ = ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B x) ∂μ :=
        GlobalTheory.UnipMean.mean_smul hcov (c := 1 / 2) (by norm_num)
          (fun y => f (isoPart V W C y + midPart V V' W B x)) (periodic hs hf x)
    _ = res V V' W C B μ 𝓨 f x := rfl

end GlobalTheory.LeviRes
end
end

