module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapPreimageVolumeLowerBound
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFinite
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreNonzero

open Topology Set Filter

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

private theorem exists_continuous_compactSupport_bump_of_isOpen (hU : IsOpen U) {x : V} (hx : x ∈ U) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧ φ x = 1 ∧
      ∀ v, 0 ≤ φ v := by
  obtain ⟨O, hO, hxO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hU
      (Set.singleton_subset_iff.mpr hx)
  obtain ⟨g, hgs, hg1, hg01⟩ :=
    exists_tsupport_one_of_isOpen_isClosed hO hOc isClosed_singleton hxO
  refine ⟨g, g.continuous, ?_, hgs.trans (subset_closure.trans hOU), ?_, fun v => (hg01 v).1⟩
  · exact hOc.of_isClosed_subset (isClosed_tsupport _) (hgs.trans subset_closure)
  · simpa using hg1 (Set.mem_singleton x)

theorem fib_ne_zero_of_lb (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) {f' : V → X}
    (hf' : Continuous f') (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    {x : V} (hx : x ∈ U) {b0 : X}
    (hlb : ∀ W : Set V, IsOpen W → x ∈ W → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 b0,
      ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W)) :
    fib b0 ≠ 0 := by
  intro h0
  obtain ⟨φ, hφc, hφs, hφU, hφx, hφ0⟩ := exists_continuous_compactSupport_bump_of_isOpen hU hx
  obtain ⟨hsupp, hdis, hcont⟩ := h
  obtain ⟨hint, hgc⟩ := hcont φ hφc hφs hφU

  set W : Set V := {v | (1 / 2 : ℝ) < φ v} with hW
  have hWo : IsOpen W := isOpen_lt continuous_const hφc
  have hxW : x ∈ W := by
    show (1 / 2 : ℝ) < φ x
    rw [hφx]; norm_num
  have hWU : W ⊆ U := fun v hv =>
    hφU (subset_tsupport _ (by
      show φ v ≠ 0
      exact ne_of_gt (lt_trans (by norm_num) hv)))
  obtain ⟨c, hc0, hctop, N, hN, hlbN⟩ := hlb W hWo hxW
  set e : ℝ≥0∞ := ENNReal.ofReal (1 / 2) * c with he
  have he0 : e ≠ 0 := mul_ne_zero (by simp) hc0.ne'
  have hetop : e ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have hepos : 0 < e.toReal := ENNReal.toReal_pos he0 hetop
  set δ : ℝ := e.toReal / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδe : ENNReal.ofReal δ < e := by
    rw [← ENNReal.ofReal_toReal hetop, ENNReal.ofReal_lt_ofReal_iff hepos, hδ]
    linarith

  have hgcont : Continuous (fun b => ∫ v, φ v ∂(fib b)) := continuousOn_univ.mp hgc
  have hg0 : (∫ v, φ v ∂(fib b0)) = 0 := by simp [h0]
  have hnear : {b | (∫ v, φ v ∂(fib b)) < δ} ∈ 𝓝 b0 :=
    hgcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hg0]; exact hδpos))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hN hnear)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hK0 : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKtop : ν K ≠ ⊤ := hKc.measure_lt_top.ne

  set A : Set V := f' ⁻¹' K with hA
  have hAm : MeasurableSet A := (hKc.isClosed.preimage hf').measurableSet
  set Φ : V → ℝ≥0∞ := A.indicator (fun v => ENNReal.ofReal (φ v)) with hΦ
  have hΦm : Measurable Φ := (ENNReal.measurable_ofReal.comp hφc.measurable).indicator hAm
  have hinner : ∀ b, ∫⁻ v, Φ v ∂(fib b) =
      K.indicator (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) b := by
    intro b
    have hon : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U := ae_iff.mpr (hsupp b)
    have hae : ∀ᵐ v ∂(fib b), f' v = b := by
      filter_upwards [hon] with v hv
      apply hι
      rw [← hff']
      exact hv.1
    have hcongr : Φ =ᵐ[fib b] fun v => K.indicator (fun _ => ENNReal.ofReal (φ v)) b := by
      filter_upwards [hae] with v hv
      by_cases hb : b ∈ K
      · have hvA : v ∈ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_mem hvA, Set.indicator_of_mem hb]
      · have hvA : v ∉ A := by rw [hA, Set.mem_preimage, hv]; exact hb
        rw [hΦ, Set.indicator_of_notMem hvA, Set.indicator_of_notMem hb]
    rw [lintegral_congr_ae hcongr]
    by_cases hb : b ∈ K
    · simp only [Set.indicator_of_mem hb]
      exact (ofReal_integral_eq_lintegral_ofReal (hint b (Set.mem_univ b))
        (ae_of_all _ hφ0)).symm
    · simp [Set.indicator_of_notMem hb]
  have hupper : ∫⁻ v in U, Φ v ∂μ ≤ ENNReal.ofReal δ * ν K := by
    rw [hdis Φ hΦm]
    simp_rw [hinner]
    rw [lintegral_indicator hKm]
    calc ∫⁻ b in K, ENNReal.ofReal (∫ v, φ v ∂(fib b)) ∂ν
        ≤ ∫⁻ _ in K, ENNReal.ofReal δ ∂ν :=
          setLIntegral_mono measurable_const
            (fun b hb => ENNReal.ofReal_le_ofReal (hKsub hb).2.le)
      _ = ENNReal.ofReal δ * ν K := setLIntegral_const K _
  have hpre : f ⁻¹' (ι '' K) = A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, hff', hA]
    constructor
    · rintro ⟨b, hb, hbv⟩
      rwa [← hι hbv]
    · intro hv
      exact ⟨_, hv, rfl⟩
  have hsub : A ∩ W ⊆ {v | ENNReal.ofReal (1 / 2) ≤ Φ v} ∩ U := by
    intro v hv
    refine ⟨?_, hWU hv.2⟩
    show ENNReal.ofReal (1 / 2) ≤ Φ v
    rw [hΦ, Set.indicator_of_mem hv.1]
    exact ENNReal.ofReal_le_ofReal hv.2.le
  have hlower : e * ν K ≤ ∫⁻ v in U, Φ v ∂μ := by
    calc e * ν K = ENNReal.ofReal (1 / 2) * (c * ν K) := by rw [he, mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2) * μ (f ⁻¹' (ι '' K) ∩ W) :=
          mul_le_mul_of_nonneg_left (hlbN K (fun b hb => (hKsub hb).1) hKm) (by positivity)
      _ ≤ ENNReal.ofReal (1 / 2) * (μ.restrict U) {v | ENNReal.ofReal (1 / 2) ≤ Φ v} := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hpre]
          exact (measure_mono hsub).trans (Measure.le_restrict_apply _ _)
      _ ≤ ∫⁻ v in U, Φ v ∂μ := mul_meas_ge_le_lintegral hΦm _
  have hle := hlower.trans hupper
  rw [mul_comm e, mul_comm (ENNReal.ofReal δ)] at hle
  exact absurd hle (not_le.mpr (ENNReal.mul_lt_mul_right hK0.ne' hKtop hδe))

end Gen

section Tens

open PI.VolStabS PI.VolStabS.TensAllW

theorem fib_tens {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (x : Fin a → Fin M → R ⊗[F] E) (S : HermR R σ a) (hx : LinearIndependent (R ⊗[F] E) x)
    (hlb : ∀ W : Set (Fin a → Fin M → R ⊗[F] E), IsOpen W → x ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ nhds S, ∀ T ⊆ N, MeasurableSet T →
        c * ν T ≤ μ ((gramR R σ J) ⁻¹' (Subtype.val '' T) ∩ W)) :
    fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin M → R ⊗[F] E), IsCompact K →
      K ⊆ {X | LinearIndependent (R ⊗[F] E) X} → fib S K < ⊤ := by
  have hopen : IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    isOpen_linIndep (Module.finBasis F E) R hU hL
  refine ⟨fib_ne_zero_of_lb h hopen (f' := gramH R σ hσ J hJ) (continuous_gramH R σ hσ J hJ)
    (fun _ => rfl) Subtype.val_injective hx hlb, fun K hK hKU => ?_⟩
  exact PI.VolStabS.FibUniq.fin_cpt h hopen S K hK hKU

end Tens

theorem fibre_nonzero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib h x S hx hS
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ y, σ (σ y) = y := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v)
    (PI.VolStabS.TensAllW.lip_field _) μ ν fib h x S hx
    (_root_.GlobalTheory.GramPreimageLB.lb_gram_preimage F E σ hCM n J hJ v a μ ν hμ hν x S hx hS)

end GlobalTheory.LocalFibreNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTerAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.principalLevelFrame GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.RowFrameParts

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R F X0), StdPsi Y.hF Y.PY ∧ ∀ σ, R.HE.e (Y.eE (D.what₂.onb σ)) ∈ isotE R.θ Y.PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rowRepR R.θ (Y.eFT (D.what₂.ft σ))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y
  refine ⟨Y.stdPsi.1, fun σ => ?_⟩
  have h := Y.tied.sharp.ft σ
  have h1 := Y.prtE (D.what₂.ft σ)
  have h2 := Y.eE_read (D.what₂.onb σ)
  have h3 := h1 ▸ h
  obtain ⟨z, hz, hze⟩ := h3
  rw [h2] at hze
  have : z = R.HE.e (Y.eE (D.what₂.onb σ)) := LinearEquiv.injective _ hze
  rw [← this]
  exact hz

end GlobalTheory.Mem.R3.RowFrameParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselPairMajorantMulRight
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.CellMajTransfer


open Formalism.FourierDecayAlt in
theorem pt_bound {k r : ℕ} (L : LocBessel k r) {γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ₁ ∈ UH (Hpk k r)) (ha : a ∈ UH (Hpk k r)) {b : ℝ} (hb : 0 ≤ b) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ h ∈ UWset k r L.z', B.gN h ≤ K)
    {p : PairSp k r} (hp : p ∈ GlobalTheory.CellOrbInt.pairSet L) {h'' : Mt k r} (hh : Matrix.of h'' ∈ UWset k r L.z') :
    pairMaj (γ₁ * a) b p ≤ (K * K * B.gN a⁻¹) ^ b * pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set X : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * (γ₁ * a) *
    Matrix.of p.2.2 * Matrix.of p.2.1 with hX
  set Y : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ₁ *
    (a * Matrix.of p.2.2 * a⁻¹) * Matrix.of h'' with hY
  have hXv : pairMaj (γ₁ * a) b p = B.gN X ^ (-b) := rfl
  have hYv : pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) = B.gN Y ^ (-b) := rfl
  rw [hXv, hYv]
  have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
  have eY : Y = X * ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := by
    simp only [hX, hY, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hh'u]
  have hai : a⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha
  have hA1 : 1 ≤ B.gN a⁻¹ := P.BetaSesquilinearity.gN_ge_one hai
  have hYG : Y ∈ B.GV k r := by
    rw [hY]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1)) hγ)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul ha h4.1) hai)) hh.1
  have hY1 : 1 ≤ B.gN Y := P.BetaSesquilinearity.gN_ge_one hYG
  have hX0 : 0 ≤ B.gN X := P.B6.gN_nonneg X
  have hle : B.gN Y ≤ (K * K * B.gN a⁻¹) * B.gN X := by
    rw [eY]
    have e1 := P.B6.gN_mul_le X ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have e2 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) (Matrix.of h'')
    have e3 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹) a⁻¹
    have k1 := hK _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
    have k2 := hK _ hh
    have n1 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹)
    have n2 := P.B6.gN_nonneg (a⁻¹)
    have n3 := P.B6.gN_nonneg (Matrix.of h'' : B.Mat k r)
    have n4 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹)
    have n5 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have s1 : B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') ≤ K * K * B.gN a⁻¹ := by
      calc _ ≤ B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) * B.gN (Matrix.of h'' : B.Mat k r) := e2
        _ ≤ (B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹) * B.gN a⁻¹) * K :=
            mul_le_mul e3 k2 n3 (mul_nonneg n1 n2)
        _ ≤ (K * B.gN a⁻¹) * K := by gcongr
        _ = K * K * B.gN a⁻¹ := by ring
    calc _ ≤ B.gN X * B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := e1
      _ ≤ B.gN X * (K * K * B.gN a⁻¹) := mul_le_mul_of_nonneg_left s1 hX0
      _ = (K * K * B.gN a⁻¹) * B.gN X := by ring
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hc0 : 0 < c := by linarith
  have hcb : c ^ b * c ^ (-b) = 1 := by
    rw [← Real.rpow_add hc0, add_neg_cancel, Real.rpow_zero]
  have hmono : (c * B.gN X) ^ (-b) ≤ B.gN Y ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
  calc B.gN X ^ (-b) = c ^ b * (c * B.gN X) ^ (-b) := by
        rw [Real.mul_rpow hc0.le hX0, ← mul_assoc, hcb, one_mul]
    _ ≤ c ^ b * B.gN Y ^ (-b) := mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hc0.le _)

end GlobalTheory.CellMajTransfer

namespace GlobalTheory.CellMajTransfer


open Formalism.FourierDecayAlt in
theorem inner_eq {k r : ℕ} (L : LocBessel k r) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {C : ℝ≥0∞}
    (hmap : L.μN.map (conjM a) = C • L.μN) {f : PairSp k r → ℝ≥0∞} (hfm : Measurable f) (x : Mt k r × Mt k r) :
    ∫⁻ y, ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' ∂(L.μW'.prod L.μN) = C * ∫⁻ y, f (x, y) ∂(L.μW'.prod L.μN) := by
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hF : Measurable fun q : Mt k r × (Mt k r × Mt k r) => f (x, (q.1, conjM a q.2.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk (hconj.comp measurable_snd.snd)))
  have hG : Measurable fun y : Mt k r × Mt k r => ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' :=
    hF.lintegral_prod_left'
  have hH' : Measurable fun q : Mt k r × Mt k r => f (x, (q.1, q.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hH : Measurable fun n' : Mt k r => ∫⁻ h'', f (x, (h'', n')) ∂L.μW' := hH'.lintegral_prod_left'
  have hfx : Measurable fun y : Mt k r × Mt k r => f (x, y) := hfm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hG.aemeasurable, lintegral_prod _ hfx.aemeasurable]
  simp only [lintegral_const, L.hμW'.2, one_mul]
  have e1 : ∫⁻ n', ∫⁻ h'', f (x, (h'', conjM a n')) ∂L.μW' ∂L.μN =
      ∫⁻ n', ∫⁻ h'', f (x, (h'', n')) ∂L.μW' ∂(L.μN.map (conjM a)) := by
    rw [lintegral_map hH hconj]
  rw [e1, hmap, lintegral_smul_measure, smul_eq_mul]
  have hs := lintegral_lintegral_swap (μ := L.μW') (ν := L.μN) (f := fun h'' n' => f (x, (h'', n')))
    hH'.aemeasurable
  rw [hs, mul_one]


open Formalism.FourierDecayAlt in
theorem integrable_mul_right : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (C : ℝ≥0∞), 0 < L.κN → L.κN ≠ ⊤ → 0 ≤ b → γ₁ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → C ≠ ⊤ → L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ₁ b) (Formalism.MainNotions.S.pairMeas L) → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (γ₁ * a) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L γ₁ a b C _hκ0 _hκ hb hγ ha hC hmap hint
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  obtain ⟨K, hK1, hK⟩ := P.Dx3.UW_bound L.z' L.hz'.1 L.hz'.2
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  set f : PairSp k r → ℝ≥0∞ := fun p => ENNReal.ofReal (pairMaj γ₁ b p) with hfdef
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (GlobalTheory.CellMaj.meas_pairMaj γ₁ b)
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  set Φ : PairSp k r × Mt k r → PairSp k r := fun q => (q.1.1, (q.2, conjM a q.1.2.2)) with hΦdef
  have hΦ : Measurable Φ := measurable_fst.fst.prodMk (measurable_snd.prodMk (hconj.comp measurable_fst.snd.snd))
  have aW' : ∀ᵐ y ∂L.μW', Matrix.of y ∈ UWset k r L.z' := by rw [ae_iff]; exact L.hμW'.1.2.2.1
  have hP0 : ∀ p, 0 ≤ pairMaj (γ₁ * a) b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hQ0 : ∀ p, 0 ≤ pairMaj γ₁ b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hcb0 : 0 ≤ c ^ b := Real.rpow_nonneg (by rw [hc]; have := P.B6.gN_nonneg a⁻¹; positivity) _
  have step1 : ∀ᵐ p ∂(pairMeas L), ENNReal.ofReal (pairMaj (γ₁ * a) b p) ≤
      ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' := by
    filter_upwards [GlobalTheory.CellOrbInt.ae_pairMeas L] with p hp
    calc ENNReal.ofReal (pairMaj (γ₁ * a) b p) = ∫⁻ _h'', ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂L.μW' := by
          rw [lintegral_const, L.hμW'.2, mul_one]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [aW'] with h'' hh
          rw [hfdef, ← ENNReal.ofReal_mul hcb0]
          exact ENNReal.ofReal_le_ofReal (pt_bound L hγ ha hb hK1 hK hp hh)
  have step2 : ∫⁻ p, ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) = C * ∫⁻ p, f p ∂(pairMeas L) := by
    have hm : Measurable fun p : PairSp k r => ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' := (hfm.comp hΦ).lintegral_prod_right'
    unfold pairMeas
    rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hfm.aemeasurable]
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_congr fun x => ?_
    exact inner_eq L a hmap hfm x
  have hfin : ∫⁻ p, f p ∂(pairMeas L) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hQ0)).1 hint.2
  refine ⟨(GlobalTheory.CellMaj.meas_pairMaj (γ₁ * a) b).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP0)]
  calc ∫⁻ p, ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂(pairMeas L)
      ≤ ∫⁻ p, ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) := lintegral_mono_ae step1
    _ = ENNReal.ofReal (c ^ b) * (C * ∫⁻ p, f p ∂(pairMeas L)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [step2]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hC.lt_top hfin)

end GlobalTheory.CellMajTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjUnipotentHaarEqSmul
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
namespace GlobalTheory.NConjHaar

theorem map_conj_eq_smul : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r), 0 < L.κN → L.κN ≠ ⊤ → ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ n, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ a * n * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN := by
  intro k r L h0 ht a ha hN
  have hμ := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN h0 ht.lt_top
  have hu : IsUnit a.det := GlobalTheory.Amp.StabHaar.unit_of_GG ha
  have hmap := GlobalTheory.Amp.StabHaar.haar_conj (G := Formalism.QuantumDeterminants.Nset k r) (G' := Formalism.QuantumDeterminants.Nset k r) a hu hN hμ
  obtain ⟨c, c0, ct, hc⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (Formalism.FourierDecayAlt.P.B2x2.closedN k r) hmap hμ
  exact ⟨c, ct, hc⟩

end GlobalTheory.NConjHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZero
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory.SplitProj

theorem proj_eq_lift_compAt (L : Type) [Field L] [NumberField L] (s : SplitPlace L) (x : AL L) :
    s.proj x = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) (compAt L s.v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem proj_eq_zero_of_compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L)
    (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  intro L _ _ s a h
  rw [proj_eq_lift_compAt, h, map_zero]

end GlobalTheory.SplitProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstantStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bessel_constant : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  first | exact @GlobalTheory.AmpNorm.lintegral_hsNormSq_amp | exact GlobalTheory.AmpNorm.lintegral_hsNormSq_amp | (intros; apply GlobalTheory.AmpNorm.lintegral_hsNormSq_amp <;> assumption)
end

