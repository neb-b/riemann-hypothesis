module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormula
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSets
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.FinCptOfIntegrable
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace PositivityTheory.Rg.Rsw.L.LatticeFibreBump

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem archBump [IsTotallyReal F] {M n : ℕ} (C : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (hC : IsCompact C) :
    ∃ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ ∧ ∀ Y ∈ C, φ Y = 1 := by
  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin n)
  let eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  obtain ⟨ρ, hρ⟩ := (hC.image eV.continuous).isBounded.subset_closedBall 0
  let β : ContDiffBump (0 : Fin N → ℝ) :=
    ⟨max ρ 1, max ρ 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : SchwartzMap (Fin N → ℝ) ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  refine ⟨fun X => f (eA X), ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩, fun Y hY => ?_⟩
  show ((β (eA Y) : ℝ) : ℂ) = 1
  have hm : eA Y ∈ Metric.closedBall (0 : Fin N → ℝ) β.rIn :=
    Metric.closedBall_subset_closedBall (le_max_left ρ 1) (hρ ⟨Y, hY, rfl⟩)
  rw [β.one_of_mem_closedBall hm, Complex.ofReal_one]

omit [NumberField F] [NumberField E] in
theorem repr_natCast_mul' {d : ℕ} (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R]
    [Algebra F R] (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((N : R ⊗[F] E) * y) k =
      (N : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem scaled_cpt_open {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hL : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧
      IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    IsCompact {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} ∧
      IsOpen {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  set u : Fv F v ⊗[F] E := algebraMap F _ ((N : F)⁻¹) with hu
  have hNu : (N : Fv F v ⊗[F] E) * u = 1 := by
    rw [hu, ← map_natCast (algebraMap F (Fv F v ⊗[F] E)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have hc : ∀ c : Fv F v ⊗[F] E, Continuous fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => c * Y a i :=
    fun c => continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have heq : {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} =
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => u * Y a i) '' latV b v := by
    ext Y
    constructor
    · intro hY
      refine ⟨_, hY, ?_⟩
      funext a i
      show u * ((N : Fv F v ⊗[F] E) * Y a i) = Y a i
      rw [← mul_assoc, mul_comm u, hNu, one_mul]
    · rintro ⟨Z, hZ, rfl⟩
      show (fun a i => (N : Fv F v ⊗[F] E) * (u * Z a i)) ∈ latV b v
      simpa only [← mul_assoc, hNu, one_mul] using hZ
  exact ⟨heq ▸ hL.1.image (hc u), hL.2.preimage (hc _)⟩


omit [NumberField E] in
theorem scaled_eq_lat {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hv : (algebraMap F (Af F) ((N : F)⁻¹)) v ∈ v.adicCompletionIntegers F) :
    {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} = latV b v := by
  have hw : algebraMap F (Fv F v) ((N : F)⁻¹) ∈ v.adicCompletionIntegers F := by
    have h : (algebraMap F (Af F) ((N : F)⁻¹)) v = algebraMap F (Fv F v) ((N : F)⁻¹) :=
      (evalV F v).commutes _
    rwa [h] at hv
  have hwN : algebraMap F (Fv F v) ((N : F)⁻¹) * (N : Fv F v) = 1 := by
    rw [← map_natCast (algebraMap F (Fv F v)) N, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have key : ∀ c : Fv F v, (N : Fv F v) * c ∈ v.adicCompletionIntegers F ↔ c ∈ v.adicCompletionIntegers F := by
    intro c
    constructor
    · intro h
      have := mul_mem hw h
      rwa [← mul_assoc, hwN, one_mul] at this
    · exact fun h => mul_mem (natCast_mem _ N) h
  ext Y
  simp only [Set.mem_ofPred_eq, latV, repr_natCast_mul', key]

theorem finCpt_of_integrable (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (n : ℕ) (h2n : 2 * n < M) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hν : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := F) (E := E) Φ → Integrable Φ ν) :
    IsFiniteMeasureOnCompacts ν := by
  classical
  have : IsTotallyReal F := hCM.1
  refine ⟨fun K hK => ?_⟩
  let b := Module.finBasis F E
  obtain ⟨N, R, hN, -, hsub⟩ := (_root_.GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples F E σ hCM _ b n M).2 K hK
  obtain ⟨hcInf, -, -, hlat, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM _ b n M
  obtain ⟨φ, hφ, hφ1⟩ := archBump (projInf '' K) (hK.image hcInf)
  let A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun v => {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}
  let y : Af F := algebraMap F (Af F) ((N : F)⁻¹)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | y v ∉ v.adicCompletionIntegers F}.Finite := y.2
  have hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => scaled_cpt_open b v N hN (hlat v)
  have hAl : ∀ v, v ∉ hfin.toFinset → A v = latV b v := fun v hv =>
    scaled_eq_lat b v N hN (not_not.mp fun h => hv (hfin.mem_toFinset.mpr h))
  have hΦ := _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat F E σ hCM M J hJ n h2n _ b hfin.toFinset φ A hφ hA hAl
  have hint := hν _ hΦ
  have h1 : K ⊆ {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := by
    intro X hX
    have e1 : GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X = 1 := by
      unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
      rw [hφ1 _ ⟨X, hX, rfl⟩, Set.indicator_of_mem
        (show projFin X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxFN A from fun v => (hsub X hX).1 v), one_mul]
    simp [e1]
  calc ν K ≤ ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := measure_mono h1
    _ = 1 * ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := (one_mul _).symm
    _ ≤ ∫⁻ X, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ ∂ν := mul_meas_ge_le_lintegral₀ hint.1.enorm 1
    _ < ⊤ := hint.2

end PositivityTheory.Rg.Rsw.L.LatticeFibreBump

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

abbrev thM (V : HSp D) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (T : Matrix (Fin r) (Fin r) D.host.E) :
    Measure (Fin r → Fin V.rank → AE D) :=
  GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram μH 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = T}

theorem thInt (V : HSp D) (hr : 2 * r < V.rank) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμH : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (T : Matrix (Fin r) (Fin r) D.host.E)
    (hT : ∀ a b, D.sp.cm.sig (T b a) = T a b) (hdet : T.det ≠ 0) (Φ : (Fin r → Fin V.rank → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    Integrable Φ (thM V μH 𝓕 T) := by
  classical
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  let b := Module.finBasis D.host.F D.host.E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf D.host.F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV D.host.F
  have : BorelSpace (Ainf D.host.F) := ⟨rfl⟩
  have : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), BorelSpace (Fv D.host.F v) :=
    fun _ => ⟨rfl⟩
  obtain ⟨minf, hminf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Ainf D.host.F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf D.host.F hCM.1) b laminf hinf.1 r
  choose m hm using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Fv D.host.F v)
    (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv D.host.F v) b (lam v) (hlam v).1 r
  have hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b (thM V μH 𝓕 T) 1
      (minf (hermOf (Ainf D.host.F) D.sp.cm.sig T hT)) (fun v => m v (hermOf (Fv D.host.F v) D.sp.cm.sig T hT)) :=
    _root_.GlobalTheory.CompanionTheory.SW.AllFrames.swMeas_all D.host.F D.host.E D.sp.cm.sig hCM r V.rank V.gram hJ (by omega) T hT hdet _ b laminf lam hinf hlam
      μH 𝓕 hμH h𝓕 minf m hminf hm
  obtain ⟨N, φ, A, S, hφ, hA, hAl, hsum⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.schwartzBruhat_eq_sum_pureTuples D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b Φ hΦ
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN D.host.F D.host.E V.rank r _ b _ 1 _ _ hEu
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R],
      IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det := by
    intro R _ _
    have h : (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det = HeckeCharacterZeroLocus.SiegelWeilU.inclR R T.det :=
      ((HeckeCharacterZeroLocus.SiegelWeilU.inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR R)
  have hP : ∀ i, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i)) (thM V μH 𝓕 T) := by
    intro i
    obtain ⟨hφm, hφi, -⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.FibN.fibre_schwartzN D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b laminf hinf
      minf hminf _ (hu _) (φ i) (hφ i)
    have hfin := fun v => _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b v (lam v)
      (hlam v) (m v) (hm v) (hermOf (Fv D.host.F v) D.sp.cm.sig T hT) (hu _) (A i v) (hA i v).1 (hA i v).2
    exact (hS₁ (S ∪ S₁) Finset.subset_union_right (φ i) hφm hφi.self_of_nhds (A i) (fun v => (hfin v).1)
      (fun v => (hfin v).2) (fun v hv => hAl i v fun h => hv (Finset.mem_union_left _ h))).1
  have hΦe : Φ = fun X => ∑ i, GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i) X := funext hsum
  rw [hΦe]
  exact integrable_finsetSum _ fun i _ => hP i

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end

