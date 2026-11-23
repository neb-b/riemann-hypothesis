module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0281
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0041
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFibreMeasureLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationComposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorph
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneIsotropic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeFact

theorem free_act {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (actW R σ J h X) := by
  let g : GL (Fin M) (R ⊗[F] E) := HA.mat R σ J h
  let e : (Fin M → R ⊗[F] E) ≃ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E) :=
    Matrix.toLin'OfInv (M := ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)))
      (M' := (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) (by simp) (by simp)
  have he : actW R σ J h X = e.toLinearMap ∘ X := by
    funext a
    simp [e, g, actW, actTup, Matrix.toLin'OfInv]
  rw [he]
  exact hX.map' e.toLinearMap (LinearEquiv.ker e)

theorem fib_compact_lt_top {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V}
    {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) (hU : IsOpen U) (b : X)
    {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨φ, hc, hcs, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hK hU hKU
  have hi := (h.2.2 φ hc hcs hs).1 b (Set.mem_univ b)
  refine lt_of_le_of_lt (GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hK h0 h1) ?_
  exact hi.lintegral_lt_top

theorem local_pack_free {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b)
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) :
    (∀ K : Set (Fin 1 → Fin M → R ⊗[F] E), IsCompact K →
      K ⊆ {Y | LinearIndependent (R ⊗[F] E) Y} → m (hermOf R σ 0 h₀) K < ⊤) ∧
    (∀ h : HA R σ J, (m (hermOf R σ 0 h₀)).map (actW R σ J h) = m (hermOf R σ 0 h₀)) ∧
    m (hermOf R σ 0 h₀) ({Y | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
      {Y | LinearIndependent (R ⊗[F] E) Y})ᶜ = 0 ∧
    (({Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
      {Y | LinearIndependent (R ⊗[F] E) Y}).Nonempty → m (hermOf R σ 0 h₀) ≠ 0) ∧
    (∀ X ∈ {Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
        {Y | LinearIndependent (R ⊗[F] E) Y},
      ∀ Y ∈ {Y : Fin 1 → Fin M → R ⊗[F] E | gramR R σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR R)} ∩
        {Y | LinearIndependent (R ⊗[F] E) Y},
      ∃ h : HA R σ J, actW R σ J h X = Y) := by
  obtain ⟨tr, lc, sc, t2, art, red, -⟩ := id hR
  haveI := tr
  haveI := lc
  haveI := sc
  haveI := t2
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (Fin 1 → Fin M → R ⊗[F] E) := tK8 1 M
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ R d b lam hlam
  haveI := hW 1 M
  haveI := hH 1
  have hU := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ R hR 1 M
  have hz : (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (F := F) R) = 0 := by
    ext a c
    simp
  refine ⟨fun K hK hKU => fib_compact_lt_top hm hU _ hK hKU,
    fun h => _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free F E σ hσ M J hJ R hR 1 _ _ m (hW 1 M) (hH 1) hm h _, ?_, ?_, ?_⟩
  · exact hm.1 (hermOf R σ 0 h₀)
  · rintro ⟨X, hX, hXf⟩
    exact _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero F E σ hσ M J hJ R hR _ _ m (hW 1 M) (hH 1) hm X hXf (hX.trans hz) _
  · rintro X ⟨hX, hXf⟩ Y ⟨hY, hYf⟩
    exact _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans.transitive_free_isotropic F E σ hσ M J hJ R hR X Y hXf hYf (hX.trans hz) (hY.trans hz)

theorem fact_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ℝ≥0, ∀ (φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → ∫⁻ X, pureL b S φinf φ X ∂I = (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b laminf lam hinf hlam minf hminf m hm I hIl hIinv hIT S
  classical
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hRI := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  have hRv := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  obtain ⟨trI, lcI, scI, t2I, -⟩ := id hRI
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hRv v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hRv v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hRv v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hRv v).2.2.2.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have kA := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  have kI := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  have kV := fun v => _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := kA.1
  haveI := kA.2.1
  haveI := kA.2.2.1
  haveI := kA.2.2.2.1
  haveI := kA.2.2.2.2.2.2.2.1 1 M
  haveI := kI.1
  haveI := kI.2.1
  haveI := kI.2.2.1
  haveI := kI.2.2.2.1
  haveI := kI.2.2.2.2.2.2.2.1 1 M
  haveI : ∀ v, IsTopologicalRing (Fv F v ⊗[F] E) := fun v => (kV v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v ⊗[F] E) := fun v => (kV v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v ⊗[F] E) := fun v => (kV v).2.2.1
  haveI : ∀ v, T2Space (Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fin 1 → Fin M → Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.2.2.2.2.1 1 M
  have uA := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ (AF F)
  have uI := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ (Ainf F)
  have uV := fun v => _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ (Fv F v)
  haveI := uI.1
  haveI := uI.2.1
  haveI := uI.2.2.1
  haveI := uI.2.2.2.1
  haveI : ∀ v, IsTopologicalGroup (HA (Fv F v) σ J) := fun v => (uV v).1
  haveI : ∀ v, LocallyCompactSpace (HA (Fv F v) σ J) := fun v => (uV v).2.1
  haveI : ∀ v, SecondCountableTopology (HA (Fv F v) σ J) := fun v => (uV v).2.2.1
  haveI : ∀ v, T2Space (HA (Fv F v) σ J) := fun v => (uV v).2.2.2.1
  have LI := local_pack_free σ hσ J hJ (Ainf F) hRI h₀ b laminf hinf.1 minf hminf
  have LV := fun v => local_pack_free σ hσ J hJ (Fv F v) (hRv v) h₀ b (lam v) (hlam v).1 (m v) (hm v)
  obtain ⟨cI, cF, cV, hlat, hint, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b 1 M
  have hprc : Continuous (FactS.pr S : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    cI.prodMk (continuous_pi fun v => (cV v.1).comp cF)
  have hprm : Measurable (FactS.pr S : (Fin 1 → Fin M → AF F ⊗[F] E) → _) := hprc.measurable
  have hintm : MeasurableSet (intOff b S : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    (hint S).measurableSet
  have actC : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] ,
      (Continuous fun p : HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) →
      ∀ h : HA R σ J, Continuous (actW R σ J h : (Fin 1 → Fin M → R ⊗[F] E) → _) :=
    fun R _ _ _ hc h => hc.comp (Continuous.prodMk_right h)
  have cAI := (uI.2.2.2.2.2 1).1
  have cAV := fun v => ((uV v).2.2.2.2.2 1).1
  have cAA := (uA.2.2.2.2.2 1).1
  set P := (I.restrict (intOff b S)).map (FactS.pr S) with hPdef
  haveI hPc : IsFiniteMeasureOnCompacts P := ⟨fun K hK => by
    rw [hPdef, Measure.map_apply hprm hK.isClosed.measurableSet,
      Measure.restrict_apply (hprm hK.isClosed.measurableSet)]
    exact FactS.preimage_lt_top σ hσ b S I K hK⟩
  have hPinv : ∀ (g₀ : HA (Ainf F) σ J) (g : ∀ v : S, HA (Fv F v.1) σ J),
      P.map (fun x => (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) = P := by
    intro g₀ g
    refine FactS.push_inv σ hσ J hJ b S I hIinv (fun v X => ((uV v).2.2.2.2.2 1).2.1 X) hprm
      (fun h => (actC _ cAA h).measurable) hintm g₀ g ?_
    refine Continuous.measurable (Continuous.prodMk ((actC _ cAI g₀).comp continuous_fst)
      (continuous_pi fun v => ?_))
    exact (actC _ (cAV v.1) (g v)).comp ((continuous_apply v).comp continuous_snd)
  have hZ₀ : IsClosed {Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
      gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} :=
    isClosed_eq (kI.2.2.2.2.2.2.2.2.2 1 M J) continuous_const
  have hZ : ∀ v : S, IsClosed {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
      gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} := fun v =>
    isClosed_eq ((kV v.1).2.2.2.2.2.2.2.2.2 1 M J) continuous_const
  have hU₀ := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ (Ainf F) hRI 1 M
  have hU : ∀ v : S, IsOpen {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
      LinearIndependent (Fv F v.1 ⊗[F] E) Y} := fun v =>
    GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ (Fv F v.1) (hRv v.1) 1 M
  have hPZ : P (({Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
        gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} ∩
        {Y | LinearIndependent (Ainf F ⊗[F] E) Y}) ×ˢ
      Set.univ.pi fun v : S => {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
        gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} ∩
        {Y | LinearIndependent (Fv F v.1 ⊗[F] E) Y})ᶜ = 0 := by
    have hms : MeasurableSet (({Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
        gramR (Ainf F) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Ainf F))} ∩
        {Y | LinearIndependent (Ainf F ⊗[F] E) Y}) ×ˢ
      Set.univ.pi fun v : S => {Y : Fin 1 → Fin M → Fv F v.1 ⊗[F] E |
        gramR (Fv F v.1) σ J Y = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (Fv F v.1))} ∩
        {Y | LinearIndependent (Fv F v.1 ⊗[F] E) Y}) :=
      (hZ₀.measurableSet.inter hU₀.measurableSet).prod
        (MeasurableSet.univ_pi fun v => (hZ v).measurableSet.inter (hU v).measurableSet)
    rw [hPdef, Measure.map_apply hprm hms.compl]
    refine le_antisymm (le_trans (Measure.restrict_apply_le _ _) ?_) bot_le
    refine le_trans (measure_mono ?_) hIT.le
    rintro X hX ⟨hXg, hXi, hXv⟩
    apply hX
    have hg := ((_root_.GlobalTheory.CompanionTheory.SW.GramLocal.gram_local F E σ hσ M J hJ 1 X 0).1.mp hXg)
    exact ⟨⟨hg.1, hXi⟩, fun v _ => ⟨hg.2 v.1, hXv v.1⟩⟩
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.SW.FactS.OpenFactor.prod_factor_open (ι := S) (G := fun v : S => HA (Fv F v.1) σ J)
    (W := fun v : S => Fin 1 → Fin M → Fv F v.1 ⊗[F] E)
    (actW (Ainf F) σ J) (fun v => actW (Fv F v.1) σ J)
    cAI (uI.2.2.2.2.2 1).2.1 (uI.2.2.2.2.2 1).2.2.1
    (fun v => cAV v.1) (fun v => ((uV v.1).2.2.2.2.2 1).2.1) (fun v => ((uV v.1).2.2.2.2.2 1).2.2.1)
    _ _ hU₀ hU
    (fun g x hx => free_act _ σ J g x hx) (fun v g x hx => free_act _ σ J g x hx)
    _ _ hZ₀ hZ
    (fun g x hx => ((uI.2.2.2.2.2 1).2.2.2 g x).trans hx)
    (fun v g x hx => (((uV v.1).2.2.2.2.2 1).2.2.2 g x).trans hx)
    LI.2.2.2.2 (fun v => (LV v.1).2.2.2.2)
    (minf (hermOf (Ainf F) σ 0 h₀)) (fun v => m v.1 (hermOf (Fv F v.1) σ 0 h₀))
    LI.1 (fun v => (LV v.1).1)
    LI.2.1 (fun v => (LV v.1).2.1) LI.2.2.1 (fun v => (LV v.1).2.2.1)
    LI.2.2.2.1 (fun v => (LV v.1).2.2.2.1) P hPc hPinv hPZ
  refine ⟨c, fun φinf φ hφinf hφ => ?_⟩
  have h := hc φinf (fun v => φ v.1) hφinf (fun v => hφ v.1)
  have hΦ : Measurable fun x : (Fin 1 → Fin M → Ainf F ⊗[F] E) ×
      ∀ v : S, Fin 1 → Fin M → Fv F v.1 ⊗[F] E => φinf x.1 * ∏ v : S, φ v.1 (x.2 v) :=
    (hφinf.comp measurable_fst).mul
      (Finset.measurable_prod _ fun v _ => (hφ v.1).comp ((measurable_pi_apply v).comp measurable_snd))
  rw [hPdef, lintegral_map hΦ hprm, Finset.prod_coe_sort S fun v => ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ 0 h₀))] at h
  rw [← h]
  unfold pureL
  rw [lintegral_indicator hintm]
  refine lintegral_congr fun X => ?_
  simp only [FactS.pr]
  rw [Finset.prod_coe_sort S fun v => φ v (projV v (projFin X))]

end GlobalTheory.CompanionTheory.WeilSiegel.FreeFact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFibreFreeExtension
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero

theorem stages_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → (∀ X, 0 ≤ φ X) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m 0) = ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (φ (chartS R σ J x a 0 Y)) ∂(m' 0) ∂(coordW R b lam 1 n) ∂(m₁ 0) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc n d b lam hlam m m₁ m' hm hm₁ hm' φ hφc hφs hφt hφ0
  have hLoc' := hLoc
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hLoc'
  obtain ⟨_, _, _, _, hsigc, -, -, hbor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hbor 1 (M + 2)
  haveI := hbor n M
  haveI := hbor 1 n
  haveI := hbor (n + 1) (M + 2)
  obtain ⟨_, _, _, _, hl1⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R 1
  obtain ⟨_, _, _, _, hl3⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨_, _, _, _, hlN⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R (n + 1)
  have hJ' : IsHermND σ (hypOne J) := isHermND_hypOne σ hJ
  obtain ⟨G₁, hG₁c, hG₁⟩ := hl1 (M + 2) (hypOne J) hJ'
  obtain ⟨G₃, hG₃c, hG₃⟩ := hl3 M J hJ
  obtain ⟨G, hGc, hG⟩ := hlN (M + 2) (hypOne J) hJ'
  obtain ⟨e, he, hep⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit F E σ hσ M J hJ R hLoc n d b lam hlam
  obtain ⟨hψc, hψs, hψt⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart F E σ hσ M J hJ R hLoc n φ hφc hφs hφt
  obtain ⟨-, hcellF, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props F E σ hσ M J hJ R hLoc n
  obtain ⟨-, hWh, hHh⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ R d b lam hlam
  haveI := hWh 1 (M + 2)
  haveI := hWh n M
  haveI := hWh 1 n
  haveI := hHh 1
  haveI := hHh n
  have hU1 : IsOpen {X : Fin 1 → Fin (M + 2) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ R hLoc 1 (M + 2)
  have hU3 : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ R hLoc n M
  have hWo : IsOpen {X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hσ R hLoc (n + 1) (M + 2)
  have li1 : ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, IsUnit (x 0 0) → LinearIndependent (R ⊗[F] E) x := by
    intro x hx
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hx.mul_left_eq_zero.1 h0
  let Q : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) → HermR R σ n :=
    fun p => qH R σ (sig_invol σ hσ) p.1 p.2.1 p.2.2
  have hQc : Continuous Q := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 (continuous_matrix fun i j => ?_)
    have ca : ∀ i, Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        p.2.2 0 i := fun i =>
      (continuous_apply i).comp ((continuous_apply 0).comp (continuous_snd.comp continuous_snd))
    have cs : ∀ i, Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        p.2.1 0 i := fun i =>
      (continuous_apply i).comp ((continuous_apply 0).comp (continuous_fst.comp continuous_snd))
    have ct : Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        (p.1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      (continuous_fst.subtype_val).matrix_elem 0 0
    exact ((((hsigc.comp (ca i)).mul (cs j)).add ((hsigc.comp (cs i)).mul (ca j))).sub
      (ct.mul ((hsigc.comp (ca i)).mul (ca j))))
  let ψ : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin n → Fin M → R ⊗[F] E) → ℝ := fun p => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)
  obtain ⟨hLc, hL⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.StageAbs.stages_abstract (Fin 1 → Fin (M + 2) → R ⊗[F] E) (Fin n → Fin M → R ⊗[F] E)
    (HermR R σ 1) (HermR R σ n) (Fin 1 → Fin n → R ⊗[F] E) (Fin 1 → Fin n → R ⊗[F] E)
    (Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) (Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (coordW R b lam 1 (M + 2)) (coordW R b lam n M) (coordHerm R σ b lam 1) (coordHerm R σ b lam n)
    (coordW R b lam 1 n) (coordW R b lam 1 n)
    (gramR R σ (hypOne J)) Subtype.val G₁ {X | LinearIndependent (R ⊗[F] E) X} m₁
    (gramR R σ J) Subtype.val G₃ {X | LinearIndependent (R ⊗[F] E) X} m' Q hU1 hU3 hG₁c hG₃c
    Subtype.val_injective Subtype.val_injective hG₁ hG₃ hm₁ hm' hQc ψ hψc hψs
    (fun p hp => ⟨li1 _ (hψt p hp).1, (hψt p hp).2⟩) (fun p => hφ0 _)
  have key : ∀ (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E)
      (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) →
      e (G (chartS R σ J x a s Y)) = (G₁ x, s, G₃ Y + Q (G₁ x, s, a)) := by
    intro x a s Y hx
    obtain ⟨g1, g2, g3⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS F E σ hσ M J hJ R n x a s Y hx
    obtain ⟨e1, e2, e3⟩ := he (G (chartS R σ J x a s Y))
    rw [← hG] at e1 e2 e3
    have ht : ((G₁ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = hR R σ (hypOne J) (x 0) (x 0) := by
      rw [← hG₁]; rfl
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact e1.trans (g1.trans ht.symm)
    · funext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact (e2 j).trans (g2 j)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      refine (e3 i j).trans ((g3 i j).trans ?_)
      show _ = ((G₃ Y : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j +
        (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
          ((G₁ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j))
      rw [← hG₃, ht]
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) :=
    ENNReal.measurable_ofReal.comp hφc.measurable
  have hφz : ∀ X, X ∉ freeCell (R ⊗[F] E) M n → φ X = 0 := fun X hX =>
    image_eq_zero_of_notMem_tsupport fun h => hX (hφt h)
  have hmF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 2)) (gramR R σ (hypOne J))
      Subtype.val {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam (n + 1)) Set.univ m := hm
  obtain ⟨hint, hcont⟩ := hmF.2.2 φ hφc hφs (hφt.trans fun X hX => hcellF X hX)
  have hD : ∀ B, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m B) = ENNReal.ofReal (∫ X, φ X ∂(m B)) := fun B =>
    (ofReal_integral_eq_lintegral_ofReal (hint B trivial) (Filter.Eventually.of_forall hφ0)).symm
  have hDc : Continuous fun z : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (e.symm z)) := by
    simp only [hD]
    exact ENNReal.continuous_ofReal.comp ((continuousOn_univ.1 hcont).comp e.symm.continuous)
  have hcmp : ∀ S : Set (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), IsCompact S →
      ∫⁻ z in S, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (e.symm z))
        ∂((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) =
      ∫⁻ z in S, (∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y))
          ∂(m' (z.2.2 - Q (z.1, z.2.1, a))) ∂(coordW R b lam 1 n) ∂(m₁ z.1))
        ∂((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
    intro S hS
    have hSm : MeasurableSet S := hS.measurableSet
    have hfm : Measurable (S.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hSm
    have h1 := hL _ hfm
    have h2 : ∀ L : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞,
        (fun z => S.indicator (fun _ => (1 : ℝ≥0∞)) z * L z) = S.indicator L := by
      intro L
      funext z
      by_cases hz : z ∈ S <;> simp [hz]
    rw [h2, lintegral_indicator hSm] at h1
    rw [← h1, ← hep.setLIntegral_comp_preimage_emb e.measurableEmbedding _ S]
    simp only [Homeomorph.symm_apply_apply]
    have hGm := e.continuous.measurable hSm
    rw [← GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage Subtype.val_injective hGc hG hWo subset_rfl hm _ hφm
      (fun X hX => ?_) _ hGm]
    · have hgm : Measurable ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) :=
        hφm.indicator (hGc.measurable hGm)
      have hg0 : ∀ X, X ∉ freeCell (R ⊗[F] E) M n →
          ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) X = 0 := by
        intro X hX
        exact Set.indicator_apply_eq_zero.2 fun _ => by rw [hφz X hX, ENNReal.ofReal_zero]
      have h3 : ∫⁻ v in {X | LinearIndependent (R ⊗[F] E) X},
            ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) v ∂(coordW R b lam (n + 1) (M + 2)) =
          ∫⁻ v, ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) v
            ∂(coordW R b lam (n + 1) (M + 2)) := by
        rw [← lintegral_indicator hWo.measurableSet]
        refine lintegral_congr fun v => ?_
        by_cases hv : v ∈ {X | LinearIndependent (R ⊗[F] E) X}
        · rw [Set.indicator_of_mem hv]
        · rw [Set.indicator_of_notMem hv]
          exact (hg0 v fun hc => hv (hcellF v hc)).symm
      rw [h3, _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStage.chartS_lintegral F E σ hσ M J hJ R hLoc n d b lam hlam _ hgm
        (fun X hX => hg0 X fun hc => hX hc.1)]
      refine lintegral_congr fun x => lintegral_congr fun a => lintegral_congr fun s =>
        lintegral_congr fun Y => ?_
      by_cases hx : IsUnit (x 0 0)
      · have hk := key x a s Y hx
        by_cases hz : (G₁ x, s, G₃ Y + Q (G₁ x, s, a)) ∈ S
        · have hm1 : chartS R σ J x a s Y ∈ G ⁻¹' (e ⁻¹' S) := by
            simpa only [Set.mem_preimage, hk] using hz
          rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hz]
          simp [ψ]
        · have hm1 : chartS R σ J x a s Y ∉ G ⁻¹' (e ⁻¹' S) := by
            simpa only [Set.mem_preimage, hk] using hz
          rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hz]
          simp
      · have hp : ψ (x, a, s, Y) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (hψt _ h).1
        have hp' : φ (chartS R σ J x a s Y) = 0 := hp
        rw [hp, ENNReal.ofReal_zero, zero_mul]
        exact Set.indicator_apply_eq_zero.2 fun _ => by rw [hp', ENNReal.ofReal_zero]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hX (hcellF X (hφt h)), ENNReal.ofReal_zero]
  have hfin := _root_.GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq _ ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n)))
    Set.univ isOpen_univ _ _ hDc.continuousOn hLc.continuousOn (fun S hS _ => hcmp S hS) 0 trivial
  have he0 : e 0 = 0 := by
    obtain ⟨e1, e2, e3⟩ := he 0
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact e1
    · funext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact e2 j
    · exact Subtype.ext (Matrix.ext fun i j => e3 i j)
  have hes : e.symm 0 = 0 := by rw [← he0, e.symm_apply_apply]
  have hQ0 : ∀ a, Q (0, 0, a) = 0 := by
    intro a
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show sigR R σ (a 0 i) * 0 + sigR R σ 0 * a 0 j - 0 * (sigR R σ (a 0 i) * a 0 j) = 0
    simp
  simp only [hes, Prod.fst_zero, Prod.snd_zero, hQ0, sub_zero] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_injective_of_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LInjective k := by
  first | exact @GlobalTheory.CompanionTheory.Multisegment.lInjective | exact GlobalTheory.CompanionTheory.Multisegment.lInjective | (intros; apply GlobalTheory.CompanionTheory.Multisegment.lInjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_sum_subquotient_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k → (∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) → ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1), IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.LangSumSub.main | exact GlobalTheory.CompanionTheory.LangSumSub.main | (intros; apply GlobalTheory.CompanionTheory.LangSumSub.main <;> assumption)
end

