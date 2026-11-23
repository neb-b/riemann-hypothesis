module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.FirstSubSecondLeviFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondLeviFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliClassificationOfAction
section
namespace GlobalTheory.CompanionTheory.CapClsA

open GlobalTheory.CompanionTheory.PairMult

theorem capOne_newton : CapOne := by
  intro n V _ _ E χ hE hg Y
  refine LinearMap.ext fun v => ?_
  have h := GlobalTheory.CapelliNewton.capelli_of_gelfand V n E χ hE
    (fun k x => by rw [etr_eq_gelA]; exact hg (k + 1) x) Y v
  simpa [Formalism.QuantumDeterminants.capP] using h

theorem dualCap_newton : DualCap := by
  intro n V _ _ E χ hE hg Y
  obtain ⟨hF, hq⟩ := GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  have h := capOne_newton n V (PositivityTheory.RgBcC.RealD.barF E) (fun a => -χ a) hF hg (-Y)
  have hq' := hq (-Y + ((n : ℂ) - 1) / 2)
  have harg : (n : ℂ) - 1 - (-Y + ((n : ℂ) - 1) / 2) = Y + ((n : ℂ) - 1) / 2 := by ring
  rw [harg] at hq'
  have hne : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]; simp
  have h2 : ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) =
      ((-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y) • (1 : Module.End ℂ V) := by
    rw [← hq', ← capelliPoly_neg]
    exact h
  calc Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
      = ((-1 : ℂ) ^ n) • (((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)) := by
        rw [smul_smul, hne, one_smul]
    _ = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
        rw [h2, smul_smul, ← mul_assoc, hne, one_mul]

theorem capCls_of_actUU : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := fun hAct =>
  GlobalTheory.CompanionTheory.CapClsProof.capCls_of hAct capOne_newton dualCap_newton

end GlobalTheory.CompanionTheory.CapClsA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompactStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_free_set_projects_compact : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ) (Q : Set (Fin (n + 1) → Fin (M + 1) → K)), IsCompact Q → (∀ Y ∈ Q, LinearIndependent K Y) → ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧ ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | exact GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem traceGram_isSymm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).IsSymm := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  ext k l
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have h := Algebra.trace_eq_of_algEquiv s (b l * σ (b k))
  have hs : s (b l * σ (b k)) = b k * σ (b l) := by
    show σ (b l * σ (b k)) = b k * σ (b l)
    rw [map_mul, hσ, mul_comm]
  rw [hs] at h
  exact h.symm ▸ rfl

theorem traceGram_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).det ≠ 0 := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  intro h0
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  set y : E := ∑ l, v l • b l with hy
  have hk : ∀ k, Algebra.trace F E (b k * σ y) = 0 := by
    intro k
    have := congrFun hmul k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hsm : σ (v l • b l) = v l • σ (b l) := by
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]
    rw [hsm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hz : ∀ x, Algebra.traceForm F E (σ y) x = 0 := by
    intro x
    rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Algebra.traceForm_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm (σ y), hk, smul_zero]
  have hσy : σ y = 0 := (traceForm_nondegenerate F E).1 _ hz
  have hy0 : y = 0 := by rw [← hσ y, hσy, map_zero]
  have := (Fintype.linearIndependent_iff.1 b.linearIndependent) v hy0
  exact funext this

theorem coordForm_isSymm_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b n
  constructor
  · refine Matrix.IsSymm.fromBlocks (Matrix.isSymm_one) (by simp) ?_
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    congr 1
    funext _
    exact traceGram_isSymm hCM b
  · unfold coordForm
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => traceGram_det_ne_zero hCM b

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneInvariantUnderMatrix
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.PiCovol

theorem isFD_pi {ι Y : Type} [Fintype ι] [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {G : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain G D ν) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : ι => G) (Set.univ.pi fun _ : ι => D)
      (Measure.pi fun _ : ι => ν) := by
  have hq (i : ι) := Measure.quasiMeasurePreserving_eval (fun _ : ι => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : ι => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

theorem map_eq_of_isFD {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure V) [P.IsAddHaarMeasure] (G : AddSubgroup V) [Countable G] {D : Set V}
    (hD : IsAddFundamentalDomain G D P) (h0 : P D ≠ 0) (h1 : P D ≠ ⊤) (e : V ≃ₜ+ V)
    (hG : ∀ v ∈ G, e.symm v ∈ G) (hG' : ∀ v ∈ G, e v ∈ G) : P.map e = P := by
  haveI : (P.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map P
  set c := Measure.addHaarScalarFactor (P.map e) P with hc
  have h : P.map e = c • P := Measure.isAddLeftInvariant_eq_smul _ P
  have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hpre : IsAddFundamentalDomain G (e ⁻¹' D) P := by
    refine hD.preimage_of_equiv (f := e) ⟨hm.measurable.aemeasurable, ?_⟩
      (e := fun b : G => (⟨e.symm b, hG _ b.2⟩ : G)) ⟨fun b b' h => ?_, fun a => ?_⟩ fun b v => ?_
    · rw [h]; exact Measure.smul_absolutelyContinuous
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact ⟨⟨e a, hG' _ a.2⟩, Subtype.ext (e.symm_apply_apply _)⟩
    · change e (e.symm b + v) = b + e v
      simp
  have e1 : P (e ⁻¹' D) = P D := hpre.measure_eq hD
  have e2 : P (e ⁻¹' D) = c * P D := by rw [← hm.map_apply, h]; rfl
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have : (c : ℝ≥0∞) * P D = 1 * P D := by rw [← e2, e1, one_mul]
    exact (ENNReal.mul_left_inj h0 h1).1 this
  have : c = 1 := by exact_mod_cast hc1
  rw [h, this, one_smul]

end GlobalTheory.CompanionTheory.SiegelND.PiCovol


open GlobalTheory.CompanionTheory.SiegelND.PiCovol in
theorem GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  intro F _ _ ν hν ι _ _ A hA
  obtain ⟨hH, D, hD, hD1⟩ := hν
  haveI := hH
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  set G₀ : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range with hG₀
  set G : AddSubgroup (ι → AF F) := AddSubgroup.pi Set.univ fun _ : ι => G₀ with hGdef
  have hmemG : ∀ v : ι → AF F, v ∈ G ↔ ∃ ξ : ι → F, v = fun i => algebraMap F (AF F) (ξ i) := by
    intro v
    constructor
    · intro hv
      choose ξ hξ using fun i => hv i trivial
      exact ⟨ξ, funext fun i => (hξ i).symm⟩
    · rintro ⟨ξ, rfl⟩ i _
      exact ⟨ξ i, rfl⟩
  haveI : Countable G := by
    have : Function.Surjective (fun ξ : ι → F => (⟨fun i => algebraMap F (AF F) (ξ i), (hmemG _).2 ⟨ξ, rfl⟩⟩ : G)) := by
      rintro ⟨v, hv⟩
      obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
      exact ⟨ξ, rfl⟩
    exact this.countable
  have hFD := isFD_pi (ι := ι) ν hD
  have hmass : (Measure.pi fun _ : ι => ν) (Set.univ.pi fun _ : ι => D) = 1 := by
    rw [Measure.pi_pi]; simp [hD1]
  have hrat : ∀ (B : Matrix ι ι F) (ξ : ι → F), (B.map (algebraMap F (AF F))).mulVec (fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) (B.mulVec ξ i) := by
    intro B ξ
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) B ξ i).symm
  have hu := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map (R := AF F) A hA
  have hinv : (A.map (algebraMap F (AF F)))⁻¹ = A⁻¹.map (algebraMap F (AF F)) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  have := map_eq_of_isFD (Measure.pi fun _ : ι => ν) G hFD (by rw [hmass]; simp) (by rw [hmass]; simp)
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE _ hu) ?_ ?_
  · exact this
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A⁻¹.mulVec ξ, ?_⟩
    change (A.map (algebraMap F (AF F)))⁻¹.mulVec _ = _
    rw [hinv, hrat]
  · intro v hv
    obtain ⟨ξ, rfl⟩ := (hmemG v).1 hv
    refine (hmemG _).2 ⟨A.mulVec ξ, ?_⟩
    exact hrat A ξ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInductionStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_segment_induction : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len) (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJac Δ'), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_step | exact GlobalTheory.CompanionTheory.SegFine.fineJac_step | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquiv
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem hCo_continuousAddEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ d b n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hfin : Module.finrank F E = 2 := hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  let h1 : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv hfin hδ hσδ n t5 t6).homeomorph _
  let h2 : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph _
  have h2a : ∀ y k, h2 y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  let G : ((Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) ≃ₜ (Idx n d → R) :=
    { toFun := fun x => Sum.elim x.1 (fun q => h2 (x.2 q.2) q.1)
      invFun := fun f => (fun i => f (Sum.inl i), fun p => h2.symm fun k => f (Sum.inr (k, p)))
      left_inv := by
        rintro ⟨x, y⟩
        refine Prod.ext rfl ?_
        funext p
        exact h2.symm_apply_apply (y p)
      right_inv := by
        intro f
        funext q
        rcases q with i | ⟨k, p⟩
        · rfl
        · simp
      continuous_toFun := by
        refine continuous_pi fun q => ?_
        rcases q with i | ⟨k, p⟩
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply k).comp
            (h2.continuous.comp ((continuous_apply p).comp continuous_snd))
      continuous_invFun := by
        refine Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_pi fun p => ?_)
        exact h2.symm.continuous.comp (continuous_pi fun k => continuous_apply _) }
  let H : HermR R σ n ≃ₜ (Idx n d → R) := h1.trans G
  have hH : ∀ S, H S = hCo R σ b S := by
    intro S
    funext q
    rcases q with i | ⟨k, p⟩ <;> rfl
  refine ⟨{ toEquiv := H.toEquiv
            map_add' := ?_
            continuous_toFun := H.continuous
            continuous_invFun := H.symm.continuous }, hH⟩
  intro S T
  show H (S + T) = H S + H T
  rw [hH, hH, hH]
  funext q
  rcases q with i | ⟨k, p⟩
  · simp [hCo, map_add (f := _), mul_add]
  · simp [hCo, map_add (f := _)]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterIntegralVanishes
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

open scoped Pointwise

theorem trace_single_mul_eq {R : Type} [CommRing R] {a b : ℕ} (j : Fin a) (i : Fin b) (w : R)
    (M : Matrix (Fin b) (Fin a) R) : Matrix.trace (Matrix.single j i w * M) = w * M i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem trA_algebraMap_half [Nontrivial (AF D.host.F)] (t : AF D.host.F) :
    trA (D := D) (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  show Algebra.trace (AF D.host.F) (AE D) (algebraMap (AF D.host.F) (AE D)
    (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t
  rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h2, two_nsmul, ← add_mul, ← map_add (f := _)]
  norm_num

theorem exists_chv_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (hdet : b₀.1.det ≠ 0) (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∃ x₀ : Mx D ρ p, chv ψ b₀ x₀ (rt ζ) ≠ 1 := by
  obtain ⟨-, -, -, t, ht⟩ := hψ
  have hB : b₀.1 * ζ ≠ 0 := by
    intro h0
    apply hζ
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hdet
    calc ζ = b₀.1⁻¹ * (b₀.1 * ζ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (b₀.1 * ζ) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB (Matrix.ext hc)
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = algebraMap (AF D.host.F) (AE D)
      (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) * incA D ((b₀.1 * ζ) i j)⁻¹ := ⟨_, rfl⟩
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have key : Matrix.trace (pr b₀ (adj (Matrix.single j i c)) (rt ζ)) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) := by
    show Matrix.trace (adj (adj (Matrix.single j i c)) * (b₀.1.map (incA D) * rt ζ)) = _
    rw [adj_adj, show b₀.1.map (incA D) * rt ζ = rat (b₀.1 * ζ) from (rat_mul _ _).symm,
      trace_single_mul_eq]
    show c * incA D ((b₀.1 * ζ) i j) = _
    rw [hc, mul_assoc, ← map_mul, inv_mul_cancel₀ hij, map_one, mul_one]
  show ψ (trA (Matrix.trace (pr b₀ _ (rt ζ)))) ≠ 1
  haveI : Nontrivial (AF D.host.F) :=
    nontrivial_of_ne t 0 (fun h => ht (by rw [h, AddChar.map_zero_eq_one]))
  rw [key, trA_algebraMap_half]
  exact ht

theorem integral_chv_rt_eq_zero {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (hdet : b₀.1.det ≠ 0)
    (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_chv_ne_one ψ hψ b₀ hdet ζ hζ
  obtain ⟨hadd, -, -, -, hrat, -⟩ := _root_.GlobalTheory.CompanionTheory.FJE.chv_facts ψ hψ b₀
  have hper : ∀ γ ∈ ratMx D ρ p, ∀ a, chv ψ b₀ (γ + a) (rt ζ) = chv ψ b₀ a (rt ζ) := by
    intro γ hγ a
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [hadd, show rat g = rt g from rfl, hrat, one_mul]
  have h := covolOne_integral_add m.hμ (fun x => chv ψ b₀ x (rt ζ)) hper x₀
  simp only [hadd] at h
  rw [MeasureTheory.integral_mul_const] at h
  have h2 : (∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ) * (chv ψ b₀ x₀ (rt ζ) - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hx₀)

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesNaturalInRing
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem repr_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem trace_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      f (Algebra.trace R (R ⊗[F] E) x) := by
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : Algebra.TensorProduct.map f (AlgHom.id F E) (x * Algebra.TensorProduct.basis R b k) =
      Algebra.TensorProduct.map f (AlgHom.id F E) x * Algebra.TensorProduct.basis R' b k := by
    rw [_root_.map_mul]
    simp [Algebra.TensorProduct.basis_apply]
  rw [← repr_map_tensor f b, h]

theorem hCo_hermMap : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d), hCo R' σ b (hermMap f σ S) i = f (hCo R σ b S i) := by
  intro F E _ _ _ σ R R' _ _ _ _ f d b n S i
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, hermMap, Matrix.map_apply, map_mul, AlgHom.commutes, trace_map_tensor f b]
  · simp only [hCo, Sum.elim_inr, hermMap, Matrix.map_apply, repr_map_tensor f b]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

