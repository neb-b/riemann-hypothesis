module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0053
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneEulerProductMeasureExists
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open GlobalTheory.CompanionTheory.SiegelND.DxN GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler
open scoped TensorProduct ENNReal NNReal

theorem cvN_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {d M n : ℕ} (b : Module.Basis (Fin d) F E) (r : Fin n → Fin M → E) (p : Fin n × (Fin M × Fin d)) :
    cvN R b (ratTup R r : Fin n → Fin M → R ⊗[F] E) p = algebraMap F R (b.repr (r p.1 p.2.1) p.2.2) := by
  simp only [cvN, cv, ratTup, inclR]
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (r p.1 p.2.1)) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, one_smul]

section Meas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_covolOne (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (n : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) (e : (Fin 1 → Fin n → AF F ⊗[F] E) ≃ₜ (Fin 1 × (Fin n × Fin d) → AF F)),
      (∀ X, e X = cvN (AF F) b X) ∧ BorelSpace (Fin 1 → Fin n → AF F ⊗[F] E) ∧
      dA.map e = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F ∧ IsCovolOne dA := by
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM 1 n b
  obtain ⟨t1, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI : IsTopologicalAddGroup (Fin 1 → Fin n → AF F ⊗[F] E) := inferInstance
  let eA := e.toMeasurableEquiv
  let μ := GroundTheory.Automorphic.GJMatrix.adeleMeasurePi (K := F) (ι := Fin 1 × (Fin n × Fin d))
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    rw [he, he, he]
    funext p
    simp [cvN, cv]
  let φ : (Fin 1 → Fin n → AF F ⊗[F] E) ≃+ (Fin 1 × (Fin n × Fin d) → AF F) :=
    { e.toEquiv with map_add' := hadd }
  have hr : ∀ (r : Fin 1 → Fin n → E) p,
      e (ratTup (AF F) r) p = algebraMap F (AF F) (b.repr (r p.1 p.2.1) p.2.2) := by
    intro r p
    rw [he, cvN_ratTup]
  refine ⟨μ.map eA.symm, e, he, hB, ?_, ?_, e ⁻¹' Set.univ.pi fun _ => fundamentalSet F, ?_, ?_⟩
  · exact MeasurableEquiv.map_map_symm eA
  · exact φ.symm.isAddHaarMeasure_map μ e.symm.continuous e.continuous
  · refine IsAddFundamentalDomain.mk' (eA.measurable (MeasurableSet.univ_pi fun _ =>
      measurableSet_fundamentalSet F)).nullMeasurableSet fun x => ?_
    choose k hk huniq using fun p => existsUnique_sub_mem_fundamentalSet F (e x p)
    let r : Fin 1 → Fin n → E := fun a i => ∑ j, (-k (a, (i, j))) • b j
    have hrk : ∀ p, b.repr (r p.1 p.2.1) p.2.2 = -k p := by
      intro p
      simp only [r]
      rw [Module.Basis.repr_sum_self]
    refine ⟨⟨ratTup (AF F) r, r, rfl⟩, ?_, ?_⟩
    · change e (ratTup (AF F) r + x) ∈ Set.univ.pi fun _ => fundamentalSet F
      rw [hadd]
      intro p _
      have := hk p
      rw [Pi.add_apply, hr, hrk, map_neg, neg_add_eq_sub]
      exact this
    · rintro ⟨_, r', rfl⟩ h
      change e (ratTup (AF F) r' + x) ∈ Set.univ.pi fun _ => fundamentalSet F at h
      rw [hadd] at h
      refine Subtype.ext (e.injective (funext fun p => ?_))
      change e (ratTup (AF F) r') p = e (ratTup (AF F) r) p
      have hp := h p (Set.mem_univ p)
      rw [Pi.add_apply, hr] at hp
      have hk' : -(b.repr (r' p.1 p.2.1) p.2.2) = k p := huniq p _ (by
        change e x p - algebraMap F (AF F) (-(b.repr (r' p.1 p.2.1) p.2.2)) ∈ fundamentalSet F
        rw [map_neg, sub_neg_eq_add, add_comm]
        exact hp)
      rw [hr, hr, hrk, ← hk', neg_neg]
  · rw [MeasurableEquiv.map_apply]
    have : eA.symm ⁻¹' (e ⁻¹' Set.univ.pi fun _ => fundamentalSet F) = Set.univ.pi fun _ => fundamentalSet F := by
      ext u
      simp [eA]
    rw [this]
    change Measure.pi (fun _ => adeleMeasure F) _ = 1
    rw [Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

theorem split_coord' (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : dx.map e = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F)
    (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M)) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hEq := adele_eq l hH D hD hD1 lf hlf h1
  obtain ⟨i1, i3⟩ := coordMapN σ hCM (Ainf F) b l hH n M
  obtain ⟨f1, f3⟩ := coordMapN σ hCM (Af F) b lf hlf n M
  haveI hBi := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.2.1 n M
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  haveI : SigmaFinite l := by
    exact Measure.IsAddHaarMeasure.sigmaFinite l
  haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
  let eI := (i1.homeomorph).toMeasurableEquiv
  let eF := (f1.homeomorph).toMeasurableEquiv
  let eA := e.toMeasurableEquiv
  have hI : MeasurePreserving eI (coordW (Ainf F) b l n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l) :=
    ⟨eI.measurable, i3⟩
  have hF : MeasurePreserving eF (coordW (Af F) b lf n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf) :=
    ⟨eF.measurable, f3⟩
  have hΘ := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    (Fin n × (Fin M × Fin d)) (fun _ => l) (fun _ => lf)
  have hA' : MeasurePreserving eA dx (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf) := by
    have e1 : GroundTheory.Automorphic.GJMatrix.adeleMeasurePi (K := F) (ι := Fin n × (Fin M × Fin d)) =
        Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf := by
      rw [GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, hEq]
    exact ⟨eA.measurable, hdxc.trans e1⟩
  let eP := eI.prodCongr eF
  haveI : SFinite (coordW (Af F) b lf n M) := sfinite_coordW σ hCM b lf hlf n M
  haveI : SFinite (coordW (Ainf F) b l n M) := by
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Ainf F) b) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.1 d b
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Ainf F) hK l
    unfold coordW
    infer_instance
  have hP : MeasurePreserving eP ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M))
      ((Measure.pi fun _ : Fin n × (Fin M × Fin d) => l).prod (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf)) :=
    hI.prod hF
  refine (hP.comp_left_iff).1 ?_
  have hc := hΘ.comp hA'
  convert hc using 1
  funext X
  have hX : ∀ p, e X p = cvN (AF F) b X p := fun p => by rw [he]
  refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
  · change cvN (Ainf F) b (projInf X) p = (e X p).1
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (fstA F) (X p.1 p.2.1) p.2.2
  · change cvN (Af F) b (projFin X) p = (e X p).2
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (sndA F) (X p.1 p.2.1) p.2.2

end Meas

section Euler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem split_coord (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : @Measure.map _ _ _ (@MeasurableSpace.pi _ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F) e dx =
      @GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F _ _ (Fin n × (Fin M × Fin d)) _)
    (laminf : Measure (Ainf F)) (hinf : IsStdInf laminf)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b laminf n M).prod (coordW (Af F) b lf n M)) := by
  have hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨l, hl, hH, D, hD, hD1⟩ := @std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm
  have h := split_coord' σ hCM M n dx b e he hB hdxc l hH D hD hD1 lf hlf h1
  rw [coordW_congr hm l laminf hl b n M] at h
  exact h

theorem euler_coord (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : @Measure.map _ _ _ (@MeasurableSpace.pi _ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F) e dx =
      @GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F _ _ (Fin n × (Fin M × Fin d)) _)
    (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v)) :
    IsEulerProd b dx 1 (coordW (Ainf F) b laminf n M) (fun v => coordW (Fv F v) b (lam v) n M) := by
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  have hmass := fun v => coordW_latV σ hCM b lam hlam n M v
  refine ⟨fun v => ?_, ?_, ∅, fun S _ φinf φ hφi hφ => ?_⟩
  · simp only [hmass v]; exact ENNReal.one_lt_top
  · simp only [hmass]; simp [summable_zero]
  · have hT := split_coord σ hCM M n dx b e he hB hdxc laminf hinf lf hlf h1
    obtain ⟨hg, hI⟩ := lint_fin σ hCM b lam hlam lf hlf h1 n M S φ hφ
    haveI := sfinite_coordW σ hCM b lf hlf n M
    set g := ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      fun Y => ∏ v ∈ S, φ v (projV v Y) with hgdef
    have e' : ∀ X, pureL b S φinf φ X =
        (fun p : _ × _ => φinf p.1 * g p.2) (projInf X, projFin X) := by
      intro X
      by_cases hX : X ∈ intOff b S
      · have hX' : projFin X ∈ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_mem hX, hgdef, Set.indicator_of_mem hX']
      · have hX' : projFin X ∉ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_notMem hX, hgdef, Set.indicator_of_notMem hX', mul_zero]
    have hm : Measurable (fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) => φinf p.1 * g p.2) :=
      (hφi.comp measurable_fst).mul (hg.comp measurable_snd)
    rw [lintegral_congr e', hT.lintegral_comp hm, lintegral_prod_mul hφi.aemeasurable hg.aemeasurable, hI]
    simp [hmass]

end Euler

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA

end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_dA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA ∧ IsEulerProd b dA 1 (coordW (Ainf F) b laminf 1 n) (fun v => coordW (Fv F v) b (lam v) 1 n) := by
  intro F E _ _ _ _ _ σ hCM n d b laminf lam hinf hlam
  obtain ⟨dA, e, he, hB, hm, hc⟩ := GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_covolOne σ hCM n b
  exact ⟨dA, hc, GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.euler_coord σ hCM n 1 dA b e he hB hm laminf lam hinf hlam⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal

open Set

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}

theorem fib_lt_top (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U) (b : X)
    {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hI := (h.2.2 g g.continuous hgc hgs).1 b (mem_univ b)
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂(fib b) := (lintegral_indicator_one hK.measurableSet).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂(fib b) := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [indicator_of_mem hv, hg1 hv]
        · simp [indicator_of_notMem hv]
    _ < ⊤ := hI.lintegral_lt_top

theorem sigmaFinite_fib (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) : SigmaFinite (fib b) := by
  have hc : fib b Uᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.1 b)
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hKc, hKU⟩ := hσ
  have hsub : ∀ n, K n ⊆ U := fun n => hKU ▸ subset_iUnion K n
  refine Measure.FiniteSpanningSetsIn.sigmaFinite
    (μ := fib b) (C := univ)
    { set := fun n => K n ∪ Uᶜ, set_mem := fun _ => mem_univ _, finite := fun n => ?_, spanning := ?_ }
  · exact (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨fib_lt_top h hU b (hKc n) (hsub n), by simp [hc]⟩)
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · rw [← hKU] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨n, Or.inl hn⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hx⟩

end Gen

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gramR_ratTup_eq (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem ratTup_free (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (X : Fin 1 → Fin M → E)
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  have h0 : X 0 ≠ 0 := hX.ne_zero 0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
  have hu : IsUnit (inclR (F := F) R (X 0 i)) := (isUnit_iff_ne_zero.2 hi).map _
  refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ratTup] at h1
  exact (hu.mul_left_eq_zero).1 h1

end Rat

section Arch

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem arch_lb (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E))
    (ν : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (x : Fin a → Fin M → Ainf F ⊗[F] E) (S0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a)
    (hx : LinearIndependent (Ainf F ⊗[F] E) x)
    (hxS : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J x = (S0 : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)))
    (W : Set (Fin a → Fin M → Ainf F ⊗[F] E)) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 S0, ∀ S ⊆ N, MeasurableSet S →
      c * ν S ≤ μ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W) := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩ :=
    GlobalTheory.ArchGramFibre.exists_submersion_coords F E σ hCM M a J hJ
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨rfl⟩
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hW' : IsOpen (eV.symm ⁻¹' W) := hW.preimage eV.symm.continuous
  have hx0W : eV x ∈ eV.symm ⁻¹' W := by
    show eV.symm (eV x) ∈ W
    rw [Homeomorph.symm_apply_apply]
    exact hxW
  obtain ⟨c, hc0, hct, N', hN', hlb'⟩ :=
    PI.VolStabS.submLB_holds n m _ _ hμ' hν' f' hf' (eV x) (hsurj x hx) _ hW' hx0W
  have hfx0 : f' (eV x) = eH S0 := by
    have h1 : eH.symm (f' (eV x)) = S0 := Subtype.ext ((hG x).trans hxS)
    rw [← h1, Homeomorph.apply_symm_apply]
  have hN : eH ⁻¹' N' ∈ 𝓝 S0 := eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')
  refine ⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩
  have hS'm : MeasurableSet (eH.symm ⁻¹' S) := eH.symm.continuous.measurable hSm
  have hS'N : eH.symm ⁻¹' S ⊆ N' := fun z hz => by
    have := hSN hz
    rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
  have h := hlb' _ hS'N hS'm
  rw [show (ν.map eH) = ν.map eH.toMeasurableEquiv from rfl,
    show (μ.map eV) = μ.map eV.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at h
  have e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S := by
    ext z
    simp
  have e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W := by
    ext X
    simp only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1, hG X⟩, h2⟩
    · rintro ⟨⟨s, hs, hsX⟩, h2⟩
      refine ⟨?_, h2⟩
      have : s = eH.symm (f' (eV X)) := Subtype.ext (hsX.trans (hG X).symm)
      rw [← this]
      exact hs
  rw [e1, e2] at h
  exact h

end Arch

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigmaFinite_free (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (hm : IsGramFibFree R σ J n μ ν m)
    (S : HermR R σ n) : SigmaFinite (m S) := by
  have hO := GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM R hR n M
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  exact sigmaFinite_fib hm hO S

theorem free_fibre_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → SigmaFinite (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) ∧ (∀ v, SigmaFinite (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) ∧ ((framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0 ∧ ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ h₀ d b laminf lam hinf hlam minf hminf m hm
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine ⟨sigmaFinite_free σ hCM J (Ainf F) hLi 1 _ _ minf hminf _,
    fun v => sigmaFinite_free σ hCM J (Fv F v) (hLv v) 1 _ _ (m v) (hm v) _, ?_⟩
  rintro ⟨X₀, hX₀, hg⟩
  have hgram : ∀ (R : Type) [CommRing R] [Algebra F R],
      gramR R σ J (ratTup (F := F) R X₀) = (hermOf R σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := fun R _ _ => by
    rw [gramR_ratTup_eq, hg]
    rfl
  constructor
  · obtain ⟨h1, h2, h3, h4, hA, hRed, hU, -⟩ := hLi
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    haveI := hA
    haveI := hRed
    haveI : FiniteDimensional F E := Module.Finite.of_basis b
    have hUo : IsOpen {r : Ainf F | IsUnit r} := by
      have := hU.isOpen_range
      convert this using 1
      ext r
      simp [IsUnit]
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1
    haveI := hH.2.1 1 M
    let ν' : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HermR (Ainf F) σ 1) := coordHerm (Ainf F) σ b laminf 1
    haveI : ν'.IsAddHaarMeasure := hH.2.2 1
    exact (GlobalTheory.LocalFibreNonzero.fib_tens σ (PI.VolStabS.sigma_invol σ hCM.2.2.2) J hJ.1 1 (Ainf F)
      hUo (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.lip_of_artinian_reduced (Ainf F)) _ ν' minf hminf
      (ratTup (F := F) (Ainf F) X₀) _ (ratTup_free (Ainf F) X₀ hX₀)
      (fun W hW hxW => arch_lb F E σ hCM M 1 J hJ _ _ (hH.2.1 1 M) (hH.2.2 1) _ _
        (ratTup_free (Ainf F) X₀ hX₀) (hgram (Ainf F)) W hW hxW)).1
  · intro v
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    haveI := h1
    haveI := h2
    haveI := h3
    haveI := h4
    have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact (GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite F E σ hCM M J hJ v 1 _ _ (hH.2.1 1 M) (hH.2.2 1)
      (m v) (hm v) (ratTup (F := F) (Fv F v) X₀) _ (ratTup_free (Fv F v) X₀ hX₀) (hgram (Fv F v))).1

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSum
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem integral_fold {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ) (hP : Integrable P m.μ) :
    ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D ρ p
  have : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  have : Countable (ratMx D ρ p) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hμ := m.hμ
  have := hμ.1
  let e : Matrix (Fin ρ) (Fin p) D.host.E ≃ ratMx D ρ p :=
    Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
      ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨ξ, hξ⟩ := mem_ratMx.1 g.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩
  have h1 : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) =
      ∑' g : ratMx D ρ p, P (g +ᵥ y) := fun y => e.tsum_eq fun g => P (g +ᵥ y)
  simp only [h1]
  rw [hμ.2.1.integral_eq_tsum'' P hP]
  refine (integral_tsum (ι := ratMx D ρ p) (f := fun g y => P (g +ᵥ y)) (fun g => ?_) ?_).symm
  · exact ((hP.comp_add_left (g : Mx D ρ p)).aestronglyMeasurable).restrict
  · rw [← hμ.2.1.lintegral_eq_tsum'' fun x => ‖P x‖ₑ]
    exact hP.2.ne

end GlobalTheory.CompanionTheory.FJE
end
end

