module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.EvalVSingleVSame
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evalV_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evalV F v a = a v := rfl

open Classical in
theorem evalV_singleV_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_same _ _ _

open Classical in
theorem evalV_singleV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v) : evalV F w (singleV F v y) = 0 := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ _ h

theorem addChar_sum {A M ι : Type} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem AF_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

theorem psi_split (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ x : AF F,
      (∀ v, v ∉ S → evalV F v (sndA F x) ∈ v.adicCompletionIntegers F) →
      ψ x = psiInf F ψ (fstA F x) * ∏ v ∈ S, psiV F ψ v (evalV F v (sndA F x)) := by
  classical
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat ξ)
  refine ⟨hfin.toFinset, fun S hS x hx => ?_⟩
  set xf : Af F := sndA F x with hxf
  set r : Af F := xf - ∑ v ∈ S, singleV F v (evalV F v xf) with hr
  have hdec : x = pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r := by
    refine AF_ext ?_ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), map_sum, fstA_pairA, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, add_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), map_sum, sndA_pairA, sndA_pairA]
        simp only [sndA_pairA, hr, hxf]
        abel
  have hrv : ∀ v, evalV F v r = if v ∈ S then 0 else evalV F v xf := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr, map_sub, map_sum]
    by_cases hv : v ∈ S
    · rw [if_pos hv, Finset.sum_eq_single v]
      · rw [evalV_singleV_same, sub_self]
      · intro w _ hw
        exact evalV_singleV_ne (Ne.symm hw) _
      · intro h; exact absurd hv h
    · rw [if_neg hv, Finset.sum_eq_zero, sub_zero]
      intro w hw
      exact evalV_singleV_ne (by rintro rfl; exact hv hw) _
  have hmem : algebraMap F (Af F) ξ * r ∈ GroundTheory.Global.finiteInvDifferent F := by
    intro v
    have e1 : (algebraMap F (Af F) ξ * r) v = algebraMap F (Fv F v) ξ * evalV F v r := rfl
    rw [e1, hrv v]
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_zero]
      exact zero_mem _
    · rw [if_neg hv]
      have hξv : algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F := by
        by_contra h
        exact hv (hS (hfin.mem_toFinset.2 h))
      exact GroundTheory.Global.mem_localInvDifferent_of_mem (mul_mem hξv (hx v hv))
  have hr1 : ψ (pairA F 0 r) = 1 := by
    rw [hξ]
    have e2 : algebraMap F (AF F) ξ * pairA F 0 r = pairA F 0 (algebraMap F (Af F) ξ * r) := by
      refine AF_ext ?_ ?_
      · rw [map_mul, fstA_pairA, fstA_pairA, mul_zero]
      · rw [map_mul, sndA_pairA, sndA_pairA, AlgHom.commutes]
    rw [e2]
    have hm2 : pairA F 0 (algebraMap F (Af F) ξ * r) ∈ GroundTheory.Global.invDifferentAdeles F :=
      GroundTheory.Global.mem_invDifferentAdeles.mpr hmem
    rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hm2]
    simp [pairA]
  have h1 : ψ x = ψ (pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r) :=
    congrArg ψ hdec
  rw [h1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, addChar_sum, hr1, mul_one]
  rfl

end PositivityTheory.SiegelWeilFormula.GFac

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.SigmaFiniteOfMp
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac.HS

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH hermMap)
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hermVec_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d) :
    hermVec R' σ b n (hermMap f σ S) i = f (hermVec R σ b n S i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  cases i with
  | inl i =>
    simp only [hermVec, toVec, GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord, Sum.elim_inl, hermMap, Matrix.map_apply]
    rw [GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map f b, map_mul, AlgHom.commutes]
    congr 1
    have h := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map (AlgHom.id F R) b ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)
    rw [Algebra.TensorProduct.map_id, AlgHom.id_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes]
    rfl
  | inr q =>
    simp only [hermVec, toVec, GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord, Sum.elim_inr, hermMap, Matrix.map_apply]
    exact GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.repr_map f b _ q.2

def hInfR (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Ainf F) σ n := hermInf σ S

def hFinR (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Af F) σ n := hermFin σ S

theorem sigmaFinite_of_mp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) {μ : Measure X}
    {ν : Measure Y} [SigmaFinite ν] (h : MeasurePreserving e μ ν) : SigmaFinite μ := by
  have h2 : μ = ν.map e.symm := by
    rw [← h.map_eq, MeasurableEquiv.map_symm_map]
  rw [h2]
  exact e.symm.measurableEmbedding.sigmaFinite_map


omit [NumberField E] in
theorem coordHerm_congr {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    {m₁ m₂ : MeasurableSpace R} (h : m₁ = m₂) (l₁ : @Measure R m₁) (l₂ : @Measure R m₂) (hl : ∀ s, l₁ s = l₂ s)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    @coordHerm F E _ _ _ R _ _ _ m₁ σ d b l₁ n = @coordHerm F E _ _ _ R _ _ _ m₂ σ d b l₂ n := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

section Meas
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

theorem db_split' (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun S : HermR (AF F) σ n => (hInfR σ S, hFinR σ S)) db
      ((coordHerm (Ainf F) σ b l n).prod (coordHerm (Af F) σ b lf n)) := by
  obtain ⟨⟨hALC, hASC, hAT2⟩, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp

  let e : HermR (AF F) σ n ≃ₜ (Idx n d → AF F) := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  have hpair : ∀ S T : HermR (AF F) σ n, chiG (ξ • formB σ b n) (e S) (e T) = ψ (pairHerm (AF F) σ n S T) := by
    intro S T
    rw [he, he, pair_eq (AF F) hinv hCM.2.2.1 hδ hσδ b n S T, hξ, chiG]
    congr 2
    have h2 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
        algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
      ext p q
      exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
    rw [h2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hsd : db.map e = adeleMeasurePi F :=
    selfDual_eq _ hs hdet _ (selfDual_transport e (fun S T => by rw [he, he, he, hermVec_add]) _ _ hpair db hdb)
  have hEq := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.adele_eq l hH D hD hD1 lf hlf h1
  haveI : SigmaFinite l := Measure.IsAddHaarMeasure.sigmaFinite l
  haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
  have hΘ := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    (Idx n d) (fun _ => l) (fun _ => lf)
  have hA' : MeasurePreserving e.toMeasurableEquiv db (Measure.pi fun _ : Idx n d => l.prod lf) := by
    refine ⟨e.toMeasurableEquiv.measurable, ?_⟩
    change db.map e = _
    rw [hsd, adeleMeasurePi, hEq]
  let eI := ((hermVec_isHomeomorph hCM (Ainf F) b n).homeomorph _).toMeasurableEquiv
  let eF := ((hermVec_isHomeomorph hCM (Af F) b n).homeomorph _).toMeasurableEquiv
  have hI : MeasurePreserving eI (coordHerm (Ainf F) σ b l n) (Measure.pi fun _ : Idx n d => l) :=
    mp_hermVec hCM (Ainf F) b n l
  have hF : MeasurePreserving eF (coordHerm (Af F) σ b lf n) (Measure.pi fun _ : Idx n d => lf) :=
    mp_hermVec hCM (Af F) b n lf
  haveI : SigmaFinite (coordHerm (Ainf F) σ b l n) := sigmaFinite_of_mp eI hI
  haveI : SigmaFinite (coordHerm (Af F) σ b lf n) := sigmaFinite_of_mp eF hF
  let eP := eI.prodCongr eF
  have hP : MeasurePreserving eP ((coordHerm (Ainf F) σ b l n).prod (coordHerm (Af F) σ b lf n))
      ((Measure.pi fun _ : Idx n d => l).prod (Measure.pi fun _ : Idx n d => lf)) :=
    hI.prod hF
  refine (hP.comp_left_iff).1 ?_
  have hc := hΘ.comp hA'
  convert hc using 1
  funext S
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show hermVec (Ainf F) σ b n (hermMap (fstA F) σ S) i = (hermVec (AF F) σ b n S i).1
    rw [hermVec_map]
    rfl
  · show hermVec (Af F) σ b n (hermMap (sndA F) σ S) i = (hermVec (AF F) σ b n S i).2
    rw [hermVec_map]
    rfl

end Meas

theorem db_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (hinf : IsStdInf laminf)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun S : HermR (AF F) σ n => (hInfR σ S, hFinR σ S)) db
      ((coordHerm (Ainf F) σ b laminf n).prod (coordHerm (Af F) σ b lf n)) := by
  have hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨l, hl, hH, D, hD, hD1⟩ :=
    @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm
  have h := db_split' σ hCM ψ hψ n db hdb b l hH D hD hD1 lf hlf h1
  rw [coordHerm_congr hm l laminf hl σ b n] at h
  exact h

end PositivityTheory.SiegelWeilFormula.GFac.HS

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TendstoUH
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_UH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (bs : Module.Basis (Fin d) F E) (n : ℕ)
    (ν : Measure (HermR (AF F) σ n)) (f : HermR (AF F) σ n → ℂ) (hf : Integrable f ν) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ∫ b in UH σ bs n S, f b ∂ν) atTop (nhds (∫ b, f b ∂ν)) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have he : ∀ S, ∫ b in UH σ bs n S, f b ∂ν = ∫ b, (UH σ bs n S).indicator f b ∂ν := fun S =>
    (integral_indicator (measurableSet_UH σ hCM bs n S)).symm
  simp_rw [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall fun S => hf.aestronglyMeasurable.indicator (measurableSet_UH σ hCM bs n S)
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_
    by_cases h : y ∈ UH σ bs n S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ bs v n}.Finite :=
      Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_latH σ bs y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : y ∈ UH σ bs n S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [Set.indicator_of_mem hmem]

end PositivityTheory.SiegelWeilFormula.GFac

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TrPairGramFE
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Tens

variable {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

abbrev fE (f : R →ₐ[F] R') : R ⊗[F] E →ₐ[F] R' ⊗[F] E := Algebra.TensorProduct.map f (AlgHom.id F E)

theorem fE_comp (f : R →ₐ[F] R') (g : R' →ₐ[F] R'') (x : R ⊗[F] E) :
    fE (E := E) g (fE f x) = fE (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [fE]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fE_inclR (f : R →ₐ[F] R') (e : E) : fE f (inclR R e) = inclR R' e := by
  simp [fE, inclR]

theorem trace_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (x : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) x) = Algebra.trace R' (R' ⊗[F] E) (fE f x) := by
  have h1 := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map (AlgHom.id F R) bs x
  have h2 := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map f bs x
  have h3 : Algebra.TensorProduct.map (AlgHom.id F R) (AlgHom.id F E) x = x := by
    rw [Algebra.TensorProduct.map_id]; rfl
  rw [h3] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fE, h2, h1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, AlgHom.commutes]
  rfl

theorem sigR_fE (σ : E →ₐ[F] E) (f : R →ₐ[F] R') (x : R ⊗[F] E) : sigR R' σ (fE f x) = fE f (sigR R σ x) :=
  GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_map f σ x

theorem trPair_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) :
    f (trPair R A B) = trPair R' (A.map (fE f)) (B.map (fE f)) := by
  simp only [trPair, map_mul, AlgHom.commutes]
  rw [trace_fE bs]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, Matrix.map_apply]

theorem gramR_fE (σ : E →ₐ[F] E) (f : R →ₐ[F] R') {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → R ⊗[F] E) :
    (gramR R σ J Y).map (fE f) = gramR R' σ J (fun a i => fE f (Y a i)) := by
  ext a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_fE, fE_inclR]

theorem trPair_gram_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (f : R →ₐ[F] R') {M m : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) (Y : Fin m → Fin M → R ⊗[F] E) :
    f (trPair R B (gramR R σ J Y)) = trPair R' (B.map (fE f)) (gramR R' σ J (fun a i => fE f (Y a i))) := by
  rw [trPair_fE bs, gramR_fE]

theorem trPair_T_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') {m : ℕ}
    (T : Matrix (Fin m) (Fin m) E) (B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) :
    f (trPair R (T.map (inclR R)) B) = trPair R' (T.map (inclR R')) (B.map (fE f)) := by
  rw [trPair_fE bs]
  congr 1
  ext a c
  simp [Matrix.map_apply, fE_inclR]

end Tens

theorem hermInf_val (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = matInf (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
  rfl

theorem hermV_val (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermV σ v (hermFin σ b) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      matV v (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := by
  ext i j
  simp only [hermV, hermFin, GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap, matV, Matrix.map_apply]
  exact fE_comp (sndA F) (evalV F v) _

theorem hermV_val' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermV σ v (hermFin σ b) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (fE ((evalV F v).comp (sndA F))) := by
  rw [hermV_val]; rfl

theorem projV_projFin {M n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) :
    projV v (projFin X) = fun a i => fE ((evalV F v).comp (sndA F)) (X a i) := by
  funext a i
  exact fE_comp (sndA F) (evalV F v) _

theorem projInf_eq {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projInf X = fun a i => fE (fstA F) (X a i) := rfl

end PositivityTheory.SiegelWeilFormula.GFac

end
end

