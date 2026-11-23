module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import GroundTheory.AutomorphicForms.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorCosetScaledIntegralEqRestrictedProduct
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.EvAdm

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def cosetBoxV (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : Set (κ → Fv F v) :=
  {x | ∀ i, (algebraMap F (v.adicCompletion F) a)⁻¹ * (x i - (r i) v) ∈ v.adicCompletionIntegers F}

theorem indicator_cosetBoxV_mem_SB [Finite κ] {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator (cosetBoxV a r v) (1 : (κ → Fv F v) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  classical
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).2 ha
  let P : Set (κ → Fv F v) := Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))
  let f : (κ → Fv F v) → (κ → Fv F v) := fun x i => (algebraMap F (v.adicCompletion F) a)⁻¹ * (x i - (r i) v)
  let g : (κ → Fv F v) → (κ → Fv F v) := fun z i => algebraMap F (v.adicCompletion F) a * z i + (r i) v
  have hf : Continuous f :=
    continuous_pi fun i => continuous_const.mul ((continuous_apply i).sub continuous_const)
  have hg : Continuous g :=
    continuous_pi fun i => (continuous_const.mul (continuous_apply i)).add continuous_const
  have hS : cosetBoxV a r v = f ⁻¹' P := by
    ext x
    simp only [cosetBoxV, P, f, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq,
      SetLike.mem_coe]
  have hPo : IsOpen P := isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  have hPc : IsCompact P := isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  have hcl : IsClopen (cosetBoxV a r v) := by
    rw [hS]
    exact ⟨hPc.isClosed.preimage hf, hPo.preimage hf⟩
  have hco : IsCompact (cosetBoxV a r v) := by
    refine (hPc.image hg).of_isClosed_subset hcl.isClosed ?_
    intro x hx
    refine ⟨f x, ?_, ?_⟩
    · rw [hS] at hx
      exact hx
    · funext i
      simp only [f, g]
      rw [mul_inv_cancel_left₀ ha0, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ cosetBoxV a r v
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

theorem eventually_cosetBoxV_eq {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F) [Finite κ] :
    ∀ᶠ v in cofinite, cosetBoxV a r v = {x | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
  have h1 : ∀ᶠ v in cofinite, (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v ∈ v.adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) a).2
  have h2 : ∀ᶠ v in cofinite, (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) v ∈ v.adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹).2
  have h3 : ∀ᶠ v in cofinite, ∀ i, (r i) v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (r i).2
  filter_upwards [h1, h2, h3] with v hv1 hv2 hv3
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).2 ha
  have e1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v = algebraMap F (v.adicCompletion F) a := rfl
  have e2 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) v = (algebraMap F (v.adicCompletion F) a)⁻¹ := by
    show algebraMap F (v.adicCompletion F) a⁻¹ = _
    exact map_inv₀ _ a
  rw [e1] at hv1
  rw [e2] at hv2
  ext x
  simp only [cosetBoxV, Set.mem_setOf_eq]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => ?_⟩
  · have hd : x i - (r i) v ∈ v.adicCompletionIntegers F := by
      rw [← mul_inv_cancel_left₀ ha0 (x i - (r i) v)]
      exact mul_mem hv1 h
    have e : x i = (x i - (r i) v) + (r i) v := (sub_add_cancel _ _).symm
    rw [e]
    exact add_mem hd (hv3 i)
  · exact mul_mem hv2 (sub_mem h (hv3 i))

theorem indicator_coset_scaledInt_eq_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F)
    (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  intro F _ _ κ _ a r ha
  classical
  refine ⟨fun v => Set.indicator (cosetBoxV a r v) 1, fun v => indicator_cosetBoxV_mem_SB ha r v, ?_, ?_⟩
  · filter_upwards [eventually_cosetBoxV_eq ha r] with v hv
    rw [hv]
  · intro y
    have hmem : ∀ v, (fun i => evalV F v (y i)) ∈ cosetBoxV a r v ↔
        ∀ i, (algebraMap F (v.adicCompletion F) a)⁻¹ * ((y - r) i) v ∈ v.adicCompletionIntegers F :=
      fun v => Iff.rfl
    by_cases hy : y - r ∈ scaledInt F κ a
    · rw [Set.indicator_of_mem (show y ∈ {y | y - r ∈ scaledInt F κ a} from hy)]
      have h1 : ∀ v, Set.indicator (cosetBoxV a r v) (1 : (κ → Fv F v) → ℂ) (fun i => evalV F v (y i)) = 1 :=
        fun v => by rw [Set.indicator_of_mem ((hmem v).2 fun i => hy i v)]; rfl
      rw [finprod_congr h1, finprod_one]
    · rw [Set.indicator_of_notMem (show y ∉ {y | y - r ∈ scaledInt F κ a} from hy)]
      rw [mem_scaledInt] at hy
      push_neg at hy
      obtain ⟨i, v, hv⟩ := hy
      symm
      refine finprod_eq_zero _ v ?_ ?_
      · exact Set.indicator_of_notMem (fun h => hv ((hmem v).1 h i)) _
      · have hint : ∀ᶠ w in cofinite, ∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F :=
          Filter.eventually_all.2 fun i => (y i).2
        refine (Filter.eventually_cofinite.1 ((eventually_cosetBoxV_eq ha r).and hint)).subset ?_
        intro w hw h'
        apply hw
        simp only [Function.mem_mulSupport, not_not]
        rw [h'.1, Set.indicator_of_mem (show (fun i => evalV F w (y i)) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from h'.2)]
        rfl

end GlobalTheory.EvAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.JacSubst

open GlobalTheory.ModuLR GlobalTheory.GaugeEx

theorem chi_AF_split (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  let Mi : Matrix κ κ (Ainf F) := (fstA F).toRingHom.mapMatrix M
  let Mf : Matrix κ κ (Af F) := (sndA F).toRingHom.mapMatrix M
  have hi : Mi.det = fstA F M.det := (RingHom.map_det _ _).symm
  have hf : Mf.det = sndA F M.det := (RingHom.map_det _ _).symm
  have hMi : IsUnit Mi.det := hi ▸ hM.map (fstA F)
  have hMf : IsUnit Mf.det := hf ▸ hM.map (sndA F)
  let j : (κ → Ainf F) × (κ → Af F) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := _root_.GlobalTheory.ModuLR.zipHom_isOpenEmbedding κ (Ainf F) (Af F)
  have s1 : addEquivAddHaarChar (mulVecCE M hM) =
      addEquivAddHaarChar (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) :=
    _root_.GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding _ _ j hj (mulVecCE M hM) (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) fun p => by
      funext i
      show (M *ᵥ j p) i = ((Mi *ᵥ p.1) i, (Mf *ᵥ p.2) i)
      have e1 : fstA F ((M *ᵥ j p) i) = (Mi *ᵥ p.1) i := by
        rw [show (fstA F) ((M *ᵥ j p) i) = (fstA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      have e2 : sndA F ((M *ᵥ j p) i) = (Mf *ᵥ p.2) i := by
        rw [show (sndA F) ((M *ᵥ j p) i) = (sndA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      rw [← e1, ← e2]
      rfl
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  have s2 : addEquivAddHaarChar (mulVecCE Mi hMi) = modu (Ainf F) Mi.det :=
    _root_.GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE (Ainf F) inferInstance inferInstance κ Mi hMi
  rw [s1, _root_.GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE, NNReal.coe_mul, s2, chi_Af F Mf hMf, hi, hf]

theorem chi_AF_det (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  classical
  let a : (AF F)ˣ := hM.unit
  let N : Matrix Unit Unit (AF F) := fun _ _ => (a : AF F)
  have hNd : N.det = M.det := by rw [Matrix.det_unique]; rfl
  have hN : IsUnit N.det := hNd ▸ hM
  have h1 : distribHaarChar (AF F) a = addEquivAddHaarChar (mulVecCE N hN) := by
    rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar,
      ← addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)]
    congr 1
    ext x
    show (a : AF F) * x = (N *ᵥ fun _ => x) ()
    simp [N, Matrix.mulVec, dotProduct]
  apply NNReal.coe_injective
  show (addEquivAddHaarChar (mulVecCE M hM) : ℝ) = (distribHaarChar (AF F) a : ℝ)
  rw [h1, chi_AF_split, chi_AF_split, hNd]

def colCE (R : Type) [AddCommGroup R] [TopologicalSpace R] (d : ℕ) : (Fin d → R) ≃ₜ+ Matrix (Fin d) (Fin 1) R where
  toFun u := Matrix.of fun i _ => u i
  invFun m i := m i 0
  left_inv u := rfl
  right_inv m := by
    ext i j
    rw [Fin.fin_one_eq_zero j]
    rfl
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_pi fun _ => continuous_apply i
  continuous_invFun := continuous_pi fun i => (continuous_apply 0).comp (continuous_apply i)

def coordCE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (b : Module.Basis (Fin n) F E) : AE F E ≃ₜ (Fin n → AF F) :=
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  { (Algebra.TensorProduct.basis (AF F) b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap }

end GlobalTheory.JacSubst


open GlobalTheory.ModuLR GlobalTheory.GaugeEx GlobalTheory.JacSubst in
theorem GlobalTheory.JacSubst.integral_mulVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (t : GL (Fin d) (AE F E)),
    ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin d → AE F E) → ℂ, ∫ u, f ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ u) ∂μ =
      (((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ u, f u ∂μ := by
  intro F E _ _ _ _ _ d t μ hμ f
  letI mV : MeasurableSpace (Fin d → AE F E) := borel _
  haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  let e := coordCE F E (Module.finBasis F E)
  haveI : LocallyCompactSpace (AE F E) := e.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin d) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin d) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin d) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin d) (Fin 1) (AE F E)) := ⟨rfl⟩
  haveI : μ.Regular := inferInstance
  have hdt : IsUnit (t : Matrix (Fin d) (Fin d) (AE F E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  let φ := mulVecCE (t : Matrix (Fin d) (Fin d) (AE F E)) hdt
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hχ⟩ := @exists_matrix_restrictScalars_lrCE F E _ _ _ _ _ d (1 : ℕ) _ _ _ _ t (1 : GL (Fin 1) (AE F E))
  have hc : addEquivAddHaarChar φ =
      distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) := by
    have h1 : addEquivAddHaarChar φ = addEquivAddHaarChar (lrCE t (1 : GL (Fin 1) (AE F E))) := by
      rw [← addEquivAddHaarChar_transport (colCE (AE F E) d) φ]
      congr 1
      ext m i j
      rw [Fin.fin_one_eq_zero j]
      show ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ (fun k => m k 0)) i =
        ((t : Matrix (Fin d) (Fin d) (AE F E)) * m * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0
      rw [Units.val_one, Matrix.mul_one]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h1, hχ, chi_AF_det]
    congr 1
    ext
    simp only [IsUnit.unit_spec, hdet, Units.coe_map, MonoidHom.coe_coe, map_one, one_pow, mul_one, pow_one]
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ u, f ((t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ u) ∂μ :=
    integral_map_equiv φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, hc, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelCov

section Gen

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR

theorem chi_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  let Mi : Matrix κ κ (Ainf F) := (fstA F).toRingHom.mapMatrix M
  let Mf : Matrix κ κ (Af F) := (sndA F).toRingHom.mapMatrix M
  have hi : Mi.det = fstA F M.det := (RingHom.map_det _ _).symm
  have hf : Mf.det = sndA F M.det := (RingHom.map_det _ _).symm
  have hMi : IsUnit Mi.det := hi ▸ hM.map (fstA F)
  have hMf : IsUnit Mf.det := hf ▸ hM.map (sndA F)
  let j : (κ → Ainf F) × (κ → Af F) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := _root_.GlobalTheory.ModuLR.zipHom_isOpenEmbedding κ (Ainf F) (Af F)
  have s1 : addEquivAddHaarChar (mulVecCE M hM) =
      addEquivAddHaarChar (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) :=
    _root_.GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding _ _ j hj (mulVecCE M hM) (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) fun p => by
      funext i
      show (M *ᵥ j p) i = ((Mi *ᵥ p.1) i, (Mf *ᵥ p.2) i)
      have e1 : fstA F ((M *ᵥ j p) i) = (Mi *ᵥ p.1) i := by
        rw [show (fstA F) ((M *ᵥ j p) i) = (fstA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      have e2 : sndA F ((M *ᵥ j p) i) = (Mf *ᵥ p.2) i := by
        rw [show (sndA F) ((M *ᵥ j p) i) = (sndA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      rw [← e1, ← e2]
      rfl
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  have s2 : addEquivAddHaarChar (mulVecCE Mi hMi) = modu (Ainf F) Mi.det :=
    _root_.GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE (Ainf F) inferInstance inferInstance κ Mi hMi
  rw [s1, _root_.GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE, NNReal.coe_mul, s2, chi_Af F Mf hMf, hi, hf]

theorem addEquivAddHaarChar_mulVecCE_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  let N : Matrix Unit Unit (AF F) := fun _ _ => M.det
  have hdet : N.det = M.det := Matrix.det_unique N
  have hN : IsUnit N.det := hdet ▸ hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)
  have hext : ((GlobalTheory.ModuNorm.evalUnitCE (AF F)).symm.trans (mulVecCE N hN)).trans (GlobalTheory.ModuNorm.evalUnitCE (AF F)) =
      GlobalTheory.ModuNorm.mulUnitCE hM.unit := by
    ext x
    show (N *ᵥ fun _ => x) () = M.det * x
    simp [Matrix.mulVec, dotProduct, N]
  rw [hext] at htr
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, htr]
  apply NNReal.coe_injective
  rw [chi_adele, chi_adele, hdet]

end Gen

end GlobalTheory.SiegelCov

namespace GlobalTheory.SiegelCov

section Coord

open Matrix GlobalTheory.ModuLR

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)

def vecCoord : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin (Module.finrank F E) → AF F) where
  toFun u p := (tensBasis F E).equivFun (u p.1) p.2
  invFun x i := (tensBasis F E).equivFun.symm fun k => x (i, k)
  left_inv u := by
    funext i
    exact (tensBasis F E).equivFun.symm_apply_apply (u i)
  right_inv x := by
    funext p
    obtain ⟨i, k⟩ := p
    show (tensBasis F E).equivFun ((tensBasis F E).equivFun.symm fun k => x (i, k)) k = x (i, k)
    rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by funext p; simp
  map_smul' c u := by funext p; simp

theorem continuous_vecCoord : Continuous (vecCoord F E n) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.toLinearMap
  exact continuous_pi fun p => (continuous_apply p.2).comp (hb.comp (continuous_apply p.1))

theorem continuous_vecCoord_symm : Continuous (vecCoord F E n).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hb : Continuous (tensBasis F E).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.symm.toLinearMap
  exact continuous_pi fun i => hb.comp (continuous_pi fun k => continuous_apply (i, k))

def vecCoordCE : (Fin n → AE F E) ≃ₜ+ (Fin n × Fin (Module.finrank F E) → AF F) :=
  { (vecCoord F E n).toAddEquiv with
    continuous_toFun := continuous_vecCoord F E n
    continuous_invFun := continuous_vecCoord_symm F E n }

end Coord

end GlobalTheory.SiegelCov


open GlobalTheory.GaugeEx in
theorem GlobalTheory.SiegelCov.integral_mulVec_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (μ : @Measure (Fin n → AE F E) (borel _)), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ (t : GL (Fin n) (AE F E)) (f : (Fin n → AE F E) → ℂ),
      (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) →
      (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        ∫ y, f (((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ y) ∂μ) =
        (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) : ℂ) *
          (letI : MeasurableSpace (Fin n → AE F E) := borel _; ∫ y, f y ∂μ) := by
  intro F E _ _ _ _ _ n μ hμ t f _
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalAddGroup (AE F E) := IsModuleTopology.isTopologicalAddGroup (AF F) _
  haveI : Module.Free (AF F) (AF F ⊗[F] E) := Module.Free.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  haveI : Module.Finite (AF F) (AF F ⊗[F] E) := Module.Finite.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  let Φ := GlobalTheory.SiegelCov.vecCoordCE F E n
  haveI : LocallyCompactSpace (Fin n → AE F E) := Φ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin n → AE F E) := Φ.toHomeomorph.isInducing.secondCountableTopology
  haveI : T2Space (Fin n → AE F E) := Φ.toHomeomorph.isEmbedding.t2Space
  haveI : μ.IsAddHaarMeasure := hμ
  haveI : TopologicalSpace.PseudoMetrizableSpace (Fin n → AE F E) := inferInstance
  haveI : SigmaCompactSpace (Fin n → AE F E) := inferInstance
  haveI : μ.Regular := inferInstance
  set T : Matrix (Fin n) (Fin n) (AE F E) := ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hTdef
  have hT : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 (t⁻¹).isUnit
  set L := GlobalTheory.ModuLR.mulVecCE T hT with hL
  set Λ := LinearMap.toMatrix' ((GlobalTheory.SiegelCov.vecCoord F E n).toLinearMap ∘ₗ
    (Matrix.toLin' T).restrictScalars (AF F) ∘ₗ (GlobalTheory.SiegelCov.vecCoord F E n).symm.toLinearMap) with hΛdef
  have hdet : Λ.det = Algebra.norm (AF F) T.det := by
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  have hΛ : IsUnit Λ.det := hdet ▸ hT.map (Algebra.norm (AF F))
  have hc : GlobalTheory.ModuLR.mulVecCE Λ hΛ = (Φ.symm.trans L).trans Φ := by
    ext x
    rw [GlobalTheory.ModuLR.mulVecCE_apply, LinearMap.toMatrix'_mulVec]
    rfl
  have hχ : addEquivAddHaarChar L = distribHaarChar (AF F) hΛ.unit := by
    rw [← GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele, hc, GlobalTheory.ModuLR.addEquivAddHaarChar_transport]
  have hu : hΛ.unit = (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))⁻¹ := by
    ext
    rw [IsUnit.unit_spec, hdet, hTdef]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have key := addEquivAddHaarChar_smul_map μ L
  set c := addEquivAddHaarChar L with hcdef
  have hc0 : c ≠ 0 := (addEquivAddHaarChar_pos L).ne'
  have hmap : μ.map L = c⁻¹ • μ := by
    calc μ.map L = (c⁻¹ * c) • μ.map L := by rw [inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ y, f (T *ᵥ y) ∂μ = ∫ y, f y ∂(μ.map L) :=
    (integral_map_equiv L.toHomeomorph.toMeasurableEquiv f).symm
  have hmodu : ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
      (Matrix.GeneralLinearGroup.det t)) : ℝ≥0) = c⁻¹ := by
    rw [hχ, hu, map_inv, inv_inv]
    rfl
  show ∫ y, f (T *ᵥ y) ∂μ = _
  rw [hint, hmap, integral_smul_nnreal_measure, hmodu, NNReal.smul_def, Complex.real_smul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
section
noncomputable section

open NumberField IsDedekindDomain Matrix GroundTheory.Automorphic UpperTheory.V.Af
open GlobalTheory.CuspRep (GA Af Ad pFin pLoc)

namespace GlobalTheory.HenQ.Basic

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_KGL_iff (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)) :
    y ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov K w := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun i j => (z.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((z⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map (Formalism.UG.Ov K w).subtype = y.val := by ext i j; rfl
    have hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hM

end GlobalTheory.HenQ.Basic
end
end

