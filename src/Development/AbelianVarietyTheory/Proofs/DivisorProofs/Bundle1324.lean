module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceCuspForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import GroundTheory.GlobalFields.Adele.BaseChange
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.ConjLoc

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def conjSchR (κ : Type) [Fintype κ] : SInf F κ →L[ℝ] SInf F κ :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem conjSchR_apply {κ : Type} [Fintype κ] (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    conjSchR κ f x = starRingEnd ℂ (f x) := rfl

def conjSchCLM {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : SInf F κ →L[ℂ] SInf F κ₁) : SInf F κ →L[ℂ] SInf F κ₁ where
  toFun f := conjSchR κ₁ (T (conjSchR κ f))
  map_add' f g := by simp only [map_add (f := _)]
  map_smul' c f := by
    have h : conjSchR κ (c • f) = starRingEnd ℂ c • conjSchR κ f := by
      refine SchwartzMap.ext fun y => ?_; simp only [conjSchR_apply, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
    refine SchwartzMap.ext fun x => ?_
    rw [h, map_smul, conjSchR_apply, RingHom.id_apply, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul, Complex.conj_conj, conjSchR_apply]
  cont := (conjSchR κ₁).continuous.comp (T.continuous.comp (conjSchR κ).continuous)

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) :
    (fun x => starRingEnd ℂ (φ x)) ∈ SB X :=
  ⟨h.1.comp (starRingEnd ℂ), h.2.comp_left (g := starRingEnd ℂ) (map_zero _)⟩

theorem conj_stdInd_apply (κ : Type) (v : Pl (F := F)) (y : κ → Fv F v) :
    starRingEnd ℂ (stdInd F κ v y) = stdInd F κ v y := by
  unfold stdInd
  by_cases hy : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
  · rw [Set.indicator_of_mem hy, Pi.one_apply, map_one]
  · rw [Set.indicator_of_notMem hy, map_zero]

theorem conj_stdInd (κ : Type) (v : Pl (F := F)) :
    (fun y => starRingEnd ℂ (stdInd F κ v y)) = stdInd F κ v :=
  funext (conj_stdInd_apply κ v)

theorem conj_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) :
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) x := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, conjSchR_apply, map_mul]
  congr 1
  exact MulEquiv.map_finprod (starRingAut : ℂ ≃+* ℂ).toMulEquiv _

theorem isLocOp_conjLin {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ)
    (he : IsLocOp e) : IsLocOp (conjLin e) := by
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  refine ⟨conjSchCLM ei, fun v => conjLin (ev v), fun v φ hφ => conj_mem_SB (hSB v _ (conj_mem_SB hφ)), ?_, ?_⟩
  · filter_upwards [hstd] with v hv
    funext y
    rw [conjLin_apply, conj_stdInd, hv, conj_stdInd_apply]
  · intro f φ hφ hfin
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) :=
      funext (conj_pure f φ)
    have hfin' : ∀ᶠ v in cofinite, (fun y => starRingEnd ℂ (φ v y)) = stdInd F κ v := by
      filter_upwards [hfin] with v hv
      rw [hv, conj_stdInd]
    rw [h1, hloc _ _ (fun v => conj_mem_SB (hφ v)) hfin', conj_pure]
    rfl

end GlobalTheory.DblEval.ConjLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulPosDef
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryClasses

theorem posDef_cT_inv_mul_inv (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E)
    (τ : E →+* ℂ) :
    ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  set B : Matrix (Fin n) (Fin n) E := (h⁻¹).val with hB
  have hc : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom B).map τ = (B.map τ)ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
  rw [Matrix.map_mul, hc]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  have hu : IsUnit B := (h⁻¹).isUnit
  exact hu.map (RingHom.mapMatrix τ)

end GlobalTheory.UnitaryClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero
section
noncomputable section

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem IsCuspForm.mem_cuspForms {φ : Sm E a} (h : IsCuspForm φ) : φ.1 ∈ cuspForms E a :=
  (UpperTheory.V.Cm.isCuspForm_iff φ).1 h

theorem IsCuspForm.constantTerm_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a) (h : IsCuspForm φ) : AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 :=
  h.mem_cuspForms.2

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpan
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem slice_cpt_mem {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ} (hr : r ≤ a)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) [MeasurableSpace (BlockIx a r → Ad E)]
    [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (h1 : μ 𝓕 = 1)
    (φ : Sm E a) (hφ : φ ∈ GlobalTheory.HCF.formsGL E a L W X N) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a)
    (g : GA E (a - r)) :
    (fun k : Kinf E (a - r) => slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) (Unitary.toUnits k))) ∈
      ktypeSub hr κ W := by
  have hm := GlobalTheory.HCFct.constTerm_cptTranslate_mem E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ (Submodule.subset_span hφ)
    (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ))
  refine ⟨_, hm, ?_⟩
  funext k
  exact (slice_mul_cpt μ 𝓕 hr φ.1 m₁ t κ g k).symm

end GlobalTheory.SliceTwo

namespace GlobalTheory.HCFct

open GlobalTheory.SliceTwo

theorem slice2_autForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (L' : Subgroup (GL (Fin (a - r)) (Af E))) (W' : Submodule ℂ (Kinf E (a - r) → ℂ)), IsOpen (L' : Set (GL (Fin (a - r)) (Af E))) ∧ FiniteDimensional ℂ W' ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∃ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∧ (∀ γ g, ψ.1 (ratGL E (a - r) γ * g) = ψ.1 g) ∧ IsOpen {k | finRep E (a - r) k ψ = ψ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) ∧ (∀ g, ∃ (C : ℝ) (M : ℕ), ∀ y, ‖ψ.1 (g * infGL E (a - r) y)‖ ≤ C * height y ^ M) ∧ (∀ k ∈ L', finRep E (a - r) k ψ = ψ) ∧ ∀ g : GA E (a - r), (fun k : Kinf E (a - r) => (cptRep E (a - r) k ψ).1 g) ∈ W' := by
  intro E _ _ _ a L hL W hW X _ N r _ hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  refine ⟨levelSub hr.le t L, ktypeSub hr.le κ W, _root_.GlobalTheory.SliceTwo.isOpen_levelSub E a r hr.le t L hL, inferInstance, fun φ hφ m₁ => ?_⟩
  have hA : IsAutForm φ := hφ.1
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hA.level
  have hfix : ∀ k ∈ L, ∀ g, φ.1 (g * finGL E a k) = φ.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (hφ.2.1 k hk)) g
  let ψ : Sm E (a - r) := ⟨slice E μ 𝓕 hr.le φ.1 m₁ t κ, _root_.GlobalTheory.SliceTwoSmooth.slice_mem_Sm E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ⟩
  have hlev : ∀ k ∈ levelSub hr.le t L, finRep E (a - r) k ψ = ψ := fun k hk =>
    Subtype.ext (funext fun g => slice_mul_finGL μ 𝓕 hr.le φ.1 L hfix m₁ t κ k hk g)
  refine ⟨ψ, rfl, _root_.GlobalTheory.SliceTwo.slice_ratGL_mul E a r hr.le μ 𝓕 hμ h𝓕 h1 φ.1 hc hA.left m₁ t κ, ?_,
    GlobalTheory.T.constant_term_slice_levi_restriction E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ ψ rfl, _root_.GlobalTheory.SliceTwo.Growth.norm_slice_le E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ, hlev,
    fun g => slice_cpt_mem hr.le L W hW X N μ 𝓕 hμ h𝓕 h1 φ hφ m₁ t κ g⟩
  refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((_root_.GlobalTheory.SliceTwo.isOpen_levelSub E a r hr.le t L hL).mem_nhds (Subgroup.one_mem _)) fun k hk => hlev k hk)

end GlobalTheory.HCFct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterTrivialOnSmallIdeles
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.PsiTriv

theorem exists_nat_trivial {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m : Fv F v)‖) → ψ t = 1 := by
  classical
  let f : FiniteAdeleRing (𝓞 F) F → AF F := fun y => (0, y)
  have hf : Continuous f := continuous_const.prodMk continuous_id
  have hW : (fun y => ψ (f y)) ⁻¹' {z : ℂ | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
    refine ((isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).preimage (hψ.comp hf)).mem_nhds ?_
    show ‖ψ (0 : AF F) - 1‖ < 1 / 2
    rw [AddChar.map_zero_eq_one]; norm_num
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  set D : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d) with hD
  have htriv : ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = 1 := by
    intro y hy
    refine GroundTheory.Global.eq_one_of_sq_mem
      (s := {z | ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = z}) ?_ ?_ ⟨y, hy, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨a + a, add_mem ha ha, ?_⟩
      rw [sq, ← AddChar.map_add_eq_mul]
      congr 1
      show ((0 : InfiniteAdeleRing F), D * (a + a)) = ((0 : InfiniteAdeleRing F) + 0, D * a + D * a)
      rw [mul_add, add_zero]
    · rintro _ ⟨a, ha, rfl⟩
      exact hd a ha
  have hm0 : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero hm0, fun t ht0 ht => ?_⟩
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
  let y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2
  have hty : t = f (D * y) := by
    refine Prod.ext ht0 ?_
    show t.2 = algebraMap F _ (algebraMap (𝓞 F) F d) * (algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hdF, map_one, one_mul]
  rw [hty]
  refine htriv y fun v => ?_
  have hv : ‖t.2 v‖ ≤ _ := ht v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
  have hy : y v = algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)⁻¹ * t.2 v := rfl
  have hm : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Fv F v) =
      algebraMap F (Fv F v) (algebraMap (𝓞 F) F e) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) := by
    rw [← map_mul, ← map_mul, he, map_natCast, map_natCast]
  have hdv : algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) ≠ 0 := (map_ne_zero _).2 hdF
  have he1 : ‖algebraMap F (Fv F v) (algebraMap (𝓞 F) F e)‖ ≤ 1 := FinitePlace.norm_le_one F v e
  rw [hy, map_inv₀, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hdv)]
  rw [hm, norm_mul] at hv
  nlinarith [norm_nonneg (algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)), norm_nonneg (t.2 v)]

end GlobalTheory.PsiTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

open scoped GroundTheory.Global.AdeleBaseChange NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.IdeleLogHom

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

section Transfer

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toE : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ →* IdeleGroup E :=
  Units.map (adeleTensorAlgEquivLeft F E : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →ₐ[AF F] AdeleRing (𝓞 E) E).toMonoidHom

theorem absE_eq_ideleModule (x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    (absE F E x : ℝ) = (IdeleGroup.ideleModule E (toE F E x) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), ← GlobalTheory.ModuAdele.modu_norm_eq_absE]
  have h2 : ∀ u : (AF F)ˣ, (((adeleClass F).modu u : ℝ≥0) : ℝ) = (IdeleGroup.ideleModule F u : ℝ) := fun u => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) u : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u
  have h3 : Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) x = ideleNorm F E (toE F E x) := by
    ext
    simp [toE, ideleNorm, Algebra.norm_eq_of_algEquiv]
  rw [h2, h3]

end Transfer

section OnE

variable {E : Type} [Field E] [NumberField E]

end OnE

end GlobalTheory.IdeleLogHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

theorem continuous_mixedSymm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_infAd : Continuous (infAd F) :=
  (continuous_mixedSymm F).prodMk continuous_const

theorem continuous_evI_arch : Continuous (evI F) := (continuous_mixed F).comp continuous_fst

@[simp] theorem evI_infAd (a : mixedEmbedding.mixedSpace F) : evI F (infAd F a) = a := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) = a
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd; rw [map_add (f := _), map_add (f := _)]

theorem infAd_zero : infAd F 0 = 0 := by unfold infAd; rw [map_zero, map_zero]

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  exact map_add ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) a b

theorem evI_zero' : evI F 0 = 0 := by
  exact map_zero ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

abbrev dimA : ℕ := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)

def ubasis : Module.Basis (Fin (dimA F κ)) ℝ (κ → mixedEmbedding.mixedSpace F) :=
  (Module.finBasis ℝ _).unitsSMul fun j =>
    Units.mk0 ‖Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F) j‖⁻¹
      (inv_ne_zero (norm_ne_zero_iff.2 ((Module.finBasis ℝ _).ne_zero j)))

theorem norm_ubasis (j : Fin (dimA F κ)) : ‖ubasis F κ j‖ = 1 := by
  have h := norm_ne_zero_iff.2 ((Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)).ne_zero j)
  simp [ubasis, Module.Basis.unitsSMul_apply, norm_smul, h]

def archIn : (Fin (dimA F κ) → ℝ) →+ (κ → AF F) where
  toFun t := fun i => infAd F ((ubasis F κ).equivFun.symm t i)
  map_zero' := by funext i; rw [map_zero]; exact infAd_zero F
  map_add' s t := by funext i; rw [map_add (f := _)]; exact infAd_add F _ _

def archOut : (κ → AF F) →+ (Fin (dimA F κ) → ℝ) where
  toFun x := (ubasis F κ).equivFun (arch F x)
  map_zero' := by
    have : arch F (0 : κ → AF F) = 0 := by funext i; exact evI_zero' F
    rw [this, map_zero]
  map_add' x y := by
    have : arch F (x + y) = arch F x + arch F y := by funext i; exact evI_add' F _ _
    rw [this, map_add (f := _)]

theorem archIn_apply (t : Fin (dimA F κ) → ℝ) (i : κ) :
    archIn F κ t i = infAd F ((ubasis F κ).equivFun.symm t i) := rfl

theorem archOut_apply (x : κ → AF F) : archOut F κ x = (ubasis F κ).equivFun (arch F x) := rfl

@[simp] theorem archOut_archIn (t : Fin (dimA F κ) → ℝ) : archOut F κ (archIn F κ t) = t := by
  have : arch F (archIn F κ t) = (ubasis F κ).equivFun.symm t := by funext i; simp [arch, archIn_apply]
  rw [archOut_apply, this, LinearEquiv.apply_symm_apply]

theorem continuous_archIn : Continuous (archIn F κ) := by
  refine continuous_pi fun i => ?_
  show Continuous fun t => infAd F ((ubasis F κ).equivFun.symm t i)
  exact (continuous_infAd F).comp ((continuous_apply i).comp
    (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.symm.toLinearMap))

theorem continuous_archOut : Continuous (archOut F κ) := by
  show Continuous fun x => (ubasis F κ).equivFun (arch F x)
  exact (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.toLinearMap).comp
    (continuous_pi fun i => (continuous_evI_arch F).comp (continuous_apply i))

def perSet (m : ℕ) : Set (κ → AF F) :=
  {z | ∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧ z i = (m : AF F) * a}

def slab (m : ℕ) : Set (κ → AF F) := {w | w - archIn F κ (archOut F κ w) ∈ perSet F κ m}

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContragredientEqInvTransposeClass
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.DualClassTranspose

def equivComp {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {σ : Representation ℂ H W} (φ : G →* H) (e : ρ.Equiv σ) :
    Representation.Equiv (ρ.comp φ : Representation ℂ G V) (σ.comp φ : Representation ℂ G W) :=
  Representation.Equiv.mk' ⟨e.toLinearMap, fun g => e.toIntertwiningMap.isIntertwining' (φ g)⟩ e.symm
    (fun v => e.symm_apply_apply v) (fun w => e.apply_symm_apply w)

theorem invTranspose_eq (k : Type) [Field k] (n : ℕ) :
    GlobalTheory.TypeTame.invTranspose (R := k) n = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n k :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem dualCl_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ x y : IrrGL (k := k), DualCl x y ↔ ∃ (h1 : IsSmooth (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))) (h2 : Representation.IsIrreducible (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))), y = IrrGL.of (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1)) h1 h2 := by
  intro k _ _ _ _ hA x y
  have hinv : ∀ n (g : GL (Fin n) k), GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g :=
    fun n g => GlobalTheory.TypeTame.invTranspose_invTranspose n g
  have hsm : ∀ (z : IrrGL (k := k)), IsSmooth (z.rep.comp (GlobalTheory.TypeTame.invTranspose z.1)) := fun z v =>
    (z.2.rep.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose z.1)
  have hirr : ∀ (z : IrrGL (k := k)), Representation.IsIrreducible (z.rep.comp (GlobalTheory.TypeTame.invTranspose z.1)) := fun z =>
    GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, hinv _ g⟩) z.2.rep.irr

  have gk : ∀ {n : ℕ} (π : IrrRep (GL (Fin n) k)),
      Nonempty (Representation.Equiv (π.ρ.comp (GlobalTheory.TypeTame.invTranspose n) : Representation ℂ (GL (Fin n) k) π.V) (contra π.ρ)) := by
    intro n π
    rw [invTranspose_eq]
    exact GlobalTheory.GelfandKazhdan.equiv_contra k n π.V π.ρ (hA k n π.V π.ρ π.smooth π.irr) π.irr
  constructor
  · rintro ⟨n, π, π', rfl, rfl, ⟨e⟩⟩
    refine ⟨hsm _, hirr _, ?_⟩
    obtain ⟨f⟩ := gk π
    obtain ⟨r⟩ := IrrRep.nonempty_equiv_rep π

    have e2 : Representation.Equiv ((cls π).rep.comp (GlobalTheory.TypeTame.invTranspose (cls π).1) : Representation ℂ (GL (Fin n) k) _) π'.ρ :=
      (equivComp _ r).trans (f.trans e.symm)
    show (⟨n, π'.cl⟩ : IrrGL (k := k)) = _
    have : (⟨n, π'.cl⟩ : IrrGL (k := k)) = IrrGL.of π'.ρ π'.smooth π'.irr := rfl
    rw [this]
    exact IrrGL.of_eq_of.2 ⟨e2.symm⟩
  · rintro ⟨h1, h2, rfl⟩
    refine ⟨x.1, x.2.rep, ⟨_, x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1), h1, h2⟩, ?_, rfl, ?_⟩
    · exact (congrArg (Sigma.mk x.1) x.2.cl_rep).symm
    · exact gk x.2.rep

end GlobalTheory.DualClassTranspose
end

