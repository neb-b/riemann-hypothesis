module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelHalfChainNumbersAnyLevelPrime
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LatVac

theorem exists_integer_add_conj_eq_one_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance

end GlobalTheory.LatVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_isLv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ f
  exact ⟨GlobalTheory.SphEisModel.lv f, GlobalTheory.SphEisModel.isLv_lv f⟩

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisCompletionInSpanLieLattice
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LieSpan

theorem exists_isLieBasis_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib B.pol) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (n : SABMap G.t B.t (spMap ρV)), ∃ vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G), IsLieBasis vV ∧ ∀ k, ∃ (M : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A), IsLieComb M F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ ∧ (fun l => iK (M l)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) l => iK (v l)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  intro E _ _ _ H K _ _ B F 𝔓 T iK hiK ρV hρV G n
  obtain ⟨N, r, M, hr, hM, -, hloc⟩ := _root_.GlobalTheory.CM.LieGlue.exists_cover_lieLat K B.pol F
  obtain ⟨i, hi⟩ : ∃ i, r i ∉ 𝔓.asIdeal := by
    by_contra h
    push_neg at h
    refine 𝔓.isPrime.ne_top ?_
    rw [eq_top_iff, ← hr]
    exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h j)
  have hv1 : ∀ m : ℕ, 𝔓.valuation K (algebraMap (𝓞 K) K (r i ^ m)) = 1 := fun m => by
    rw [HeightOneSpectrum.valuation_of_algebraMap, map_pow]
    rw [le_antisymm (𝔓.intValuation_le_one _) (not_lt.1 fun h => hi ((𝔓.intValuation_lt_one_iff_mem _).1 h)),
      one_pow]
  let R := Localization.subalgebra.ofField K (Submonoid.powers (r i))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (hM i).1)
  have e₁ : (algebraMap R K).comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hval : ∀ z : R, iK (algebraMap R K z) ∈ Set.range (algebraMap T.V T.Fr) := fun z => by
    refine (hiK _).2 ?_
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r i)) z
    have hz := congrArg (algebraMap R K) (IsLocalization.mk'_spec R x s)
    rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, e₁] at hz
    obtain ⟨m, hm⟩ := s.2
    have hs : 𝔓.valuation K (algebraMap (𝓞 K) K s) = 1 := by rw [← hm]; exact hv1 m
    have := congrArg (𝔓.valuation K) hz
    rw [map_mul, hs, _root_.mul_one] at this
    rw [this]
    exact 𝔓.valuation_le_one x
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.LamT.exists_restrict_ringHom (algebraMap R K) (algebraMap T.V T.Fr) hinj iK hval
  have hρ : ρV = ψ'.comp (algebraMap (𝓞 K) R) := by
    refine RingHom.ext fun x => hinj ?_
    have h₁ := RingHom.congr_fun hρV x
    have h₂ := RingHom.congr_fun hψ' (algebraMap (𝓞 K) R x)
    have h₃ := RingHom.congr_fun e₁ x
    simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  let GR := (Over.pullback (spMap (algebraMap (𝓞 K) R))).obj B.t.G
  have hp : IsGrpPullback GR B.t.G (spMap (algebraMap (𝓞 K) R)) (pullback.fst _ _) := isGrpPullback_pullback _ _
  have es₁ : spMap (algebraMap (𝓞 K) K) = spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [← spMap_comp, e₁]
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have w₁ : F.φ ≫ B.t.G.hom = (F.P₀.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hF.1.w, es₁, Category.assoc]
  have hψ : IsGrpPullback F.P₀.A GR (spMap (algebraMap R K)) (hp.1.lift _ _ w₁) :=
    IsGrpPullback.cancel hp (hF.congr es₁ (hp.1.lift_fst _ _ w₁).symm) (hp.1.lift_snd _ _ w₁)
  obtain ⟨e, he, hx⟩ := hloc i R GR (pullback.fst _ _) (hp.1.lift _ _ w₁)
    (IsLocalization.map_units R (⟨r i, Submonoid.mem_powers _⟩ : Submonoid.powers (r i))) hp hψ
    (hp.1.lift_fst _ _ w₁)
  choose e₀ he₀ hM₀ using hx
  have hin := (_root_.GlobalTheory.CM.LieLoc.lieLat_localization K B.pol F R (Submonoid.powers (r i)) GR (pullback.fst _ _) (hp.1.lift _ _ w₁) e e₀ (M i)
    hp hψ (hp.1.lift_fst _ _ w₁) he fun k => ⟨he₀ k, hM₀ k⟩).1
  have es₂ : spMap ρV = spMap ψ' ≫ spMap (algebraMap (𝓞 K) R) := by rw [hρ]; exact spMap_comp _ _
  have hn : IsGrpPullback G.t.G B.t.G (spMap ρV) n.φ := n.cart
  have w₂ : n.φ ≫ B.t.G.hom = (G.t.G.hom ≫ spMap ψ') ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hn.1.w, es₂, Category.assoc]
  have hq : IsGrpPullback G.t.G GR (spMap ψ') (hp.1.lift _ _ w₂) :=
    IsGrpPullback.cancel hp (hn.congr es₂ (hp.1.lift_fst _ _ w₂).symm) (hp.1.lift_snd _ _ w₂)
  have hsm : Smooth GR.hom := by
    haveI := B.dim
    haveI : Smooth B.t.G.hom := SmoothOfRelativeDimension.smooth B.g _
    exact MorphismProperty.of_isPullback (P := @Smooth) hp.1 inferInstance
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ' GR G.t.G _ hq hsm _ e he
  refine ⟨v', hb, fun k => ⟨M i k, e₀ k, hM₀ k, ?_, ?_⟩⟩
  · have ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        (Formalism.L2.Pj.dualMap iK).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      refine RingHom.ext fun x => ?_
      have h₁ := RingHom.congr_fun hψ' x.fst
      have h₂ := RingHom.congr_fun hψ' x.snd
      simp only [RingHom.comp_apply] at h₁ h₂
      refine TrivSqZeroExt.ext ?_ ?_
      · simpa [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR] using h₁
      · simp only [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
          zero_add]
        exact h₂
    have es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      rw [← spMap_comp, ← spMap_comp, ed]
    have eL : (v' k).left ≫ n.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₂, ← Category.assoc, hv' k, Category.assoc]
    have eR : (e₀ k).left ≫ F.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₁, ← Category.assoc, he₀ k, Category.assoc]
    rw [eL, eR, ← Category.assoc, es, Category.assoc]
  · obtain ⟨_, ⟨m, rfl⟩, hs⟩ := hin k
    have hs0 : algebraMap (𝓞 K) K (r i ^ m) ≠ 0 := by
      intro h0
      have := hv1 m
      rw [h0, map_zero] at this
      exact zero_ne_one this
    obtain ⟨u, hu⟩ := (hiK (algebraMap (𝓞 K) K (r i ^ m))⁻¹).2 (by rw [map_inv₀, hv1 m, inv_one])
    have eq : (fun l => iK (M i k l)) = u • fun l => iK ((r i ^ m • M i k) l) := by
      funext l
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hu, map_inv₀]
      rw [← _root_.mul_assoc, inv_mul_cancel₀ ((map_ne_zero iK).2 hs0), _root_.one_mul]
    rw [eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hs, rfl⟩)

end GlobalTheory.LieSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisFibreOverCompletionFractionField
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

noncomputable section

open Limits

namespace GlobalTheory.LieLatGen

theorem exists_isLieBasis_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)), ∃ v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G), IsLieBasis v' ∧ ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK t' n'
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have hm : IsGrpPullback t₀.G B.t.G (spMap (algebraMap (𝓞 K) K)) m2.φ := m2.cart
  have hn : IsGrpPullback t'.G t₀.G (spMap iK) n'.φ := n'.cart
  have hc : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) := hn.comp hm
  have w : (n'.φ ≫ m2.φ) ≫ B.t.G.hom = (t'.G.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hc.1.w, Category.assoc]
  have hq : IsGrpPullback t'.G F.P₀.A (spMap iK) (hF.1.lift _ _ w) :=
    IsGrpPullback.cancel hF (hc.congr rfl (hF.1.lift_fst _ _ w).symm) (hF.1.lift_snd _ _ w)
  have := F.P₀.isAb.comm
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange K T.Fr iK _ _ _ hq F.P₀.isAb.smooth _ F.v F.basis
  refine ⟨v', hb, fun k => ?_⟩
  rw [← hF.1.lift_fst _ _ w, ← Category.assoc, hv' k, Category.assoc]
  rfl

end GlobalTheory.LieLatGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearHomPowEqOfKillsComplexTorsion
section
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DivisibleLinear

variable {S S' : Scheme.{0}}

theorem eq_one_iff {G T : Over S} [GrpObj G] (z : T ⟶ G) : z = 1 ↔ z.left = T.hom ≫ η[G].left := by
  have hu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  constructor
  · rintro rfl
    rw [Hom.one_def, Over.comp_left, hu]
  · intro h
    apply Over.OverMorphism.ext
    rw [h, Hom.one_def, Over.comp_left, hu]

section BaseChange

variable {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'}
    (h : Out.toBase hg.w x = Out.toBase hg.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hg.hom_ext
  · simpa [Out.toBase] using congrArg (·.left) h
  · rw [Over.w x, Over.w y]

variable (hg : IsPullback g G'.hom G.hom f)
  (hm : ∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hg.w (x * y) = Out.toBase hg.w x * Out.toBase hg.w y)
include hm

theorem toBase_one (T : Over S') : Out.toBase hg.w (1 : T ⟶ G') = 1 := by
  have h := hm T 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.mp h.symm

theorem toBase_pow {T : Over S'} (x : T ⟶ G') (n : ℕ) : Out.toBase hg.w (x ^ n) = Out.toBase hg.w x ^ n := by
  induction n with
  | zero => simpa using toBase_one hg hm T
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]

end BaseChange

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem torsion_comp_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (P Q : Out.PolAV (Sp (𝓞 K))) (ψ : P.A ⟶ Q.A) [IsMonHom ψ] (n : ℕ) (hn : 0 < n)
    (h : ∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, u ^ n = 1 → u ≫ ψ = 1)
    (T : Over (Sp (𝓞 K))) (x : T ⟶ P.A) (hx : x ^ n = 1) : x ≫ ψ = 1 := by
  set gc : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K) with hgc
  set t : Sp ℂ ⟶ Sp (𝓞 K) := spMap gc with ht
  have hgci : Function.Injective gc :=
    σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨P', gA, hgA, -, hmA, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t P
  obtain ⟨Q', gB, hgB, -, hmB, -⟩ := hL.polBaseChange (Sp (𝓞 K)) (Sp ℂ) t Q
  have := Q.isAb.proper
  have := Q'.isAb.proper

  let ψ' : P'.A ⟶ Q'.A := Over.homMk (hgB.lift (gA ≫ ψ.left) P'.A.hom
    (by rw [Category.assoc, Over.w ψ, hgA.w])) (hgB.lift_snd _ _ _)
  have tb : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A),
      Out.toBase hgB.w (y ≫ ψ') = Out.toBase hgA.w y ≫ ψ := by
    intro T' y
    apply Over.OverMorphism.ext
    simp [Out.toBase, ψ']
  have : IsMonHom ψ' := GlobalTheory.DivisibleHom.isMonHom_of_mul_points ψ' fun T' y₁ y₂ =>
    toBase_injective hgB (by rw [tb, hmA, MonObj.mul_comp, hmB, tb, tb])

  have hC : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, y ^ n = 1 → y ≫ ψ' = 1 := by
    intro y hy
    let e : Over.mk t ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ t) := Over.homMk (𝟙 _) (by simp)
    have h1 : (e ≫ Out.toBase hgA.w y) ^ n = 1 := by
      rw [← MonObj.comp_pow, ← toBase_pow hgA hmA, hy, toBase_one hgA hmA, MonObj.comp_one]
    have h2 := h _ h1
    apply toBase_injective hgB
    rw [tb, toBase_one hgB hmB, eq_one_iff]
    have h3 := (eq_one_iff _).1 h2
    simpa [e] using h3
  obtain ⟨α, hα, hfac⟩ := GlobalTheory.HolUnifEnd.exists_factor_pow P'.A Q'.A P'.isAb n hn ψ' hC
  have kill' : ∀ (T' : Over (Sp ℂ)) (y : T' ⟶ P'.A), y ^ n = 1 → y ≫ ψ' = 1 := by
    intro T' y hy
    rw [← hfac, ← Category.assoc, MonObj.comp_pow, Category.comp_id, hy, MonObj.one_comp]

  obtain ⟨_, hfl, _, _, -⟩ := hL.mulN (Sp (𝓞 K)) P n hn
  let Z := pullback (Out.mulA P.A n) η[P.A]
  let inc : Z ⟶ P.A := pullback.fst (Out.mulA P.A n) η[P.A]
  have hinc : inc ^ n = 1 := by
    rw [← GlobalTheory.DivisibleHom.comp_mulA, pullback.condition, Hom.one_def,
      toUnit_unique (pullback.snd (Out.mulA P.A n) η[P.A]) (toUnit Z)]
  have hp := (IsPullback.of_hasPullback (Out.mulA P.A n) η[P.A]).map (Over.forget (Sp (𝓞 K)))
  have hf : Flat (pullback.snd (Out.mulA P.A n) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hfl
  have hw : (pullback.snd (Out.mulA P.A n) η[P.A]).left = Z.hom := by
    simpa using Over.w (pullback.snd (Out.mulA P.A n) η[P.A])
  rw [hw] at hf
  have hx' : x ≫ Out.mulA P.A n = toUnit T ≫ η[P.A] := by
    rw [GlobalTheory.DivisibleHom.comp_mulA, hx, Hom.one_def]
  suffices hZ : inc ≫ ψ = 1 by
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ ψ = 1
    rw [hZ, MonObj.comp_one]
  rw [eq_one_iff]
  refine GlobalTheory.ArcDataDescent.ext_of_injective hgci (IsPullback.of_hasPullback Z.hom t) Q.A.hom ?_ ?_
  · simp
  · let π := pullback.fst Z.hom t
    let p' := pullback.snd Z.hom t
    let w := hgA.lift (π ≫ inc.left) p' (by rw [Category.assoc, Over.w inc, pullback.condition])
    let x' : Over.mk p' ⟶ P'.A := Over.homMk w (hgA.lift_snd _ _ _)
    let πZ : Over.mk (p' ≫ t) ⟶ Z := Over.homMk π pullback.condition
    have hb : Out.toBase hgA.w x' = πZ ≫ inc := by
      apply Over.OverMorphism.ext
      simp [Out.toBase, x', w, πZ]
    have hx'n : x' ^ n = 1 := by
      apply toBase_injective hgA
      rw [toBase_pow hgA hmA, hb, ← MonObj.comp_pow, hinc, MonObj.comp_one, toBase_one hgA hmA]
    have k2 := congrArg (Out.toBase hgB.w) (kill' _ x' hx'n)
    rw [tb, toBase_one hgB hmB, hb, eq_one_iff] at k2
    simp only [Over.comp_left] at k2 ⊢
    rw [pullback.condition_assoc]
    simpa [πZ] using k2

end GlobalTheory.DivisibleLinear

namespace GlobalTheory.DivisibleLinear

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K)))
    (ψ : A.t.G ⟶ B.t.G), GlobalTheory.Serre.IsLinearHom A.t.act B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ u : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, u ^ n = 1 → u ≫ ψ = 1) →
    ∃ χ : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act χ ∧ χ ^ n = ψ := by
  intro E _ _ _ H K _ _ σ A B ψ hψ n hn hk
  have := hψ.isMonHom
  have hker := torsion_comp_eq_one σ A.pol B.pol ψ n hn hk
  obtain ⟨⟨χ, hχ, hχψ⟩, -⟩ := GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one
    (fun S _ P m hm => by
      obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN S P m hm
      exact ⟨h1, h2, h3, h4⟩)
    (Sp (𝓞 K)) A.pol B.t.G n hn ψ hψ.isMonHom hker
  refine ⟨χ, ⟨hχ, fun c => ?_⟩, hχψ.symm⟩
  have := B.t.act.hom c
  have := A.t.act.hom c
  obtain ⟨_, hfl, hsu, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp (𝓞 K)) A.pol n hn
  have : Flat (Out.mulA A.t.G n).left := hfl
  have : Surjective (Out.mulA A.t.G n).left := hsu
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (Out.mulA A.t.G n)
  rw [GlobalTheory.DivisibleHom.mulA_comp, GlobalTheory.DivisibleHom.mulA_comp, ← MonObj.comp_pow, ← hχψ, hψ.comm c, hχψ,
    MonObj.pow_comp]

end GlobalTheory.DivisibleLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLiftPreservingAppellHumbertForm
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LieGramLift

theorem exists_lift : ∀ (Q P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (u' : HolUnif P.A P.L g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (f : Q.A ⟶ P.A), IsMonHom f → LBIso (lbPow (P.L.pull f.left) 1) (lbPow Q.L 1) → ∀ (n : ℕ) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (Wc : Fin n → Fin Q.g → ℂ), (∀ i, IsTangent (v' i) ∧ u.IsDiff (Wc i) (v' i)) → ∀ (m : ℕ) (a : Fin m → Fin n → ℂ) (tv : Fin m → (epsR ℂ ⟶ P.A)) (Xv : Fin m → Fin g → ℂ), (∀ i, u'.IsDiff (Xv i) (tv i)) → (∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (a i) v' q → q ≫ f = tv i) → ∃ L : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x x', hermForm Hm' (L x) (L x') = hermForm Hm x x') ∧ ∀ i, L (∑ k, a i k • Wc k) = Xv i := by
  intro Q P g u Hm χ u' Hm' χ' hu hu' f hf hL n v' Wc hv m a tv Xv htv hq
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all P g u' Hm' χ' hu'
  obtain ⟨F, hF, -, hFd, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A P.A Q.isAb P.isAb Q.L P.L Q.g g u u'
    h1 h2 f hf
  refine ⟨F, fun x x' => ?_, fun i => ?_⟩
  · have := GlobalTheory.hermForm_pull_eq_of_lbIso_pow Q.A P.A Q.L P.L Q.isLB P.isLB Q.g g u u' Hm χ Hm' χ' hu hu' f F hF 1 1 hL x x'
    simpa using this
  · have hc : IsLieComb (a i) v' (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (a i) v') :=
      (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff (a i) v' _).2 rfl
    have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb Q.A Q.L Q.g n u Wc v' (a i) _
      (fun k => (hv k).1) (fun k => (hv k).2) hc
    have ht := GlobalTheory.HermHom.isTangent_of_isLieComb u (fun k => (hv k).1) (fun k => (hv k).2) hc
    obtain ⟨ht', hd'⟩ := hFd _ _ ht hd
    rw [hq i _ hc] at ht' hd'
    obtain ⟨w, -, hw⟩ := h1 (tv i) ht'
    exact (hw _ hd').trans (hw _ (htv i)).symm

end GlobalTheory.LieGramLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => GlobalTheory.RatDarboux.exists_rational_darboux _ B X Y r s r' s' hB hX hY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdelesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  first | exact @GlobalTheory.RatDarboux.exists_rational_darboux | exact GlobalTheory.RatDarboux.exists_rational_darboux | (intros; apply GlobalTheory.RatDarboux.exists_rational_darboux <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelHalfChainNumbersAnyLevelPrimeStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime : ∀ CY : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) [_root_.NumberField.IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu = 1 → cst.sharp = true → I.Ok Ch sel mu cst G (N.R.m - 2) → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Reads N eJ δ (Pr.T u) R → KerSide R (InfinitePlace X.K) C (FactorBounds (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) fun l => (eJ l).1) := by
  first | exact @GlobalTheory.KernelHalfS.kerSide_chainS | exact GlobalTheory.KernelHalfS.kerSide_chainS | (intros; apply GlobalTheory.KernelHalfS.kerSide_chainS <;> assumption)
end

