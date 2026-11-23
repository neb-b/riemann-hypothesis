module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantFor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProperCover

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem evaluation_genericPoint_injective (X : Scheme.{0}) [IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V) : Function.Injective (X.evaluation V (genericPoint X) hV) := by
  intro a b h
  apply germ_injective_of_isIntegral X _ hV
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  apply φ.injective
  exact h

theorem dim_le_of_residueDegree_pos {Z' Z : Scheme.{0}} [IsIntegral Z'] [IsIntegral Z]
    [IsLocallyNoetherian Z] (f : Z' ⟶ Z) [LocallyOfFiniteType f]
    (hg : f (genericPoint Z') = genericPoint Z) (hdeg : 0 < f.residueDegree (genericPoint Z')) :
    topologicalKrullDim Z' ≤ topologicalKrullDim Z := by
  have hd : ∀ {X : Scheme.{0}} (U : X.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := fun {X} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 Z'.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le Z (U : Set Z))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Z, U) Γ(Z', V) := f.finiteType_appLE hU hV hVU
  have hηV : genericPoint Z' ∈ V :=
    ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : f (genericPoint Z') ∈ U := hVU hηV
  letI := (Z.evaluation U _ hyU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := isFractionRing_evaluation Z hU hg hyU
  have : Algebra.IsAlgebraic Γ(Z, U) (Z.residueField (f (genericPoint Z'))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Z, U))
  have : Module.Finite (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z')) :=
    Module.finite_of_finrank_pos hdeg
  have : Algebra.IsAlgebraic Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    Algebra.IsAlgebraic.trans Γ(Z, U) (Z.residueField (f (genericPoint Z'))) _
  have hnat : f.appLE U V hVU ≫ Z'.evaluation V _ hηV =
      Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z') := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  let ψ : Γ(Z', V) →ₐ[Γ(Z, U)] Z'.residueField (genericPoint Z') :=
    { (Z'.evaluation V _ hηV).hom with
      commutes' := fun a => RingHom.congr_fun congr($(hnat).hom) a }
  have hψ : Function.Injective ψ := evaluation_genericPoint_injective Z' V hηV
  have hinj : Function.Injective (algebraMap Γ(Z, U) Γ(Z', V)) := by
    have h1 : Function.Injective (algebraMap Γ(Z, U) (Z'.residueField (genericPoint Z'))) := by
      rw [IsScalarTower.algebraMap_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
        (Z'.residueField (genericPoint Z'))]
      exact (f.residueFieldMap (genericPoint Z')).hom.injective.comp (IsFractionRing.injective Γ(Z, U) _)
    intro a b h
    apply h1
    rw [← ψ.commutes, ← ψ.commutes, h]
  have : FaithfulSMul Γ(Z, U) Γ(Z', V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.IsAlgebraic Γ(Z, U) Γ(Z', V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact GlobalTheory.ModelDom.ringKrullDim_le_of_isAlgebraic _ _

end GlobalTheory.ProperCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterSpaceCoordsIffLevelActsByCharStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  intro K _ _ _ S G _ _ r P ψ f
  constructor
  · rintro ⟨x, rfl⟩ p
    have h1 : (S.lvlE r P ψ).mulVec x ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := ⟨x, rfl⟩
    rw [(image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2, level_part_spec K S G r P ψ] at h1
    have hz := h1 p
    have h4 := S.I_actMat r (p : G) ((S.lvlE r P ψ).mulVec x)
    rw [hz, map_smul, CSD.I_apply] at h4
    apply Subtype.ext
    rw [← h4]
    rfl
  · intro hf
    have hI : Function.Injective S.I := by
      intro a b h
      rw [CSD.I_apply, CSD.I_apply] at h
      exact S.basis.equivFun.symm.injective (Subtype.ext h)
    have hzf : S.basis.equivFun.symm (S.basis.equivFun f) = f := S.basis.equivFun.symm_apply_apply f
    have hz : ∀ p : P, (S.actMat r (p : G)).mulVec (S.basis.equivFun f) =
        ((ψ p : Kˣ) : K) • S.basis.equivFun f := by
      intro p
      apply hI
      rw [S.I_actMat r (p : G) _, map_smul, CSD.I_apply, hzf, hf p]
      rfl
    have h1 : S.basis.equivFun f ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := by
      rw [(image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2, level_part_spec K S G r P ψ]
      exact hz
    obtain ⟨x, hx⟩ := h1
    refine ⟨x, ?_⟩
    have hx' : (S.lvlE r P ψ).mulVec x = S.basis.equivFun f := hx
    rw [hx', hzf]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelRowsReadingEmbeddingGoodRowsModelWithNorm
section
namespace MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace CompanionTheory.Member.InnerProductScaling

theorem isMultiplicityInner_smul_measure {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * a) := by
  intro v v'
  obtain ⟨h1, h2⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at h1 ⊢
    rw [Measure.restrict_smul]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal hc, Complex.real_smul, mul_assoc]

theorem ipM_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * a := by
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  have h' := isMultiplicityInner_smul_measure M μ 𝓕 T T' c hc a h
  exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, h'⟩) h'

theorem main {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (H : HMod (MMap M)) (W W0 : Submodule ℂ (MMap M)) (hW : W ≤ W0)
    (hH : H.Is W0 (ipM M μ 𝓕)) (n : ℝ) (hn : 0 < n)
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    (j : EE ≃ₗ[ℂ] (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap))
    (hj : HilbTie (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap)
      (ipMT M (ENNReal.ofReal n⁻¹ • μ) 𝓕) j) :
    ∃ eE : EE →ₗ[ℂ] H.H, LinearMap.range eE = W.comap H.e ∧ (∀ x, ‖eE x‖ ^ 2 = n * ‖x‖ ^ 2) ∧
      ∀ x, ((j x : W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap) : AmbT M) =
        PiTensorProduct.lift (H.e (eE x)) := by
  let L : MMap M ≃ₗ[ℂ] AmbT M := PiTensorProduct.lift
  let f : EE →ₗ[ℂ] MMap M := L.symm.toLinearMap ∘ₗ (W.map L.toLinearMap).subtype ∘ₗ j.toLinearMap
  have hf : ∀ x, f x = L.symm (j x : AmbT M) := fun _ => rfl
  have hfW : ∀ x, f x ∈ W := fun x => by
    obtain ⟨y, hy, e⟩ := (j x).2
    have e' : L y = (j x : AmbT M) := e
    rw [hf, ← e', L.symm_apply_apply]
    exact hy
  obtain ⟨g, hg⟩ := GlobalTheory.Mem.Th.exists_factor H.e hH.1 f fun x => by
    rw [hH.2.1]; exact hW (hfW x)
  refine ⟨g, ?_, fun x => ?_, fun x => ?_⟩
  · ext u
    constructor
    · rintro ⟨x, rfl⟩
      show H.e (g x) ∈ W
      rw [hg]; exact hfW x
    · intro hu
      refine ⟨j.symm ⟨L (H.e u), Submodule.mem_map_of_mem hu⟩, hH.1 ?_⟩
      rw [hg, hf, j.apply_symm_apply]
      exact L.symm_apply_apply _
  · have h1 : IsMultIP M μ 𝓕 (H.e (g x)) (H.e (g x)) (1 * ⟪g x, g x⟫_ℂ) :=
      GlobalTheory.Mem.Th.isMultiplicityInner_mul_inner H.e one_ne_zero (fun a b => by rw [one_mul]; exact (hH.2.2 a b).symm) _ _
    have h2 := ipM_smul M μ 𝓕 _ _ n⁻¹ (inv_pos.2 hn).le _ h1
    have h3 : ⟪x, x⟫_ℂ = ipM M (ENNReal.ofReal n⁻¹ • μ) 𝓕 (f x) (f x) := hj x x
    rw [← hg, h2, one_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ‖x‖ ^ 2 = n⁻¹ * ‖g x‖ ^ 2 := by
      have h5 : ((‖x‖ ^ 2 : ℝ) : ℂ) = ((n⁻¹ * ‖g x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact h3
      exact Complex.ofReal_injective h5
    rw [h4, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  · rw [hg, hf]
    exact (L.apply_symm_apply _).symm

end CompanionTheory.Member.InnerProductScaling

theorem CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop b EE _ _ _ X I hE hj
  exact CompanionTheory.Member.InnerProductScaling.main (R.MY 0) R.ν0 R.fd0 R.HE (R.EEat (R.levR F b)) (R.EEat R.triv)
    (GlobalTheory.Mem.Th.EEat_le_triv R _) hE (RealDat.nP F b) (RealDat.nP_pos b) I.jE hj

end

end MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
theorem _root_.GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  first | exact @MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | exact MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | (intros; apply MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLabelPartFinrankEqRowsPartFinrankStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLabelPart_finrank_eq_rowsPart_finrank : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Module.finrank ℂ ((R.Wp3 i p).comap (Y.mj.eW i)) = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  first | exact @GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 | exact GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 | (intros; apply GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajAtSmulRightOf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetBase

open Formalism.HermitianLatticesTheory

section Polar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fcoord_smul_emb (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i; simp [vecAt, map_mul]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem fcoord_add_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i; simp [vecAt, map_add (f := _)]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem majAt_add_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x x' y : V) : majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  simp only [majAt, fcoord_add_of b X v x x', Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem majAt_add_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y y' : V) : majAt b X v x (y + y') = majAt b X v x y + majAt b X v x y' := by
  simp only [majAt, fcoord_add_of b X v y y', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_smul_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v x (a • y) = v.embedding a * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_self_eq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    majAt b X v x x = (((normAt b X v x) ^ 2 : ℝ) : ℂ) := by
  unfold normAt cnorm majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem majAt_eq_of_diag {V' ι' : Type} [AddCommGroup V'] [Module K V'] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Module.Basis ι' K V')
    (X' : InfinitePlace K → Matrix ι' ι' ℂ) (v : InfinitePlace K) (e : V' →ₗ[K] V)
    (hv : ∃ a : K, star (v.embedding a) ≠ v.embedding a)
    (h : ∀ x, majAt b X v (e x) (e x) = majAt b' X' v x x) (x y : V') :
    majAt b X v (e x) (e y) = majAt b' X' v x y := by
  have hadd : ∀ x y : V', (majAt b X v (e x) (e y) - majAt b' X' v x y) +
      (majAt b X v (e y) (e x) - majAt b' X' v y x) = 0 := by
    intro x y
    have h0 := h (x + y)
    have h1 := h x
    have h2 := h y
    simp only [map_add (f := _), majAt_add_left_of, majAt_add_right_of] at h0
    linear_combination h0 - h1 - h2
  obtain ⟨a, ha⟩ := hv
  have h3 := hadd x (a • y)
  simp only [map_smul, majAt_smul_left_of, majAt_smul_right_of] at h3
  have h4 := hadd x y
  have h5 : (v.embedding a - star (v.embedding a)) * (majAt b X v (e x) (e y) - majAt b' X' v x y) = 0 := by
    linear_combination h3 - star (v.embedding a) * h4
  have h6 : v.embedding a - star (v.embedding a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left h6)

end Polar

theorem exists_nonreal {K : Type} [Field K] (v : InfinitePlace K) (hv : v.IsComplex) :
    ∃ a : K, star (v.embedding a) ≠ v.embedding a := by
  by_contra hc
  push_neg at hc
  apply InfinitePlace.not_isReal_iff_isComplex.2 hv
  rw [InfinitePlace.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact hc a

end GlobalTheory.Mem.R3.MetBase

namespace GlobalTheory.Mem.R3.MetBase


set_option maxHeartbeats 2000000 in
theorem metric_base_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s0Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH x y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr false := (hCx.what₂ false).1
  have hE : R.models_HE := hP.char.base.models.HE
  have hn : 0 < RealDat.nP F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hv0 : A3.A.v0 = InfinitePlace.mk D.what₂.embLL := R.hv0
  have hcx : ∃ a : D.what₂.LL, star (A3.A.v0.embedding a) ≠ A3.A.v0.embedding a := by
    haveI := (GlobalTheory.ptField_main D).1
    exact exists_nonreal _ (IsTotallyComplex.isComplex _)
  refine majAt_eq_of_diag _ _ _ _ _ Z.eRR0.toLinearMap hcx ?_ x y
  intro x
  have hR := PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr false h2 hn x x

  set w := (R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding x) with hw
  set z := X0.s.jEE (Z.eRR0 x) with hz
  set u : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) w with hu
  have hjE := Z.jEE0 x
  rw [← hz] at hjE
  change _ = PiTensorProduct.lift (R.HE.e u) at hjE
  have hee := Y.tied.base.ee z z
  have hnorm := X0.s.jEE_norm (Z.eRR0 x)
  have hL : Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) = ⟪z, z⟫_ℂ := by
    rw [majAt_self_eq, hv0, hnorm, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hK : ⟪z, z⟫_ℂ = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
    by_cases hT : R.HE.e (u) = 0
    · have h0 : u = 0 := hE.1 (hT.trans (map_zero _).symm)
      have hz0 : Y.Iz.jE z = 0 := by
        apply Subtype.ext
        rw [hjE, hT, map_zero]
        rfl
      have hz1 : z = 0 := Y.Iz.jE.map_eq_zero_iff.1 hz0
      rw [hz1, h0]
      simp
    · obtain ⟨v, hv⟩ := GlobalTheory.KapRedII.exists_vec_of_ne hT
      rw [hee]
      show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.ν0) R.fd0 _ _ = _
      rw [hjE, ipMT, LinearEquiv.symm_apply_apply, GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ (inv_pos.2 hn) v hv, ← hE.2.2]
  change Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XE F.cr false) A3.fam3.base3.v0 x x
  rw [hL, hK, hR]
  have hc : ∀ (s : Bool) (c : ℂ), starRingEnd ℂ c = c → Formalism.IndefR.Links.cj s c = c := by
    intro s c h
    cases s <;> simp [Formalism.IndefR.Links.cj, h]
  change _ = _ * Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) ⟪u, u⟫_ℂ
  rw [hc _ _ (inner_conj_symm u u)]
  rfl

end GlobalTheory.Mem.R3.MetBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapSingleAtEmb
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.OneRep

variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [NumberField.IsTotallyComplex E] in
theorem atEmb_zero (τ : E →+* ℂ) : atEmb τ 0 = 0 := by
  classical
  unfold atEmb; split_ifs <;> simp


omit [NumberField E] [NumberField.IsTotallyComplex E] in
theorem map_single_atEmb (τ : E →+* ℂ) (i k : Fin a) (z : ℂ) :
    (Matrix.single i k z).map (atEmb τ) = Matrix.single i k (atEmb τ z) := by
  ext p q
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [atEmb_zero]

end GlobalTheory.OneRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantForStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceTransvection_acts_positively_invariant_forms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ ξ, IsoVec T ξ → ∀ e, IsSplitIdem D e → ∀ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z → ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) → ∀ f, IsThetaFunO ψ S T f → ℓ (om (1, z) f) = (r : ℂ) * ℓ f := by
  first | exact @GlobalTheory.SplitTransvection.transvection_pos | exact GlobalTheory.SplitTransvection.transvection_pos | (intros; apply GlobalTheory.SplitTransvection.transvection_pos <;> assumption)
end

