module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAtStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_completion_tensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  first | exact @GlobalTheory.InertTensorField.isField_tensor_of_isInertAt | exact GlobalTheory.InertTensorField.isField_tensor_of_isInertAt | (intros; apply GlobalTheory.InertTensorField.isField_tensor_of_isInertAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lagAt {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  {u | At (evFin F v) u ∧ ∃ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u = z * Cᵀ}

def IsLagrAt (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Prop :=
  IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) W.J) (C.map (compFin F E v))

def HeisInv {σ : E →ₐ[F] E} {n d m : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u ∈ lagAt v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → l φ₁ = l φ

end GlobalTheory.InertVacLag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGL
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistSph

theorem isSpherical_twist_absPow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ), GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a)) →
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
      (CuspSub.isOpen_ker_locDet _ w)).ρ := by
  intro E _ _ _ a w σ s h
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  rw [← hK] at hv
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have h1 : CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w g.1 = 1 := by
    show (GlobalTheory.HeckeGal.Model.absPow E s).loc w (Matrix.GeneralLinearGroup.det g.1) = 1
    rw [GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s) w]
    refine isUnram_absPow _ _ _ ?_
    obtain ⟨u, hu⟩ := g.2
    rw [← hu]
    have h2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation (w.adicCompletion E)).integer (w.adicCompletion E)) u) :
          (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap (ValuativeRel.valuation (w.adicCompletion E)).integer (w.adicCompletion E) u.val.det := by
      rw [RingHom.map_det]; rfl
    rw [h2]
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).1
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  have h3 := hv g
  show ((CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

end GlobalTheory.TwistSph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Inhab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Chr
open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isConjPl_iff_conjPl {w w' : HeightOneSpectrum (𝓞 D.host.E)} :
    Lev.IsConjPl w w' ↔ ConjPl D.host.conj.toRingEquiv w w' := by
  rw [conjPl_iff_smul]
  constructor
  · intro hc
    have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hc _ hy
      have e : z = y := RingOfIntegers.ext
        ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
      exact e ▸ hz
    obtain ⟨v, hv, -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
    have hv' := (conjPl_iff_smul D.host.conj w v).1 hv
    have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
    exact hvw ▸ hv'
  · intro h c hc
    exact ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (bridge_star_holds D.R D.host _).symm⟩

theorem mem_aboveK {P : HeightOneSpectrum (𝓞 D.host.K)} {w : HeightOneSpectrum (𝓞 D.host.E)} :
    w ∈ Formalism.L2.Host.aboveF (L := D.host.E) D.host.K P ↔ w.under (𝓞 D.host.K) = P := by
  simp [Formalism.L2.Host.aboveF]

theorem overP_of_under {p : ℕ} {P : HeightOneSpectrum (𝓞 D.host.K)} (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.K) = P) : Formalism.L2.Host.OverP D.host p w := by
  subst h
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := hP
  rwa [map_natCast] at h2

section One

variable {p : ℕ} (hp : p.Prime) (hs : SplitsC D.host.E p) {P : HeightOneSpectrum (𝓞 D.host.K)}
  (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
include hp hs hP

theorem overP_iff (w : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Host.OverP D.host p w ↔
    w ∈ Formalism.L2.Host.aboveF (L := D.host.E) D.host.K P ∨ ∃ w' ∈ Formalism.L2.Host.aboveF (L := D.host.E) D.host.K P, Lev.IsConjPl w' w := by
  constructor
  · intro hw
    by_cases h : w.under (𝓞 D.host.K) = P
    · exact Or.inl (mem_aboveK.2 h)
    · obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv.symm w
      have hc : ConjPl D.host.conj.toRingEquiv w' w := fun x => by
        have := hw' (D.host.conj.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have ho : Formalism.L2.Host.OverP D.host p w' := ((conjPl_iff_mem _ w' w).1 hc _ _ (by simp)).2 hw
      exact Or.inr ⟨w', mem_aboveK.2 (((splitsC_main D.R D.host p hp hs w' ho).2.2.2 P hP w hc).2.2 h),
        isConjPl_iff_conjPl.2 hc⟩
  · rintro (h | ⟨w', h, hc⟩)
    · exact overP_of_under hP (mem_aboveK.1 h)
    · exact ((splitsC_main D.R D.host p hp hs w' (overP_of_under hP (mem_aboveK.1 h))).2.2.2 P hP w
        (isConjPl_iff_conjPl.1 hc)).1

end One

end GlobalTheory.BigOn.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SkewUnit

theorem isUnit_det_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → IsUnit W.J.det := by
  intro F E _ _ _ _ _ σ B d W r s hW
  exact isUnit_iff_ne_zero.2 (GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B d r s W hW)

end GlobalTheory.SkewUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.VanishNumberField

open GlobalTheory.AbLaw

theorem subsingleton_of_tensor {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
    (h : Subsingleton (TensorProduct k E V)) : Subsingleton V := by
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  exact not_nontrivial_iff_subsingleton.2 h (Module.FaithfullyFlat.lTensor_nontrivial k E V)

theorem subsingleton_coh_of_pull {k E : Type} [Field k] [Field E] [Algebra k E] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X} [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ)
    (h : Subsingleton (coh (twist (structureModule X') (M.pull π)) n)) :
    Subsingleton (coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have cechIso {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      (N : LB Z) {κ : Type} [LinearOrder κ] (U : κ → Z.Opens) :
      letI := algebraΓOfHom g
      cechLB g N U ≅ cech R (LB.toMod N) ⊤ U := by
    letI := algebraΓOfHom g
    exact (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
      (M := SecOnR g N (⨅ i ∈ s, U i)) (M₂ := sectionsOn (LB.toMod N) (⊤ ⊓ ⨅ i ∈ s, U i))
      (SecOnR.restrict g N (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, U i) ≤ ⨅ i ∈ s, U i))
      (SecOnR.restrict_bijective g _ (le_inf le_top le_rfl)))
      fun {s t} ht x => (SecOnR.restrict_restrict g _ inf_le_right x).trans
        (SecOnR.restrict_restrict g inf_le_right (cechOpen_anti ⊤ U ht) x).symm)
  have cohEquiv {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      {N : LB Z} (hN : N.IsLB) {κ : Type} [LinearOrder κ] [Finite κ] {U : κ → Z.Opens}
      (hu : ⨆ i, U i = ⊤) (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (i : ℕ) :
      letI := algebraΓOfHom g
      Nonempty ((cechLB g N U).homology i ≃ₗ[R] coh (twist (structureModule Z) N) i) := by
    letI := algebraΓOfHom g
    haveI := LB.isQuasicoherent_toMod hN
    exact ⟨((HomologicalComplex.homologyFunctor _ _ i).mapIso (cechIso g N U)).toLinearEquiv ≪≫ₗ
      cechHEquivCoh R hu hU (LB.toMod N) i ≪≫ₗ (cohOn.mapIso R ⊤ i (Twist.unitTwistIso N)).symm⟩
  have homologyEquiv {R : Type} (O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O]
      (C : CochainComplex (ModuleCat.{0} R) ℕ) (i : ℕ) :
      Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
        C).homology i ≃ₗ[O] TensorProduct R O (C.homology i)) := by
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
    have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
    obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology i)
    exact ⟨((C.sc i).mapHomologyIso
      (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩
  obtain ⟨e₁⟩ := cohEquiv f hM hc hD' n
  obtain ⟨e₂⟩ := cohEquiv f' (LB.isLB_pull hM π) (U := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := homologyEquiv E (cechLB f M D) n
  have bcIso (g : k →+* E)
      (H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
      ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj (cechLB f M D) ≅
        cechLB f' (M.pull π) (fun i => π ⁻¹ᵁ D i) := by
    letI := g.toAlgebra
    let φ : (secCube f M D ⋙ ModuleCat.extendScalars g) ⟶
        secCube f' (M.pull π) (fun i => π ⁻¹ᵁ D i) :=
      Cube.homMk (Fin m) E (fun s => SecOnR.baseChangeHom M H'.w _ _ (preimage_biInf D π s).ge)
        fun {s t} ht x => SecOnR.baseChangeHom_restrict H'.w (iInf_le_iInf_of_subset D ht)
          (iInf_le_iInf_of_subset (fun i => π ⁻¹ᵁ D i) ht) (preimage_biInf D π s).ge
          (preimage_biInf D π t).ge x
    exact @asIso _ _ _ _ (cechComparison (ModuleCat.extendScalars g) (secCube f M D))
      (isIso_cechComparison _ _) ≪≫
      @asIso _ _ _ _ (cechComplexMap φ)
        (isIso_cechComplexMap _ fun s hs => SecOnR.baseChangeHom_bijective hM H' (hD' s hs) (preimage_biInf D π s).symm)
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (bcIso (algebraMap k E) H)).toLinearEquiv
  have h₁ : Subsingleton (TensorProduct k E ((cechLB f M D).homology n)) :=
    (e₃.symm.toEquiv.trans (e₄.toEquiv.trans e₂.toEquiv)).subsingleton_congr.2 h
  exact e₁.symm.toEquiv.subsingleton_congr.2 (subsingleton_of_tensor h₁)

theorem topologicalKrullDim_eq_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [Nonempty Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y = D := by
  have key : topologicalKrullDim (Set.univ : Set Y) = D := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    replace hU : IsAffineOpen (X := Y) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)
  rw [← key]
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : Y → Y)) Topology.IsEmbedding.id Set.range_id).symm

theorem vanishFrom_adj : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  intro Q K _ _ G hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K (X := G.Y)) := hstr ▸ hV.proj
  haveI : IsProper (strHom K (X := G.Y)) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens G.LA (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens G.LA (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens G.LA (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens G.LA (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (G.isLB_adj j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((G.adj j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (G.isLB_adj j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add (f := _)]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB G.isLBA) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB G.isLBA,
          cls_tens G.isLBA (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (G.adj j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (G.isLB_adj j) q hKV
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (G.isLB_adj j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle G.LA)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

end GlobalTheory.HSCore.VanishNumberField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacianStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ p : Polynomial ℂ, p ≠ 0 → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)) (P : Polynomial ℂ), P.Monic ∧ (∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) → (fun y : glG E a => f (toL y.1.val)) ∈ solG (glH E a) b P) ∧ ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → ∀ x, glRes φ.1 x ∈ solG (glH E a) b P := by
  first | exact @GlobalTheory.HCA.solG_of_polyLap | exact GlobalTheory.HCA.solG_of_polyLap | (intros; apply GlobalTheory.HCA.solG_of_polyLap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeftStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → ∀ M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  exact @GlobalTheory.AdelMatLat.almost_all_stable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open Matrix
namespace GlobalTheory.AdelMatLatRight


open NumberField IsDedekindDomain in
open Matrix in
theorem _root_.GlobalTheory.AdelMatLatRight.transpose_mem_latAtV {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (w : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y w, γᵀ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y X w := by
  intro γ hγ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV at hγ ⊢
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    rw [transpose_smul]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, vecMulVec_apply, mul_comm]
  | zero => simpa using zero_mem _
  | add u v _ _ hu hv => simpa [transpose_add] using add_mem hu hv
  | neg u _ hu => simpa [transpose_neg] using neg_mem hu

theorem almost_all_stable_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), Y.L.IsFullLattice E → ∀ N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hY N
  refine (GlobalTheory.AdelMatLat.almost_all_stable F E d n Y X hY N).subset fun w hw h => hw fun γ hγ => ?_
  have h1 := transpose_mem_latAtV Y X w _ (h _ (transpose_mem_latAtV X Y w γ hγ))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h1

end GlobalTheory.AdelMatLatRight

end
end

