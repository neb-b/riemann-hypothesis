module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfFlatOfMapComapMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (V : Type) [CommRing V]
    [IsRegularLocalRing V] (I : Type) [Fintype I] (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (φ : MvPolynomial I V →+* S) (hflat : φ.Flat)
    (hmap : ((maximalIdeal S).comap φ).map φ = maximalIdeal S) : IsRegularLocalRing S := by
  haveI : IsRegularRing V := GlobalTheory.isRegularRing_of_isRegularLocalRing V
  set q : Ideal (MvPolynomial I V) := (maximalIdeal S).comap φ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime φ (maximalIdeal S)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let χ : L →+* S := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I V) S := φ.toAlgebra
  letI : Algebra L S := χ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I V) L S := IsScalarTower.of_algebraMap_eq (fun a => by
    change φ a = χ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I V) S := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S) :=
    isLocalizedModule_id q.primeCompl S L
  haveI : Module.Flat L S :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S)
  have hm : maximalIdeal S = (maximalIdeal L).map (algebraMap L S) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L S (maximalIdeal L) hm

theorem isRegularLocalRing_quotient_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      ∀ 𝔭 : Ideal W, 𝔭 ≠ ⊤ → IsRegularLocalRing (W ⧸ 𝔭) →
        IsRegularLocalRing (R ⧸ 𝔭.map (ψ.comp MvPolynomial.C)) := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc 𝔭 h𝔭 hreg
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsNoetherianRing R := hnoeth
  haveI : IsRegularLocalRing (W ⧸ 𝔭) := hreg
  rw [← Ideal.map_map]
  set J : Ideal R := (Ideal.map MvPolynomial.C 𝔭).map ψ with hJ
  have hJm : J ≤ maximalIdeal R := by
    rw [hJ, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact h𝔭 (Ideal.eq_top_of_isUnit_mem _ hx (isUnit_of_map_unit _ _ hu))
  haveI : Nontrivial (R ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJm)
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := I) 𝔭
  have heC : ∀ a : W, e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a)) = Ideal.Quotient.mk _ (MvPolynomial.C a) := by
    intro a; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  have heX : ∀ i : I, e (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
    intro i; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  let ψ' : MvPolynomial I (W ⧸ 𝔭) →+* R ⧸ J :=
    (Ideal.quotientMap J ψ Ideal.le_comap_map).comp e.toRingEquiv.toRingHom
  have hflat' : ψ'.Flat :=
    (RingHom.Flat.of_bijective e.bijective).comp (GlobalTheory.Pat.flat_quotientMap_map ψ hflat _)
  let π : MvPolynomial I W →+* MvPolynomial I (W ⧸ 𝔭) := MvPolynomial.map (Ideal.Quotient.mk 𝔭)
  have hcomm : ψ'.comp π = (Ideal.Quotient.mk J).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, π, MvPolynomial.map_C, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a))) = _
      rw [heC, Ideal.quotientMap_mk]
    · intro i
      simp only [RingHom.comp_apply, π, MvPolynomial.map_X, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.X i)) = _
      rw [heX, Ideal.quotientMap_mk]
  have hmax : maximalIdeal (R ⧸ J) = (maximalIdeal R).map (Ideal.Quotient.mk J) := by
    exact (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  refine isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (W ⧸ 𝔭) I (R ⧸ J) ψ' hflat' ?_
  refine le_antisymm Ideal.map_comap_le ?_
  have h1 : maximalIdeal (R ⧸ J) = (((maximalIdeal R).comap ψ).map π).map ψ' := by
    rw [hmax, Ideal.map_map, hcomm, ← Ideal.map_map, hmap]
  refine h1.le.trans (Ideal.map_mono ?_)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  apply Ideal.comap_mono
  rw [hmax]
  exact Ideal.le_comap_map

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isSymCoc_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  intro R _ A _ hA f g hfg
  have hc : IsCommMonObj A := hA.comm
  unfold IsSymCoc
  unfold IsAdd at hfg
  intro D _ _
  constructor
  · let k : Fn0 (A ⊗ A) := fun E _ _ w ↦
      g E (w ≫ fst A A) (w ≫ snd A A) - g E (w ≫ snd A A) (w ≫ fst A A)
    have hk : IsCob (whole (A ⊗ A)) (Fn1.zero (A ⊗ A)) k := by
      unfold IsCob
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ fst A A) (w ≫ snd A A)
      have h2 := hfg E E' φ (w ≫ snd A A) (w ≫ fst A A)
      rw [mul_comm (w ≫ snd A A) (w ≫ fst A A)] at h2
      simp only [k, Fn1.zero, Category.assoc, map_sub]
      linear_combination h2 - h1
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.PtExt.NatConst.const_of_natural R (A ⊗ A) Unit (whole (A ⊗ A)) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ A)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 k hk
    intro x y
    have e1 := hr D (lift x y) (sm_whole _)
    have e0 := hr D (lift 1 1) (sm_whole _)
    simp only [k, lift_fst, lift_snd, sub_self] at e0 e1
    exact sub_eq_zero.mp (e1.trans e0.symm)
  · let k : Fn0 (A ⊗ (A ⊗ A)) := fun E _ _ w ↦
      g E (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
        - g E ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
        + g E (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
        - g E (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
    have hk : IsCob (whole (A ⊗ (A ⊗ A))) (Fn1.zero _) k := by
      unfold IsCob
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
      have h2 := hfg E E' φ ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
      have h3 := hfg E E' φ (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
      have h4 := hfg E E' φ (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
      rw [_root_.mul_assoc] at h2
      simp only [MonObj.comp_mul] at h2 h3
      simp only [k, Fn1.zero, Category.assoc, map_sub, map_add (f := _), MonObj.comp_mul]
      linear_combination h2 - h1 - h3 + h4
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.PtExt.NatConst.const_of_natural R (A ⊗ (A ⊗ A)) Unit (whole _) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ (A ⊗ A))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A (A ⊗ A) hA
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA))).2 k hk
    intro x y z
    have e1 := hr D (lift x (lift y z)) (sm_whole _)
    have e0 := hr D (lift 1 (lift 1 1)) (sm_whole _)
    simp only [k, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, _root_.mul_one, sub_self, add_sub_cancel_right,
      sub_add_cancel] at e0 e1
    rw [← e0] at e1
    exact e1

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechKS.isTangent_of_fibre : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  intro E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a

  have hunit : η[A].left ≫ m = x0 ≫ η[t.G].left := by
    have hw : (η[A].left ≫ m) ≫ t.G.hom = (𝟙_ (Over (Sp K))).hom ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w η[A]]
    let p : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk (η[A].left ≫ m) hw
    have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    have hpp := hm.2 (𝟙_ (Over (Sp K))) 1 1 p p (by rw [h1]; rfl) (by rw [h1]; rfl)
    rw [_root_.mul_one, h1] at hpp
    have hp : p * p = p := Over.OverMorphism.ext hpp
    have hp1 : p = 1 := mul_eq_left.mp hp
    have := congrArg (fun q => q.left) hp1
    simp only [p, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom] at this
    rw [this]
    simp
  show spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (u a).left = η[A].left
  apply hm.1.hom_ext
  · rw [Category.assoc, hu a, hunit, ← Category.assoc, ← Spec.map_comp]
    have hr : CommRingCat.ofHom (dualMap (ev x0 U.1 hU)) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ CommRingCat.ofHom (ev x0 U.1 hU) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp [dualMap, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
    rw [hr, Spec.map_comp, Category.assoc, (hv a).2, Hom.one_def, Over.comp_left, Over.toUnit_left,
      ← Category.assoc]
    congr 1
    exact GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  · rw [Category.assoc, Over.w (u a), Over.w η[A]]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    show _ = 𝟙 (Sp K)
    rw [← Spec.map_id]
    congr 1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtFibreSpreadModelAtFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (j : B →+* C) :
    spMap j ≫ spMap f = spMap (j.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem isThetaPt_fibre : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (m : ℕ) (I : Type) (x : I → (baseOver (Sp Ω) ⟶ A.A)) (y : I → (baseOver (Sp T) ⟶ P.A)) (v : I → F), Odd m → 3 ≤ m → (∀ i, (x i).left ≫ φ = spMap jT ≫ (y i).left) → (∀ i, y i ^ (m ^ 2) = 1) → (∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ m = 1 → ∃ i, ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) ^ m = z) → IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → IsThetaPt P m (fun i => (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v i)) := by
  intro F Ω T _ _ _ _ _ _ _ _ em jT t hft hinj hcomp A P φ hp hw m I x y v hm hm3 hxy hy hcov hA
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  let tR : T →+* F := t.toRingHom
  have htR : ∀ a : F, tR (algebraMap F T a) = a := fun a => t.commutes a
  have hsurj : Function.Surjective tR := fun a => ⟨algebraMap F T a, htR a⟩
  let p : Ideal T := RingHom.ker tR
  haveI hpm : p.IsMaximal := RingHom.ker_isMaximal_of_surjective tR hsurj
  let R := Localization.AtPrime p
  let s : Sp R ⟶ Sp T := spMap (algebraMap T R)
  have hjT : ∀ z : p.primeCompl, IsUnit (jT z) := fun z => by
    refine IsUnit.mk0 _ fun h => z.2 ?_
    have : (z : T) = 0 := hinj (h.trans (map_zero jT).symm)
    rw [this]; exact p.zero_mem
  have htU : ∀ z : p.primeCompl, IsUnit (tR z) := fun z => IsUnit.mk0 _ fun h => z.2 h
  let jR : R →+* Ω := IsLocalization.lift hjT
  let r : R →+* F := IsLocalization.lift htU
  have hjR : jR.comp (algebraMap T R) = jT := IsLocalization.lift_comp hjT
  have hr : r.comp (algebraMap T R) = tR := IsLocalization.lift_comp htU
  have hjRinj : Function.Injective jR := by
    refine (injective_iff_map_eq_zero jR).2 fun z hz => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have hz' := hz
    simp only [jR] at hz'
    rw [IsLocalization.lift_mk', Units.mul_left_eq_zero] at hz'
    show IsLocalization.mk' R a b = 0
    rw [hinj (hz'.trans (map_zero jT).symm), IsLocalization.mk'_zero]
  let aR : F →+* R := (algebraMap T R).comp (algebraMap F T)
  have hjaR : ∀ a, jR (aR a) = em a := fun a => by
    show (jR.comp (algebraMap T R)) (algebraMap F T a) = em a
    rw [hjR, ← hcomp]; rfl
  have hraR : ∀ a, r (aR a) = a := fun a => by
    show (r.comp (algebraMap T R)) (algebraMap F T a) = a
    rw [hr]; exact htR a
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu : IsUnit (m : R) := by
    have := (IsUnit.mk0 (m : F) hmF).map aR
    rwa [map_natCast] at this

  have hmo : ∀ i, ((Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i) ^ (m ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨w, hwR⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local hL hL2 P s hm hu _ hmo

  have e1 : spMap jR ≫ s = 𝟙 (Sp Ω) ≫ spMap jT := by
    rw [Category.id_comp, spMap_comp_spMap, hjR]
  have e2 : spMap r ≫ s = spMap tR := by rw [spMap_comp_spMap, hr]
  have hΩ := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P jR e1 hwR
  have hF := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P r e2 hwR

  let yΩ : I → (Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ P.A) := fun i =>
    (Over.homMk (spMap jR) e1 : Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ Over.mk s) ≫
      (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i
  have hyΩ : ∀ i, (yΩ i).left = (x i).left ≫ φ := fun i => by
    rw [hxy i]
    simp only [yΩ, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, e1, Category.id_comp]
  obtain ⟨eA, heA⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp Ω)) (𝟙 (Sp Ω) ≫ spMap jT) rfl
  have hxo : ∀ i, x i ^ (m ^ 2) = 1 := fun i => by
    apply eA.injective
    rw [map_pow, map_one]
    have : eA (x i) = yΩ i := Over.OverMorphism.ext ((heA (x i)).trans (hyΩ i).symm)
    rw [this]
    simp only [yΩ]
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hy, MonObj.comp_one, MonObj.comp_one]
  have hA' := (GlobalTheory.ThetaPtUp.isThetaPt_iff (T := baseOver (Sp Ω)) (x₀ := yΩ) hp hw hyΩ hxo _).1 hA
  let eΩ : Γ(Sp Ω, ⊤) ≃+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk (𝟙 (Sp Ω) ≫ spMap jT)).left, ⊤) := eΩ.symm.isLocalRing
  obtain ⟨u, hu'⟩ := GlobalTheory.ThetaUniq.exists_unit_over hL.globalFns P hm
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hΩ) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hA')
  let cΩ : Ωˣ := Units.map eΩ.toMonoidHom u
  have hc : ∀ i, em (v i) = (cΩ : Ω) * jR (w i) := fun i =>
    (eΩ.apply_symm_apply (em (v i))).symm.trans (((congrArg eΩ (hu' i)).trans (map_mul eΩ _ _)).trans
      (congrArg (_ * ·) (eΩ.apply_symm_apply (jR (w i)))))

  have hF' : IsThetaPt P m (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i)
      (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i))) := by
    have hpts : (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i) =
        fun i => (Over.homMk (spMap r) e2 : Over.mk (spMap tR) ⟶ Over.mk s) ≫
          (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i := funext fun i => by
      refine Over.OverMorphism.ext ?_
      simp only [Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, e2]
    rw [hpts]
    exact hF
  obtain ⟨z, hz, hne⟩ := GlobalTheory.ThetaCoset.exists_ne_zero_over hL hL2 P (spMap tR) (k := m) (by omega) hmF
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hF') 1
  obtain ⟨i₀, hi₀⟩ := hcov z hz
  have hr0 : r (w i₀) ≠ 0 := fun h => hne i₀ (by rw [_root_.one_mul]; exact hi₀) (by
    show (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i₀)) = 0
    rw [h]; exact map_zero _)

  have hv0 : v i₀ ≠ 0 := fun h => hr0 (by
    have q := hc i₀
    rw [h, map_zero, eq_comm, Units.mul_right_eq_zero] at q
    rw [hjRinj (q.trans (map_zero jR).symm), map_zero])
  have key : ∀ i, w i * aR (v i₀) = w i₀ * aR (v i) := fun i => hjRinj (by
    rw [map_mul, map_mul, hjaR, hjaR, hc, hc]; ring)
  have hrw : ∀ i, r (w i) * v i₀ = r (w i₀) * v i := fun i => by
    have q := congrArg r (key i)
    rwa [map_mul, map_mul, hraR, hraR] at q
  have hd : r (w i₀) / v i₀ ≠ 0 := div_ne_zero hr0 hv0
  have hfin : ∀ i, (r (w i₀) / v i₀)⁻¹ * r (w i) = v i := fun i => by
    rw [inv_div, div_mul_eq_mul_div, div_eq_iff hr0]
    linear_combination hrw i
  have H := GlobalTheory.Ex.Specialise.isThetaPt_mul P hF' (inv_ne_zero hd)
  simp only [hfin] at H
  exact H

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isThetaTerms_of_mul_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  intro V₁ _ _ D N₁ X C _ e T v c₀ h hv
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨(algebraMap V₁ (FractionRing V₁) v) • th, g, b, w, h₁, h₂, h₃, h₄, ?_, ⟨c₀, hv⟩⟩
  intro mu c z J hJ
  have H := h₅ mu c z J hJ
  rw [ReciprocityTheory.ChartRestriction.G.DVR.sval_smul _ _ _ _ z hJ]
  have e₁ : (lift (𝟙 (TF (R := V₁) (FractionRing V₁))) (g c).b).left ≫
      (fst (TF (R := V₁) (FractionRing V₁)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  rw [e₁]
  have e₂ : GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c * v)) =
      GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) v) *
        GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c)) := by
    simp only [GlobalTheory.UT.cst, map_mul]
    rw [gs_mul _ z ⊤ trivial, mul_comm]
  rw [e₂, _root_.mul_assoc, H]
  simp only [GlobalTheory.UT.cst, _root_.mul_assoc]

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsCharTorsVal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {p : ℕ} {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {G : PDivGroup p R}
  (t : PDivGroup.TorsionTower G A) (N : ℕ)


open Classical in
def torsVal (b : G.A N) : Fn0 A := fun _ _ _ x ↦
  if h : x ^ p ^ N = 1 then t.lift N x h b else 0

theorem lift_spOver {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (w : Pt A D) (hw : w ^ p ^ N = 1) (hw' : (spOver φ ≫ w) ^ p ^ N = 1) :
    t.lift N (spOver φ ≫ w) hw' = φ.comp (t.lift N w hw) :=
  t.inj N D' _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.lift_y])

theorem lift_mul {D : Type} [CommRing D] [Algebra R D] (w w' : Pt A D) (hw : w ^ p ^ N = 1)
    (hw' : w' ^ p ^ N = 1) (h : (w * w') ^ p ^ N = 1) :
    t.lift N (w * w') h = (toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv :=
  t.inj N D _ _ (by rw [t.lift_y, t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y])

theorem isTorsChar_torsVal (b : G.A N) (hb : cobOne R (G.A N) b = 0) :
    IsTorsChar (p ^ N) (torsVal t N b) := by
  have hc : Coalgebra.comul (R := R) b = b ⊗ₜ 1 + 1 ⊗ₜ b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb; exact hb
  refine ⟨fun D _ _ D' _ _ φ w hw ↦ ?_, fun D _ _ w w' hw hw' ↦ ?_⟩
  · have hw2 : (spOver φ ≫ w) ^ p ^ N = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    simp only [torsVal, dite_eq_left hw, dite_eq_left hw2, lift_spOver t N φ w hw hw2,
      AlgHom.comp_apply]
  · have h : (w * w') ^ p ^ N = 1 := (t.exists_iff N _).1
      ⟨(toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv, by
        rw [t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y]⟩
    simp only [torsVal, dite_eq_left hw, dite_eq_left hw', dite_eq_left h, lift_mul t N w w' hw hw' h]
    change (toConv (t.lift N w hw) * toConv (t.lift N w' hw')) b = _
    simp only [AlgHom.convMul_apply, hc, map_add, Algebra.TensorProduct.lift_tmul, map_one,
      _root_.mul_one, _root_.one_mul]

theorem exists_isTorsChar :
    ∀ (p : ℕ) (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (G : PDivGroup p R)
      (t : PDivGroup.TorsionTower G A) (N : ℕ) (b : G.A N),
      cobOne R (G.A N) b = 0 → ∃ β : Fn0 A, IsTorsChar (p ^ N) β ∧
        ∀ (D : Type) [CommRing D] [Algebra R D] (φ : G.A N →ₐ[R] D), β D (spOver φ ≫ t.y N) = φ b := by
  intro p R _ A _ G t N b hb
  refine ⟨torsVal t N b, isTorsChar_torsVal t N b hb, fun D _ _ φ ↦ ?_⟩
  have h : (spOver φ ≫ t.y N) ^ p ^ N = 1 := (t.exists_iff N _).1 ⟨φ, rfl⟩
  have e : t.lift N (spOver φ ≫ t.y N) h = φ := t.inj N D _ _ (t.lift_y N _ h)
  simp only [torsVal, dite_eq_left h, e]

end GlobalTheory.PtExt
end
end

