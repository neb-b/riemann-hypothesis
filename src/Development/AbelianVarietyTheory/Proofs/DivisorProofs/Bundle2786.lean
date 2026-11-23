module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfHyp
section
set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_of_crystallineSmoothLift : GlobalTheory.Published.CrystallineSmoothLift →
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  intro hL hH hC hD hP
  obtain ⟨⟨hfree, hhodge, hbc⟩, hcrys⟩ := _root_.GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses hL hH
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hhodge, hbc,
    GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys,
    _root_.GlobalTheory.CubeDual.abelianDeRham_duality hC hD hP hF⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentGradedFamilyNonzero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.DescGraded

theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _

theorem theta_c₀ (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    have e1 : spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) = spMap (Desc.cst (σ.C x).G.hom) ≫ spMap (σ.ρ x) := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc, (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem c₀_mem_W (σ : Setup) (x : Sp σ.R) (r : σ.R) : σ.c₀ r ∈ σ.W x := fun z _ => by
  have := RingHom.congr_fun (theta_c₀ σ x) r
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact regAt_cst _ _ _

theorem W_mul (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a * b ∈ σ.W x := fun z hz => by
  rw [map_mul]; exact (ha z hz).mul (hb z hz)

theorem W_add (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a + b ∈ σ.W x := fun z hz => by
  rw [map_add (f := _)]; exact (ha z hz).add (hb z hz)

theorem sec_mul_left {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) {a b : X.functionField}
    (ha : ∀ x, RegAt x a) (hb : b ∈ Sec D k) : a * b ∈ Sec D k := fun x => by
  obtain ⟨g, hg, h⟩ := hb x
  exact ⟨g, hg, _root_.mul_assoc a b g ▸ (ha x).mul h⟩

theorem finite_height_one {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R} (hf : f ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})).preimage
    (f := fun p : PrimeSpectrum R => p.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro p ⟨hp, hfp⟩
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hfp) ?_
  rw [hp]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf)

theorem c₀_f_ne_zero (σ : Setup) : σ.c₀ σ.f ≠ 0 := by
  have e : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    have e2 : spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) =
        spMap (Desc.cst σ.A.hom) ≫ Desc.awayMap σ.f := by
      rw [← Spec.map_comp]; rfl
    have e : spMap σ.c₀ = spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) := by
      rw [e2, Setup.c₀, spMap_cst, spMap_cst, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e, RingHom.comp_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit σ.f).map _).ne_zero

theorem gradedFam_and_ne_zero : ∀ σ : Setup, GradedFam σ.c₀ σ.N ∧ ∃ k, 1 ≤ k ∧ ∃ b ∈ σ.N k, b ≠ 0 := by
  intro σ
  refine ⟨⟨⟨fun x => ?_, fun x => ?_⟩, fun k => ⟨fun x => ?_, fun x => ?_⟩,
    fun k a ha b hb => ⟨fun x => (ha.1 x).add (hb.1 x), fun x => W_add σ x (ha.2 x) (hb.2 x)⟩,
    fun k r a ha => ⟨sec_mul_left _ _ (fun x => regAt_cst _ x r) ha.1, fun x => W_mul σ x (c₀_mem_W σ x r) (ha.2 x)⟩,
    fun k l a ha b hb => ⟨fun x => ?_, fun x => W_mul σ x (ha.2 x) (hb.2 x)⟩⟩, ?_⟩
  · rw [zero_nsmul]
    exact ⟨1, CartierDiv.isEqn_zero x, by simpa using (unitAt_one x).regAt⟩
  · simpa using c₀_mem_W σ x 1
  · exact (CartierDiv.vanishesAt_zero _ x).regularAt
  · simpa using c₀_mem_W σ x 0
  · rw [add_nsmul]
    exact (ha.1 x).mul (hb.1 x)
  · obtain ⟨k, hk, u, hu, U, -, hU, hx⟩ := σ.amp (genericPoint _)
    have hu0 : u ≠ 0 := by
      have : genericPoint σ.A.left ∈ locus σ.D k u := hU ▸ hx
      exact CartierDiv.GeneratesAt.ne_zero this
    choose m hm using fun x => _root_.GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart σ x u
    obtain ⟨M, hM⟩ := ((finite_height_one σ.hf).image m).bddAbove
    refine ⟨k, hk, σ.c₀ σ.f ^ M * u, ⟨?_, (_root_.GlobalTheory.Desc.Setup.forall_mem_W_iff σ _).2 fun p hp hfp => ?_⟩,
      mul_ne_zero (pow_ne_zero _ (c₀_f_ne_zero σ)) hu0⟩
    · rw [← map_pow]
      exact sec_mul_left _ _ (fun x => regAt_cst _ x _) hu
    · have hle : m p ≤ M := hM ⟨p, ⟨hp, hfp⟩, rfl⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
      rw [pow_add, _root_.mul_assoc, ← map_pow]
      exact W_mul σ p (c₀_mem_W σ p _) (hm p)

end GlobalTheory.DescGraded
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyNoetherian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCohRing

theorem rankAtStalk_eq_finrank_residueField {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  rw [Module.rankAtStalk_eq_finrank_tensorProduct]
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    Module.free_of_flat_of_isLocalRing
  have e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal)
    p.asIdeal.ResidueField p.asIdeal.ResidueField M)
  rw [← e.finrank_eq]
  exact (Module.finrank_baseChange (S := Localization.AtPrime p.asIdeal) (R := p.asIdeal.ResidueField)
    (M' := Localization.AtPrime p.asIdeal ⊗[R] M)).symm

theorem exists_grpObj_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) {X' : Scheme.{0}} (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
    (h : IsPullback φ s' A.hom (spMap f)) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  letI : GrpObj ((Over.pullback (spMap f)).obj A) := Functor.grpObjObj
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hPA, -⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) (pullback.fst A.hom (spMap f)) g hP hA hg
  let e : Over.mk s' ≅ (Over.pullback (spMap f)).obj A := Over.isoMk h.isoPullback (by simp)
  letI gr : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine ⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hPA,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩
  haveI : IsMonHom e.symm.hom := inferInstance
  exact isMonHom_inv_of_iso e.symm

end GlobalTheory.AbCohRing

namespace GlobalTheory.AbCohRing

theorem fp_and_bc (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom)) ∧
      (Module.Finite R (HO2 A.hom) ∧ Module.Projective R (HO2 A.hom)) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  have := hA.proper
  have := hA.smooth
  refine _root_.GlobalTheory.AbCoh.CohBaseChange.main R A.left A.hom inferInstance inferInstance (_root_.GlobalTheory.AbCoh.uConst_of_isAbelianScheme R A hA) ?_
  intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hφ w
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R R') A g s' φ hφ hA hg
  exact _root_.GlobalTheory.AbCoh.artinian_pullHO_surjective R' (Over.mk s') g hA' hg' k α hα X₀ s₀ ψ w

theorem rankAtStalk_HO1 (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) [Module.Finite R (HO1 A.hom)]
    [Module.Projective R (HO1 A.hom)] (hb : StructureSheafH1BaseChange A.hom) (p : PrimeSpectrum R) :
    Module.rankAtStalk (HO1 A.hom) p = g := by
  let κ := p.asIdeal.ResidueField
  have hpb := IsPullback.of_hasPullback A.hom (spMap (algebraMap R κ))
  obtain ⟨e, -⟩ := hb κ _ _ _ hpb
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R κ) A g _ _ hpb hA hg
  have hκ := (_root_.GlobalTheory.AbCoh.abelian_HO_field_any κ _ g hA' hg').2.1
  rw [rankAtStalk_eq_finrank_residueField, ← hκ]
  exact e.finrank_eq

theorem oStr_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  intro R _ _ A _ g hA hg
  obtain ⟨⟨h1f, h1p⟩, ⟨h2f, h2p⟩, hb1, hb2⟩ := fp_and_bc R A g hA hg
  refine ⟨⟨h1f, h1p, rankAtStalk_HO1 R A g hA hg hb1⟩, ?_, hb1, hb2⟩
  refine _root_.GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres R A.left A.hom h1f h1p h2f h2p hb1 hb2 (_root_.GlobalTheory.AbCoh.cup_self_eq_zero_of_isAbelianScheme R A g hA hg) ?_
  intro k _ _ X' s' φ h
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R k) A g s' φ h hA hg
  exact (_root_.GlobalTheory.AbCoh.abelian_HO_field_any k (Over.mk s') g hA' hg').2.2.1

end GlobalTheory.AbCohRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAbelianPartsOfUniformisedRetract
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem cls_lam_proj {S : Scheme.{0}} {H : Over S} [GrpObj H] {L : LB H.left} (hL : L.IsLB) (h : (abelian₂ H L).IsLB) :
    cls (abelian₂ H L) h = lam (cls L hL) (fst H H) (snd H H) :=
  cls_cube_two hL (fst H H) (snd H H) h

theorem lbIso_iff_lam {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}
    (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (f g : H₁ ⟶ H₂) :
    LBIso (abelian₂ H₁ L₁) ((abelian₂ H₂ L₂).pull (lift (fst H₁ H₁ ≫ f) (snd H₁ H₁ ≫ g) : G2 H₁ ⟶ G2 H₂).left) ↔
      ∀ (T : Over S) (x z : T ⟶ H₁), lam (cls L₁ h₁) x z = lam (cls L₂ h₂) (x ≫ f) (z ≫ g) := by
  have hA : (abelian₂ H₁ L₁).IsLB := LB.isLB_linComb h₁ _ _
  have hB : (abelian₂ H₂ L₂).IsLB := LB.isLB_linComb h₂ _ _
  rw [← cls_eq_iff hA (pull_isLB hB _), cls_pull hB, cls_lam_proj h₁, cls_lam_proj h₂, pull_lam, lift_fst, lift_snd]
  constructor
  · intro h T x z
    have e := congrArg (pull (lift x z).left) h
    simpa only [pull_lam, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using e
  · intro h
    exact h _ _ _

theorem lam_of_rosatiGen {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {a b : B ⟶ B} (u : LB.Gen (LB.LinComb M (rosatiφ B a b) rosatiε)) (hu : u.IsGen) {T : Over S} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ a) y = lam (cls M hM) x (y ≫ b) := by
  unfold lam
  rw [GlobalTheory.EndRosati.cls_of_rosati hM u hu x y]

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData


set_option maxHeartbeats 1000000 in
theorem adjCls_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q r inc j hq hr hinc hj hiq hjr hqj hri qB jB hqB hjB hOq hOj
  obtain ⟨hAdm, hCZ⟩ := hR
  obtain ⟨incB, hincB, hOinc⟩ := exists_abelian_hom R _ hAdm D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  obtain ⟨rB, hrB, hOr⟩ := exists_abelian_hom R _ hAdm D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre r hr
  have hjrB : jB ≫ rB = 𝟙 _ :=
    (over₀_onTorus_unique R _ hAdm D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre (j ≫ r)).1 _ _
      (FactorPol.over_comp hOj hOr) (by rw [hjr]; exact FactorPol.over_id)

  have h1 : ∀ (T : Over (Sp R)) (x z : T ⟶ G₀),
      lam (cls U₀.LG.L U₀.LG.isLB) x z = lam (cls U.LG.L U.LG.isLB) (x ≫ inc) (z ≫ j) := by
    intro T x z
    rw [hqj T (x ≫ inc) z, Category.assoc, hiq, Category.comp_id]
  have hI := _root_.GlobalTheory.HomMum.lbIso_descends R hAdm D₀ D A₀ A G₀ G hG₀ hG U₀ U inc j incB jB hinc hj hincB hjB hOinc hOj
    ((lbIso_iff_lam U₀.LG.isLB U.LG.isLB inc j).2 h1)
  have h1B := (lbIso_iff_lam D₀.toPre.P.isLB D.toPre.P.isLB incB jB).1 hI

  have hadj : ∀ (T : Over (Sp R)) (x z : T ⟶ G),
      lam (cls U.LG.L U.LG.isLB) (x ≫ q ≫ inc) z = lam (cls U.LG.L U.LG.isLB) x (z ≫ r ≫ j) := by
    intro T x z
    rw [lam_comm, ← Category.assoc x, hri T z (x ≫ q), lam_comm, ← hqj T x (z ≫ r), Category.assoc]
  have hiso : LBIso (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L) := by
    have ha : (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    have hb : (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    refine (cls_eq_iff ha hb).1 ?_
    rw [cls_cube_two U.LG.isLB _ _ ha, cls_cube_two U.LG.isLB _ _ hb]
    exact hadj _ _ _

  haveI : IsMonHom U.gen.hom := U.gen_hom
  have hext : ∀ a : G ⟶ G, (Over.pullback (jK R)).map a ≫ U.gen.hom =
      U.gen.hom ≫ (U.gen.inv ≫ (Over.pullback (jK R)).map a ≫ U.gen.hom) := fun a => by simp
  obtain ⟨E, hE, -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (q ≫ inc) _ inferInstance inferInstance (hext _)
  obtain ⟨E', hE', -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (r ≫ j) _ inferInstance inferInstance (hext _)
  have hros := (rosatiAdjoint_and_linear_of_admissibleBase R _ hAdm D A G hG U E E' (by rw [hE, hE']; exact hiso)).2.1
  have hEB : E.aB = qB ≫ incB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E.aG).1 _ _ (lin_of_endU E).1.2.2.1
      (by rw [hE]; exact FactorPol.over_comp hOq hOinc)
  have hE'B : E'.aB = rB ≫ jB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E'.aG).1 _ _ (lin_of_endU E').1.2.2.1
      (by rw [hE']; exact FactorPol.over_comp hOr hOj)
  haveI := E.homB
  haveI := E'.homB
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.firstFiveLaws.1.globalFns D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hros
  intro T x z
  rw [h1B T (x ≫ qB) z, Category.assoc, ← hEB, lam_of_rosatiGen D.toPre.P.isLB u hu, hE'B, Category.assoc,
    reassoc_of% hjrB]

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniqueAdditiveScalar
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.AdjCalc

variable {K : Type} [Field K]

theorem comp_zpow' {X Y G : Over (Sp K)} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (m : ℤ) :
    f ≫ g ^ m = (f ≫ g) ^ m :=
  map_zpow (MonoidHom.mk' (fun g : Y ⟶ G => f ≫ g) (MonObj.comp_mul f)) g m

theorem isAdj_pt {A B : AbVar K} {c : Pic A.X.left} {d : Pic B.X.left} {f : A ⟶ B} {n : ℤ} {h : B ⟶ A}
    (H : IsAdj c d f n h) {Y : Over (Sp K)} (x : Y ⟶ A.X) (y : Y ⟶ B.X) :
    n • lam d (x ≫ f.hom) y = lam c x (y ≫ h.hom) := by
  have H' := congrArg (CechPic.pull (lift x y).left) H
  rw [map_zsmul, (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K A A c c c (𝟙 A) _ Y (lift x y) _ _).2.1,
    (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K B B d d d (𝟙 B) _ Y (lift x y) _ _).2.1] at H'
  simpa only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using H'

end GlobalTheory.AV.AbVar.AdjCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.HSUpper

noncomputable def polyComb {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ) :
    (Fin δ → MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) →ₗ[ℤ] K :=
  ∑ i : Fin δ, LinearMap.mulRight ℤ (w i) ∘ₗ (MvPolynomial.aeval x).toLinearMap ∘ₗ
    (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n).subtype ∘ₗ LinearMap.proj i

theorem polyComb_apply {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ) (T) :
    polyComb x w n T = ∑ i, MvPolynomial.aeval x (T i : MvPolynomial (Fin (D + 1)) ℤ) * w i := by
  simp [polyComb]

theorem fg_finrank_le {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ)
    (H : AddSubgroup K) (hH : ∀ f ∈ H, ∃ T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ,
      (∀ i, (T i).IsHomogeneous n) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i) :
    H.FG ∧ Module.finrank ℤ H ≤ δ * (n + D).choose D := by
  obtain ⟨-, -, -, hrk, hfin⟩ := _root_.GlobalTheory.HSAmp.card_bounded_forms D n δ 0 le_rfl
  haveI := hfin
  haveI : Module.Free ℤ (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) :=
    Module.free_of_finite_type_torsion_free'
  set Φ := polyComb x w n
  have hle : ∀ f ∈ H, f ∈ LinearMap.range Φ := by
    intro f hf
    obtain ⟨T, hT, rfl⟩ := hH f hf
    refine ⟨fun i => ⟨T i, (MvPolynomial.mem_homogeneousSubmodule n (T i)).2 (hT i)⟩, ?_⟩
    simp [Φ, polyComb_apply]
  let g : H →ₗ[ℤ] LinearMap.range Φ :=
    { toFun := fun f => ⟨f.1, hle f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun m f => by ext; simp }
  have hg : Function.Injective g := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Module.Finite ℤ H := Module.Finite.of_injective g hg
  refine ⟨(AddGroup.fg_iff_addSubgroup_fg H).1 (Module.Finite.iff_addGroup_fg.1 inferInstance), ?_⟩
  calc Module.finrank ℤ H ≤ Module.finrank ℤ (LinearMap.range Φ) := LinearMap.finrank_le_finrank_of_injective hg
    _ ≤ Module.finrank ℤ (Fin δ → MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) := LinearMap.finrank_range_le Φ
    _ = δ * (n + D).choose D := by
      rw [Module.finrank_pi_fintype, hrk]; simp

end GlobalTheory.HSAmp.HSUpper

theorem GlobalTheory.HSAmp.HSUpper.upper_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (P.H (e * q + a) b).FG ∧ Module.finrank ℤ (P.H (e * q + a) b) ≤ Module.finrank (ratF x) X.functionField * (q + c + D).choose D ∧ ∀ R κ : ℝ, 0 ≤ R → 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (P.Bl (e * q + a) b R).Finite ∧ (P.Bl (e * q + a) b R).ncard ≤ (2 * ⌊C * R / κ ^ (q + c)⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + c + D).choose D) := by
  intro k _ X _ p D hD P hA e x hx a b
  obtain ⟨c, w, C, hC, hrep⟩ := _root_.GlobalTheory.HSRep.sections_eq_sum_aeval_bounded k X p D hD P hA e x hx a b
  refine ⟨c, C, hC, fun q => ?_⟩
  obtain ⟨hfg, hrk⟩ := GlobalTheory.HSAmp.HSUpper.fg_finrank_le x w (q + c) (P.H (e * q + a) b) (fun f hf => by
    obtain ⟨T, hT, hf', -⟩ := hrep q f hf
    exact ⟨T, hT, hf'⟩)
  refine ⟨hfg, hrk, fun R κ hR hκ hcov => ?_⟩
  set R' : ℝ := C * R / κ ^ (q + c)
  have hR' : 0 ≤ R' := div_nonneg (mul_nonneg hC.le hR) (pow_pos hκ _).le
  obtain ⟨hSfin, hScard, -⟩ := _root_.GlobalTheory.HSAmp.card_bounded_forms D (q + c) (Module.finrank (ratF x) X.functionField) R' hR'
  set S := {T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ |
    (∀ i, (T i).IsHomogeneous (q + c)) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R'}
  have hsub : P.Bl (e * q + a) b R ⊆
      (fun T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ =>
        ∑ i, MvPolynomial.aeval x (T i) * w i) '' S := by
    intro f hf
    rw [← ballIn_H] at hf
    obtain ⟨hfH, hfR⟩ := hf
    obtain ⟨T, hT, hfT, hbd⟩ := hrep q f hfH
    exact ⟨T, ⟨hT, hbd R κ hκ hcov hfR⟩, hfT.symm⟩
  have himfin := hSfin.image (fun T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ =>
        ∑ i, MvPolynomial.aeval x (T i) * w i)
  refine ⟨himfin.subset hsub, ?_⟩
  calc (P.Bl (e * q + a) b R).ncard ≤ _ := Set.ncard_le_ncard hsub himfin
    _ ≤ S.ncard := Set.ncard_image_le hSfin
    _ = _ := hScard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDimStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_geometricPoints_eq_pow_two_dim : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), (n : K) ≠ 0 → Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  first | exact @GlobalTheory.AV.AbVar.card_torsion_pt | exact GlobalTheory.AV.AbVar.card_torsion_pt | (intros; apply GlobalTheory.AV.AbVar.card_torsion_pt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_primeToP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (exact GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent) | (intros; apply GlobalTheory.UPel.HT.ES.KerPowDescent.kernel_primePower_descent  <;> assumption)
end

