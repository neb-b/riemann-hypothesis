module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SemiAbDenseExt

theorem exists_extension : ∀ {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S] [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ (A B : Over U) [GrpObj A] [GrpObj B] (φ : A.left ⟶ G.left) (ψ : B.left ⟶ H.left), IsGrpPullback A G j φ → IsGrpPullback B H j ψ → ∀ g : A ⟶ B, IsMonHom g → ∃ f : G ⟶ H, g.left ≫ ψ = φ ≫ f.left := by
  intro U S _ _ j _ hd G H _ _ hG hH A B _ _ φ ψ hA hB g hg
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hA
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hB (isGrpPullback_pullback H j)
  let f := a.hom ≫ g ≫ b.hom
  have hf : IsMonHom f := by infer_instance
  have : IsDominant j := ⟨hd⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.dense_openImmersion j
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  have := hG.smooth
  have := hH.smooth
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, pullback.condition]
  obtain ⟨F, hF, hF'⟩ := GlobalTheory.DedekindExt.exists_of_stalks (j := j) G.hom H.hom
    (IsPullback.of_hasPullback G.hom j) hf₀ fun s => by
      obtain ⟨k, hk⟩ : ∃ k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U,
          k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s :=
        ⟨IsOpenImmersion.lift j _ (GlobalTheory.T.range_genericPoint_stalk_subset_of_denseOpen j hd s), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨g', hg', hA'⟩ := _root_.GlobalTheory.StalkExt.exists_agree_at_stalk j G H hG hH f hf s k hk
      exact ⟨_, S.fromSpecStalk s, 𝟙 _, g', Category.id_comp _, hg', hA'⟩
  refine ⟨Over.homMk F hF, ?_⟩
  have hφ : φ = a.inv.left ≫ pullback.fst G.hom j := by
    rw [← ha', ← Category.assoc, ← Over.comp_left, a.inv_hom_id, Over.id_left, Category.id_comp]
  show g.left ≫ ψ = φ ≫ F
  rw [hφ, Category.assoc, hF']
  simp only [f, Over.comp_left, Category.assoc, hb']
  rw [← Category.assoc a.inv.left, ← Over.comp_left, a.inv_hom_id, Over.id_left, Category.id_comp]

end GlobalTheory.SemiAbDenseExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionGenericPointFractionMeet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorDown

theorem ext_of_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  intro Z R R' _ _ _ _ _ gam hgam x a' hx
  obtain ⟨U, hU, hz, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
    (show a' (IsLocalRing.closedPoint R') ∈ (⊤ : Z.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hra : Set.range a' ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map a'.continuous).mem_open U.isOpen hz
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t'⟩ : Nonempty (Sp (FractionRing R')) := inferInstance
    have e1 : (spMap gam) t' = t := Subsingleton.elim _ _
    have e2 := congrArg (fun h : Sp (FractionRing R') ⟶ Z => h t') hx
    simp only [Scheme.Hom.comp_apply] at e2
    rw [← e1, ← e2]
    exact hra ⟨_, rfl⟩
  have ha₁ := IsOpenImmersion.lift_fac hU'.fromSpec a' hra
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec a' hra)] at ha₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec a' hra) with hψ
  set χ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hχ
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) = χ ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha₁, hx₁]
    exact hx
  have hmem : ∀ b : Γ(Z, U), χ.hom b ∈ (algebraMap R (FractionRing R)).range := by
    intro b
    have e := congrArg (fun h => h.hom b) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    obtain ⟨r, hr⟩ := hgam (χ.hom b) (ψ.hom b) e
    exact ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)).rangeRestrict := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  let eR := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨hinj, RingHom.rangeRestrict_surjective _⟩
  let θ : Γ(Z, U) →+* R := eR.symm.toRingHom.comp (χ.hom.codRestrict _ hmem)
  have hθ : ∀ b, algebraMap R (FractionRing R) (θ b) = χ.hom b := by
    intro b
    have := eR.apply_symm_apply (χ.hom.codRestrict _ hmem b)
    exact congrArg Subtype.val this
  refine ⟨Spec.map (CommRingCat.ofHom θ : Γ(Z, U) ⟶ CommRingCat.of R) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact hθ b

end GlobalTheory.TorDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointLiftFiniteSurjectiveMorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinLift

theorem lift_fieldPoint : ∀ (U X : Scheme.{0}) (c : U ⟶ X) [IsFinite c] [Surjective c] (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (y' : Sp K' ⟶ U), y' ≫ c = spMap (algebraMap K K') ≫ y := by
  intro U X c _ _ K _ y
  set P := pullback y c
  haveI : IsAffine P := inferInstance
  let f : P ⟶ Sp K := pullback.fst y c
  let A : CommRingCat := Γ(P, ⊤)
  let φ : CommRingCat.of K ⟶ A := Spec.preimage (P.isoSpec.inv ≫ f)
  have hφ : Spec.map φ = P.isoSpec.inv ≫ f := Spec.map_preimage _
  haveI : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance

  obtain ⟨p, -⟩ := (pullback.fst y c).surjective (IsLocalRing.closedPoint K)
  haveI : Nontrivial A := by
    have q : PrimeSpectrum A := P.isoSpec.hom.base p
    exact q.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A : Type)
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Algebra K A := φ.hom.toAlgebra
  haveI : Module.Finite K A := hfin
  haveI : Module.Finite K (A ⧸ m) := Module.Finite.trans A (A ⧸ m)
  refine ⟨A ⧸ m, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ P.isoSpec.inv ≫ pullback.snd y c, ?_⟩
  simp only [Category.assoc]
  rw [← pullback.condition, ← Category.assoc P.isoSpec.inv, ← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.FinLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_cover_step (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (t : Ω) (q : Polynomial (ResidueField R))
    (hq : q.Monic) (hqt : q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ t ∈ Set.range β := by
  letI : Algebra (ResidueField R) Ω := e₀.toAlgebra
  have hint : IsIntegral (ResidueField R) t := ⟨q, hq, hqt⟩
  set p := minpoly (ResidueField R) t with hpdef
  have hpm : p.Monic := minpoly.monic hint
  have hirr : Irreducible p := minpoly.irreducible hint
  have hdeg : 0 < p.degree := minpoly.degree_pos hint
  have hpt : p.eval₂ e₀ t = 0 := minpoly.aeval _ t
  have hlift : p ∈ Polynomial.lifts (residue R) :=
    (Polynomial.lifts_iff_set_range p).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective p)
  obtain ⟨P, hPmap, hPdeg, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  let C := AdjoinRoot P
  have hfinC : (AdjoinRoot.of P).Finite := by
    have : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hPm).finite
    exact RingHom.finite_algebraMap.2 this
  have hinjC : Function.Injective (AdjoinRoot.of P) := by
    refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
    rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hr
      (lt_of_le_of_lt Polynomial.degree_C_le (hPdeg ▸ hdeg))
    simpa using h0
  obtain ⟨R', i1, i2, i3, ρ, σ, hcn', hinj', hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (AdjoinRoot.of P) hR hinjC hfinC
  let r : ResidueField R' := residue R' (σ (AdjoinRoot.root P))
  have hres : (ResidueField.map ρ).comp (residue R) = (residue R').comp ρ := ResidueField.map_comp_residue ρ
  have hr : p.eval₂ (ResidueField.map ρ) r = 0 := by
    rw [← hPmap, Polynomial.eval₂_map, hres, ← hσ]
    show Polynomial.eval₂ (((residue R').comp σ).comp (AdjoinRoot.of P)) (((residue R').comp σ) (AdjoinRoot.root P)) P = 0
    rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  haveI : Fact (Irreducible p) := ⟨hirr⟩
  let gam : AdjoinRoot p →+* ResidueField R' := AdjoinRoot.lift (ResidueField.map ρ) r hr
  let del : AdjoinRoot p →+* Ω := AdjoinRoot.lift e₀ t hpt
  letI : Algebra (AdjoinRoot p) (ResidueField R') := gam.toAlgebra
  letI : Algebra (AdjoinRoot p) Ω := del.toAlgebra
  have hintR : ρ.IsIntegral := hfin'.to_isIntegral
  haveI : Algebra.IsIntegral (AdjoinRoot p) (ResidueField R') := by
    constructor
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨m, hm, hmx⟩ := hintR x
    refine ⟨(m.map (residue R)).map (AdjoinRoot.of p), (hm.map _).map _, ?_⟩
    show Polynomial.eval₂ gam (residue R' x) ((m.map (residue R)).map (AdjoinRoot.of p)) = 0
    rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
    have hgam : (gam.comp (AdjoinRoot.of p)).comp (residue R) = (residue R').comp ρ := by
      rw [← hres]; congr 1; ext a; exact AdjoinRoot.lift_of hr
    rw [hgam, ← Polynomial.hom_eval₂, hmx, map_zero]
  let β₀ : ResidueField R' →ₐ[AdjoinRoot p] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hβ : ∀ a, β₀ (gam a) = del a := fun a => β₀.commutes a
  refine ⟨R', i1, i2, i3, ρ, hloc, β₀.toRingHom, hcn', hinj', hfin', ?_, ⟨gam (AdjoinRoot.root p), ?_⟩⟩
  · ext a
    have h1 : ResidueField.map ρ a = gam (AdjoinRoot.of p a) := (AdjoinRoot.lift_of hr).symm
    show β₀ (ResidueField.map ρ a) = e₀ a
    rw [h1, hβ]
    exact AdjoinRoot.lift_of hpt
  · show β₀ (gam (AdjoinRoot.root p)) = t
    rw [hβ]
    exact AdjoinRoot.lift_root hpt

theorem exists_cover_residue (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.TorRef.IsCN R)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (e₀ : ResidueField R →+* Ω) (s : Finset Ω)
    (hs : ∀ t ∈ s, ∃ q : Polynomial (ResidueField R), q.Monic ∧ q.eval₂ e₀ t = 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ)
      (β : ResidueField R' →+* Ω), GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
      β.comp (ResidueField.map ρ) = e₀ ∧ (s : Set Ω) ⊆ Set.range β := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, inferInstance, e₀, hR, Function.injective_id,
      RingHom.Finite.id R, by rw [ResidueField.map_id]; rfl, by simp⟩
  | insert t s ht ih =>
    obtain ⟨R₁, i1, i2, i3, ρ₁, hl₁, β₁, hcn₁, hinj₁, hfin₁, hβ₁, hs₁⟩ :=
      ih fun u hu => hs u (Finset.mem_insert_of_mem hu)
    obtain ⟨q, hq, hqt⟩ := hs t (Finset.mem_insert_self t s)
    have hqt' : (q.map (ResidueField.map ρ₁)).eval₂ β₁ t = 0 := by rw [Polynomial.eval₂_map, hβ₁, hqt]
    obtain ⟨R₂, j1, j2, j3, ρ₂, hl₂, β₂, hcn₂, hinj₂, hfin₂, hβ₂, ht₂⟩ :=
      exists_cover_step R₁ hcn₁ β₁ t _ (hq.map _) hqt'
    refine ⟨R₂, j1, j2, j3, ρ₂.comp ρ₁, inferInstance, β₂, hcn₂, hinj₂.comp hinj₁, hfin₂.comp hfin₁, ?_, ?_⟩
    · rw [ResidueField.map_comp, ← RingHom.comp_assoc, hβ₂, hβ₁]
    · rw [Finset.coe_insert]
      refine Set.insert_subset ht₂ (hs₁.trans ?_)
      rintro _ ⟨a, rfl⟩
      exact ⟨ResidueField.map ρ₂ a, by rw [← hβ₂]; rfl⟩

theorem exists_finExt_tq_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), FinExt ρ ∧ IsGrpPullback G' G (spMap ρ) β ∧ Nonempty (GlobalTheory.UU.TQ (thickObj R' (maximalIdeal R') 0 G') X) := by
  intro R _ _ _ hR G _ _ hG
  have hcn : GlobalTheory.TorRef.IsCN R := ⟨hR.1.1, hR.1.2.2.1, hR.1.2.2.2, hR.2⟩
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField R
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := GlobalTheory.FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  obtain ⟨R', i1, i2, i3, ρ, hl, β, hcn', hinj, hfin, hβ, hr⟩ := exists_cover_residue R hcn (algebraMap k Ω) hs.toFinset
    (fun t _ => ⟨minpoly k t, minpoly.monic (Algebra.IsIntegral.isIntegral t), minpoly.aeval k t⟩)
  have hT := H (ResidueField R') (ResidueField.map ρ) β hβ (by simpa using hr)
  let G' := (Over.pullback (spMap ρ)).obj G
  have hT' : Nonempty (TorusExtension ((Over.pullback (spMap (residue R'))).obj G')) := by
    refine GlobalTheory.nonempty_torusExtension_of_comp_eq ?_ G hT
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ResidueField.map_comp_residue]
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := GlobalTheory.Raynaud.exists_tq_level_zero_of_torusExtension R' G' hT'
  exact ⟨R', i1, i2, i3, ρ, G', inferInstance, inferInstance, _, X, inferInstance, inferInstance, inferInstance,
    ⟨⟨hcn'.1, inferInstance, hcn'.2.1, hcn'.2.2.1⟩, hinj, hfin⟩, isGrpPullback_pullback G (spMap ρ), ⟨Q⟩⟩

end GlobalTheory.Mum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteChartMapToNormalFiniteModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.ModelAt

open GlobalTheory.Points GlobalTheory.ZH.RatModel

theorem isIntegral_valMap {C : Type} [CommRing C] {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    (f : Sp C ⟶ V) [IsFinite f] (h : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V) : (valMap (f ≫ V.ι) V h).hom.IsIntegral := by
  have e := specMap_valMap_fromSpec hV (f ≫ V.ι) h
  have e2 : Spec.map (valMap (f ≫ V.ι) V h) = f ≫ hV.isoSpec.hom := by
    rw [← cancel_mono hV.fromSpec, e, Category.assoc, ← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map (valMap (f ≫ V.ι) V h)) := by rw [e2]; infer_instance
  exact ((IsFinite.SpecMap_iff _).1 this).to_isIntegral

theorem mem_of_isIntegralElem {o Ω A : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing A]
    (S : Subalgebra o Ω) [IsFractionRing S Ω] [IsIntegrallyClosed S] (σ : A →+* Ω) (hσ : ∀ a, σ a ∈ S) {x : Ω}
    (hx : σ.IsIntegralElem x) : x ∈ S := by
  have h1 : (algebraMap S Ω).IsIntegralElem x := by
    obtain ⟨p, hp, h0⟩ := hx
    refine ⟨p.map (σ.codRestrict S hσ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral S x from h1)
  exact hy ▸ y.2

theorem exists_map_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := by
  intro o Ω _ _ _ M Z π hn hπ R hR hic V f hV hf hpt
  have hg : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V := fun w _ => (f w).2
  have hpV : ⊤ ≤ (M.pt ≫ π) ⁻¹ᵁ V := by
    rw [hpt]
    exact fun w _ => hg (x := _) trivial
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hne : ((π ⁻¹ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨M.pt (IsLocalRing.closedPoint Ω), hpV (x := IsLocalRing.closedPoint Ω) trivial⟩
  haveI : IsFractionRing R Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, c, hc, h⟩ := hR z
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, h⟩
  have hα := isIntegral_valMap hV f hg
  have hβ : (π.app V).hom.IsIntegral := (π.finite_app V hV).to_isIntegral
  have hcomm : ∀ a, M.res _ hne ((π.app V).hom a) = (((valMap (f ≫ V.ι) V hg).hom a : R) : Ω) := fun a => by
    rw [res_apply, valF_eq_valR, ← valR_comp, hpt, valR_spMap_comp _ _ _ hg, valR_eq _ _ hg]
    rfl
  have hσ : (M.res _ hne).comp (π.app V).hom = R.val.toRingHom.comp (valMap (f ≫ V.ι) V hg).hom :=
    RingHom.ext hcomm
  have h1 : ∀ c, M.res _ hne c ∈ R := fun c =>
    mem_of_isIntegralElem R ((M.res _ hne).comp (π.app V).hom) (fun a => by
      rw [RingHom.comp_apply, hcomm]; exact Subtype.prop _) (by
      obtain ⟨p, hp, h0⟩ := hβ c
      exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, h0, map_zero]⟩)
  have h2 : ∀ r : R, ∃ c, M.res _ hne c = r := fun r => by
    have : (r : Ω) ∈ M.ringOn (π ⁻¹ᵁ V : M.Z.Opens) := mem_ringOn.2 fun z hz => by
      have := isIntegrallyClosed_O hn z
      refine mem_of_isIntegralElem (M.O z) ((M.res _ hne).comp (π.app V).hom) (fun a => by
        rw [RingHom.comp_apply, res_apply]; exact valF_mem_O hz _) ?_
      obtain ⟨p, hp, h0⟩ := hα r
      refine ⟨p, hp, ?_⟩
      rw [hσ]
      exact (Polynomial.hom_eval₂ p _ R.val.toRingHom r).symm.trans (by rw [h0, map_zero])
    obtain ⟨c, hc⟩ := (mem_ringOn_iff_exists hne).1 this
    exact ⟨c, (M.res_apply _ hne c).trans hc⟩
  let ψ : Γ(M.Z, π ⁻¹ᵁ V) ⟶ CommRingCat.of R := CommRingCat.ofHom ((M.res _ hne).codRestrict R h1)
  have hφ := le_preimage_specMap_fromSpec hW ψ
  refine ⟨Spec.map ψ ≫ hW.fromSpec, ?_, fun P a b hb => ?_⟩
  · refine ext_of_valR hV hφ hg fun a => ?_
    rw [valR_comp, valR_eq _ _ hφ, valMap_specMap_fromSpec, valR_eq _ _ hg]
    exact Subtype.ext (hcomm a)
  · have hz : (Spec.map ψ ≫ hW.fromSpec) P ∈ π ⁻¹ᵁ V := hφ (x := P) trivial
    obtain ⟨a', ha'⟩ := h2 a
    obtain ⟨b', hb'⟩ := h2 b
    have hbz : (Spec.map ψ ≫ hW.fromSpec) P ∈ M.Z.basicOpen b' := by
      change Spec.map ψ P ∈ hW.fromSpec ⁻¹ᵁ M.Z.basicOpen b'
      rw [hW.fromSpec_preimage_basicOpen]
      change ψ.hom b' ∉ P.asIdeal
      rwa [show ψ.hom b' = b from Subtype.ext hb']
    have hu := ((isUnit_O_iff _).1 ((isUnit_valF_iff hz b').2 hbz)).2
    rw [← ha', ← hb', res_apply, res_apply, div_eq_mul_inv]
    exact mul_mem (valF_mem_O hz a') hu

end GlobalTheory.Poinc.ModelAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteNormalExtSqrtFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqRoots

open Polynomial

theorem exists_sqrt_one (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (b : R)
    (h : IsCN R) : ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (s : R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      s ^ 2 = ρ b := by
  set g : R[X] := X ^ 2 - C b with hg_def
  have hg : g.Monic := monic_X_pow_sub_C b two_ne_zero
  have hdeg : g.natDegree = 2 := natDegree_X_pow_sub_C _
  have hinj : Function.Injective (AdjoinRoot.of g) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hne
    have hdvd : g ∣ C r := by
      rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
      exact hr
    refine hg.not_dvd_of_natDegree_lt (C_ne_zero.mpr hne) ?_ hdvd
    rw [natDegree_C, hdeg]; norm_num
  have hfin : (AdjoinRoot.of g).Finite := by
    have := RingHom.finite_algebraMap.mpr hg.finite_adjoinRoot
    rwa [AdjoinRoot.algebraMap_eq] at this
  obtain ⟨R', _, _, _, ρ, σ, hC, hi, hf, hl, hσ⟩ :=
    _root_.GlobalTheory.LocExt.exists_isCN_cover_of_finite R (AdjoinRoot g) (AdjoinRoot.of g) h hinj hfin
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, σ (AdjoinRoot.root g), hC, hi, hf, hl, ?_⟩
  have hroot : AdjoinRoot.root g ^ 2 = AdjoinRoot.of g b := by
    have h0 : AdjoinRoot.mk g g = 0 := AdjoinRoot.mk_self
    rw [hg_def, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  rw [← map_pow, hroot, ← RingHom.comp_apply, hσ]

theorem exists_sqrt_fin : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (a : Fin n → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (r : Fin n → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      ∀ i, r i ^ 2 = ρ (a i) := by
  intro n
  induction n with
  | zero =>
    intro R _ _ _ a h
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, Fin.elim0, h,
      Function.injective_id, RingHom.Finite.id R, inferInstance, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro R _ _ _ a h
    obtain ⟨R₁, _, _, _, ρ₁, r₁, hC₁, hi₁, hf₁, hl₁, hr₁⟩ := ih R (fun i => a i.castSucc) h
    obtain ⟨R₂, _, _, _, ρ₂, s, hC₂, hi₂, hf₂, hl₂, hs⟩ :=
      exists_sqrt_one R₁ (ρ₁ (a (Fin.last n))) hC₁
    refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp ρ₁,
      Fin.lastCases s (fun i => ρ₂ (r₁ i)), hC₂, hi₂.comp hi₁, hf₂.comp hf₁, ?_, ?_⟩
    · haveI := hl₁; haveI := hl₂; infer_instance
    · intro i
      induction i using Fin.lastCases with
      | last => beta_reduce; rw [Fin.lastCases_last, hs, RingHom.comp_apply]
      | cast i => beta_reduce; rw [Fin.lastCases_castSucc, ← map_pow, hr₁, RingHom.comp_apply]

end GlobalTheory.SqRoots

theorem GlobalTheory.sqrt_of_finite_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Type) [Finite I] (a : I → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : I → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (a i) := by
  intro R _ _ _ I _ a h
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨R', _, _, _, ρ, r, hC, hi, hf, hl, hr⟩ := GlobalTheory.SqRoots.exists_sqrt_fin n R (a ∘ e.symm) h
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, r ∘ e, hC, hi, hf, hl, fun i => ?_⟩
  simpa using hr (e i)
end

