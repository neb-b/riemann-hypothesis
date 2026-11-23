module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedFactorAlgebraicPartPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.PFactorPull


open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.FactorPull in
theorem algebraic_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X) (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B (spMap θ) β → (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) → ∃ (inc : Q'.B ⟶ D₁.P.A) (pr : D₁.P.A ⟶ Q'.B) (xi : Q'.X →+ D₁.X) (xp : D₁.X →+ Q'.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left ∧ (∀ y, hD.xe (xi y) = F.xi (ex y)) ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) ∧ (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁.X, ∃ y, star F.e • z = star F.e • F.f • xi y) := by
  intro R V _ _ _ _ θ Q D₀ F D₁ hD _ o₁ hx ho Q' ex β gp hcβ
  have gp' := pull_grp hD
  obtain ⟨inc, mi, hi⟩ := hom_pull gp gp' F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gp' gp F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : Q'.X →+ D₁.X, ∀ y, hD.xe (xi y) = F.xi (ex y) :=
    ⟨hD.xe.symm.toAddMonoidHom.comp (F.xi.comp ex.toAddMonoidHom), fun y => hD.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁.X →+ Q'.X, ∀ y, ex (xp y) = F.xp (hD.xe y) :=
    ⟨ex.symm.toAddMonoidHom.comp (F.xp.comp hD.xe.toAddMonoidHom), fun y => ex.apply_symm_apply _⟩
  have hc : ∀ y, D₁.c (xi y) = Q'.c y ≫ inc := fun y => ext_pull gp' (by
    rw [hD.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (Q'.c y).left,
      hcβ, Category.assoc]
    try rfl)
  refine ⟨inc, pr, xi, xp, hi, hxi, mi, mp, ext_pull gp ?_, ext_pull gp' ?_, fun y => ex.injective ?_,
    fun y => hD.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD.xe h
    simp only [hx, hxi] at h'
    exact ex.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD.xe z)
    refine ⟨ex.symm y, hD.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ex.apply_symm_apply, hy]

end GlobalTheory.PFactorPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPullbackRefinement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorPull

section PFactorPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [GrpObj C]
  [GrpObj B₁] [GrpObj C₁] [IsCommMonObj C] [IsCommMonObj C₁] {β : B₁.left ⟶ B.left} {δ : C₁.left ⟶ C.left}

theorem lift_sq_of (β₂ : (G2 B₁).left ⟶ (G2 B).left) (hsq : IsSquare β β₂) (gC : IsGrpPullback C₁ C f δ)
    {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁} (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ sqOf gC =
      β₂ ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, (isSquare_sqOf gC).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc β₂,
      hsq.1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, (isSquare_sqOf gC).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc β₂,
      hsq.2, Category.assoc]

end PFactorPull


set_option maxHeartbeats 800000 in
theorem pfactor_pull : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
  ∀ (Q : Data R) (D' : DegPre R) (F : PFactor Q D') (D : DegPre R') (ε : D.X ≃+ Q.X), Refines Q ρ D ε →
  ∀ (D₁' : DegPre R') (hD' : IsPullDeg ρ D' D₁') [Module F.O D₁'.X] (o₁ : D₁'.OAct F.O),
    (∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y) →
    (∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) →
    ∃ (inc : D.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D.P.A) (xi : D.X →+ D₁'.X) (xp : D₁'.X →+ D.X)
      (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  intro R R' _ _ _ _ ρ hρ Q D' F D ε hR D₁' hD' _ o₁ hx ho
  obtain ⟨β, β₂, wR, gB, hsq, hwR, hcR, htR⟩ := hR
  have gC := pull_grp hD'
  obtain ⟨inc, mi, hi⟩ := hom_pull gB gC F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gC gB F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : D.X →+ D₁'.X, ∀ y, hD'.xe (xi y) = F.xi (ε y) :=
    ⟨hD'.xe.symm.toAddMonoidHom.comp (F.xi.comp ε.toAddMonoidHom), fun y => hD'.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁'.X →+ D.X, ∀ y, ε (xp y) = F.xp (hD'.xe y) :=
    ⟨ε.symm.toAddMonoidHom.comp (F.xp.comp hD'.xe.toAddMonoidHom), fun y => ε.apply_symm_apply _⟩
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ proj hD' = β ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  have hm := lift_sq_of β₂ hsq gC hi hf
  obtain ⟨w, hw, vw⟩ := _root_.GlobalTheory.FactorPull.lam_down_gen gC Q.M.isLB D'.P.isLB D.P.isLB D₁'.P.isLB β₂ wR hwR hD'.w hD'.w_gen hm F.w F.w_gen
  have hc : ∀ y, D₁'.c (xi y) = D.c y ≫ inc := fun y => ext_pull gC (by
    rw [hD'.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (D.c y).left,
      hcR, Category.assoc])
  refine ⟨inc, pr, xi, xp, w, mi, mp, ext_pull gB ?_, ext_pull gC ?_, fun y => ε.injective ?_,
    fun y => hD'.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_, hw, fun a b z I₁ J₁ hI₁ hJ₁ => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD'.xe h
    simp only [hx, hxi] at h'
    exact ε.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD'.xe z)
    refine ⟨ε.symm y, hD'.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ε.apply_symm_apply, hy]
  · obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' Q.M.isLB z
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' D'.P.isLB z
    let g₀ := genMap hρ
    have sq : (TK R').hom ≫ spMap ρ = g₀ ≫ (TK R).hom := (Category.id_comp _).symm.trans (fracMap_sq hρ)
    have hκ : g₀ ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hρ).symm.trans (Category.id_comp _)
    have cQ : ∀ y, (toUnit (TK R') ≫ D.c y).left ≫ β = g₀ ≫ (toUnit (TK R) ≫ Q.c (ε y)).left := fun y => by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hcR, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (Q.c (ε y)).left) sq
    have hP : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫ β₂ =
        g₀ ≫ (lift (toUnit (TK R) ≫ Q.c (ε a)) (toUnit (TK R) ≫ Q.c (ε b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q.B Q.B).left = _ ≫ (fst Q.B Q.B).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact cQ a
      · show _ ≫ (snd Q.B Q.B).left = _ ≫ (snd Q.B Q.B).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact cQ b
    have hQ : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left =
        (lift (toUnit (TK R') ≫ D₁'.c (xi a)) (toUnit (TK R') ≫ D₁'.c (F.f • xi b))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hc, hc]
      simp only [Category.assoc]
    have R₁ := htR g₀ hκ a b z J J₁ hJ hJ₁
    have t₁ := F.tau (ε a) (ε b) (g₀ z) (fun ψ => I (g₀ ≫ ψ)) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => hI (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (Q.tau (ε a) (ε b)) (g₀ ≫ 𝟙 _) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (ε a) (ε b)) (𝟙 _) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J hJ).2.2.1 _)
    have n₂ : val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (g₀ ≫ 𝟙 _) z I =
        Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (𝟙 _) (g₀ z) (fun ψ => I (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z I hI).2.2.1 _)
    rw [Category.comp_id] at n₁ n₂
    have E := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp F.w g₀ _ z I J hI hJ).symm n₂.symm))
    have K := vw _ (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z I J I₁ J₁ hI hJ hI₁ hJ₁
    rw [hP, hQ] at K
    have a₂ := tau_lam hD' hρ (xi a) (F.f • xi b) hI hI₁
    rw [hx, hxi, hxi] at a₂
    rw [R₁, ← a₂, E, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_comm (lamVal w _ z I₁ J₁), K,
      mul_comm (lamVal F.w _ z I J)]

end GlobalTheory.FactorPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTor

theorem pow_comp_monHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∃ ρ, TorMatch U U' (RingHom.id R) p.left ρ := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ hG' D' A' U' p hpm
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map p) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp' hp p _ e
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p) inferInstance
  refine ⟨ρ, ?_⟩
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thetaNZ_of_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨V, _, _, _, φ, D', A', G', _, _, U', U₀, F, C, hV, hφ, hc, hU⟩ := _root_.GlobalTheory.Mum.TraitCompare.exists_cmp_under R hB D A G U hE
  obtain ⟨σ, f, g, q, hq, hf, hfg, hg0, hgm⟩ := _root_.GlobalTheory.Mum.exists_coefData_of_ne_zero R hB D A G U V φ D' A' G' U' U₀ F C hV hφ hc hU
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.SecDiv.exists_expT_of_dvd R hB D A G U σ f g q hq hf hfg
  have := U.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint G _ (_root_.GlobalTheory.PreUTheta.exists_mem_nonzeroLocus R D A G U τ g hτ hg0 hgm)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveAxesDescendField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem one_tmul_injective_field (K L M : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Function.Injective (fun m : M ↦ (1 : L) ⊗ₜ[K] m) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (fun m : M ↦ (1 : L) ⊗ₜ[K] m) = ((Algebra.linearMap K L).rTensor M) ∘ (TensorProduct.lid K M).symm := by
    funext m; simp
  rw [h2]; exact h1.comp (TensorProduct.lid K M).symm.injective

theorem pullHO_injective_field (K L : Type) [Field K] [Field L] [Algebra K L] (X X' : Scheme.{0}) (s : X ⟶ Sp K)
    (s' : X' ⟶ Sp L) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap K L))) (hs : IsSeparated s)
    (hq : QuasiCompact s) :
    Function.Injective (pullHO1 h.w) ∧ Function.Injective (pullHO2 h.w) := by
  obtain ⟨⟨e1, he1⟩, ⟨e2, he2⟩⟩ := _root_.GlobalTheory.AbCoh.flat_baseChange_HO K L X X' s s' φ h hs hq
  refine ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩
  · apply one_tmul_injective_field K L
    apply e1.injective
    simp only [he1, hab]
  · apply one_tmul_injective_field K L
    apply e2.injective
    simp only [he2, hab]

theorem noPrimO2_axesO1_descend : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  intro K L _ _ _ A _ B _ φ hφ hA
  have hpA : IsProper A.hom := hA.proper
  have hpAA : IsProper (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨Φ, hΦ, hμ, hf, hs, ha1, ha2⟩ := _root_.GlobalTheory.AbCoh.prod_pullback_sq K L (algebraMap K L) A B φ hφ
  have injA := pullHO_injective_field K L A.left B.left A.hom B.hom φ hφ.1 inferInstance inferInstance
  have injAA := pullHO_injective_field K L (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom Φ hΦ
    inferInstance inferInstance
  have N := pull_over_baseChange_comm K L (algebraMap K L)
  refine ⟨fun hB z hz ↦ ?_, fun hB y h1 h2 ↦ ?_⟩
  · apply injA.2
    rw [map_zero]
    apply hB
    have e := congrArg (pullHO2 hΦ.w) hz
    rw [map_add (f := _)] at e
    rw [← (N A (A ⊗ A) B (B ⊗ B) μ[A] μ[B] φ Φ hφ.1.w hΦ.w hμ).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (fst A A) (fst B B) φ Φ hφ.1.w hΦ.w hf).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (snd A A) (snd B B) φ Φ hφ.1.w hΦ.w hs).2]
    exact e
  · apply injAA.1
    rw [map_zero]
    apply hB
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha1).1, h1, map_zero]
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha2).1, h2, map_zero]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_of_primO2 (hO : PrimitiveStructureSheafDegTwoVanish) : PrimitiveExtendedDegTwoVanish := by
  intro R₀ R₁ _ _ _ q hq A _ g hA hsm c c₁ c₂ hμ h₁ h₂
  obtain ⟨B, _, pr, pr', hB, hBs, hp, hp', eμ, ef, es, -, -⟩ := _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R₀ R₁ A g hA hsm
  obtain ⟨e, he⟩ := _root_.GlobalTheory.Obs.extCoef_two_equiv R₀ R₁ q hq
  set eX := e A.left B.left A.hom B.hom pr hp
  set eY := e (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
  have hc : c = eX (eX.symm c) := (eX.apply_symm_apply c).symm
  have hc₁ : c₁ = eY (eY.symm c₁) := (eY.apply_symm_apply c₁).symm
  have hc₂ : c₂ = eY (eY.symm c₂) := (eY.apply_symm_apply c₂).symm
  have hsum : c₁ + c₂ = eY (eY.symm c₁ + eY.symm c₂) := by rw [map_add (f := _), ← hc₁, ← hc₂]
  have hd : eX.symm c = 0 := by
    refine hO R₁ B g hB hBs (eX.symm c) (eY.symm c₁) (eY.symm c₂) ?_ ?_ ?_
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (μ[A]).left (μ[B]).left (overW μ[A]) (overW μ[B]) eμ _ _ ?_
      rw [← hc, ← hsum]; exact hμ
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (fst A A).left (fst B B).left (overW (fst A A)) (overW (fst B B)) ef _ _ ?_
      rw [← hc, ← hc₁]; exact h₁
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (snd A A).left (snd B B).left (overW (snd A A)) (overW (snd B B)) es _ _ ?_
      rw [← hc, ← hc₂]; exact h₂
  rw [hc, hd, map_zero]

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicProperties
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.CrdBasic

theorem pCrd_basic : (∀ (o R R' : Type) [CommRing o] [CommRing R] [CommRing R'] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (i : R →+* R'), PCrd x v → PCrd (spMap i ≫ x) (fun j => i (v j))) ∧ (∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (a : R), IsUnit a → PCrd x v → PCrd x (fun j => a * v j)) ∧ ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n), (∃ v, PCrd x v) ∧ ∀ v, PCrd x v → ∃ j, v j ≠ 0 := by
  refine ⟨fun o R R' _ _ _ n x v i h => ?_, fun o R _ _ n x v a ha h => ?_, fun o K _ _ n x => ⟨?_, fun v h => ?_⟩⟩
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).1 R' i
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).2.1 ha.unit
  · exact GlobalTheory.ZM.FieldPoint.exists_secCoord o n K x
  · obtain ⟨c, hc⟩ := RepUniq.exists_spMap (x ≫ PSpace.str o n)
    obtain ⟨hv, -⟩ := GlobalTheory.ZM.ProjExt.eq_pt_of_secCoord c x hc v h
    by_contra h0
    push_neg at h0
    have : Ideal.span (Set.range v) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨j, rfl⟩
      exact h0 j
    rw [this] at hv
    exact bot_ne_top hv

end GlobalTheory.UMin.CrdBasic
end

