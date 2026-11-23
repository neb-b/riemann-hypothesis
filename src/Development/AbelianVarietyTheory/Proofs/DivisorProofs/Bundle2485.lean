module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RigLinUnique

theorem eq_pull_section {X S S' : Scheme.{0}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (j : S' ⟶ S)
    (hi : Function.Injective (pullback.fst p j).appTop.hom)
    (hs : Function.Surjective (pullback.snd p j).appTop.hom) (u : Γ(X, ⊤)) :
    u = p.appTop.hom (e.appTop.hom u) := by
  have cmp : ∀ {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Γ(C, ⊤)),
      a.appTop.hom (b.appTop.hom x) = (a ≫ b).appTop.hom x := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  obtain ⟨c, hc⟩ := hs ((pullback.fst p j).appTop.hom u)
  let e' : S' ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 S') (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have h2 : e' ≫ pullback.snd p j = 𝟙 S' := pullback.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom u) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h1, h2, ← cmp, Scheme.Hom.id_appTop] at this
    exact this
  apply hi
  rw [cmp, pullback.condition, ← cmp, ← hc', hc]

theorem exists_ratio {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (w₁ w₂ : LB.Iso L' (L.pull F)) (h₁ : PGen w₁) (h₂ : PGen w₂) :
    ∃ u : Γ(X', ⊤)ˣ, ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), F (g y) ∈ L.U j → g y ∈ L'.U k →
      gw w₂ g y j k = gm g y ⊤ u * gw w₁ g y j k := by
  have key : ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι),
      gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w₂.s (fun _ => j, k) * (w₁.s (fun _ => j, k))⁻¹) =
        gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := fun Y g y j k =>
    (map_mul _ _ _).trans (congrArg (gw w₂ g y j k * ·) (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit (X := X') (J := L.ι × L'.ι) ⊤ (fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2)
    (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩)
    (fun p => w₂.s (fun _ => p.1, p.2) * (w₁.s (fun _ => p.1, p.2))⁻¹) (fun p q x hx => by
      have a := h₁ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      refine (key _ _ x p.1 p.2).trans (Eq.trans ?_ (key _ _ x q.1 q.2).symm)
      rw [a, b, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  refine ⟨u, fun Y g y j k hj hk => ?_⟩
  have hm : g y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have : gm g y ⊤ u = gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := (gm_res g y le_top hm u).symm.trans
    ((congrArg (gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k)) (hu (j, k))).trans (key Y g y j k))
  rw [this]
  exact (inv_mul_cancel_right _ _).symm

theorem gw_eq_of_rigidified : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  intro R' _ _ _ D' A' G' _ _ hS U' s f₁ f₂ hf he₁ he₂ w₁ w₂ g₁ g₂ m₁ m₂ z j k hk hj
  subst hf
  have hL := U'.LG.isLB
  obtain ⟨u, hu⟩ := exists_ratio hL hL w₁ w₂ ((isGen_iff w₁).1 g₁) ((isGen_iff w₂).1 g₂)
  have p₁ := (maps_iff w₁ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₁ U'.LG.L)
    (fun _ => rfl)).1 m₁
  have p₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₂ U'.LG.L)
    (fun _ => rfl)).1 m₂
  have he1 : pullU (eSec G') ⊤ u = 1 := by
    apply unit_ext
    intro x _
    obtain ⟨a, ha⟩ := exists_chart hL (f₁ (eSec G' x))
    obtain ⟨b, hb⟩ := exists_chart hL (eSec G' x)
    have q₁ := p₁ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q₂ := p₂ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q := mul_right_cancel (q₂.symm.trans q₁)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hu _ (𝟙 _ ≫ eSec G') x a b ha hb] at q
    rw [map_one]
    exact (gm_pull (𝟙 _) (eSec G') x ⊤ trivial u).trans (mul_eq_right.1 q)
  have := U'.smooth
  have : Flat G'.hom := inferInstance
  have : IsDominant (jK R') := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (algebraMap R' (FractionRing R')))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R' (FractionRing R'))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R')
  have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R')) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G'.hom (jK R')).flip
  have hb := GlobalFunctionsDvrPowers.bijective_of_iso U'.gen (GlobalTheory.SemiRigid.globalFns _ A'.A A'.isAb)
  have hv := eq_pull_section G'.hom (eSec G') (Over.w η[G']) (jK R')
    ((pullback.fst G'.hom (jK R')).app_injective ⊤) hb.2 u.val
  have he2 : (eSec G').appTop.hom u.val = 1 := congrArg Units.val he1
  have hu1 : u = 1 := Units.ext (hv.trans ((congrArg G'.hom.appTop.hom he2).trans (map_one _)))
  rw [hu _ (𝟙 _) z j k hj hk, hu1, map_one, _root_.one_mul]

end GlobalTheory.Mum.RigLinUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharac
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8

theorem eq_torusMap_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X →+ X)
    (t : splitTorus S X ⟶ splitTorus S X) (ht : TorusEndOf X h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

theorem endChar_endU : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  intro V₁ _ _ _ _ D P G _ _ _ U E κ _ a ha G₀ _ φ h f₀ hf
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V₁ (maximalIdeal V₁) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatri
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.EndCompat

def preH {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (w : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (w ≫ ·) fun a b => MonObj.comp_mul w a b

def postH {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) (hf : IsMonHom f) :
    (T ⟶ G) →* (T ⟶ H) :=
  haveI := hf
  MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f

def pullH {S S' : Scheme.{0}} (f : S' ⟶ S) (T G : Over S) [GrpObj G] :
    (T ⟶ G) →* ((Over.pullback f).obj T ⟶ (Over.pullback f).obj G) where
  toFun := (Over.pullback f).map
  map_one' := by simp
  map_mul' a b := Functor.map_mul _ a b

theorem map_ofFn_prod {M N : Type} [Group M] [Group N] (f : M →* N) (x : Fin 8 → M) (k : Fin 8 → ℤ) :
    f (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => f (x v) ^ k v).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp [Function.comp_def, map_zpow]

theorem aG_comp_eq_prod : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hG₀ hα P c φc hφc pr hpr G _ _ hG D U q hq hqc a E hE u
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  haveI := E.homG
  haveI := hq u
  haveI := U₀.gen_hom
  have hR : IsMonHom (List.ofFn fun v => q v ^ a u v).prod := by
    refine isMonHom_of_mul _ fun T x z => ?_
    have key : ∀ w : T ⟶ G, w ≫ (List.ofFn fun v => q v ^ a u v).prod = ∏ v, (w ≫ q v) ^ a u v := fun w => by
      rw [← List.prod_ofFn]
      exact map_ofFn_prod (preH w) q (a u)
    rw [key, key, key, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    haveI := hq v
    rw [MonObj.mul_comp, mul_zpow]
  obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField V₁ (FractionRing V₁) G G₀ hG hG₀
    ((Over.pullback (jK V₁)).map (E.aG ≫ q u))
  refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
  rw [← cancel_mono U₀.gen.hom]
  apply Over.OverMorphism.ext
  refine hα.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have hv : ∀ v, pushHom hα ((Over.pullback (jK V₁)).obj G) ((Over.pullback (jK V₁)).map (q v) ≫ U₀.gen.hom) =
      pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) :=
    fun v => Over.OverMorphism.ext (hqc v)
  have e₁ : ((Over.pullback (jK V₁)).map (List.ofFn fun v => q v ^ a u v).prod ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have := map_ofFn_prod ((pushHom hα ((Over.pullback (jK V₁)).obj G)).comp
      ((postH U₀.gen.hom U₀.gen_hom).comp (pullH (jK V₁) G G₀))) q (a u)
    refine (congrArg (fun z => z.left) this).trans ?_
    refine congrArg (fun z => Over.Hom.left (List.ofFn z).prod) (funext fun v => ?_)
    rw [← hv v]
    rfl
  have e₂ : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have h1 : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
        (U.gen.hom ≫ (List.ofFn fun v => pr v ^ a u v).prod).left ≫ φc := by
      rw [Functor.map_comp, Category.assoc, Over.comp_left, Category.assoc, hqc u, ← Category.assoc,
        ← Over.comp_left, ← Category.assoc, E.ext, Category.assoc, hE u]
    have h2 := map_ofFn_prod ((pushHom hφc ((Over.pullback (jK V₁)).obj G)).comp (preH U.gen.hom)) pr (a u)
    exact h1.trans (congrArg (fun z => z.left) h2)
  exact e₁.trans e₂.symm

end GlobalTheory.Poinc.Sep.EndCompat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem abPart_eq {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg ρ D D') (h h' : IsPullDeg s D' D') (H : PullOver hD h) (H' : PullOver hD h') :
    h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) =
      h'.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) := by
  have hcb := H.2 _ _ rfl rfl
  have hcb' := H'.2 _ _ rfl rfl
  have hov : ∀ k : IsPullDeg s D' D', (k.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s)) ≫ D'.P.A.hom =
      D'.P.A.hom ≫ specOf s := by
    intro k
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w k.e.hom
  have : IsIso hD.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map hD.e.hom))
  rw [← cancel_mono hD.e.hom.left]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    simp only [Category.assoc] at hcb hcb'
    rw [hcb, hcb']
  · simp only [Category.assoc]
    have w0 : hD.e.hom.left ≫ pullback.snd D.P.A.hom (specOf ρ) = D'.P.A.hom := Over.w hD.e.hom
    rw [w0, ← Category.assoc, hov h, ← Category.assoc, hov h']

theorem iso_eq_of_rig {s : R' →+* R'} {D' : DegPre R'} (F : D'.P.A.left ⟶ D'.P.A.left)
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A)
    (w w' : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig)) : w = w' :=
  iso_unique_of_rig GlobalTheory.globalFns_holds D'.P.A D'.P.isAb D'.P.isLB D'.P.isLB hw hw' hr hr'

theorem level_eq {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ (g.t x))) : f = f' := by
  exact _root_.GlobalTheory.Mum.gtCoord_point_ext g f f' hb (hp.symm.trans hp') fun z J hJ χ => by
    obtain ⟨hψ, hm⟩ := ht χ
    obtain ⟨hψ', hm'⟩ := ht' χ
    exact _root_.GlobalTheory.Mum.gtCoord_val_eq_of_maps g F w f f' χ hψ hψ' hm hm' z J hJ

end GlobalTheory.Mum.GalUniq

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem level_eq_two {s : R' →+* R'} {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F F' : D'.P.A.left ⟶ D'.P.A.left) (hF : F = F')
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A) (he' : eSec D'.P.A ≫ F' = specOf s ≫ eSec D'.P.A)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (w' : LB.Iso D'.P.L (D'.P.L.pull F')) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F' (specOf s) he' D'.P.L D'.rig))
    (xe xe' : D'.X → D'.X) (hxe : xe = id) (hxe' : xe' = id)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F' = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG (xe x) k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t (xe x))))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F' = f' ≫ D'.Oφ g.pG (xe' x) k,
      LB.Gen.Maps (LB.linCombIso w' _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F' f' _ Oinvε _ hψ (g.t (xe' x)))) : f = f' := by
  subst hF hxe hxe'
  obtain rfl := iso_eq_of_rig F he w w' hw hw' hr hr'
  exact level_eq g F w hw f f' hb hp hp' ht ht'

end GlobalTheory.Mum.GalUniq


open GlobalTheory.Mum.GalUniq in
theorem GlobalTheory.Mum.galMap_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ) (a a' : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' σ a' → a = a' := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG U' σ a a' ha ha'
  obtain ⟨-, h, bc, rfl, P, PO⟩ := ha
  obtain ⟨-, h', bc', rfl, P', PO'⟩ := ha'
  have hc := abPart_eq hD h h' PO PO'
  have hxe : (⇑h.xe : D'.toPre.X → D'.toPre.X) = id := funext PO.1
  have hxe' : (⇑h'.xe : D'.toPre.X → D'.toPre.X) = id := funext PO'.1
  have hov : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) ≫ G'.hom = G'.hom ≫ specOf (Gal.hom σ) := by
    intro b
    rw [pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w b.hom
  have lev : ∀ n : ℕ, (fstG (maximalIdeal R') n G').left ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      (fstG (maximalIdeal R') n G').left ≫ bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := by
    intro n
    obtain ⟨wL, -, he1, -, hl⟩ := P.lg
    obtain ⟨wL', -, he1', -, hl'⟩ := P'.lg
    obtain ⟨f, hf, hpG, hT, -⟩ := hl n
    obtain ⟨f', hf', hpG', hT', -⟩ := hl' n
    have hb : f ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) =
        f' ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) := by
      have : IsClosedImmersion (thick R' (maximalIdeal R') n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← cancel_mono (thick R' (maximalIdeal R') n), Category.assoc, Category.assoc,
        ← pullback.condition]
      have e1 : f ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf]; simp only [Category.assoc]; rw [hov bc]
      have e2 : f' ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf']; simp only [Category.assoc]; rw [hov bc']
      exact e1.trans e2.symm
    have := level_eq_two (U'.gt n) _ _ hc h.he h'.he h.w h.w_gen h'.w h'.w_gen h.w_rig h'.w_rig _ _ hxe hxe' f f' hb hpG hpG' hT hT'
    rw [← hf, ← hf', this]
  have hI : maximalIdeal R' ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have : IsNoetherianRing R' := hρ.1.1
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have : IsSeparated G'.hom := hG.separated
  have : IsIso (CommRingCat.ofHom (Gal.hom σ)) := σ.1.toCommRingCatIso.isIso_hom
  have : IsIso (specOf (Gal.hom σ)) := inferInstanceAs (IsIso (Spec.map _))
  let Y : Over (Sp R') := Over.mk (G'.hom ≫ inv (specOf (Gal.hom σ)))
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (G'.hom ≫ inv (specOf (Gal.hom σ))))
  have hov2 : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      (b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) ≫ Y.hom = G'.hom := by
    intro b
    change _ ≫ G'.hom ≫ inv (specOf (Gal.hom σ)) = _
    simp only [Category.assoc]
    rw [reassoc_of% (hov b), IsIso.hom_inv_id, Category.comp_id]
  have key := (sec_eq_zero_and_hom_eq_of_thickenings R' (maximalIdeal R') hI G').2 Y
    (Over.homMk (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc))
    (Over.homMk (bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc')) lev
  exact congrArg CommaMorphism.left key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {h : X' → X}
    {t t' : splitTorus S X ⟶ splitTorus S X'} (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (splitTorusPointsEquiv S X' _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusHomOf_iff_appTop _ _).1 ht,
    (torusHomOf_iff_appTop _ _).1 ht']

theorem hom_eq_of_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U D' A' U' g g' b h hg hg' q₁ q₂ i₁ i₂
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨t, ht, j₁⟩ := i₁ e
  obtain ⟨t', ht', j₂⟩ := i₂ e
  have htt : t = t' := torusHomOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U'.gt e) GlobalTheory.globalFns_holds _ _
    ((q₁ e).trans (q₂ e).symm) (j₁.trans (htt ▸ j₂.symm))

end GlobalTheory.Mum.Two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumFam

theorem val_psi_zero_mul_rigK : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi 0) (𝟙 _) z J * val D.rigK (𝟙 _) z J = 1 := by
  intro R _ _ D hB z J hJ
  have h1 := GlobalTheory.PolDeg.Data.val_tau_zero (GlobalTheory.PolDeg.Wit.ofDeg D hB) 0 z J hJ
  have h2 : val ((GlobalTheory.PolDeg.Wit.ofDeg D hB).tau 0 0) (𝟙 _) z J = val (D.tau 0 0) (𝟙 _) z J :=
    (GlobalTheory.PolDeg.Wit.exists_tau D 0 0).choose_spec.2 _ _ z J hJ
  rw [h2] at h1
  unfold DegPre.tau at h1
  rw [val_mul hJ, val_mul hJ, val_mul hJ] at h1
  simp only [val_inv] at h1
  rw [congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul,
    ← mul_inv_rev, inv_eq_one] at h1
  rw [mul_comm]
  exact h1

end GlobalTheory.MumFam
end
end

