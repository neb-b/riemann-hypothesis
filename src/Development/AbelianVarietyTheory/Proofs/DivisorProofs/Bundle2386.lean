module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPull

open GlobalTheory.TChart

theorem gm_unitOn_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) (z : Sp R') :
    gm (𝟙 (Sp R')) z ⊤ (unitOn (Units.map f.toMonoidHom u)) =
      Units.map ((spMap f).stalkMap z).hom.toMonoidHom (gm (𝟙 (Sp R)) (spMap f z) ⊤ (unitOn u)) := by
  rw [← GlobalTheory.ConstFam.gm_comp_stalkMap (spMap f) (𝟙 _) z ⊤ trivial, Category.comp_id]
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have e := congrArg (fun g => g.hom (u : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [e]
  simp [Scheme.Hom.appTop]
  rfl

theorem periods_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  intro n V _ _ D r e₀ o W _ _ _ T V₁ _ _ f₁ κ₁ e B' _ β₂ β₂' x w₁ q hf₁ hP V₂ _ _ f₂ fK I _ s ε hfK hq D' hD Φ gΦ hc w hw a b
  refine ⟨Units.map fK.toMonoidHom (q (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)),
    hq _ _, ?_⟩
  intro z J J' hJ hJ'
  set E := hD.xe.trans (e₀.symm.trans e.symm) with hE
  obtain ⟨κK, hκK, -⟩ := GlobalTheory.HalfBC.exists_kappa f₁ f₂ fK hfK hf₁
  let g₀ : (TK V₂).left ⟶ (TK V₁).left := spMap fK
  have sg : g₀ ≫ jK V₁ = jK V₂ ≫ spMap f₂ := GlobalTheory.HalfBC.gam_comm f₂ fK hfK
  choose J₁ hJ₀ using fun χ : (TK V₂).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hJ₁ : Good D.P.L z J₁ := hJ₀
  have cE : ∀ a, (e.trans e₀) (E a) = hD.xe a := fun a => by simp [E]
  have t₁ := hP κK hκK (E a) (E b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
    (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
  rw [cE, cE] at t₁
  have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
  have n₁ : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
      (val (D.tau (hD.xe a) (hD.xe b)) κK (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
    Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κK g₀ z J₁ hJ₁).2.2.1 _)
  have h0 : g₀ ≫ (TK V₁).hom ≫ spMap κ₁ = (TK V₂).hom ≫ spMap (f₂.comp κ₁) := by
    show g₀ ≫ jK V₁ ≫ spMap κ₁ = jK V₂ ≫ spMap (f₂.comp κ₁)
    rw [← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  have n₀ : val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b))
        ((TK V₁).hom ≫ spMap κ₁) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) := by
    rw [← h0]; exact Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ g₀ z J hJ).2.2.1 _)
  have nC : gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK V₁).left) (g₀ z) ⊤ (unitOn (q (E a) (E b)))) :=
    gm_unitOn_map fK _ z
  have ni : isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (isoVal w₁ (lift (toUnit (TK V₁) ≫ x (E a))
        (toUnit (TK V₁) ≫ x (E b))).left (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))) := by
    unfold isoVal
    simp only [Category.assoc]
    refine GlobalTheory.ConstFam.gm_comp_stalkMap g₀ _ z _ ?_ _
    exact ⟨mem_pull.2 (Set.mem_iInter.2 fun I => hJ _), mem_pull.2 (Set.mem_iInter.2 fun I => hJ₁ _)⟩
  have hr : 𝟙 _ ≫ jK V₂ ≫ spMap (f₂.comp f₁) = (g₀ ≫ κK) ≫ jK V := by
    rw [Category.id_comp, Category.assoc, hκK, ← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂]
  have tv := GlobalTheory.ArcPull.tau_val hD (g₀ ≫ κK) (𝟙 _) hr hJ₁ hJ' a b
  have A : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ =
      gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) *
        (isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ *
          val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
    rw [n₁, t₂, nC, ni, n₀]
  have hx : ∀ χ, (toUnit (TK V₂) ≫ D'.c χ).left ≫ Φ = g₀ ≫ (toUnit (TK V₁) ≫ x (E χ)).left := fun χ => by
    show (jK V₂ ≫ (D'.c χ).left) ≫ Φ = spMap fK ≫ jK V₁ ≫ (x (E χ)).left
    rw [Category.assoc, hc, ← Category.assoc, ← sg, Category.assoc]
  have hPq : (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left ≫ GlobalTheory.HalfBC.sqOf gΦ =
      g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left := by
    have sq1 : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    have sq2 : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    apply pullback.hom_ext
    · show _ ≫ (fst B' B').left = _ ≫ (fst B' B').left
      rw [Category.assoc, sq1, ← Category.assoc, ← Over.comp_left, lift_fst,
        Category.assoc, ← Over.comp_left, lift_fst]
      exact hx a
    · show _ ≫ (snd B' B').left = _ ≫ (snd B' B').left
      rw [Category.assoc, sq2, ← Category.assoc, ← Over.comp_left, lift_snd,
        Category.assoc, ← Over.comp_left, lift_snd]
      exact hx b
  let h : ((TK V₂).left ⟶ D'.P.A.left) → ((TK V₂).left.presheaf.stalk z)ˣ :=
    fun q => gw hD.w q z (J₁ (q ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' q)
  have K := (hw _ (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
    (congrArg₂ (· * ·) (congrArg (fun q => isoVal w₁ q z J J₁) hPq)
      (prod_lam (DVR.cP D' (TK V₂) a) (DVR.cP D' (TK V₂) b) h))
  rw [← DVR.cPoint_add] at K
  have c₀ : ∀ χ, GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ D'.xK χ) = h (DVR.cP D' (TK V₂) χ).left := fun χ => by
    rw [Category.id_comp]; rfl
  have c₁ : GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ (1 : TK V₂ ⟶ D'.P.A).left) = h (1 : TK V₂ ⟶ D'.P.A).left := by
    rw [Category.id_comp]; rfl
  rw [c₀, c₀, c₀, c₁] at tv
  rw [K]
  have F := tv.symm.trans A
  generalize val (D'.tau a b) (𝟙 _) z J' = X at F ⊢
  generalize h (DVR.cP D' (TK V₂) (a + b)).left = Y₀ at F ⊢
  generalize h (DVR.cP D' (TK V₂) a).left = Y₁ at F ⊢
  generalize h (DVR.cP D' (TK V₂) b).left = Y₂ at F ⊢
  generalize h (1 : TK V₂ ⟶ D'.P.A).left = Y₃ at F ⊢
  have F' := congrArg Additive.ofMul F
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at F' ⊢
  linear_combination (norm := abel) F'

end GlobalTheory.PeriodPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfPullbacksEqZeroArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ArtinPicGlue

theorem units_lift_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (hR : Nontrivial R₀ → IsLocalRing R) (g : R →+* R₀)
    (hg : Function.Surjective g) (r : R₀ˣ) : ∃ r' : Rˣ, g r' = r := by
  rcases subsingleton_or_nontrivial R₀ with h | h
  · exact ⟨1, Subsingleton.elim _ _⟩
  · haveI := hR h
    haveI : IsLocalHom g := IsLocalHom.of_surjective g hg
    obtain ⟨a, ha⟩ := hg r
    exact ⟨(isUnit_of_map_unit g a (ha ▸ r.isUnit)).unit, ha⟩

theorem units_lift_baseChange (P R₂ R₀ : CommRingCat.{0}) (f₂ : P ⟶ R₂) (g₂ : R₂ ⟶ R₀) (hR : Nontrivial R₀ → IsLocalRing R₂)
    (hg₂ : Function.Surjective g₂) (A : Over (Spec P)) [GrpObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (Units.map (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left.appTop.hom.toMonoidHom) := by
  have hpb : IsPullback (fst A (Over.mk (Spec.map (f₂ ≫ g₂)))).left (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left
      A.hom (Over.mk (Spec.map (f₂ ≫ g₂))).hom := IsPullback.of_hasPullback _ _
  obtain ⟨G, -, hAb, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback P R₀ (f₂ ≫ g₂).hom A _ _ _ hpb
  letI := G
  have hbij := GlobalTheory.globalFns_holds _ _ (hAb hA)
  let e := RingEquiv.ofBijective _ hbij
  intro u
  let u₀ : Γ((Over.mk (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left).left, ⊤) := u.1
  have hu' : IsUnit (e.symm u₀) := by have := u.isUnit.map e.symm; exact this
  have hr : IsUnit ((Scheme.ΓSpecIso R₀).hom.hom (e.symm u₀)) := hu'.map _
  obtain ⟨r₂, hr₂⟩ := units_lift_of_surjective hR g₂.hom hg₂ hr.unit
  have hv : IsUnit ((snd A (Over.mk (Spec.map f₂))).left.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) :=
    (r₂.isUnit.map (Scheme.ΓSpecIso R₂).inv.hom).map _
  refine ⟨hv.unit, Units.ext ?_⟩
  have hw : (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left ≫ (snd A (Over.mk (Spec.map f₂))).left =
      (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left ≫ Spec.map g₂ := by
    rw [← Over.comp_left, whiskerLeft_snd]; rfl
  have hn := Scheme.ΓSpecIso_inv_naturality g₂
  have h1 : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) =
      (Scheme.ΓSpecIso R₀).inv.hom (g₂.hom r₂) := by
    have := congrArg (fun φ => φ.hom (r₂ : R₂)) hn
    exact this.symm
  have key : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) = e.symm u₀ := by
    rw [h1, hr₂, IsUnit.unit_spec]
    exact congrArg (fun φ => φ.hom (e.symm u₀)) (Scheme.ΓSpecIso R₀).hom_inv_id
  have h2 := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) hw
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  simp only [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe]
  exact h2.trans ((congrArg _ key).trans (e.apply_symm_apply u₀))

theorem surjective_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁) : Function.Surjective f₂ := by
  intro y
  obtain ⟨x, hx⟩ := hg₁ (g₂ y)
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, -, hp⟩ := H.2.2 x y hx
  exact ⟨p, hp⟩

theorem pic_eq_zero_of_pull_eq_zero : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ hg₁ hg₂ A _ A₁ A₂ φ₁ φ₂ hA h₁ h₂ c hc₁ hc₂
  haveI : Flat A.hom := by have := hA.smooth; infer_instance
  have hf₂ := surjective_of_isPullback h hg₁
  have hloc : Nontrivial R₀ → IsLocalRing R₂ := fun _ => by
    haveI : Nontrivial R₂ := g₂.hom.domain_nontrivial
    exact IsLocalRing.of_surjective' f₂.hom hf₂
  let T : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let T₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let T₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let T₀ : Over (Spec P) := Over.mk (Spec.map (f₂ ≫ g₂))
  let j₁ : T₁ ⟶ T := Over.homMk (Spec.map f₁) (by simp [T, T₁])
  let j₂ : T₂ ⟶ T := Over.homMk (Spec.map f₂) (by simp [T, T₂])
  let k₁ : T₀ ⟶ T₁ := Over.homMk (Spec.map g₁) (by simp only [T₀, T₁, Over.mk_hom]; rw [← Spec.map_comp, h.w])
  let k₂ : T₀ ⟶ T₂ := Over.homMk (Spec.map g₂) (by simp [T₀, T₂, Spec.map_comp])
  have hM : GlobalTheory.DualOpen.Milnor j₁.left j₂.left k₁.left k₂.left := GlobalTheory.DualOpen.Milnor.of_isPullback h hg₂
  have key := GlobalTheory.DualOpen.pic_eq_zero_of_milnor (Spec P) A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
    (units_lift_baseChange P R₂ R₀ f₂ g₂ hloc hg₂ A hA)
  let s : A ⟶ A ⊗ T := lift (𝟙 A) (Over.homMk A.hom (by simp [T]))
  have hs : s.left ≫ (fst A T).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have hc : c = GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.pull (fst A T).left c) := by
    rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id]
  rw [hc, key (GlobalTheory.CechPic.pull (fst A T).left c) ?_ ?_, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₁.lift_fst (fst A T₁).left (snd A T₁).left ((Over.w (fst A T₁)).trans (Over.w (snd A T₁)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₁, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₂.lift_fst (fst A T₂).left (snd A T₂).left ((Over.w (fst A T₂)).trans (Over.w (snd A T₂)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₂, map_zero]

end GlobalTheory.ArtinPicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointWithZeroSecondCoordLeftCompSnd
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.CupA

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem spOver_left {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (spOver (R := R) φ).left = spMap (φ : D →+* D') := rfl

theorem pointWithZeroSecondCoord_left_comp_fst {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left ≫ (fst A B).left = x.left := by
  rw [← Over.comp_left]; unfold pt0; rw [lift_fst]

theorem ptV_fst (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (ptV v x).left ≫ (fst A B).left = spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫ x.left := by
  rw [← Over.comp_left]; unfold ptV; rw [lift_fst]; rfl

theorem ptV_snd (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (ptV v x).left ≫ (snd A B).left = spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left := by
  rw [← Over.comp_left]; unfold ptV; rw [lift_snd]; rfl

theorem pointWithZeroSecondCoord_left_comp_snd (v : epsR R ⟶ B) (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (pt0 B x).left ≫ (snd A B).left =
      spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left := by
  have h := congrArg (fun p : Pt (A ⊗ B) D ↦ (p ≫ snd A B).left)
    (ContrMor.spOver_fst_ptV v hv x).symm
  simpa only [Over.comp_left, spOver_left, Category.assoc, ptV_snd] using h

theorem epsMap_fst {D : Type} [CommRing D] [Algebra R D] (c : DualNumber R) :
    (EpsWeil.epsMap R D c).fst = algebraMap R D c.fst := by
  simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem epsMap_inl {D : Type} [CommRing D] [Algebra R D] (b : R) :
    EpsWeil.epsMap R D (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (algebraMap R D b) := by
  simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem epsMap_inr {D : Type} [CommRing D] [Algebra R D] (b : R) :
    EpsWeil.epsMap R D (TrivSqZeroExt.inr b) = TrivSqZeroExt.inr (algebraMap R D b) := by
  ext <;> simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl', Algebra.smul_def]

theorem snd_epsHom' {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp [epsHom, DualNumber.lift_apply_apply]

theorem epsHom_inl' {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (r : D) : epsHom φ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r) := by
  ext
  · simp [epsHom, DualNumber.lift_apply_apply]
  · simp [snd_epsHom']

theorem dualVal_eq (v : epsR R ⟶ B) (β : Form (B.hom ≫ 𝟙 _)) :
    (SqExt.dual R).val v.left (pt_w v) β.1 = TrivSqZeroExt.inr (tanVal v β) := by
  ext
  · exact (SqExt.dual R).π_val v.left (pt_w v) β
  · exact (tanVal_apply v β).symm

def eA (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    m₁.functor.obj (trivAt (pt0 B x)) ⟶ m₁.functor.obj (trivAt (ptV v x)) where
  φ := { (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) with
    commutes' := fun r ↦ (TrivSqZeroExt.inlAlgHom R D D).commutes r }
  φ₀ := (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D)
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (TrivSqZeroExt.inlAlgHom R D D : D →+* DualNumber D) ≫ (pt0 B x).left ≫ (fst A B).left =
      (ptV v x).left ≫ (fst A B).left
    rw [pointWithZeroSecondCoord_left_comp_fst, ptV_fst]

def uA (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    trivAt x ⟶ m₁.functor.obj (trivAt (pt0 B x)) where
  φ := { RingHom.id D with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id D) ≫ x.left = (pt0 B x).left ≫ (fst A B).left
    rw [pointWithZeroSecondCoord_left_comp_fst, spMap_id]
    exact Category.id_comp _

abbrev yV (v : epsR R ⟶ B) (D : Type) [CommRing D] [Algebra R D] : Sp (DualNumber D) ⟶ B.left :=
  spMap (EpsWeil.epsMap R D : DualNumber R →+* DualNumber D) ≫ v.left

theorem yV_w (v : epsR R ⟶ B) (D : Type) [CommRing D] [Algebra R D] :
    yV v D ≫ B.hom ≫ 𝟙 _ = spMap (algebraMap R (epsExt R D).C) :=
  pt_w (spOver (EpsWeil.epsMap R D) ≫ v)

section Bside

variable (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
  (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D)

def cB (hv : IsTangent v) : (epsExt R D).thick _ ((epsExt R D).red_w (yV_w v D)) ⟶ m₂.functor.obj (thickAt B x) where
  φ := { RingHom.id (DualNumber D) with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := (DividedPowers.DPMorphism.id _).isDPMorphism
  pt := by
    change spMap (RingHom.id D) ≫ spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ yV v D =
      (pt0 B x).left ≫ (snd A B).left
    rw [pointWithZeroSecondCoord_left_comp_snd v hv, spMap_id]
    exact Category.id_comp _

def u0B (hv : IsTangent v) : Thick.triv (epsExt R D).B _ ((epsExt R D).red_w (yV_w v D)) ⟶ m₂.functor.obj (trivAt (pt0 B x)) where
  φ := { RingHom.id D with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id D
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id D) ≫ spMap (TrivSqZeroExt.fstHom R D D : DualNumber D →+* D) ≫ yV v D =
      (pt0 B x).left ≫ (snd A B).left
    rw [pointWithZeroSecondCoord_left_comp_snd v hv, spMap_id]
    exact Category.id_comp _

def u1B : Thick.triv (epsExt R D).C (yV v D) (yV_w v D) ⟶ m₂.functor.obj (trivAt (ptV v x)) where
  φ := { RingHom.id (DualNumber D) with commutes' := fun _ ↦ rfl }
  φ₀ := RingHom.id (DualNumber D)
  comm := fun _ ↦ rfl
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  pt := by
    change spMap (RingHom.id (DualNumber D)) ≫ yV v D = (ptV v x).left ≫ (snd A B).left
    rw [ptV_snd, spMap_id]
    exact Category.id_comp _

theorem bval (hv : IsTangent v) (β : Form (B.hom ≫ 𝟙 _)) (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
    (hs : ∀ r, s.φ r = TrivSqZeroExt.inl r) (hi : ∀ r, i.φ r = r) :
    ev β.1 (m₂.functor.map s) - ev β.1 (m₂.functor.map i) =
      TrivSqZeroExt.inr (algebraMap R D (tanVal v β)) := by
  let E := epsExt R D
  have k1 := Form.ev_sq β (u0B m₂ v x hv) (m₂.functor.map s) (E.secHom (E.red_w (yV_w v D)) E.i E.π_i)
    (cB m₂ v x hv) rfl rfl (fun r ↦ by
      change s.φ r = TrivSqZeroExt.inl r
      exact hs r)
  have k2 := Form.ev_sq β (u1B m₂ v x) (m₂.functor.map i) (E.idHom (yV_w v D))
    (cB m₂ v x hv) rfl rfl (fun r ↦ by
      change i.φ r = r
      exact hi r)
  rw [k1, k2]
  rw [add_sub_add_right_eq_sub, ← map_sub]
  have vm := (SqExt.dual R).val_map E (EpsWeil.epsMap R D) (Algebra.ofId R D)
    (fun c ↦ (epsMap_fst c).symm) (fun b ↦ epsMap_inl b) v.left (pt_w v) (yV v D) (yV_w v D) rfl β
  calc _ = E.val (yV v D) (yV_w v D) β.1 := rfl
    _ = _ := by rw [vm, dualVal_eq]; exact epsMap_inr _

end Bside

theorem alg {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (t : R)
    (Ae Ai As Bi : DualNumber D) (Bτ Bi' Bs' Ab Ae' X1 X2 X3 X4 Y1 Y2 W : DualNumber D') (Aa fvv fvt C' Z : D') (C : D)
    (hX1 : X1 = epsHom φ As) (hX2 : X2 = TrivSqZeroExt.inl Aa) (hX3 : X3 = epsHom φ Ai) (hX4 : Ab = X4)
    (hY1 : Y1 = TrivSqZeroExt.inl Aa) (hY2 : Y2 = epsHom φ Ae) (hW : W = epsHom φ Bi) (hZ : Z = φ C)
    (hfvt : fvt = (-t) • fvv)
    (hAs : As = Ae + Ai) (hAb : Y1 + Ae' = Y2 + Ab) (hAa : fvv + C' = Z + Aa)
    (hBτ : Bi' = W + Bτ) (hBs : Bs' - Bi' = TrivSqZeroExt.inr (algebraMap R D' t)) :
    (X1 * Bτ - X2 * Bs' - X3 * Bτ + X4 * Bi').snd + -fvt =
      ((Ae' * Bi').snd - algebraMap R D' t * C') - φ ((Ae * Bi).snd - algebraMap R D t * C) := by
  subst hX1 hX2 hX3 hX4 hY1 hY2 hW hZ hfvt
  have h1 : epsHom φ As = epsHom φ Ae + epsHom φ Ai := by rw [hAs, map_add (f := _)]
  have key : epsHom φ As * Bτ - TrivSqZeroExt.inl Aa * Bs' - epsHom φ Ai * Bτ + Ab * Bi' =
      Ae' * Bi' - epsHom φ (Ae * Bi) - TrivSqZeroExt.inl Aa * TrivSqZeroExt.inr (algebraMap R D' t) := by
    rw [map_mul]
    linear_combination Bτ * h1 - Bi' * hAb - epsHom φ Ae * hBτ - TrivSqZeroExt.inl Aa * hBs
  rw [key, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_sub, snd_epsHom', TrivSqZeroExt.inl_mul_inr,
    TrivSqZeroExt.snd_inr, smul_eq_mul, map_sub, map_mul, AlgHom.commutes, Algebra.smul_def, map_neg]
  linear_combination (algebraMap R D' t) * hAa


open Classical in
def kFn (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) : Fn0 A := fun D _ _ x ↦
  if h : ∃ i : trivAt (ptV v x) ⟶ thickAt B x, ∀ r, i.φ r = r then
    ((show DualNumber D from ev a (eA m₁ v x)) * (show DualNumber D from ev β.1 (m₂.functor.map h.choose))).snd -
      algebraMap R D (tanVal v β) * (show D from ev a (uA m₁ x))
  else 0

theorem kFn_eq (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (v : epsR R ⟶ B) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) {D : Type} [CommRing D]
    [Algebra R D] (x : Pt A D) (i : trivAt (ptV v x) ⟶ thickAt B x) (hi : ∀ r, i.φ r = r) :
    kFn m₁ m₂ v a β D x =
      ((show DualNumber D from ev a (eA m₁ v x)) * (show DualNumber D from ev β.1 (m₂.functor.map i))).snd -
        algebraMap R D (tanVal v β) * (show D from ev a (uA m₁ x)) := by
  have h : ∃ i : trivAt (ptV v x) ⟶ thickAt B x, ∀ r, i.φ r = r := ⟨i, hi⟩
  unfold kFn
  rw [dite_eq_left h]
  congr 3
  have he : h.choose = i := Thick.Hom.ext' (AlgHom.ext fun r ↦ (h.choose_spec r).trans (hi r).symm)
  exact congrArg (fun j ↦ ev β.1 (m₂.functor.map j)) he

end GlobalTheory.PtExt.CupA

open GlobalTheory.PtExt.CupA in
theorem GlobalTheory.PtExt.cohom_contr_cupA : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (v : epsR R ⟶ B), IsTangent v → ∀ (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Form (B.hom ≫ 𝟙 _)) (κ : Fn1 A), IsContr (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle β.1)).1 v κ → Cohom (whole A) κ (fv ((-tanVal v β) • a)) := by
  intro R _ A B _ _ m₁ m₂ v hv a β κ hκ
  refine ⟨kFn m₁ m₂ v a β, ?_⟩
  intro D _ _ D' _ _ φ x _
  obtain ⟨s, i, s', i', a', b, τ, hs, hi, hs', hi', ha, hb, hτ⟩ := (GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product R A B v hv).1 D D' φ x
  have hK := hκ D D' φ x s i s' i' a' b τ hs hi hs' hi' ha hb hτ
  change κ D D' φ x = TrivSqZeroExt.snd (R := D') (M := D')
    ((show DualNumber D' from τ.φ (ev a (m₁.functor.map s))) * (show DualNumber D' from ev β.1 (m₂.functor.map τ)) -
      (show DualNumber D' from s'.φ (ev a (m₁.functor.map a'))) * (show DualNumber D' from ev β.1 (m₂.functor.map s')) -
      (show DualNumber D' from τ.φ (ev a (m₁.functor.map i))) * (show DualNumber D' from ev β.1 (m₂.functor.map τ)) +
      (show DualNumber D' from i'.φ (ev a (m₁.functor.map b))) * (show DualNumber D' from ev β.1 (m₂.functor.map i'))) at hK
  have fAs : (show DualNumber D from ev a (m₁.functor.map s)) = (show DualNumber D from ev a (eA m₁ v x)) + (show DualNumber D from ev a (m₁.functor.map i)) := by
    rw [show m₁.functor.map s = eA m₁ v x ≫ m₁.functor.map i from Thick.Hom.ext' (AlgHom.ext fun r ↦ by
      change s.φ r = i.φ (TrivSqZeroExt.inl r)
      exact (hs r).trans (hi _).symm), ev_comp]
    change i.φ _ + _ = _
    erw [hi]
  have fAb := ev_sq a (m₁.functor.map a') (eA m₁ v (spOver φ ≫ x)) (eA m₁ v x) (m₁.functor.map b) (fun r ↦ by
    change TrivSqZeroExt.inl (a'.φ r) = b.φ (TrivSqZeroExt.inl r)
    exact (congrArg TrivSqZeroExt.inl (ha r)).trans ((hb _).trans (epsHom_inl' φ r)).symm)
  have fAa := ev_sq a (trivMap φ x) (uA m₁ (spOver φ ≫ x)) (uA m₁ x) (m₁.functor.map a') (fun r ↦ by
    change φ r = a'.φ r
    exact (ha r).symm)
  have fBτ := Form.ev_sq β (m₂.functor.map b) (m₂.functor.map i') (m₂.functor.map i) (m₂.functor.map τ) rfl rfl
    (fun r ↦ by
      change i'.φ (b.φ r) = τ.φ (i.φ r)
      exact (hi' _).trans ((hb r).trans (((congrArg τ.φ (hi r)).trans (hτ r)).symm)))
  have fBs := bval m₂ v (spOver φ ≫ x) hv β s' i' hs' hi'
  have e1 := kFn_eq m₁ m₂ v a β x i hi
  have e2 := kFn_eq m₁ m₂ v a β (spOver φ ≫ x) i' hi'
  change (Fn1.add κ (fv ((-tanVal v β) • a)).neg) D D' φ x = _
  unfold Fn1.add Fn1.neg
  rw [hK, e1, e2]
  exact alg φ (tanVal v β) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fv a D D' φ x) _ _ _ _ (hτ _) (hs' _) (hτ _) (hi' _).symm
    rfl (hb _) (hτ _) (ha _) rfl fAs fAb fAa fBτ fBs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (inc : G ⟶ G'), IsMonHom inc → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → ∃ t : LB.Gen (letI := A'.isAb.comm; (abelian₂ A'.A A'.L).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.f) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left), t.IsGen := by
  first | exact @GlobalTheory.Mum.pull_gen_lam_generic | exact GlobalTheory.Mum.pull_gen_lam_generic | (intros; apply GlobalTheory.Mum.pull_gen_lam_generic <;> assumption)
end

