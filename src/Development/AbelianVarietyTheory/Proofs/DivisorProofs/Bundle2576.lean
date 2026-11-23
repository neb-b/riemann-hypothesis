module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFac

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, fun i j => ?_, fun Z r z J => map_zpow _ _ _⟩
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => (zpow_mul _ _ _).symm)

theorem exists_norm {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (S₀ ⟶ X)} {ε' : K' → ℤ}
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hF : FormEq (fun k => e ≫ φ k) ε φ' ε')
    (w : LB.Gen (LB.LinComb M φ ε)) (hw : w.IsGen) (v : LB.Gen (LB.LinComb M φ' ε')) (hv : v.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ y J, Good M y J → val u e y J = val v (𝟙 _) y J := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := φ) (ε' := ε) (fun U _ h => by
      have q := hF U (fun g => h (p ≫ g))
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [q, mul_inv_cancel, _root_.mul_one])
    (LB.mulGen M _ _ _ _ w (LB.pullGen M _ _ (LB.mulGen M _ _ _ _ v (LB.invGen M _ _ (LB.pullGen M _ _ w e))) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hv
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hw _))) _))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  rw [vu _ _ y J hJ, val_mul hJ, val_pull hJ, he, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, mul_comm,
    inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R]

theorem tr_left (D : DegPre R) (mu : D.X) :
    (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left =
      (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  refine (lift_snd _ _).trans ?_
  refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
  rw [Category.comp_id]
  exact congrArg (DegPre.prB D (FractionRing R) * ·) (DVR.comp_cP D _ mu).symm

theorem prod_t (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) (n j : ℤ) {T : Over (Sp R)} (y : T ⟶ D.P.A)
    {U : Type} [CommGroup U] (g : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, g (y.left ≫ tφ D a β k) ^ tε n j k = g y.left ^ (n - 1) * g (y * DVR.cP D T β).left *
      (g (DVR.cP D T β).left)⁻¹ * g (1 : T ⟶ D.P.A).left * g (y ≫ a).left ^ j := by
  have e₀ : y.left ≫ tφ D a β 0 = y.left := Category.comp_id _
  have e₁ : y.left ≫ tφ D a β 1 = (y * DVR.cP D T β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul y (𝟙 _) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : y.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D y β)
  have e₃ : y.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) y)
  have e₄ : y.left ≫ tφ D a β 4 = (y ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_fac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a] (hh : ∀ y, D.c (h y) = D.c y ≫ a)
    (n j : ℤ) (mu β β' : D.X) (w : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) (hw : w.IsGen) :
    ∃ u, IsFac D a h n j mu β β' u := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (D.psi mu) (D.psi_gen mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (D.psi (h mu)) (D.psi_gen _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rigK (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) (n + j)
  have z₁ : DegPre.zF D (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R) = 1 := lift_snd _ _
  have z₃ : DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DVR.cP D _ mu := by
    rw [DVR.trF_eq, DVR.tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (fst (TF (R := R) (FractionRing R)) D.P.A).left
    (DegPre.zF D (FractionRing R)).left (congrArg (fun q => q.left) z₁) (fun U _ g => by
      have a₁ : ∀ χ, jFK (R := R) (FractionRing R) ≫ ptK (D.c χ) = (DVR.cP D (TF (R := R) (FractionRing R)) χ).left :=
        fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
          (1 : TF (R := R) (FractionRing R) ⟶ D.P.A).left := (Category.assoc _ _ _).symm
      have q₁ := prod_t D a β' n j (DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R)) g
      have q₂ := prod_t D a β n j
        (DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) g
      have b₁ : (1 : TF (R := R) (FractionRing R) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      have b₂ : DVR.cP D (TF (R := R) (FractionRing R)) mu ≫ a = DVR.cP D _ (h mu) := by
        rw [DVR.cP, DVR.cP, hh, Category.assoc]
      conv_rhs at q₁ => rw [z₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, b₂, ← DVR.cPoint_add]
      simp only [Over.comp_left, Category.assoc] at q₁ q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂)
      (D.tau mu β)) p₃) (jFK (R := R) (FractionRing R)))
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) (DVR.tau_isGen D mu β)) h₃) _)
  refine ⟨u, hu, fun z J hJ => (vu z J hJ).trans ((val_pull hJ _ _ _).trans ?_)⟩
  rw [Category.id_comp]
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) rfl)) (v₃ _ _ _ _))

theorem fac_exists_unique_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ _ D a h ha hh n j mu β β' u₀ hu₀
  have hL := D.toPre.P.isLB
  have hs := DVR.surj_appTop D.toPre (FractionRing R) GlobalTheory.globalFns_holds
  obtain ⟨w, hw, vw⟩ := exists_gen hL (φ' := dφ D.toPre a mu β β') (ε' := dε n j) (fun U _ g => by
      refine Finset.prod_congr rfl ?_
      rintro (k | k) -
      · rfl
      · simp only [dφ, Sum.elim_inr]
        rw [← Category.assoc, ← tr_left, Category.assoc])
    (LB.pullGen D.toPre.P.L _ _ u₀ (DegPre.prB D.toPre (FractionRing R)).left) (DVR.pullGen_isGen _ _ _ _ hu₀ _)
  refine ⟨exists_fac D.toPre a h hh n j mu β β' w hw, fun u u' hu hu' => ?_, fun u hu => ?_⟩
  · have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    exact gen_unique hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
      (congrArg (fun q => q.left) z₁) hs hu.1 hu'.1 (fun y J hJ => (hu.2 y J hJ).trans (hu'.2 y J hJ).symm)
  · obtain ⟨c, hc⟩ := GlobalTheory.WeilMul.exists_ratio hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left hs hu hw
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c, fun Z x z J hJ => ?_⟩
    have e : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c) = c := Iso.hom_inv_id_apply _ c
    have e₂ := (hc Z x z J hJ).trans ((gs_pull x (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z ⊤ trivial c).symm)
    rw [vw _ _ z J hJ, val_pull hJ] at e₂
    refine Eq.trans ?_ (congrArg₂ (· * ·) (e₂.trans (congrArg (fun q => gs x z ⊤
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left.appTop.hom q)) e.symm)) rfl)
    rw [← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.TwFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationPullbackOfIntegralThetaFunctional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) {T : Over (Sp R)} (ρ : T ⟶ D.P.A) (β : D.X) (n j : ℤ)
    {U : Type} [CommGroup U] (hh : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, hh (ρ.left ≫ tφ D a β i) ^ tε n j i = hh ρ.left ^ (n - 1) * hh (DVR.cP D T β * ρ).left *
      (hh (DVR.cP D T β).left)⁻¹ * hh (1 : T ⟶ D.P.A).left * hh (ρ ≫ a).left ^ j := by
  have e₁ : ρ.left ≫ tφ D a β 1 = (DVR.cP D T β * ρ).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (toUnit _ ≫ D.c β)).trans (by
      rw [Category.comp_id, ← DVR.cP, DVR.comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ β)
  have e₃ : ρ.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  have e₀ : ρ.left ≫ tφ D a β 0 = ρ.left := Category.comp_id _
  have e₄ : ρ.left ≫ tφ D a β 4 = (ρ ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem iota_c (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (hE : EndData D a a' h h') (α mu : D.X)
    (u : LB.Gen (IotaLB D a α (h' α))) (hu : IsIota u) (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J)
    (hJ : Good D.P.L z J) :
    val (D.tau (h mu) α) r z J = val (D.tau mu (h' α)) r z J * val u (r ≫ D.xK mu) z J := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, hma', hr, -, hc, hB⟩ := hE
  obtain ⟨t, ht, t₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T (h' α) = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  have key := gen_unique' D.P.isLB (φ := Sum.elim (D.Oφ (𝟙 _) (h' α)) (D.Oφ a α)) (ε := Sum.elim Oε Oinvε)
    (u' := LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) _ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (fun y I hI => by
      let T : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
      have C : IsCub (cubV D.cub (T := T) y I) := isCub_cubV D.cub hI
      have e := (ros_add D.cub hG D.P.isAb a a' t ht t₀ (T := T) hI 1 1 (DVR.cP D _ α)).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      have e' : val₂ t (T := T) y I 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
      have o : (1 : T ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
      have k : eSec D.P.A ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
        rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
      have n := hu.2 _ (𝟙 _) y I hI
      rw [Category.id_comp] at n
      rw [val_inv, val_pull hI, k]
      exact n.trans (inv_eq_one.2 e').symm) Z (r ≫ D.xK mu) z J hJ
  have m : D.xK mu ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = D.pt2 mu α := by
    rw [← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]; rfl
  have b := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hB t ht t₀ mu α) r)
  rw [val_pull hJ] at b
  rw [val_inv, val_pull hJ, Category.assoc, m] at key
  rw [key, ← b, mul_inv_cancel_right]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem formEq_pull (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (mu ν α β β' : D.X)
    (aK : DegPre.BF D (FractionRing R) ⟶ DegPre.BF D (FractionRing R))
    (h₁ : aK ≫ DegPre.prB D (FractionRing R) = DegPre.prB D (FractionRing R) ≫ a)
    (h₂ : aK ≫ DegPre.trF D (FractionRing R) ν ≫ DegPre.prB D (FractionRing R) =
      DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) ≫ a) :
    FormEq (Sum.elim (Sum.elim (fun i => aK.left ≫ DegPre.deltaφ D (FractionRing R) k α ν i)
        (fun i => (DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β') (D.Oφ a (α + k • ν)) i))
        (fun i => (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β) (D.Oφ a α) i))
      (Sum.elim (Sum.elim (DegPre.deltaε k) (Sum.elim Oε Oinvε)) (fun i => - Sum.elim Oε Oinvε i))
      (dφ D a mu β β') (dε 0 k) := by
  intro U _ hh
  have io : ∀ (ρ : DegPre.BF D (FractionRing R) ⟶ D.P.A) (ξ δ : D.X),
      ∏ i, hh (ρ.left ≫ Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a ξ) i) ^ Sum.elim Oε Oinvε i =
        (hh (DVR.cP D _ δ * ρ).left * (hh (DVR.cP D _ δ).left)⁻¹ * (hh ρ.left)⁻¹ *
          hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left) *
        ((hh (DVR.cP D _ ξ * (ρ ≫ a)).left)⁻¹ * hh (DVR.cP D _ ξ).left * hh (ρ ≫ a).left *
          (hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left)⁻¹) := fun ρ ξ δ => by
    refine DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ ?_ ?_
    · simp only [Sum.elim_inl, WeightPf.Oφ_comp, Category.comp_id]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ D ρ δ hh
    · simp only [Sum.elim_inr, WeightPf.Oφ_comp]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ_inv D (ρ ≫ a) ξ hh
  have p₁ := DVR.prod_fam D (FractionRing R) aK (α + k • ν) k hh
  have p₂ := DVR.prod_fam D (FractionRing R) (aK ≫ DegPre.trF D (FractionRing R) ν) α k hh
  have q₁ := prod_tφ D a (DegPre.prB D (FractionRing R)) β' 0 k hh
  have q₂ := prod_tφ D a (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) β 0 k hh
  rw [h₁] at p₁
  rw [Category.assoc, h₂, ← Category.assoc] at p₂
  simp only [Over.comp_left, Category.assoc] at p₂ q₂
  refine (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₁ (DVR.prod_neg _ _ p₂)) (io _ _ _))
    (DVR.prod_neg _ _ (io _ _ _))).trans
    (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).symm)
  simp only [Over.comp_left, Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (mu α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))) (u' : LB.Gen (IotaLB D.toPre a (α + k • h mu) (h' (α + k • h mu)))) (s : SecT D.toPre a 0 k (h' α)) (s' : SecT D.toPre a 0 k (h' (α + k • h mu))), IsIota u → IsIota u' → IsPullT u (F.f α) s → IsPullT u' (F.f (α + k • h mu)) s' → TRel h mu s s' := by
  intro R _ _ _ _ D a a' h h' hE k F mu α u u' s s' hu hu' hs hs'
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, -, -, hch, -, -⟩ := id hE
  have hL := D.toPre.P.isLB
  obtain ⟨⟨uF, huF, hcF⟩, -⟩ := DVR.gen_fe (D := D.toPre) (F := FractionRing R) hG k (h mu) α
  have feF := (secRel_iff hL _ _ _ _ _ _ _ _ _ uF).1 (F.F.fe (h mu) α uF huF hcF)
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by unfold scal; rw [map_one, map_one]
  have ext : ∀ β (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (F.F.s β) r z J = sval (F.f β) (r ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J := by
    intro β Z r z J hJ
    have e := F.ext β
    rw [h1] at e
    exact (DVR.SectionScalarValuation.secScal_sval e r z hJ).symm
  let aK : DegPre.BF D.toPre (FractionRing R) ⟶ DegPre.BF D.toPre (FractionRing R) :=
    lift (fst _ _) (DegPre.prB D.toPre (FractionRing R) ≫ a)
  have aK_pr : aK ≫ DegPre.prB D.toPre (FractionRing R) = DegPre.prB D.toPre (FractionRing R) ≫ a := lift_snd _ _
  have aK_fst : aK ≫ fst _ _ = fst _ _ := lift_fst _ _
  have cPh : ∀ T, DVR.cP D.toPre T (h mu) = DVR.cP D.toPre T mu ≫ a := fun T => by
    rw [DVR.cP, hch, ← Category.assoc]; rfl
  have trpr : ∀ ν, DegPre.trF D.toPre (FractionRing R) ν ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.prB D.toPre (FractionRing R) * DVR.cP D.toPre _ ν := fun ν => by
    rw [DVR.trF_eq, DVR.tr_pr, DVR.comp_cP]
  have M1 : aK ≫ DegPre.trF D.toPre (FractionRing R) (h mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R) ≫ a := by
    haveI := hma
    rw [trpr, MonObj.comp_mul, aK_pr, DVR.comp_cP, ← Category.assoc, trpr, MonObj.mul_comp, cPh]
  haveI := hma
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.prB D.toPre (FractionRing R) = 1 := lift_snd _ _
  have M2 : DegPre.zF D.toPre (FractionRing R) ≫ aK = DegPre.zF D.toPre (FractionRing R) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, aK_fst]
    · rw [Category.assoc, aK_pr, ← Category.assoc, z₂, MonObj.one_comp]
  have M3 : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.trF D.toPre (FractionRing R) mu ≫
      DegPre.prB D.toPre (FractionRing R) = DVR.cP D.toPre _ mu := by
    rw [trpr, MonObj.comp_mul, z₂, DVR.comp_cP, _root_.one_mul]
  intro v hv Z x z J hJ
  have wv : ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      val (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ uF aK.left)
        (LB.pullGen _ _ _ u' (DegPre.prB D.toPre (FractionRing R)).left)) (LB.invGen _ _ _ (LB.pullGen _ _ _ u
          (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left))) x z J =
      val uF (x ≫ aK.left) z J * val u' (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J *
        (val u (x ≫ (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left) z J)⁻¹ :=
    fun Z x z J hJ => by rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]
  have key := (gen_unique' hL (formEq_pull D.toPre a k mu (h mu) α (h' α) (h' (α + k • h mu)) aK aK_pr M1)
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
    (congrArg (fun q => q.left) z₁) (DVR.surj_appTop D.toPre _ hG) hv.1
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huF _)
      (DVR.pullGen_isGen _ _ _ _ hu'.1 _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu.1 _)))
    (fun y I hI => by
      have e₁ := val_corr hI hcF (𝟙 _)
      rw [val_pull hI, Category.id_comp] at e₁
      have e₂ := DVR.val_famMult (D := D.toPre) (F := FractionRing R) (𝟙 _) hI k (h mu) α
      rw [Over.id_left, Category.id_comp, DVR.TWM.val_powGen, DVR.TWM.val_powGen] at e₂
      have e₃ : val u' (1 : TF (R := R) (FractionRing R) ⟶ D.toPre.P.A).left y I = 1 :=
        hu'.2 _ (TF (R := R) (FractionRing R)).hom y I hI
      have e₄ := iota_c D.toPre a a' h h' hE α mu u hu _ (jFK (R := R) (FractionRing R)) y I hI
      have e₅ : jFK (R := R) (FractionRing R) ≫ D.toPre.xK mu = (DVR.cP D.toPre (TF (R := R) (FractionRing R)) mu).left :=
        (Category.assoc _ _ _).symm
      rw [wv _ _ y I hI, hv.2 y I hI, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, M2, z₂, M3, e₁, e₂, e₃, e₄, e₅]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) Z x z J hJ).trans (wv Z x z J hJ)
  have f₁ : (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left =
      (x ≫ aK.left) ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, aK_pr]
  have f₂ : ((x ≫ aK.left) ≫ (DegPre.trF D.toPre (FractionRing R) (h mu)).left) ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left := by
    have := congrArg (fun q => x ≫ q.left) M1
    simpa only [Over.comp_left, Category.assoc] using this
  rw [hs' _ _ z J hJ, hs _ _ z J hJ, key, f₁, ← ext _ _ _ z J hJ, feF _ _ z J hJ, ext _ _ _ z J hJ, f₂, Over.comp_left,
    _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_comm (val u _ z J), inv_mul_cancel_right]

end GlobalTheory.TwFam.PullRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.GenPull

theorem pull_comp_iso {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {F : Y ⟶ X} (H : LBIso M (L.pull F)) (h : Z ⟶ Y) :
    LBIso (M.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (chartPullSame L _ _ _ h fun _ => rfl) H

theorem pull_congr_iso {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {a b : Y ⟶ X} (e : a = b) :
    LBIso (L.pull a) (L.pull b) := e ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)

theorem pull_pull_iso {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  pull_comp_iso (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)) b

theorem pull_id_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

end GlobalTheory.TInj.GenPull


open GlobalTheory.TInj.GenPull in
theorem GlobalTheory.TInj.overPt_genPull : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  intro X g n B _ ζ sX c R _ _ V _ _ J J' D₀ A₀ G₀ _ _ U₀ f D hD A U hU y₀ α₀ hO κ hκ
  let G := (Over.pullback (specOf f)).obj G₀
  let p := pullback.fst G.hom (jK V)
  let q := pullback.fst G₀.hom (specOf f)
  let p₀ := pullback.fst G₀.hom (jK R)
  have hsq : jK V ≫ specOf f = κ ≫ jK R := hκ.symm
  let κG : pullback G.hom (jK V) ⟶ pullback G₀.hom (jK R) :=
    pullback.lift (p ≫ q) (pullback.snd _ _ ≫ κ) (by
      have c1 : q ≫ G₀.hom = G.hom ≫ specOf f := pullback.condition
      have c2 : p ≫ G.hom = pullback.snd G.hom (jK V) ≫ jK V := pullback.condition
      rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, hsq, Category.assoc])
  have hκf : κG ≫ p₀ = p ≫ q := pullback.lift_fst _ _ _
  have w : κG ≫ ((Over.pullback (jK R)).obj G₀).hom = ((Over.pullback (jK V)).obj G).hom ≫ κ :=
    pullback.lift_snd _ _ _
  have hκG : IsGrpPullback ((Over.pullback (jK V)).obj G) ((Over.pullback (jK R)).obj G₀) κ κG :=
    (isGrpPullback_pullback G₀ (jK R)).cancel
      (((isGrpPullback_pullback G (jK V)).comp (isGrpPullback_pullback G₀ (specOf f))).congr hsq hκf.symm) w
  have : IsMonHom U.gen.hom := U.gen_hom
  have : IsMonHom U₀.gen.hom := U₀.gen_hom
  have : IsMonHom U.gen.symm.hom := show IsMonHom U.gen.inv by infer_instance
  have hu : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G₀) A₀.A (𝟙 _) U₀.gen.hom.left := isGrpPullback_of_iso U₀.gen
  let π : A.A.left ⟶ A₀.A.left := U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left
  have hπ : IsGrpPullback A.A A₀.A κ π := (hu.comp (hκG.comp hg)).congr (by simp) rfl
  obtain ⟨hO₁, α₀₂, sα₀, hΛ₀⟩ := hO

  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hLG₀ : U₀.LG.L.IsLB := U₀.LG.isLB
  obtain ⟨wL, hwL, -⟩ := hU.lg
  have E1 : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull p) := U.ext
  have E2 : LBIso (U.LG.L.pull p) (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) := pull_comp_iso ⟨wL, hwL⟩ p
  have E4 : LBIso (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) (U₀.LG.L.pull (κG ≫ p₀)) :=
    pull_congr_iso hLG₀ (by rw [hκf, Iso.refl_hom, Over.id_left, Category.id_comp])
  have E3 : LBIso ((A₀.L.pull U₀.gen.hom.left).pull κG) (U₀.LG.L.pull (κG ≫ p₀)) := pull_comp_iso U₀.ext κG
  have E5 := pull_pull_iso A₀.isLB U₀.gen.hom.left κG
  have hA₀g := pull_isLB A₀.isLB U₀.gen.hom.left
  have X1 : LBIso (A.L.pull U.gen.hom.left) (A₀.L.pull (κG ≫ U₀.gen.hom.left)) :=
    LBIso.trans (pull_isLB A.isLB _) (pull_isLB hLG _) (pull_isLB A₀.isLB _) E1
      (LBIso.trans (pull_isLB hLG _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E2
        (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E4
          (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hA₀g _) (pull_isLB A₀.isLB _) E3.symm E5)))
  have X2 : LBIso ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) (A₀.L.pull π) := pull_comp_iso X1 _
  have X3 : LBIso A.L ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_id_iso A.isLB)
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
        (pull_congr_iso A.isLB (by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]))
        (pull_pull_iso A.isLB _ _).symm)
  have hA : LBIso A.L (A₀.L.pull π) :=
    LBIso.trans A.isLB (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A₀.isLB _) X3 X2
  have sπ := GlobalTheory.LamPull.exists_isSquare hπ.1.w
  have hΛ := GlobalTheory.LamPull.lbIso_lam_pull hπ A₀.isLB A.isLB hA sπ
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hΛA₀ : (abelian₂ A₀.A A₀.L).IsLB := DVR.linComb_isLB _ A₀.isLB _ _
  refine ⟨π ≫ α₀, ⟨hπ.comp hO₁, _ ≫ α₀₂, ⟨?_, ?_⟩,
    LBIso.trans hΛA (pull_isLB hΛA₀ _) (pull_isLB c.isLB _) hΛ (pull_comp_iso hΛ₀ _)⟩, ?_⟩
  · rw [Category.assoc, sα₀.1, ← Category.assoc, sπ.1, Category.assoc]
  · rw [Category.assoc, sα₀.2, ← Category.assoc, sπ.2, Category.assoc]
  · intro Z x x₀ hx
    have : Mono (jK R) := GlobalTheory.GenericBundleDescent.mono_jK R
    have : Mono p₀ := pullback.fst_of_mono
    have h1 : x ≫ U.gen.inv.left ≫ κG = x₀ ≫ U₀.gen.inv.left := by
      apply (cancel_mono p₀).1
      simp only [Category.assoc, hκf]
      exact hx
    show x ≫ (U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left) ≫ α₀ = x₀ ≫ α₀
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc x, h1]
    simp only [Category.assoc]
    rw [← Category.assoc U₀.gen.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingClassicalTraitSameGeometricFibrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRecharting_classicalTrait_same_geometric_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real), USame X.ρ ρ' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real), USame X.ρ ρ'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ ∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left := by
  first | exact @GlobalTheory.UPoinc.USpread.main | exact GlobalTheory.UPoinc.USpread.main | (intros; apply GlobalTheory.UPoinc.USpread.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmpleAlongPullback_transport_iso : ∀ {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn], gn ≫ pA = p → ∀ (π : Y ⟶ X) {L : LB X}, L.IsLB → ∀ {LA : LB XA}, LA.IsLB → ∀ {k m : ℕ} (b : Fin (m + 1) → H0 LA k), VeryAmpleAlong pA (𝟙 XA) LA b → ∀ (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ), (∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) → ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j = u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) → VeryAmpleAlong p π L σ := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_transport | exact GlobalTheory.Mum.veryAmpleAlong_transport | (intros; apply GlobalTheory.Mum.veryAmpleAlong_transport <;> assumption)
end

