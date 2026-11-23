module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SiegLift

theorem exists_level_of_forget : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal →
    SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  intro g n N B _ ζ k _ _ s c b ho hN3 hc hg
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hG := hL.globalFns
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hN : ((N : ℕ) : k) ≠ 0 := b.unit.ne_zero
  have hN₀ : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hz : IsPrimitiveRoot b.ζ N := IsPrimitiveRoot.coe_units_iff.1 (b.prim k (RingHom.id k))
  have hz₂ : IsPrimitiveRoot (b.ζ ^ 2) N := hz.pow_of_coprime 2 (Nat.coprime_two_left.2 ho)
  have card := GlobalTheory.card_torsion_geometricPoint_of_field GlobalTheory.card_torsion_abelianVariety _ c.A c.ab g hg

  obtain ⟨L, hLM, ⟨cu⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta hL _ c.A c.ab c.diag hD
    (DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hD _))
    (GlobalTheory.exists_gen_theta_of_isAbelianScheme k c.A c.ab _ hD)
  have toW : ∀ {m : ℕ} {T : Over (Sp k)} {x y : T ⟶ c.A} {u}, UU.CubWeil cu m x y u →
      Out.WeilIs c.A c.diag m x y u := fun H => hLM ▸ (UU.cubWeil_iff_weilIs hG c.ab H.1 H.2.1 _).1 H
  obtain ⟨f₁, f₂, f₃⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow k c.A c.diag c.P c.ab
    hD hc.1 c.isLB).2 N (Nat.pos_of_ne_zero hN₀)
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ c.A) := (powMonoidHom N).ker
  have hH : ∀ x : H, x.1 ^ N = 1 := fun x => x.2
  have ex : ∀ x y : H, ∃ u : kˣ, UU.CubWeil cu N x.1 y.1 (unitOn u) := fun x y => by
    obtain ⟨u, hu, -⟩ := UU.existsUnique_cubWeil cu (hH x) (hH y)
    obtain ⟨w, rfl⟩ : ∃ w : kˣ, unitOn w = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom u,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) u.val)⟩
    exact ⟨w, hu⟩
  choose w hw using ex
  have uq : ∀ x y u, UU.CubWeil cu N x.1 y.1 (unitOn u) → w x y = u := fun x y u H =>
    SiegelOfPolarised.unitOn_inj ((hw x y).unique H)
  have l : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y => uq _ _ _ (by
    have := (hw x y).mul_left (hw x' y)
    unfold unitOn at this ⊢
    rwa [map_mul])
  have sk : ∀ x y, w y x = (w x y)⁻¹ := fun x y => uq _ _ _ (by
    have := (hw x y).symm
    unfold unitOn at this ⊢
    rwa [map_inv])
  have u1 : unitOn (1 : kˣ) = 1 := map_one _
  let e : H →* H →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) fun y y' => by
    rw [sk (y * y'), l, mul_inv, ← sk, ← sk]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨l₁, add₁, w₁⟩ := exists_symplectic_hom (g := g) (Nat.pos_of_ne_zero hN₀) hz₂
    (fun x => Subtype.ext (hH x)) (fun m hm => by
      obtain ⟨r, hr⟩ := hm
      have hm : (m : k) ≠ 0 := left_ne_zero_of_mul (by rwa [hr, Nat.cast_mul] at hN)
      refine Eq.trans (Nat.card_congr ?_) (card k (𝟙 _) m hm)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ N = 1 by
        rw [hr, pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => uq _ _ _ (u1 ▸ UU.cubWeil_self cu (hH x))) (fun x hx => Subtype.ext (by
      have t := GlobalTheory.CubNondeg.main hL _ c.A c.ab L cu k (𝟙 _) N hN f₁ f₂ f₃ x.1 (hH x) fun y hy => by
        have := hw x ⟨y, hy⟩
        rwa [show w x ⟨y, hy⟩ = 1 from hx ⟨y, hy⟩, u1] at this
      rw [hLM] at t
      have s₂ : x.1 ^ 2 = 1 := sq_eq_one_of_translDiff c hc (𝟙 _) x.1 t
      exact (pow_eq_one_iff_of_coprime (Nat.coprime_two_left.2 ho)).1 ⟨s₂, hH x⟩))
  let l₂ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A) := fun a => (l₁ a).1
  have add₂ : ∀ a a', l₂ (a + a') = l₂ a * l₂ a' := fun a a' => congrArg Subtype.val (add₁ a a')
  have tors₂ : ∀ a, l₂ a ^ N = 1 := fun a => hH _
  have w₂ : ∀ a a', UU.CubWeil cu N (l₂ a) (l₂ a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) := fun a a' =>
    (show w (l₁ a) (l₁ a') = _ from w₁ a a') ▸ hw (l₁ a) (l₁ a')

  have mk : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) (β : k →+* k') (z : k'ˣ),
        x ≫ 𝟙 _ = spMap β → (z : k') = β b.ζ →
        (∀ a, (toUnit (Over.mk x) ≫ l₂ a = 1 ↔ ∃ v, a = N • v)) ∧
        (∀ y : Over.mk x ⟶ c.A, y ^ N = 1 → ∃ a, toUnit _ ≫ l₂ a = y) ∧
        ∀ a a', Out.WeilIs c.A c.diag (N : ℕ) (toUnit (Over.mk x) ≫ l₂ a) (toUnit _ ≫ l₂ a')
          (unitOn (z ^ (2 * omegaStd a a'))) := by
    intro k' _ _ x β z hx hzz
    obtain rfl : x = spMap β := (Category.comp_id _).symm.trans hx
    obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hzz
    have hz' : IsPrimitiveRoot (Units.map β.toMonoidHom (b.ζ ^ 2)) N :=
      hz₂.map_of_injective (Units.map_injective β.injective)
    have hk' : ((N : ℕ) : k') ≠ 0 := by rw [← map_natCast β]; exact (map_ne_zero β).2 hN
    have W : ∀ a a', UU.CubWeil cu N (toUnit (Over.mk (spMap β)) ≫ l₂ a) (toUnit _ ≫ l₂ a')
        (unitOn (Units.map β.toMonoidHom (b.ζ ^ 2) ^ omegaStd a a')) := fun a a' => by
      have H := (w₂ a a').comp (toUnit (Over.mk (spMap β)))
      have e : Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom
          (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) = unitOn (Units.map β.toMonoidHom ((b.ζ ^ 2) ^ omegaStd a a')) :=
        Units.ext (congrArg (fun q => q.hom ((b.ζ ^ 2) ^ omegaStd a a').val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
      rw [e, map_zpow] at H
      exact H
    have ker : ∀ a, toUnit (Over.mk (spMap β)) ≫ l₂ a = 1 → ∃ v, a = N • v := fun a ha =>
      SiegelOfPolarised.exists_smul_of_dvd fun a' => by
        have w₁ := W a a'
        rw [ha] at w₁
        have e := SiegelOfPolarised.unitOn_inj
          ((w₁.unique (UU.cubWeil_one_left cu w₁.2.1)).trans (map_one _).symm)
        exact (hz'.zpow_eq_one_iff_dvd _).1 e
    refine ⟨fun a => ⟨ker a, ?_⟩, SiegelOfPolarised.onto_torsion hN₀ _ (fun a b => by rw [add₂, MonObj.comp_mul])
      (fun a => by rw [← MonObj.comp_pow, tors₂, MonObj.comp_one]) ker ?_, fun a a' => ?_⟩
    · rintro ⟨v, rfl⟩
      have pw : ∀ m : ℕ, l₂ (m • v) = l₂ v ^ m := fun m => by
        induction m with
        | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add₂ 0 0).symm.trans (by rw [add_zero]))
        | succ m ih => rw [succ_nsmul, add₂, ih, pow_succ]
      rw [pw, tors₂, MonObj.comp_one]
    · rw [card k' _ _ hk']
      simp [two_mul]
    · have H := toW (W a a')
      rwa [map_pow, ← zpow_ofNat, ← zpow_mul] at H
  refine ⟨{ A := c.A
            ab := c.ab
            P := c.P
            isLB := c.isLB
            rig₁ := c.rig₁
            rig₂ := c.rig₂
            symm := c.symm
            lev := l₂
            lev_add := add₂
            lev_tors := tors₂
            geom := mk },
    𝟙 _, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl c.A) (inferInstanceAs (IsMonHom (𝟙 c.A))),
    ⟨𝟙 _, ⟨by simp, by simp⟩, ?_⟩, fun a => ?_⟩
  · exact (CechPic.cls_eq_iff c.isLB (pull_isLB c.isLB _)).1
      ((CechPic.pull_id _).symm.trans (CechPic.cls_pull c.isLB _ _).symm)
  · simp

end GlobalTheory.SiegLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorPreDataRigidificationInvPsiZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TensData

def cpt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (lim : IsLimit (Fan.mk P'.A pr)) (y : Fin r → D.X) :
    𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P'.A :=
  lim.lift (Fan.mk _ fun i => D.c (y i))

theorem cpt_pr {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (lim : IsLimit (Fan.mk P'.A pr)) (y : Fin r → D.X) (i : Fin r) :
    cpt lim y ≫ pr i = D.c (y i) :=
  lim.fac (Fan.mk _ fun i => D.c (y i)) ⟨i⟩

theorem cpt_add {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk P'.A pr)) (a b : Fin r → D.X) :
    cpt lim (a + b) = padd P'.A (cpt lim a) (cpt lim b) := by
  refine lim.hom_ext fun ⟨i⟩ => ?_
  show cpt lim (a + b) ≫ pr i = padd P'.A (cpt lim a) (cpt lim b) ≫ pr i
  have := hpr i
  rw [cpt_pr, padd, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, cpt_pr, cpt_pr]
  exact D.c_add _ _

theorem cpt_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk P'.A pr)) :
    cpt lim (0 : Fin r → D.X) = η[P'.A] := by
  refine lim.hom_ext fun ⟨i⟩ => ?_
  show cpt lim 0 ≫ pr i = η[P'.A] ≫ pr i
  have := hpr i
  rw [cpt_pr, IsMonHom.one_hom]
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

end GlobalTheory.Mum.TensData
end


open GlobalTheory.Mum.TensData in
theorem GlobalTheory.Mum.TensData.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (D' : DegPre R) (_ : Tens D.toPre D' W), ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1 := by
  intro R _ _ _ hA D r W hW hdet
  haveI : IsNoetherianRing R := hA.1
  obtain ⟨P', pr, hpr, ⟨lim⟩, -, ⟨w, hw⟩⟩ := GlobalTheory.Mum.PowPol.exists_pow_polAV R D.toPre.P W hW hdet
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P'
  obtain ⟨rig, hrig, hrv⟩ := _root_.GlobalTheory.Mum.TensRig.rig_exists R D.toPre W P'.A P'.L P'.isLB pr hpr w hw
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have cub := (hL.cube _ P' ⟨P'.L, rig, P'.isLB, hrig⟩ rfl).1.some
  choose psi hpsi hpv using fun y : Fin r → D.toPre.X =>
    GlobalTheory.T.exists_tensorTrivialisation_powerLattice_points R D.toPre W P'.A P'.L P'.isLB pr w hw (cpt lim y) y (cpt_pr lim y)
  let D' : DegPre R :=
    { P := P'
      rig := rig
      rig_gen := hrig
      cub := cub
      sym := sym
      sym_gen := hsym
      sym_rig := hsr
      X := Fin r → D.toPre.X
      c := cpt lim
      c_add := cpt_add hpr lim
      psi := psi
      psi_gen := hpsi }
  refine ⟨D', ⟨pr, hpr, lim, AddEquiv.refl _, fun y i => cpt_pr lim y i, w, hw, fun y z J J' hJ hJ' => hpv y z J J' hJ hJ'⟩,
    fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hτ : ∀ a b : D.toPre.X, a = 0 → b = 0 → val (D.toPre.tau a b) (𝟙 _) z J = 1 := by
    rintro a b rfl rfl
    have vρ : val D.toPre.rigK (𝟙 _) z J = val D.toPre.rig (jK R) z J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ b : D.toPre.X, b = 0 → val (D.toPre.psi b) (𝟙 _) z J = val (D.toPre.psi 0) (𝟙 _) z J := by
      rintro b rfl; rfl
    have e : val (D.toPre.tau 0 0) (𝟙 _) z J = val (D.toPre.psi (0 + 0)) (𝟙 _) z J * (val (D.toPre.psi 0) (𝟙 _) z J)⁻¹ *
        (val (D.toPre.psi 0) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    rw [e, hp (0 + 0) (by simp), vρ, GlobalTheory.PsiZero.val_psi_zero D.tau_bimult hJ]
    group
  have h1 := hpv 0 z J J' hJ hJ'
  have h2 := hrv z J J' hJ hJ'
  have hprod : (∏ i, ∏ j, val (D.toPre.tau ((0 : Fin r → D.toPre.X) i) ((0 : Fin r → D.toPre.X) j)) (𝟙 _) z J ^ W i j) = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by rw [hτ ((0 : Fin r → D.toPre.X) i) ((0 : Fin r → D.toPre.X) j) rfl rfl, one_zpow]
  rw [hprod, _root_.mul_one] at h1
  show val (psi 0) (𝟙 _) z J' * val (LB.pullGen P'.L _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' = 1
  rw [h1, _root_.mul_comm]
  have hz := cpt_zero hpr lim (D := D.toPre)
  revert h2
  generalize cpt lim 0 = x at hz ⊢
  subst hz
  exact id
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaImm

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

theorem isUnit_resG_of_le {X : Scheme.{0}} {U V : X.Opens} (r : Γ(X, U)) (h : V ≤ X.basicOpen r) :
    IsUnit (resG X (h.trans (X.basicOpen_le r)) r) := by
  have := (X.toRingedSpace.isUnit_res_basicOpen r).map (resG X h)
  exact (congrArg IsUnit (resG_resG (X.basicOpen_le r) h r)).mp this

theorem exists_immersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (S : Finset D.toPre.X) (k₁ : ℕ), ∀ k ≥ k₁, ∃ (N : ℕ) (α : Fin (N + 1) → D.toPre.X) (b : ∀ i, D.toPre.SecB k (α i)) (τ : Fin (N + 1) → SecK D.toPre.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), (∀ i, α i ∈ S ∧ IsTermOf Y (b i) (τ i)) ∧ IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
  intro R _ _ _ hR D Y
  classical
  have : IsNoetherianRing R := hR.1.1
  obtain ⟨-, hqa, -, -, hterm⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := GlobalTheory.Mum.ext_torus R D.toPre Y
  let bs := Module.Free.chooseBasis ℤ D.toPre.X
  choose k₀ hk₀ using fun c => GlobalTheory.Mum.exists_secB_generating R D.toPre (bs c)
  refine ⟨insert 0 (Finset.univ.image bs), max 4 (Finset.univ.sup k₀), fun k hk => ?_⟩
  obtain ⟨m, s, hs⟩ := GlobalTheory.Mum.WeightZero.exists_veryAmpleBy_secB_zero R D.toPre k (le_of_max_le_left hk)
  choose n bb hbb using fun c => hk₀ c k ((Finset.le_sup (Finset.mem_univ c)).trans (le_of_max_le_right hk))
  let J := Fin (m + 1) ⊕ Σ c, Fin (n c)
  let αJ : J → D.toPre.X := Sum.elim (fun _ => 0) (fun p => bs p.1)
  let bJ : ∀ j : J, D.toPre.SecB k (αJ j) := fun j => match j with
    | .inl a => s a
    | .inr p => bb p.1 p.2
  choose τJ hτJ using fun j : J => hterm k (αJ j) (bJ j)
  have hcard : Fintype.card J = (Fintype.card J - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.2 ⟨.inl 0⟩)).symm
  let e : Fin (Fintype.card J - 1 + 1) ≃ J := (Fintype.equivFinOfCardEq hcard).symm
  have ht₀ : ∀ a, IsTermOf Y (s a) (τJ (e (e.symm (.inl a)))) := fun a => by
    rw [e.apply_symm_apply]; exact hτJ (.inl a)
  have htc : ∀ c l, IsTermOf Y (bb c l) (τJ (e (e.symm (.inr ⟨c, l⟩)))) := fun c l => by
    rw [e.apply_symm_apply]; exact hτJ (.inr ⟨c, l⟩)
  obtain ⟨hs₁, hsc⟩ := (veryAmpleBy_iff _ s).1 hs
  have hsi := (isClosedImmersion_toProj_iff _ s hs₁).1 hsc
  have hτ : ⨆ i, nonzeroLocus (τJ (e i)) = ⊤ := top_le_iff.1 fun y _ => by
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs₁.ge (Set.mem_univ (Y.q.left y)))
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (.inl a), ?_⟩
    rw [GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k 0 _ _ (ht₀ a)]
    exact ha
  refine ⟨_, fun i => αJ (e i), fun i => bJ (e i), fun i => τJ (e i), hτ, fun i => ⟨?_, hτJ (e i)⟩, ?_⟩
  · show αJ (e i) ∈ _
    generalize e i = j
    rcases j with a | p
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem bs (Finset.mem_univ p.1))
  refine GlobalTheory.isImmersion_of_forall_affine_surjective_appLE _ _ _ fun y => ?_
  set φ := toProj Y.H.hom (fun i => τJ (e i)) hτ with hφ
  let q := Y.q.left
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs₁.ge (Set.mem_univ (q y)))
  choose l hl using fun c => TopologicalSpace.Opens.mem_iSup.1 ((hbb c).ge (Set.mem_univ (q y)))

  let V₀ := nonzeroLocus (s a)
  have hV₀ : IsAffineOpen V₀ := (hsi a).1
  let O : D.toPre.P.A.left.Opens := V₀ ⊓ Finset.univ.inf fun c => nonzeroLocus (bb c (l c))
  have hyO : q y ∈ O := by
    refine ⟨ha, ?_⟩
    show q y ∈ ((Finset.univ.inf fun c => nonzeroLocus (bb c (l c)) : D.toPre.P.A.left.Opens) : Set _)
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter, Function.comp_apply]
    exact fun c => hl c
  obtain ⟨f, hfO, hyf⟩ := hV₀.exists_basicOpen_le (V := O) ⟨q y, hyO⟩ ha
  let V := D.toPre.P.A.left.basicOpen f
  have hV : IsAffineOpen V := hV₀.basicOpen f
  have hVV₀ : V ≤ V₀ := D.toPre.P.A.left.basicOpen_le f
  have hVc : ∀ c, V ≤ nonzeroLocus (bb c (l c)) := fun c x hx => by
    have h := (hfO hx).2
    change x ∈ ((Finset.univ.inf fun c => nonzeroLocus (bb c (l c)) : D.toPre.P.A.left.Opens) : Set _) at h
    rw [TopologicalSpace.Opens.coe_finset_inf] at h
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter, Function.comp_apply] at h
    exact h c
  let i₀ := e.symm (.inl a)
  let iκ := fun c =>  e.symm (.inr ⟨c, l c⟩)
  have hloc₀ : nonzeroLocus (τJ (e i₀)) = q ⁻¹ᵁ V₀ := GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k 0 _ _ (ht₀ a)
  have hlocc : ∀ c, nonzeroLocus (τJ (e (iκ c))) = q ⁻¹ᵁ nonzeroLocus (bb c (l c)) := fun c =>
    GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k _ _ _ (htc c (l c))
  have hch₀ : φ ⁻¹ᵁ chart R _ i₀ = q ⁻¹ᵁ V₀ := (toProj_preimage_chart _ _ hτ i₀).trans hloc₀

  let base := (baseRingHom (PSpace.str R _) (chart R _ i₀)).hom
  let rat : Fin (m + 1) → Γ(PSpace R _, chart R _ i₀) := fun j => ratio R _ i₀ (e.symm (.inl j))
  have hW₀ : ∀ {W' : Y.H.left.Opens}, W' ≤ q ⁻¹ᵁ V₀ → W' ≤ φ ⁻¹ᵁ chart R _ i₀ := fun h => h.trans hch₀.ge
  have hpoly : ∀ (W' : Y.H.left.Opens) (hq : W' ≤ q ⁻¹ᵁ V₀) (P : MvPolynomial (Fin (m + 1)) R),
      (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom (MvPolynomial.eval₂Hom base rat P) =
      (q.appLE V₀ W' hq).hom (MvPolynomial.eval₂Hom (baseRingHom D.toPre.P.A.hom V₀).hom
        (fun j => secRatio (s a) (s j)) P) := by
    intro W' hq P
    have e1 : (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom.comp (MvPolynomial.eval₂Hom base rat) =
        (q.appLE V₀ W' hq).hom.comp (MvPolynomial.eval₂Hom (baseRingHom D.toPre.P.A.hom V₀).hom
          (fun j => secRatio (s a) (s j))) := by
      rw [MvPolynomial.comp_eval₂Hom, MvPolynomial.comp_eval₂Hom]
      congr 1
      · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, baseRingHom_appLE, baseRingHom_appLE, toProj_str]
        exact congrArg (fun g => (baseRingHom g W').hom) (Over.w Y.q).symm
      · funext j
        show pullRatio φ W' i₀ _ _ = _
        rw [pullRatio_toProj_on]
        exact (GlobalTheory.Mum.secRatio_isTermOf_zero R D.toPre Y k (s a) (s j) _ _ (ht₀ a) (ht₀ j) W' hq _).symm
    exact RingHom.congr_fun e1 P
  let W := q ⁻¹ᵁ V
  have hWV₀ : W ≤ q ⁻¹ᵁ V₀ := q.preimage_mono hVV₀
  obtain ⟨p, hp⟩ := (hsi a).2 f
  let F₀ := MvPolynomial.eval₂Hom base rat p
  let G := F₀ * ∏ c, ratio R _ i₀ (iκ c)
  let U := (PSpace R _).basicOpen G
  have hU : IsAffineOpen U := (isAffineOpen_chart R _ i₀).basicOpen G
  have hUc : U ≤ chart R _ i₀ := (PSpace R _).basicOpen_le G
  have hF : ∀ (W' : Y.H.left.Opens) (hq : W' ≤ q ⁻¹ᵁ V₀),
      (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom F₀ = (q.appLE V₀ W' hq).hom f := fun W' hq => by
    rw [hpoly W' hq p, hp]
  have hUW : φ ⁻¹ᵁ U ≤ W := by
    intro x hx
    have hx₀ : x ∈ q ⁻¹ᵁ V₀ := hch₀.le (φ.preimage_mono hUc hx)
    have h1 : x ∈ Y.H.left.basicOpen ((φ.appLE (chart R _ i₀) (q ⁻¹ᵁ V₀) (hW₀ le_rfl)).hom G) := by
      rw [Scheme.basicOpen_appLE]; exact ⟨hx₀, hx⟩
    rw [map_mul, Scheme.basicOpen_mul, hF _ le_rfl, Scheme.basicOpen_appLE] at h1
    exact h1.1.2
  have hWU : W ≤ φ ⁻¹ᵁ U := by
    intro x hx
    have hx₀ : x ∈ q ⁻¹ᵁ V₀ := hWV₀ hx
    have h1 : x ∈ Y.H.left.basicOpen ((φ.appLE (chart R _ i₀) (q ⁻¹ᵁ V₀) (hW₀ le_rfl)).hom G) := by
      rw [map_mul, Scheme.basicOpen_mul, hF _ le_rfl, Scheme.basicOpen_appLE, map_prod]
      refine ⟨⟨hx₀, hx⟩, ?_⟩
      refine Finset.prod_induction _ (fun r => x ∈ Y.H.left.basicOpen r)
        (fun r r' h h' => by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩)
        (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial) fun c _ => ?_
      show x ∈ Y.H.left.basicOpen (pullRatio φ _ i₀ _ (iκ c))
      rw [basicOpen_pullRatio, toProj_preimage_chart]
      refine ⟨hx₀, ?_⟩
      show x ∈ nonzeroLocus (τJ (e (iκ c)))
      rw [hlocc c]
      exact hVc c hx
    rw [Scheme.basicOpen_appLE] at h1
    exact h1.2
  haveI := hqa
  refine ⟨U, W, hWU, hU, hWU hyf, hUW, hV.preimage q, ?_⟩

  let S := (φ.appLE U W hWU).hom.range
  have hS_chart : ∀ r : Γ(PSpace R _, chart R _ i₀), (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom r ∈ S :=
    fun r => ⟨resG _ hUc r, appLE_resG φ hUc hWU r⟩
  have hS_unit : ∀ r : Γ(PSpace R _, chart R _ i₀), U ≤ (PSpace R _).basicOpen r →
      ∃ w ∈ S, (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom r * w = 1 := by
    intro r hr
    obtain ⟨v, hv⟩ := isUnit_resG_of_le r hr
    refine ⟨(φ.appLE U W hWU).hom ↑v⁻¹, ⟨_, rfl⟩, ?_⟩
    rw [← appLE_resG φ hUc hWU r, ← map_mul]
    have : resG _ hUc r = ↑v := hv.symm
    rw [this, Units.mul_inv, map_one]
  have hUF : U ≤ (PSpace R _).basicOpen F₀ := fun x hx => by
    have := hx
    change x ∈ (PSpace R _).basicOpen G at this
    rw [Scheme.basicOpen_mul] at this
    exact this.1
  have hUr : ∀ c, U ≤ (PSpace R _).basicOpen (ratio R _ i₀ (iκ c)) := fun c x hx => by
    have := hx
    change x ∈ (PSpace R _).basicOpen G at this
    rw [Scheme.basicOpen_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Scheme.basicOpen_mul] at this
    exact this.2.1
  have hS_q : ∀ x : Γ(D.toPre.P.A.left, V₀), (q.appLE V₀ W hWV₀).hom x ∈ S := fun x => by
    obtain ⟨P, rfl⟩ := (hsi a).2 x
    rw [← hpoly W hWV₀ P]
    exact hS_chart _
  have hWτ₀ : W ≤ nonzeroLocus (τJ (e i₀)) := hWV₀.trans hloc₀.ge
  have hWb : ∀ c, W ≤ Y.H.left.basicOpen (secRatio (τJ (e i₀)) (τJ (e (iκ c)))) := fun c x hx => by
    rw [basicOpen_secRatio]
    refine ⟨hWτ₀ hx, ?_⟩
    rw [hlocc c]
    exact hVc c hx
  let u : _ → Γ(Y.H.left, W)ˣ := fun c => (isUnit_resG_of_le _ (hWb c)).unit
  have hu : ∀ c, (u c).val = resG _ hWτ₀ (secRatio (τJ (e i₀)) (τJ (e (iκ c)))) := fun c =>
    (isUnit_resG_of_le _ (hWb c)).unit_spec
  have hupr : ∀ c, (u c).val = (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom (ratio R _ i₀ (iκ c)) := fun c => by
    rw [hu c]
    exact (pullRatio_toProj_on _ _ hτ i₀ (iκ c) (hW₀ hWV₀)).symm
  have hSt : S = ⊤ := by
    refine GlobalTheory.Mum.subring_eq_top_of_weight_units R D.toPre Y i hi₁ hi₂ bs V hV u (fun c => ?_) S (fun c => ?_) (fun c => ?_)
    · rw [hu c]
      exact (GlobalTheory.Mum.TermWeight.isWt_secRatio R D.toPre Y i hi₃ hi₂ k (bs c) (s a) (bb c (l c)) _ _ (ht₀ a) (htc c (l c))).res hWτ₀
    · have := hV₀.isLocalization_basicOpen f
      obtain ⟨⟨a', _, n', rfl⟩, ha'⟩ := IsLocalization.surj (Submonoid.powers f) c
      have ha'' : c * resG _ hVV₀ (f ^ n') = resG _ hVV₀ a' := ha'
      have happ : ∀ x : Γ(D.toPre.P.A.left, V₀), (q.app V).hom (resG _ hVV₀ x) = (q.appLE V₀ W hWV₀).hom x := fun x => by
        rw [Scheme.Hom.app_eq_appLE]
        exact appLE_resG q hVV₀ le_rfl x
      obtain ⟨w, hw, hfw⟩ := hS_unit F₀ hUF
      rw [hF W hWV₀] at hfw
      have key := congrArg (q.app V).hom ha''
      rw [map_mul, happ, happ, map_pow] at key
      have : (q.app V).hom c = (q.appLE V₀ W hWV₀).hom a' * w ^ n' := by
        rw [← key, _root_.mul_assoc, ← mul_pow, hfw, one_pow, _root_.mul_one]
      rw [this]
      exact S.mul_mem (hS_q a') (S.pow_mem hw n')
    · refine ⟨(hupr c).symm ▸ hS_chart _, ?_⟩
      obtain ⟨w, hw, hrw⟩ := hS_unit _ (hUr c)
      rw [← hupr c] at hrw
      rw [Units.mul_eq_one_iff_inv_eq.1 hrw]
      exact hw
  intro x
  have hx : x ∈ S := hSt ▸ Subring.mem_top x
  exact hx

end GlobalTheory.Mum.ThetaImm
end
end

