module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Algebraise
variable {X Y : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (rs_rs h₁ h₂ u.val)

theorem pw_pw (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem pw_pull (H : LB X) (f : Y ⟶ X) (a : ℤ) :
    (AbLaw.pw H a).pull f = AbLaw.pw (H.pull f) a := by
  have : ((AbLaw.pw H a).pull f).g = (AbLaw.pw (H.pull f) a).g := by
    funext j j'
    change (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k) ^ a))) ^ (1 : ℤ)) =
      (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k)))) ^ (1 : ℤ)) ^ a
    simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact congrArg (fun g => (⟨(H.pull f).ι, (H.pull f).U, g⟩ : LB Y)) this

theorem lbIso_pw {A B : LB X} (h : LBIso A B) (a : ℤ) : LBIso (AbLaw.pw A a) (AbLaw.pw B a) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => (w.s p) ^ a⟩, fun p q => ?_⟩
  have key : ∀ {G : Type} [CommGroup G] {x y z u : G}, x = y * z⁻¹ * u →
      x ^ a = y ^ a * (z ^ a)⁻¹ * u ^ a := by
    rintro G _ x y z u rfl
    rw [mul_zpow, mul_zpow, inv_zpow]
  change res _ (w.s p ^ a) = (res _ (B.g p.1 q.1 ^ a) * (res _ (A.g p.2 q.2 ^ a))⁻¹) * res _ (w.s q ^ a)
  rw [map_zpow, map_zpow, map_zpow, map_zpow]
  exact key (hw p q)

theorem cocycle_on {H : LB X} (hH : H.IsLB) (i j k : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hj : W ≤ H.U j) (hk : W ≤ H.U k) :
    res (le_inf hi hj) (H.g i j) * res (le_inf hj hk) (H.g j k) = res (le_inf hi hk) (H.g i k) := by
  have h := congrArg (res (le_inf (le_inf hi hj) hk : W ≤ H.U i ⊓ H.U j ⊓ H.U k)) (hH.cocycle i j k)
  simpa only [map_mul, res_res] using h

theorem rel_on {H : LB X} (hH : H.IsLB) (i k i' k' : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hk : W ≤ H.U k) (hi' : W ≤ H.U i') (hk' : W ≤ H.U k') :
    res (le_inf hi hk) (H.g i k) = res (le_inf hi hi') (H.g i i') * (res (le_inf hk hk') (H.g k k'))⁻¹ *
      res (le_inf hi' hk') (H.g i' k') := by
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq, cocycle_on hH i k k' hi hk hk',
    cocycle_on hH i i' k' hi hi' hk']

theorem lbIso_tw {H : LB X} (hH : H.IsLB) (t : ℤ) : LBIso (AbLaw.pw H (t + 1)) (tw H H t) := by
  refine ⟨⟨fun p => res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.1 ⊓ H.U p.2) (H.g p.1.1 p.2) *
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.2 ⊓ H.U p.2) (H.g p.1.2 p.2) ^ t⟩, ?_⟩
  rintro ⟨⟨i, j : H.ι⟩, k : H.ι⟩ ⟨⟨i', j' : H.ι⟩, k' : H.ι⟩
  let W : X.Opens := H.U i ⊓ H.U j ⊓ H.U k ⊓ (H.U i' ⊓ H.U j' ⊓ H.U k')
  have hi : W ≤ H.U i := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hj : W ≤ H.U j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hk : W ≤ H.U k := inf_le_left.trans inf_le_right
  have hi' : W ≤ H.U i' := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hj' : W ≤ H.U j' := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have hk' : W ≤ H.U k' := inf_le_right.trans inf_le_right
  change res (inf_le_left : W ≤ H.U i ⊓ H.U j ⊓ H.U k) (res _ (H.g i k) * res _ (H.g j k) ^ t) =
    (res (V := W) (U := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _
        (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g i i') *
          (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g j j' ^ (-t)))⁻¹) *
      (res (V := W) _ (H.g k k' ^ (t + 1)))⁻¹) *
    res (inf_le_right : W ≤ H.U i' ⊓ H.U j' ⊓ H.U k') (res _ (H.g i' k') * res _ (H.g j' k') ^ t)
  simp only [map_mul, map_inv, map_zpow, res_res]
  erw [res_res, res_res]
  rw [rel_on hH i k i' k' hi hk hi' hk', rel_on hH j k j' k' hj hk hj' hk']
  simp only [zpow_neg, inv_inv, mul_zpow, inv_zpow, zpow_add_one, mul_inv]
  ac_rfl

theorem exists_veryAmple_h1Zero (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) (L : LB B.left) (hL : L.IsLB) (h : RelAmple B L) :
    ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes (AbLaw.pw L d) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy B.hom (AbLaw.pw L d) s := by
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  have hH := isLB_pw hL (d₀ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 R B.left B.hom _ n₀ s₀ hH hs₀ _ hH
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH hH _).cover (isLB_pw hH _) w hw h1
  have h3 := veryAmpleBy_pw R B.left B.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

theorem algebraisation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (M H : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left) (n d : ℕ) (s : Fin (n + 1) → LB.Sec H), M.IsLB ∧ H.IsLB ∧ Flat B.hom ∧ VeryAmpleBy B.hom H s ∧ 1 ≤ d ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) ∧ LBIso (pw (N e) d) (H.pull (b e)) := by
  intro V _ _ _ _ Y β hβ hY N v hN hA
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := exists_veryAmple_h1Zero _ (Y 0) (N 0) (hN 0).1 hA
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [pw_pull]
    exact lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' h0 (s₀ j)
  have hva : VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext hs0
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, hw, -⟩ := GlobalTheory.Unif.exists_projective_of_formal_embedding V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => hs j e) hva
  have hP : IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have := isProper_of_isProjBy V B.left B.hom hP
  have hF : Flat B.hom := GlobalTheory.FlatThickenings.flat_of_flat_thickenings V B Y b hb hY
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hP hF hb hbβ N v hN
  exact ⟨B, M, H, b, n, d, s', hM, hH, hF, hB, hd, hb, hbβ, fun e => ⟨hNM e, w e, (hw e).1⟩⟩

end GlobalTheory.Algebraise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsWeightBundleTorusQuotientTowerAlgebraisati
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] {s : HidaSetting V A G}

theorem exists_levels (t : Tower s) (χ : s.X) : ∃ (N : ∀ e, LB (t.l e).Q.B.left)
    (u : ∀ e, LB.Gen ((N e).pull (t.l e).Q.q.left)),
    ∀ e, (N e).IsLB ∧ (t.l e).Q.GenWt (N e) (u e) χ ∧ Triv (abelian₂ (t.l e).Q.B (N e)) := by
  have H : ∀ e, ∃ (N : LB (t.l e).Q.B.left) (u : LB.Gen (N.pull (t.l e).Q.q.left)),
      N.IsLB ∧ (t.l e).Q.GenWt N u χ ∧ Triv (abelian₂ (t.l e).Q.B N) := by
    intro e
    haveI := isLocalRing_quotient_pow V e
    obtain ⟨N, u, hN, hu, g, hg⟩ := GlobalTheory.exists_weight_bundle _ _ _ (t.l e).Q χ
    exact ⟨N, u, hN, hu, g, hg⟩
  choose N u h using H
  exact ⟨N, u, h⟩

theorem lbIso_succ (t : Tower s) {χ : s.X} (e : ℕ) {N : LB (t.l e).Q.B.left} {N' : LB (t.l (e + 1)).Q.B.left}
    {u : LB.Gen (N.pull (t.l e).Q.q.left)} {u' : LB.Gen (N'.pull (t.l (e + 1)).Q.q.left)} (hN : N.IsLB)
    (hN' : N'.IsLB) (hu : (t.l e).Q.GenWt N u χ) (hu' : (t.l (e + 1)).Q.GenWt N' u' χ) :
    LBIso N (N'.pull (t.β e)) := by
  obtain ⟨v, hv⟩ := exists_genWt_pull (t.l (e + 1)).Q (t.l e).Q
    (isGrpPullback_thickMap (IsLocalRing.maximalIdeal V) G e) (t.tor e) (t.β_q e) hu'
  exact lbIso_of_genWt _ _ _ (t.l e).Q N (N'.pull (t.β e)) u v χ hN (pull_isLB hN' _) hu hv

theorem isPullback_of_isCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B']
    [GrpObj B] [IsCommMonObj B] {M' : CP B'} {M : CP B} {f : S' ⟶ S} {β : B'.left ⟶ B.left}
    (h : IsCPPullback M' M f β) : IsPullback β B'.hom B.hom f := by
  obtain ⟨hg, -⟩ := h
  exact hg.1

theorem exists_alg_of_lbIso {V : Type} [CommRing V] [IsDomain V] [i : IsLocalRing V] (hV : CDVR V)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e))
    (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) (hp : IsProjBy B.hom) (hf : Flat B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hc : ∀ e, β e ≫ b (e + 1) = b e) (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) :
    ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hV.2.1
  choose w hw using h
  exact GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hp hf hb hc N w fun e => ⟨hN e, hw e⟩

theorem isPullback_β (t : Tower s) (e : ℕ) : IsPullback (t.β e) (t.l e).Q.B.hom (t.l (e + 1)).Q.B.hom
    (thickTrans V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (t.β_pb e)

theorem isPullback_b {t : Tower s} (a : t.Alg) (e : ℕ) : IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom
    (thick V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (a.b_pb e)

theorem flat_alg {t : Tower s} (a : t.Alg) : Flat a.B.hom := by
  haveI := a.isAb.smooth
  infer_instance

theorem exists_alg {t : Tower s} (a : t.Alg) (N : ∀ e, LB (t.l e).Q.B.left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e))) :
    ∃ O : LB a.B.left, O.IsLB ∧ ∀ e, LBIso (N e) (O.pull (a.b e)) := by
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  exact exists_alg_of_lbIso s.cdvr (fun e => (t.l e).Q.B) t.β (isPullback_β t) a.B a.b hp (flat_alg a)
    (isPullback_b a) a.b_β N hN h

theorem triv_lam_alg (hG : GlobalFnsSt) {t : Tower s} (a : t.Alg) {N : ∀ e, LB (t.l e).Q.B.left}
    (hN : ∀ e, (N e).IsLB) {O : LB a.B.left} (hO : O.IsLB) (hi : ∀ e, LBIso (N e) (O.pull (a.b e)))
    (h : ∀ e, Triv (abelian₂ (t.l e).Q.B (N e))) : Triv (abelian₂ a.B O) := by
  haveI : IsDiscreteValuationRing V := s.cdvr.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := s.cdvr.2.1
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  refine triv_lam_of_levels hG a.isAb hp hO fun e => ?_
  obtain ⟨hb, -⟩ := a.b_pb e
  exact triv_lam_pull hb hO (hN e) (hi e) (h e) (fstG (IsLocalRing.maximalIdeal V) e (a.B ⊗ a.B))

theorem exists_weight_bundle_alg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  intro hL V _ _ _ A G _ _ s t a χ
  obtain ⟨N, u, h⟩ := exists_levels t χ
  have hiso : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e)) := fun e =>
    lbIso_succ t e (h e).1 (h (e + 1)).1 (h e).2.1 (h (e + 1)).2.1
  obtain ⟨O, hO, hi⟩ := exists_alg a N (fun e => (h e).1) hiso
  have hT := triv_lam_alg hL.globalFns a (fun e => (h e).1) hO hi (fun e => (h e).2.2)
  refine ⟨O, hO, hT, fun e => ?_⟩
  obtain ⟨v, hv⟩ := exists_genWt_of_lbIso (t.l e).Q (h e).1 (pull_isLB hO _) (hi e) (h e).2.1
  exact exists_gen_comp (t.l e).Q (a.b e) hv

end GlobalTheory.WtTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivTorusQuotientTowerAlgebraisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.Principal

theorem finite_points {S : Scheme.{0}} (H : Over S) [IsFinite H.hom] {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) : Finite (Over.mk t ⟶ H) := by
  have hfin := ((pullback.snd H.hom t).finite_preimage_singleton (IsLocalRing.closedPoint K)).to_subtype
  let σ : (Over.mk t ⟶ H) → (Spec (CommRingCat.of K) ⟶ pullback H.hom t) := fun x =>
    pullback.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp _).symm)
  have h₁ : ∀ x, σ x ≫ pullback.fst H.hom t = x.left := fun x => pullback.lift_fst _ _ _
  have h₂ : ∀ x, σ x ≫ pullback.snd H.hom t = 𝟙 _ := fun x => pullback.lift_snd _ _ _
  refine Finite.of_injective (fun x => (⟨σ x (IsLocalRing.closedPoint K),
    Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _⟩ :
      (pullback.snd H.hom t) ⁻¹' {IsLocalRing.closedPoint K})) fun a b hab => ?_
  have e : σ a = σ b :=
    ext_of_apply_closedPoint_eq (K := K) (pullback.snd H.hom t) (h₂ a) (h₂ b) (congrArg Subtype.val hab)
  exact Over.OverMorphism.ext ((h₁ a).symm.trans (e ▸ h₁ b))

theorem exists_pow_eq_one (hG : GlobalFnsSt) {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {L : LB B.left} (hLB : L.IsLB) (hL : RelAmple B L)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ B) (hx : InK B L x) : ∃ N : ℕ, 1 ≤ N ∧ x ^ N = 1 := by
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG R B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ x : Over.mk t ⟶ B, InK B L x ↔ ∃ y : Over.mk t ⟶ H, y ≫ j = x :=
    fun x => (hK _ rfl _ x).trans (hH _ x)
  have := finite_points H t
  have : Finite (kSubgroup B hLB (Over.mk t)) :=
    Finite.of_surjective (fun y : Over.mk t ⟶ H => (⟨y ≫ j, (hrep _).2 ⟨y, rfl⟩⟩ : kSubgroup B hLB (Over.mk t)))
      fun z => ((hrep z.1).1 z.2).imp fun _ h => Subtype.ext h
  exact ⟨Nat.card (kSubgroup B hLB (Over.mk t)), Nat.card_pos,
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : kSubgroup B hLB (Over.mk t))))⟩

theorem exists_gen_of_inK {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hLB : L.IsLB)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ B) (hx : InK B L x) :
    ∃ u : LB.Gen (translDiff B L x), u.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  refine GlobalTheory.TwistTranslate.gen_of_pull_top hLB _ (fun z => ?_) c hc
  have e : ∀ p q : Spec (CommRingCat.of K), p = q := fun p q => Subsingleton.elim p q
  change (fst (Over.mk t) B).left z ∈ V
  rw [e ((fst (Over.mk t) B).left z) (IsLocalRing.closedPoint K)]
  exact hpV

theorem kTriv_alg : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L := by
  intro hc laws V _ _ _ A G _ _ s t a
  have hdvr : IsDiscreteValuationRing V := s.cdvr.1
  have hchar : CharZero V := s.cdvr.2.2
  refine GlobalTheory.KTrivGeneric.kTriv_of_generic laws.globalFns V a.B a.isAb a.M.L a.M.c a.ample fun x hx => ?_
  obtain ⟨N, hN, hxN⟩ := exists_pow_eq_one laws.globalFns a.isAb a.M.L.isLB a.ample _ x hx
  exact GlobalTheory.UU.cubWeil_nondegenerate_generic hc laws V A G s t a (AlgebraicClosure (FractionRing V)) N hN x hxN fun y hy =>
    GlobalTheory.UU.KerPair.cubWeil_of_gen laws.globalFns _ a.B a.isAb a.M.L a.M.c N _ x y hxN hy
      (exists_gen_of_inK a.M.L.isLB _ x hx)

end GlobalTheory.UU.Principal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelOfAmpleBundleFiniteFlatOfLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelFlat

theorem kernelFiniteFlat : Laws → GlobalTheory.Published.KernelFiniteFlatSt := by
  intro hLaw V _ _ A _ hA L hL ha
  obtain ⟨H, j, hj, hfin, hH⟩ := _root_.GlobalTheory.KernelRep.exists_finite_closed_kernel hLaw.globalFns V A hA L hL ha
  refine ⟨H, j, hj, hfin, _root_.GlobalTheory.flat_of_isFinite_of_flat_localization_maximal V H hfin fun m _ => ?_, hH⟩
  let f := spMap (algebraMap V (Localization.AtPrime m))
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have : IsCommMonObj ((Over.pullback f).obj A) := hA'.comm
  have hP : IsProjBy ((Over.pullback f).obj A).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha (Localization.AtPrime m) f
      _ (pullback.fst A.hom f) (pullback.snd A.hom f) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom f)).IsLB := LB.isLB_pull hL _
  have hj' : IsClosedImmersion ((Over.pullback f).map j).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f j hj
  have hfin' : IsFinite ((Over.pullback f).obj H).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback H.hom f) hfin
  exact _root_.GlobalTheory.StabFlatLocal.flat_of_isFinite hLaw.globalFns (Localization.AtPrime m) ((Over.pullback f).obj A) hA' hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hLaw _ _ hA' hP _ hL') ((Over.pullback f).obj H)
    ((Over.pullback f).map j) hj' (_root_.GlobalTheory.memKL_baseChange_rep _ _ f A L hL H j hH) hfin'

end GlobalTheory.KernelFlat
end

