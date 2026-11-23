module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsWitnessesBaseChangeAlongTower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep.TermsTrans

open GlobalTheory.TermsMove GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull

theorem tfk_hom (V : Type) [CommRing V] [IsDomain V] : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

theorem gw_stalk {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (r : Z ⟶ Y)
    (g : Y ⟶ X') (z : Z) {j : L.ι} {k : L'.ι} (hj : F (g (r z)) ∈ L.U j) (hk : g (r z) ∈ L'.U k) :
    (Geo.Tor.gw w (r ≫ g) z j k).val = (r.stalkMap z).hom (Geo.Tor.gw w g (r z) j k).val := by
  have hm : g (r z) ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  exact (gs_unit (r ≫ g) z _ hm _).symm.trans ((LiftTest.gs_comp r g z _ hm _).trans
    (congrArg _ (gs_unit g (r z) _ hm _)))

theorem exists_theta {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V]
    [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V}
    {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A))
    (fr : ∀ a, FrAt (x a)) (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∃ th : SecA 𝔪.A (FractionRing V) 1, ∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := by
  have gp := 𝔪.cart
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [tfk_hom]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨th, fun a => ?_⟩
  have H : GlobalTheory.ThetaPtMove.GenThrough 𝔪.wl _ _ _ (fr a) (X₁.ρ.fr a)
      (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) := by
    intro Z r z J J' hJ hJ'
    have e := congrArg (fun u => (r.stalkMap z).hom (Units.val u))
      (hfr a (r z) _ _ (LevelExpansion.good_comp r hJ) (LevelExpansion.good_comp r hJ'))
    rw [Fin.prod_univ_one, zpow_one]
    refine Units.ext ((LevelExpansion.val_comp _ r _ hJ).trans (e.symm.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ?_ ?_))))
    · refine (gw_stalk 𝔪.wl r (x a).left z (hJ (r ≫ (x a).left ≫ 𝔪.φ)) (hJ' (r ≫ (x a).left))).symm.trans ?_
      rw [← Category.assoc]
      rfl
    · exact (LevelExpansion.val_comp _ r (𝟙 _) hJ').symm.trans (by rw [Category.comp_id])
  have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
    (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) H (s₀ := X₁.ρ.th₁) (s := th) hth
    (X₁.ρ.th_val a)
  intro z J hJ
  have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
  rw [Category.id_comp] at e
  refine e.trans ?_
  rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
  congr 1
  exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
    ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

theorem exists_moved {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    [Algebra (FractionRing R) (FractionRing R')] {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {Φ : A'.A.left ⟶ A.A.left} {v : LB.Iso A'.L (A.L.pull Φ)} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} (hI : I.map φ ≤ I') (hbc : IsMonHom bc.hom)
    (hU : IsPullUnif φ hD bc U U') (hF : Compat φ (FractionRing R'))
    (gΦ : IsPullback Φ A'.A.hom A.A.hom (spMap (algebraMap (FractionRing R) (FractionRing R')))) (hv : v.IsGen)
    (hΦ : U'.gen.hom.left ≫ Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {th : SecA A (FractionRing R) 1} {s : Fam D.toPre (FractionRing R) 1}
    (hE : U.ExpandsF (FractionRing R) 1 w₀ th s) :
    ∃ (w₀' : W0 U'.toUnifPre) (th' : SecA A' (FractionRing R') 1) (s' : Fam D'.toPre (FractionRing R') 1),
      w₀'.IsGen ∧ U'.ExpandsF (FractionRing R') 1 w₀' th' s' ∧
      (∀ (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R') (FractionRing R') ⟶ A'.A)
        (fr' : FrAt x') (ρ : (FractionRing R')ˣ) (c : FractionRing R),
        x'.left ≫ Φ = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ x.left →
        FrPull v (algebraMap _ _) x' fr' x fr ρ → ValAt th x fr c →
        ValAt th' x' fr' (algebraMap (FractionRing R) (FractionRing R') c * (ρ⁻¹).val)) ∧
      ∀ (g : GtPtF D.toPre (FractionRing R)) (w : GlobalTheory.UT.Frm D.toPre (FractionRing R) 1 g.b) (ρ : (FractionRing R')ˣ),
        w.IsGen → ∃ (g' : GtPtF D'.toPre (FractionRing R')) (w' : GlobalTheory.UT.Frm D'.toPre (FractionRing R') 1 g'.b), w'.IsGen ∧
        (∀ n, (∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) → ∃ o, GtPtF.IsNsmul n g' o ∧ o.IsZero) ∧
        (∀ α, coef s' g' w' α * ρ = algebraMap (FractionRing R) (FractionRing R') (coef s g w (hD.xe α))) ∧
        ∀ (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R') (FractionRing R') ⟶ A'.A)
          (fr' : FrAt x'), fr.IsGen → x'.left ≫ Φ = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ x.left →
          FrPull v (algebraMap _ _) x' fr' x fr ρ → LiesOver U.toUnifPre (FractionRing R) w₀ g w x fr →
          LiesOver U'.toUnifPre (FractionRing R') w₀' g' w' x' fr' := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  have hg₂ : jFK (R := R') (FractionRing R') ≫ spMap (algebraMap (FractionRing R) (FractionRing R')) =
      jFK (R := R) (FractionRing R') := by
    rw [show jFK (R := R') (FractionRing R') = 𝟙 _ from tfk_hom R']
    exact Category.id_comp _
  obtain ⟨w₀', hw₀', Ω, h₁, h₂, H⟩ := exists_expand hG hbc hU hF hg₂ gΦ hv hΦ hw₀ hκ
  obtain ⟨th', s', E', up, fup⟩ := (H 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing R') U.toUnifPre hG hE)
  have frup : ∀ {x : TFK (R := R) (FractionRing R) ⟶ A.A} {fr : FrAt x} {x' : TFK (R := R') (FractionRing R') ⟶ A'.A}
      {fr' : FrAt x'} {ρ : (FractionRing R')ˣ}, FrPull v (algebraMap _ _) x' fr' x fr ρ →
      FrUp v fr' (frExt (FractionRing R') fr) ρ := fun {x fr x' fr' ρ} h z J J' hJ hJ' => by
    refine (h z J J' hJ hJ').trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))
    exact ((val_frExt fr (𝟙 _) hJ).trans (by rw [Category.id_comp])).symm
  refine ⟨w₀', th', s', hw₀', E', fun x fr x' fr' ρ c hx hp hc => ?_, fun g w ρ hw => ?_⟩
  · have := valAt_pull h₁ h₂ up (x := fieldMap (R := R) (FractionRing R) (FractionRing R') ≫ x) hx (frup hp)
      (valAt_ext hc)
    rwa [pow_one] at this
  obtain ⟨g₁, w₁, hw₁, t₁, c₁, l₁⟩ := exists_ext (F := FractionRing R') hG U hw₀ g hw
  obtain ⟨g', w', hw', t₂, c₂, l₂⟩ := exists_point hG hI hF hκ h₁ h₂ (fun k hk => (H k hk).2) g₁ hw₁ ρ
  refine ⟨g', w', hw', fun n h => t₂ n (t₁ n h), fun α => (c₂ _ _ fup α).trans (c₁ s _),
    fun x fr x' fr' gen hx hp hl => ?_⟩
  have a := l₁ x fr gen hl
  have b : (frExt (FractionRing R') fr).IsGen := pullGen_isGen _ _ _ _ gen _
  exact l₂ x' fr' (fieldMap (R := R) (FractionRing R) (FractionRing R') ≫ x) (frExt (FractionRing R') fr) b hx (frup hp) a

theorem terms_witnesses_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro I X₁ act 𝔗 z₁ z₂ _ x₀ hdiv V _ _ _ ev X _ t δ 𝔪 C lab x fr th w₀ s g' w hx hfr hth hw₀ hE hc V' _ _ _ io f hf hinj hfin
    ev₂ 𝔪₂ ψ hD bc _ hy gψ wψ hwψ hφ hbc hU hxe hgen x₂ fr₂ hx₂ hfr₂ ρ hρ
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := by
    have := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
    exact Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit io v hv
  obtain ⟨w₀₂, th', s', hw₀₂, E', hval, hpt⟩ := exists_moved (v := wψ) hI hbc hU hf gψ.1 hwψ hgen hw₀ hE
  have hxx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = spMap f ≫ (x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · have e : spMap 𝔪₂.yK ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK :=
        (Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔪₂.yK)).symm.trans
          ((congrArg spMap hy).trans (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom f)))
      rw [Category.assoc, ← hφ, ← Category.assoc, hx₂, Category.assoc, Category.assoc, hx]
      exact (congrArg (_ ≫ ·) (𝔗.lam_pt b)).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans
        (Category.assoc _ _ _)))
    · rw [Category.assoc, gψ.1.w, ← Category.assoc, Over.w (x₂ (𝔗.lam b)), Category.assoc, Over.w (x b), tfk_hom, tfk_hom]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hv' := fun b => hval _ _ _ _ (ρ b) _ (hxx b) (hρ b) (hth b)
  have hne : (show AbSec 𝔪₂.A (FractionRing V') 1 from th') ≠ 0 := fun h => by
    have h₀ := hv' x₀
    rw [show th' = _ from h] at h₀
    exact mul_ne_zero ((map_ne_zero_iff f f.injective).2
      (GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv)) (Units.ne_zero _)
      (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨th₂, hth₂⟩ := exists_theta 𝔪₂ x₂ fr₂ hx₂ fun a => (hfr₂ a).2
  obtain ⟨K, hK⟩ := exists_eq_smul hne th₂
  choose g₂ w₂ hw₂ ht₂ hc₂ hl₂ using fun c => hpt (g' c) (w c) (ρ (lab c)) (hc c).2.1
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') (k := 1) le_rfl w₀₂ hw₀₂
  refine ⟨th₂, w₀₂, K • s', g₂, w₂, K, hth₂, hw₀₂, (he _ _).2 ?_, fun c => ⟨?_, hw₂ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e hK).trans ((map_smul e K _).trans (congrArg (K • ·) ((he _ _).1 E')))
  · letI := @TorusExt.gtGroup
    obtain ⟨o, o₁, o₂⟩ := ht₂ c _ (hc c).1
    rw [TorusExt.isNsmul_iff_eq] at o₁
    rw [TorusExt.isZero_iff_eq] at o₂
    refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [𝔗.lev, mul_nsmul, ← o₁, o₂, nsmul_zero]
  · exact hl₂ c _ _ _ _ (hfr _).1 (hxx _) (hρ _) (hc c).2.2
  · rw [coef_smul (hw₂ c), _root_.mul_assoc, hc₂, hxe]
    rfl
  · have a := valAt_lin (hv' b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at a
    rw [valAt_unique (hth₂ _) a, _root_.mul_assoc, Units.inv_mul_cancel_right]
    rfl

end GlobalTheory.GSep.TermsTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

theorem commGroup_fourfold_cancellation {G : Type*} [CommGroup G] (a1 a2 a3 a4 b1 b2 b3 b4 U V : G) :
    a1 * a2⁻¹ * a3⁻¹ * a4 * V = ((b1⁻¹ * (U * a1)) * (b2⁻¹ * (U * a2))⁻¹ * (b3⁻¹ * (U * a3))⁻¹ * (b4⁻¹ * (U * a4))) *
      (b1 * b2⁻¹ * b3⁻¹ * b4 * V) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_const_of_fromBase : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), GlobalTheory.TautRigid.AbConst Q ρ B' π₁ π₂ w c' → ∀ (y z : Q.X) (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L zz J → val (τ₀ y z) (spMap ρ) zz J = GlobalTheory.TautRigid.lamC Q w c' y z zz J * val (τ₀ y z) (spMap (GlobalTheory.RigChart.constHom ρ)) zz J := by
  intro R _ _ Q τ₀ W₀ _ ιb hFB k _ ρ hρ B' iG π₁ π₂ w c' hA y z zz J hJ
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hA
  obtain ⟨B₀, iB₀, M₀, c₀, τ₁, β, wF, hB₀, hM₀, hβ, hwF, hc₀, hτ₁, hpt⟩ := GlobalTheory.T.fromBase_identity_along_morphism Q τ₀ ιb hFB
  have hπ : π₁ ≫ β = π₂ ≫ β := _root_.GlobalTheory.RigHom.comp_eq_of_const Q ιb B₀ β hβ k ρ hρ B' π₁ π₂ h₁ h₂ h₃
  have hB'ab : IsAbelianScheme B' := _root_.GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback π₁ h₁ Q.P.isAb
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.PullAutConst.exists_unit (DualNumber k) B' hB'ab Q.P.L M₀ β wF π₁ π₂ w Q.P.isLB hM₀ hwF h₄ hπ
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt hM₀ zz
  have e1 := hpt _ (spMap ρ) y z zz J J₀ hJ hJ₀
  have e2 := hpt _ (spMap (GlobalTheory.RigChart.constHom ρ)) y z zz J J₀ hJ hJ₀
  have hιb : spMap ρ ≫ spMap ιb = spMap (GlobalTheory.RigChart.constHom ρ) ≫ spMap ιb := by
    have h' : (GlobalTheory.RigChart.constHom ρ).comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) := by
      exact RingHom.ext fun x => rfl
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (hρ.trans h'.symm)
  rw [hιb] at e1
  have q1 : ∀ x, spMap ρ ≫ cpt Q x = c' x ≫ π₁ := fun x => ((h₅ x).2.1).symm
  have q2 : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x = c' x ≫ π₂ := fun x => ((h₅ x).2.2).symm
  have q1' : ∀ x, spMap ρ ≫ cpt Q x ≫ β = c' x ≫ π₁ ≫ β := fun x => by
    rw [← Category.assoc, q1, Category.assoc]
  have q2' : ∀ x, spMap (GlobalTheory.RigChart.constHom ρ) ≫ cpt Q x ≫ β = c' x ≫ π₂ ≫ β := fun x => by
    rw [← Category.assoc, q2, Category.assoc]
  rw [q1', q1', q1', q1', q1, q1, q1, q1] at e1
  rw [q2', q2', q2', q2', q2, q2, q2, q2] at e2
  have hW : ∀ x, gm (c' x) zz _ (w.s (fun _ => J (c' x ≫ π₂), fun _ => J (c' x ≫ π₁))) =
      (gm (c' x ≫ π₂) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₂ ≫ β), J (c' x ≫ π₂))))⁻¹ *
        (gm (𝟙 _) zz ⊤ (unitOn u) * gm (c' x ≫ π₁) zz _ (wF.s (fun _ => J₀ (c' x ≫ π₁ ≫ β), J (c' x ≫ π₁)))) :=
    fun x => eq_inv_mul_of_mul_eq (hu (c' x) (h₅ x).1 zz J J₀ hJ hJ₀)
  unfold GlobalTheory.TautRigid.lamC
  rw [e1, e2, hW, hW, hW, hW]
  exact commGroup_fourfold_cancellation _ _ _ _ _ _ _ _ _ _

theorem snd_eq_zero_of_isConstAlong : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) → ∀ j, (ρ (Cn.ψ (MvPolynomial.X (.inr j)))).snd = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hC hconst j
  obtain ⟨ε', τ₀, hε', hFB, hτ⟩ := _root_.GlobalTheory.UCanon.PerCoord.main Xo c φ R hB C Cn
  obtain ⟨B', iG, π₁, π₂, w, c', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hC
  have hA : GlobalTheory.TautRigid.AbConst C.P.D.toPre ρ B' π₁ π₂ w c' := ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hB1 := val_const_of_fromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) hFB k ρ hconst B' iG π₁ π₂ w c' hA
  haveI : CharZero k := by
    let f : c.F →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp (ρ.comp C.b)
    exact (f.charZero_iff f.injective).1 inferInstance
  set M : ℕ := l.M' with hMdef
  have hM : 0 < M := level_pos l
  let Q := C.P.D.toPre
  let u : Fin Cn.N → Rˣ := fun j => (Cn.tor j).unit
  have hu : ∀ j, (u j : R) = Cn.ψ (MvPolynomial.X (.inr j)) := fun j => IsUnit.unit_spec _
  let δ : Fin C.m → LinearMap.BilinForm ℤ Q.X := C.δ
  let ε : Fin Cn.N → LinearMap.BilinForm ℤ Q.X := fun j => (ε' (.inr j) : LinearMap.BilinForm ℤ Q.X)
  have hδ : ∀ i, (ε' (.inl i) : LinearMap.BilinForm ℤ Q.X) = C.δ i := fun i => by
    rw [hε', Cn.cone i]
  have hli : LinearIndependent ℤ (Sum.elim δ ε) := by
    have h0 : LinearIndependent ℤ (fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X)) :=
      ε'.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    have hEq : Sum.elim δ ε = fun κ => (ε' κ : LinearMap.BilinForm ℤ Q.X) := by
      funext κ; rcases κ with i | i
      · exact (hδ i).symm
      · rfl
    rw [hEq]; exact h0
  have key : ∀ y z, ∑ j, ((M : ℤ) * ε j y z) • Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) =
      ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) := by
    intro y z
    set v : Rˣ := ∏ j, u j ^ ((M : ℤ) * ε j y z) with hvdef
    let f : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
    obtain ⟨hg, kk, hk, hv⟩ := hτ y z
    have hU' : GlobalTheory.RigChart.IsUnitTau Q C.s (fun i => (M : ℤ) • C.δ i) y z (GlobalTheory.UU.scaleGen (unitOn v) (τ₀ y z)) := by
      refine ⟨GlobalTheory.UU.scaleGen_isGen _ hg, kk * (f v)⁻¹, ?_, fun zz J hJ => ?_⟩
      · have hfv : ((f v : (FractionRing R)ˣ) : FractionRing R) =
            ∏ j, algebraMap R (FractionRing R) (u j : R) ^ ((M : ℤ) * ε j y z) := by
          simp only [f, v, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
            MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
        have hne : ((f v : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := (f v).ne_zero
        rw [Units.val_mul, hk, Units.val_inv_eq_inv_val, Fin.prod_univ_add]
        simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, LinearMap.smul_apply, smul_eq_mul,
          Cn.bd, hδ, ← hu]
        rw [← hfv, mul_inv_cancel_right₀ hne]
      · have e : gm (toUnit (TK R)).left zz ⊤ (unitOn v) = gm (𝟙 (TK R).left) zz ⊤ (unitOn (f v)) := by
          rw [GlobalTheory.UU.gm_top]
          exact congrArg _ (pullTop_unitOn (algebraMap R (FractionRing R)) _)
        rw [hv zz J hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e, ← _root_.mul_assoc, ← map_mul, ← unitOn_mul,
          inv_mul_cancel_right]
    set s : k := ∑ i, a i * ((((M : ℤ) • δ i) y z : ℤ) : k) with hs
    have hE : ∀ zz : Sp (DualNumber k), gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) =
        gm (𝟙 _) zz ⊤ (unitOn (GlobalTheory.TautRigid.onePlus s * Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
      intro zz
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt C.P.D.toPre.P.isLB zz
      have hp := h₆ y z _ hU' (GlobalTheory.TautRigid.onePlus s) rfl zz J hJ
      have hb := hB1 y z zz J hJ
      have e₁ : gm (spMap ρ) zz ⊤ (unitOn v) = gm (𝟙 _) zz ⊤ (unitOn (Units.map ρ.toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn ρ v)
      have e₂ : gm (spMap (GlobalTheory.RigChart.constHom ρ)) zz ⊤ (unitOn v) =
          gm (𝟙 _) zz ⊤ (unitOn (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) := by
        rw [GlobalTheory.UU.gm_top]; exact congrArg _ (pullTop_unitOn (GlobalTheory.RigChart.constHom ρ) v)
      rw [GlobalTheory.UU.val_scaleGen _ _ _ hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, e₁, e₂, hb] at hp
      change _ = GlobalTheory.TautRigid.lamC Q w c' y z zz J * _ * _ at hp
      rw [unitOn_mul, map_mul]
      exact mul_right_cancel (hp.trans ((congrArg (· * _) (_root_.mul_comm _ _)).trans (mul_mul_mul_comm _ _ _ _)))
    have hv2 := unitOn_inj.1 (unit_ext fun x _ => hE x)
    have h3 := congrArg (fun x => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k x)) hv2
    rw [map_mul, toAdd_mul, GlobalTheory.TautRigid.dlog_onePlus] at h3
    have hc0 : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map (GlobalTheory.RigChart.constHom ρ).toMonoidHom v)) = 0 := by
      have hs0 : ∀ r : R, (GlobalTheory.RigChart.constHom ρ r).snd = 0 := fun r => by
        simp only [GlobalTheory.RigChart.constHom, RingHom.comp_apply]
        rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map]
      erw [hs0, zero_div]
    rw [hc0, add_zero] at h3
    rw [← h3, hvdef, map_prod, map_prod, toAdd_prod]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zpow, map_zpow, toAdd_zpow]
  set L : Fin Cn.N → k := fun j => Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) with hL
  let F : Fin C.m ⊕ Fin Cn.N → Q.X × Q.X → ℤ := fun κ p => Sum.elim δ ε κ p.1 p.2
  have hF : LinearIndependent ℤ F := by
    let e : LinearMap.BilinForm ℤ Q.X →ₗ[ℤ] (Q.X × Q.X → ℤ) :=
      { toFun := fun β p => β p.1 p.2
        map_add' := fun β β' => by funext p; rfl
        map_smul' := fun n β => by funext p; rfl }
    have he : LinearMap.ker e = ⊥ := LinearMap.ker_eq_bot.mpr fun β β' h =>
      LinearMap.ext fun y => LinearMap.ext fun z => congrFun h (y, z)
    have hEq : F = e ∘ Sum.elim δ ε := by
      funext κ p
      rcases κ with i | j <;> rfl
    rw [hEq]
    exact hli.map' e he
  have hz := GlobalTheory.PolFan.eq_zero_of_linearIndependent_int hF k
    (Sum.elim (fun i => a i * (M : k)) (fun j => -(L j * (M : k)))) fun p => by
      rw [Fintype.sum_sum_type]
      have hk := key p.1 p.2
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, LinearMap.smul_apply, smul_eq_mul] at hk
      simp only [Sum.elim_inl, Sum.elim_inr, F]
      have e1 : ∑ i, a i * (M : k) * ((δ i p.1 p.2 : ℤ) : k) = ∑ i, a i * ((M : k) * ((δ i p.1 p.2 : ℤ) : k)) :=
        Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, -(L j * (M : k)) * ((ε j p.1 p.2 : ℤ) : k) =
          -∑ j, (M : k) * ((ε j p.1 p.2 : ℤ) : k) * L j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1, e2, ← hk]
      ring
  have h1 := congrFun hz (Sum.inr j)
  simp only [Sum.elim_inr, Pi.zero_apply, neg_eq_zero, mul_eq_zero, Nat.cast_eq_zero] at h1
  have hLj : Multiplicative.toAdd (GlobalTheory.TautRigid.dlog k (Units.map ρ.toMonoidHom (u j))) = 0 := h1.resolve_right hM.ne'
  rw [GlobalTheory.TautRigid.dlog_apply, Units.coe_map] at hLj
  have := (div_eq_zero_iff.1 hLj).resolve_right (by
    have := GlobalTheory.TautRigid.fst_ne_zero (Units.map ρ.toMonoidHom (u j))
    rwa [Units.coe_map] at this)
  rw [← hu]
  exact this

end GlobalTheory.TorRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.ZConvIdent
open GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem conjU_mul {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) (g k : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h (g * k) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h k := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]

theorem thetaSum_finset_sum {F : Type} [Field F] [NumberField F] {κ ι : Type} [Fintype κ] (s : Finset ι)
    (f : ι → (κ → AdeleRing (𝓞 F) F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (hf a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

theorem translates_kerSmall_le_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ (z : GA D (G.V (.grid i j)) →₀ ℂ) (Φ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank +
        (G.V (.grid i j)).rank) → AF D.host.F) → ℂ) (a : GA D (G.V (.grid i j)) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB Γ.V'.J) (C₀ : ℝ),
      zdeg z ≠ 0 ∧ Φ ∈ Γ.M'.So Bs.ψ Bs.τ₁ ∧
      ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
        C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁))‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hB, z, hz, hS⟩ := _root_.GlobalTheory.SmallDatum.exists_datum_comb_mem_So hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ξ, hξ, hk⟩ := _root_.GlobalTheory.SmallKernel.kerSmall_eq_theta hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv ΦB hB
  refine ⟨z, _, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁, 1, hz, hS, fun g u => le_of_eq ?_⟩
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hpres : ∀ p φ, φ ∈ schA D.host.F _ → om' p φ ∈ schA D.host.F _ := fun p φ hφ => hW.pres p φ hφ
  have hB0 := hB.1
  set a := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁
  set hh := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)
  have ha : ∀ x y, a (x * y) = a x * a y := conjU_mul _ _ _
  have e1 : translates z (kerSmall W Θ' g g₁) u =
      ξ (g, g₁) * z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [translates, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hk, ha, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    ring
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' (z.sum fun k c => c • om' (a k, 1) ΦB) (a u) hh =
      z.sum fun k c => c * thetaSum D.host.F (om' (a u, hh) (om' (a k, 1) ΦB)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_finsuppSum, Finsupp.sum, thetaSum_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, thetaSum_smul]
    · intro k _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hpres _ _ (hpres _ _ hB0))
  rw [e1, e2, norm_mul, hξ, one_mul]

end GlobalTheory.ZConvIdent
end
end

