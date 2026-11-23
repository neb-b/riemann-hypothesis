module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSecondPresentationWeightEq
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WtSecond

lemma left_eq {S : Scheme.{0}} {A B C : Over S} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (H : f ≫ g = h) :
    f.left ≫ g.left = h.left :=
  (Over.comp_left _ _ _ f g).symm.trans (congrArg (fun k => k.left) H)

lemma appLE_congr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

section Core

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    WeightPf.Te D I e ⊗ thickObj R I e G ⟶ WeightPf.Te D' I e ⊗ thickObj R I e G :=
  lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv) (snd (WeightPf.Te D I e) (thickObj R I e G))

lemma chg_fst (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ fst (WeightPf.Te D' I e) (thickObj R I e G) =
      fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv :=
  lift_fst _ _

lemma chg_snd (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ snd (WeightPf.Te D' I e) (thickObj R I e G) = snd (WeightPf.Te D I e) (thickObj R I e G) :=
  lift_snd _ _

lemma chg_chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ chg (G := G) θ.symm = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, chg_fst, ← Category.assoc, chg_fst, Category.assoc, Iso.symm_inv, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, chg_snd, chg_snd, Category.id_comp]

lemma chg_act (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) : chg θ ≫ WeightPf.act g' = WeightPf.act g := by
  have hgi : θ.inv ≫ g'.i = g.i := (Iso.inv_comp_eq θ).2 hi.symm
  have h1 : chg θ ≫ lift (fst (WeightPf.Te D' I e) (thickObj R I e G) ≫ g'.i) (snd _ _) =
      lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, chg_fst, Category.assoc, hgi]
    · rw [Category.assoc, lift_snd, lift_snd, chg_snd]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ μ[thickObj R I e G]) h1)

end Core

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma chg_weight (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) (x₀ : D'.X → D.X)
    (hx : ∀ x, θ.hom.left.appTop.hom (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X (x₀ x)).val =
      (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.X x).val)
    (α' : D'.X) (jt : Fin 4 → D'.P.L.ι) (hjt : LB.Coh D'.P.L (D'.Oφ g'.pG α') jt)
    (W' : (WeightPf.Te D I e ⊗ thickObj R I e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt)
    (ha : W' ≤ (WeightPf.act g).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt) :
    ((WeightPf.act g).left.appLE _ W' ha).hom ((g'.t α').s jt).val =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.X (thickObj R I e G) (x₀ α')) *
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g'.t α').s jt).val := by
  have hΨs : chg (G := G) θ.symm ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)) = (snd (WeightPf.Te D' I e) (thickObj R I e G)) := chg_snd θ.symm
  have hact' : chg (G := G) θ.symm ≫ WeightPf.act g = WeightPf.act g' :=
    chg_act g' g θ.symm (by rw [Iso.symm_hom, ← hi, Iso.inv_hom_id_assoc])
  have hs'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (chg (G := G) θ.symm).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
      (left_eq hΨs).symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => hs hy
  have ha'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (WeightPf.act g').left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (WeightPf.act g').left = (chg (G := G) θ.symm).left ≫ (WeightPf.act g).left :=
      (left_eq hact').symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => ha hy
  have hΦW : W' ≤ (chg (G := G) θ).left ⁻¹ᵁ ((chg (G := G) θ.symm).left ⁻¹ᵁ W') := by
    have h2 : (chg (G := G) θ).left ≫ (chg (G := G) θ.symm).left = 𝟙 _ :=
      (left_eq (chg_chg θ)).trans (Over.id_left _)
    rw [← Scheme.Hom.comp_preimage, h2]
    exact fun y hy => hy
  have key := WeightPf.t_act g' α' jt hjt _ hs'' ha''
  have k2 := congrArg ((chg (G := G) θ).left.appLE _ W' hΦW).hom key
  have e0 : (chg (G := G) θ).left ≫ (WeightPf.act g').left = (WeightPf.act g).left :=
    left_eq (chg_act g g' θ hi)
  have e1 : (chg (G := G) θ).left ≫ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
    left_eq (chg_snd θ)
  have L : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.act g').left.appLE _ _ ha'').hom x) =
      ((WeightPf.act g).left.appLE _ W' ha).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e0 _ ha)
  have S : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((snd (WeightPf.Te D' I e) (thickObj R I e G)).left.appLE _ _ hs'').hom x) =
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e1 _ hs)
  have hres : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.Te D' I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom x) =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom ((chg (G := G) θ).left.appTop.hom x) := by
    intro x
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    first | erw [Scheme.Hom.appLE_map] | rfl
  have hchi : (chg (G := G) θ).left.appTop.hom (TorusInj.chiP D'.X (thickObj R I e G) α') =
      TorusInj.chiP D.X (thickObj R I e G) (x₀ α') := by
    unfold TorusInj.chiP
    rw [← SplitTorusHom.appTop_comp, chg_fst, SplitTorusHom.appTop_comp, ← hx α',
      ← SplitTorusHom.appTop_comp θ.inv θ.hom, Iso.inv_hom_id, SplitTorusHom.appTop_id]
  rw [map_mul] at k2
  exact (L _).symm.trans (k2.trans (congrArg₂ (· * ·) ((hres _).trans (congrArg _ hchi)) (S _)))

end Weight

theorem wt_second : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (e : ℕ) (xe : D'.toPre.X ≃+ D.toPre.X), GlobalTheory.CharAgree.Match (U.gt e) (U'.gt e) xe → ∀ (α' : D'.toPre.X) (jt : Fin 4 → D'.toPre.P.L.ι), LB.Coh D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt → ∀ (W' : (WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt) (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt), ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom (((U'.gt e).t α').s jt).val = ((WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) (xe α')) * ((snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs).hom (((U'.gt e).t α').s jt).val := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' e xe hM α' jt hjt W' hs ha
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨hN, -, -, -⟩ := hR
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  obtain ⟨θ, hθ, hi⟩ := CharAgree.exists_torus_iso hI (U.gt e) (U'.gt e)
  have := CharAgree.connected_thick hI e
  obtain ⟨x₀, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.toPre.X D'.toPre.X θ hθ

  have hM₀ : CharAgree.Match (U.gt e) (U'.gt e) x₀ := by
    intro Z r z J J' hJ hJ' _ h' x
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
      Over.mk (r ≫ (thickObj R (maximalIdeal R) e G).hom)
    let a : FinalForm ⟶ thickObj R (maximalIdeal R) e G := Over.homMk r rfl
    let τ := (U'.gt e).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U'.gt e) a).2 h')
    have hτ : τ ≫ (U'.gt e).i = a := (U'.gt e).isKernel.lift_fst _ _ _
    have hτ' : (τ ≫ θ.hom) ≫ (U.gt e).i = a := by rw [Category.assoc, hi, hτ]
    have k := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D.toPre e G (U.gt e) FinalForm
      (τ ≫ θ.hom) 1 z J hJ (x₀ x)).1
    have k' := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D'.toPre e G (U'.gt e) FinalForm
      τ 1 z J' hJ' x).1
    rw [hτ'] at k
    rw [hτ] at k'
    refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
    rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
    refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
    exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))
  have hxe : (xe : D'.toPre.X → D.toPre.X) = x₀ := CharAgree.match_unique hI _ _ hM hM₀
  rw [congrFun hxe α']
  exact chg_weight (U.gt e) (U'.gt e) θ hi x₀ hx α' jt hjt W' hs ha

end GlobalTheory.WtSecond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionSumsEqTransport
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
set_option maxHeartbeats 1600000 in
theorem expansion_sums_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ e : ℕ, ∃ S : Finset D'.toPre.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → (∀ α' ∉ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0) ∧ (∀ α' ∉ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0) ∧ ∑ α' ∈ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * ∑ α' ∈ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  intro R _ _ _ _ G _ _ _ D D' A A' U U' Φ w wL _ _ _ hlev xe _ σ σ' f f' hE hE' hσ e
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U.toUnifPre e 2 σ f (hE e)
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U'.toUnifPre e 2 σ' f' (hE' e)
  refine ⟨S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂, fun Z r z J J' hJ hJ' => ?_⟩
  obtain ⟨A₁, B₁⟩ := hS₁ Z r z J hJ
  obtain ⟨A₂, B₂⟩ := hS₂ Z r z J' hJ'
  have z₁ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0 := by
    intro α' hα
    refine A₁ _ fun hc => hα (Finset.mem_union_left _ (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩))
  have z₂ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0 := by
    intro α' hα
    exact A₂ _ fun hc => hα (Finset.mem_union_right _ hc)
  refine ⟨z₁, z₂, ?_⟩

  have E₁ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val =
      ∑ α ∈ S₁, sval (f α) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) r z J).val := by
    rw [← Finset.sum_subset (Finset.subset_union_left) (fun α' _ hα => by
      rw [A₁ (xe α') fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩), zero_mul]),
      Finset.sum_map]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h₀ : xe (xe.symm.toEquiv.toEmbedding α) = α := xe.apply_symm_apply α
    rw [h₀]
  have E₂ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val =
      ∑ α' ∈ S₂, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val :=
    (Finset.sum_subset (Finset.subset_union_right) (fun α' _ hα => by rw [A₂ α' hα, zero_mul])).symm
  rw [E₁, E₂]
  obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  rw [← B₁ jL hL, ← B₂ jL' hL']
  obtain ⟨J₀, hJ₀, k₀⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL) (fun _ _ _ => rfl) (fun _ => hL)
  obtain ⟨J₀', hJ₀', k₀'⟩ := exists_good U'.LG.L U'.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL') (fun _ _ _ => rfl) (fun _ => hL')
  have c₀ : J₀ (r ≫ (fstG (maximalIdeal R) e G).left) = jL := k₀ PUnit.unit
  have c₀' : J₀' (r ≫ (fstG (maximalIdeal R) e G).left) = jL' := k₀' PUnit.unit
  have hS : sv U.toUnifPre 2 σ (r ≫ (fstG (maximalIdeal R) e G).left) z jL =
      (gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')).val *
        sv U'.toUnifPre 2 σ' (r ≫ (fstG (maximalIdeal R) e G).left) z jL' := by
    have H := hσ Z (r ≫ (fstG (maximalIdeal R) e G).left) z J₀ J₀' hJ₀ hJ₀'
    rw [sval_of σ _ z J₀ (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact c₀),
      sval_of σ' _ z J₀' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact c₀'), c₀, c₀'] at H
    exact H
  have W : gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) *
        wv U'.toUnifPre e r z (J' (r ≫ (U'.gt e).pG.left)) jL' ^ 2 =
      wv U.toUnifPre e r z (J (r ≫ (U.gt e).pG.left)) jL ^ 2 *
        gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') :=
    (hlev e).2 Z r z (J (r ≫ (U.gt e).pG.left)) (J' (r ≫ (U'.gt e).pG.left)) jL jL' (hJ _) (hJ' _) hL hL'
  have hO : ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left) =
      gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := by
    show gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J ((r ≫ (U'.gt e).pG.left) ≫ Φ.hom.left))
      (fun _ => J' (r ≫ (U'.gt e).pG.left)) = _
    rw [Category.assoc, (hlev e).1]
  rw [hS, hO, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, W]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTwoFactorSqValuesCorrespond
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famB_wtTwo {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (y : T ⟶ D.P.A) (α : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (y.left ≫ D.famφB α i) ^ DegPre.famε 2 i =
      h y.left * h (y * cP D T α).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have a₀ : y.left ≫ D.famφB α 0 = y.left := Category.comp_id _
  have a₁ : y.left ≫ D.famφB α 1 = (y * cP D T α).left := congrArg (fun z => z.left)
    ((MonObj.comp_mul y (𝟙 _) (cP D _ α)).trans (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : y.left ≫ D.famφB α 2 = (cP D T α).left := congrArg (fun z => z.left) (comp_cP D y α)
  have a₃ : y.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) y)
  rw [Fin.prod_univ_four, a₀, a₁, a₂, a₃]
  show _ ^ (((2 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  norm_num

theorem sq_unit_cancel {A : Type} [CommRing A] [IsDomain A] {s s' F₁ F₁' : A}
    {θ θ' V V' ωx ωam ωm2 ω1 ωa ωm : Aˣ} (hs : s ≠ 0)
    (h₁ : F₁ = s * (θ * V).val) (h₂ : F₁' = s' * (θ' * V').val)
    (h₃ : F₁ ^ 2 = (ωx * ωam * ωm2⁻¹ * ω1).val * F₁' ^ 2)
    (h₄ : s ^ 2 = (ωa * ωa * ω1⁻¹ * ω1).val * s' ^ 2)
    (h₅ : θ ^ 2 = ωam * ωm2⁻¹ * ωa⁻¹ * ωa⁻¹ * ωm * ωm * ωx * ω1⁻¹ * θ' ^ 2) :
    V' ^ 2 = (ωm * ω1⁻¹) ^ 2 * V ^ 2 := by
  have hs' : s' ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, MulZeroClass.mul_zero] at h₄
    exact hs (pow_eq_zero_iff two_ne_zero |>.1 h₄)
  have E : ωa * ωa * ω1⁻¹ * ω1 * (θ * V) ^ 2 = ωx * ωam * ωm2⁻¹ * ω1 * (θ' * V') ^ 2 :=
    Units.ext (mul_left_cancel₀ (pow_ne_zero 2 hs') (by
      rw [h₁, h₂] at h₃
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h₃ h₄ ⊢
      linear_combination h₃ - ((θ : A) * V) ^ 2 * h₄))
  apply Additive.ofMul.injective
  have E' := congrArg Additive.ofMul E
  have h₅' := congrArg Additive.ofMul h₅
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at E' h₅' ⊢
  linear_combination (norm := abel) h₅' - E'

end GlobalTheory.PsiCompare


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare in
theorem GlobalTheory.PsiCompare.famMult_sq_corr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → ∀ (y : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left) (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → IsDomain ((DegPre.BF D.toPre (FractionRing R)).left.presheaf.stalk z) → sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left z J ≠ 0 → val (DegPre.famMult D'.toPre (FractionRing R) 2 (2 • y) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (xe (2 • y)) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2 := by
  intro R _ _ _ D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y z J J' hJ hJ' hdom h0
  haveI := hΦ
  haveI := hdom
  set κ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R) := fst (TF (R := R) (FractionRing R)) D.toPre.P.A with hκ
  set pB : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A := DegPre.prB D.toPre (FractionRing R) with hpB
  set m' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y) with hm'
  set a : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := pB ≫ Φ.inv with ha
  set x' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := a * m'⁻¹ with hx'
  let T := DegPre.BF D.toPre (FractionRing R)
  have hxm : x' * m' = a := inv_mul_cancel_right _ _
  have hmΦ : m' ≫ Φ.hom = cP D.toPre T (xe (2 • y)) := cP_comp Φ.hom (hc y) T
  have haΦ : a ≫ Φ.hom = pB := by rw [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hx'Φ : (x' ≫ Φ.hom) * cP D.toPre T (xe (2 • y)) = pB := by
    rw [← hmΦ, ← MonObj.mul_comp, hxm, haΦ]

  have e₁ := hf (xe (2 • y)) 0 T κ (x' ≫ Φ.hom) z J hJ
  have u₁ : uVal D.toPre (FractionRing R) 2 0 (cP D.toPre _ (xe (2 • y))) (lift κ (x' ≫ Φ.hom)) z J =
      cubV D.toPre.cub z J (cP D.toPre T (xe (2 • y))) (cP D.toPre T (xe (2 • y))) (x' ≫ Φ.hom) := by
    have C := isCub_cubV D.toPre.cub hJ
    have ρ₂ : lift κ (x' ≫ Φ.hom) ≫ DegPre.prB D.toPre (FractionRing R) = x' ≫ Φ.hom := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₁, hx'Φ, zero_add] at e₁

  have e₂ := hf' (2 • y) 0 T κ x' z J' hJ'
  have u₂ : uVal D'.toPre (FractionRing R) 2 0 (cP D'.toPre _ (2 • y)) (lift κ x') z J' =
      cubV D'.toPre.cub z J' m' m' x' := by
    have C := isCub_cubV D'.toPre.cub hJ'
    have ρ₂ : lift κ x' ≫ DegPre.prB D'.toPre (FractionRing R) = x' := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₂, hxm, zero_add] at e₂

  have e₃ := hcorr (2 • y) T.left x'.left z J J' hJ hJ'
  have p₄ : x' * m' ^ 2 = a * m' := by rw [pow_two, ← _root_.mul_assoc, hxm]
  rw [prod_famB_wtTwo, cPoint_nsmul, ← hm', p₄, map_nsmul] at e₃

  have e₄ := hcorr 0 T.left a.left z J J' hJ hJ'
  rw [prod_famB_wtTwo, smul_zero, map_zero, cPoint_zero, _root_.mul_one,
    show a.left ≫ Φ.hom.left = pB.left from congrArg (fun q => q.left) haΦ] at e₄

  have e₅ := hcub T z J J' hJ hJ' _ rfl m' m' x'
  have p₁ : m' * m' * x' = a * m' := by rw [mul_comm (m' * m') x', ← _root_.mul_assoc, hxm]
  have p₃ : m' * x' = a := by rw [mul_comm, hxm]
  rw [hmΦ, p₁, p₃, ← sq] at e₅
  exact sq_unit_cancel h0 e₁ e₂ e₃ e₄ e₅
end
end

