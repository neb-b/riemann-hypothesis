module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullLinear

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusCoord

theorem map_left_fst {S T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

theorem ext_of_iso_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' Z : Over S'}
    (e : A' ≅ (Over.pullback f).obj A) {a b : Z ⟶ A'}
    (h : a.left ≫ e.hom.left ≫ pullback.fst A.hom f = b.left ≫ e.hom.left ≫ pullback.fst A.hom f) :
    a = b := by
  rw [← cancel_mono e.hom]
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simpa only [Over.comp_left, Category.assoc] using h
  · exact (Over.w (a ≫ e.hom)).trans (Over.w (b ≫ e.hom)).symm

theorem ext_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {Z : Over S'}
    {a b : Z ⟶ (Over.pullback f).obj A}
    (h : a.left ≫ pullback.fst A.hom f = b.left ≫ pullback.fst A.hom f) : a = b :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w a).trans (Over.w b).symm))

theorem act_proj {S S' : Scheme.{0}} (f : S' ⟶ S) {A : Over S} {A' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) {u : A ⟶ A} {u' : A' ⟶ A'}
    (h : u' ≫ e = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e.left ≫ pullback.fst A.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem pG_left : g.pG.left = g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) := rfl

theorem im_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e) :
    im g (τ ≫ g.i) = 1 := by
  have := g.q_hom
  rw [← im_one g]
  refine im_congr g ?_
  rw [Category.assoc, g.isKernel.w, MonObj.one_comp, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem exists_torus_of_im {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : Z ⟶ thickObj R I e G) (h : im g y = 1) : ∃ τ : Z ⟶ WeightPf.Te D I e, τ ≫ g.i = y := by
  have h1 : y ≫ g.q = (1 : Z ⟶ thickObj R I e G) ≫ g.q := by
    refine ext_of_pullback _ ?_
    have := congrArg (·.left) (h.trans (im_one g).symm)
    exact ((Category.assoc _ _ _).trans this).trans (Category.assoc _ _ _).symm
  obtain ⟨τ, hτ⟩ := exists_torus g y 1 h1
  exact ⟨τ, by rw [hτ, _root_.mul_one]⟩

theorem prod_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ WeightPf.Te D I e)
    (χ : D.X) {U : Type} [CommGroup U] (f : (Z.left ⟶ D.P.A.left) → U) :
    ∏ k, f ((τ ≫ g.i).left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, (τ ≫ g.i).left ≫ D.Oφ g.pG χ k = D.Oφ (im g (τ ≫ g.i)) χ k := fun k =>
    WeightPf.Oφ_comp ((Over.map (thick R I e)).map (τ ≫ g.i)) g.pG χ k
  simp only [e0]
  rw [Fin.prod_univ_four, im_torus]
  change f ((1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A) * cPt Z χ).left ^ (-1 : ℤ) *
    f (cPt Z χ).left ^ (1 : ℤ) * f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (1 : ℤ) *
    f (1 : (Over.map (thick R I e)).obj Z ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  rw [_root_.one_mul, zpow_neg_one, zpow_neg_one, zpow_one, zpow_one, inv_mul_cancel, _root_.one_mul,
    mul_inv_cancel]

theorem torusEndOf_iff {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) :
    TorusEndOf X h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X),
      gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} {D : DegPre R} {D' : DegPre R'} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I' D' e G') {F : D'.P.A.left ⟶ D.P.A.left}
  {h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left}

theorem char_eq (w : LB.Iso D'.P.L (D.P.L.pull F)) {x' : D'.X} {x : D.X}
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    (hm : PMaps w (D'.Oφ g'.pG x') (D.Oφ g.pG x) Oinvε (g'.t x') (g.t x) h)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))}
    {s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))}
    (τ' : Z' ⟶ WeightPf.Te D' I' e) (τ : Over.mk s ⟶ WeightPf.Te D I e)
    (hτ : (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h) (z : Z'.left) :
    gm (Y := Z'.left) τ.left z ⊤ (charUnit _ D.X x) = gm τ'.left z ⊤ (charUnit _ D'.X x') := by
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB z
  obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
  have h₁ := (val_torus_point_and_translate R I D e G g (Over.mk s) τ 1 z J hJ x).1
  have h₂ := (val_torus_point_and_translate R' I' D' e G' g' Z' τ' 1 z J' hJ' x').1
  have h₃ := hm Z'.left (τ' ≫ g'.i).left z
    (fun k => J (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => J' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
    (fun k => hJ (((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k) ≫ F))
    (fun k => hJ' ((τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' k))
  rw [prod_torus g' τ' x' (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at h₃
  refine h₁.symm.trans (Eq.trans ?_ (h₃.trans h₂))
  rw [hτ]
  exact val_of (g.t x) ((τ' ≫ g'.i).left ≫ h) z J _ (fun k => by
    rw [Category.assoc, Category.assoc, hψ k])

theorem exists_point {x' : D'.X} {x : D.X} (hp : g'.pG.left ≫ F = h ≫ g.pG.left)
    (hψ : ∀ κ : Fin 4, D'.Oφ g'.pG x' κ ≫ F = h ≫ D.Oφ g.pG x κ)
    {Z' : Over (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))} (τ' : Z' ⟶ WeightPf.Te D' I' e) :
    ∃ (s : Z'.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (τ : Over.mk s ⟶ WeightPf.Te D I e),
      (τ ≫ g.i).left = (τ' ≫ g'.i).left ≫ h := by
  let y : Over.mk (((τ' ≫ g'.i).left ≫ h) ≫ (thickObj R I e G).hom) ⟶ thickObj R I e G :=
    Over.homMk ((τ' ≫ g'.i).left ≫ h) rfl
  have h1 : (τ' ≫ g'.i).left ≫ g'.pG.left = (τ' ≫ g'.i).left ≫ D'.Oφ g'.pG x' 3 := by
    refine (congrArg (·.left) (im_torus g' τ')).trans ?_
    exact (WeightPf.Oφ_comp ((Over.map (thick R' I' e)).map (τ' ≫ g'.i)) g'.pG x' 3).symm
  have h2 : im g y = 1 := by
    refine Over.OverMorphism.ext ?_
    refine Eq.trans ?_ (WeightPf.Oφ_comp ((Over.map (thick R I e)).map y) g.pG x 3)
    change ((τ' ≫ g'.i).left ≫ h) ≫ g.pG.left = ((τ' ≫ g'.i).left ≫ h) ≫ D.Oφ g.pG x 3
    rw [Category.assoc, Category.assoc, ← hp, ← hψ, ← Category.assoc, h1, Category.assoc]
  obtain ⟨τ, hτ⟩ := exists_torus_of_im g y h2
  exact ⟨_, τ, congrArg (·.left) hτ⟩

end Two

theorem oLinear_of_isPullUnif : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → (∀ a, (ιG'.act a) ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf φ)).map (ιG.act a)) → (∀ a, (Over.pullback (jK R')).map (ιG'.act a) ≫ U'.gen.hom = U'.gen.hom ≫ ιA'.act a) → (∀ (a : O) (y : D'.toPre.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) → U'.OLinear O ιD' ιA' ιG' := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ U U' hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    hlin hG hgen hx hB
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ) (a : O), ((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left := by
    intro e a
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom (hG a), Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ) (a : O), (Over.pullback (thick R' I' e)).map (ιG'.act a) ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map (ιD'.onB.act a) := by
    intro e a
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = g.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ g u
      rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
      rw [← k, ← hlin.q_lin e a]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ ιD'.onB.act a := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ (ιD'.onB.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom (hB a), (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine ⟨hgen, hq, fun e a => ?_⟩
  obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
  have := ιD'.onB.hom a
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (star a • χ)).1 ((hpt e).2 (star a • χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.PullLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LbIsoPwPullPowLocal
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem lbIso_pw_pull_of_hasGen {X : Scheme.{0}} {L : LB X} (F : X ⟶ X) (t : ℤ)
    (h : MulPull.HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -t]) : LBIso (pw L t) (L.pull F) := by
  obtain ⟨a, ha⟩ := h
  have mem : ∀ (x : X) (j k : L.ι), F x ∈ L.U j → x ∈ L.U k → x ∈ LB.wchart L ![F, 𝟙 X] ![j, k] :=
    fun x j k hj hk => Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact hj
      · exact hk
  have le : ∀ p : (L.pull F).ι × L.ι,
      (L.pull F).U p.1 ⊓ L.U p.2 ≤ LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] :=
    fun p x hx => mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso (pw L t) (L.pull F) := ⟨fun p => res (le p) (a.s _)⟩
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ j k, F (r y) ∈ L.U j → r y ∈ L.U k →
      gw w r y j k = gm r y (LB.wchart L ![F, 𝟙 X] ![j, k]) (a.s ![j, k]) := fun j k hj hk =>
    gm_res r y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
  rw [e j k hj hk, e j' k' hj' hk', gen_trans ha r y (mem _ _ _ hj hk) (mem _ _ _ hj' hk'), trF, Fin.prod_univ_two]
  congr 1
  show gm (r ≫ F) y _ (L.g j j') ^ (1 : ℤ) * gm (r ≫ 𝟙 X) y _ (L.g k k') ^ (-t) =
    gm (r ≫ F) y _ (L.g j j') * (gm r y (L.U k ⊓ L.U k') (L.g k k' ^ t))⁻¹
  rw [zpow_one, Category.comp_id, map_zpow, zpow_neg]

theorem CP.lbIso_pw_pull_pow {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ) :
    LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  have hL := M.L.isLB
  have hcube : MulPull.HasGen M.L.L (thφ B (x3 B)) thε := ⟨M.c.t, M.c.isGen⟩
  have hrig : MulPull.HasGen M.L.L (K := PUnit) (fun _ => eSec B) (fun _ => 1) := ⟨M.L.rig, M.L.rigGen⟩
  have hsym : MulPull.HasGen M.L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1] := ⟨M.sym, M.sym_gen⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 B) ((hrig.pull B.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one, one_left]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) n
  refine lbIso_pw_pull_of_hasGen _ _ (h.inv.of_formEq hL fun U _ h => ?_)
  rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
  rfl

theorem lbIso_pw_pull_pow_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) :=
  fun _ _ _ _ _ _ M n => M.lbIso_pw_pull_pow n

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem exists_fraction_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) :
    ∃ g : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R)),
      g ≫ jK R = jK R' ≫ specOf φ ∧ jFK (R := R') F ≫ g = jFK (R := R) F := by
  have inj : Function.Injective ((algebraMap R' (FractionRing R')).comp φ) :=
    (injective_iff_map_eq_zero _).2 fun r hr => by
      have e := hF r
      rw [show algebraMap R' (FractionRing R') (φ r) = 0 from hr, map_zero] at e
      exact (IsFractionRing.injective R (FractionRing R))
        (((algebraMap (FractionRing R) F).injective (e.trans (map_zero _).symm)).trans (map_zero _).symm)
  obtain ⟨ψ, h₁⟩ : ∃ ψ : FractionRing R →+* FractionRing R',
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing R) inj, RingHom.ext fun r => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have h₂ : (algebraMap (FractionRing R') F).comp ψ = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (congrArg (algebraMap (FractionRing R') F) (RingHom.congr_fun h₁ r)).trans (hF r).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · exact (Spec.map_comp _ _).symm.trans ((congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₁).trans
      (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' (FractionRing R')))))
  · exact (Spec.map_comp _ _).symm.trans (congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₂)

theorem grp_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl

end GlobalTheory.ThetaBaseChange

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaBaseChange in
set_option maxHeartbeats 1600000 in
theorem qkToAk_baseChange : GlobalFnsSt → SecBaseChangeSt → QkBaseChangeSt := by
  intro hG _ R R' _ _ _ _ I I' _ _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU F _ _ _ hF k hk p x p' x' hy hg hx H w' hw'
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨hx1, H⟩ := H w hw
  obtain ⟨g, hg₁, hg₂⟩ := exists_fraction_map φ F hF
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hΘF : (jFK (R := R') F ≫ jK R') ≫ specOf φ = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, ← hg₁, ← Category.assoc, hg₂]
  obtain ⟨Θ, hΘ₁, hΘ₂⟩ := exists_cmp hΘF (pull_grp hD).1.w
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : A'.A.left ⟶ A.A.left, Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      Φ ≫ A.A.hom = A'.A.hom ≫ g :=
    ⟨gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁]), gA.1.lift_fst _ _ _, gA.1.lift_snd _ _ _⟩
  have gΦ : IsGrpPullback A'.A A.A g Φ := gA.cancel (gA'.congr hg₁.symm hΦ₁.symm) hΦ₂
  have hxΦ : x'.left ≫ Φ = x.left := gA.1.hom_ext (by
    rw [Category.assoc, hΦ₁, ← hx]; simp only [Category.assoc]) (by
    rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w x', Over.w x]; exact hg₂)
  refine ⟨pow_eq_one_of_push hg₂ gΦ hxΦ hx1, fun θ' hθ' => ?_⟩
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    rw [Category.assoc, hΦ₁, ← Category.assoc, ← Category.assoc U'.gen.hom.left, n₃]
    exact congrArg (· ≫ _) (Category.id_comp _)
  obtain ⟨v₂, hv₂, hsq⟩ := exists_side A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw _ n₁ hw' hwL _ hΦ₃
  obtain ⟨v, hv, hvv⟩ := exists_unpull hv₂ _ n₂ (P := Φ) (by rw [← Category.assoc, n₂, Category.id_comp])
  obtain ⟨Ω, hΩ₁, hΩ₂⟩ := exists_cmp hg₂ hΦ₂
  obtain ⟨ω, hω₁, hω₂⟩ := exists_cmp_inv hg₂ gΦ.1
  have hΩω : Ω ≫ ω = 𝟙 _ := cmp_ext gΦ.1 (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp])
    (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _ := congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n])
  have hn₁ : n.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)
  have hn₂ : n.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)
  have hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R := R') F) A'.A).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)
  have hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R := R') F) A'.A).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left,
      Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩
  have x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left := by
    rw [hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω,
      Category.comp_id]
  have x₂ : Ξ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]
    refine (congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_
    rw [← Category.assoc, ← Category.assoc, hh₂]
    simp only [Category.assoc]
  have hΞ₁ : Ξ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₁]
    exact (congrArg (_ ≫ ·) hΩ₁).trans hh₁
  have hΞ₂ : Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)
    simp only [Category.assoc]
  obtain ⟨θ, hθ, hact⟩ := exists_theta_moved A.isLB A'.isLB hg₂ gΦ hv hω₁ hω₂ θ' (x := x) (by rw [hθ']; exact hxΦ)
  obtain ⟨ν, hν, Hν⟩ := H θ hθ
  obtain ⟨ν', hν', Hν'⟩ := GlobalTheory.phiRel_transport hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k p p' hy hg ν hν
  refine ⟨ν', hν', fun t' t₂' s' s₂' E E₂ hA => ?_⟩
  have bij := (expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw).1
  have bij' := (expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw').1
  choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k
  have key : ∀ a' b', U'.toUnifPre.ExpandsF F k w' a' b' → ∃ a b, Moved v ω a' a ∧
      U.toUnifPre.ExpandsF F k w a b ∧ pl b = b' := fun a' b' E => by
    obtain ⟨a, ha⟩ := exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'
    obtain ⟨b, σ, h₁, h₂⟩ := (bij a).exists
    refine ⟨a, b, ha, ⟨σ, h₁, h₂⟩, (bij' a').unique ?_ E⟩
    obtain ⟨σ', h₁', -⟩ := E
    exact ⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF
      Θ hΘ₁ hΘ₂ Ξ hΞ₁ hΞ₂ k σ σ' b (pl b)
      (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩
  obtain ⟨t, s, m, e, rfl⟩ := key t' s' E
  obtain ⟨t₂, s₂, m₂, e₂, rfl⟩ := key t₂' s₂' E₂
  exact Hν' s s₂ _ _ (hpl s) (hpl s₂) (Hν t t₂ s s₂ e e₂ (hact t' t₂' t t₂ m m₂ hA))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothProjOfFree
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem TQ.smooth_proj_of_free {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G : Over S} [GrpObj G] (Q : TQ G X) : Smooth Q.q.left := by
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact Q.q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

theorem TQ.dim_eq_add_finrank :
    (∀ (S : Scheme.{0}) [Nonempty S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] (Q : TQ G X) (g g' : ℕ), SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' Q.B.hom → g = g' + Module.finrank ℤ X) := by
  intro S hS X _ _ _ G _ Q g g' dG dB
  obtain ⟨y⟩ := hS
  have := Q.i_hom
  have := Q.smooth_proj_of_free
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim Q.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (Q.isKernel.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom Q.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w Q.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end GlobalTheory.UU
end

