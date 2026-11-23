module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace SplitTorusPow

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

noncomputable def torusMap (S : Scheme.{0}) (φ : X →+ X') : splitTorus S X' ⟶ splitTorus S X :=
  (splitTorusPointsEquiv S X (splitTorus S X')).symm
    ((splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _)).comp (AddMonoidHom.toMultiplicative φ))

theorem torusMap_char (φ : X →+ X') (χ : X) :
    (torusMap S φ).left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  rw [← splitTorusPointsEquiv_val, torusMap, MulEquiv.apply_symm_apply]
  change (splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _) (Multiplicative.ofAdd (φ χ))).val = _
  rw [splitTorusPointsEquiv_val]
  simp

theorem points_comp_torusMap (φ : X →+ X') {Z : Over S} (t : Z ⟶ splitTorus S X') :
    splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) =
      (splitTorusPointsEquiv S X' Z t).comp (AddMonoidHom.toMultiplicative φ) := by
  refine MonoidHom.ext fun χ => Units.ext ?_
  change (splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) (Multiplicative.ofAdd χ.toAdd)).val =
    (splitTorusPointsEquiv S X' Z t (Multiplicative.ofAdd (φ χ.toAdd))).val
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, ← torusMap_char, Over.comp_left,
    Scheme.Hom.comp_appTop]
  rfl

theorem mul_comp_torusMap (φ : X →+ X') {Z : Over S} (a b : Z ⟶ splitTorus S X') :
    (a * b) ≫ torusMap S φ = (a ≫ torusMap S φ) * (b ≫ torusMap S φ) := by
  apply (splitTorusPointsEquiv S X Z).injective
  rw [map_mul, points_comp_torusMap, points_comp_torusMap, points_comp_torusMap, map_mul,
    MonoidHom.mul_comp]

theorem isMonHom_torusMap (φ : X →+ X') : IsMonHom (torusMap S φ) := by
  constructor
  · have h : (1 : 𝟙_ (Over S) ⟶ splitTorus S X') ≫ torusMap S φ = 1 := by
      apply (splitTorusPointsEquiv S X _).injective
      rw [points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
    simpa [Hom.one_def] using h
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
      mul_comp_torusMap (S := S) φ (fst (splitTorus S X') (splitTorus S X')) (snd _ _)

def incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) : X →+ X' :=
  xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => X) i)

theorem incl_apply {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) (χ : X) :
    incl xe i χ = xe.symm (Pi.single i χ) := rfl

theorem sum_incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (x : X') : ∑ i, incl xe i (xe x i) = x := by
  simp only [incl_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]

theorem hom_ext_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    {u v : Multiplicative X' →* M}
    (h : ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) =
      v.comp (AddMonoidHom.toMultiplicative (incl xe i))) : u = v := by
  refine MonoidHom.ext fun x => ?_
  have e : x = ∏ i, Multiplicative.ofAdd (incl xe i (xe x.toAdd i)) := by
    rw [← ofAdd_sum, sum_incl]; rfl
  rw [e, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ =>
    DFunLike.congr_fun (h i) (Multiplicative.ofAdd (xe x.toAdd i))

theorem exists_hom_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    (w : Fin j → (Multiplicative X →* M)) :
    ∃ u : Multiplicative X' →* M,
      ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) = w i := by
  refine ⟨∏ i, (w i).comp (AddMonoidHom.toMultiplicative
    ((Pi.evalAddMonoidHom (fun _ => X) i).comp xe.toAddMonoidHom)), fun i => ?_⟩
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, Finset.prod_eq_single i]
  · simp [incl_apply]
  · intro k _ hk
    simp [incl_apply, Pi.single_eq_of_ne hk]
  · simp

noncomputable def isPowGrp (S : Scheme.{0}) {j : ℕ} (xe : X' ≃+ (Fin j → X)) :
    IsPowGrp (splitTorus S X') (splitTorus S X) j where
  pr i := torusMap S (incl xe i)
  hom i := isMonHom_torusMap _
  lim := Fan.IsLimit.mk _
    (fun s => (splitTorusPointsEquiv S X' s.pt).symm
      (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose)
    (fun s i => by
      apply (splitTorusPointsEquiv S X s.pt).injective
      refine (points_comp_torusMap (incl xe i) _).trans ?_
      rw [MulEquiv.apply_symm_apply]
      exact (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i)
    (fun s m hm => by
      apply (splitTorusPointsEquiv S X' s.pt).injective
      rw [MulEquiv.apply_symm_apply]
      refine hom_ext_incl xe fun i => ?_
      rw [(exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i,
        ← hm i]
      exact (points_comp_torusMap (incl xe i) m).symm)

end SplitTorusPow

theorem exists_isPowGrp_splitTorus : ∀ (S : Scheme.{0}) (X X' : Type) [AddCommGroup X] [AddCommGroup X'] (j : ℕ) (xe : X' ≃+ (Fin j → X)), ∃ p : IsPowGrp (splitTorus S X') (splitTorus S X) j, ∀ (i : Fin j) (χ : X), res (fun x _ => show (p.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (p.pr i).left ⊤ (charUnit S X χ)) = charUnit S X' (xe.symm (Pi.single i χ)) := by
  intro S X X' _ _ j xe
  refine ⟨SplitTorusPow.isPowGrp S xe, fun i χ => ?_⟩
  ext1
  rw [← SplitTorusPow.incl_apply, ← SplitTorusPow.torusMap_char]
  change ((splitTorus S X').left.presheaf.map (𝟙 _)).hom
    ((SplitTorusPow.torusMap S (SplitTorusPow.incl xe i)).left.appTop.hom (charUnit S X χ).val) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowAct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open GlobalTheory.Serre in
theorem exists_powAct : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), (∀ (O : Type) [Ring O] (r : RingAct G O), ∃ r' : RingAct G' O, ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a) ∧ ∀ (O : Type) [CommRing O] (r : Geo.Tor.OAct O G), ∃ r' : Geo.Tor.OAct O G', ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a := by
  intro S G' G _ _ _ _ j p
  obtain ⟨pr, hpr, hl⟩ := p
  have hprI : ∀ i, IsMonHom (pr i) := hpr
  have hext : ∀ {X : Over S} (f g : X ⟶ G'), (∀ i, f ≫ pr i = g ≫ pr i) → f = g :=
    fun f g h => Fan.IsLimit.hom_ext hl f g h

  let lf : (G ⟶ G) → (G' ⟶ G') := fun f => Fan.IsLimit.lift hl (fun i => pr i ≫ f)
  have hlf : ∀ (f : G ⟶ G) (i : Fin j), lf f ≫ pr i = pr i ≫ f :=
    fun f i => Fan.IsLimit.fac hl _ i
  have hlf' : ∀ (f : G ⟶ G) (i : Fin j) {Z : Over S} (h : G ⟶ Z),
      lf f ≫ pr i ≫ h = pr i ≫ f ≫ h := by
    intro f i Z h
    rw [← Category.assoc, hlf, Category.assoc]
  have hone : lf (𝟙 G) = 𝟙 G' := hext _ _ (fun i => by rw [hlf]; simp)
  have hcomp : ∀ f g : G ⟶ G, lf (f ≫ g) = lf f ≫ lf g := fun f g =>
    hext _ _ (fun i => by simp only [Category.assoc, hlf, hlf'])
  have hmon : ∀ f : G ⟶ G, IsMonHom f → IsMonHom (lf f) := by
    intro f hf
    constructor
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.one_hom]
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

  have hadd : ∀ f g : G ⟶ G, lf (lift f g ≫ μ) = lift (lf f) (lf g) ≫ μ := by
    intro f g
    refine hext _ _ (fun i => ?_)
    simp only [Category.assoc, hlf, IsMonHom.mul_hom, comp_lift_assoc, lift_map_assoc]
  refine ⟨fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.map_one, hone],
      fun a b => by
        try dsimp only
        rw [r.map_mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.map_add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩,
    fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.one, hone],
      fun a b => by
        try dsimp only
        rw [r.mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecBGenerates
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndivisibleSection

theorem exists_secBGenerates : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) (D : DegData R I), ∃ b : D.toPre.SecB 1 0, SecBGenerates (D := D) 1 0 b :=
  fun hS _ _ _ _ _ _ D => exists_generator D.toPre hS

end GlobalTheory.IndivisibleSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpBijFOfAdmissibleBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem expBijF_of_admissible_base : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
      [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), Geo.Tor.ExpBijF U.toUnifPre :=
  fun hL _ R _ _ I _ D A G _ _ U => expansion_bijective_over_fields hL.globalFns R I D A G U

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtDvdOfSecIsMul
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace WeightDvd

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem appLE_dvd {P T : Scheme.{0}} [IsAffine P] (p : P ⟶ T) (W : T.Opens) (e : ⊤ ≤ p ⁻¹ᵁ W) (u v : Γ(T, W))
    (h : ∀ w ∈ W, gs (𝟙 T) w W u ∣ gs (𝟙 T) w W v) : (p.appLE W ⊤ e).hom u ∣ (p.appLE W ⊤ e).hom v := by
  rw [← Ideal.mem_span_singleton, (isAffineOpen_top P).mem_ideal_iff]
  intro z hz
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have k : ∀ c : Γ(T, W), (P.presheaf.germ ⊤ z hz).hom ((p.appLE W ⊤ e).hom c) =
      (p.stalkMap z).hom (gs (𝟙 T) (p z) W c) := fun c =>
    ((gs_eq (𝟙 P) z ⊤ hz _).symm.trans (gs_appLE p W ⊤ e (𝟙 P) z hz c)).trans
      ((by rw [Category.id_comp] : gs (𝟙 P ≫ p) z W c = gs p z W c).trans (gs_stalkMap p z W (e hz) c))
  have := map_dvd (p.stalkMap z).hom (h (p z) (e hz))
  rw [← k, ← k] at this
  exact this

theorem dvd_of_sum {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (s : Finset X) (a : Γ(Y.left, V)) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      gs (snd (splitTorus S X) Y).left w V a ∣
        ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ)) :
    ∀ χ ∈ s, a ∣ h χ := by
  intro χ₀ hχ₀
  have k : ∀ (w : (splitTorus S X ⊗ Y).left) (hw : (snd (splitTorus S X) Y).left w ∈ V) (c : Γ(Y.left, V)),
      gs (𝟙 _) w ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) (((snd (splitTorus S X) Y).left.app V).hom c) =
        gs (snd (splitTorus S X) Y).left w V c := fun w hw c =>
    (gs_pull (𝟙 _) _ w V hw c).trans (by rw [Category.id_comp])
  have H := appLE_dvd (TorusInj.pt (X := X) hV) _ (TorusInj.pt_le hV) (((snd (splitTorus S X) Y).left.app V).hom a)
    (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) fun w hw => by
      rw [k w hw, gs_fsum (𝟙 _) w _ hw]
      refine (hs w hw).trans (dvd_of_eq (Finset.sum_congr rfl fun χ _ => ?_))
      rw [gs_mul (𝟙 _) w _ hw, k w hw, gs_res (𝟙 _) w _ hw]
  have H' : TorusInj.ev hV (((snd (splitTorus S X) Y).left.app V).hom a) ∣ TorusInj.ev hV
      (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) :=
    map_dvd (Scheme.ΓSpecIso (TorusInj.GA (X := X) (V := V))).hom.hom H
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, TorusInj.ev_chi, TorusInj.ev_snd, AddMonoidAlgebra.single_mul_single,
    add_zero, _root_.one_mul] at H'
  obtain ⟨g, hg⟩ := H'
  have hc := congrArg (fun f => f.coeff χ₀) hg
  rw [TorusInj.coeff_sum_single X s _ χ₀ hχ₀] at hc
  refine ⟨g.coeff χ₀, hc.trans ?_⟩
  simp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem val_act (β : D.toPre.X) (w : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left) {J}
    (hJ : Good D.toPre.P.L w J) :
    (val (tG U e β) (WeightPf.act (U.gt e)).left w J).val =
      gs (𝟙 _) w ⊤ (TorusInj.chiP D.toPre.X (thickObj R I e G) β) *
        (val (tG U e β) (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w J).val := by
  have E := val_corr hJ ((U.gt e).t_weight β) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at E
  refine (congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  have hm := hJ.mem (L := D.toPre.P.L) (K := PEmpty) (Y := (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left)
    PEmpty.elim (𝟙 _)
  exact (congrArg Units.val (gm_rp₁ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ _ _ hm
    (charUnit _ D.toPre.X β))).trans ((gs_unit _ w ⊤ trivial _).symm.trans
      ((gs_pull (𝟙 _) (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ trivial _).trans
        (by rw [Category.id_comp])).symm)

theorem dvd_on_group (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hσ : SecIsMul G.hom r σ τ)
    (hE : U.ExpandsAt e k σ f) (α : D.toPre.X) (y : (thickObj R I e G).left) (J) (hJ : Good D.toPre.P.L y J) :
    cst (pGl U e ≫ D.toPre.P.A.hom) y r ∣ sval (f α) (pGl U e) y J := by
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  by_cases hα : α ∉ S
  · have := (hS _ (𝟙 _) y J hJ).1 α hα
    rw [Category.id_comp] at this
    rw [this]
    exact dvd_zero _
  push Not at hα
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (pGl U e ≫ D.toPre.famφB β a)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (Oφl U e β a)
  have hy : y ∈ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) :=
    mem_finf S _ _ fun β _ => ⟨hJ.mem (D.toPre.famφB β) (pGl U e), Set.mem_iInter.2 fun a => hJ _⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ := ((thickObj R I e G).left.isBasis_affineOpens).exists_subset_of_mem_open hy
    (S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β))).2
  have hVW' : V ≤ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) := hVW
  have hVf : ∀ β ∈ S, V ≤ pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_left)
  have hVt : ∀ β ∈ S, V ≤ LB.wchart D.toPre.P.L (Oφl U e β) (jt β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_right)
  have ex : ∀ β ∈ S, ∃ c : Γ((thickObj R I e G).left, V), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (thickObj R I e G).left) (z : Z),
      ρ z ∈ V → gs ρ z V c = gs (ρ ≫ pGl U e) z (LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β)) ((f β).f (jf β)) *
        (gm ρ z (LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) ((tG U e β).s (jt β))).val := fun β hβ =>
    ⟨((pGl U e).appLE _ V (hVf β hβ)).hom ((f β).f (jf β)) * (res (hVt β hβ) ((tG U e β).s (jt β))).val,
      fun Z ρ z hz => (gs_mul ρ z V hz _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ z hz _)
        ((gs_unit ρ z V hz _).trans (congrArg Units.val (gm_res ρ z _ hz _))))⟩
  choose! c hc using ex
  have hpG := WeightPf.act_left_pG (U.gt e)
  have hb : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := dvd_of_sum D.toPre.X (thickObj R I e G) hV S (constFn (pGl U e ≫ D.toPre.P.A.hom) V r) c (fun w hw => by
    choose d hd using fun ψ : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ w)
    let J₂ : ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun ψ =>
      if ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ)) then
        J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ) else d ψ
    have hJ₂ : Good D.toPre.P.L w J₂ := fun ψ => by
      by_cases h : ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hd ψ
    have eJ : ∀ φ : (thickObj R I e G).left ⟶ D.toPre.P.A.left,
        φ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w) ∈ D.toPre.P.L.U (J φ) →
        J₂ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ) = J φ := fun φ h => by
      have e₁ : (WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫
          (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ = φ := by
        rw [← Category.assoc, WeightPf.sec_left_snd, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (fGl I G e ((WeightPf.act (U.gt e)).left w))
    have E := (hS _ (WeightPf.act (U.gt e)).left w J₂ hJ₂).2 jL hL
    have hs : sv U k σ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL =
        cst (((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom) w r *
          sv U k τ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL :=
      secIsMul_gs hσ _ w (fun _ => jL) (Set.mem_iInter.2 fun _ => hL)
    have e₂ : ((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom =
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ pGl U e ≫ D.toPre.P.A.hom := by
      rw [Category.assoc, ← hb, ← Category.assoc, hpG, Category.assoc]
    rw [hs, e₂, mul_left_comm] at E
    refine (dvd_of_eq (gs_constFn _ V _ w hw r)).trans ((Dvd.intro _ E).trans
      (dvd_of_eq (Finset.sum_congr rfl fun β hβ => ?_)))
    rw [hc β hβ _ _ w hw, val_act U e β w hJ₂, mul_left_comm, hpG,
      sval_of (f β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (tG U e β) _ w J₂ (jt β) (fun a => eJ _ (Set.mem_iInter.1 (hVt β hβ hw) a))]) α hα
  obtain ⟨g, hg⟩ := H
  have E := hc α hα _ (𝟙 _) y hyV
  rw [hg, gs_mul (𝟙 _) y V hyV, gs_constFn _ V (𝟙 _) y hyV, Category.id_comp, Category.id_comp] at E
  exact (Units.dvd_mul_right).1 (Dvd.intro _ E)

end WeightDvd

theorem expandsAt_dvd_of_secIsMul : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom r σ τ → U.ExpandsAt e k σ f → ∀ (α : D.toPre.X) (x : (thickObj R I e D.toPre.P.A).left) (J), Geo.Tor.Good D.toPre.P.L x J → Geo.Tor.cst ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) x r ∣ Geo.Tor.sval (f α) (fstG I e D.toPre.P.A).left x J := by
  intro R _ _ I D A G _ _ U e k r σ τ f hσ hE α x J hJ
  have := (U.gt e).q_flat
  obtain ⟨y, rfl⟩ := (U.gt e).q_surj.surj x
  choose J' hJ' using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have H := WeightDvd.dvd_on_group U e k r σ τ f hσ hE α y J' hJ'
  have hm := hJ.mem (D.toPre.famφB α) (fstG I e D.toPre.P.A).left
  have e₁ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left (fstG I e D.toPre.P.A).left y _ hm
    ((f α).f fun a => J ((fstG I e D.toPre.P.A).left ≫ D.toPre.famφB α a))
  have e₂ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) y ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₃ := sec_trans (f α) (pGl U e) y hm (Good.mem hJ' (D.toPre.famφB α) (pGl U e))
  refine dvd_descend (U.gt e).q.left y ?_
  exact (dvd_of_eq e₂.symm).trans ((H.mul_left _).trans (dvd_of_eq (e₃.symm.trans e₁)))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isPowGrp_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), ∃ p' : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j, ∀ i, p'.pr i = (Over.pullback f).map (p.pr i) := by
  intro S S' f G' G _ _ j p
  refine ⟨⟨fun i => (Over.pullback f).map (p.pr i), fun i => ?_, ?_⟩, fun i => rfl⟩
  · haveI := p.hom i
    infer_instance
  · exact isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim

end GlobalTheory
end

