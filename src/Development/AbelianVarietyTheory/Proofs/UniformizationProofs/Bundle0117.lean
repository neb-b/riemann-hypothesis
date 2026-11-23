module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.TorsionCount

theorem card_torsion_points_unconditional :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) :=
  _root_.GlobalTheory.UU.TorsionCount.card_torsion_points GlobalTheory.laws_without_cohomology.1 GlobalTheory.laws_without_cohomology.2.1

end GlobalTheory.UU.TorsionCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBuStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle : GlobalFnsSt → ∀ (R : Type) [CommRing R] (T B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB (T ⊗ B).left, F.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ T), IsClosedImmersion j.left ∧ ∀ (T' : Over (Spec (CommRingCat.of R))) (x : T' ⟶ T), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (x ▷ B).left).pull ((fst T' B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  first | exact @GlobalTheory.TrivSubscheme.exists_closed_locTriv | exact GlobalTheory.TrivSubscheme.exists_closed_locTriv | (intros; apply GlobalTheory.TrivSubscheme.exists_closed_locTriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorOfCompatibleThickeningGenerators
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem exists_gen_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Gen (LB.LinComb L (φ' e) ε), (∀ e, (f e).IsGen) → (∀ e z J, Good L z J → val (f (e + 1)) (thickMap R I e Y) z J = val (f e) (𝟙 _) z J) → ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → val u (r ≫ pullback.fst Y.hom (thick R I e)) z J = val (f e) r z J := by
  intro R _ _ I hI Y hs hp W L K _ φ ε φ' hL hφ f hf hc
  obtain ⟨s, hsv⟩ := _root_.GlobalTheory.SecAlgLinComb.exists_sec_linComb R I hI Y hs hp W L K φ ε φ' hL hφ (fun e => genSec (f e) (hf e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (hc e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy _ _ _ hp
  have top : nonzeroLocus s = ⊤ :=
    eq_top_of_special_part R I (IsAdicComplete.le_jacobson_bot I) Y _ fun z => by
      choose J hJ using fun ψ : (thickObj R I 0 Y).left ⟶ W => exists_chart hL (ψ z)
      have h1 := hsv 0 _ (𝟙 _) z J hJ
      rw [Category.id_comp, sval_genSec _ _ _ z hJ] at h1
      refine (TwistZero.mem_nonzeroLocus_iff s (pullback.fst Y.hom (thick R I 0)) z hJ).2 ?_
      exact (congrArg IsUnit h1).mpr (Units.isUnit _)
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y.left) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul ((TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)))
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), fun e Z r z J hJ => Units.ext ?_⟩
  exact (gs_unit _ z _ (hJ.mem φ _) _).symm.trans ((hsv e Z r z J hJ).trans (sval_genSec _ _ r z hJ))

end GlobalTheory.Unif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

theorem gm_linCombIso {X Y Z : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    gm r z _ ((LB.linCombIso w φ ε).s p) =
      ∏ a, gm (r ≫ φ a) z ((LB.div M L).U (p.1 a, p.2 a)) (w.s (p.1 a, p.2 a)) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ M.U (p.1 a) ⊓ L.U (p.2 a) :=
    ⟨LB.wchart_le M φ p.1 a hz.1, LB.wchart_le L φ p.2 a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z ((LB.div M L).U (p.1 a, p.2 a)) hm _)

theorem exists_gen_of_iso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    (t : LB.Gen A) (ht : t.IsGen) : ∃ t' : LB.Gen B, t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : B.ι) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) (t'.s j) = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
  have tr : ∀ (y : Y) (j j' : B.ι) (i i' : A.ι), y ∈ B.U j → y ∈ B.U j' → y ∈ A.U i → y ∈ A.U i' →
      gm (𝟙 Y) y (B.U j ⊓ A.U i) (w.s (j, i)) * gm (𝟙 Y) y (A.U i) (t.s i) =
        gm (𝟙 Y) y _ (B.g j j') * (gm (𝟙 Y) y (B.U j' ⊓ A.U i') (w.s (j', i')) * gm (𝟙 Y) y (A.U i') (t.s i')) := by
    intro y j j' i i' hj hj' hi hi'
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ B.U j ⊓ A.U i ⊓ (B.U j' ⊓ A.U i') := ⟨⟨hj, hi⟩, hj', hi'⟩
    have hn : (𝟙 Y : Y ⟶ Y) y ∈ A.U i ⊓ A.U i' := ⟨hi, hi'⟩
    have e := (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (j, i) (j', i'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 Y) y (j, i) (j', i') hm) (gm_res _ y _ hm _))))
    have e' := (gm_res _ y _ hn _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht i i')).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res _ y _ hn _))))
    refine (congrArg₂ (· * ·) e e').trans ?_
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel_right]
    rfl
  have glue : ∀ j : B.ι, ∃ s : Γ(Y, B.U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) s = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
    intro j
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι), r z ∈ B.U j ⊓ A.U i →
        gm r z (B.U j ⊓ A.U i) (@id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) =
          gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := fun Z r z i h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res r z _ h _))
    obtain ⟨s, hs⟩ := glue_unit (B.U j) (fun i => B.U j ⊓ A.U i) (fun _ => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hA x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩)
      (fun i => @id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) (fun i i' x hx => by
        rw [v _ _ x i hx.1, v _ _ x i' hx.2, tr x j j i i' hx.1.1 hx.1.1 hx.1.2 hx.2.2, gm_self hB _ x hx.1.1,
          _root_.one_mul])
    refine ⟨s, fun Z r z i hj hi => ?_⟩
    have hm : r z ∈ B.U j ⊓ A.U i := ⟨hj, hi⟩
    exact (gm_res r z inf_le_left hm s).symm.trans ((congrArg (gm r z _) (hs i)).trans (v Z r z i hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z j i => hs j Z r z i⟩
  obtain ⟨i, hi⟩ := exists_chart hA y
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  exact (hs j _ _ y i hy.1 hi).trans ((tr y j j' i i hy.1 hy.2 hi hi).trans (congrArg _ (hs j' _ _ y i hy.2 hi).symm))

theorem triv_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : Triv A) :
    Triv B := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := t
  obtain ⟨t', ht', -⟩ := exists_gen_of_iso hA hB w hw t ht
  exact ⟨t', ht'⟩

variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_genWt_of_lbIso {G : Over S} [GrpObj G] (Q : TQ G X) {N N' : LB Q.B.left} (hN : N.IsLB) (hN' : N'.IsLB)
    (h : LBIso N N') {u : LB.Gen (N.pull Q.q.left)} {χ : X} (hu : Q.GenWt N u χ) :
    ∃ u' : LB.Gen (N'.pull Q.q.left), Q.GenWt N' u' χ := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨u', hu', hv⟩ := exists_gen_of_iso (pull_isLB hN _) (pull_isLB hN' _)
    (LB.linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _) u hu.1
  refine ⟨u', hu', fun J => isWt_of_gm _ _ fun Z t g z hz => ?_⟩
  have e : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := congrArg (·.left) (WtBundle.act_comp Q t g)
  have m : ∀ (M : LB Q.B.left) (I : PUnit → M.ι), g.left z ∈ (M.pull Q.q.left).U I →
      ((t ≫ Q.i) * g).left z ∈ (M.pull Q.q.left).U I := fun M I h =>
    (mem_pull (F := Q.q.left)).2 ((congrArg (fun a : Z.left ⟶ Q.B.left => a z ∈ M.U (I PUnit.unit)) e).mpr
      ((mem_pull (F := Q.q.left)).1 h))
  obtain ⟨I, hI⟩ := exists_chart (pull_isLB hN Q.q.left) (g.left z)
  have a₁ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) g.left z ⟨hz, hI⟩
  have a₂ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) ((t ≫ Q.i) * g).left z
    ⟨m _ _ hz, m _ _ hI⟩
  rw [e, ← a₁] at a₂
  rw [hv _ _ z J I (m _ _ hz) (m _ _ hI), hv _ _ z J I hz hI, WtBundle.gm_of_isWt (hu.2 I) t g z (m _ _ hI) hI,
    gm_charUnit, mul_left_comm]
  exact congrArg (fun x => _ * (x * _)) a₂

theorem exists_genWt_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (Q : TQ G X) (Q' : TQ G' X) {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) (hi : TorusCompat f F Q'.i Q.i) {β : Q'.B.left ⟶ Q.B.left}
    (hβ : Q'.q.left ≫ β = F ≫ Q.q.left) {N : LB Q.B.left} {u : LB.Gen (N.pull Q.q.left)} {χ : X}
    (hu : Q.GenWt N u χ) : ∃ u' : LB.Gen ((N.pull β).pull Q'.q.left), Q'.GenWt (N.pull β) u' χ :=
  let c := chartPullLinComb N β (K := PUnit) (fun _ => Q'.q.left) (fun _ => Q.q.left) (fun _ => 1) F fun _ => hβ
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).pull hF hi (c.le J)⟩

theorem exists_gen_comp {G : Over S} [GrpObj G] (Q : TQ G X) {Y : Scheme.{0}} (b : Q.B.left ⟶ Y) {O : LB Y}
    {u : LB.Gen ((O.pull b).pull Q.q.left)} {χ : X} (hu : Q.GenWt (O.pull b) u χ) :
    ∃ u' : LB.Gen (O.pull (Q.q.left ≫ b)), u'.IsGen ∧ ∀ j, IsWt Q.i _ (u'.s j).val χ :=
  let c := chartPullIn O (K := PUnit) (fun _ => b) (fun _ => 1) Q.q.left
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).res (c.le J)⟩

theorem psum_eq_lift {B T : Over S} [GrpObj B] [IsCommMonObj B] (x : Fin 2 → (T ⟶ B)) (I : Finset (Fin 2)) :
    (psum B x I).left = (lift (x 0) (x 1)).left ≫ (psum B (x2 B) I).left := by
  have e : (fun i => preHom (lift (x 0) (x 1)) (x2 B i)) = x := funext fun i => by
    fin_cases i
    exacts [lift_fst (x 0) (x 1), lift_snd (x 0) (x 1)]
  have := psum_hom (preHom (lift (x 0) (x 1))) (x2 B) I
  rw [e] at this
  exact congrArg (·.left) this.symm

theorem triv_lam_pull {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {f : S' ⟶ S} {b : B'.left ⟶ B.left} (hb : IsGrpPullback B' B f b) {O : LB B.left} {N : LB B'.left} (hO : O.IsLB)
    (hN : N.IsLB) (h : LBIso N (O.pull b)) (ht : Triv (abelian₂ B' N)) {T : Over S'} (U : Over.mk (T.hom ≫ f) ⟶ B ⊗ B) :
    Triv ((abelian₂ B O).pull U.left) := by
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → (T ⟶ B'), ∀ i, pushPt hb.1.w (x i) = U ≫ x2 B i :=
    ⟨fun i => Over.homMk (hb.1.lift (U ≫ x2 B i).left T.hom (Over.w (U ≫ x2 B i))) (hb.1.lift_snd _ _ _),
      fun i => Over.OverMorphism.ext (hb.1.lift_fst _ _ _)⟩
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := ht
  have t₁ : Triv (cubeLB B' x N) :=
    gen_chartPull (chartPullSame N (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (lift (x 0) (x 1)).left
      fun I => psum_eq_lift x I.down) t ht
  have l₁ : (cubeLB B' x N).IsLB := LB.isLB_linComb hN _ _
  have l₂ : (cubeLB B' x (O.pull b)).IsLB := LB.isLB_linComb (pull_isLB hO b) _ _
  have l₃ : (abelian₂ B O).IsLB := LB.isLB_linComb hO _ _
  have t₂ : Triv (cubeLB B' x (O.pull b)) := triv_of_lbIso l₁ l₂ ⟨_, DVR.linCombIso_isGen w hw _ _⟩ t₁
  have c : ChartPull (cubeLB B' x (O.pull b)) (abelian₂ B O) U.left :=
    chartPullLinComb O b (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) U.left
      fun I => psum_push hb x (x2 B) U hx I.down
  exact triv_of_lbIso l₂ (pull_isLB l₃ _)
    (LBIso.chartPull c (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B O) U.left U.left rfl) (GtBaseChange.lbIso_refl l₃)) t₂

theorem isGrpPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (e : ℕ) : IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem isLocalRing_quotient_pow (V : Type) [CommRing V] [IsLocalRing V] (e : ℕ) :
    IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isProjBy_of_relAmple {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) {L : LB B.left}
    (hL : L.IsLB) (h : RelAmple B L) : IsProjBy B.hom := by
  obtain ⟨d, -, n, σ, hσ⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  exact ⟨_, isLB_pw hL _, n, σ, hσ⟩

theorem triv_lam_of_levels (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {O : LB B.left} (hO : O.IsLB)
    (h : ∀ e, Triv ((abelian₂ B O).pull (fstG (IsLocalRing.maximalIdeal V) e (B ⊗ B)).left)) : Triv (abelian₂ B O) :=
  AbTriv.triv_of_forall_thick hG V (B ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB)
    (isProjBy_tensor V _ _ hp hp) _ (LB.isLB_linComb hO _ _) h

end GlobalTheory.WtTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidArcOfMono
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcRigidity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
  {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
  {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}

theorem core (hL : Laws) (hL₂ : Laws2) (hL₅ : Laws5)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c)
    (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ) (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ')
    (hs : y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF)
    (hs' : y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) :
    y = y' ∧ ∃ ψ : W.t.G ≅ W'.t.G,
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left)
        (τ : T ⟶ Sp (FractionRing (PowerSeries k))),
        g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ W.m.φ = g₁ ≫ Y.m.φ →
        g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
        g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) ∧
      ((∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ) := by
  letI := H.starRing
  obtain ⟨hD, hdat⟩ := GlobalTheory.arcWit_data_iso hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W'
  have hI : Ideal.span {(PowerSeries.X : PowerSeries k)} = IsLocalRing.maximalIdeal (PowerSeries k) :=
    PowerSeries.maximalIdeal_eq_span_X.symm
  obtain ⟨ψ, bc, hψ, hbc, hfst, hU⟩ := _root_.GlobalTheory.exists_iso_isPullUnif_of_isPullDeg hL hL₂ (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD
  have hx : ∀ (x : 𝓞 E) (z : W.P.D.toPre.X), hD.xe (x • z) = x • hD.xe z := by
    intro x z
    obtain ⟨z₀, rfl⟩ := W.e.surjective z
    rw [← W.e.map_smul, hdat.2.1, hdat.2.1]
    exact W'.e.map_smul x z₀
  have hB : ∀ x, (W.P.oD.onB.act x).left ≫
        (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) =
      (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
        (W'.P.oD.onB.act x).left := by
    intro x
    apply W'.spec.1.1.hom_ext
    · have h₁ : (W.P.oD.onB.act x).left ≫ W.φ = W.φ ≫ (a.oa.onB.act x).left := W.spec.2.2.2.1 x
      have h₂ : (W'.P.oD.onB.act x).left ≫ W'.φ = W'.φ ≫ (a.oa.onB.act x).left := W'.spec.2.2.2.1 x
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hdat.1).trans h₁)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hdat.1)))).symm
    · have e : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
          W'.P.D.toPre.P.A.hom = W.P.D.toPre.P.A.hom := by
        have w : hD.e.hom.left ≫ pullback.snd W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k))) =
          W.P.D.toPre.P.A.hom := Over.w hD.e.hom
        rw [Category.assoc, pullback.condition, ← Category.assoc, w, specOf_id, Category.comp_id]
      rw [Category.assoc, e, Over.w, Category.assoc, Over.w, e]
  have hlin := act_comm_of_isPullUnif_id hL.globalFns (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD bc hbc hU (𝓞 E) W'.P.oD W.P.oD W'.P.oA W.P.oA
    W'.t.act.toRingAct W.t.act.toRingAct W'.P.lin W.P.lin hx hB
  have hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x := by
    intro x
    have q := congrArg (fun z => z.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k)))) (hlin x)
    ext
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at q
    rw [hfst, ← Category.assoc, hfst] at q
    exact q
  have hlev := GlobalTheory.T.uniformisedArc_iso_matches_levelPoints hL hL₂ hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact
    y y' hy hy' hs hs'
  have hb : LBIso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hU.lg
    rw [← W.P.bundle, ← W'.P.bundle, ← hfst]
    exact ⟨w, hw⟩
  obtain ⟨e, h⟩ := ArcObj.point_eq hL W.m W'.m ψ hact hb _ y y' hy hy' (hs.trans hs'.symm) hlev
  exact ⟨e, ψ, h, arcWit_agree_of_isPullUnif E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact⟩

theorem exists_generic
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    {T : Scheme.{0}} (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (h₁ : g ≫ W.m.φ = g₁ ≫ Y.m.φ) :
    (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j ∧
      ∃ τ : T ⟶ Sp (FractionRing (PowerSeries k)), g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) := by
  have := ThetaShiftProofs.isOpenImmersion_jK_powerSeries k
  have q : (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j := by
    have h₁' : g ≫ W.m.cm.F = g₁ ≫ Y.m.cm.F := h₁
    rw [Category.assoc, ← W.m.cart.1.w, reassoc_of% h₁', Y.m.cart.1.w, Category.assoc]; rfl
  have hr : Set.range (g ≫ W.t.G.hom) ⊆ Set.range (jK (PowerSeries k)) := by
    rintro _ ⟨p, rfl⟩
    exact arcWit_mem_range_jK_of_mem_range_j E H D l Xo c k bF a O β Y χ W _
      ⟨(g₁ ≫ Y.oF.t.G.hom) p, congrArg (fun z => z p) q.symm⟩
  exact ⟨q, _, (IsOpenImmersion.lift_fac (jK (PowerSeries k)) _ hr).symm⟩

end ArcRigidity

theorem rigidArc_of_mono : Laws → Laws2 → Laws5 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β')
    (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
    y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' →
    y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) := by
  intro hL hL₂ hL₅ E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' y y' hy hy' hs hs'
  obtain ⟨e, ψ, h, hA⟩ := ArcRigidity.core hL hL₂ hL₅ W W' y y' hy hy' hs hs'
  refine ⟨e, fun hm => ⟨ψ, hA fun T g g₁ g₂ h₁ h₂ h₃ => ?_⟩⟩
  obtain ⟨q, τ, hτ⟩ := ArcRigidity.exists_generic W g g₁ h₁
  refine h T g g₁ g₂ τ hτ ?_ h₁ h₂ h₃
  rw [← cancel_mono Y.j, ← q, hτ, Category.assoc, Category.assoc, hy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifAssembly
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem unif_assembly : Laws → Laws2 → (AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegPre V) (U : PreU (IsLocalRing.maximalIdeal V) D A G), U.P = s.P ∧ U.gen = s.gen) → (AllPre fun {V} _ _ _ {_} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c := by
  intro h1 h2 hA hB V _ _ _ A G _ _ s
  obtain ⟨D, U, hP, hg⟩ := hA V A G s
  obtain ⟨D', U', hP', hg', hFE⟩ := hB V s.cdvr D A G U
  obtain ⟨U'', hM⟩ := _root_.GlobalTheory.UU.exists_unif_of_fe_one h1 h2 V s.cdvr D' A G U' hFE
  have e : U'.P = s.P := hP'.trans hP
  refine ⟨D', U'', ?_, ?_, ?_⟩
  · exact hM.LG.trans (by rw [e])
  · exact hM.gen.trans (hg'.trans hg)
  · exact hM.cub.trans (by rw [e])
end GlobalTheory.UU
end

