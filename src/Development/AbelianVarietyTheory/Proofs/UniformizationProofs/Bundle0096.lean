module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfProportional
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjUniq

theorem hom_eq_of_proportional : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (T : Scheme.{0}) (φ ψ : T ⟶ Z), φ ≫ f = ψ ≫ f → (∀ z k k' i i', φ z ∈ H.U k → ψ z ∈ H.U k' → gs φ z (H.U k) ((s i).f k) * gs ψ z (H.U k') ((s i').f k') = gs φ z (H.U k) ((s i').f k) * gs ψ z (H.U k') ((s i).f k')) → φ = ψ := by
  intro R _ Z f H n s hH hs T φ ψ hf h
  choose r hr hsurj using fun i => (hs.2 i).2
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
    obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show ψ z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk] at hz
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i') ψ z hk'] at hi'
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk']
    have hu := hz.mul hi'
    rw [h z k k' i i' hk hk'] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm
    fun i z hz a => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (φ z)
  obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j => by
    have e₁ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) φ z hz hk
    have e₂ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) ψ z hz' hk'
    have u₁ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk).1 hz
    have u₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk').1 hz'
    have e := h z k k' j i hk hk'
    rw [e₁, e₂] at e
    refine (u₁.mul u₂).mul_right_cancel ?_
    linear_combination e
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, MapUniq.gs_cst f φ z _ hz, MapUniq.gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add (f := _), gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.ProjUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfThickeningPoints
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isProper_tensorObj_over {S : Scheme.{0}} {Z B : Over S} (hZ : IsProper Z.hom)
    (hB : IsProper B.hom) : IsProper (Z ⊗ B).hom := by
  simp only [Over.tensorObj_hom]
  infer_instance

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma hom_ext_of_thickenings (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X B : Over (Spec (CommRingCat.of V))} [IsProper X.hom]
    [IsProper B.hom] (f g : X ⟶ B)
    (h : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (t : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ X), t ≫ f = t ≫ g) :
    f = g := by
  refine _root_.GlobalTheory.hom_eq_of_thickenings_of_isProper V (IsLocalRing.maximalIdeal V) ?_ X B f g ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exact bot_ne_top
  · intro e
    exact congrArg Over.Hom.left (h e (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj V _ e X) (_root_.ReciprocityTheory.ChartRestriction.G.Out.fstG _ e X))


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.grpObj_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) (Y (e + 1)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) [IsProper B.hom], (∀ e, IsPullback (b e) (Y e).hom B.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) → ∃ _ : GrpObj B, (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) B (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V _ e) (b e)) ∧ ((∀ e, IsCommMonObj (Y e)) → IsCommMonObj B) := by
  intro V _ _ _ Y _ β _ B b _ hpb _ mu io un hY
  have lft : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B),
      ∃ x : T ⟶ Y e, u.left = x.left ≫ b e := by
    intro e T u
    refine ⟨Over.homMk ((hpb e).lift u.left T.hom (by simpa using Over.w u))
      ((hpb e).lift_snd _ _ _), ?_⟩
    simp
  have hmul : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u v : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x y : T ⟶ Y e),
      u.left = x.left ≫ b e → v.left = y.left ≫ b e → (lift u v ≫ mu).left = (x * y).left ≫ b e :=
    fun e T u v x y hu hv => (hY e T x y u v hu hv).1
  have hinv : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x : T ⟶ Y e),
      u.left = x.left ≫ b e → (u ≫ io).left = x⁻¹.left ≫ b e :=
    fun e T u x hu => (hY e T x x u u hu hu).2.1
  have hone : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))),
      (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left =
        (1 : T ⟶ Y e).left ≫ b e := by
    intro e T
    obtain ⟨u, hu⟩ : ∃ u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B,
        u.left = (1 : T ⟶ Y e).left ≫ b e :=
      ⟨Over.homMk ((1 : T ⟶ Y e).left ≫ b e) (by
        simp only [Over.mk_hom, Category.assoc, (hpb e).w]
        rw [← Category.assoc, Over.w]), rfl⟩
    exact (hY e T 1 1 u u hu hu).2.2
  have hB2 : IsProper (B ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over inferInstance inferInstance
  have hB3 : IsProper ((B ⊗ B) ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over hB2 inferInstance
  have hB1 : IsProper (B ⊗ 𝟙_ _).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over inferInstance (by simp; infer_instance)
  have hB1' : IsProper (𝟙_ _ ⊗ B).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over (by simp; infer_instance) inferInstance
  letI : MonObj B :=
    { one := un
      mul := mu
      one_mul := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ fst _ _) (toUnit _)]
        simp only [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        ext
        rw [hmul e T _ _ 1 x (hone e T) hx, _root_.one_mul, hx]
      mul_one := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ snd _ _) (toUnit _)]
        simp only [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        ext
        rw [hmul e T _ _ x 1 hx (hone e T), _root_.mul_one, hx]
      mul_assoc := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (lift (t ≫ fst _ _ ≫ fst _ _) (t ≫ fst _ _ ≫ snd _ _)) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;>
            [apply CartesianMonoidalCategory.hom_ext; skip] <;> simp
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        ext
        rw [hmul e T _ _ (x * y) z (hmul e T _ _ x y hx hy) hz,
          hmul e T _ _ x (y * z) hx (hmul e T _ _ y z hy hz), _root_.mul_assoc] }
  letI : GrpObj B :=
    { inv := io
      left_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x⁻¹ x (hinv e T t x hx) hx).trans ?_
        rw [inv_mul_cancel, ← hone e T]
        rfl
      right_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x x⁻¹ hx (hinv e T t x hx)).trans ?_
        rw [mul_inv_cancel, ← hone e T]
        rfl }
  refine ⟨this, fun e => ⟨hpb e, fun T x y x₀ y₀ hx hy => hmul e T x₀ y₀ x y hx hy⟩, fun hc => ?_⟩
  exact
    { mul_comm := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht]
        simp only [lift_braiding_hom_assoc]
        ext
        have := hc e
        refine (hmul e T _ _ y x hy hx).trans ?_
        rw [_root_.mul_comm]
        exact (hmul e T _ _ x y hx hy).symm }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TrivTwist

variable {X Y : Scheme.{0}}

theorem gm_pull_g (A : LB X) (f : Y ⟶ X) (y : Y) (i j : A.ι) (hi : f y ∈ A.U i) (hj : f y ∈ A.U j) :
    gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j)) ((A.pull f).g (fun _ => i) (fun _ => j)) =
      gm f y (A.U i ⊓ A.U j) (A.g i j) := by
  have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (A.g i j))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) f y (A.U i ⊓ A.U j) ⟨hi, hj⟩ _).trans (by rw [Category.id_comp]))

theorem isGen_pull_iff (A : LB X) (f : Y ⟶ X) (t : LB.Gen (A.pull f)) :
    t.IsGen ↔ ∀ (i j : A.ι) (y : Y), f y ∈ A.U i → f y ∈ A.U j →
      gm (𝟙 Y) y ((A.pull f).U (fun _ => i)) (t.s (fun _ => i)) =
        gm f y (A.U i ⊓ A.U j) (A.g i j) * gm (𝟙 Y) y ((A.pull f).U (fun _ => j)) (t.s (fun _ => j)) := by
  constructor
  · intro h i j y hi hj
    have hp : (𝟙 Y : Y ⟶ Y) y ∈ (A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j) :=
      ⟨mem_pull.2 hi, mem_pull.2 hj⟩
    have := congrArg (gm (𝟙 Y) y ((A.pull f).U (fun _ => i) ⊓ (A.pull f).U (fun _ => j))) (h (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res _ y _ hp, gm_res _ y _ hp, gm_pull_g A f y i j hi hj] at this
    exact this
  · intro h I J
    refine unit_ext fun y hy => ?_
    have hi := mem_pull.1 hy.1
    have hj := mem_pull.1 hy.2
    have := h (I PUnit.unit) (J PUnit.unit) y hi hj
    rw [← gm_pull_g A f y _ _ hi hj] at this
    exact (gm_res _ y _ hy _).trans (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hy _))).symm)

theorem gm_div_g_one (M N : LB X) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) (y : Y) (p q : M.ι × N.ι)
    (hp : f y ∈ (LB.div M N).U p) (hq : f y ∈ (LB.div M N).U q) :
    gm f y ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) = gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) := by
  show gm f y _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  have hm : f y ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res f y _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm _)))).trans ?_)
  rw [hN, map_one, inv_one, _root_.mul_one]

theorem triv_pull_div_iff (M N : LB X) (hc : ∀ x : X, ∃ k, x ∈ N.U k) (hN : ∀ i j, N.g i j = 1) (f : Y ⟶ X) :
    Triv (M.pull f) ↔ Triv ((LB.div M N).pull f) := by
  have hle : ∀ p : M.ι × N.ι, ((LB.div M N).pull f).U (fun _ => p) ≤ (M.pull f).U (fun _ => p.1) :=
    fun p y hy => mem_pull.2 (mem_pull.1 hy).1
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun P => res (hle (P PUnit.unit)) (t.s (fun _ => (P PUnit.unit).1))⟩, (isGen_pull_iff _ f _).2 ?_⟩
    intro p q y hp hq
    rw [gm_div_g_one M N hN f y p q hp hq]
    exact (gm_res (𝟙 Y) y (hle p) (mem_pull.2 hp) _).trans (((isGen_pull_iff M f t).1 ht p.1 q.1 y hp.1 hq.1).trans
      (congrArg _ (gm_res (𝟙 Y) y (hle q) (mem_pull.2 hq) _).symm))
  · rintro ⟨c, hc'⟩
    have H : ∀ (p q : M.ι × N.ι) (y : Y), f y ∈ (LB.div M N).U p → f y ∈ (LB.div M N).U q →
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => p)) (c.s (fun _ => p)) =
          gm f y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
            gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => q)) (c.s (fun _ => q)) := fun p q y hp hq => by
      rw [← gm_div_g_one M N hN f y p q hp hq]
      exact (isGen_pull_iff _ f c).1 hc' p q y hp hq
    have glue : ∀ i : M.ι, ∃ s : Γ(Y, (M.pull f).U (fun _ => i))ˣ, ∀ k : N.ι,
        res (hle (i, k)) s = c.s (fun _ => (i, k)) := fun i =>
      glue_unit _ (fun k => ((LB.div M N).pull f).U (fun _ => (i, k))) (fun k => hle (i, k))
        (fun y hy => by
          obtain ⟨k, hk⟩ := hc (f y)
          exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.2 ⟨mem_pull.1 hy, hk⟩⟩)
        (fun k => c.s (fun _ => (i, k))) (fun k k' y hy => by
          have h₁ := mem_pull.1 hy.1
          have h₂ := mem_pull.1 hy.2
          have e := mul_eq_right.1 (H (i, k) (i, k) y h₁ h₁).symm
          have e' := H (i, k) (i, k') y h₁ h₂
          exact e'.trans ((congrArg (· * _) e).trans (_root_.one_mul _)))
    choose s hs using glue
    refine ⟨⟨fun I => s (I PUnit.unit)⟩, (isGen_pull_iff M f _).2 fun i j y hi hj => ?_⟩
    obtain ⟨k, hk⟩ := hc (f y)
    have v : ∀ a, f y ∈ M.U a → gm (𝟙 Y) y ((M.pull f).U (fun _ => a)) (s a) =
        gm (𝟙 Y) y (((LB.div M N).pull f).U (fun _ => (a, k))) (c.s (fun _ => (a, k))) := fun a ha =>
      (gm_res (𝟙 Y) y (hle (a, k)) (mem_pull.2 ⟨ha, hk⟩) _).symm.trans (congrArg _ (hs a k))
    exact (v i hi).trans ((H (i, k) (j, k) y ⟨hi, hk⟩ ⟨hj, hk⟩).trans (congrArg _ (v j hj).symm))

theorem linComb_pw_zero_g (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j : K → L.ι) :
    (LB.LinComb (pw L 0) φ ε).g i j = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  have e : (pw L 0).g (i k) (j k) = 1 := zpow_zero _
  exact (congrArg (· ^ ε k) ((congrArg _ ((congrArg _ e).trans (map_one _))).trans (map_one _))).trans (one_zpow _)

theorem inK_iff_trivial_twist : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → (pw L 0).IsLB ∧ (∃ u : LB.Gen (abelian₂ B (pw L 0)), u.IsGen) ∧ ∀ (O : LB B.left), O = pw L 0 → ∀ (T : Over S) (x : T ⟶ B), InK B L x ↔ (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) := by
  intro S B _ L hL
  refine ⟨isLB_pw hL 0, ⟨⟨fun _ => 1⟩, fun i j => ?_⟩, ?_⟩
  · exact (map_one _).trans
      ((congrArg₂ (· * ·) (linComb_pw_zero_g L _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm
  · rintro O rfl T x
    refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
    refine triv_pull_div_iff _ _ (fun y => ?_) (fun i j => linComb_pw_zero_g L _ _ i j) _
    obtain ⟨k, hk⟩ := exists_chart (isLB_pw hL 0) ((snd T B).left y)
    exact ⟨fun _ => k, mem_pull.2 hk⟩

end GlobalTheory.UU.TrivTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKSubgroupTwist
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.KTwist

open GlobalTheory.KerPow

section General

variable {X Y B : Scheme.{0}} {N N' : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem gen_div_of_gen {M M' : LB Y} (h : ∃ t : LB.Gen M, t.IsGen) (h' : ∃ t : LB.Gen M', t.IsGen) :
    ∃ t : LB.Gen (LB.div M M'), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  refine ⟨⟨fun p => res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
    (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : M.ι × M'.ι, y ∈ M.U p.1 ⊓ M'.U p.2 → gm (𝟙 Y) y (M.U p.1 ⊓ M'.U p.2)
      (res (inf_le_left : M.U p.1 ⊓ M'.U p.2 ≤ _) (t.s p.1) *
        (res (inf_le_right : M.U p.1 ⊓ M'.U p.2 ≤ _) (t'.s p.2))⁻¹) =
      gm (𝟙 Y) y _ (t.s p.1) * (gm (𝟙 Y) y _ (t'.s p.2))⁻¹ := fun p hp =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))
  have tr : ∀ {A : LB Y} {a : LB.Gen A}, a.IsGen → ∀ i j, y ∈ A.U i ⊓ A.U j →
      gm (𝟙 Y) y _ (a.s i) = gm (𝟙 Y) y _ (A.g i j) * gm (𝟙 Y) y _ (a.s j) := fun ha i j hm =>
    (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ha i j)).trans
      ((map_mul _ _ _).trans (congrArg _ (gm_res _ y _ hm _))))
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div M' M (𝟙 Y) y p q hy) ((gm_res _ y _ hy _).trans (v q hy.2)))).symm)
  rw [tr ht p.1 q.1 ⟨hy.1.1, hy.2.1⟩, tr ht' p.2 q.2 ⟨hy.1.2, hy.2.2⟩, mul_inv, _root_.mul_mul_mul_comm]

theorem hasGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) (h' : HasGen N' φ ε) :
    HasGen (LB.div N N') φ ε ↔ HasGen N φ ε := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨u', hu'⟩ := h'
    obtain ⟨u, hu, -⟩ := DescendedPrincipal.exists_gen_mul_div hN hN' u' hu' q hq
    exact ⟨u, hu⟩
  · intro h
    obtain ⟨w, hw⟩ := gen_div_of_gen h h'
    exact gen_chartPull (DescendedPrincipal.chartPullDiv N N' φ ε) w hw

theorem locGen_div_iff (hN : N.IsLB) (hN' : N'.IsLB) {π : Y ⟶ B} (h' : LocGen N' π φ ε) :
    LocGen (LB.div N N') π φ ε ↔ LocGen N π φ ε := by
  have shrink : ∀ {A : LB X} {V W : B.Opens}, W ≤ V → HasGen A (fun k => (π ⁻¹ᵁ V).ι ≫ φ k) ε →
      HasGen A (fun k => (π ⁻¹ᵁ W).ι ≫ φ k) ε := fun {A V W} hle t =>
    t.pull (Y.homOfLE (show π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V from fun _ h => hle h))
      (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  constructor <;> intro H p <;> obtain ⟨V, hV, t⟩ := H p <;> obtain ⟨V', hV', t'⟩ := h' p
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).1 (shrink inf_le_left t)⟩
  · exact ⟨V ⊓ V', ⟨hV, hV'⟩, (hasGen_div_iff hN hN' (shrink inf_le_right t')).2 (shrink inf_le_left t)⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S}

theorem inK_div_iff {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) {x : T ⟶ B} (hx : InK B O x) :
    InK B (LB.div L O) x ↔ InK B L x :=
  (inK_iff_locGen x).trans ((locGen_div_iff hL hO ((inK_iff_locGen x).1 hx)).trans (inK_iff_locGen x).symm)

theorem inK_of_lam [IsCommMonObj B] {O : LB B.left} (hO : O.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen)
    (x : T ⟶ B) : InK B O x := by
  have H₀ : HasGen O (PrimCocycle.lamφ B) PrimCocycle.lamε := hu
  have H₁ : LocGen O (fst T B).left
      (fun I => (lift (fst T B ≫ x) (snd T B)).left ≫ PrimCocycle.lamφ B I) PrimCocycle.lamε := fun _ =>
    ⟨⊤, trivial, H₀.pull (((fst T B).left ⁻¹ᵁ ⊤).ι ≫ (lift (fst T B ≫ x) (snd T B)).left)
      fun _ => Category.assoc _ _ _⟩
  have H₂ := BoxKernel.locGen_base hO (fst T B).left (K := Fin 2) ![x.left, (1 : T ⟶ B).left] ![-1, 1]
  refine (inK_iff_locGen x).2 (H₁.comb hO H₂ fun U _ h => ?_)
  rw [PrimCocycle.prod_lam (fst T B ≫ x) (snd T B) h, Fin.prod_univ_two, Fin.prod_univ_two]
  have e₁ : (fst T B).left ≫ (1 : T ⟶ B).left = (1 : T ⊗ B ⟶ B).left :=
    congrArg (fun q : T ⊗ B ⟶ B => q.left) (MonObj.comp_one (fst T B))
  show h (translPt B x).left * (h ((fst T B).left ≫ x.left))⁻¹ * (h (snd T B).left)⁻¹ * h (1 : T ⊗ B ⟶ B).left *
      (h ((fst T B).left ≫ x.left) ^ (-1 : ℤ) * h ((fst T B).left ≫ (1 : T ⟶ B).left) ^ (1 : ℤ))⁻¹ =
    h (translPt B x).left ^ (1 : ℤ) * h (snd T B).left ^ (-1 : ℤ)
  rw [e₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.UU.KTwist

namespace GlobalTheory.UU

end GlobalTheory.UU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem nonempty_tq_pullback_comp {T S S' : Scheme.{0}} (r : T ⟶ S') (f : S' ⟶ S) {g : T ⟶ S} (h : g = r ≫ f)
    (G : Over S) [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ ((Over.pullback f).obj G) X) :
    Nonempty (TQ ((Over.pullback g).obj G) X) := by
  subst h
  obtain ⟨Q', -⟩ := exists_tq_baseChange _ _ _ X _ _ _
    ((isGrpPullback_of_iso (pullCompIso r f G)).comp (isGrpPullback_pullback _ r)) Q
  exact ⟨Q'⟩

theorem thick_zero_factor (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ r, thick V (IsLocalRing.maximalIdeal V) 0 = r ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (show IsLocalRing.maximalIdeal V ≤ IsLocalRing.maximalIdeal V ^ (0 + 1) by simp))), ?_⟩
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistThroughIsoStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endU_twist_of_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  first | exact @GlobalTheory.UT.TwistCompare.twist_through_iso | exact GlobalTheory.UT.TwistCompare.twist_through_iso | (intros; apply GlobalTheory.UT.TwistCompare.twist_through_iso <;> assumption)
end

