module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundlePointCarryingOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorProps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem mul_single_mul_apply (M N : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ) * N) i j = M i i₀ * N i₀ j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single i₀]
  · congr 1
    simp [Matrix.mul_apply, Matrix.single_apply]
  · intro b _ hb
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hb]
  · simp

theorem mul_single_apply' (M : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ)) i j = if j = i₀ then M i i₀ else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
  · by_cases h : j = i₀
    · subst h; simp
    · simp [Matrix.single_apply, Ne.symm h, h]
  · intro b _ hb
    simp [Matrix.single_apply, Ne.symm hb]
  · simp

theorem Tens.xe_xi (T : Tens D D' W) (i₀ : Fin r) (y : D.X) :
    T.xe (T.xi i₀ y) = Pi.single i₀ y := by
  simp [Tens.xi]

theorem Tens.xe_smul_xi (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (i₀ : Fin r) (y : D.X) (i : Fin r) :
    letI := T.mod s
    T.xe (a • T.xi i₀ y) i = TensO.mat s a i i₀ • y := by
  letI := T.mod s
  rw [Tens.xe_smul]
  simp only [Tens.xe_xi]
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem TensO.mat_star_idem_mul_binv {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀) * TensO.binv s) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 := by
  change TensO.mat s (star (TensO.idem s i₀)) * TensO.mat s (TensO.binv s) = _
  rw [TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) * ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one]

theorem TensO.mat_star_idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀)) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) := by
  rw [TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single]

theorem SymUnit.inv_col_ne {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    ∃ i, ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 := congrFun (congrFun (Units.mul_inv s.1) i₀) i₀
  rw [Matrix.mul_apply, Finset.sum_eq_zero (fun k _ => by rw [h k, mul_zero]), Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

theorem tens_factor_latt : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s;
    (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧
    Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧
    ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  intro R _ _ D D' r W T s i₀
  letI := T.mod s
  have key : ∀ y i, T.xe (star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) i =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ • y := by
    intro y i
    rw [← mul_smul, Tens.xe_smul_xi, TensO.mat_star_idem_mul_binv, mul_single_apply']
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    show T.xe (T.xi i₀ y) i₀ = y
    rw [Tens.xe_xi]; simp
  · intro z
    apply T.xe.injective
    funext i
    rw [Tens.xe_xi, Tens.xe_smul]
    show Pi.single (M := fun _ => D.X) i₀ (T.xe z i₀) i = _
    simp only [TensO.idem, TensO.ofMat, TensO.mat, Matrix.single_apply]
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  · intro y y' h
    obtain ⟨i, hi⟩ := SymUnit.inv_col_ne s i₀
    have h' := congrArg (fun z => T.xe z i) h
    simp only [key] at h'
    exact smul_right_injective D.X hi h'
  · intro z
    refine ⟨∑ j, (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ j • T.xe z j, ?_⟩
    apply T.xe.injective
    funext i
    rw [key, Tens.xe_smul, TensO.mat_star_idem, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_single_mul_apply, mul_smul]
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensAct

section General

variable {S : Scheme.{0}} {X Y Z G : Over S}

def preHom [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g h => MonObj.comp_mul f g h

theorem comp_prod_zpow [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) {K : Type} [Fintype K] (g : K → (Y ⟶ G)) (n : K → ℤ) :
    f ≫ (∏ j, g j ^ n j) = ∏ j, (f ≫ g j) ^ n j := by
  show preHom f (∏ j, g j ^ n j) = ∏ j, (preHom f (g j)) ^ n j
  rw [map_prod]
  simp only [map_zpow]

end General

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem hom_ext (T : Tens D D' W) {X} {f g : X ⟶ D'.P.A} (h : ∀ i, f ≫ T.pr i = g ≫ T.pr i) : f = g :=
  T.lim.hom_ext fun ⟨i⟩ => h i

theorem comp_act_pr (T : Tens D D' W) {X} (f : X ⟶ D'.P.A) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    f ≫ T.act a ≫ T.pr i = ∏ j, (f ≫ T.pr j) ^ a i j := by
  rw [Tens.act_pr, comp_prod_zpow]

theorem act_isMonHom (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (T.act a) := by
  haveI := T.pr_hom
  have h1 : ∀ {X} , (1 : X ⟶ D'.P.A) ≫ T.act a = 1 := by
    intro X
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr]
    simp [MonObj.one_comp]
  have h2 : ∀ {X} (f g : X ⟶ D'.P.A), (f * g) ≫ T.act a = (f ≫ T.act a) * (g ≫ T.act a) := by
    intro X f g
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr, MonObj.mul_comp, Category.assoc, Category.assoc, comp_act_pr, comp_act_pr,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [MonObj.mul_comp, mul_zpow]
  constructor
  · have := h1 (X := 𝟙_ _)
    simpa [Hom.one_def] using this
  · have := h2 (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

theorem act_one (T : Tens D D' W) : T.act 1 = 𝟙 _ := by
  refine hom_ext T fun i => ?_
  rw [Tens.act_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, zpow_zero]
  · simp

theorem act_mul (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) : T.act (a * b) = T.act b ≫ T.act a := by
  refine hom_ext T fun i => ?_
  rw [Category.assoc, comp_act_pr, Tens.act_pr]
  simp only [Tens.act_pr, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : ∀ (s : Finset (Fin r)) (n : Fin r → ℤ), T.pr k ^ (∑ j ∈ s, n j) = ∏ j ∈ s, T.pr k ^ n j := by
    intro s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]
  rw [this]
  simp only [mul_comm]

theorem act_add (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) :
    T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  haveI := T.pr_hom
  show _ = T.act a * T.act b
  refine hom_ext T fun i => ?_
  rw [MonObj.mul_comp]
  simp only [Tens.act_pr, Matrix.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem act_ring : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧
      ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) :=
  fun _ _ _ _ _ _ _ T => ⟨act_isMonHom T, act_one T, act_mul T, act_add T⟩

end GlobalTheory.Mum.TensAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenPullbackToSelfProductSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem surjective_U_hom {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} (hπ : Surjective π)
    {G' : Over S} [GrpObj G'] (N : Near π G') : Surjective N.U.hom := by
  have := N.smooth
  obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
  let e : S ⟶ G'.left := (1 : Over.mk (𝟙 S) ⟶ G').left
  have he : e ≫ G'.hom = 𝟙 S := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  have hes : G'.hom (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨z, hz⟩ : e s ∈ Set.range N.u := N.all _ (by rw [hes]; exact hs)
  have hzs : pullback.snd N.U.hom π z = s := by
    rw [← N.u_over, Scheme.Hom.comp_apply, hz, hes]
  have hc : closedPoint R ∈ Set.range N.U.hom := ⟨pullback.fst N.U.hom π z, by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hzs, hs]⟩
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (IsLocalRing.specializes_closedPoint x) hc⟩

theorem surjective_UT_hom : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π →
    ∀ (G' : Over S) [GrpObj G'] (N : Near π G'), Surjective (Desc.UT N).hom := by
  intro R _ _ S π hπ G' _ N
  have := surjective_U_hom hπ N
  exact inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))

end GlobalTheory.Mum.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIntegralFlagModelOfSmoothCoefficientFiel
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

theorem nonempty_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → PushInvertible Y.t.G Y.t.PP.L → Nonempty (GlobalTheory.FlagMod.FlagModel Y) := by
  intro E _ _ _ H Dw l Xo c Y _ hP
  obtain ⟨p⟩ := LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_atlas E H Dw l Xo c Y p hP
  have := A.fin
  obtain ⟨Z, π, g, κ, h1, h2, h3, h4, h5, h6⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_properFlag c.F Y.X Y.s (E →+* ℂ) Dw.mult A.N A.B A.V A.alpha A.cv A.Dv Y.proj Y.normal (_root_.GlobalTheory.FlagMod.FieldFlag.atlas_isCover E H Dw l Xo c Y p A) A.cov
  have hZ : Cells A π g κ := ⟨h1, h2, h3, h5, h6⟩
  have := h4
  have ht := _root_.GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular E H Dw l Xo c Y p A Z π g κ hZ
  have huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z), (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂ := by
    intro S' _ _ P₁ z₁ z₂ e₁ e₂
    refine _root_.GlobalTheory.FlagMod.FieldFlag.hom_ext_of_localization_atPrime S' Z z₁ z₂ fun q => ?_
    obtain ⟨P', hP'⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.AtPrime q.asIdeal)) P₁
    have l₁ := e₁.frMap hP'
    have l₂ := e₂.frMap hP'
    refine _root_.GlobalTheory.FlagMod.FieldFlag.cell_sep E H Dw l Xo c Y p A Z π g κ hZ ht _ _ _ _ l₁.1 l₂.1 fun σ i => ?_
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₁)
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₂)
    exact (l₁.initSpan_eq hk l₁.1 rfl σ i).symm.trans (l₂.initSpan_eq hk' l₂.1 rfl σ i)
  refine ⟨{ YY := Z, π := π, proper := h1, normal := h2, flat := ?_, F := cellFrames hZ ht
            dense := _root_.GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage E H Dw l Xo c Y p A Z π g κ hZ, top := _root_.GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen E H Dw l Xo c Y p A Z π g κ hZ ht
            rep := fun S _ _ P => ?_, fin := fun K _ _ z => ?_ }⟩
  · exact _root_.GlobalTheory.flat_to_spec_field c.F Z (π ≫ Y.s)
  · obtain ⟨z, hz⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_lies_of_local E H Dw l Xo c Y p A Z π g κ hZ ht S P huniq fun q => _root_.GlobalTheory.FlagMod.FieldFlag.exists_cell_lies E H Dw l Xo c Y p A Z π g κ hZ ht S P q
    exact ⟨z, hz, fun z' hz' => huniq S P z' z hz' hz⟩
  · refine (Set.finite_singleton z).subset fun z' ⟨hx, h⟩ => ?_
    exact _root_.GlobalTheory.FlagMod.FieldFlag.cell_sep E H Dw l Xo c Y p A Z π g κ hZ ht K z' z _ hx rfl h

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegUniqAny

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PullDegUniq
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_isPullDeg_id {φ : R →+* R'} {D : DegPre R} {D₁ D₂ : DegPre R'} (h₁ : IsPullDeg φ D D₁)
    (h₂ : IsPullDeg φ D D₂) : Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) := by
  have hβ : Function.Injective (RingHom.id R') := Function.injective_id
  have h : IsPullDeg ((RingHom.id R').comp φ) D D₂ := (RingHom.id_comp φ).symm ▸ h₂
  have p₁ : IsGrpPullback D₁.P.A D.P.A (spMap φ) (proj h₁) := pull_grp h₁
  have sc : spMap (RingHom.id R') ≫ spMap φ = spMap ((RingHom.id R').comp φ) := (spMap_comp φ _).symm
  have p : IsGrpPullback D₂.P.A D.P.A (spMap (RingHom.id R') ≫ spMap φ) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D₂.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧
      Φ ≫ D₁.P.A.hom = D₂.P.A.hom ≫ spMap (RingHom.id R') :=
    ⟨p₁.1.lift (proj h) (D₂.P.A.hom ≫ spMap (RingHom.id R')) (p.1.w.trans (Category.assoc _ _ _).symm),
      p₁.1.lift_fst _ _ _, p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id R')) Φ :=
    IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D.P.isLB D₁.P.isLB D₂.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D₂.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D₂.c x).left ≫ Φ = spMap (RingHom.id R') ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D₂ ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D.P.isLB z
    have sβ : jK R' ≫ spMap (RingHom.id R') = genMap hβ ≫ jK R' :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := PsiEvenPull.psi_pull h₁ (xe x) (genMap hβ) z hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (genMap hβ ≫ h₁.g) z J₀ = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, h₁.g_comm, Category.assoc, h.g_comm, Category.id_comp, ← Category.assoc, ← sβ,
          Category.assoc]
        exact congrArg (jK R' ≫ ·) sc) hJ₀
    have hx : D₂.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R' ≫ (D₂.c x).left) ≫ Φ = genMap hβ ≫ jK R' ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    change _ = (om h₁.w z J₀ J₁ (genMap hβ ≫ D₁.xK (xe x)))⁻¹ * _ at v₁
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D₂.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniqAny

namespace GlobalTheory.Mum

theorem isPullDeg_unique_any : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg φ D D₁) → Nonempty (IsPullDeg φ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) :=
  fun _ _ _ _ _ _ _ _ _ _ ⟨h₁⟩ ⟨h₂⟩ => GlobalTheory.PullDegUniqAny.nonempty_isPullDeg_id h₁ h₂

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPrimitiveDeRhamTorsionTowerPresentation
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_sub_tower {B : ℕ → Type} [∀ n, AddCommGroup (B n)] (r : ∀ n, B (n + 1) → B n)
    (hr : ∀ n, Function.Surjective (r n)) (a : ∀ n, B n) :
    ∃ h : ∀ n, B n, ∀ n, a n = h n - r n (h (n + 1)) := by
  choose s hs using hr
  refine ⟨fun n ↦ Nat.rec (motive := B) 0 (fun n x ↦ s n (x - a n)) n, fun n ↦ ?_⟩
  simp only [hs, sub_sub_cancel]

theorem nonempty_dat (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) : Nonempty (Dat t c) := by
  obtain ⟨f, hf⟩ := CatCoh.H1.mk_surjective _ c.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R A f (by rw [hf]; exact c.2)
  obtain ⟨h, hh⟩ := exists_sub_tower (B := fun n ↦ G.A n) (fun n ↦ G.res n) (fun n ↦ G.res_surjective n)
    (fun n ↦ fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)))
  exact ⟨⟨f, hf, g, hg, h, hh⟩⟩

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalOfGenericFibrePullback
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.FlagCls

theorem isNormalScheme_of_isPreimmersion_of_flat {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isNormalScheme_of_isPullback_fractionField : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N G : Scheme.{0}) (g : N ⟶ Sp R) (j : G ⟶ N) (s : G ⟶ Sp K), IsPullback j s g (spMap (algebraMap R K)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G := by
  intro R K _ _ _ _ _ N G g j s hp hN
  have hb : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hbf : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) hp.flip hb
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) hp.flip hbf
  exact isNormalScheme_of_isPreimmersion_of_flat j hN

end GlobalTheory.FlagCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
section
open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((PDivGroup.relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) :=
  kerIdeal_relFrob_le_frobKerIdeal p R h G n
end

