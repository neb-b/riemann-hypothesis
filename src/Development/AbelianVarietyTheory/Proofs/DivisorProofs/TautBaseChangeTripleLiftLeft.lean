module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautEx

theorem toUnit_left {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

section Gen

variable {Y : Scheme.{0}} {M : LB Y}

def mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top u * t.s j⟩

theorem gm_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {y : Y} {i : M.ι} (h : y ∈ M.U i) :
    gm (𝟙 Y) y (M.U i) ((mulU u t).s i) = gm (𝟙 Y) y ⊤ u * gm (𝟙 Y) y (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res (𝟙 Y) y _ h _))

theorem isGen_mulU (u : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (mulU u t).IsGen := by
  intro i j
  refine unit_ext fun x hx => ?_
  have e := congrArg (gm (𝟙 Y) x _) (ht i j)
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx] at e
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx, gm_mulU u t hx.1, gm_mulU u t hx.2, e]
  exact mul_left_comm _ _ _

variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem val_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (hJ : Good L z J) : val (mulU u t) r z J = gm r z ⊤ u * val t r z J :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ (hJ.mem φ r) _))

end Gen

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

abbrev fC : Sp (MvPowerSeries (Fin N) W) ⟶ Sp W := spMap MvPowerSeries.C

abbrev Bp : Over (Sp (MvPowerSeries (Fin N) W)) := (Over.pullback (fC (W := W) N)).obj T.B

theorem isAb_Bp : IsAbelianScheme (Bp T N) := GlobalTheory.isAbelianScheme_pullback_obj _ _ T.isAb

instance : IsCommMonObj (Bp T N) := (isAb_Bp T N).comm

theorem cart : IsGrpPullback (Bp T N) T.B (fC N) (pullback.fst T.B.hom (fC N)) := isGrpPullback_pullback T.B _

abbrev cm : CubeMap (Bp T N) T.B := cubeMapOf (cart T N)

theorem pullSt : ∃ (hL : (T.M.L.pull (cm T N).F).IsLB) (hr : ((cm T N).rigPull T.M.L T.M.rig).IsGen),
    (∃ c' : CubicalStr (Bp T N) ((cm T N).rigLB T.M hL hr), (cm T N).IsPullCubical c' T.cub) ∧
      (T.M.IsSymmetric → ((cm T N).rigLB T.M hL hr).IsSymmetric) :=
  proved_CubePullSt _ _ T.B (Bp T N) (cm T N) T.M T.cub

abbrev Mp : RigLB (Bp T N) := (cm T N).rigLB T.M (pullSt T N).fst (pullSt T N).snd.fst

abbrev cubP : CubicalStr (Bp T N) (Mp T N) := CubePf.cubical (cm T N) T.M T.cub _ _

end Base

section Pts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

theorem lamPts_w {S : Scheme.{0}} {G Tt : Over S} [GrpObj G] (x y : Tt ⟶ G) (k : Fin 4) :
    lamPts x y k ≫ G.hom = Tt.hom := by
  fin_cases k <;> simp [lamPts]

theorem unit_hom (S : Scheme.{0}) : (𝟙_ (Over S)).hom = 𝟙 S := rfl

end Pts

section Periods

variable (W : Type) [CommRing W] [IsDomain W] (N : ℕ)

end Periods

section Charts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)


end Charts

section Tau

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v := map_mul _ _ _

theorem triple_lift_comp_projections {S : Scheme.{0}} {G Tt : Over S} (x y w : Tt ⟶ G) :
    lift x (lift y w) ≫ x3 G 0 = x ∧ lift x (lift y w) ≫ x3 G 1 = y ∧ lift x (lift y w) ≫ x3 G 2 = w := by
  simp [x3]

theorem alg_step {G : Type} [CommGroup G] {g₁ g₂ v c a b : G} (e : v * c = a * b) :
    g₁ * g₂ * v * c = g₁ * a * (g₂ * b) := by
  rw [mul_assoc (g₁ * g₂), e, _root_.mul_mul_mul_comm]

end Tau

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

end Main

end GlobalTheory.PolDeg.TautEx
