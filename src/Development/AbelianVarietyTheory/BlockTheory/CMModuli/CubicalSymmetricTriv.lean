module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def thirdDiff {A U : Type} [CommGroup A] [CommGroup U] (f : A → U) (x y w : A) : U :=
  f (x * y * w) * (f (x * y))⁻¹ * (f (x * w))⁻¹ * (f (y * w))⁻¹ * f x * f y * f w * (f 1)⁻¹

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev symLB (L : LB G.left) : LB G.left :=
  LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]

variable {G}

def rigV (L : RigLB G) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) L.rig (toUnit T).left z J

def symV {L : LB G.left} (σ : LB.Gen (symLB G L)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ x.left z J

variable (G)

structure CubSym where

  L : RigLB G

  cub : CubicalStr G L

  sym : LB.Gen (symLB G L.L)
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)
  sym_cub : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ x y w : T ⟶ G, cubV cub z J x⁻¹ y⁻¹ w⁻¹ = thirdDiff (symV sym z J) x y w * cubV cub z J x y w

variable {G}

end Sym

section Iso

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G']
  [GrpObj G] [IsCommMonObj G]

end Iso

section Triv

variable {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]

abbrev lamOn (i : H ⟶ G) (L : LB G.left) : LB (H ⊗ G).left :=
  LB.LinComb L (K := Fin 4)
    ![((fst H G ≫ i) * snd H G).left, (fst H G ≫ i).left, (snd H G).left, (1 : H ⊗ G ⟶ G).left]
    ![1, -1, -1, 1]

def lamV {i : H ⟶ G} {L : LB G.left} (s : LB.Gen (lamOn i L)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (t : T ⟶ H) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) s (lift t x).left z J

structure IsBiextTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i]
    (s : LB.Gen (lamOn i L.L)) : Prop where
  gen : s.IsGen
  law₁ : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ (t t' : T ⟶ H) (x : T ⟶ G), lamV s z J (t * t') x =
      cubV c z J (t ≫ i) (t' ≫ i) x * lamV s z J t x * lamV s z J t' x
  law₂ : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ (t : T ⟶ H) (x x' : T ⟶ G), lamV s z J t (x * x') =
      cubV c z J (t ≫ i) x x' * lamV s z J t x * lamV s z J t x'

def trivV {i : H ⟶ G} {L : LB G.left} (σ : LB.Gen (L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (t : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ t.left z J

structure IsCubTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i]
    (σ : LB.Gen (L.L.pull i.left)) : Prop where
  gen : σ.IsGen
  rig : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    trivV σ z J 1 = rigV L z J
  cub : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ t t' t'' : T ⟶ H,
      thirdDiff (trivV σ z J) t t' t'' = cubV c z J (t ≫ i) (t' ≫ i) (t'' ≫ i)

def IsEven (L : CubSym G) (i : H ⟶ G) [IsMonHom i] (σ : LB.Gen (L.L.L.pull i.left)) : Prop :=
  ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.L.ι), Good L.L.L z J →
    ∀ t : T ⟶ H, trivV σ z J t⁻¹ = symV L.sym z J (t ≫ i) * trivV σ z J t

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

end Triv

section Pairing

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
  (c : CubicalStr G L)

end Pairing

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

def charV (χ : X) {T : Over S} (z : T.left) (t : T ⟶ splitTorus S X) : (T.left.presheaf.stalk z)ˣ :=
  gm t.left z ⊤ (charUnit S X χ)

variable {B : Over S} [GrpObj B]

structure IsTorusExt (i : splitTorus S X ⟶ G) (q : G ⟶ B) : Prop where
  free : Module.Free ℤ X
  finite : Module.Finite ℤ X
  comm : IsCommMonObj G
  abelian : IsAbelianScheme B
  i_hom : IsMonHom i
  q_hom : IsMonHom q
  isKernel : IsPullback i (toUnit _) q (η[B])
  locTriv : ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧
    ∃ r : V.toScheme ⟶ G.left, r ≫ q.left = V.ι

end Torus

section Examples

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def trivLB (Y : Scheme.{0}) : LB Y := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def trivGen {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb (trivLB Y) φ ε) := ⟨fun _ => 1⟩

theorem trivGen_isGen {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ) :
    (trivGen φ ε).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Finset.prod_eq_one fun _ _ =>
    (congrArg (· ^ _) ((congrArg _ (map_one _)).trans (map_one _))).trans (one_zpow _))
    (map_one _)).trans (_root_.mul_one _)).symm

theorem val_trivGen {Y Z W : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ)
    (r : W ⟶ Z) (z : W) (J) : val (trivGen φ ε) r z J = 1 := map_one _

def trivRig : RigLB G where
  L := trivLB _
  rig := trivGen _ _
  isLB := ⟨by simp [trivLB], fun _ => map_one _, fun _ _ _ =>
    ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).trans (map_one _).symm⟩
  rigGen := trivGen_isGen _ _

def trivCubSym : CubSym G where
  L := trivRig G
  cub :=
    { t := trivGen _ _
      isGen := trivGen_isGen _ _
      face := fun _ => corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_pull hJ _ _ _).trans ((val_trivGen _ _ _ _ _).trans (val_one _).symm)
      cubeSymmetric_swap_first := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_trivGen _ _ _ _ _).trans ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)).symm
      cubeSymmetric_swap_last := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        (val_trivGen _ _ _ _ _).trans ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)).symm
      cocycle := corr_of_val (trivRig G).isLB fun _ _ hJ =>
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _))
          ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)))).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _))
          ((val_pull hJ _ _ _).trans (val_trivGen _ _ _ _ _)))).symm }
  sym := trivGen _ _
  sym_gen := trivGen_isGen _ _
  sym_rig := corr_of_val (trivRig G).isLB fun _ _ hJ =>
    (val_pull hJ _ _ _).trans ((val_trivGen _ _ _ _ _).trans (val_one _).symm)
  sym_cub := fun T z J _ x y w => by
    have a : ∀ x : T ⟶ G, symV (L := (trivRig G).L) (trivGen _ _) z J x = 1 := fun _ => val_trivGen _ _ _ _ _
    simp only [thirdDiff, a, inv_one, _root_.mul_one, _root_.one_mul]
    exact (val_trivGen _ _ _ _ _).trans (val_trivGen _ _ _ _ _).symm

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
