module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

@[expose] public section

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

structure PLat (O : Type) [Ring O] (bar : O → O) where
  La : Type
  [acg : AddCommGroup La]
  [mod : Module O La]
  fin : Module.Finite ℤ La
  free : Module.Free ℤ La
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0
  adj : ∀ (a : O) x y, EF (a • x) y = EF x (bar a • y)

attribute [instance] PLat.acg PLat.mod PLat.fin PLat.free

variable {O : Type} [Ring O] {bar : O → O}

def IsPeriod (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) : Prop :=
  (∀ (a : O) x, P (a • x) = ρ a *ᵥ P x) ∧ Function.Injective P ∧ DiscreteTopology P.range ∧
    Submodule.span ℝ (Set.range P) = ⊤ ∧
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y

def IsHolPeriods (D : PLat O bar) {g m : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (B : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) : Prop :=
  (∀ b ∈ B, IsPeriod D ρ (P b)) ∧ ∀ x, DifferentiableOn ℂ (fun b => P b x) B

def PerCoord (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (d : ℕ) : Prop :=
  ∀ P₀, IsPeriod D ρ P₀ → ∃ (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)))
    (Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ)) (s : Finset D.La) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ IsHolPeriods D ρ B Q ∧
    Z P₀ ∈ B ∧ Q (Z P₀) = P₀ ∧ (∀ b ∈ B, (∀ x ∈ s, ‖Q b x - P₀ x‖ < ε) → Z (Q b) = b) ∧
    (∀ P, IsPeriod D ρ P → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → Z P ∈ B ∧
      ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, P x = h (Q (Z P) x)) ∧
    (∀ P P', IsPeriod D ρ P → IsPeriod D ρ P' → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → (∀ x ∈ s, ‖P' x - P₀ x‖ < ε) →
      ∀ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ x, P' x = h (P x)) → Z P' = Z P) ∧
    ∀ (m : ℕ) (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B' → IsHolPeriods D ρ B' P →
      (∀ b ∈ B', ∀ x ∈ s, ‖P b x - P₀ x‖ < ε) → DifferentiableOn ℂ (fun b => Z (P b)) B'

def IsIsom (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) : Prop := ∀ x y, D'.EF (w x) (w y) = D.EF x y

def IsMarkedIsom {Λ : Type} (N : ℕ) (D D' : PLat O bar) (t : Λ → D.La) (t' : Λ → D'.La) (w : D.La ≃ₗ[O] D'.La) : Prop :=
  IsIsom D D' w ∧ ∀ a, ∃ e, w (t a) = t' a + N • e

def Genus (p N : ℕ) (D D' : PLat O bar) (t : D.La → D'.La) : Prop :=
  ∃ (f : ℕ → D.La →+ D'.La) (ν : ℕ → ℤ), t = f N ∧
    (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ ν (n * m) - ν n ∧ ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
    ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (ν n) (n : ℤ) ∧ (∀ (c : O) a, ∃ e, f n (c • a) = c • f n a + n • e) ∧
      (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧
      (∀ a', ∃ a e, a' = f n a + n • e) ∧ ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a'

structure Fam (R : Type) [CommRing R] (O : Type) [Ring O] (Λ : Type) (g : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  A : Over X
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension g A.hom
  act : O → (A ⟶ A)
  hom : ∀ a, IsMonHom (act a)
  act_one : act 1 = 𝟙 A
  act_mul : ∀ a b, act (a * b) = act b ≫ act a
  act_add : ∀ a b, act (a + b) = act a * act b
  L : LB A.left
  isLB : L.IsLB
  ample : Out.RelAmple A L
  eta : Λ → (𝟙_ (Over X) ⟶ A)

attribute [instance] Fam.grp Fam.comm

variable {R : Type} [CommRing R] {Λ : Type} {g : ℕ}

def IsExp {X : Scheme.{0}} {G : Over X} [GrpObj G] (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left

def UnifAt (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La)
    (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) : Prop :=
  y ≫ F.s = spMap σ ∧ IsPeriod D' ρ P ∧ IsExp y e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧
    (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ F.act a) ∧
    (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs F.A F.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) ∧
    ∀ a, toUnit _ ≫ F.eta a = e ((N : ℂ)⁻¹ • P (t a))

structure FineAt (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) : Prop where
  pts : ∀ y : Sp ℂ ⟶ F.X, y ≫ F.s = spMap σ → ∃ D' t P e, C D' t ∧ UnifAt F σ ρ N D' t P y e
  occ : ∀ D' t P, C D' t → IsPeriod D' ρ P → ∃ y e, UnifAt F σ ρ N D' t P y e
  sep : ∀ (D' D'' : PLat O bar) t t' P P' y y' e e', UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y' e' →
    ∀ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w →
      (∀ x, P' (w x) = h (P x)) → y = y'

structure Unif (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) where
  n : ℕ
  Di : Fin n → PLat O bar
  t : ∀ i, Λ → (Di i).La
  mem : ∀ i, C (Di i) (t i)
  ne : ∀ i, ∃ P, IsPeriod (Di i) ρ P
  all : ∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w
  distinct : ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j
  u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ F.X)
  ex : ∀ i P, (Fin g → ℂ) → (Over.mk (u i P) ⟶ F.A)
  unif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F σ ρ N (Di i) (t i) P (u i P) (ex i P)
  onto : ∀ y : Sp ℂ ⟶ F.X, y ≫ F.s = spMap σ → ∃ i P, IsPeriod (Di i) ρ P ∧ u i P = y
  disj : ∀ i j P P', IsPeriod (Di i) ρ P → IsPeriod (Di j) ρ P' → u i P = u j P' → i = j
  fibre : ∀ i P P', IsPeriod (Di i) ρ P → IsPeriod (Di i) ρ P' → (u i P = u i P' ↔
    ∃ (w : (Di i).La ≃ₗ[O] (Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (Di i) (Di i) (t i) (t i) w ∧ ∀ x, P' (w x) = h (P x))
  hol : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))), IsOpen B →
    IsHolPeriods (Di i) ρ B P → IsHolTo B (fun b => u i (P b)) ∧
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (ex i (P bz.1) bz.2).left)
  lift : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)), IsOpen B →
    (∀ b ∈ B, y b ≫ F.s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B,
    ∃ (B' : Set (Fin m → ℂ)) (i : Fin n) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (Di i) ρ B' P ∧ ∀ b ∈ B', u i (P b) = y b

def FullMark (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) : Prop := ∀ x, ∃ a e, x = t a + N • e

def IsBC (F' : Fam ℂ O Λ g) (F : Fam R O Λ g) (σ : R →+* ℂ) : Prop :=
  ∃ (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsPullback f F'.s F.s (spMap σ) ∧ IsGrpPullback F'.A F.A f φ ∧
    (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) ∧ LBIso F'.L (F.L.pull φ) ∧
    ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left

section Groups

variable (D : PLat O bar) {r : ℕ} (b : Module.Basis (Fin r) ℤ D.La) (K : Type) [CommRing K]

def actM (a : O) : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => ((b.repr (a • b j) i : ℤ) : K)

end Groups

end GlobalTheory.PELU
