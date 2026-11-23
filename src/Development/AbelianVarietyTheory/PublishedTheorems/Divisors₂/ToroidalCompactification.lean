module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogDR

section Nabla

variable {R : Type} [CommRing R]

def derHom (D : Derivation ℤ R R) : R →+* DualNumber R where
  toFun r := TrivSqZeroExt.inl r + TrivSqZeroExt.inr (D r)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem derHom_apply (D : Derivation ℤ R R) (r : R) :
    derHom D r = TrivSqZeroExt.inl r + TrivSqZeroExt.inr (D r) := rfl

variable (A : Over (Sp R)) [GrpObj A]

theorem derMor (D : Derivation ℤ R R) :
    GrpMor (dp0 R) (𝟙 _) A (epsDP R) (epsRed R) A (derHom D) (𝟙 _) (Over.Hom.left (𝟙 A)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← Cris.spMap_comp, show (TrivSqZeroExt.fstHom R R R).toRingHom.comp (derHom D) = RingHom.id R from
        RingHom.ext fun r ↦ by simp [derHom_apply]]
      exact (Cris.spMap_id R).symm) (𝟙 A)

variable {A}

def IsNabla (D : Derivation ℤ R R) (h k : HdR A) : Prop :=
  ∃ d : Crys (epsDP R) (epsRed R) A, (derMor A D).Corr h d ∧
    ∀ c : primDR A, d ((constMor A).pull c) = TrivSqZeroExt.inl (h c) + TrivSqZeroExt.inr (k c)

variable {D : Derivation ℤ R R}

end Nabla

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

structure Chart (t : SAB H X) (V : X.Opens) where

  U : X.affineOpens

  S : Type
  [ring : CommRing S]
  [alg : Algebra Γ(X, U.1) S]
  isOpenImmersion : IsOpenImmersion (spMap (algebraMap Γ(X, U.1) S) ≫ chart U)
  range : Set.range (spMap (algebraMap Γ(X, U.1) S) ≫ chart U :) = (U.1 ⊓ V : X.Opens)

  A : Over (Sp S)
  [grp : GrpObj A]

  φ : A.left ⟶ t.G.left
  cart : IsGrpPullback A t.G (spMap (algebraMap Γ(X, U.1) S) ≫ chart U) φ

attribute [instance] Chart.ring Chart.alg Chart.grp

variable {t : SAB H X} {V : X.Opens}

theorem exists_chart (t : SAB H X) (U : X.affineOpens) (h : IsAffineOpen (U.1 ⊓ V)) :
    ∃ c : Chart t V, c.U = U := by
  let _ : Algebra Γ(X, U.1) Γ(X, U.1 ⊓ V) := (resG X inf_le_left).toAlgebra
  have e : spMap (algebraMap Γ(X, U.1) Γ(X, U.1 ⊓ V)) ≫ chart U = h.fromSpec :=
    U.2.map_fromSpec h (homOfLE inf_le_left).op
  refine ⟨{ U := U, S := Γ(X, U.1 ⊓ V), isOpenImmersion := ?_, range := ?_
            A := (Over.pullback _).obj t.G, φ := _, cart := isGrpPullback_pullback t.G _ }, rfl⟩
  · rw [e]; infer_instance
  · rw [e]; exact h.range_fromSpec

namespace Chart

variable (c : Chart t V)

def HasImage (h : HdR c.A) (v : Sp (DualNumber Γ(X, c.U.1)) ⟶ t.G.left) : Prop :=
  ∃ w : epsR c.S ⟶ c.A,
    w.left ≫ c.φ = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap Γ(X, c.U.1) c.S)) ≫ v ∧
    IsLieImage h w


def coLie (ψ : LinearMap.BilinForm c.S (HdR c.A)) : Submodule Γ(X, c.U.1) (HdR c.A) where
  carrier := {f | f ∈ Fil c.A ∧ ∀ h v, IsTanAtG t (chart c.U) v → c.HasImage h v →
    ψ f h ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)}
  zero_mem' := ⟨zero_mem _, fun h v _ _ ↦ ⟨0, by simp⟩⟩
  add_mem' := fun {f g} hf hg ↦ ⟨add_mem hf.1 hg.1, fun h v a b ↦ by
    obtain ⟨r, hr⟩ := hf.2 h v a b
    obtain ⟨s, hs⟩ := hg.2 h v a b
    exact ⟨r + s, by simp [hr, hs]⟩⟩
  smul_mem' := fun r f hf ↦ by
    rw [← algebraMap_smul c.S r f]
    refine ⟨Submodule.smul_mem _ _ hf.1, fun h v a b ↦ ?_⟩
    obtain ⟨s, hs⟩ := hf.2 h v a b
    exact ⟨r * s, by rw [map_smul, LinearMap.smul_apply, map_mul, hs, smul_eq_mul]⟩

end Chart

def IsCanLattice {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : Chart t V) (L : Submodule Γ(X, c.U.1) (HdR c.A)) : Prop :=
  Module.Finite Γ(X, c.U.1) L ∧ Module.Projective Γ(X, c.U.1) L ∧ Submodule.span c.S (L : Set (HdR c.A)) = ⊤ ∧
  (∃ ψ : LinearMap.BilinForm c.S (HdR c.A), IsPolForm (dp0 c.S) (𝟙 _) c.A (t.PP.L.pull c.φ) ψ ∧
    (∀ x, x ∈ L ↔ ∀ y ∈ L, ψ x y ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)) ∧
    (∀ x, x ∈ c.coLie ψ ↔ x ∈ L ∧ x ∈ Fil c.A) ∧ ∀ x ∈ c.coLie ψ, ∀ y ∈ c.coLie ψ, ψ x y = 0) ∧
  (∀ h ∈ L, ∃ v, IsTanAtG t (chart c.U) v ∧ c.HasImage h v) ∧
  (∀ v, IsTanAtG t (chart c.U) v → ∃ h ∈ L, c.HasImage h v) ∧
  (∀ D ∈ logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) c.U, ∃ D' : Derivation ℤ c.S c.S,
    (∀ r, D' (algebraMap Γ(X, c.U.1) c.S r) = algebraMap Γ(X, c.U.1) c.S (D r)) ∧
      ∀ h ∈ L, ∃ k ∈ L, IsNabla D' h k) ∧
  ∀ (a : 𝓞 E) (f : c.A ⟶ c.A) [IsMonHom f], f.left ≫ c.φ = c.φ ≫ (t.act.act a).left →
    ∀ h ∈ L, push (dp0 c.S) (𝟙 _) f h ∈ L

def IsCanExt {K : Type} [CommRing K] (s : X ⟶ Sp K)
    (L : ∀ c : Chart t V, Submodule Γ(X, c.U.1) (HdR c.A)) : Prop :=
  (∀ c, IsCanLattice s c (L c)) ∧
    ∀ c c' : Chart t V, c'.U.1 ≤ c.U.1 → ∀ (σ : c.S →+* c'.S) (q : c'.A.left ⟶ c.A.left)
      (m : GrpMor (dp0 c.S) (𝟙 _) c.A (dp0 c'.S) (𝟙 _) c'.A σ (spMap σ) q), q ≫ c.φ = c'.φ →
      L c' = Submodule.span Γ(X, c'.U.1) {h' | ∃ h ∈ L c, m.Corr h h'}

end GlobalTheory.LogDR

namespace GlobalTheory.Published

open GlobalTheory.LogDR

def DeRhamCanonicalExtension : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      ∃ Y : Model Xo c (RingHom.id c.F),
        SmoothOfRelativeDimension Dw.dim Y.s ∧ ReciprocityTheory.AnForm.R.FinalTheorems.Snc (boundary Y) ∧
          HasLogKS Y.t Y.s (interior Y) ∧
          ∃ L : ∀ ch : Chart Y.t (interior Y), Submodule Γ(Y.X, ch.U.1) (HdR ch.A), IsCanExt Y.s L

end GlobalTheory.Published
