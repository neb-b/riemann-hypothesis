module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def alongS (F : Shv R) (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : HS R F n Z →+ HS R F n X where
  toFun x := (Abelian.Ext.mk₀ t).comp x (zero_add n)
  map_zero' := Abelian.Ext.comp_zero _ _ _ _ _
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _

def push (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : H R n Z →ₗ[R] H R n X where
  toFun x := (Abelian.Ext.mk₀ t).comp (x : HS R (coef R) n Z) (zero_add n)
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _
  map_smul' r _ := Abelian.Ext.comp_smul _ _ _ (ULift.up r : ULift.{1} R)

end Transfer

section Mu

variable (n : ℕ) [NeZero n]

def Mu (A : Type) [CommRing A] : Type := Additive (rootsOfUnity n A)


end Mu

def IsStrictlySemistable {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.Et

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
section
noncomputable section

namespace GlobalTheory.Cong

variable {k : Type} [NormedField k]

def PolyApprox [IsUltrametricDist k] {J : Type} (θ : J → k) (S : Set (J → k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

def trc {Γ A : Type} [Group Γ] [CommRing A] {a : ℕ} (r : Γ →* GL (Fin a) A) (g : Γ) : A :=
  ((r g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).trace

def LinApprox {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C ∧
    ∀ g : Γ, ‖trc r g - ∑ ρ ∈ s, c ρ * trc ρ g‖ ≤ ε

def opOf {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) (v : V) : V :=
  f.sum fun g c => c • ρ g v

theorem PolyApprox.mono [IsUltrametricDist k] {J : Type} {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hST : S ⊆ T) : PolyApprox θ T := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hST, hP⟩

variable [NormOneClass k] [IsUltrametricDist k]

theorem aeval_sub_le {J : Type} {x y : J → k} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1)
    (hxy : ∀ j, ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖MvPolynomial.aeval x P‖ ≤ 1 ∧ ‖MvPolynomial.aeval y P‖ ≤ 1 ∧
      ‖MvPolynomial.aeval x P - MvPolynomial.aeval y P‖ ≤ δ := by
  first
  | exact @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | (apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le ..)

end GlobalTheory.Cong

end
end

