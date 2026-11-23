module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Lattice

variable {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]

def IsIsoSub (form : abelian₂ →ₗ[ℤ] abelian₂ →ₗ[ℤ] ℤ) (I : Submodule O abelian₂) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, form v w = 0

def IsSaturated (I : Submodule O abelian₂) : Prop :=
  ∀ (v : abelian₂) (n : ℤ), n ≠ 0 → n • v ∈ I → v ∈ I

def IsNzFamily (I : Submodule O abelian₂) (ρ : ℕ) (v : Fin ρ → abelian₂) : Prop :=
  1 ≤ ρ ∧ (∀ a, v a ∈ I) ∧ LinearIndependent O v ∧
    (Submodule.span O (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0

end Lattice

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure CuspData (D : ComponentData II Ψ K ι Ω E) (O : Type) [CommRing O] (abelian₂ : Type)
    [AddCommGroup abelian₂] [Module O abelian₂] where

  rank : ℕ
  basis : Module.Basis (Fin rank) ℤ abelian₂

  form : abelian₂ →ₗ[ℤ] abelian₂ →ₗ[ℤ] ℤ
  alt : ∀ v, form v v = 0
  unimod : IsUnit (Matrix.of fun a b => form (basis a) (basis b)).det

  emb : Ψ → O →+* ℂ

  normSq : ((Σ k, ι k) → ℂ) → abelian₂ → ℝ
  normSq_pos : ∀ z ∈ D.Xo, ∀ v, v ≠ 0 → 0 < normSq z v
  form_le : ∀ z ∈ D.Xo, ∀ v w, ((form v w : ℤ) : ℝ) ^ 2 ≤ normSq z v * normSq z w

  lie : ((Σ k, ι k) → ℂ) → Ψ → abelian₂ → Fin (D.N - D.j) → ℂ
  lie_add : ∀ z τ v w, lie z τ (v + w) = lie z τ v + lie z τ w
  lie_smul : ∀ z τ (a : O) v, lie z τ (a • v) = emb τ a • lie z τ v
  lie_le : ∀ z ∈ D.Xo, ∀ v, ∑ τ, ∑ c, ‖lie z τ v c‖ ^ 2 ≤ normSq z v
  inj : ∀ z ∈ D.Xo, ∀ τ (I : Submodule O abelian₂), IsIsoSub form I → ∀ (ρ : ℕ) (v : Fin ρ → abelian₂),
    (∀ a, v a ∈ I) → LinearIndependent O v → LinearIndependent ℂ fun a => lie z τ (v a)
  torus : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
    normSq (torusSmul c z) = normSq z ∧ lie (torusSmul c z) = lie z

namespace CuspData

variable {D : ComponentData II Ψ K ι Ω E} {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]
  (Cd : CuspData D O abelian₂)

def gramLie (z : (Σ k, ι k) → ℂ) (τ : Ψ) {ρ : ℕ} (v : Fin ρ → abelian₂) : Matrix (Fin ρ) (Fin ρ) ℂ :=
  Matrix.of fun a b => ∑ c, starRingEnd ℂ (Cd.lie z τ (v a) c) * Cd.lie z τ (v b) c


open Classical in
def Nz (z : (Σ k, ι k) → ℂ) (I : Submodule O abelian₂) : ℝ :=
  if h : ∃ ρ v, IsNzFamily I ρ v then
    (∏ τ, (Cd.gramLie z τ h.choose_spec.choose).det.re) /
      ((Submodule.span O (Set.range h.choose_spec.choose)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)
  else 1

def cuspWeight (z : (Σ k, ι k) → ℂ) : ℝ :=
  max 0 (sSup {x | ∃ I : Submodule O abelian₂, I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧
    x = -Real.log (Cd.Nz z I)})

end CuspData

namespace Line

open GaussianInt

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Values

variable {Ω : Type} [Field Ω]

omit [Fintype K] in
theorem isValueAt_add {y : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt y s z v) (hw : IsValueAt y t z w) : IsValueAt y (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · rw [map_add (f := _), map_mul, map_mul, map_mul, heq, heq']; ring
  · rw [map_mul, map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul]
    field_simp

theorem isValueAt_intCast (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) :
    IsValueAt y (n : Ω) z (n : ℂ) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_inv {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (hs : s ≠ 0) (hv0 : v ≠ 0) : IsValueAt y s⁻¹ z v⁻¹ := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hgy : aeval y g ≠ 0 := by rw [heq]; exact mul_ne_zero hs hy
  have hgz : eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hv0; exact hv0 rfl
  refine ⟨d, h, g, hh, hg, hgy, ?_, hgz, by rw [inv_div]⟩
  rw [heq]
  field_simp

theorem isValueAt_pow {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (n : ℕ) : IsValueAt y (s ^ n) z (v ^ n) := by
  induction n with
  | zero => simpa using isValueAt_one_self y z
  | succ n ih => rw [pow_succ, pow_succ]; exact isValueAt_mul ih hv

theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨a, i₀⟩ := p
  show ∑ i, (Finsupp.single (⟨a, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = if k = a then 1 else 0
  by_cases hk : k = a
  · subst hk
    rw [if_pos rfl, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      classical
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    classical
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

end Values

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

