module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
section
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.SW

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

def SWAt (n N : ℕ) : Prop :=
  ∀ (M R : ℕ) (φ : Fam E n N), admitted M R φ → ∀ Z ∈ Hn Ψ N, swd Ψ M φ Z 0 0 = 0

def LevelL (Λ : Lt E n) (R : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ) : Prop :=
  (∀ x, φ x ≠ 0 → ColsIn Λ ((R : E) • x)) ∧ ∀ x y, ColsIn Λ y → φ (x + (R : E) • y) = φ x

abbrev CF (a b : ℕ) : Type := Ψ → Fin a → Fin b → ℂ

def IsHeat (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ) : Prop :=
  DifferentiableOn ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
    {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N} ∧
  ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (τ : Ψ) (a b : Fin N),
    2 * Real.pi * I * deriv (fun s : ℂ =>
      D (fun σ => Z σ + if σ = τ then Matrix.single a b s else 0) z z') 0 =
    ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
      D Z (fun σ => z σ + if σ = τ then Matrix.single k a s else 0)
        (fun σ => z' σ + if σ = τ then Matrix.single k b t else 0)) 0) 0

def IsMaj {m : ℕ} (G : Matrix (Fin m) (Fin m) E) (H : CM Ψ m m) : Prop :=
  ∀ τ : Ψ, (H τ).PosDef ∧ H τ * (G.map τ.1)⁻¹ * H τ = G.map τ.1

def hval {m : ℕ} (H : CM Ψ m m) (τ : Ψ) (v : Fin m → E) : ℝ :=
  ((fun a => τ.1 (v a)) ⬝ᵥ H τ *ᵥ fun a => conj (τ.1 (v a))).re

def IsoRows {k m : ℕ} (G : Matrix (Fin m) (Fin m) E) (W : Matrix (Fin k) (Fin m) E) : Prop :=
  LinearIndependent E (fun i => W i) ∧ W * G * ccT W = 0

def ShortIso (N D : ℕ) (ε C : ℝ) : Prop :=
  ∀ (G : Matrix (Fin (2 * N)) (Fin (2 * N)) E) (H : CM Ψ (2 * N) (2 * N)), ccT G = G → G.det ≠ 0 →
    Den D G → Den D G⁻¹ → (∃ W : Matrix (Fin N) (Fin (2 * N)) E, IsoRows G W) → IsMaj Ψ G H →
    (∀ v : Fin (2 * N) → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) → ε ≤ ∑ τ, hval Ψ H τ v) →
    ∃ W : Matrix (Fin N) (Fin (2 * N)) E, IntM W ∧ IsoRows G W ∧ ∀ i τ, hval Ψ H τ (W i) ≤ C

end

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SpanningFamilies.NotAdmissibleHalfLatticeFamily
section
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.SW.Model

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_cc (x : E) : cc (cc x) = x := by simp [cc]

theorem cc_integral {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)

omit [IsCMField E] in
theorem mem_stdL {m : ℕ} (x : Fin m → E) : x ∈ stdL E m ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      by_cases h : a = b
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx =>
      intro a
      have : (c • x) a = (c : E) * x a := rfl
      rw [this]; exact c.isIntegral_coe.mul (hx a)
  · intro hx
    have : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin m → E) := by
      ext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · change x b = x b * (Pi.single b (1 : E) : Fin m → E) b
        simp
      · intro a _ h
        change x a * (Pi.single a (1 : E) : Fin m → E) b = 0
        simp [Pi.single_apply, Ne.symm h]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem herm_one {m : ℕ} (x y : Fin m → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a] <;> simp +contextual [Matrix.one_apply, eq_comm]

omit [IsCMField E] in
theorem nat_smul_mem {m : ℕ} (Λ : Lt E m) (s : ℕ) {v : Fin m → E} (hv : v ∈ Λ) :
    (s : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubgroup.nsmul_mem hv s






end

end GlobalTheory.SW.Model
end

