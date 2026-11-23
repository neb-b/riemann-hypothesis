module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.CoefDuty.Model
open GlobalTheory.CoefDuty

section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

variable {N₀ N₁ N₂ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {A₂ : NAut N₂} {i₀ : N₀.Loc} {i₁ : N₁.Loc} {i₂ : N₂.Loc}

theorem iotaO_injective (N : NData R H what₂) (A : NAut N) (i : N.Loc) : Function.Injective (iotaO N A i) :=
  (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).injective).comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))

theorem φ_injective (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Function.Injective a.φ := fun x y h =>
  iotaO_injective N₀ A₀ i₀ (by rw [← a.φ_iota, ← a.φ_iota, h])

theorem s0_eq (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : N₀.s0 i₀ = N₁.s0 i₁ := by
  by_cases h : N₀.l i₀ = 2
  · rw [N₀.restNLevelExponent_of_two i₀ h, N₁.restNLevelExponent_of_two i₁ (a.l_eq ▸ h)]
  · rw [N₀.restNLevelExponent_of_odd i₀ h, N₁.restNLevelExponent_of_odd i₁ (a.l_eq ▸ h), a.l_eq]

theorem heckePol_map (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁) (w : PlE H) (hw : SplitOut N₁ i₁ w) :
    heckePol N₁ i₁ x w = (heckePol N₀ i₀ (a.e x) w).map a.φ := by
  unfold heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_add (f := _), Polynomial.map_pow, map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [a.hT w k x hw hk.1 hk.2]
  simp

theorem gen_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (s : ℕ) (z : ℤ_[p]ˣ) (z' : ℤ_[q]ˣ) (hz : HEq z z') :
    (∃ u : ℤ_[p]ˣ, (z : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ s * (u : ℤ_[p])) ↔
    ∃ u : ℤ_[q]ˣ, (z' : ℤ_[q]) = 1 + (q : ℤ_[q]) ^ s * (u : ℤ_[q]) := by
  subst h
  cases hz
  rfl

theorem localisationCoefficientExtension_isWildInertiaCyclotomic_iff (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (g : GE N₁) : IsWildInertiaCyclotomicElement N₁ i₁ g ↔ IsWildInertiaCyclotomicElement N₀ i₀ (a.γ g) := by
  unfold IsWildInertiaCyclotomicElement GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsInertiaCyclotomicGeneratorElement
  rw [gen_heq a.l_eq (N₀.s0 i₀) _ _ (a.cyc g), s0_eq a]
  simp only [a.ine, a.wild, a.l_eq]

end Record

section Plain
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isBounded_umax : IsBounded (Umax L n) := ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using hκ⟩⟩

theorem exists_isClassReps (J : Subgroup (GAf L n)) (T : Finset (GAf L n))
    (hT : ∀ g : GAf L n, ∃ t ∈ T, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ) :
    ∃ T', IsClassReps J T' := by
  classical
  let q : GAf L n → DoubleCoset.Quotient (GQ L n : Set (GAf L n)) J := DoubleCoset.mk _ _
  have key : ∀ g t : GAf L n, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ) ↔ q t = q g := by
    intro g t
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨γ, κ, h, e⟩ => ⟨γ, γ.2, κ, h, e⟩, fun ⟨γ, hγ, κ, h, e⟩ => ⟨⟨γ, hγ⟩, κ, h, e⟩⟩
  have hout : ∀ c, q (Quotient.out c) = c := fun c => Quotient.out_eq c
  refine ⟨T.image fun t => (q t).out, fun g => ⟨(q g).out, ⟨?_, (key _ _).2 (hout _)⟩, ?_⟩⟩
  · obtain ⟨t, ht, h⟩ := hT g
    exact Finset.mem_image.2 ⟨t, ht, by rw [(key _ _).1 h]⟩
  · rintro y ⟨hy, h⟩
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy
    rw [← (key _ _).1 h, hout]

end Plain
end GlobalTheory.CoefDuty.Model
end
