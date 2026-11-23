module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ChowHt

section Mult

variable {R : Type} [CommRing R]

def localLength (J Q : Ideal R) [Q.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))

theorem localLength_ne_top [IsNoetherianRing R] {J Q : Ideal R} [Q.IsPrime]
    (h : Q ∈ J.minimalPrimes) : localLength J Q ≠ ⊤ := by
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime Q) Q J h
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hrad
  have hmin : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
      (J.map (algebraMap R (Localization.AtPrime Q))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  haveI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  rw [localLength, Module.length_eq_of_surjective
    (R := Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end Mult

variable {k : Type} [Field k] {N : ℕ}


open Classical in
def projCycle (J : Ideal (MvPolynomial (Fin N) k)) : Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun Q => if h : Q ∈ projComponents J then
      (haveI : Q.IsPrime := h.1.1.1; localLength J Q).toNat else 0)
    ((finite_projComponents J).subset fun Q hQ => by
      by_contra h
      exact hQ (dif_neg h))

theorem cast_projCycle_apply {J Q : Ideal (MvPolynomial (Fin N) k)} [Q.IsPrime]
    (h : Q ∈ projComponents J) : (projCycle J Q : ℕ∞) = localLength J Q := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  simp only [dif_pos h]
  exact ENat.coe_toNat (localLength_ne_top h.1)

theorem projCycle_apply_of_notMem {J Q : Ideal (MvPolynomial (Fin N) k)}
    (h : Q ∉ projComponents J) : projCycle J Q = 0 := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  exact dif_neg h

def hyperplaneForm (u : Fin N → k) : MvPolynomial (Fin N) k := ∑ j, C (u j) * X j

def hyperplaneSection (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) :
    Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  projCycle (P ⊔ Ideal.span {hyperplaneForm u})

def fixFirstBlock {B : ℕ} (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k) :
    MvPolynomial (Fin B × Fin N) k :=
  aeval (fun p : Fin (B + 1) × Fin N =>
    (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
      Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) f

end GlobalTheory.ChowHt

namespace GlobalTheory.Published

open GlobalTheory.ChowHt

def ChowFormExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
    I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
    (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
      MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f ∧
      ∀ g : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f

def ChowFormIntExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f ∧
      ∀ g : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f

def ChowFormHyperplaneSection : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 + 1 : ℕ) →
    ∀ u : Fin N → k, hyperplaneForm u ∉ P →
    ∀ (dl : ℕ) (f : MvPolynomial (Fin (e + 1 + 1) × Fin N) k), IsChowFormInt P (e + 1) dl f →
    ∀ (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
      (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k),
      (∀ Q ∈ (hyperplaneSection P u).support, IsChowFormInt Q e (d Q) (g Q)) →
      ∃ c : k, c ≠ 0 ∧
        fixFirstBlock u f = C c * (hyperplaneSection P u).prod (fun Q m => g Q ^ m)

theorem chowFormExists_iff : ChowFormExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
      I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
      (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
        MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f := by
  refine ⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left,
    fun h k _ _ N D I h1 h2 h3 => ?_⟩
  obtain ⟨f, hf⟩ := h k N D I h1 h2 h3
  exact ⟨f, hf, fun g hg => (hf.isChowFormInt.unique hg.isChowFormInt).2⟩

theorem chowFormIntExists_iff : ChowFormIntExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
      P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f := by
  refine ⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left,
    fun h k _ _ N D I h1 h2 h3 => ?_⟩
  obtain ⟨f, hf⟩ := h k N D I h1 h2 h3
  exact ⟨f, hf, fun g hg => (hf.unique hg).2⟩

end GlobalTheory.Published
