module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PDivisibleGroupsOverOC
section
noncomputable section

open CategoryTheory Ideal
open scoped TensorProduct

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup

def hodgeTateSubspace {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] (C : Type) [Field C]
    [Algebra O C] (G : PDivGroup p O) : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) :=
  LinearMap.ker (G.hodgeTateLinear.baseChange C)

def PDivisibleGroupsOverOC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x ∈ hodgeTateSubspace C G, (f.baseChange O).baseChange C x ∈ hodgeTateSubspace C H) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] (Fin h → ℤ_[p])))),
        ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
          ∀ x, x ∈ hodgeTateSubspace C G ↔ (e.toLinearMap.baseChange O).baseChange C x ∈ W

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
section
noncomputable section

open CategoryTheory Ideal
open scoped TensorProduct

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup

def ScholzeWeinsteinB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x, G.hodgeTateLinear x = 0 → H.hodgeTateLinear (f.baseChange O x) = 0) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule O (O ⊗[ℤ_[p]] (Fin h → ℤ_[p]))),
        (∀ (c : O) (x : O ⊗[ℤ_[p]] (Fin h → ℤ_[p])), c ≠ 0 → c • x ∈ W → x ∈ W) →
          ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
            ∀ x, G.hodgeTateLinear x = 0 ↔ e.toLinearMap.baseChange O x ∈ W

end GlobalTheory.Published
end
end

