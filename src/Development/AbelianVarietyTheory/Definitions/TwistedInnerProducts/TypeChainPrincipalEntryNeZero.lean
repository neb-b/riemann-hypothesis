module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

@[expose] public section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section A
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

variable [MeasurableSpace k] [BorelSpace k]


omit [DecidableEq n] in
theorem hat_coset {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : ε ∈ 𝒪[k]) (y₀ : n → k) {η : n → k} (hη : ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n 1) (Submodule.Quotient.mk y₀)) η = ψ (ε * (η ⬝ᵥ y₀)) := by
  have := hν.1
  have := secondCountable k
  unfold hat
  rw [← integral_add_left_eq_self _ y₀]
  have e : ∀ y : n → k, cosetInd (box n 1) (Submodule.Quotient.mk y₀) (y₀ + y) * (ψ (ε * (η ⬝ᵥ (y₀ + y))) : ℂ) =
      (Set.pi Set.univ fun _ => (𝒪[k] : Set k)).indicator (fun _ => (ψ (ε * (η ⬝ᵥ y₀)) : ℂ)) y := fun y => by
    have hy : (y₀ + y ∈ {y' : n → k | Submodule.Quotient.mk (p := box n 1) y' = Submodule.Quotient.mk y₀}) ↔
        y ∈ Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
      simp [Submodule.Quotient.eq, mem_box, Valuation.mem_integer_iff]
    by_cases h : y ∈ Set.pi Set.univ fun _ => (𝒪[k] : Set k)
    · have hi : ε * (η ⬝ᵥ y) ∈ 𝒪[k] := mul_mem hε (sum_mem fun i _ => mul_mem (hη i) (h i trivial))
      rw [cosetInd, Set.indicator_of_mem (hy.2 h), Set.indicator_of_mem h, dotProduct_add, mul_add,
        AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]
      simp
    · rw [cosetInd, Set.indicator_of_notMem (mt hy.1 h), Set.indicator_of_notMem h, zero_mul]
  simp only [e]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_int k).measurableSet), Measure.real,
    Measure.pi_pi]
  simp [hν.2]


end A

section B
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

def wt (ϖ : kˣ) : n ⊕ Fin c → k := Sum.elim (fun _ => 1) fun i => (ϖ : k) ^ (i.val + 1)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] in
theorem wt_ne_zero (ϖ : kˣ) (i : n ⊕ Fin c) : wt ϖ i ≠ 0 := by
  rcases i with i | i <;> simp [wt]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_val (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) : (typeFrame ϖ o).bas.val = diagonal (wt ϖ) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← diagonal_one, fromBlocks_diagonal]; congr

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_inv (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ o).bas⁻¹).val = diagonal fun i => (wt ϖ i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_val, diagonal_mul_diagonal, ← diagonal_one]
  congr; funext i; exact mul_inv_cancel₀ (wt_ne_zero ϖ i)


end B

section C
variable [MeasurableSpace k] [BorelSpace k] {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]


end C

section D
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]


end D

end GlobalTheory.StepData.Model
