module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH
section
open Polynomial UpperTheory.V.Z.Sym.Wt

theorem UpperTheory.V.Z.Sym.Wt.finMH :
    UpperTheory.V.Z.Sym.Wt.FinMH := by
  intro K _ d n
  have hle : MH d n ≤ MvPolynomial.restrictDegree (K × Fin d) ℂ (∑ k, n k) := by
    intro P hP
    rw [MvPolynomial.mem_restrictDegree]
    rintro m hm ⟨k, i⟩
    have h := (memMH K d n P).1 hP m hm k
    calc m (k, i) ≤ ∑ j, m (k, j) :=
          Finset.single_le_sum (f := fun j => m (k, j)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
      _ = n k := h
      _ ≤ ∑ k, n k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HqThree
section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem hs_opt {σ : Type} [Fintype σ] [DecidableEq σ] (x : Option σ → ℂ) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ (j + 1)) =
      x none * MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ j) +
        MvPolynomial.eval (x ∘ some) (MvPolynomial.hsymm σ ℂ (j + 1)) := by
  have ev : ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y : τ → ℂ) (n : ℕ),
      MvPolynomial.eval y (MvPolynomial.hsymm τ ℂ n) = ∑ s : Sym τ n, ((s : Multiset τ).map y).prod := by
    intro τ _ _ y n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.hsymm, map_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl (fun a _ => MvPolynomial.eval_X _)
  rw [ev, ev, ev]
  rw [← (symOptionSuccEquiv (α := σ) (n := j)).symm.sum_comp, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((none ::ₘ (s : Multiset (Option σ))).map x).prod = _
    rw [Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((Multiset.map some (s : Multiset σ)).map x).prod = _
    rw [Multiset.map_map]

private theorem hs_succ {d : ℕ} (x : Fin (d + 1) → ℂ) (k : Fin (d + 1)) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ (j + 1)) =
      x k * MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ j) +
        MvPolynomial.eval (x ∘ k.succAbove) (MvPolynomial.hsymm (Fin d) ℂ (j + 1)) := by
  have e1 : ∀ n, MvPolynomial.hsymm (Fin (d + 1)) ℂ n =
      MvPolynomial.rename (finSuccEquiv' k).symm (MvPolynomial.hsymm (Option (Fin d)) ℂ n) :=
    fun n => (MvPolynomial.rename_hsymm (Option (Fin d)) ℂ n (finSuccEquiv' k).symm).symm
  rw [e1, e1, MvPolynomial.eval_rename, MvPolynomial.eval_rename, hs_opt]
  have h1 : (x ∘ (finSuccEquiv' k).symm) none = x k := by simp
  have h2 : (x ∘ (finSuccEquiv' k).symm) ∘ some = x ∘ k.succAbove := by
    ext i
    simp
  rw [h1, h2]

theorem UpperTheory.V.Z.Sym.Wt.hqThree :
    UpperTheory.V.Z.Sym.Wt.HqThree := by
  intro j a b
  have hv : (![a, 1, b] ∘ (1 : Fin 3).succAbove) = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  rw [hs_succ ![a, 1, b] 1 j, hv, UpperTheory.V.Z.Sym.Wt.hqTwo]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
  ring
end

