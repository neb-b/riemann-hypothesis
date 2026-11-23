module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Weier
section
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.weier :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ϖ : O), Irreducible ϖ → ∀ f : O⟦X⟧, f ≠ 0 →
      ∃ (m : ℕ) (P : Polynomial O) (U : O⟦X⟧), mu f = m ∧ P.IsDistinguishedAt (maximalIdeal O) ∧ P.natDegree = lam f ∧
        IsUnit U ∧ f = C ϖ ^ m * (P : O⟦X⟧) * U := by
  intro O _ _ _ _ ϖ hϖ f hf
  have htop : mu f ≠ ⊤ := fun h => hf (mu_eq_top_iff.mp h)
  have hM := mu_dvd O ϖ hϖ
  obtain ⟨m, hmf⟩ : ∃ m : ℕ, (m : ℕ∞) = mu f := ⟨(mu f).toNat, ENat.coe_toNat htop⟩
  obtain ⟨g, hgf⟩ := ((hM f).1 m).mp hmf.le
  subst hgf
  obtain ⟨-, hzero, hlam, hshift⟩ := hM g
  obtain ⟨hmu, hl⟩ := hshift m
  have hg0 : mu g = 0 := by
    have h1 : (m : ℕ∞) + mu g = (m : ℕ∞) + 0 := by rw [add_zero, ← hmu, hmf]
    exact (WithTop.add_left_cancel (ENat.coe_ne_top m) h1)
  have hmap : (map (residue O)) g ≠ 0 := hzero.mp hg0
  obtain ⟨P, U, H⟩ := exists_isWeierstrassFactorization hmap
  refine ⟨m, P, U, hmf.symm, H.isDistinguishedAt, ?_, H.isUnit, ?_⟩
  · rw [hl, hlam hg0, H.natDegree_eq_toNat_order_map]
  · rw [mul_assoc, ← H.eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.adicComplete
section
open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

theorem UpperTheory.V.abelian₂.adicComplete :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O],
      IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := by
  intro O _ _ _
  have key : ∀ (x y : O⟦X⟧) (n : ℕ),
      x ≡ y [SMOD (maximalIdeal O⟦X⟧) ^ n • (⊤ : Submodule O⟦X⟧ O⟦X⟧)] ↔
        ∀ i, coeff i x - coeff i y ∈ maximalIdeal O ^ (n - i) := by
    intro x y n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow]
    simp only [map_sub]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    ext i
    apply eq_of_sub_mem_pow (maximalIdeal O)
    intro n
    have h := (key x 0 (n + i)).1 (hx (n + i)) i
    simpa using h
  · intro f hf
    have hc : ∀ i, ∃ L : O, ∀ n, coeff i (f (n + i)) - L ∈ maximalIdeal O ^ n := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal O) (M := O)
        (fun m => coeff i (f (m + i))) (by
          intro m n hmn
          have h := (key _ _ (m + i)).1 (hf (Nat.add_le_add_right hmn i)) i
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
          simpa using h)
      refine ⟨L, fun n => ?_⟩
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
      exact h
    choose L hL using hc
    refine ⟨PowerSeries.mk L, fun n => ?_⟩
    rw [key]
    intro i
    rw [coeff_mk]
    rcases le_or_gt i n with hin | hin
    · have h := hL i (n - i)
      rwa [Nat.sub_add_cancel hin] at h
    · rw [Nat.sub_eq_zero_of_le hin.le, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
end

