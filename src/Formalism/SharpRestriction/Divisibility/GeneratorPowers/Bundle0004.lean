module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CPfSym
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

end Sym

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

end Sym

namespace Sym

variable {k : Type} [CommRing k]

private theorem const_subst_lemma {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (g : MvPowerSeries σ k) :
    constantCoeff (subst a g) = constantCoeff g := by
  have hA : HasSubst a := by
    first
      | exact hasSubst_of_constantCoeff_zero ha
      | exact HasSubst.of_constantCoeff_zero' ha
      | exact hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
      | exact HasSubst.of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
  rw [constantCoeff_subst hA, finsum_eq_single _ (0 : σ →₀ ℕ)]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact he (Finsupp.ext fun t => by simpa using hc t)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · rw [map_pow, ha s, zero_pow hs]

theorem const_ev {m n d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p q, constantCoeff (a p q) = 0) (g : PS k m d) :
    constantCoeff (ev a g) = constantCoeff g := by
  unfold ev
  exact const_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) g

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinD
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem finiteShort_holds : FiniteShortStatement := by
  intro d G hG B
  obtain ⟨R, hRu, hGR⟩ := whiten_holds d G hG
  set A : ℝ := ∑ i, ∑ j, |R⁻¹ i j| with hA
  set M : ℤ := ⌈A * (1 + B)⌉ with hM
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-M) M) fun _ => Set.finite_Icc _ _).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro i
  set cv : Fin d → ℝ := fun i => (c i : ℝ) with hcv
  set y : Fin d → ℝ := R *ᵥ cv with hy
  have hyy : ∑ j, y j * y j ≤ B := by
    have e : cv ⬝ᵥ (G *ᵥ cv) = y ⬝ᵥ y := by
      rw [hGR, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [e] at hc
    simpa [dotProduct] using hc
  have hyj : ∀ j, |y j| ≤ 1 + B := by
    intro j
    have h1 : y j * y j ≤ ∑ k, y k * y k :=
      Finset.single_le_sum (f := fun k => y k * y k) (fun k _ => mul_self_nonneg (y k)) (Finset.mem_univ j)
    have h2 : |y j| ≤ 1 + y j * y j := by
      nlinarith [abs_nonneg (y j), sq_abs (y j), abs_mul_abs_self (y j)]
    linarith
  have hB : 0 ≤ 1 + B := (abs_nonneg _).trans (hyj i)
  have hcvR : cv = R⁻¹ *ᵥ y := by
    rw [hy, mulVec_mulVec, nonsing_inv_mul R hRu, one_mulVec]
  have hci : |cv i| ≤ A * (1 + B) := by
    have e : cv i = ∑ j, R⁻¹ i j * y j := by
      rw [hcvR]
      rfl
    rw [e]
    calc |∑ j, R⁻¹ i j * y j| ≤ ∑ j, |R⁻¹ i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |R⁻¹ i j| * |y j| := by simp only [abs_mul]
      _ ≤ ∑ j, |R⁻¹ i j| * (1 + B) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hyj j) (abs_nonneg _)
      _ = (∑ j, |R⁻¹ i j|) * (1 + B) := by rw [Finset.sum_mul]
      _ ≤ A * (1 + B) := by
          refine mul_le_mul_of_nonneg_right ?_ hB
          exact Finset.single_le_sum (f := fun i => ∑ j, |R⁻¹ i j|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hle : ((|c i| : ℤ) : ℝ) ≤ (M : ℝ) := by
    rw [Int.cast_abs]
    exact hci.trans (Int.le_ceil _)
  have hle' : |c i| ≤ M := by exact_mod_cast hle
  exact abs_le.1 hle'

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

