module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.LowerInv

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExt
section
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem polyExt_of (hp : PI.PolyCoef) (hu : PI.UnitaryDense) : PolyExt := by
  intro N H _ _ σ S hσ hfin hS
  classical
  let d := Module.finrank ℂ S
  let b : OrthonormalBasis (Fin d) ℂ S := stdOrthonormalBasis ℂ S
  have hc : ∀ i j : Fin d, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ ((b i : S) : H) (σ g ((b j : S) : H)) * g.det ^ k =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P :=
    fun i j => hp N H σ S hσ hfin hS ((b j : S) : H) (b j).2 ((b i : S) : H)
  choose k P hkP using hc
  let K : ℕ := ∑ p : Fin d × Fin d, k p.1 p.2
  have hk : ∀ i j, k i j ≤ K := fun i j =>
    Finset.single_le_sum (f := fun p : Fin d × Fin d => k p.1 p.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  let Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) ℂ := fun i j => P i j * detPoly N ^ (K - k i j)
  have hQ : ∀ g ∈ Kset (allPos N), ∀ i j,
      evM g (Q i j) = g.det ^ K * ⟪((b i : S) : H), σ g ((b j : S) : H)⟫_ℂ := by
    intro g hg i j
    have e1 : evM g (Q i j) = evM g (P i j) * g.det ^ (K - k i j) := by
      rw [← pe_evM_detPoly g]
      simp only [Q, evM, map_mul, map_pow]
    rw [e1, show evM g (P i j) = _ from (hkP i j g hg).symm, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hk i j), mul_comm]
  let Pm : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin d) (Fin d) ℂ := fun g => Matrix.of fun i j => evM g (Q i j)
  let Pl : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S) := fun g => Matrix.toLin b.toBasis b.toBasis (Pm g)
  have hA : ∀ g ∈ Kset (allPos N), ∀ x : S, ((Pl g x : S) : H) = g.det ^ K • σ g (x : H) := by
    intro g hg x
    have key : S.subtype ∘ₗ Pl g = g.det ^ K • ((σ g : H →ₗ[ℂ] H) ∘ₗ S.subtype) := by
      refine b.toBasis.ext fun j => ?_
      have hmem : σ g ((b j : S) : H) ∈ S := hS g hg _ (b j).2
      have hsum := b.sum_repr' (⟨σ g ((b j : S) : H), hmem⟩ : S)
      have hsumH := congrArg (fun y : S => (y : H)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hsumH
      show ((Matrix.toLin b.toBasis b.toBasis (Pm g) (b.toBasis j) : S) : H) =
        g.det ^ K • σ g ((b.toBasis j : S) : H)
      rw [Matrix.toLin_self]
      simp only [OrthonormalBasis.coe_toBasis, Submodule.coe_sum, Submodule.coe_smul, Pm, Matrix.of_apply]
      conv_rhs => rw [← hsumH]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQ g hg i j, smul_smul]
    exact congrArg (fun f : S →ₗ[ℂ] H => f x) key
  have hPlmul : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pl (g * h) = Pl g ∘ₗ Pl h := by
    intro g hg h hh
    ext x
    rw [LinearMap.comp_apply, hA _ (pe_mul_mem hg hh), hA g hg, hA h hh, hσ.1.2 g hg h hh,
      ContinuousLinearMap.comp_apply, map_smul, smul_smul, Matrix.det_mul, mul_pow]
  have hB : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pm (g * h) = Pm g * Pm h := by
    intro g hg h hh
    apply (Matrix.toLin b.toBasis b.toBasis).injective
    rw [Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
    exact hPlmul g hg h hh
  have hC1 : ∀ h ∈ Kset (allPos N), ∀ g, Pm (g * h) = Pm g * Pm h := by
    intro h hh g
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_right h (Q i j)
    let D := Q' - ∑ r, Q i r * C (Pm h r j)
    have hD : ∀ g', evM g' D = (Pm (g' * h) - Pm g' * Pm h) i j := by
      intro g'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hB u (pe_unitary_mem u hu') h hh, sub_self, Matrix.zero_apply]
    have := hD g
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  have hC2 : ∀ g h, Pm (g * h) = Pm g * Pm h := by
    intro g h
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_left g (Q i j)
    let D := Q' - ∑ r, C (Pm g i r) * Q r j
    have hD : ∀ h', evM h' D = (Pm (g * h') - Pm g * Pm h') i j := by
      intro h'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hC1 u (pe_unitary_mem u hu') g, sub_self, Matrix.zero_apply]
    have := hD h
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  refine ⟨K, Pl, ⟨?_, ?_, ?_⟩, hA⟩
  · intro g h
    show Matrix.toLin b.toBasis b.toBasis (Pm (g * h)) = _
    rw [hC2, Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
  · ext x
    rw [hA 1 (pe_one_mem N), hσ.1.1]
    simp
  · intro x y
    let fL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
      (innerₛₗ ℂ y).comp ((LinearMap.applyₗ x).comp (Matrix.toLin b.toBasis b.toBasis).toLinearMap)
    refine ⟨∑ i, ∑ j, Q i j * C (fL (Matrix.single i j 1)), fun g => ?_⟩
    have hf : ⟪y, Pl g x⟫_ℂ = fL (Pm g) := rfl
    rw [hf, Matrix.matrix_eq_sum_single (Pm g)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, evM, map_mul, eval_C]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (Pm g i j) = Pm g i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    rfl

end PI.WMI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.TorusEigenvalueFormula
section
noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem lambda_integrality : LamInt := by
  intro N Λ H _ _ σ v hU hv hw a
  have hfun : (fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin N → ℝ) b : ℝ) : ℂ) * Complex.I))
      = fun _ => (1 : ℂ) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [hb]
  have hmem := lowerInv_torus_mem (N := N) (Pi.single a (2 * Real.pi))
  have h := hw (Pi.single a (2 * Real.pi)) hmem
  rw [hfun, Matrix.diagonal_one, hU.1.1] at h
  have hsum : (∑ b, Λ b * (Pi.single a (2 * Real.pi) : Fin N → ℝ) b) = Λ a * (2 * Real.pi) := by
    simp [Pi.single_apply]
  rw [hsum] at h
  have he : Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    apply hv
    have h2 : (1 - Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) • v = 0 := by
      rw [sub_smul, one_smul, ← h]
      simp
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, ?_⟩
  have hpi : (2 * (Real.pi : ℂ)) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (Λ a : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

theorem torus_eigenvalue_formula : TorusEig := by
  intro N Λ H _ _ σ S K P hU hstab hPσ v0 hw θ x
  have hwt : σ (torus (-θ)) (v0 : H) =
      Complex.exp (((∑ a, Λ a * (-θ) a : ℝ) : ℂ) * Complex.I) • (v0 : H) :=
    hw (-θ) (lowerInv_torus_mem (-θ))
  have hdet : (torus θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I) := by
    rw [torus, Matrix.det_diagonal]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  rw [Submodule.coe_inner, hPσ (torus θ) (lowerInv_torus_mem θ) x, inner_smul_right,
    lowerInv_adj hU θ, hwt, inner_smul_left, ← Submodule.coe_inner, hdet, ← Complex.exp_nat_mul,
    ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  simp only [Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  ring_nf
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end PI.WMI
end
end

