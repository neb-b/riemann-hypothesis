module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_umat_one (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := by
  have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  rw [e]
  exact (sigLam_isURepOn hgap hP hv₀).1.1

theorem sigLam_umat_mul (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (a b : Formalism.REAL.UJ ε) :
    sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat (a * b)) = (sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat a)).comp (sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat b)) := by
  have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
  rw [e]
  exact (sigLam_isURepOn hgap hP hv₀).1.2 _ (umat_mem_UJset _ a) _ (umat_mem_UJset _ b)

theorem sigLam_umat_iso (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (g : Formalism.REAL.UJ ε)
    (v : Hlam ε Ψ v₀) : ‖sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ :=
  (sigLam_isURepOn hgap hP hv₀).2.1 _ (umat_mem_UJset _ g) v

theorem sigLam_memLp_of_ne (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (w₀ x₀ : Hlam ε Ψ v₀)
    (hx₀ : x₀ ≠ 0)
    (h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) x₀⟫_ℂ) 2 (Formalism.REAL.muG ε))
    (x : Hlam ε Ψ v₀) :
    MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) x⟫_ℂ) 2 (Formalism.REAL.muG ε) :=
  GraphTrick.memLp_of_ne (μ := Formalism.REAL.muG ε) (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g))
    (measurePreserving_mul_right ε)
    (sigLam_umat_one hgap hP hv₀) (sigLam_umat_mul hgap hP hv₀)
    (sigLam_umat_iso hgap hP hv₀) (Formalism.MainNotions.BridgeCSchur.irr_of (sigLam_irred hgap hP hv₀)) w₀ x₀ hx₀ h0 x

theorem inner_sigLam_umat (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (y z : Hlam ε Ψ v₀)
    (g : Formalism.REAL.UJ ε) :
    ⟪y, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) z⟫_ℂ = inner ℂ (y : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) (z : L2 ε)) := by
  rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ (umat_mem_UJset _ g)]

theorem coef_memLp_all (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : Hlam ε Ψ v₀) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      inner ℂ (uniformisationL2 ε Ψ v₀ T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε))) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Hlam ε Ψ v₀, (w₀ : L2 ε) = uniformisationL2 ε Ψ v₀ T.w := ⟨⟨_, datumEmbedding_mem_Hlam hP T.w⟩, rfl⟩
  have hne : w₀ ≠ 0 := by
    intro h
    apply datumEmbedding_highest_ne_zero hgap hP hv₀
    rw [← hw₀, h]
    rfl
  have e0 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w₀⟫_ℂ) =
      fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * jfun Ψ T.w T.w (Formalism.MainNotions.S.umat g) := by
    funext g
    rw [inner_sigLam_umat hgap hP hv₀, hw₀, formulaF hgap hP hv₀ (umat_mem_UJset _ g)]
    rfl
  have h0 : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w₀⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    rw [e0]
    exact ((datumFunction_isSmoothL2 hP T.w T.w).2 []).const_mul _
  have h1 := sigLam_memLp_of_ne hgap hP hv₀ w₀ w₀ hne h0 x
  have e1 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) x⟫_ℂ) =
      fun g => inner ℂ (uniformisationL2 ε Ψ v₀ T.w) (rreg ε (Formalism.MainNotions.S.umat g) (x : L2 ε)) := by
    funext g
    rw [inner_sigLam_umat hgap hP hv₀, hw₀]
  rw [e1] at h1
  exact h1

theorem sqInt_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Formalism.MainNotions.S.IsSqIntOn ε (sigLam ε Ψ v₀) := by
  intro v w
  show MemLp (fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) v⟫_ℂ) 2 (Formalism.REAL.muG ε)
  by_cases hw : w = 0
  · have e : (fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) v⟫_ℂ) = 0 := by
      funext g
      rw [hw, inner_zero_left]
      rfl
    rw [e]
    exact (Lp.memLp (0 : Lp ℂ 2 (Formalism.REAL.muG ε))).ae_eq (Lp.coeFn_zero ℂ 2 _)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Hlam ε Ψ v₀, (w₀ : L2 ε) = uniformisationL2 ε Ψ v₀ T.w := ⟨⟨_, datumEmbedding_mem_Hlam hP T.w⟩, rfl⟩
  have hne : w₀ ≠ 0 := by
    intro h
    apply datumEmbedding_highest_ne_zero hgap hP hv₀
    rw [← hw₀, h]
    rfl
  have hF : MemLp (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
    have e1 : (fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w⟫_ℂ) =
        fun g => inner ℂ (uniformisationL2 ε Ψ v₀ T.w) (rreg ε (Formalism.MainNotions.S.umat g) (w : L2 ε)) := by
      funext g
      rw [inner_sigLam_umat hgap hP hv₀, hw₀]
    rw [e1]
    exact coef_memLp_all hgap hP hv₀ w
  have hinv := (hF.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e2 : star ((fun g : Formalism.REAL.UJ ε => ⟪w₀, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w⟫_ℂ) ∘ Inv.inv) =
      fun g : Formalism.REAL.UJ ε => ⟪w, sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g) w₀⟫_ℂ := by
    funext g
    have hs : star (sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g⁻¹)) = sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g⁻¹⁻¹) :=
      GraphTrick.star_eq (ρ := fun g : Formalism.REAL.UJ ε => sigLam ε Ψ v₀ (Formalism.MainNotions.S.umat g))
        (sigLam_umat_one hgap hP hv₀) (sigLam_umat_mul hgap hP hv₀) (sigLam_umat_iso hgap hP hv₀) g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e2] at hinv
  exact sigLam_memLp_of_ne hgap hP hv₀ w w₀ hne hinv v

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigZeroDecay_one_le_hs {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (i : Fin n) : 1 ≤ S7.hs g := by
  unfold S7.hs
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (gᴴ * Jm ε * g) i i = Jm ε i i := by rw [hg']
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1
  have key : ‖(if ε i = true then (1 : ℂ) else -1)‖ ≤ ∑ x, ‖g x i‖ ^ 2 := by
    rw [← h1]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, norm_mul, norm_star]
    split_ifs <;> simp [sq]
  have hrow : ∑ x, ‖g x i‖ ^ 2 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => ‖g a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i)
  have hn : ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by
    split_ifs <;> simp
  linarith

theorem sigZeroDecay_real {h c s N G : ℝ} (hh : 0 < h) (hc : 1 ≤ c) (hN : 0 < N)
    (hG : 0 < G) (hGle : G ≤ N * Real.exp s) :
    Real.exp (-(h / 8) * min (s ^ 2) (s / c)) ≤
      (Real.exp (h / (8 * c)) * N ^ (h / (8 * c))) * G ^ (-(h / (8 * c))) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have ha : 0 < h / (8 * c) := by positivity
  have hlog : Real.log G ≤ Real.log N + s := by
    have h1 := Real.log_le_log hG hGle
    rwa [Real.log_mul hN.ne' (Real.exp_pos s).ne', Real.log_exp] at h1
  have hcs : c * (s / c) = s := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hmin : s - 1 ≤ c * min (s ^ 2) (s / c) := by
    rcases min_cases (s ^ 2) (s / c) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg s), sq_nonneg (s - 1)]
    · rw [h1, hcs]
      linarith
  have hh8 : h / 8 = c * (h / (8 * c)) := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hG, ← Real.exp_add, ← Real.exp_add,
    Real.exp_le_exp, hh8]
  nlinarith [mul_le_mul_of_nonneg_left hmin ha.le, mul_le_mul_of_nonneg_left hlog ha.le]

theorem dec_gN_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {h : ℝ} (hq : 1 ≤ S7.q0 ε)
    (hdec : ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
        Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))))
    (v v' : T.V) :
    ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v))‖ ≤
        C * Real.sqrt (S7.hs g) ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))))) := by

  have hqn : S7.q0 ε ≤ n := by
    unfold S7.q0 pOf
    exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans_eq (Finset.card_fin n))
  have hn : 0 < n := lt_of_lt_of_le one_pos (hq.trans hqn)
  have hG1 : ∀ g ∈ UJset ε, 1 ≤ Real.sqrt (S7.hs g) := fun g hg =>
    Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs hg ⟨0, hn⟩)
  set c := Real.sqrt (2 * (S7.q0 ε : ℝ)) with hcdef
  have hc : 1 ≤ c := by
    rw [hcdef, Real.one_le_sqrt]
    have : (1 : ℝ) ≤ S7.q0 ε := by exact_mod_cast hq
    linarith
  rcases le_or_gt h 0 with hh | hh
  ·
    refine ⟨‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖, fun g hg => ?_⟩
    have hiso : ‖rreg ε g (uniformisationL2 ε Ψ v₀ v)‖ = ‖uniformisationL2 ε Ψ v₀ v‖ := (rreg_isURepOn ε).2.1 g hg _
    have hpow : 1 ≤ Real.sqrt (S7.hs g) ^ (-(h / (8 * c))) := by
      refine Real.one_le_rpow (hG1 g hg) ?_
      have : h / (8 * c) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hh (by linarith)
      linarith
    calc ‖inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v))‖
        ≤ ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖rreg ε g (uniformisationL2 ε Ψ v₀ v)‖ := norm_inner_le_norm _ _
      _ = ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖ := by rw [hiso]
      _ ≤ ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖ * Real.sqrt (S7.hs g) ^ (-(h / (8 * c))) :=
          le_mul_of_one_le_right (by positivity) hpow
  ·
    refine ⟨‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
      (Real.exp (h / (8 * c)) * Real.sqrt n ^ (h / (8 * c))), fun g hg => ?_⟩
    obtain ⟨k, X, hX, rfl⟩ := S7.polar_exists hg
    have hd := dec_sigLam hgap hP hv₀ hdec k hX v v'
    set s := Real.sqrt (S7.hs X) with hsdef
    have hsX : S7.hs X = s ^ 2 := (Real.sq_sqrt (S7.hs_nonnegVG X)).symm
    have hN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hGpos : 0 < Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) :=
      lt_of_lt_of_le one_pos (hG1 _ hg)
    have hGle : Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) ≤ Real.sqrt n * Real.exp s := by
      rw [S7.hs_kmulVG]
      have h2 : S7.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp s) ^ 2 := by
        have e2 : Real.exp s ^ 2 = Real.exp (2 * s) := by
          rw [← Real.exp_nat_mul]; norm_num
        have := S7.hs_exp_leVG X
        rw [← hsdef] at this
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), e2]
        exact this
      calc Real.sqrt (S7.hs (NormedSpace.exp X)) ≤ Real.sqrt ((Real.sqrt n * Real.exp s) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = Real.sqrt n * Real.exp s := Real.sqrt_sq (by positivity)
    have hr := sigZeroDecay_real hh hc hN hGpos hGle
    rw [← hsX] at hr
    have hM : 0 ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ := by positivity
    calc _ ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
          Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) := hd
      _ ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
          ((Real.exp (h / (8 * c)) * Real.sqrt n ^ (h / (8 * c))) *
            Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) ^ (-(h / (8 * c)))) :=
          mul_le_mul_of_nonneg_left hr hM
      _ = _ := by ring

end ReciprocityTheory.ChartRestriction.DS
end
end

