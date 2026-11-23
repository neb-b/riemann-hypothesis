module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharp
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem sch_sharp {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - root a b) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  classical
  have hne : a ≠ b := hab.ne
  have hΛ : lowK ε (lam - root a b) = lowK ε lam - root a b := by
    unfold lowK; abel
  have hW' : IsKIrrHW ε E (lowK ε (lam - root a b)) W := by rw [hΛ]; exact hW
  have hmono' := ssh_strictAnti hmono hh h2 hE a b hW'
  obtain ⟨z, hzW, -, hz0, hzK⟩ := lowFock_exists ε hE hmono' hW'
  have hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - root a b - rhoC ε) + rhoHol ε) z := hzK
  have hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z := by
    obtain ⟨z0, hz0eq⟩ := LinearMap.mem_range.mp hzW
    rw [ssh_casimir_eT, ← hz0eq]
    clear hz0eq
    induction z0 using TensorProduct.induction_on with
    | zero => simp
    | tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  have hD2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas
  have hval : nsq (lam - root a b - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam = 2 - 2 * (lam a - lam b) := by
    rw [sub_add_cancel, ssh_nsq_sub_root lam hne]
    unfold casVal
    ring
  have hgap : h ≤ lam a - lam b := by
    have := hh a b hε
    rwa [abs_of_pos (sub_pos.mpr (hmono hab))] at this
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef
  have key : tform z ((2 : ℂ) • (D * D) z) = ((2 - 2 * (lam a - lam b) : ℝ) : ℂ) * tform z z := by
    rw [hD2, tform_smul_right, ← hval]
    push_cast
    ring
  rw [tform_smul_right, Module.End.mul_apply, ← tform_D hU] at key
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have p1 := tform_self_re_nonneg (D z)
  have p2 := tform_self_re_pos hz0
  have hneg : (2 - 2 * (lam a - lam b)) < 0 := by linarith
  nlinarith

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev L2 (ε : Fin n → Bool) : Type := Lp ℂ 2 (Formalism.REAL.muG ε)

def rregG (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) : L2 ε →L[ℂ] L2 ε :=
  if hm : MeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y) (Formalism.REAL.muG ε) (Formalism.REAL.muG ε) then
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : Formalism.REAL.UJ ε => x * y) hm).toContinuousLinearMap
  else 1

def rreg (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : L2 ε →L[ℂ] L2 ε :=
  if h : ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g then rregG ε h.choose else 1

def toL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : L2 ε :=
  if h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) then h.toLp _ else 0

theorem signature_matrix_sq (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem exists_unitary_preimage (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have hJ := signature_matrix_sq ε
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ (Formalism.REAL.Jm ε) g, h, hJ]
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp hl
    | (letI := Matrix.invertibleOfLeftInverse g _ hl; exact mul_invOf_self g)
  exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, hr, hl⟩, h⟩, rfl⟩

theorem unitary_matrix_injective (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

theorem unitary_matrix_mem_set (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat y ∈ UJset ε := y.2

theorem continuous_unitary_matrix (ε : Fin n → Bool) :
    Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := Units.continuous_val.comp continuous_subtype_val

theorem rightRegular_unitary_eq (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  unfold rreg
  rw [dif_pos h, unitary_matrix_injective ε h.choose_spec]

theorem rightRegularGroup_eq_comp (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y) (measurePreserving_mul_right ε y) f := by
  unfold rregG
  rw [dif_pos (measurePreserving_mul_right ε y)]
  rfl

theorem toL2_eq_memLp_toLp (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε F = hF.toLp _ := by
  unfold toL2
  exact dif_pos hF

theorem toL2_eq_zero_of_not_memLp (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ¬ MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε F = 0 := by
  unfold toL2
  exact dif_neg hF

theorem rreg_umat_ae (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    (rreg ε (Formalism.MainNotions.S.umat y) f : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun x => f (x * y) := by
  rw [rightRegular_unitary_eq, rightRegularGroup_eq_comp]
  exact Lp.coeFn_compMeasurePreserving _ _

theorem rightRegular_toL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : rreg ε g (toL2 ε F) = toL2 ε (fun x => F (x * g)) := by
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hFy : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) 2
        (Formalism.REAL.muG ε) := hF.comp_measurePreserving (measurePreserving_mul_right ε y)
    rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε (F := fun x => F (x * Formalism.MainNotions.S.umat y)) hFy,
      rightRegular_unitary_eq, rightRegularGroup_eq_comp]
    refine Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
    refine (hF.coeFn_toLp.comp_tendsto
      (measurePreserving_mul_right ε y).quasiMeasurePreserving.tendsto_ae).trans ?_
    exact hFy.coeFn_toLp.symm
  · have hFy : ¬ MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) 2
        (Formalism.REAL.muG ε) := by
      intro h
      apply hF
      have h2 := h.comp_measurePreserving (measurePreserving_mul_right ε y⁻¹)
      have e : ((fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) ∘
          fun x => x * y⁻¹) = fun g => F (Formalism.MainNotions.S.umat g) := by
        funext g
        show F (Formalism.MainNotions.S.umat (g * y⁻¹ * y)) = F (Formalism.MainNotions.S.umat g)
        rw [inv_mul_cancel_right]
      rwa [e] at h2
    rw [toL2_eq_zero_of_not_memLp ε hF, toL2_eq_zero_of_not_memLp ε (F := fun x => F (x * Formalism.MainNotions.S.umat y)) hFy,
      map_zero]

theorem toL2_add_smooth (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε (F + G) = toL2 ε F + toL2 ε G := by
  have hFG : MemLp (fun g : Formalism.REAL.UJ ε => (F + G) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    hF.add hG
  rw [toL2_eq_memLp_toLp ε hFG, toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG]
  exact MemLp.toLp_add hF hG

theorem toL2_smul_smooth (ε : Fin n → Bool) (c : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    toL2 ε (c • F) = c • toL2 ε F := by
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hcF : MemLp (fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
      hF.const_smul c
    rw [toL2_eq_memLp_toLp ε hcF, toL2_eq_memLp_toLp ε hF]
    exact MemLp.toLp_const_smul c hF
  · by_cases hc : c = 0
    · subst hc
      rw [zero_smul, zero_smul]
      have h0 : MemLp (fun g : Formalism.REAL.UJ ε => (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) (Formalism.MainNotions.S.umat g)) 2
          (Formalism.REAL.muG ε) := MemLp.zero
      rw [toL2_eq_memLp_toLp ε h0]
      exact Lp.ext (h0.coeFn_toLp.trans (Lp.coeFn_zero ..).symm)
    · have hcF : ¬ MemLp (fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
        intro h
        apply hF
        have h2 := h.const_smul c⁻¹
        have e : (c⁻¹ • fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) =
            fun g => F (Formalism.MainNotions.S.umat g) := by
          funext g
          simp only [Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
        rwa [e] at h2
      rw [toL2_eq_zero_of_not_memLp ε hcF, toL2_eq_zero_of_not_memLp ε hF, smul_zero]

theorem inner_toL2_eq_theta_pairing (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    inner ℂ (toL2 ε F) (toL2 ε G) =
      ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (F (Formalism.MainNotions.S.umat g)) * G (Formalism.MainNotions.S.umat g) ∂(Formalism.REAL.muG ε) := by
  rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with g h1 h2
  simp only [h1, h2, RCLike.inner_apply]
  exact mul_comm _ _

end ReciprocityTheory.ChartRestriction.DS
end
end

