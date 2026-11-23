module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReducePosDef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplReducePosDef

theorem sum_mul_symplCons {n : ℕ} (c : ℝ) (x : Fin n ⊕ Fin n → ℝ)
    (F : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    ∑ p, F p * symplCons c 0 x p =
      F (Sum.inl 0) * c + ∑ q, F (Sum.map Fin.succ Fin.succ q) * x q := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, symplCons]
  ring

end PSymplReducePosDef


open PSymplReducePosDef in
theorem SymplReducePosDef.proof : SymplReducePosDef.Statement := by
  intro n H hH
  have hsymm : ∀ i j, H j i = H i j := fun i j => by
    simpa using hH.isHermitian.apply i j
  have hpos : 0 < H (Sum.inl 0) (Sum.inl 0) := hH.diag_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    simp only [symplReduce, star_trivial]
    rw [hsymm (Sum.map Fin.succ Fin.succ a), hsymm (Sum.map Fin.succ Fin.succ a) (Sum.inl 0),
      hsymm (Sum.inl 0) (Sum.map Fin.succ Fin.succ b)]
    ring
  · intro x hx
    simp only [star_trivial]
    set h := H (Sum.inl 0) (Sum.inl 0) with hh
    set S := ∑ b, H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) * x b with hS
    set Q := ∑ a, (∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b) * x a
      with hQ
    have hT : ∑ a, x a * H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = S := by
      rw [hS]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hsymm]; ring
    have hy : symplCons (-(S / h)) 0 x ≠ 0 := by
      intro hz
      apply hx
      funext q
      have := congrFun hz (Sum.map Fin.succ Fin.succ q)
      cases q <;> simpa [symplCons] using this
    have h1 := hH.dotProduct_mulVec_pos hy
    simp only [star_trivial] at h1
    have hL : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        (h * (-(S / h)) + S) * (-(S / h)) + (-(S / h)) * S + Q := by
      rw [dotProduct_comm]
      simp only [dotProduct, mulVec, PSymplReducePosDef.sum_mul_symplCons]
      rw [← hh, ← hS]
      simp only [add_mul, Finset.sum_add_distrib]
      rw [← hQ]
      have hc : ∑ q, H (Sum.map Fin.succ Fin.succ q) (Sum.inl 0) * (-(S / h)) * x q =
          (-(S / h)) * S := by
        rw [← hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [hc]
      ring
    have hRa : ∀ a, ∑ b, (H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
        H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
          h) * x b =
        ∑ b, H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) * x b -
          H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / h * S := by
      intro a
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hR : x ⬝ᵥ (symplReduce H *ᵥ x) = Q - S / h * S := by
      simp only [dotProduct, mulVec, symplReduce]
      rw [← hh]
      simp only [hRa, mul_sub, Finset.sum_sub_distrib]
      rw [hQ, ← hT, Finset.sum_div, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
    have hne : h ≠ 0 := hpos.ne'
    have key : symplCons (-(S / h)) 0 x ⬝ᵥ (H *ᵥ symplCons (-(S / h)) 0 x) =
        x ⬝ᵥ (symplReduce H *ᵥ x) := by
      rw [hL, hR]
      field_simp
      ring
    rw [← key]
    exact h1

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplShortPrim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplShortPrim

lemma intVec_smul {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by
  funext i
  simp [intVec]

lemma qf_smul {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

end PSymplShortPrim


open PSymplShortPrim in
theorem SymplShortPrim.proof : SymplShortPrim.Statement := by
  intro ι _ _ G hG v w m hvw hv hmin
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hwR : intVec w ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa [intVec] using this
  have hq : 0 < qf G (intVec w) := by
    have := hG.dotProduct_mulVec_pos hwR
    simpa [qf] using this
  have hle := hmin w hw
  rw [hvw, intVec_smul, qf_smul] at hle
  have hm2 : ((m : ℝ)) ^ 2 ≤ 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hm2' : m ^ 2 ≤ 1 := by exact_mod_cast hm2
  have habs : |m| ≤ 1 := (sq_le_one_iff_abs_le_one m).mp hm2'
  rw [abs_le] at habs
  omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplTwoRow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplTwoRow

def twoBlock (n : ℕ) (a b r s : ℤ) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℤ :=
  Matrix.of (vecCons (vecCons a (vecCons b 0))
    (vecCons (vecCons (-s) (vecCons r 0)) fun k => vecCons 0 (vecCons 0 (Pi.single k 1))))

theorem twoBlock_mul_transpose {n : ℕ} {c d x y : ℤ} (h : x * c + y * d = 1) :
    twoBlock n c d x y * (twoBlock n x y c d)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
  simp [twoBlock, Fin.sum_univ_succ, Matrix.one_apply, Pi.single_apply] <;>
  first | linarith | (split_ifs <;> simp_all [Fin.ext_iff]) | simp [Fin.ext_iff]

end PSymplTwoRow


open PSymplTwoRow in
theorem SymplTwoRow.proof : SymplTwoRow.Statement := by
  intro n c d x y h
  refine ⟨fromBlocks (twoBlock n c d x y) 0 0 (twoBlock n x y c d), ?_, ?_⟩
  · rw [SymplecticGroup.mem_iff]
    have h1 := twoBlock_mul_transpose (n := n) h
    have h2 : twoBlock n x y c d * (twoBlock n c d x y)ᵀ = 1 := by
      rw [← transpose_transpose (twoBlock n x y c d), ← transpose_mul, h1, transpose_one]
    simp [J, fromBlocks_transpose, fromBlocks_multiply, h1, h2]
  · funext z
    rcases z with i | i
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons, twoBlock]
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCharIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory

noncomputable section

namespace KThetaCharIntegral

theorem integral_Icc_exp (n : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((n : ℂ) * (t : ℂ))) =
      if n = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hn
  · subst hn; simp
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have h1 : ∀ t : ℝ, 2 * π * Complex.I * ((n : ℂ) * (t : ℂ)) = 2 * π * Complex.I * n * t := by
      intro t; ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = n * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h2]
    simp

theorem torusChar_eq_prod {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = ∏ i, Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (u i : ℂ))) := by
  unfold torusChar
  rw [Finset.mul_sum, Complex.exp_sum]

end KThetaCharIntegral

theorem ThetaCharIntegral.proof : ThetaCharIntegral.Statement := by
  intro g m
  have hset : Set.Icc (0 : Fin g → ℝ) 1 = Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
    rw [← Set.pi_univ_Icc]; rfl
  rw [hset, volume_pi, Measure.restrict_pi_pi]
  simp_rw [KThetaCharIntegral.torusChar_eq_prod]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (t : ℂ))))]
  simp_rw [KThetaCharIntegral.integral_Icc_exp]
  by_cases hm : m = 0
  · subst hm; simp
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (funext h)
    rw [if_neg hm]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaConstants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace KThetaConstants

lemma log_lhs (C₃ ρ d : ℝ) (g : ℕ) (hC₃ : 0 < C₃) (hg : (0 : ℝ) < g) (hρ : 0 < ρ) (hd : 0 < d) :
    Real.log ((C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) =
      (g / 2) * Real.log (C₃ * g) + (-(1 / 2)) * Real.log d + g * Real.log (1 + 1 / ρ) := by
  have h1 : 0 < C₃ * g := mul_pos hC₃ hg
  have h2 : 0 < 1 + 1 / ρ := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow h1, Real.log_rpow hd, Real.log_pow]

lemma log_rhs (C ρ d : ℝ) (g : ℕ) (hd : 0 < d) :
    Real.log (((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) *
        exp (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g))) =
      (-(1 / 4)) * (g * Real.log 2 + Real.log d) +
        (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)) := by
  have h1 : 0 < (2 : ℝ) ^ g * d := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow h1, Real.log_exp,
    Real.log_mul (by positivity) hd.ne', Real.log_pow]

end KThetaConstants


open KThetaConstants in
theorem ThetaConstants.proof : ThetaConstants.Statement := by
  intro C₃ hC₃
  have hK1 : (1 : ℝ) ≤ max C₃ 1 := le_max_right _ _
  have hK0 : (0 : ℝ) < max C₃ 1 := by linarith
  have hlK : 0 ≤ Real.log (max C₃ 1) := Real.log_nonneg hK1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + Real.log (max C₃ 1) / (2 * Real.log 2), by positivity, ?_⟩
  intro g ρ d hg hρ hd hρ2 hdinv
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  have h2g : (0 : ℝ) < 2 * g := by linarith
  have hl2g : Real.log 2 ≤ Real.log (2 * g) := Real.log_le_log (by norm_num) (by linarith)
  have h1 : -Real.log d ≤ g * Real.log (2 * g) := by
    have hpow : ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) ≤ (2 * (g : ℝ)) ^ g := by
      obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ' (2 * ((n + 1 : ℕ) : ℝ)) n]
      exact mul_le_mul_of_nonneg_right hρ2 (pow_nonneg h2g.le n)
    have := Real.log_le_log (inv_pos.mpr hd) (hdinv.trans hpow)
    rwa [Real.log_inv, Real.log_pow] at this
  have h2 : Real.log (C₃ * g) ≤ Real.log (max C₃ 1) + Real.log (2 * g) := by
    rw [← Real.log_mul hK0.ne' h2g.ne']
    apply Real.log_le_log (mul_pos hC₃ hg0)
    have : C₃ ≤ max C₃ 1 := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_right this hg0.le,
      mul_le_mul_of_nonneg_left (show (g : ℝ) ≤ 2 * g by linarith) hK0.le]
  have h5 : (g : ℝ) / 2 * Real.log (max C₃ 1) ≤
      Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) := by
    rw [show Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) =
        (g * Real.log (max C₃ 1) * Real.log (2 * g)) / (2 * Real.log 2) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hl2g (mul_nonneg hg0.le hlK)]
  have ha := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ g / 2 by positivity)
  have hc := mul_le_mul_of_nonneg_left hl2g hg0.le
  rw [← Real.log_le_log_iff (by positivity) (by positivity), log_lhs C₃ ρ d g hC₃ hg0 hρ hd,
    log_rhs _ ρ d g hd]
  nlinarith [h1, ha, hc, h5]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCubeParseval
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace KThetaCubeParseval

lemma torusChar_eq {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = Complex.exp (((2 * π * ∑ i, (m i : ℝ) * u i : ℝ) : ℂ) * Complex.I) := by
  unfold torusChar
  congr 1
  push_cast
  ring

lemma norm_torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ‖torusChar m u‖ = 1 := by
  rw [torusChar_eq, Complex.norm_exp_ofReal_mul_I]

lemma torusChar_mul_conj {g : ℕ} (k l : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar k u * conj (torusChar l u) = torusChar (k - l) u := by
  rw [torusChar_eq, torusChar_eq, torusChar_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

lemma continuous_torusChar {g : ℕ} (m : Fin g → ℤ) : Continuous (torusChar m) := by
  unfold torusChar
  fun_prop

lemma measureReal_cube (g : ℕ) :
    (volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)).real Set.univ = 1 := by
  simp [Measure.real, Real.volume_Icc_pi]

end KThetaCubeParseval


open KThetaCubeParseval in
theorem ThetaCubeParseval.proof (h : ThetaCharIntegral.Statement) : ThetaCubeParseval.Statement := by
  intro g c hc
  set μ := volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)

  set F : (Fin g → ℤ) × (Fin g → ℤ) → (Fin g → ℝ) → ℂ :=
    fun p u => c p.1 * conj (c p.2) * torusChar (p.1 - p.2) u with hF
  have hnorm1 : ∀ u, Summable fun k => ‖c k * torusChar k u‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hnorm2 : ∀ u, Summable fun l => ‖conj (c l) * conj (torusChar l u)‖ := fun u => by
    simpa [norm_torusChar] using hc
  have hpt : ∀ u, ((‖∑' k, c k * torusChar k u‖ ^ 2 : ℝ) : ℂ) = ∑' p, F p u := by
    intro u
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.conj_tsum]
    simp only [map_mul]
    rw [tsum_mul_tsum_of_summable_norm (hnorm1 u) (hnorm2 u)]
    congr 1
    ext p
    rw [hF]
    dsimp only
    rw [← torusChar_mul_conj]
    ring
  have hnormF : ∀ p u, ‖F p u‖ = ‖c p.1‖ * ‖c p.2‖ := by
    intro p u
    simp [hF, norm_torusChar]
  have hint : ∀ p, Integrable (F p) μ := fun p =>
    ((continuous_torusChar (p.1 - p.2)).const_smul (c p.1 * conj (c p.2))).integrableOn_Icc
  have hμ : μ.real Set.univ = 1 := measureReal_cube g
  have hsum : Summable fun p => ∫ u, ‖F p u‖ ∂μ := by
    simp only [hnormF, integral_const, hμ, one_smul]
    exact Summable.mul_of_nonneg hc hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hterm : ∀ p, ∫ u, F p u ∂μ = if p.1 - p.2 = 0 then c p.1 * conj (c p.2) else 0 := by
    intro p
    rw [hF]
    dsimp only
    rw [integral_const_mul, h g (p.1 - p.2)]
    split_ifs <;> simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_tsum]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hterm]
  have hinj : Function.Injective fun k : Fin g → ℤ => (k, k) := fun a b hab => (Prod.mk.inj hab).1
  rw [← hinj.tsum_eq]
  · congr 1
    ext k
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · intro p hp
    have : p.1 - p.2 = 0 := by
      by_contra hne
      exact hp (by simp [hne])
    exact ⟨p.1, Prod.ext rfl (sub_eq_zero.mp this)⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

theorem ThetaBound.proof (hG : GaussianSum.Statement) (hMean : ThetaMean.Statement)
    (hMaj : ThetaNormMajorant.Statement) (hSplit : ThetaFirstCoordSplit.Statement)
    (hConst : ThetaConstants.Statement) : ThetaBound.Statement := by
  obtain ⟨C₃, hC₃, hG⟩ := hG
  obtain ⟨C, hC, hK⟩ := hConst C₃ hC₃
  refine ⟨C, hC, ?_⟩
  intro g _ X Y ρ a b _ hY hR _ _
  refine ⟨hMean g X Y a b hY, fun u₁ u₂ => ?_⟩
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ))
  have hdet : Y.det⁻¹ ≤ ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) := by
    have h := hR.det_le
    rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h
  have hg : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have h1 := hMaj g X Y a b u₁ u₂ hY
  have h2 := hSplit g Y ρ a u₁ hY hR.pos hR.first
  have h3 := (hG g Y ρ hY hR.pos hR.min (a + u₁)).2
  have h4 := hK g ρ Y.det hg hR.pos hY.det_pos hR.sq_le hdet
  have he : 0 ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := (exp_pos _).le
  calc thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := h1
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := h2
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ((C₃ * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) :=
        mul_le_mul_of_nonneg_left h3 he
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) * (((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))) :=
        mul_le_mul_of_nonneg_left h4 he
    _ = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (-(π / (2 * ρ ^ 2)) * δ ^ 2 + (g * log (1 + 1 / ρ) + C * g * log (2 * g))) := by
        rw [exp_add (-(π / (2 * ρ ^ 2)) * δ ^ 2)]; ring

end GroundTheory.Heights₂.Heights
end

