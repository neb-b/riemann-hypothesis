module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StabUnfold

theorem ofReal_qEps_eq {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) :
    ((qEps ε y : ℝ) : ℂ) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (y i) * y i = ((‖y i‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.conj_mul']
  split_ifs <;> simp [← h]

theorem frame_inv_form (I : AutInst) (v : InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have hd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem isPerp_at_place (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (h : IsPerp D s x A xf) (v : InfinitePlace I.F) :
    qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧
      star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧
      (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  obtain ⟨-, h1, h2, h3, -⟩ := h
  have hφ : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  have hF := frame_inv_form I v
  have hs : star (fun i => I.φ v (x i)) = fun i => I.φ v (star x i) := by
    funext i; simp [hφ]
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ofReal_injective
    rw [ofReal_qEps_eq, infVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hF, hs]
    have := congrArg (I.φ v) h1
    have e : ((sgn ℝ s : ℝ) : ℂ) = I.φ v (sgn I.E s) := by
      unfold sgn; split_ifs <;> simp
    rw [e, ← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, mulVec, map_sum]
  · rw [infVec, infMat, star_mulVec, vecMul_vecMul]
    have e : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v))
        = (I.J * A).map (I.φ v) * D.P v := by
      rw [Matrix.map_mul, ← hF]; simp only [Matrix.mul_assoc]
    rw [e, ← vecMul_vecMul, hs]
    have e2 : (fun i => I.φ v (star x i)) ᵥ* (I.J * A).map (I.φ v) = 0 := by
      funext j
      have := congrArg (I.φ v) (congrFun h2 j)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [vecMul, dotProduct, map_sum] using this
    rw [e2, zero_vecMul]
  · rw [← D.P_spec v, ← h3, Matrix.map_mul, Matrix.map_mul, ← hF, infMat,
      Matrix.conjTranspose_map (I.φ v) hφ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.StabUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentDimEqSumPairs
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadicalDimSum

theorem two_mul_pairs_add_sq {ι : Type} [LinearOrder ι] (s : Finset ι) (f : ι → ℕ) :
    2 * (∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k) + ∑ i ∈ s, f i ^ 2 = (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h2 : (insert a s).filter (fun k => a < k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_irrefl _
      · exact not_lt.mpr (ha x hx).le
    have h3 : ∑ i ∈ s, ∑ k ∈ (insert a s).filter (fun k => i < k), f i * f k
        = ∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k + (∑ i ∈ s, f i) * f a := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.filter_insert, if_pos (ha i hi), Finset.sum_insert (by simp [hna])]
      ring
    simp only [Finset.sum_insert hna]
    rw [h2, Finset.sum_empty, h3,
      show (f a + ∑ i ∈ s, f i) ^ 2 = f a ^ 2 + 2 * (∑ i ∈ s, f i) * f a + (∑ i ∈ s, f i) ^ 2 by ring,
      ← ih]
    ring

theorem sum_shift_eq (N : ℕ) (r : ℕ → ℕ) (hr : ∀ b, N ≤ b → r b = 0) (b : ℕ) :
    ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ (range N).filter (fun k => b < k), r k := by
  have e : ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ Ico (b + 1) (b + 1 + N), r k := by
    rw [Finset.sum_Ico_eq_sum_range, show b + 1 + N - (b + 1) = N by omega]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    omega
  rw [e]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ico]
    omega
  · intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hk hk'
    apply hr
    by_contra h
    exact absurd (hk' (by omega)) (by omega)

theorem dimN_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  intro n a j r hj ha hz
  have hpairs : ∑ c ∈ range (2 * a + 1), ∑ b ∈ range (2 * a + 1), r b * r (b + c + 1)
      = ∑ b ∈ range (2 * a + 1), ∑ k ∈ (range (2 * a + 1)).filter (fun k => b < k), r b * r k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_shift_eq (2 * a + 1) r hz b]
  have hsum : ∑ b ∈ range (2 * a + 1), r b = 2 * ∑ i, j i + (n - 2 * ∑ i, j i) := by
    have h : ∑ b ∈ range (2 * a + 1), r b = ∑ i : Fin a, (r i + r (2 * a - i)) + r a :=
      GlobalTheory.DoubledFlag.sum_range_double a r
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have hsq : ∑ b ∈ range (2 * a + 1), r b ^ 2 = 2 * ∑ i, j i ^ 2 + (n - 2 * ∑ i, j i) ^ 2 := by
    have h : ∑ b ∈ range (2 * a + 1), r b ^ 2 = ∑ i : Fin a, (r i ^ 2 + r (2 * a - i) ^ 2) + r a ^ 2 :=
      GlobalTheory.DoubledFlag.sum_range_double a (fun b => r b ^ 2)
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have h1 := two_mul_pairs_add_sq (range (2 * a + 1)) r
  have h2 := two_mul_pairs_add_sq (univ : Finset (Fin a)) j
  rw [hsum, hsq] at h1
  rw [hpairs, GlobalTheory.FlagMeas.dimN]
  nlinarith [h1, h2]

end GlobalTheory.RadicalDimSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalEqLowering
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadFullFlag

theorem form_uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star (uMat g *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]

private theorem dotProduct_Jm_uMat_sub_one {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) =
      -(star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)) -
        star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) := by
  have h := form_uMat g x y
  simp only [sub_mulVec, one_mulVec, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢
  linear_combination h

theorem flagN_eq_lowers : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  intro n a ε W W' hF htop hW'
  obtain ⟨hmono, -, hstab, hdual⟩ := hF
  have hmem : ∀ y, y ∈ W (2 * a + 1) := fun y => by rw [htop]; exact Submodule.mem_top

  have horth : ∀ b, b ≤ 2 * a + 1 → ∀ y,
      y ∈ W (2 * a + 1 - b) ↔ ∀ x ∈ W b, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 :=
    fun b hb y => (hdual b hb y).trans ⟨fun h => h.2, fun h => ⟨hmem y, h⟩⟩
  ext g
  have hsub : ∀ y, (uMat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
    rw [sub_mulVec, one_mulVec]
  unfold GlobalTheory.FlagMeas.flagN
  simp only [Set.mem_setOf_eq, mem_lowers, add_zero]
  constructor
  · rintro ⟨h1, h2⟩

    have hlow : ∀ b, b < a → ∀ y ∈ W (b + 1), (uMat g - 1) *ᵥ y ∈ W b := by
      intro b hb y hy
      have := h1 ⟨b, hb⟩ y (by rw [hW']; exact hy)
      rw [hW'] at this
      rw [hsub]; exact this
    have hmid : ∀ y ∈ W (a + 1), (uMat g - 1) *ᵥ y ∈ W a := by
      intro y hy
      have hy' : ∀ x ∈ W' (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
        rw [hW']
        have e : 2 * a + 1 - a = a + 1 := by omega
        exact (horth a (by omega) y).1 (by rw [e]; exact hy)
      have := h2 y hy'
      rw [hW'] at this
      rw [hsub]; exact this

    have hup : ∀ k, k ≤ a → ∀ y ∈ W (2 * a + 1 - k + 1),
        (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) := by
      intro k
      induction k with
      | zero =>
        intro _ y _
        simpa using hmem ((uMat g - 1) *ᵥ y)
      | succ k ih =>
        intro hk y hy
        rw [horth (k + 1) (by omega)]
        intro x hx
        have hx' : (uMat g - 1) *ᵥ x ∈ W k := hlow k (by omega) x hx
        have hyk : y ∈ W (2 * a + 1 - k) := by
          have e : 2 * a + 1 - (k + 1) + 1 = 2 * a + 1 - k := by omega
          rw [e] at hy; exact hy
        have hgy : (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) :=
          ih (by omega) y (hmono (by omega : 2 * a + 1 - k ≤ 2 * a + 1 - k + 1) hyk)
        rw [dotProduct_Jm_uMat_sub_one, (horth k (by omega) y).1 hyk _ hx',
          (horth k (by omega) _).1 hgy _ hx']
        simp
    intro b y hy
    rcases lt_trichotomy b a with hb | hb | hb
    · exact hlow b hb y hy
    · subst hb; exact hmid y hy
    · by_cases hbm : 2 * a + 1 ≤ b
      · rw [hstab b hbm]; exact hmem _
      · have hk : b = 2 * a + 1 - (2 * a + 1 - b) := by omega
        have := hup (2 * a + 1 - b) (by omega) y (by rw [← hk]; exact hy)
        rw [← hk] at this; exact this
  · intro h
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · rw [hW'] at hy ⊢
      rw [← hsub]; exact h i y hy
    · rw [hW'] at hy ⊢
      have hy' : y ∈ W (a + 1) := by
        have e : 2 * a + 1 - a = a + 1 := by omega
        rw [← e]; exact (horth a (by omega) y).2 hy
      rw [← hsub]; exact h a y hy'

end GlobalTheory.RadFullFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerCovolumeProductPowTwoSidedBounds
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem prod_pow_bounds : ∀ (v : ℝ) (f k r m a b : ℕ) (x : ℝ≥0∞), 1 ≤ v → m ≤ r → a ≤ r ^ 2 → b ≤ r ^ 2 → ENNReal.ofReal ((8 * v) ^ (-(f : ℝ))) ^ m ≤ x → x ≤ ENNReal.ofReal ((8 * v) ^ (f : ℝ)) ^ m → ENNReal.ofReal (v ^ (k * m * f) / (8 * v) ^ (2 * (r + 1) ^ 2 * f)) ≤ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ∧ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ≤ ENNReal.ofReal (v ^ (k * m * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) := by
  intro v f k r m a b x hv hm ha hb hlo hhi
  have hv0 : 0 < v := by linarith
  have hw1 : 1 ≤ 8 * v := by linarith
  have hw0 : 0 < 8 * v := by linarith
  have hvw : v ≤ 8 * v := by linarith
  have hvf : 0 ≤ v ^ f := by positivity
  have key : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m *
        (ENNReal.ofReal (v ^ f) ^ b * ENNReal.ofReal y ^ m)) =
      ENNReal.ofReal (v ^ (k * m * f) * (v ^ (f * (a + m + b)) * y ^ m)) := by
    intro y hy
    rw [← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hy,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [Real.rpow_neg hw0.le, Real.rpow_natCast] at hlo
  rw [Real.rpow_natCast] at hhi
  constructor
  · refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hlo _) _) _)
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : 1 ≤ v ^ (f * (a + m + b)) := one_le_pow₀ hv
    have h2 : ((8 * v) ^ (2 * (r + 1) ^ 2 * f))⁻¹ ≤ ((8 * v) ^ f)⁻¹ ^ m := by
      rw [inv_pow, ← pow_mul]
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_right₀ hw1
      rw [mul_comm f m]
      apply Nat.mul_le_mul_right
      nlinarith
    exact h2.trans (le_mul_of_one_le_left (by positivity) h1)
  · refine le_trans (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hhi _) _) _) ?_
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : v ^ (f * (a + m + b)) ≤ (8 * v) ^ (f * (a + m + b)) :=
      pow_le_pow_left₀ hv0.le hvw _
    calc v ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m
        ≤ (8 * v) ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (8 * v) ^ ((a + m + b + m) * f) := by ring
      _ ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := by
          apply pow_le_pow_right₀ hw1
          apply Nat.mul_le_mul_right
          nlinarith

end GlobalTheory.DegVol.RefCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralIoiCompConstDivChangeOfVar
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory

theorem lintegral_Ioi_comp_const_div_mul_div :
    ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w →
      ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t =
        ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro κ hκ w _hw
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have himg : (fun u : ℝ => κ / u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hκ hu
    · intro ht
      have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
      refine ⟨κ / t, div_pos hκ ht, ?_⟩
      show κ / (κ / t) = t
      field_simp
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => κ / u) (-(κ / u ^ 2)) (Set.Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hu)
    have h := ((hasDerivAt_inv hu0).const_mul κ).hasDerivWithinAt (s := Set.Ioi (0 : ℝ))
    have hfun : (fun u : ℝ => κ / u) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [hfun]
    exact h.congr_deriv (by ring)
  have hinj : Set.InjOn (fun u : ℝ => κ / u) (Set.Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hab' : κ / a = κ / b := hab
    field_simp at hab'
    exact hab'.symm
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj,
    himg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun u hu => ?_))
  have hu : 0 < u := Set.mem_Ioi.mp hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hκu : 0 < κ / u := div_pos hκ hu
  have hsq : 0 < u ^ 2 := by positivity
  have hinv : κ / (κ / u) = u := by field_simp
  have habs : |(-(κ / u ^ 2))| = κ / u ^ 2 := by
    rw [abs_neg, abs_of_pos (div_pos hκ hsq)]
  have hne : ENNReal.ofReal (κ / u) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hκu
  simp only [hinv, habs]
  rw [ENNReal.mul_div_cancel_right hne ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos hsq]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocSizeBlocks
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Size

theorem detOn_of_frame {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (g : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) m ℂ) (X : Matrix m m ℂ) (W : Submodule ℂ (Fin n → ℂ)) (hC : Cᴴ * C = 1)
    (hW : ∀ y, y ∈ W ↔ ∃ u, y = C *ᵥ u) (hg : g * C = C * X) : detOn g W = ‖X.det‖ := by
  have hst : ∀ y ∈ W, Matrix.toLin' g y ∈ W := by
    intro y hy
    obtain ⟨u, rfl⟩ := (hW y).1 hy
    exact (hW _).2 ⟨X *ᵥ u, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]⟩
  let f : (m → ℂ) →ₗ[ℂ] W := (Matrix.toLin' C).codRestrict W fun u => (hW _).2 ⟨u, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun y => ?_⟩
    · have h1 : C *ᵥ u = C *ᵥ v := congrArg Subtype.val h
      have h2 := congrArg (fun y => Cᴴ *ᵥ y) h1
      simpa only [Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] using h2
    · obtain ⟨u, hu⟩ := (hW y).1 y.2
      exact ⟨u, Subtype.ext hu.symm⟩
  let e := LinearEquiv.ofBijective f hf
  have he : (Matrix.toLin' g).restrict hst =
      (e : (m → ℂ) →ₗ[ℂ] W) ∘ₗ Matrix.toLin' X ∘ₗ (e.symm : W →ₗ[ℂ] (m → ℂ)) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨u, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    change g *ᵥ (C *ᵥ u) = C *ᵥ (X *ᵥ u)
    rw [Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]
  unfold detOn
  rw [dite_eq_left hst, he, LinearMap.det_conj, LinearMap.det_toLin']

theorem detOn_blocks {n a : ℕ} {j : Fin a → ℕ} (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : Fin a → Prop) [DecidablePred p] (W : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ i, (B i)ᴴ * B i = 1) (h2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0)
    (hW : ∀ y, y ∈ W ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i, ¬ p i → u i = 0) ∧ y = ∑ i, B i *ᵥ u i)
    (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ)
    (hg : ∀ i, g * B i = B i * x i) :
    detOn g W = ∏ i ∈ Finset.univ.filter p, ‖(x i).det‖ := by
  let C : Matrix (Fin n) (Σ i : {i // p i}, Fin (j i)) ℂ := Matrix.of fun r s => B s.1 r s.2
  have hCv : ∀ u, C *ᵥ u = ∑ i : {i // p i}, B i *ᵥ fun s => u ⟨i, s⟩ := by
    intro u
    funext r
    simp [C, Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [detOn_of_frame g C (Matrix.blockDiagonal' fun i : {i // p i} => x i) W ?_ ?_ ?_]
  · rw [ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', norm_prod,
      Finset.prod_subtype (Finset.univ.filter p) (p := p) (by simp)]
  · ext ⟨i, s⟩ ⟨k, t⟩
    change ((B i)ᴴ * B k) s t = _
    by_cases h : i = k
    · subst h
      rw [h1]
      simp [Matrix.one_apply]
    · rw [h2 i k (fun e => h (Subtype.ext e)), Matrix.one_apply_ne (fun e => h (congrArg Sigma.fst e))]
      rfl
  · intro y
    rw [hW]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun s => u s.1 s.2, ?_⟩
      rw [hCv, ← Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun i => B i *ᵥ u i),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · rw [hu i h, Matrix.mulVec_zero]
    · rintro ⟨u, rfl⟩
      refine ⟨fun i => if h : p i then fun s => u ⟨⟨i, h⟩, s⟩ else 0, fun i h => dif_neg h, ?_⟩
      rw [hCv, ← Finset.sum_subset (Finset.filter_subset p Finset.univ) ?_,
        Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        beta_reduce
        rw [dite_eq_left i.2]
      · intro i _ hi
        beta_reduce
        rw [dif_neg (by simpa using hi), Matrix.mulVec_zero]
  · ext r ⟨k, t⟩
    change (g * B k) r t = _
    rw [hg, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [C]
    · intro i _ hi
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hi]
    · simp

theorem locSize_blocks : ∀ (n a : ℕ) (j : Fin a → ℕ) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → SpansFlag B W → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ), (∀ i, (x i).det ≠ 0) → (∀ i, g * B i = B i * x i) → ∀ i, locSize j W g i = ‖(x i).det‖ ^ (-(1 : ℝ) / j i) := by
  intro n a j B W h1 h2 hW g x hx hg i
  unfold locSize
  rw [detOn_blocks B _ _ h1 h2 (hW i.succ) g x hg, detOn_blocks B _ _ h1 h2 (hW i.castSucc) g x hg]
  have e : (Finset.univ.filter fun k : Fin a => k.castSucc < i.succ) =
      insert i (Finset.univ.filter fun k : Fin a => k.castSucc < i.castSucc) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  rw [e, Finset.prod_insert (by simp), mul_div_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hx k)

end GlobalTheory.LeviIso.Size
end
end

