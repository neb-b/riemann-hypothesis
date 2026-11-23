module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbC
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbE (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def dpbP (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun W ab := (1 / 2 : ℝ) • (W ab.1.1 ab.1.2 + star (W ab.1.2 ab.1.1))
  map_add' W W' := by
    ext ab
    simp only [Matrix.add_apply, Pi.add_apply, star_add]
    module
  map_smul' c W := by
    ext ab
    simp only [Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, star_smul, star_trivial]
    module

theorem dpbP_herm {ε : Fin n → Bool} {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ = W) (ab : PCoord ε) :
    dpbP ε W ab = W ab.1.1 ab.1.2 := by
  have h : star (W ab.1.2 ab.1.1) = W ab.1.1 ab.1.2 := by
    have := congrFun (congrFun hW ab.1.1) ab.1.2
    simpa [Matrix.conjTranspose_apply] using this
  simp only [dpbP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, Complex.real_smul]
  push_cast
  ring

theorem dpbP_E {ε : Fin n → Bool} (w : PCoord ε → ℂ) : dpbP ε (dpbE ε w) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, hab, hne⟩ := ab
  have h1 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => absurd h.1 (not_lt.mpr hab.le)
  simp only [dpbP, dpbE, LinearMap.coe_mk, AddHom.coe_mk, pmat, dif_pos (And.intro hab hne), dif_neg h1,
    star_star]
  rw [Complex.real_smul]
  push_cast
  ring

theorem dpb_JWJ (ε : Fin n → Bool) (W : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * W * Jm ε) a b = if ε a = ε b then W a b else -W a b := by
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases ε a <;> cases ε b <;> simp

theorem dpbE_P {ε : Fin n → Bool} (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbE ε (dpbP ε W) = (1 / 4 : ℝ) • (W + Wᴴ - Jm ε * W * Jm ε - (Jm ε * W * Jm ε)ᴴ) := by
  ext a b
  simp only [dpbE, dpbP, LinearMap.coe_mk, AddHom.coe_mk, pmat, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, dpb_JWJ]
  by_cases hε : ε a = ε b
  · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => h.2 hε
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => h.2 hε.symm
    rw [dif_neg h1, dif_neg h2, if_pos hε, if_pos hε.symm]
    simp
  · rw [if_neg hε, if_neg (Ne.symm hε)]
    rcases lt_trichotomy a b with h | h | h
    · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => absurd h'.1 (not_lt.mpr h.le)
      rw [dif_neg h1, dif_pos (And.intro h (Ne.symm hε))]
      simp only [Complex.real_smul]
      push_cast
      simp only [star_add, star_mul', star_star, star_div₀, star_one, star_ofNat, star_neg]
      ring
    · exact absurd (h ▸ rfl) hε
    · rw [dif_pos (And.intro h hε)]
      simp only [star_neg, Complex.real_smul]
      push_cast
      ring

theorem dpb_JYJ {ε : Fin n → Bool} (y : PCoord ε → ℂ) : Jm ε * pmat y * Jm ε = -pmat y := by
  ext a b
  rw [dpb_JWJ]
  split_ifs with h
  · have : pmat y a b = 0 := by simp [pmat, h]
    rw [Matrix.neg_apply, this, neg_zero]
  · rw [Matrix.neg_apply]

theorem dpb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.sinh_neg, neg_div_neg_eq]

theorem dpb_shc_fac : (fun u : ℝ => u * ((shc u - 1) / u)) = fun u => shc u - 1 := by
  funext u
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg h]
    field_simp

theorem dpb_theta_ad {J Y : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hY : J * Y * J = -Y)
    (W : Matrix (Fin n) (Fin n) ℂ) : J * (Y * W - W * Y) * J = -(Y * (J * W * J) - (J * W * J) * Y) := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (J * A * J) * (J * B * J) = J * (A * B) * J := by
    intro A B
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← key Y W, ← key W Y, hY]
  simp only [neg_mul, mul_neg]
  abel

theorem dpb_det {ε : Fin n → Bool} {U : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hY : Jm ε * (U * dpbD x * Uᴴ) * Jm ε = -(U * dpbD x * Uᴴ)) :
    LinearMap.det (dpbL U x shc) = LinearMap.det (dpbP ε ∘ₗ dpbL U x shc ∘ₗ dpbE ε) ^ 4 := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    change star (if ε a then (1 : ℂ) else -1) = (if ε a then 1 else -1)
    split_ifs <;> simp
  have hJJv : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let θ : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Jm ε * W * Jm ε
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c W => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let α : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Wᴴ
      map_add' := fun W W' => Matrix.conjTranspose_add W W'
      map_smul' := fun c W => by simp [Matrix.conjTranspose_smul] }
  let ι : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Complex.I • W
      map_add' := fun W W' => smul_add _ _ _
      map_smul' := fun c W => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  let N : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => (U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c W => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  let C : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) := dpbL U x (fun u => (shc u - 1) / u)
  have hsub : dpbH U x (fun u => u * ((shc u - 1) / u)) = dpbH U x (fun u => shc u - 1) := by
    rw [dpb_shc_fac]
  refine dpb_abs (dpbL U x shc) θ α ι N C (dpbE ε) (dpbP ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    show Jm ε * (Jm ε * v * Jm ε) * Jm ε = v
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJv]
  · intro v
    show (vᴴ)ᴴ = v
    exact Matrix.conjTranspose_conjTranspose v
  · intro v
    show Jm ε * vᴴ * Jm ε = (Jm ε * v * Jm ε)ᴴ
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]
  · intro v
    show Jm ε * dpbH U x shc v * Jm ε = dpbH U x shc (Jm ε * v * Jm ε)
    exact dpbH_theta hU hU' hJJ hJh hY shc dpb_shc_neg v
  · intro v
    show (dpbH U x shc v)ᴴ = dpbH U x shc vᴴ
    exact dpbH_conjTranspose U x shc dpb_shc_neg v
  · intro v
    show (U * dpbD x * Uᴴ) * dpbH U x (fun u => (shc u - 1) / u) v -
      dpbH U x (fun u => (shc u - 1) / u) v * (U * dpbD x * Uᴴ) = dpbH U x shc v - v
    rw [dpbH_ad_left x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show dpbH U x (fun u => (shc u - 1) / u) ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) =
      dpbH U x shc v - v
    rw [dpbH_ad_right x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show Jm ε * ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) * Jm ε =
      -((U * dpbD x * Uᴴ) * (Jm ε * v * Jm ε) - (Jm ε * v * Jm ε) * (U * dpbD x * Uᴴ))
    exact dpb_theta_ad hJJ hY v
  · intro v
    show Complex.I • (Complex.I • v) = -v
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  · intro v
    show Complex.I • dpbH U x shc v = dpbH U x shc (Complex.I • v)
    exact (dpbH_smul U x shc Complex.I v).symm
  · intro v
    show Jm ε * (Complex.I • v) * Jm ε = Complex.I • (Jm ε * v * Jm ε)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  · intro v
    show (Complex.I • v)ᴴ = -(Complex.I • vᴴ)
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · intro v
    exact dpbE_P v
  · intro w
    exact dpbP_E w

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FBridge
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fbr_det_exp_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    (NormedSpace.exp (pmat z)).det = 1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hsp : pmat z = U * diagonal (fun i => (pev z i : ℂ)) * Uᴴ := by
    have := (pmat_isHermitian z).spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h2
  have hu : IsUnit U := ⟨⟨U, Uᴴ, h2, h1⟩, rfl⟩
  rw [hsp, ← hinv, Matrix.exp_conj _ _ hu, Matrix.det_conj hu, Matrix.exp_diagonal, det_diagonal]
  have he : ∀ i, (NormedSpace.exp (fun i => (pev z i : ℂ))) i = Complex.exp (pev z i : ℂ) := by
    intro i
    rw [Pi.exp_def, Complex.exp_eq_exp_ℂ]
  simp only [he]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum, sum_pev, Complex.ofReal_zero, Complex.exp_zero]

theorem fbr_det_conj {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * A * toMK k).det = A.det := by
  rw [toMK_inv, Matrix.det_mul, Matrix.det_mul, mul_comm ((toMK k)ᴴ.det) A.det, mul_assoc, ← Matrix.det_mul,
    (toMK_facts k).1, Matrix.det_one, mul_one]

theorem fbr_phi {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PhiM μ (toMK k⁻¹ * NormedSpace.exp (pmat z) * toMK k) =
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) := by
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ (pmat_inP z)
  rw [inv_inv] at hP hE
  rw [← hE]
  set Y := toMK k⁻¹ * pmat z * toMK k with hY
  set E := NormedSpace.exp Y with hEdef
  have hpd : E.PosDef := exp_noncompactPart_posDef hP
  have hdet : lead n E = 1 := by
    have h1 : E.det = 1 := by rw [hE, fbr_det_conj, fbr_det_exp_pmat]
    unfold lead
    rw [dite_eq_left le_rfl]
    convert h1 using 2
    ext a b
    rfl
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) E).re := fun i => (lead_posDef hpd _ i.isLt).1
  have h : ∀ i : Fin n, lead ((i : ℕ) + 1) E = ((lead ((i : ℕ) + 1) E).re : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM μ E = ((∏ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_zpow, ← h i]
  rw [hphi]
  congr 1
  have hz : ∀ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) =
      Real.exp (Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ)) := by
    intro i
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hpos i)]
  rw [prod_congr rfl fun i _ => hz i, ← Real.exp_sum]
  congr 1
  set g : ℕ → ℝ := fun i => -(sCoef lam i * Real.log (lead (i + 1) E).re) with hg
  have hterm : ∀ i : Fin n, Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ) = g i := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · have hm : muNext μ i = μ ⟨(i : ℕ) + 1, hi⟩ := by simp [muNext, hi]
      have hs : sCoef lam i = lam i - lam ⟨(i : ℕ) + 1, hi⟩ + 1 := by simp [sCoef, hi]
      rw [hm, hg]
      simp only
      rw [hs]
      push_cast
      rw [hμ i, hμ ⟨(i : ℕ) + 1, hi⟩]
      simp only [rho]
      push_cast
      ring
    · have hs : sCoef lam i = 0 := by simp [sCoef, hi]
      have hn : (i : ℕ) + 1 = n := by omega
      rw [hg]
      simp only
      rw [hs, hn, hdet]
      simp
  rw [sum_congr rfl fun i _ => hterm i, Fin.sum_univ_eq_sum_range g n]
  have hsub : ∑ i ∈ range n, g i = ∑ i ∈ range (n - 1), g i := by
    symm
    refine sum_subset (range_subset_range.mpr (Nat.sub_le n 1)) ?_
    intro i hi hi'
    simp only [mem_range] at hi hi'
    have hs : sCoef lam i = 0 := by simp only [sCoef]; rw [dite_eq_right (by omega)]
    simp [hg, hs]
  rw [hsub, Ph, ← sum_neg_distrib]
  rfl

theorem psM_exp_pmat {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) {Λ : Fin n → ℝ}
    (T : KType ε Λ) (z : PCoord ε → ℂ) : psM T μ (NormedSpace.exp (pmat z)) = fF ε lam T (pmat z) := by
  simp only [psM, fF]
  congr 1
  refine congrArg (fun f : KG ε → T.V →L[ℂ] T.V => ∫ k, f k ∂(muK ε)) (funext fun k => ?_)
  rw [fbr_phi hμ k z]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem finrank_pcoord (ε : Fin n → Bool) :
    Module.finrank ℝ (PCoord ε → ℂ) = 2 * (pOf ε * qOf ε) := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    card_PCoord, smul_eq_mul, mul_comm]

theorem lintegral_pcoord_smul {ε : Fin n → Bool} (f : (PCoord ε → ℂ) → ENNReal) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, f z = ENNReal.ofReal (s ^ (2 * (pOf ε * qOf ε))) * ∫⁻ y, f ((s : ℂ) • y) := by
  have hsm : (fun y : PCoord ε → ℂ => f ((s : ℂ) • y)) = fun y => f (s • y) := by
    funext y
    rw [Complex.coe_smul]
  have key : ∫⁻ y, f (s • y) =
      ENNReal.ofReal |(s ^ Module.finrank ℝ (PCoord ε → ℂ))⁻¹| * ∫⁻ z, f z := by
    have h1 := lintegral_map_equiv f (MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')
      (μ := volume)
    have h2 : (⇑(MeasurableEquiv.smul₀ (α := PCoord ε → ℂ) s hs.ne')) = (s • ·) := rfl
    rw [h2, Measure.map_addHaar_smul volume hs.ne', lintegral_smul_measure, smul_eq_mul] at h1
    exact h1.symm
  rw [hsm, key, finrank_pcoord, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdUpperA
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdU_integral_exp_norm {c : ℝ} (hc : 0 < c) :
    ∫ x : ℂ, Real.exp (-c * ‖x‖) = Real.pi * c ^ (-2 : ℝ) * Real.Gamma 3 := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 1) le_rfl hc
  have e1 : (-2 / (1 : ℝ)) = -2 := by norm_num
  have e2 : (2 / (1 : ℝ) + 1) = 3 := by norm_num
  simp only [Real.rpow_one, e1, e2] at h
  exact h

theorem fdU_integrable_exp_norm {c : ℝ} (hc : 0 < c) : Integrable (fun x : ℂ => Real.exp (-c * ‖x‖)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_exp_norm hc]
  exact (mul_pos (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hc _))
    (Real.Gamma_pos_of_pos (by norm_num))).ne'

theorem fdU_integral_gauss {b : ℝ} (hb : 0 < b) : ∫ x : ℂ, Real.exp (-b * ‖x‖ ^ 2) = Real.pi / b := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 2) (by norm_num) hb
  have e1 : (-2 / (2 : ℝ)) = -1 := by norm_num
  have e2 : (2 / (2 : ℝ) + 1) = 2 := by norm_num
  simp only [Real.rpow_two, e1, e2, Real.rpow_neg_one, Real.Gamma_two, mul_one] at h
  rw [h, div_eq_mul_inv]

theorem fdU_integrable_gauss {b : ℝ} (hb : 0 < b) : Integrable (fun x : ℂ => Real.exp (-b * ‖x‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [fdU_integral_gauss hb]
  exact (div_pos Real.pi_pos hb).ne'

theorem fdU_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  have h : ((ab.1.2 : ℕ) : ℝ) < ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast ab.2.1
  simp only [wab, Pi.zero_apply]
  linarith

theorem exp_neg_quadratic_eq_prod {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Real.exp (-Qf (0 : Fin n → ℝ) y) =
      ∏ ab : PCoord ε, Real.exp (-wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2) := by
  simp only [Qf, ← Finset.sum_neg_distrib, Real.exp_sum, neg_mul]

theorem fdU_integrable_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2)) := by
  exact Integrable.fintype_prod
    (f := fun ab (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2)) (fun ab => fdU_integrable_gauss (hb ab))

theorem fdU_integral_prod_gauss {ε : Fin n → Bool} (b : PCoord ε → ℝ) (hb : ∀ ab, 0 < b ab) :
    ∫ y : PCoord ε → ℂ, ∏ ab : PCoord ε, Real.exp (-b ab * ‖y ab‖ ^ 2) = ∏ ab : PCoord ε, Real.pi / b ab := by
  exact (integral_fintype_prod_eq_prod
    (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-b ab * ‖x‖ ^ 2))).trans
    (Finset.prod_congr rfl fun ab _ => fdU_integral_gauss (hb ab))

theorem fdU_lintegral_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  have hb : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 :=
    fun ab => fdU_wab_zero_pos ab
  have hint : Integrable (fun y : PCoord ε → ℂ => Real.exp (-Qf (0 : Fin n → ℝ) y)) := by
    simp_rw [exp_neg_quadratic_eq_prod]
    exact fdU_integrable_prod_gauss _ hb
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
  congr 1
  simp_rw [exp_neg_quadratic_eq_prod]
  rw [fdU_integral_prod_gauss _ hb]
  rfl

theorem fdU_integrable_prod_exp {ε : Fin n → Bool} {c : ℝ} (hc : ∀ _ : PCoord ε, 0 < c) :
    Integrable (fun y : PCoord ε → ℂ => ∏ ab : PCoord ε, Real.exp (-c * ‖y ab‖)) := by
  exact Integrable.fintype_prod
    (f := fun _ (x : ℂ) => Real.exp (-c * ‖x‖)) (fun ab => fdU_integrable_exp_norm (hc ab))

end ReciprocityTheory.ChartRestriction.DS
end
end

