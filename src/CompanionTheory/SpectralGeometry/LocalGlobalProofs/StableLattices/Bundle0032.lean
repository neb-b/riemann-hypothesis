module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Bundle0001
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorBound
section
open Matrix CompanionTheory.Bmu Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuTorBound

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem step_le (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (M : ℝ) (hd : IsTor k r d) (hM : 1 ≤ M)
    (ha : ∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) (j : ℕ) (hj : j + 1 < 2 * r + k + 1) :
    d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩ := by
  obtain ⟨hpos, hpair, hmid, hf⟩ := hd
  by_cases h1 : j < r
  · exact ha ⟨j, h1⟩
  by_cases h2 : r + k ≤ j
  · have hlt : 2 * r + k - j - 1 < r := by omega
    have h := ha ⟨2 * r + k - j - 1, hlt⟩
    have p1 := hpair ⟨j, by omega⟩ (nxt k r ⟨2 * r + k - j - 1, hlt⟩) (Or.inr h2) (by simp only [nxt]; omega)
    have p2 := hpair ⟨j + 1, hj⟩ (eI k r ⟨2 * r + k - j - 1, hlt⟩) (Or.inr (by simp only; omega))
      (by simp only [eI]; omega)
    have q1 := hpos ⟨j, by omega⟩
    have q2 := hpos ⟨j + 1, hj⟩
    generalize d ⟨j, by omega⟩ = x at *
    generalize d ⟨j + 1, hj⟩ = y at *
    generalize d (nxt k r ⟨2 * r + k - j - 1, hlt⟩) = u at *
    generalize d (eI k r ⟨2 * r + k - j - 1, hlt⟩) = v at *
    calc x = x * y * v := by rw [mul_assoc, p2, mul_one]
      _ ≤ x * y * (M * u) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = M * y * (x * u) := by ring
      _ = M * y := by rw [p1, mul_one]
  have a1 : d ⟨j, by omega⟩ ≤ 1 := by
    by_cases h3 : j = r
    · have : (⟨j, by omega⟩ : Fin (2 * r + k + 1)) = wI k r 0 := Fin.ext (by simp [wI, h3])
      rw [this]; exact hf
    · exact (hmid _ (by simp only [outer]; omega)).le
  have a2 : 1 ≤ d ⟨j + 1, hj⟩ := by
    by_cases h3 : j + 1 = r + k
    · have p := hpair ⟨j + 1, hj⟩ (wI k r 0) (Or.inr (by simp only; omega)) (by simp [wI]; omega)
      have q := hpos ⟨j + 1, hj⟩
      nlinarith
    · exact (hmid _ (by simp only [outer]; omega)).ge
  nlinarith

theorem chain_le {n : ℕ} (d : Fin n → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩) (j m : ℕ) (h : j + m < n) :
    d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, h⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := hs (j + m) h
    calc d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, by omega⟩ := h1
      _ ≤ M ^ m * (M * d ⟨j + m + 1, h⟩) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = M ^ (m + 1) * d ⟨j + (m + 1), h⟩ := by rw [pow_succ, mul_assoc]; rfl

theorem ratio_le (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (M : ℝ) (hd : IsTor k r d) (hM : 1 ≤ M)
    (ha : ∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) (i j : Fin (2 * r + k + 1)) (h : ¬ up k r i j) :
    d j ≤ M ^ (2 * r + k + 1) * d i := by
  by_cases hij : i < j
  · have hi : ¬ outer k r i := fun h' => h ⟨hij, Or.inl h'⟩
    have hj : ¬ outer k r j := fun h' => h ⟨hij, Or.inr h'⟩
    rw [hd.2.2.1 i hi, hd.2.2.1 j hj, mul_one]
    exact one_le_pow₀ hM
  · have hji : j.val ≤ i.val := by
      have := not_lt.mp hij
      exact this
    have hc := chain_le d M hM (step_le k r d M hd hM ha) j.val (i.val - j.val) (by have := i.2; omega)
    have e : (⟨j.val + (i.val - j.val), by have := i.2; omega⟩ : Fin (2 * r + k + 1)) = i :=
      Fin.ext (by simp only; omega)
    rw [e] at hc
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (hd.1 i).le)
    exact pow_le_pow_right₀ hM (by have := i.2; omega)

theorem unitary_conj_le {n : ℕ} (R B : Mat n) (hR : Rᴴ * R = 1) : ‖Rᴴ * B * R‖ ≤ (n : ℝ) ^ 2 * ‖B‖ := by
  have hU : R ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hR
  have he : ∀ i j, ‖R i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hU i j
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  have h1 : ∀ l, ‖(Rᴴ * B) i l‖ ≤ n * ‖B‖ := by
    intro l
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ‖B‖ ?_).trans (by simp)
    intro x _
    rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
    calc ‖R x i‖ * ‖B x l‖ ≤ 1 * ‖B‖ :=
          mul_le_mul (he x i) (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) zero_le_one
      _ = ‖B‖ := one_mul _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (n * ‖B‖) ?_).trans (by simp [sq, mul_assoc])
  intro x _
  rw [norm_mul]
  calc ‖(Rᴴ * B) i x‖ * ‖R x j‖ ≤ n * ‖B‖ * 1 :=
        mul_le_mul (h1 x) (he x j) (norm_nonneg _) (by positivity)
    _ = n * ‖B‖ := mul_one _

theorem torBound : TorBound := by
  intro k r d R A M _ hd hR hM ha hA
  have hpos := hd.1
  have hinv : (dg d * R)⁻¹ = Rᴴ * dg (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    have : dg (fun i => (d i)⁻¹) * dg d = 1 := by
      unfold dg
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dg _), this, Matrix.one_mul, hR]
  have e : (dg d * R)⁻¹ * A * (dg d * R) = Rᴴ * (dg (fun i => (d i)⁻¹) * A * dg d) * R := by
    rw [hinv]; simp only [Matrix.mul_assoc]
  rw [e]
  refine (unitary_conj_le R _ hR).trans ?_
  rw [mul_assoc _ ‖A‖]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  unfold dg
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hu : up k r i j
  · rw [hA i j hu]
    simp only [mul_zero, zero_mul, norm_zero]
    positivity
  · have hr := ratio_le k r d M hd hM ha i j hu
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hpos j).le,
      Real.norm_of_nonneg (inv_pos.mpr (hpos i)).le]
    have h2 : (d i)⁻¹ * d j ≤ M ^ (2 * r + k + 1) := by
      rw [inv_mul_le_iff₀ (hpos i), mul_comm]; exact hr
    have hi := hpos i
    have hj := hpos j
    calc (d i)⁻¹ * ‖A i j‖ * d j = ‖A i j‖ * ((d i)⁻¹ * d j) := by ring
      _ ≤ ‖A‖ * M ^ (2 * r + k + 1) :=
        mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) h2 (by positivity) (norm_nonneg _)

end GlobalTheory.CompanionTheory.BmuTorBound
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacy
section
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuTorConj

theorem cStd_ne : cStd ≠ 0 := by
  simp [cStd, Complex.I_ne_zero]

theorem exists_scale (r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ T : ℕ → ℂ, (∀ n, T n ≠ 0) ∧ (∀ n, r ≤ n → T n = 1) ∧
      ∀ a : Fin r, c a * T a.val = cStd * T (a.val + 1) := by
  classical
  obtain ⟨c', hc'd⟩ : ∃ f : ℕ → ℂ, f = fun m => if h : m < r then c ⟨m, h⟩ else 1 := ⟨_, rfl⟩
  have hc' : ∀ m, c' m ≠ 0 := fun m => by
    by_cases h : m < r
    · simp only [hc'd, dif_pos h]; exact hc _
    · simp only [hc'd, dif_neg h]; exact one_ne_zero
  refine ⟨fun n => ∏ m ∈ Finset.Ico n r, (cStd / c' m), ?_, ?_, ?_⟩
  · intro n
    exact Finset.prod_ne_zero_iff.mpr fun m _ => div_ne_zero cStd_ne (hc' m)
  · intro n hn
    simp [Finset.Ico_eq_empty_of_le hn]
  · intro a
    simp only
    rw [Finset.prod_eq_prod_Ico_succ_bot a.isLt]
    have hca : c' a.val = c a := by simp only [hc'd, dif_pos a.isLt]
    rw [hca]
    have hcz := hc a
    field_simp

theorem hpk_row (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hpq : p.val + q.val = 2 * r + k)
    (h : p.val < r ∨ q.val < r) (j : Fin (2 * r + k + 1)) :
    Hpk k r p j = if j = q then 1 else 0 := by
  have hp := p.isLt
  have hq := q.isLt
  unfold Hpk
  by_cases hjq : j = q
  · subst hjq
    rw [if_pos rfl]
    rcases h with h | h
    · rw [if_pos ⟨h, hpq⟩]
    · rw [if_neg (by omega), if_pos ⟨h, hpq⟩]
  · rw [if_neg hjq]
    have hjv : j.val ≠ q.val := fun e => hjq (Fin.ext e)
    rw [if_neg (by omega), if_neg (by omega), if_neg]
    rintro ⟨h1, h2, -⟩
    omega

theorem uw_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val)
    (i : Fin (2 * r + k + 1)) : h i p = if i = p then 1 else 0 := by
  obtain ⟨-, hcols, -⟩ := hh
  have hplt := p.isLt
  rcases hp with hp | hp
  · have e : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have hx := congrFun (hcols ⟨p.val, hp⟩).1 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx
  · have e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have hx := congrFun (hcols ⟨2 * r + k - p.val, by omega⟩).2 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx

theorem uw_row (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (q : Fin (2 * r + k + 1)) (hq : q.val < r ∨ r + k < q.val)
    (j : Fin (2 * r + k + 1)) : h q j = if j = q then 1 else 0 := by
  have hqlt := q.isLt
  obtain ⟨p, hpd⟩ : ∃ p : Fin (2 * r + k + 1), p.val = 2 * r + k - q.val := ⟨⟨2 * r + k - q.val, by omega⟩, rfl⟩
  have hp : p.val < r ∨ r + k < p.val := by omega
  have hpq : p.val + q.val = 2 * r + k := by omega
  have hor : p.val < r ∨ q.val < r := by omega
  have hc : ∀ i, h i p = if i = p then 1 else 0 := uw_col k r z h hh p hp
  have hr : ∀ j', Hpk k r p j' = if j' = q then 1 else 0 := hpk_row k r p q hpq hor
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hx := congrFun (congrFun hU p) j
  simp only [Matrix.mul_apply, conjTranspose_apply, hc, hr] at hx
  simpa [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, hr] using hx

theorem torConj : CompanionTheory.Bmu.TorConj := by
  unfold CompanionTheory.Bmu.TorConj
  intro k r z c hz hc
  obtain ⟨T, hT0, hT1, hTc⟩ := exists_scale r c hc
  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * r + k + 1) → ℂ, d = fun i =>
      if i.val < r then T i.val else if i.val ≤ r + k then 1 else (star (T (2 * r + k - i.val)))⁻¹ :=
    ⟨_, rfl⟩
  have hdlow : ∀ i : Fin (2 * r + k + 1), i.val < r → d i = T i.val := fun i hi => by
    rw [hd]; simp only; rw [if_pos hi]
  have hdmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 1 := fun i h1 h2 => by
    rw [hd]; simp only; rw [if_neg (by omega), if_pos h2]
  have hdhigh : ∀ i : Fin (2 * r + k + 1), r + k < i.val → d i = (star (T (2 * r + k - i.val)))⁻¹ :=
    fun i hi => by
      rw [hd]; simp only; rw [if_neg (by omega), if_neg (by omega)]
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    by_cases h1 : i.val < r
    · rw [hdlow i h1]; exact hT0 _
    by_cases h2 : i.val ≤ r + k
    · rw [hdmid i (by omega) h2]; exact one_ne_zero
    · rw [hdhigh i (by omega)]; exact inv_ne_zero (star_ne_zero.mpr (hT0 _))
  have hHnz : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j ≠ 0 →
      (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
        (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
    intro i j h
    unfold Hpk at h
    split_ifs at h with h1 h2 h3 <;> first | exact absurd rfl h | tauto
  have hkey : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1 := by
    intro i j h
    have hilt := i.isLt
    have hjlt := j.isLt
    rcases hHnz i j h with ⟨hi, hij⟩ | ⟨hj, hij⟩ | ⟨hi1, hi2, rfl⟩
    · rw [hdlow i hi, hdhigh j (by omega), show 2 * r + k - j.val = i.val by omega]
      exact mul_inv_cancel₀ (star_ne_zero.mpr (hT0 _))
    · rw [hdhigh i (by omega), hdlow j hj, show 2 * r + k - i.val = j.val by omega]
      simp [hT0 j.val]
    · rw [hdmid i hi1 hi2]; simp
  have hdiagU : ∀ e : Fin (2 * r + k + 1) → ℂ, (∀ i j, Hpk k r i j ≠ 0 → star (e i) * e j = 1) →
      diagonal e ∈ UH (Hpk k r) := by
    intro e he
    show (diagonal e)ᴴ * Hpk k r * diagonal e = Hpk k r
    ext i j
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply]
    by_cases h0 : Hpk k r i j = 0
    · rw [h0]; ring
    · calc star (e i) * Hpk k r i j * e j = (star (e i) * e j) * Hpk k r i j := by ring
        _ = Hpk k r i j := by rw [he i j h0, one_mul]
  have hUmul : ∀ A B, A ∈ UH (Hpk k r) → B ∈ UH (Hpk k r) → A * B ∈ UH (Hpk k r) := by
    intro A B hA hB
    have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
    have hB' : Bᴴ * Hpk k r * B = Hpk k r := hB
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [conjTranspose_mul]
    calc Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hA', hB']
  have hτU : diagonal d ∈ UH (Hpk k r) := hdiagU d hkey
  have hτinvU : diagonal (fun i => (d i)⁻¹) ∈ UH (Hpk k r) := by
    refine hdiagU _ fun i j h => ?_
    rw [star_inv₀, ← mul_inv, hkey i j h, inv_one]
  have hτinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    have he : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hd0 i)
    rw [he, diagonal_one]
  have hcomm : ∀ h ∈ UWset k r z, diagonal d * h = h * diagonal d := by
    intro h hh
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : i = j
    · subst hij; ring
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_row k r z h hh i hi j, if_neg (fun e => hij e.symm)]; ring
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [uw_col k r z h hh j hj i, if_neg hij]; ring
    push_neg at hi hj
    rw [hdmid i hi.1 hi.2, hdmid j hj.1 hj.2]; ring
  have hzd : ∀ j, (d j)⁻¹ * z j = z j := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · push_neg at hj; rw [hdmid j hj.1 hj.2, inv_one, one_mul]
  refine ⟨diagonal d, hτU, hcomm, fun m hm => ?_⟩
  rw [hτinv]
  obtain ⟨hmU, hm2, hm3⟩ := hm
  have hent : ∀ i j, (diagonal d * m * diagonal (fun i => (d i)⁻¹)) i j = d i * m i j * (d j)⁻¹ := by
    intro i j
    rw [mul_diagonal, diagonal_mul]
  refine ⟨⟨hUmul _ _ (hUmul _ _ hτU hmU) hτinvU, ?_, ?_⟩, ?_⟩
  · intro a i hai
    rw [hent, hm2 a i hai]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · intro i j hj1 hj2 hi
    rw [hent, hm3 i j hj1 hj2 hi]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · have hsum : ∑ a, c a * PI.BesselMapUniq.ellA k r z (diagonal d * m * diagonal (fun i => (d i)⁻¹)) a =
        cStd * ell k r z m := by
      rw [ell, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PI.BesselMapUniq.ellA]
      have e1 : d (eI k r a) = T a.val := hdlow _ a.isLt
      split_ifs with ha
      · have e2 : d (eI k r ⟨a.val + 1, ha⟩) = T (a.val + 1) := hdlow _ ha
        rw [hent, e1, e2, ← mul_assoc, ← mul_assoc, hTc a,
          mul_right_comm (cStd * T (a.val + 1)), mul_inv_cancel_right₀ (hT0 _)]
      · have hmv : (diagonal d * m * diagonal (fun i => (d i)⁻¹)).mulVec z (eI k r a) =
            d (eI k r a) * m.mulVec z (eI k r a) := by
          simp only [mulVec, dotProduct, hent, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc d (eI k r a) * m (eI k r a) j * (d j)⁻¹ * z j
              = d (eI k r a) * m (eI k r a) j * ((d j)⁻¹ * z j) := by ring
            _ = d (eI k r a) * (m (eI k r a) j * z j) := by rw [hzd j]; ring
        rw [hmv, e1, ← mul_assoc, hTc a, hT1 _ (by omega), mul_one]
    rw [PI.BesselMapUniq.psiGen, psi, hsum]

end GlobalTheory.CompanionTheory.BmuTorConj
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesis
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTransport

open PI.UpqRep CompanionTheory.LimBd.SchurHpk

theorem dot_conj {n : ℕ} (P a Q : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ ((P * a * Q) *ᵥ x) = (u ᵥ* P) ⬝ᵥ (a *ᵥ (Q *ᵥ x)) := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem dot_expand {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ (a *ᵥ x) = ∑ p : Fin n × Fin n, u p.1 * x p.2 * a p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem kfin_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {v : H} (c : ℂ)
    (hv : IsKFinHpk (k := k) (r := r) σ v) : IsKFinHpk (k := k) (r := r) σ (c • v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, S.smul_mem c h2, h3⟩

theorem transport (U : URep k r) {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ g, q (P * g * P⁻¹) = P * q g * P⁻¹)
    (ν : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ)
    (Sm : Finset (Fin (2 * r + k + 1))) (Hs : Fin (2 * r + k + 1) → Type)
    [∀ s, NormedAddCommGroup (Hs s)] [∀ s, InnerProductSpace ℂ (Hs s)] [∀ s, CompleteSpace (Hs s)]
    (σs : ∀ s, Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs s →L[ℂ] Hs s))
    (hSm : ∀ s, s ∈ Sm ↔ IsHCParam (ν s))
    (ds : ∀ s ∈ Sm, IsHCParam (ν s) ∧ IsDS ε (ν s) (σs s))
    (toSum : ∀ (v w : U.R.H) (x y : Fin (2 * r + k + 1) → ℂ), IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) v →
      IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) w →
      ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin (2 * r + k + 1)) (vI wI : ∀ i, Hs (sI i)),
        (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, U.R.σ (P⁻¹ * g * P) v⟫_ℂ * (star y ⬝ᵥ (q g *ᵥ x)) =
          ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ)
    (ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
      ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → U.R.H) (xI yI : ι → Fin (2 * r + k + 1) → ℂ),
        (∀ i, IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (vI i) ∧ IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ =
          ∑ i, ⟪wI i, U.R.σ (P⁻¹ * g * P) (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (q g *ᵥ xI i))) :
    ∃ T : {s // IsHCParam (ν s)} → URep k r, (∀ s, (T s).R.IsDS ε (ν s)) ∧
      (∀ v w, U.R.KFin v → U.R.KFin w → ∀ c d, ∃ (I : Type) (_ : Fintype I) (s : I → {s // IsHCParam (ν s)})
        (y y' : ∀ i, (T (s i)).R.H),
        ∀ g ∈ GG k r, ⟪w, U.R.σ g v⟫_ℂ * q g c d = ∑ i, ⟪y' i, (T (s i)).R.σ g (y i)⟫_ℂ) ∧
      ∀ s, ∃ y : (T s).R.H, y ≠ 0 ∧ ∃ (I : Type) (_ : Fintype I) (v w : I → U.R.H)
        (c d : I → Fin (2 * r + k + 1)), (∀ i, U.R.KFin (v i) ∧ U.R.KFin (w i)) ∧
        ∀ g ∈ GG k r, ⟪y, (T s).R.σ g y⟫_ℂ = ∑ i, ⟪w i, U.R.σ g (v i)⟫_ℂ * q g (c i) (d i) := by
  have hk := fun v => CompanionTheory.CapEig.kfin_iff k r ε P U.R.H U.R.σ v hP
  have hds : ∀ s : {s // IsHCParam (ν s)}, IsDSHpk k r ε (ν s) (fun x => σs s (P * x * P⁻¹)) := fun s =>
    ⟨P, hP, by
      have e : (fun g => (fun x => σs s (P * x * P⁻¹)) (P⁻¹ * g * P)) = σs s := funext fun g => by
        simp only [forth_back hP.1]
      rw [e]
      exact (ds s ((hSm s).2 s.2)).2⟩
  refine ⟨fun s => ⟨⟨Hs s, fun x => σs s (P * x * P⁻¹)⟩, isURepOn_of_ds (hds s)⟩, fun s => ⟨s.2, hds s⟩,
    fun v w hv hw c d => ?_, fun s => ?_⟩
  · obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := toSum v w (P *ᵥ Pi.single d 1) (star (Pi.single c 1 ᵥ* P⁻¹))
      ((hk v).1 hv) ((hk w).1 hw)
    refine ⟨ι, inferInstance, fun i => ⟨sI i, (hSm _).1 (hI i).1⟩, vI, wI, fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    rw [back_forth hP.1, hq, star_star, dot_conj, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc (q g), inv_mul_P hP.1, Matrix.mul_one, Matrix.vecMul_one, single_one_dotProduct,
      Matrix.mulVec_single_one] at this
    exact this
  · have hs := (hSm s).2 s.2
    obtain ⟨S, hS, hSK, -, ⟨y, hyS, hy0, -⟩, -⟩ := (ds s hs).2.2.2.2.2.2.1
    have hy : IsKFin ε (σs s) y := ⟨S, hS, hyS, hSK⟩
    obtain ⟨ι, _, vI, wI, xI, yI, hI, hsum⟩ := ofSum s hs y y hy hy
    refine ⟨y, hy0, ι × Fin (2 * r + k + 1) × Fin (2 * r + k + 1), inferInstance,
      fun p => ((star (yI p.1) ᵥ* P) p.2.1 * (P⁻¹ *ᵥ xI p.1) p.2.2) • vI p.1, fun p => wI p.1,
      fun p => p.2.1, fun p => p.2.2, fun p => ⟨kfin_smul _ ((hk _).2 (hI p.1).1), (hk _).2 (hI p.1).2⟩,
      fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    refine this.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [back_forth hP.1, hq, dot_conj, dot_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, inner_smul_right]
    ring

theorem zuckerman_hypothesis_holds : ZuckH := by
  intro t hZ k r ε μ U b h hU hg hlt
  obtain ⟨hμ, P, hP, hτ⟩ := hU
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := hZ _ ε μ U.R.H _ hμ hτ h hg hlt
  cases b
  · exact transport U hP (fun g => g) (fun _ => rfl) (shift false μ) X.Sm X.Hs X.σs hX X.ds X.toSum X.ofSum
  · have hi : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ :=
      fun g => by
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
          Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    obtain ⟨T, h1, h2, h3⟩ :=
      transport U hP (fun g => g⁻¹) hi (shift true μ) Y.Sm Y.Hs Y.σs hY Y.ds Y.toSum Y.ofSum
    refine ⟨T, h1, fun v w hv hw c d => h2 v w hv hw d c, fun s => ?_⟩
    obtain ⟨y, hy, I, _, v, w, c, d, hk, he⟩ := h3 s
    exact ⟨y, hy, I, inferInstance, v, w, d, c, hk, he⟩

end GlobalTheory.CompanionTheory.ZuckTransport

end
end

