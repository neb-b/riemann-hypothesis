module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealLower2
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

lemma real_upper {ρ α β Q : ℝ} (hρ1 : ρ < 1) (hρ0 : 0 ≤ ρ)
    (hQ : Q * (1 - ρ ^ 2) ≤ (α + ρ * β) ^ 2) :
    2 * Q - (α ^ 2 - β ^ 2) ≤ (1 + ρ) / (1 - ρ) * (α ^ 2 + β ^ 2) := by
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 + ρ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith [mul_nonneg hρ0 (sq_nonneg (α - β)), mul_le_mul_of_nonneg_left hQ h2.le]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma mj_xZ_zero (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show (mat x τ * X.lowBlock 0 τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [h1, Matrix.mul_one]
  rfl

private lemma nsq_add_fundamental_domains {n : ℕ} (p q : Fin n → ℂ) :
    nsq (p + q) = nsq p + 2 * (mjip p q).re + nsq q := by
  rw [show p + q = p - ((-1 : ℝ) : ℂ) • q by simp, mjnsq_sub_smul]
  ring

private lemma re_mjip_comm {n : ℕ} (p q : Fin n → ℂ) : (mjip q p).re = (mjip p q).re := by
  simp only [mjip, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

private lemma mjip_sub_left {n : ℕ} (p q δ : Fin n → ℂ) :
    mjip (p - q) δ = mjip p δ - mjip q δ := by
  simp [mjip, sub_mul, Finset.sum_sub_distrib]

private lemma re_mjip_le_sqrt_nsq_mul {n : ℕ} (p q : Fin n → ℂ) :
    (mjip p q).re ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) :=
  (Complex.re_le_norm _).trans (mjip_norm_le p q)

private lemma neg_re_mjip_le_sqrt_nsq_mul {n : ℕ} (p q : Fin n → ℂ) :
    -(mjip p q).re ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) :=
  (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (mjip_norm_le p q))

private lemma sqrt_nsq_mulVec_le_opN_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    Real.sqrt (nsq (A *ᵥ v)) ≤ Data.opN A * Real.sqrt (nsq v) := by
  rw [← Real.sqrt_sq (opN_nonneg A), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (nsq_mulVec_le_opN A v)


set_option maxHeartbeats 800000 in
theorem mj_bounds {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1 / 10) {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (hy : X.xZ x Z ∈ X.dom) (τ : X.Ψ)
    (v : Fin r → ℂ) :
    (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
      X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v := by
  obtain ⟨w, rfl⟩ : ∃ w, v = mat x τ *ᵥ w := ⟨(mat x τ)⁻¹ *ᵥ v, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr ((X.mem_dom_iff x).1 hx τ).1), Matrix.one_mulVec]⟩
  have hx0 : X.xZ x 0 ∈ X.dom := by rw [mj_xZ_zero]; exact hx
  obtain ⟨γ0, h0maj, h0id⟩ := mj_coord X ho 0 hx0 τ w
  rw [mj_xZ_zero] at h0maj
  have hZ0 : Matrix.of ((0 : X.Coord) τ) = 0 := by ext; rfl
  have hγ0 : γ0 = mjpa X w := by
    funext d
    have := h0id (Pi.single d 1)
    simp only [hZ0, Matrix.zero_mulVec, mjip_zero_right, sub_zero, mjip_single] at this
    exact this.symm
  have hmx : X.maj x τ (mat x τ *ᵥ w) = nsq (mjpa X w) + nsq (mjpb X w) := by
    rw [h0maj, hZ0, Matrix.zero_mulVec, nsq_zero', hγ0]
    ring
  obtain ⟨γ, hmaj, hid⟩ := mj_coord X ho Z hy τ w
  rw [hmx, hmaj]
  have hk0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := opN_nonneg _
  have hkρ : Data.opN (Matrix.of (Z τ)) ≤ ρ := (opN_le_zN X Z τ).trans hZ
  have hs2 : nsq (Matrix.of (Z τ) *ᵥ γ) ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq γ :=
    nsq_mulVec_le_opN _ _
  have hS : Real.sqrt (nsq (Matrix.of (Z τ) *ᵥ γ)) ≤ Data.opN (Matrix.of (Z τ)) * Real.sqrt (nsq γ) :=
    sqrt_nsq_mulVec_le_opN_mul _ _
  have hdid : ∀ δ, mjip (mjpa X w - γ) δ =
      mjip (mjpb X w - Matrix.of (Z τ) *ᵥ γ) (Matrix.of (Z τ) *ᵥ δ) := by
    intro δ
    rw [mjip_sub_left, mjip_sub_left]
    linear_combination hid δ
  set Zm := Matrix.of (Z τ) with hZm
  set k := Data.opN Zm with hkdef
  set d := mjpa X w - γ with hd
  set t := mjpb X w - Zm *ᵥ γ with ht
  have hG0 := Real.sqrt_nonneg (nsq γ)
  have hT0 := Real.sqrt_nonneg (nsq t)
  have hD0 := Real.sqrt_nonneg (nsq d)
  have hG2 := Real.sq_sqrt (nsq_nonneg γ)
  have hT2 := Real.sq_sqrt (nsq_nonneg t)
  have hD2 := Real.sq_sqrt (nsq_nonneg d)
  have hDs : Real.sqrt (nsq d) ≤ k * Real.sqrt (nsq t) := by
    have h1 : nsq d = (mjip t (Zm *ᵥ d)).re := by rw [← hdid, mjip_self, Complex.ofReal_re]
    have h2 := re_mjip_le_sqrt_nsq_mul t (Zm *ᵥ d)
    have h4 : Real.sqrt (nsq (Zm *ᵥ d)) ≤ k * Real.sqrt (nsq d) := sqrt_nsq_mulVec_le_opN_mul Zm d
    have h5 : Real.sqrt (nsq d) ^ 2 ≤ Real.sqrt (nsq t) * (k * Real.sqrt (nsq d)) := by
      calc Real.sqrt (nsq d) ^ 2 = nsq d := hD2
        _ = (mjip t (Zm *ᵥ d)).re := h1
        _ ≤ _ := h2.trans (mul_le_mul_of_nonneg_left h4 hT0)
    rcases eq_or_lt_of_le hD0 with h | h
    · rw [← h]
      positivity
    · nlinarith
  have hdd : nsq d ≤ k ^ 2 * nsq t := by
    calc nsq d = Real.sqrt (nsq d) ^ 2 := hD2.symm
      _ ≤ (k * Real.sqrt (nsq t)) ^ 2 := pow_le_pow_left₀ hD0 hDs 2
      _ = k ^ 2 * nsq t := by rw [mul_pow, hT2]
  have hAe : nsq (mjpa X w) = nsq γ + 2 * (mjip γ d).re + nsq d := by
    rw [show mjpa X w = γ + d by rw [hd]; abel, nsq_add_fundamental_domains]
  have hBe : nsq (mjpb X w) = nsq (Zm *ᵥ γ) + 2 * (mjip (Zm *ᵥ γ) t).re + nsq t := by
    rw [show mjpb X w = Zm *ᵥ γ + t by rw [ht]; abel, nsq_add_fundamental_domains]
  have hcross : (mjip γ d).re = (mjip (Zm *ᵥ γ) t).re := by
    rw [re_mjip_comm d γ, hdid γ, re_mjip_comm (Zm *ᵥ γ) t]
  have hs2' : nsq (Zm *ᵥ γ) ≤ k ^ 2 * nsq γ := hs2
  have hS' : Real.sqrt (nsq (Zm *ᵥ γ)) ≤ k * Real.sqrt (nsq γ) := hS
  have hk1 : k < 1 := by linarith
  refine ⟨?_, ?_⟩
  · have hlow : (1 - k ^ 2) * (nsq γ + nsq t) ≤
        2 * (nsq γ - nsq (Zm *ᵥ γ)) - (nsq (mjpa X w) - nsq (mjpb X w)) := by
      rw [hAe, hBe, hcross]
      nlinarith [hs2', hdd]
    have r1 : (mjip γ d).re ≤ Real.sqrt (nsq γ) * (k * Real.sqrt (nsq t)) :=
      (re_mjip_le_sqrt_nsq_mul γ d).trans (mul_le_mul_of_nonneg_left hDs hG0)
    have r2 : (mjip (Zm *ᵥ γ) t).re ≤ (k * Real.sqrt (nsq γ)) * Real.sqrt (nsq t) :=
      (re_mjip_le_sqrt_nsq_mul (Zm *ᵥ γ) t).trans (mul_le_mul_of_nonneg_right hS' hT0)
    have hAB : nsq (mjpa X w) + nsq (mjpb X w) ≤ (1 + k) ^ 2 * (nsq γ + nsq t) := by
      rw [hAe, hBe]
      nlinarith [mul_nonneg hk0 (sq_nonneg (Real.sqrt (nsq γ) - Real.sqrt (nsq t)))]
    have hc : (1 - ρ) / (1 + ρ) ≤ (1 - k) / (1 + k) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hAB0 : 0 ≤ nsq (mjpa X w) + nsq (mjpb X w) := add_nonneg (nsq_nonneg _) (nsq_nonneg _)
    calc (1 - ρ) / (1 + ρ) * (nsq (mjpa X w) + nsq (mjpb X w))
        ≤ (1 - k) / (1 + k) * (nsq (mjpa X w) + nsq (mjpb X w)) := mul_le_mul_of_nonneg_right hc hAB0
      _ ≤ (1 - k) / (1 + k) * ((1 + k) ^ 2 * (nsq γ + nsq t)) :=
          mul_le_mul_of_nonneg_left hAB (div_nonneg (by linarith) (by linarith))
      _ = (1 - k ^ 2) * (nsq γ + nsq t) := by
          field_simp
          ring
      _ ≤ _ := hlow
  · have hQid : nsq γ - nsq (Zm *ᵥ γ) = (mjip (mjpa X w) γ).re - (mjip (mjpb X w) (Zm *ᵥ γ)).re := by
      have := congrArg Complex.re (hid γ)
      simp only [Complex.sub_re, mjip_self, Complex.ofReal_re] at this
      linarith
    have r3 := re_mjip_le_sqrt_nsq_mul (mjpa X w) γ
    have r4 := neg_re_mjip_le_sqrt_nsq_mul (mjpb X w) (Zm *ᵥ γ)
    have hβ0 := Real.sqrt_nonneg (nsq (mjpb X w))
    have hα0 := Real.sqrt_nonneg (nsq (mjpa X w))
    have r5 : Real.sqrt (nsq (mjpb X w)) * Real.sqrt (nsq (Zm *ᵥ γ)) ≤
        Real.sqrt (nsq (mjpb X w)) * (ρ * Real.sqrt (nsq γ)) :=
      mul_le_mul_of_nonneg_left (hS'.trans (mul_le_mul_of_nonneg_right hkρ hG0)) hβ0
    have hQle : nsq γ - nsq (Zm *ᵥ γ) ≤
        (Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w))) * Real.sqrt (nsq γ) := by
      rw [hQid]
      linarith [r3, r4, r5]
    have hkk : k ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hk0 hkρ 2
    have hQge : (1 - ρ ^ 2) * nsq γ ≤ nsq γ - nsq (Zm *ᵥ γ) := by
      linarith [hs2', mul_le_mul_of_nonneg_right hkk (nsq_nonneg γ)]
    have hρ2 : 0 ≤ 1 - ρ ^ 2 := by
      have : ρ ^ 2 ≤ ρ := by
        rw [sq]
        exact mul_le_of_le_one_left hρ0.le (by linarith)
      linarith
    have hQ0 : 0 ≤ nsq γ - nsq (Zm *ᵥ γ) := le_trans (mul_nonneg hρ2 (nsq_nonneg γ)) hQge
    have hup : (nsq γ - nsq (Zm *ᵥ γ)) * (1 - ρ ^ 2) ≤
        (Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w))) ^ 2 := by
      set s := Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w)) with hs
      set Q := nsq γ - nsq (Zm *ᵥ γ) with hQ
      rcases eq_or_lt_of_le hQ0 with hq | hq
      · rw [← hq, zero_mul]
        positivity
      · have hsq : Q ^ 2 ≤ (s * Real.sqrt (nsq γ)) ^ 2 := pow_le_pow_left₀ hQ0 hQle 2
        rw [mul_pow, hG2] at hsq
        nlinarith [mul_le_mul_of_nonneg_left hQge (sq_nonneg s), mul_le_mul_of_nonneg_right hsq hρ2]
    have := real_upper (ρ := ρ) (α := Real.sqrt (nsq (mjpa X w))) (β := Real.sqrt (nsq (mjpb X w)))
      (Q := nsq γ - nsq (Zm *ᵥ γ)) (by linarith) hρ0.le hup
    rwa [Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at this

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma bound_castLE {n : ℕ} (h : n ≤ X.p0) (Z : X.Coord) (τ : X.Ψ) (y : Fin n → ℂ) :
    nsq ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) ≤
      X.zN Z ^ 2 * nsq y := by
  classical
  set z : Fin X.p0 → ℂ := fun c => if h' : (c : ℕ) < n then y ⟨c, h'⟩ else 0 with hz
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  have hzc : ∀ b : Fin n, z (Fin.castLE h b) = y b := by
    intro b
    simp [hz, b.isLt]
  have hz0 : ∀ c ∉ Set.range (Fin.castLE h), z c = 0 := by
    intro c hc
    simp only [hz]
    rw [dite_eq_right]
    intro hcn
    exact hc ⟨⟨c, hcn⟩, Fin.ext rfl⟩
  have hvec : ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) =
      (Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ z := by
    funext m
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]
    refine Fintype.sum_of_injective (M := ℂ) (Fin.castLE h) hinj _ _ ?_ ?_
    · intro c hc
      simp [hz0 c hc]
    · intro b
      simp [hzc b]
  have hnz : nsq z = nsq y := by
    unfold nsq
    exact (Fintype.sum_of_injective (M := ℝ) (Fin.castLE h) hinj _ _ (fun c hc => by simp [hz0 c hc])
      (fun b => by simp [hzc b])).symm
  have hconj : ∀ {q : ℕ} (w : Fin q → ℂ), nsq (fun m => conj (w m)) = nsq w := by
    intro q w
    unfold nsq
    simp
  have hmap : ∀ w : Fin X.p0 → ℂ, nsq ((Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ w) =
      nsq (Matrix.of (Z τ) *ᵥ fun c => conj (w c)) := by
    intro w
    rw [← hconj (Matrix.of (Z τ) *ᵥ fun c => conj (w c))]
    congr 1
    funext m
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have hop0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := by
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hop : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
    unfold Data.zN
    exact le_ciSup (f := fun τ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ
  rw [hvec, hmap, ← hnz, ← hconj z]
  calc nsq (Matrix.of (Z τ) *ᵥ fun c => conj (z c))
      ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq (fun c => conj (z c)) := nsq_mulVec_le_opN _ _
    _ ≤ X.zN Z ^ 2 * nsq (fun c => conj (z c)) := by
      gcongr
      exact nsq_nonneg _

lemma det_lowBlock (Z : X.Coord) (τ : X.Ψ) : (X.lowBlock Z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro a _
    simp only [Data.lowBlock, Matrix.of_apply, if_true]
    rw [dite_eq_right (by omega)]
    simp
  · intro a b hab
    have hab' : a < b := hab
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab'), dite_eq_right]
    · simp
    · intro hh
      have : (a : ℕ) < b := hab'
      omega

lemma psgn_add (p0 k : ℕ) : psgn p0 (p0 + k) = (-1) ^ k := by
  induction k with
  | zero => simp [psgn_eq_one le_rfl]
  | succ k ih =>
    rw [← add_assoc, psgn_succ, ih, sgn, if_neg (by omega), pow_succ]

lemma signType_cancel_identity (k : ℕ) (D : ℂ) (hD : 0 < D.re) : 0 < (-1 : ℝ) ^ k * (((-1 : ℂ) ^ k) * D).re := by
  have h1 : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.re_ofReal_mul, ← mul_assoc, ← mul_pow]
  norm_num
  exact hD

lemma pos_re_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) : 0 < M.det.re := by
  exact (Complex.pos_iff.mp hM.det_pos).1

lemma minor_le {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (i : Fin (r + 1)) (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  rw [psgn_eq_one hip, one_mul]
  set A : Matrix (Fin (r - X.p0)) (Fin (i : ℕ)) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE hip b) with hA
  set B : Matrix (Fin 0) (Fin (i : ℕ)) ℂ := 0 with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X hip Z τ) hs0
  have heq : dmin X.Gm (X.xZ x Z) τ i = (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ]
    congr 1
    ext a b
    have hca : (Fin.castLE (Nat.le_of_lt_succ i.isLt) a : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip a) :=
      Fin.ext rfl
    have hcb : (Fin.castLE (Nat.le_of_lt_succ i.isLt) b : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip b) :=
      Fin.ext rfl
    rw [Matrix.submatrix_apply, hca, hcb, Gp_pp]
    simp [hA, hB, Matrix.one_apply, Matrix.mul_apply, Fin.castLE_inj]
  rw [heq]
  exact pos_re_of_posDef hpd

lemma minor_gt {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (k : ℕ) (hk : k ≤ r - X.p0) (i : Fin (r + 1)) (hik : (i : ℕ) = X.p0 + k) :
    0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  obtain ⟨i, hi⟩ := i
  simp only at hik
  subst hik
  rw [show ((⟨X.p0 + k, hi⟩ : Fin (r + 1)) : ℕ) = X.p0 + k from rfl, psgn_add]
  set A : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE (le_refl X.p0) b) with hA
  set B : Matrix (Fin k) (Fin X.p0) ℂ := Matrix.of fun m c => Z τ (Fin.castLE hk m) c with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X (le_refl X.p0) Z τ) hs0
  haveI : Invertible (1 : Matrix (Fin k) (Fin k) ℂ) := invertibleOne
  haveI : Invertible (-1 : Matrix (Fin k) (Fin k) ℂ) := invertibleNeg 1
  have heq : dmin X.Gm (X.xZ x Z) τ ⟨X.p0 + k, hi⟩ =
      (-1 : ℂ) ^ k * (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hc1 : ∀ a : Fin X.p0, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inl a)) : Fin r) =
        Fin.castLE X.p0_le a := fun a => Fin.ext (by simp)
    have hc2 : ∀ m : Fin k, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inr m)) : Fin r) =
        nI X (Fin.castLE hk m) := fun m => Fin.ext (by simp [nI])
    have hblk : ((Gp X Z τ).submatrix (Fin.castLE (Nat.le_of_lt_succ hi)) (Fin.castLE (Nat.le_of_lt_succ hi))).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (1 - Aᵀ * A.map (starRingEnd ℂ)) (-Bᵀ) (-(B.map (starRingEnd ℂ))) (-1) := by
      ext (a | m) (b | m')
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, Gp_pp, Matrix.fromBlocks_apply₁₁]
        simp [hA, Matrix.one_apply, Matrix.mul_apply]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_pn, Matrix.fromBlocks_apply₁₂]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_np, Matrix.fromBlocks_apply₂₁]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc2, Gp_nn, Matrix.fromBlocks_apply₂₂]
        simp [Matrix.one_apply, Fin.castLE_inj]
    rw [hblk, Matrix.det_fromBlocks₂₂, invOf_neg, invOf_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      mul_one]
    congr 2
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, sub_neg_eq_add]
  rw [heq]
  exact signType_cancel_identity k _ (pos_re_of_posDef hpd)

theorem xZ_mem_dom {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) :
    X.xZ x Z ∈ X.dom := by
  rw [Data.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * X.lowBlock Z τ).det ≠ 0
    rw [Matrix.det_mul, det_lowBlock, mul_one]
    exact (hx τ).1
  · by_cases hip : (i : ℕ) ≤ X.p0
    · exact minor_le X ho hZ τ i hip
    · have hi := i.isLt
      have := X.p0_le
      exact minor_gt X ho hZ τ ((i : ℕ) - X.p0) (by omega) i (by omega)

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

