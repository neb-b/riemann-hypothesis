module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.ZnNonneg

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.DivLeExpOfAbsLogSubLe
section
namespace PIW.FdPA

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric

noncomputable section

theorem inv_mul_between_ratio {c m m0 ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) (hm0 : c * m0 = 1)
    (hlo : (1 - ρ) / (1 + ρ) * m0 ≤ m) (hhi : m ≤ (1 + ρ) / (1 - ρ) * m0) :
    (1 - ρ) / (1 + ρ) ≤ 1 / (c * m) ∧ 1 / (c * m) ≤ (1 + ρ) / (1 - ρ) := by
  have hm0pos : 0 < m0 := by nlinarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have h1ρ' : 0 < 1 + ρ := by linarith
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hlo
  have hcm : 1 / (c * m) = m0 / m := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-m) * hm0
  rw [hcm]
  constructor
  · rw [div_le_div_iff₀ h1ρ' hmpos]
    have h := hhi
    rw [div_mul_eq_mul_div, le_div_iff₀ h1ρ] at h
    linarith
  · rw [div_le_div_iff₀ hmpos h1ρ]
    have h := hlo
    rw [div_mul_eq_mul_div, div_le_iff₀ h1ρ'] at h
    linarith

theorem div_le_exp_of_abs_log_sub_le {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (h : |Real.log b - Real.log a| ≤ K) :
    a / b ≤ Real.exp K := by
  have h1 : a / b = Real.exp (Real.log a - Real.log b) := by
    rw [Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
  rw [h1]
  apply Real.exp_le_exp.mpr
  have h2 := neg_le_abs (Real.log b - Real.log a)
  linarith

theorem small_power_bound {w r rh z : ℝ} (hr0 : 0 ≤ r) (hrw : r ≤ w) (hw : 0 ≤ w) (hrh : 0 ≤ rh)
    (hwrh : w * rh ≤ 1 / 36) (hz0 : 0 ≤ z) (hz : z ≤ rh) : 4 * w * r * z ^ 2 ≤ 1 / 4 := by
  have h1 : w * r ≤ w * w := mul_le_mul_of_nonneg_left hrw hw
  have h2 : z ^ 2 ≤ rh ^ 2 := pow_le_pow_left₀ hz0 hz 2
  have h3 : (w * rh) ^ 2 ≤ (1 / 36) ^ 2 := pow_le_pow_left₀ (mul_nonneg hw hrh) hwrh 2
  have h4 : w * r * z ^ 2 ≤ w * w * rh ^ 2 :=
    mul_le_mul h1 h2 (sq_nonneg z) (mul_nonneg hw hw)
  nlinarith

theorem rh_facts {c1 w : ℝ} (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < d6rh c1 w ∧ d6rh c1 w < 1 / 10 ∧ w * d6rh c1 w ≤ 1 / 36 := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.d6rh
  have hpi := Real.pi_gt_three
  have hw0 : 0 < w := by linarith
  have hpos : 0 < 12 * Real.pi * (c1 + w) := by positivity
  have hp3 : (0 : ℝ) < Real.pi - 3 := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_div_iff₀ hpos (by norm_num)]
    nlinarith [mul_pos hc1 hp3, mul_pos hw0 hp3]
  · rw [mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
    nlinarith [mul_pos hc1 hp3, mul_pos hw0 hp3]

theorem fundamentalDomain_of_parts {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hFd : FjDiff E) (hFb : FjBEq E) (hFc : FjBdd E) (hOD : OrthoDom E) (hUD : UnitDom E)
    (hBF : BorFlag E) (hZs : ZnSmul E) (hZn : ZnNonneg E) (hNp : NfacPos E) (hX0 : XZZero E)
    (h0 : OrthonormalFlagTranslate (E := E)) (h1 : OrthonormalChartNormControl (E := E)) (h2 : NearSupremumTransference (E := E))
    (h3 : SchwarzLemmaBall) (h4 : OrthonormalShortVectorBound (E := E)) (h7 : UnitaryUnipotentMove (E := E)) :
    FundamentalDomainPointBound (E := E) := by
  intro r X la P ξ ν c1 w z0 hD hrw
  dsimp only
  intro n' hn'
  obtain ⟨-, hPSS, hIso, hc1, -, -, hw1, hspr, -, hz0D1, hsup⟩ := id hD
  have hBdd : X.IsBddSec la P := hPSS.1
  have hSec : X.IsSec la P := hBdd.1
  have hFdiff : DifferentiableOn ℂ (X.fj la ξ ν P) X.dom := hFd r X.toData la P ξ ν hBdd hIso
  have hFb' : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.fj la ξ ν P (rmul x b) = bchar la b * X.fj la ξ ν P x :=
    hFb r X.toData la P ξ ν hSec hIso
  obtain ⟨C, hC⟩ := hFc r X.toData la P ξ ν hBdd hIso
  obtain ⟨hP0a, hP0b, hP0c⟩ := h0 r X.toData
  have hpn_inv := hP0b la (X.fj la ξ ν P) hFb'
  obtain ⟨hz0dom, hz0c⟩ := hz0D1
  have hself : ∀ x, X.SameFlag x x := fun x τ => rfl
  have htrans : ∀ x y z, X.SameFlag x y → X.SameFlag y z → X.SameFlag x z :=
    fun x y z h1 h2 τ => (h1 τ).trans (h2 τ)
  set F := X.fj la ξ ν P with hF
  have hpn_le_hat : ∀ y ∈ X.dom, X.pnorm la F y ≤ X.hatN la F y := by
    intro y hy
    refine le_csSup ⟨C, ?_⟩ ⟨y, hy, hself y, rfl⟩
    rintro _ ⟨x', hx', -, rfl⟩
    exact hC x' hx'
  have hhat_le : ∀ y ∈ X.dom, X.hatN la F y ≤ C := by
    intro y hy
    refine csSup_le ⟨_, y, hy, hself y, rfl⟩ ?_
    rintro _ ⟨x', hx', -, rfl⟩
    exact hC x' hx'
  set S := sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la F y} with hS
  have hSbdd : BddAbove {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la F y} :=
    ⟨C, by rintro _ ⟨y, hy, rfl⟩; exact hhat_le y hy.1⟩
  have hz0S : X.hatN la F z0 ≤ S := le_csSup hSbdd ⟨z0, ⟨hz0dom, hz0c⟩, rfl⟩
  have hlt : S / 2 < sSup {t | ∃ x' ∈ X.dom, X.SameFlag z0 x' ∧ t = X.pnorm la F x'} := by
    have h := hsup
    change S < 2 * X.hatN la F z0 at h
    change S / 2 < X.hatN la F z0
    linarith
  obtain ⟨_, ⟨x', hx'dom, hzx', rfl⟩, hx'lt⟩ :=
    exists_lt_of_lt_csSup (⟨_, z0, hz0dom, hself z0, rfl⟩ :
      {t | ∃ x' ∈ X.dom, X.SameFlag z0 x' ∧ t = X.pnorm la F x'}.Nonempty) hlt
  have hx'le : X.pnorm la F x' ≤ S := by
    refine le_trans ?_ hz0S
    refine le_csSup ⟨C, ?_⟩ ⟨x', hx'dom, hzx', rfl⟩
    rintro _ ⟨y, hy, -, rfl⟩
    exact hC y hy
  have hS0 : 0 ≤ S := by
    refine le_trans ?_ hx'le
    exact mul_nonneg (norm_nonneg _) (hNp r X.toData la x' hx'dom).le
  obtain ⟨b, hb, hortho⟩ := hP0a x' hx'dom
  have hx0dom : rmul x' b ∈ X.dom := hOD r X.toData _ hortho
  have hx'x0 : X.SameFlag x' (rmul x' b) := hBF r X.toData x' b hb hx0dom
  have hz0x0 : X.SameFlag z0 (rmul x' b) := htrans _ _ _ hzx' hx'x0
  have hpx0 : X.pnorm la F (rmul x' b) = X.pnorm la F x' := hpn_inv x' hx'dom b hb
  have hmaj : X.maj z0 = X.maj (rmul x' b) := (hP0c z0 hz0dom _ hx0dom hz0x0).2
  set x0 := rmul x' b with hx0
  obtain ⟨hrh0, hrh1, hwrh⟩ := rh_facts (c1 := c1) (w := w) hc1 hw1
  obtain ⟨hP1b, -⟩ := h1 r X.toData x0 hx0dom hortho (d6rh c1 w) hrh0 hrh1.le
  obtain ⟨-, hP1d⟩ := h1 r X.toData x0 hx0dom hortho (1 / 10) (by norm_num) le_rfl
  obtain ⟨lam, h1m, Z1, hU1, hline, hUz, hsplit1, hflag1, hZ1⟩ :=
    h4 r X la P ξ ν c1 w z0 hD x0 hx0dom hortho hz0x0
  obtain ⟨n, Z, hUn, -, hn'p, hsplit, hflag, hZ⟩ :=
    h7 r X la P ξ ν c1 w z0 hD x0 hx0dom hortho hz0x0 lam h1m Z1 hU1 hline hUz hsplit1 hflag1
      hZ1 n' hn'
  set rh := d6rh c1 w with hrh
  have hZn0 : 0 ≤ X.zN Z := hZn r X.toData Z
  have hZle : X.zN Z ≤ rh := by linarith
  obtain ⟨hxdom, -, -⟩ := hP1b Z hZle
  have hx''dom : X.lmulC n (X.lmulC h1m z0) ∈ X.dom :=
    hUD r X.toData n _ hUn (hUD r X.toData h1m z0 hU1 hz0dom)
  obtain ⟨hJ, -, hA⟩ := (hP0c _ hx''dom _ hxdom hflag).1 ξ
  have hucomp : ∀ u, X.ucomp (X.lmulC n (X.lmulC h1m z0)) ξ u = X.ucomp (X.xZ x0 Z) ξ u :=
    fun u => by simp only [Data.ucomp, hA]
  refine ⟨X.xZ x0 Z, hxdom, lam, ?_⟩
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsplit
  refine ⟨s1, s2, s3, fun j hj => ?_, fun j hj => ?_, s6, fun μ hμ => ?_, ?_⟩
  · obtain ⟨a1, a2⟩ := s4 j hj
    refine ⟨a1, ?_⟩
    rw [← hJ, ← hucomp]
    exact a2
  · obtain ⟨a1, a2⟩ := s5 j hj
    refine ⟨a1, ?_⟩
    rw [← hJ, ← hucomp]
    exact a2
  · obtain ⟨e, he, he2⟩ := hn'p μ hμ
    exact ⟨e, he, by rw [← hA]; exact he2⟩
  · set s := X.zN Z with hs
    have hmaxpos : 0 < max s (rh / 22) := lt_max_of_lt_right (by positivity)
    set ρ := rh / max s (rh / 22) with hρ
    have hρpos : 0 < ρ := div_pos hrh0 hmaxpos
    have hρs : ρ * s ≤ rh := by
      rw [hρ, div_mul_eq_mul_div, div_le_iff₀ hmaxpos]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hrh0.le
    have h21 : 21 < ρ := by
      rw [hρ, lt_div_iff₀ hmaxpos]
      rcases le_total s (rh / 22) with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h]
        linarith
    have hzt : ∀ t : ℂ, ‖t‖ ≤ ρ → X.zN (t • Z) ≤ rh := by
      intro t ht
      rw [hZs r X.toData t Z]
      calc ‖t‖ * s ≤ ρ * s := mul_le_mul_of_nonneg_right ht hZn0
        _ ≤ rh := hρs
    have hx0nf : 0 < X.nfac la x0 := hNp r X.toData la x0 hx0dom
    let γ : ℂ → ℂ := fun t => F (X.xZ x0 (t • Z)) * (X.nfac la x0 : ℂ)
    have hγd : DifferentiableOn ℂ γ (closedBall 0 ρ) := by
      have hG := hP1d F hFdiff
      have hlin : Differentiable ℂ (fun t : ℂ => t • Z) := differentiable_id.smul_const Z
      refine (hG.comp hlin.differentiableOn ?_).mul_const _
      intro t ht
      simp only [Set.mem_setOf_eq]
      have h := hzt t (mem_closedBall_zero_iff.mp ht)
      linarith
    have hγb : ∀ t ∈ closedBall (0 : ℂ) ρ, ‖γ t‖ ≤ Real.exp (9 / 4) * S := by
      intro t ht
      have htb := hzt t (mem_closedBall_zero_iff.mp ht)
      obtain ⟨hydom, hylog, hymaj⟩ := hP1b (t • Z) htb
      have hynf : 0 < X.nfac la (X.xZ x0 (t • Z)) := hNp r X.toData la _ hydom
      have hlog := hylog la w hspr
      have hsm : 4 * w * r * X.zN (t • Z) ^ 2 ≤ 1 / 4 :=
        small_power_bound (by positivity) hrw (by linarith) hrh0.le hwrh (hZn r X.toData _) htb
      have hratio : X.nfac la x0 / X.nfac la (X.xZ x0 (t • Z)) ≤ Real.exp (1 / 4) :=
        div_le_exp_of_abs_log_sub_le hx0nf hynf (by linarith)
      have htt : ∀ τ, (1 - rh) / (1 + rh) ≤ X.tt ξ (X.xZ x0 (t • Z)) τ ∧
          X.tt ξ (X.xZ x0 (t • Z)) τ ≤ (1 + rh) / (1 - rh) := by
        intro τ
        have hcpos : 0 < X.c τ :=
          mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr X.ξ0_ne))
        have hm0 : X.c τ * X.maj x0 τ (Data.emb τ.1 ξ) = 1 := by
          rw [← hmaj]
          exact hz0c τ
        obtain ⟨hlo, hhi⟩ := hymaj τ (Data.emb τ.1 ξ)
        exact inv_mul_between_ratio hrh0 (by linarith) hcpos hm0 hlo hhi
      have hyhat : X.hatN la F (X.xZ x0 (t • Z)) ≤ Real.exp 2 * S :=
        h2 r X la P ξ ν c1 w z0 hD _ hydom htt
      have hpy : X.pnorm la F (X.xZ x0 (t • Z)) =
          ‖F (X.xZ x0 (t • Z))‖ * X.nfac la (X.xZ x0 (t • Z)) := by
        rw [Data.pnorm, Data.nfac]
      have hnorm : ‖γ t‖ = X.pnorm la F (X.xZ x0 (t • Z)) *
          (X.nfac la x0 / X.nfac la (X.xZ x0 (t • Z))) := by
        simp only [γ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0nf, hpy]
        field_simp
      rw [hnorm]
      calc X.pnorm la F (X.xZ x0 (t • Z)) * (X.nfac la x0 / X.nfac la (X.xZ x0 (t • Z)))
          ≤ (Real.exp 2 * S) * Real.exp (1 / 4) :=
            mul_le_mul ((hpn_le_hat _ hydom).trans hyhat) hratio
              (div_nonneg hx0nf.le hynf.le) (mul_nonneg (Real.exp_pos 2).le hS0)
        _ = Real.exp (9 / 4) * S := by
            rw [mul_right_comm, ← Real.exp_add]
            norm_num
    have hγ0 : ‖γ 0‖ = X.pnorm la F x0 := by
      simp only [γ, zero_smul, hX0 r X.toData x0, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hx0nf]
      rw [Data.pnorm, Data.nfac]
    have hP3 := h3 ℂ γ ρ S hρpos hγd hγb (by rw [hγ0, hpx0]; linarith)
      (by rw [hγ0, hpx0]; exact hx'le) 1
      (by rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ (by norm_num)]; linarith)
    intro hF0
    apply hP3
    simp only [γ, one_smul]
    rw [hF0, zero_mul]

end

end PIW.FdPA
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
section
namespace PIW.FdPA

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate

noncomputable section

theorem mem_dom_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) : x ∈ X.dom ↔ ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := Iff.rfl

theorem gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem det_ne_of_gram {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (h : (gram τ G M).det ≠ 0) : M.det ≠ 0 := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  intro h0
  apply h
  rw [h0, zero_mul, zero_mul]

theorem lminor_last {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) : lminor M (Fin.last r) = M.det := by
  rfl

theorem det_of_minors {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (τ : X.Ψ) (h : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re) :
    (mat x τ).det ≠ 0 := by
  have h1 := h (Fin.last r)
  have h2 : dmin X.Gm x τ (Fin.last r) ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  unfold dmin at h2
  rw [lminor_last] at h2
  exact det_ne_of_gram _ _ _ h2

theorem chart_zero_eq_alt {E : Type} [Field E] [NumberField E] [IsCMField E] : XZZero E := by
  intro r X x
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  simp only [Data.xZ, h1, Matrix.mul_one]
  rfl

theorem normFactor_pos_alt {E : Type} [Field E] [NumberField E] [IsCMField E] : NfacPos E := by
  intro r X la x hx
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  unfold Data.nfac
  refine Finset.prod_pos (fun τ _ => Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos ?_ _))
  have hne : ∀ j, dmin X.Gm x τ j ≠ 0 := by
    intro j h0
    have := (hx' τ).2 j
    rw [h0] at this
    simp at this
  exact norm_pos_iff.mpr (div_ne_zero (hne _) (hne _))

theorem unitary_domain {E : Type} [Field E] [NumberField E] [IsCMField E] : UnitDom E := by
  intro r X n x hn hx
  rw [mem_dom_iff] at hx ⊢
  intro τ

  have hcol : ∀ a, col (mat (X.lmulC n x) τ) a = Matrix.mulVec (n τ) (col (mat x τ) a) := by
    intro a
    funext k
    simp [col, mat, Data.lmulC, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  have hg : gram τ.1 X.Gm (mat (X.lmulC n x) τ) = gram τ.1 X.Gm (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, hcol, hn τ]
  have hd : ∀ i, dmin X.Gm (X.lmulC n x) τ i = dmin X.Gm x τ i := by
    intro i
    simp only [dmin, hg]
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.lmulC n x) τ i).re := by
    intro i
    rw [hd]
    exact (hx τ).2 i
  exact ⟨det_of_minors X (X.lmulC n x) τ hpos, hpos⟩

theorem orthonormal_domain {E : Type} [Field E] [NumberField E] [IsCMField E] : OrthoDom E := by
  intro r X x hx
  rw [mem_dom_iff]
  intro τ
  have hdm : ∀ i : Fin (r + 1), dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    intro i
    simp only [dmin, lminor, hx τ]
    rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp [psgn, Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
  have hps : ∀ i : ℕ, psgn X.p0 i ≠ 0 := by
    intro i
    unfold psgn
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_)
    unfold sgn
    split_ifs <;> norm_num
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
    intro i
    rw [hdm, Complex.ofReal_re]
    exact mul_self_pos.mpr (hps i)
  exact ⟨det_of_minors X x τ hpos, hpos⟩

theorem opN_smul {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) = ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ, √(∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) =
      ‖t‖ * √(∑ i, ‖Matrix.mulVec A v i‖ ^ 2) := by
    intro v
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  open scoped Pointwise in
  have hset : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = √(∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / √(∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧ s = √(∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / √(∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, by rw [key, mul_div_assoc]⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [key, mul_div_assoc]⟩
  open scoped Pointwise in
  rw [hset, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]

theorem chartNorm_smul {E : Type} [Field E] [NumberField E] [IsCMField E] : ZnSmul E := by
  intro r X t Z
  unfold Data.zN
  have h : ∀ τ, Data.opN (Matrix.of ((t • Z) τ)) = ‖t‖ * Data.opN (Matrix.of (Z τ)) := by
    intro τ
    rw [← opN_smul]
    rfl
  simp only [h]
  rw [Real.mul_iSup_of_nonneg (norm_nonneg t)]

theorem chartNorm_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] : ZnNonneg E := by
  intro r X Z
  unfold Data.zN
  refine Real.iSup_nonneg (fun τ => ?_)
  unfold Data.opN
  refine Real.sSup_nonneg (fun t ht => ?_)
  obtain ⟨v, _, rfl⟩ := ht
  positivity

theorem borel_flag_translate {E : Type} [Field E] [NumberField E] [IsCMField E] : BorFlag E := by
  classical
  intro r X x b hb hxb τ
  rw [mem_dom_iff] at hxb
  have hdet : (mat (rmul x b) τ).det ≠ 0 := (hxb τ).1
  have hdx : (mat x τ).det ≠ 0 := by
    intro h0
    apply hdet
    rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, h0, zero_mul]

  have hcol : ∀ a, col (mat (rmul x b) τ) a = ∑ c, b τ c a • col (mat x τ) c := by
    intro a
    funext k
    simp [col, mat, rmul, Matrix.mul_apply, Finset.sum_apply, mul_comm]
    rfl
  have hli : ∀ y : Matrix (Fin r) (Fin r) ℂ, y.det ≠ 0 →
      LinearIndependent ℂ (fun a : Fin X.p0 => col y (Fin.castLE X.p0_le a)) := by
    intro y hy
    have h1 := Matrix.linearIndependent_cols_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det y).mpr (isUnit_iff_ne_zero.mpr hy))
    exact h1.comp (Fin.castLE X.p0_le) (Fin.castLE_injective _)
  have hle : Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat (rmul x b) τ) (Fin.castLE X.p0_le a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [hcol]
    refine Submodule.sum_mem _ (fun c _ => ?_)
    by_cases hc : (c : ℕ) < X.p0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
    · have ha := a.isLt
      have hz : b τ c (Fin.castLE X.p0_le a) = 0 :=
        (hb τ).2 c (Fin.castLE X.p0_le a) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card (hli _ hdet), finrank_span_eq_card (hli _ hdx)]

end

end PIW.FdPA
end

