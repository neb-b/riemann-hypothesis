module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0186
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0175

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cccoef_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {ε ε' : ℝ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : JC.CCCoefM Bs A mm ε' F) (he : ε ≤ ε') : JC.CCCoefM Bs A mm ε F :=
  ⟨h.1, h.2.1, fun g hg hne => he.trans (h.2.2 g hg hne)⟩

theorem cut_eq {k r : ℕ} (cut : ℕ → B.Mat k r → ℂ)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) (g : B.Mat k r) :
    cut n g = 1 - JCx2.pdPsi ((n : ℝ) + 1) g := by
  rw [hcut]
  simp [JCx2.pdPsi, JCx2.pdPhi, JCx2.pdChi, JCx2.pdSq]

theorem belowTop : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ Cc : ℝ, Cl ≤ Cc →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ i, i ≤ P.r → ∀ w : List C.Letter, w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b)) := by
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceQ
  refine ⟨Cs + 1, by positivity, ?_⟩
  intro Cc hCc Wp Wq _ _ _ _ _ _ P p f χ ε A N cut hχ hε hf hfA hA hcut i hi w hw a b
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 : (Cs + 1) * ((P.r : ℝ) + 1) ^ 4 * X ≤ A :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) (by positivity)) hA
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  set M := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hfA M
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) M f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) M
  have hψ : ∀ n : ℕ, B.CCle (A - 1) M (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) M (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact BetaSesquilinearity.CkOn_add hf (BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hsub : ∀ n, (fun g => f g - hn n g) = fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g := by
    intro n; funext g
    rw [hneq n]; simp
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  simp only [KB.Pl.RR, hFn]
  unfold D.RRplace
  by_cases hab : D.IsLocPt a i ∧ D.IsLocPt b i
  swap
  · simp only [dif_neg hab]; exact tendsto_const_nhds
  simp only [dif_pos hab, dif_pos hi]
  have hca : P.r - i = P.r - D.ptSize a := by simp [hab.1.2]
  have hcb : P.r - i = P.r - D.ptSize b := by simp [hab.2.2]
  have hQa := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw a hca hab.1 e
  have hQb := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw b hcb hab.2 e
  choose εa Ka hεa hKa hQ1a hQ2a using hQa
  choose εb Kb hεb hKb hQ1b hQ2b using hQb
  set S : ℝ := ∑ e, (εa e)⁻¹ + ∑ e, (εb e)⁻¹ with hS
  have hSa : ∀ e, (εa e)⁻¹ ≤ S := by
    intro e
    have h1 : (εa e)⁻¹ ≤ ∑ e, (εa e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εa e)⁻¹) (fun e _ => (inv_pos.2 (hεa e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εb e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεb e)).le
    linarith
  have hSb : ∀ e, (εb e)⁻¹ ≤ S := by
    intro e
    have h1 : (εb e)⁻¹ ≤ ∑ e, (εb e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εb e)⁻¹) (fun e _ => (inv_pos.2 (hεb e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εa e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεa e)).le
    linarith
  have hS0 : 0 < S := lt_of_lt_of_le (inv_pos.2 (hεa Wd.e1)) (hSa Wd.e1)
  have hε₀a : ∀ e, S⁻¹ ≤ εa e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεa e)) (hSa e); rwa [inv_inv] at this
  have hε₀b : ∀ e, S⁻¹ ≤ εb e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεb e)) (hSb e); rwa [inv_inv] at this
  set KK : ℝ := ∑ e, Ka e + ∑ e, Kb e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := by
    intro e
    have h1 : Ka e ≤ ∑ e, Ka e := Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Kb e := Finset.sum_nonneg fun e _ => hKb e
    linarith
  have hKb' : ∀ e, Kb e ≤ KK := by
    intro e
    have h1 : Kb e ≤ ∑ e, Kb e := Finset.single_le_sum (f := Kb) (fun e _ => hKb e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Ka e := Finset.sum_nonneg fun e _ => hKa e
    linarith
  have hKK0 : 0 ≤ KK := le_trans (hKa Wd.e1) (hKa' Wd.e1)
  have hB1 : bf ≤ bf + Kp * bf := by nlinarith

  have main : ∀ (q : C.LPt) (hcq : P.r - i = P.r - D.ptSize q) (εq Kq : Wd.Ix (Fin w.length) → ℝ),
      (∀ e, S⁻¹ ≤ εq e) → (∀ e, 0 ≤ Kq e) → (∀ e, Kq e ≤ KK) →
      (∀ e (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle (A - 1) M h c →
        JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) (εq e) (xs p.T χ ε i hi w q hcq h e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq h e) (Kq e * c)) →
      (∀ e (h₁ h₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h₁ →
        B.CkOn ⊤ (B.GV P.k P.r) h₂ → B.CCle (A - 1) M h₁ c₁ → B.CCle (A - 1) M h₂ c₂ →
        ∀ γ ∈ B.GV P.k (P.r - i), xs p.T χ ε i hi w q hcq h₁ e γ - xs p.T χ ε i hi w q hcq h₂ e γ =
          xs p.T χ ε i hi w q hcq (fun g => h₁ g - h₂ g) e γ) →
      (∀ e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq f e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq (hn n) e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq (hn n) e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N)
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) (KK * (Kp * bf / ((n : ℝ) + 1)))) := by
    intro q hcq εq Kq hεq hKq hKq' hQ1 hQ2
    refine ⟨fun e => ?_, fun n e => ?_, fun n e => ?_⟩
    · obtain ⟨h1, h2⟩ := hQ1 e f bf hf hbf'
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul (hKq' e) hB1 hbf0 hKK0)⟩
    · obtain ⟨h1, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))⟩
    · obtain ⟨h1, h2⟩ := hQ1 e _ _ (hψs n) (hψ n)
      have hd : ∀ γ ∈ B.GV P.k (P.r - i), (fun γ => (-1 : ℂ) • xs p.T χ ε i hi w q hcq
          (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ) γ =
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) γ := by
        intro γ hγ
        have := hQ2 e f (hn n) bf _ hf (hns n) hbf' (hnC n) γ hγ
        rw [hsub n] at this
        simp only [Pi.sub_apply, ← this]
        simp
      have hC2 := Formalism.FourierDecayAlt.P.Ux1.cc_congr hd (BetaSesquilinearity.CCle_smul (-1) h2)
      simp only [norm_neg, norm_one, one_mul] at hC2
      have hC3 := JCx2.pd_ccle_mono_c hC2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))
      refine ⟨⟨hC3.1, ⟨_, hC3⟩, fun γ hγ hne => ?_⟩, hC3⟩
      rw [← hd γ hγ] at hne
      have hne' : xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ ≠ 0 := by
        intro h0; apply hne; simp [h0]
      exact (hεq e).trans (h1.2.2 γ hγ hne')
  obtain ⟨ma1, ma2, ma3⟩ := main a hca εa Ka hε₀a hKa hKa' hQ1a hQ2a
  obtain ⟨mb1, mb2, mb3⟩ := main b hcb εb Kb hε₀b hKb hKb' hQ1b hQ2b
  have hdn : Tendsto (fun n : ℕ => KK * (Kp * bf / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr
      (fun n => by simp)
    have := (h1.const_mul (Kp * bf)).const_mul KK
    simpa [div_eq_mul_inv, mul_assoc] using this
  exact formLev_limit P p.T _ ⟨i, by omega⟩ w N hw S⁻¹ (inv_pos.2 hS0)
    (xs p.T χ ε i hi w a hca f) (xs p.T χ ε i hi w b hcb f)
    (fun n => xs p.T χ ε i hi w a hca (hn n)) (fun n => xs p.T χ ε i hi w b hcb (hn n))
    (KK * (bf + Kp * bf)) (fun n => KK * (Kp * bf / ((n : ℝ) + 1))) hdn ma1 mb1 ma2 mb2 ma3 mb3

theorem cutCpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε : ℝ) (cut : ℕ → B.Mat P.k P.r → ℂ)
    (hχ : C6.IsCut0 χ) (hε : 0 < ε) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) :
    KB.CptCoef Bs fun g => cut n g • D.cutF Bs χ f ε g := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n) := by
    have e : cut n = fun g => 1 - JCx2.pdPsi ((n : ℝ) + 1) g := funext fun g => cut_eq cut hcut n g
    rw [e]
    exact contDiff_const.sub (JCx2.pd_psi_cd _)
  refine ⟨JCx2.pd_smooth_smul hcs (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε), ⟨2 * ((n : ℝ) + 1), ?_⟩, ?_⟩
  · intro g _ hne
    have hc : cut n g ≠ 0 := by intro h0; apply hne; simp [h0]
    rw [hcut] at hc
    have hpos : 0 < (4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3 := by
      by_contra hle
      push_neg at hle
      apply hc
      rw [Real.smoothTransition.zero_of_nonpos hle]
      simp
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsum : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) =
        ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have hlt : ∑ i, ∑ j, Complex.normSq (g i j) < 4 * ((n : ℝ) + 1) ^ 2 := by
      rw [hsum] at hpos
      have h1 : ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) < 4 := by linarith
      have h2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) =
          ∑ i, ∑ j, Complex.normSq (g i j) := by
        field_simp
      have h3 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) < ((n : ℝ) + 1) ^ 2 * 4 :=
        mul_lt_mul_of_pos_left h1 (by positivity)
      rw [h2] at h3
      linarith
    unfold B.gN
    rw [show (2 * ((n : ℝ) + 1)) = Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · obtain ⟨δ, hδ, hδ0⟩ := hχ.2.1
    refine ⟨δ * ε, by positivity, fun g _ hne => ?_⟩
    have hc : χ (Gf P.k P.r Bs.z Bs.z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [D.cutF, h0]
    have h1 : δ ≤ Gf P.k P.r Bs.z Bs.z' g / ε := by
      by_contra hlt; push_neg at hlt; exact hc (hδ0 _ hlt)
    rw [le_div_iff₀ hε] at h1
    linarith

end Formalism.FourierDecayAlt.P.PBE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vfw

variable {d : ℕ}

def vfD (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  fun x => fderiv ℝ u x (V x)

def vfW : List ((Fin d → ℝ) → (Fin d → ℝ)) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | V :: Vs, u => vfD V (vfW Vs u)

abbrev WOp (d : ℕ) := List (ℂ × List ((Fin d → ℝ) → (Fin d → ℝ)))

def WOp.app (P : WOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  (P.map fun t => t.1 * vfW t.2 u x).sum

def WOp.symb (P : WOp d) (m : ℕ) (x ξ : Fin d → ℝ) : ℂ :=
  (P.map fun t => if t.2.length = m then t.1 * (t.2.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod else 0).sum

end vfw

def VOpToSOp : Prop :=
  ∀ (d m : ℕ) (P : WOp d) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = m ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (m : WithTop ℕ∞) u O → ∀ x ∈ O, S.app u x = WOp.app P u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb P m x ξ

def IsChart (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)) : Prop :=
  IsOpen O ∧ IsOpen U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def VR {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (κ x * X)

def VL {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (X * κ x)

def ChartSysW : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → WOp d) (m : ι → ℕ),
      (∀ j, m j ≤ 2 * r + k + 1) ∧ (∀ j, ∀ t ∈ P j, t.2.length ≤ m j ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, WOp.app (P j) (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, WOp.symb (P j) (m j) x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

theorem chartEqs_of (hA : ChartSysW) (hB : VOpToSOp) : ChartEqs := by
  intro k r z z' d O U κ Φ u hk hz hz' hT hT' hO hU hκ hΦ hκO hΦU hOm hG
  obtain ⟨ι, hι, P, m, hm, hP, huc, hPu, hsym⟩ :=
    hA k r z z' d O U κ Φ u hk hz hz' hT hT' ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ hOm hG
  have hS : ∀ j, ∃ S : SOp d, S.ord = m j ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ v : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((m j : ℕ) : WithTop ℕ∞) v O → ∀ x ∈ O,
        S.app v x = WOp.app (P j) v x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb (P j) (m j) x ξ :=
    fun j => hB d (m j) (P j) O hO (hP j)
  choose S hSo hSc hSa hSs using hS
  refine ⟨ι, hι, S, fun j => hSc j, fun j => by rw [hSo j]; exact hm j, huc, ?_, ?_⟩
  · intro j x hx
    rw [hSa j _ (huc.of_le (by exact_mod_cast hm j)) x hx]
    exact hPu j x hx
  · intro x hx ξ hξ hall
    exact hsym x hx ξ hξ (fun j => by rw [← hSs j x hx ξ]; exact hall j)

def ChartCov : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ∃ Ξ₀ : B.Mat k r, B.inLie k r Ξ₀ ∧ (ξ ≠ 0 → Ξ₀ ≠ 0) ∧
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re

def RwChart : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
    (∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O ∧ ContDiffOn ℝ ∞ (VL κ Φ X) O) ∧
    ∀ Xs : List (B.Mat k r), (∀ X ∈ Xs, B.inLie k r X) → Xs.length ≤ 2 * r + k + 1 → ∀ x ∈ O,
      B.Rw Xs u (κ x) = vfW (Xs.map (VR κ Φ)) (fun y => u (κ y)) x ∧
      Xs.foldr Q.LdV u (κ x) = vfW (Xs.map (VL κ Φ)) (fun y => u (κ y)) x

def LieNFin : Prop :=
  ∀ (k r : ℕ), ∃ (q : ℕ) (Xs : Fin q → B.Mat k r), (∀ i, Xs i ∈ JfS.lieOf (Nset k r)) ∧
    ∀ X ∈ JfS.lieOf (Nset k r), B.inLie k r X ∧ ∃ a : Fin q → ℝ, X = ∑ i, ((a i : ℝ) : ℂ) • Xs i

def CapWords : Prop :=
  ∀ (k r j : ℕ), 1 ≤ j → j ≤ 2 * r + k + 1 →
    ∃ (Ys : Fin (2 * r + k + 2) → ℝ) (lam : Fin (2 * r + k + 2) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.CV k r (Ys i : ℂ) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * Ξ.charpoly.coeff (2 * r + k + 1 - j)

def cmp {k r : ℕ} (Ξ : B.Mat k r) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => Matrix.trace (Ξ * Q.unitB (Hpk k r) Bs a b)

def CapRWords : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z'] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capR k r Bs (ws i) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CapLWords : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capLft k r Bs (ws i) f g = (L.map fun t => t.1 • t.2.foldr Q.LdV f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CmpZero : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    Q.IsFrameOf k r [z] Bs → ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
    (∀ j, 1 ≤ j → j ≤ k → (cmp Ξ Bs).charpoly.coeff (k - j) = 0) →
    ∀ X ∈ JfS.lieOf (UWset k r z), (Matrix.trace (Ξ * X)).re = 0

def FrameEx : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs

def ChartSysWOfParts : Prop :=
  ChartCov → RwChart → LieNFin → CapWords → CapRWords → CapLWords → CmpZero → FrameEx → ChartSysW

theorem chartEqs_of_parts (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hB : VOpToSOp) : ChartEqs :=
  chartEqs_of (hJ h1 h2 h3 h4 h5 h6 h7 h8) hB

def SOpField : Prop :=
  ∀ (d : ℕ) (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) → ContDiffOn ℝ ∞ V O →
    ∃ S' : SOp d, S'.ord = S.ord + 1 ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((S.ord + 1 : ℕ) : WithTop ℕ∞) u O → ∀ x ∈ O,
        S'.app u x = vfD V (S.app u) x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S'.symb x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) * S.symb x ξ

def SOpLift : Prop :=
  ∀ (d : ℕ) (S : SOp d) (m' : ℕ) (O : Set (Fin d → ℝ)), S.ord ≤ m' → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    ∃ S' : SOp d, S'.ord = m' ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧ (∀ u x, S'.app u x = S.app u x) ∧
      ∀ x ξ, S'.symb x ξ = if S.ord = m' then S.symb x ξ else 0

def SOpLin : Prop :=
  ∀ (d : ℕ) (S T : SOp d) (c : ℂ) (O : Set (Fin d → ℝ)), S.ord = T.ord → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    (∀ i w, ContDiffOn ℝ ∞ (T.a i w) O) →
    ∃ R : SOp d, R.ord = S.ord ∧ (∀ i w, ContDiffOn ℝ ∞ (R.a i w) O) ∧
      (∀ u x, R.app u x = c * S.app u x + T.app u x) ∧ ∀ x ξ, R.symb x ξ = c * S.symb x ξ + T.symb x ξ

def VOpToSOpOfSteps : Prop := SOpField → SOpLift → SOpLin → VOpToSOp

theorem chartEqs_of_all (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField)
    (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_parts hJ h1 h2 h3 h4 h5 h6 h7 h8 (hS s1 s2 s3)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERAsm
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem energyReal_of_capAdj (hA : CapAdj) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_leaves hA capacity_theta_facts coefficient_vector_smoothness coefficient_vector_in_class coefficient_vector_support coefficient_vector_congr coefficient_vector_commutation
    beta_form_congr_holds

theorem energyReal_of_capAdjInt (hI : CapAdjInt) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_capAdj (capAdj_of_int hI)

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEllRegW
section
namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem elliptic_regularity_weighted : EllRegW := elliptic_regularity_transfer_holds ZetaZeros.D.EllReg.elliptic_regularity_of_parts

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecFinal
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_section_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SA.SASection :=
  Formalism.FourierDecayAlt.P.CutMP.JA.SA.sASection_of_parts Formalism.FourierDecayAlt.P.CutMP.JA.SA.radial_section_holds
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

