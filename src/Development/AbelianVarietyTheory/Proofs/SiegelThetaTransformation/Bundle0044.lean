module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MatRmulUnipMulHeadProj
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NotIsIsoOfDefinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspClass

private theorem hermC_mulVec_mulVec_eq_sum_gram {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    FD.hermC τ G (P *ᵥ w) (P *ᵥ w) = ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [FD.hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem not_isIso_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (h0 : X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hξ0, hne⟩
  have τ0 : E →+* ℂ := Classical.choice inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · exact ⟨_, not_not.mp (mt (X.cmType τ0).mpr h)⟩
  obtain ⟨P, hPdet, hP⟩ := X.signature ⟨τ, hτ⟩
  have hherm : FD.hermC τ X.Gm (fun a => τ (ξ a)) (fun a => τ (ξ a)) = 0 := by
    have h1 := congrArg τ hξ0
    rw [map_zero] at h1
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [FD.herm, FD.hermC, FD.cc, map_sum, map_mul, NumberField.IsCMField.complexEmbedding_complexConj]
  obtain ⟨w, hw⟩ : ∃ w, P *ᵥ w = fun a => τ (ξ a) :=
    ⟨P⁻¹ *ᵥ (fun a => τ (ξ a)), by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hPdet), Matrix.one_mulVec]⟩
  have hsum : ∑ a, ((Complex.normSq (w a) : ℝ) : ℂ) = 0 := by
    rw [← hherm, ← hw, hermC_mulVec_mulVec_eq_sum_gram, hP]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp [Matrix.diagonal_apply_eq, FD.sgn, h0, Complex.mul_conj]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  have hsum' : ∑ a, Complex.normSq (w a) = 0 := by exact_mod_cast hsum
  have hw0 : w = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg (w a))).mp hsum' a
      (Finset.mem_univ a)
    simpa using this
  apply hne
  funext a
  have := congrFun hw a
  rw [hw0, Matrix.mulVec_zero] at this
  exact (map_eq_zero τ).mp this.symm

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → r ≤ n → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk hrn φ hφ P hP Q hQ hΓ
  obtain ⟨-, hlink⟩ := GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn
  obtain ⟨m, a, b, t, hab⟩ := hlink φ hφ
  refine GlobalTheory.ThFr.mem_SS_of_eq_sum_thFr (idx := idx) (hr := hr) (s := Finset.univ) (t := t)
    (a := fun j k i => (a j k i : ℝ)) (b := fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ?_
    (fun _ _ => hP) ?_ hΓ
  · rcases hk with ⟨τ, i, hi, hki⟩ | hq
    · exact Or.inl ⟨by omega, τ, Or.inl ⟨i, hi, hki⟩⟩
    · exact Or.inr (not_isIso_of_definite X (by omega))
  · intro x hx
    exact (hQ x hx).trans (hab P x hx)

end GlobalTheory.Dict.CuspClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchurHeisG
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker


open GlobalTheory.SW.DblZero in
theorem schur_heisG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ A : TF n g → TF n g, (∀ φ, IsSB φ → IsSB (A φ)) → (∀ φ ψ, IsSB φ → IsSB ψ → A (φ + ψ) = A φ + A ψ) → (∀ (a : ℂ) φ, IsSB φ → A (a • φ) = a • A φ) → (∀ (y : Matrix (Fin n) (Fin r) E) φ, IsSB φ → A (heisG X bas y φ) = heisG X bas y (A φ)) → ∃ c : ℂ, ∀ φ, IsSB φ → A φ = c • φ := by
  intro E _ _ _ r X g q0 hr bas idx n hs _ A hA hadd hsmul hcomm

  obtain ⟨c, hc⟩ := exists_eq_mul_ip (κ := Fin n) (ι := Fin g) (fun φ ψ => ip (A φ) ψ)
    (fun φ φ' ψ hφ hφ' hψ => by
      rw [hadd φ φ' hφ hφ', ip_add_left (hA φ hφ) (hA φ' hφ') hψ])
    (fun φ ψ ψ' hφ hψ hψ' => by
      exact ip_add_right (hA φ hφ) hψ hψ')
    (fun a b φ ψ hφ hψ => by
      rw [hsmul a φ hφ, ip_smul (hA φ hφ) hψ])
    (fun a b φ ψ hφ hψ => by
      obtain ⟨y, hy⟩ := exists_heisG (n := n) hs a b
      rw [← hy φ, hcomm y φ hφ, hy (A φ)]
      exact ((heisS_laws _ _ a b (A φ) (hA φ hφ)).2.2.2.2) ψ hψ)
  refine ⟨c, fun φ hφ => ?_⟩

  have hAφ := hA φ hφ
  have hcφ : IsSB (-c • φ) := ((isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1) (-c)
  have hd : IsSB (A φ + -c • φ) := (isSB_algebra_haar_linear _ _ _ (A φ) (-c • φ) hAφ hcφ).1
  have hzero : ip (A φ + -c • φ) (A φ + -c • φ) = 0 := by
    rw [ip_add_left hAφ hcφ hd, hc φ _ hφ hd]
    have h1 : ip (-c • φ) (A φ + -c • φ) = -c * ip φ (A φ + -c • φ) := by
      have := ip_smul hφ hd (-c) 1
      rw [one_smul, map_one, mul_one] at this
      exact this
    rw [h1]
    ring
  by_contra hne
  have hne' : A φ + -c • φ ≠ 0 := by
    intro h0
    apply hne
    have : A φ = -(-c • φ) := eq_neg_of_add_eq_zero_left h0
    rw [this, neg_smul, neg_neg]
  exact ip_self_ne_zero hd hne' hzero

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.ThetaHol

theorem exists_corner {κ ι : Type} [Fintype κ] [Fintype ι] (τ : Matrix ι ι ℂ) (S : ℝ)
    (x : Matrix κ ι ℚ) : ∃ s : κ → ι → Bool, ∀ ζ : κ → ι → ℂ, ‖ζ‖ ≤ S →
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ ≤
      ‖cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) +
        2 * (qv (x k) ⬝ᵥ fun i => (if s k i then -S else S : ℝ) * I)))‖ := by
  refine ⟨fun k i => decide (0 ≤ x k i), fun ζ hζ => ?_⟩
  rw [Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.im_sum, Complex.add_im,
    Complex.mul_im, dotProduct, qv, Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, mul_one,
    Complex.re_ofNat, Complex.im_ofNat, decide_eq_true_eq]
  refine mul_le_mul_of_nonneg_left (neg_le_neg (Finset.sum_le_sum fun k _ => ?_)) Real.pi_pos.le
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le_two
  have h1 : |(ζ k i).im| ≤ S := (Complex.abs_im_le_norm _).trans
    ((norm_le_pi_norm (ζ k) i).trans ((norm_le_pi_norm ζ k).trans hζ))
  have h2 := abs_le.mp h1
  split_ifs with h
  · have : (0 : ℝ) ≤ (x k i : ℝ) := by exact_mod_cast h
    nlinarith
  · have : (x k i : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
    nlinarith

theorem differentiable_thS {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {φ : Matrix κ ι ℚ → ℂ} (hφ : IsSB φ) {τ : Matrix ι ι ℂ} (hτ : τ ∈ Siegel ι) :
    Differentiable ℂ (thS φ τ) := by
  intro ζ₀
  let F : Matrix κ ι ℚ → (κ → ι → ℂ) → ℂ := fun x ζ => φ x *
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  let S : ℝ := ‖ζ₀‖ + 2
  let cor : (κ → ι → Bool) → κ → ι → ℂ := fun s k i => ((if s k i then -S else S : ℝ) : ℂ) * I
  choose s hs using fun x : Matrix κ ι ℚ => exists_corner τ S x
  have hFd : ∀ x, Differentiable ℂ (F x) := by
    intro x
    simp only [F, dotProduct]
    fun_prop
  have hbd : ∀ x, ∀ z : κ → ι → ℂ, ‖z‖ ≤ S → ‖F x z‖ ≤ ‖F x (cor (s x))‖ := by
    intro x z hz
    simp only [F, norm_mul]
    exact mul_le_mul_of_nonneg_left (hs x z hz) (norm_nonneg _)
  have hsum : Summable fun x => ‖F x (cor (s x))‖ := by
    have hfin : Summable fun x => ∑ t : κ → ι → Bool, ‖F x (cor t)‖ :=
      summable_sum fun t _ => SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ (cor t)
    refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hfin
    exact Finset.single_le_sum (f := fun t => ‖F x (cor t)‖) (fun t _ => norm_nonneg _)
      (Finset.mem_univ (s x))
  have hder : ∀ x, ∀ ζ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1),
      ‖fderiv ℂ (F x) ζ‖ ≤ 2 * ‖F x (cor (s x))‖ := by
    intro x ζ hζ
    have h := GlobalTheory.SCV.norm_fderiv_le_of_ball (f := F x) (c := ζ) (r := 1)
      (M := ‖F x (cor (s x))‖) one_pos (hFd x).differentiableOn (fun z hz => hbd x z (by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        rw [Metric.mem_ball, dist_zero_right] at hζ
        have := norm_sub_norm_le z ζ
        simp only [S]
        linarith))
    simpa using h
  have h0 : ζ₀ ∈ Metric.ball (0 : κ → ι → ℂ) (‖ζ₀‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have key := hasFDerivAt_tsum_of_isPreconnected (hsum.mul_left 2) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (fun x ζ _ => (hFd x ζ).hasFDerivAt) hder h0
    (SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ₀).of_norm h0
  exact key.differentiableAt

theorem differentiable_thA {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) {φ : TF n g} (hφ : IsSB φ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Differentiable ℂ (thA X bas idx φ x) := by
  have hτ := UnAct.tauMat_mem idx hs hx
  have hlin : Differentiable ℂ fun z : Fin n → Fin g → ℂ => fun k => hMat X bas idx x *ᵥ z k := by
    refine differentiable_pi.2 fun k => differentiable_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hth := (differentiable_thS hφ hτ).comp hlin
  have hq : Differentiable ℂ fun z : Fin n → Fin g → ℂ => ∑ k, (hMat X bas idx x *ᵥ z k) ⬝ᵥ
      imInv X bas idx x *ᵥ (hMat X bas idx x *ᵥ z k) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  unfold thA
  exact ((hq.const_mul _).cexp.const_mul _).mul hth

end GlobalTheory.SW.ThetaHol

namespace GlobalTheory.SW

theorem theta_holomorphic_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (φ : TF n g), IsSB φ → ∀ P ∈ Harm.rowHighest ℂ c c', DifferentiableOn ℂ (thP X hr bas idx φ P) X.dom ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, thP X hr bas idx φ P (rmul x b) = bchar (wtOf X hr c c' n) b * thP X hr bas idx φ P x) ∧ (∀ γ, IsUn X γ → ∀ x ∈ X.dom, thP X hr bas idx (wG X bas idx γ φ) P (lact γ x) = thP X hr bas idx φ P x) ∧ ∀ x ∈ X.dom, AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn c c' φ hφ P hP
  obtain ⟨m, a, b, t, ht⟩ := (_root_.GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 φ hφ
  have hH := Harm.isHarmonic_of_mem_rowHighest hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (fun x => ∑ j, t j * thFr X hr bas idx n
        (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x) X.dom :=
      DifferentiableOn.fun_sum fun j _ => (differentiableOn_thFr idx hs hr n _ _ hH).const_mul (t j)
    exact hd.congr fun x hx => ht P x hx
  · intro x hx u hu
    have hxu := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hu
    rw [ht P _ hxu, ht P x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [thFr_rmul idx hr _ _ hs hP hx hu]
    ring
  · intro γ hγ x hx
    unfold thP
    rw [(wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hx]
  · intro x hx
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiable (ThetaHol.differentiable_thA idx hs hφ hx) _

end GlobalTheory.SW
end

