module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmul
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacter
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem atkinLehner_conj_int (N l : ℕ) (a b c d : ℤ) (h : (N : ℤ) * a * d - l * b * c = 1) (γ : M2)
    (hγ : ((N * l : ℕ) : ℤ) ∣ γ 1 0) (hdet : γ.det = 1) :
    ∃ γ' : M2, !![(N : ℤ) * a, b; N * l * c, N * d] * γ = γ' * !![(N : ℤ) * a, b; N * l * c, N * d] ∧
    γ'.det = 1 ∧ ((N * l : ℕ) : ℤ) ∣ γ' 1 0 ∧ (N : ℤ) ∣ γ' 1 1 - γ 0 0 := by
  obtain ⟨r, hr⟩ := hγ
  push_cast at hr
  set p := γ 0 0
  set q := γ 0 1
  set s := γ 1 1
  have hdet' : p * s - (N * l * r) * q = 1 := by
    rw [Matrix.det_fin_two] at hdet; rw [hr] at hdet; linarith
  refine ⟨!![(N : ℤ) * a * d * p + N * l * b * d * r - N * l * a * c * q - l * b * c * s,
     -(a * b * p) - l * b * b * r + N * a * a * q + a * b * s;
     N * l * (c * d * p + N * d * d * r - l * c * c * q - c * d * s),
     -(l * b * c * p) - N * l * b * d * r + N * l * a * c * q + N * a * d * s], ?_, ?_, ?_, ?_⟩
  · have hγe : γ = !![p, q; N * l * r, s] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [p, q, s, hr]
    rw [hγe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -(N * a * p + b * N * l * r) * h
    · linear_combination -(N * a * q + b * s) * h
    · linear_combination -(N * l * c * p + N * d * N * l * r) * h
    · linear_combination -(N * l * c * q + N * d * s) * h
  · rw [Matrix.det_fin_two_of]
    linear_combination ((N : ℤ) * a * d - l * b * c) ^ 2 * hdet' + ((N : ℤ) * a * d - l * b * c + 1) * h
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    exact Dvd.intro _ rfl
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact ⟨-(b * d * l * r) + l * a * c * q + a * d * s - a * d * p, by linear_combination p * h⟩

theorem inv_slz_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ),
    N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f →
    Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  intro k N l χ f a b c d h hk hN hf
  set Q : M2 := !![(N : ℤ) * a, b; N * l * c, N * d] with hQ
  have hQdet : 0 < Q.det := by
    have : Q.det = N * (N * a * d - l * b * c) := by rw [hQ, Matrix.det_fin_two_of]; ring
    rw [this, h, mul_one]; exact_mod_cast hN
  have hiff := (slz_props k (slz k Q f) hk).2.2.1 (N * l) (ch χ⁻¹)
  have hiff0 := (slz_props k f hk).2.2.1 (N * l) (ch χ)
  refine hiff.2 fun γ hγ => ?_
  have hγdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hγ' : ((N * l : ℕ) : ℤ) ∣ (γ : M2) 1 0 := by exact_mod_cast hγ
  obtain ⟨g, hg, hgdet, hgdvd, hgcong⟩ := atkinLehner_conj_int N l a b c d h (γ : M2) hγ' hγdet
  let γ₁ : SL(2, ℤ) := ⟨g, hgdet⟩
  have hf1 := hiff0.1 hf γ₁ (by exact_mod_cast hgdvd)
  have hcalc : slz k (γ : M2) (slz k Q f) = slz k Q (slz k (γ₁ : M2) f) := by
    rw [← slz_mul k f Q (γ : M2) hQdet (by rw [hγdet]; exact one_pos), hg,
      slz_mul k f g Q (by rw [hgdet]; exact one_pos) hQdet]
  rw [hcalc, hf1]
  have hchar : ch χ (γ₁ 1 1) = ch χ⁻¹ (γ 1 1) := by
    simp only [ch]
    have e1 : ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
        have : (N : ℤ) ∣ g 1 1 - γ 0 0 := hgcong
        rw [← dvd_neg, neg_sub]; exact this)
    have e2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have hd := hγdet
      rw [Matrix.det_fin_two] at hd
      obtain ⟨r, hr⟩ := hγ'
      have : ((((γ : M2) 0 0 * (γ : M2) 1 1 - (γ : M2) 0 1 * (γ : M2) 1 0 : ℤ)) : ZMod N) = 1 := by
        rw [hd]; simp
      rw [hr] at this
      push_cast at this
      simpa using this
    rw [e1, MulChar.inv_apply_eq_inv']
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, e2, map_one]
  funext τ
  simp only [slz]
  rw [hchar]
  ring

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCusp
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Matrix.SpecialLinearGroup
open scoped Pointwise

theorem norm_petersson_self_eq (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    ‖UpperHalfPlane.petersson (k : ℤ) f f z‖ = ‖f z‖ ^ 2 * z.im ^ k := by
  simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg z.im_pos.le]
  ring

theorem cusp_decay : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (γ : SL(2, ℤ)), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ C δ : ℝ, 0 < δ ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im →
      ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C * Real.exp (-δ * τ.im) := by
  intro k L N ε a γ hk hL hN hcf
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.EisM.cuspForm_of_CF k L N ε a hk hL hN hcf
  obtain ⟨C₀, hC₀⟩ := hcf.2
  haveI : NeZero L := ⟨hL.ne'⟩
  have : ((ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹) • (Gamma1 L : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Gamma1 L : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹
  obtain ⟨δ, hδ, hd⟩ := (CuspFormClass.zero_at_infty (CuspForm.translate f γ)).petersson_exp_decay_left (k : ℤ) _
      (CuspForm.translate f γ)
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.isBigOWith_iff, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (hC₀ UpperHalfPlane.I)
  refine ⟨max D (C₀ * Real.exp (δ * |y|)), δ, hδ, fun τ hτ => ?_⟩
  have key : ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k =
      ‖UpperHalfPlane.petersson (k : ℤ) (CuspForm.translate f γ) (CuspForm.translate f γ) τ‖ := by
    rw [show ((CuspForm.translate f γ : CuspForm _ _) : ℍ → ℂ) = (⇑f) ∣[(k : ℤ)] γ from rfl,
      UpperHalfPlane.petersson_slash_SL, norm_petersson_self_eq, hf]
  rw [key]
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · rw [← key]
    have h3 : 1 ≤ Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [le_abs_self y]
    calc ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C₀ := hC₀ _
      _ ≤ C₀ * (Real.exp (δ * |y|) * Real.exp (-δ * τ.im)) := le_mul_of_one_le_right hC₀0 h3
      _ = C₀ * Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormLseriesExtendsEntire
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem div_le_half_sq_add {t x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    t / x ≤ (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 := by
  have key : (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 - t / x = (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by
    field_simp
    ring
  have : 0 ≤ (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by positivity
  linarith

theorem lseriesSummable_of_sq (a : ℕ → ℂ) (k : ℕ)
    (hsq : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s))
    (s : ℂ) (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable a s := by
  set σ := s.re with hσ
  set δ : ℝ := σ - ((k : ℝ) + 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := hsq δ hδ0
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + δ)) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · have : 0 ≤ ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := by positivity
    have : 0 ≤ (n : ℝ) ^ (-(1 + δ)) := by positivity
    linarith
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have e : (n : ℝ) ^ (-(1 + δ)) = (n : ℝ) ^ ((k : ℝ) + δ) * ((n : ℝ) ^ σ)⁻¹ * ((n : ℝ) ^ σ)⁻¹ := by
      rw [show -(1 + δ) = ((k : ℝ) + δ) + -σ + -σ by rw [hδ]; ring, Real.rpow_add hn', Real.rpow_add hn',
        Real.rpow_neg hn'.le]
    rw [e]
    exact div_le_half_sq_add (Real.rpow_pos_of_pos hn' σ) (Real.rpow_pos_of_pos hn' _)

theorem lseries_cusp_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  intro k L N ε g hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.EisM.cuspForm_of_CF k L N ε g hk hL hNL hcf
  have hcoef : ∀ n, (qExpansion 1 ⇑f).coeff n = g n := fun n => by
    have h := _root_.GlobalTheory.EisM.coef_qs g hcf.1.1 n
    rw [coef, ← hf] at h
    exact h
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hsq := (_root_.GlobalTheory.rankin_mean_square k L (ch ε) g hk hcf).2.2.1
  have hsum : ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s := lseriesSummable_of_sq g k hsq
  have habs : LSeries.abscissaOfAbsConv g ≤ (((((k : ℝ) + 1) / 2 : ℝ)) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hsum y (by simpa using hy)
  have hdiff : Differentiable ℂ (ModularForm.L hk0 f) := CuspForm.differentiable_L hk0 f

  have hagree : ∀ s : ℂ, (k : ℝ) / 2 + 1 < s.re → LSeries g s = ModularForm.L hk0 f s := by
    intro s hs
    have h := CuspForm.hasSum_L hk0 f (s := s) (by rw [Int.cast_natCast]; exact hs)
    simp only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    have hs0 : s ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hs; have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    rw [LSeries, ← h.tsum_eq]
    congr 1
    funext n
    rw [LSeries.term_of_ne_zero' hs0, hcoef]
  refine ⟨ModularForm.L hk0 f, hdiff, fun s hs => ⟨hsum s hs, ?_⟩⟩
  set U : Set ℂ := {c : ℂ | ((k : ℝ) + 1) / 2 < c.re} with hU
  have hLU : AnalyticOnNhd ℂ (LSeries g) U := (LSeries_analyticOnNhd g).mono fun c hc => by
    simp only [Set.mem_setOf_eq, hU] at hc ⊢
    exact lt_of_le_of_lt habs (by exact_mod_cast hc)
  have hΛU : AnalyticOnNhd ℂ (ModularForm.L hk0 f) U := fun z _ => hdiff.analyticAt z
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  set z₀ : ℂ := (((k : ℝ) + 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (k : ℝ) + 2 := by rw [hz₀, Complex.ofReal_re]
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hz₀U : z₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hz₀re]; linarith
  have hev : LSeries g =ᶠ[𝓝 z₀] ModularForm.L hk0 f := by
    have hopen : IsOpen {c : ℂ | (k : ℝ) / 2 + 1 < c.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp only [Set.mem_setOf_eq, hz₀re]; linarith)] with c hc
    exact hagree c hc
  exact hLU.eqOn_of_preconnected_of_eventuallyEq hΛU hconn hz₀U hev hs

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOutStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out : ∀ (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) = LSeries (fun n => φ n) (j + 2 * s) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  first | exact @GlobalTheory.EisM.lattice_sum_gcd_out | exact GlobalTheory.EisM.lattice_sum_gcd_out | (intros; apply GlobalTheory.EisM.lattice_sum_gcd_out <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinProductSeriesEqDepletedEisensteinProdu
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem zm_eq_mul_dep_eis : ∀ (k l j : ℕ) (u w A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zm k l u w (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1)) (dep l (eis (j + 1) c' A' w)) := by
  intro k l j u w A A' c c' hjk
  funext n
  unfold Zm mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1) p.1 * dep l (eis (j + 1) c' A' w) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    have hsw : ∑ q ∈ p.2.divisorsAntidiagonal, A' (q.1 : ℤ) * ((q.1 : ℂ)) ^ (j + 1 - 1) * w (q.2 : ℤ)
        = ∑ y ∈ p.2.divisorsAntidiagonal, A' (y.2 : ℤ) * ((y.2 : ℂ)) ^ (j + 1 - 1) * w (y.1 : ℤ) := by
      refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun q => ?_) (fun q _ => rfl)
      simp only [Nat.mem_divisorsAntidiagonal, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]
    rw [hsw, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    have hx0 : (x.1 : ℂ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.1 ≠ 0 := fun e => p1 (by rw [← this, e, zero_mul])
      exact_mod_cast this
    have hk : k - 2 = (k - 1 - j - 1) + j := by omega
    have hj : j + 1 - 1 = j := by omega
    rw [hk, hj, pow_add, div_pow]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinTameWeightSecondEqCharacterSum
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eisensteinTameWeightSecond_eq_character_sum :
    ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ,
      tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  intro N s hN B
  haveI : NeZero N := ⟨hN.ne'⟩
  have hφ : ((N.totient : ℂ)) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have h1 := DirichletCharacter.sum_characters_eq ℂ (B : ZMod N)
  have h2 := DirichletCharacter.sum_characters_eq ℂ (-(B : ZMod N))
  have h3 : ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N)
      = ∑ ν : DirichletCharacter ℂ N, ν (-(B : ZMod N)) := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← map_mul, neg_one_mul]
  have h4 : (-(B : ZMod N) = 1) ↔ ((B : ZMod N) = -1) := neg_eq_iff_eq_neg
  have hsum : ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B
      = ∑ ν : DirichletCharacter ℂ N, ν (B : ZMod N)
        - s * ∑ ν : DirichletCharacter ℂ N, ν (-1) * ν (B : ZMod N) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp only [ch]
    ring
  rw [hsum, h3, h1, h2]
  simp only [tw2, h4]
  field_simp
  split_ifs <;> ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTopologicalGeneratorTauTowerStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topological_generator_tau_tower : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ T : Tower p Ω, ∃ τ ∈ Ggeo p Ω, ∀ n, τ (T.qq n) = T.ζ n * T.qq n := by
  first | exact @GlobalTheory.K5.TauGen.main | exact GlobalTheory.K5.TauGen.main | (intros; apply GlobalTheory.K5.TauGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FormsOfCharactersIndependent
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM.Indep

theorem qs_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℂ) (ha : ∀ i, PolyB (a i)) :
    qs (∑ i ∈ s, a i) = ∑ i ∈ s, qs (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.EisM.Lin.qs_zero
  | insert i s hi ih =>
    have hp : PolyB (∑ j ∈ s, a j) := by
      clear ih hi
      induction s using Finset.induction_on with
      | empty => simpa using GlobalTheory.EisM.Lin.polyB_zero
      | insert j t hj ih2 =>
        rw [Finset.sum_insert hj]; exact GlobalTheory.EisM.Lin.polyB_add _ _ (ha j) ih2
    rw [Finset.sum_insert hi, Finset.sum_insert hi, GlobalTheory.EisM.Lin.qs_add _ _ (ha i) hp, ih]

theorem exists_gamma (L N : ℕ) (hL : 0 < L) (hNL : N ∣ L) (u : (ZMod N)ˣ) :
    ∃ γ : SL(2, ℤ), γ 1 0 = (L : ℤ) ∧ ((γ 1 1 : ℤ) : ZMod N) = u := by
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hNL u
  have hc : Nat.Coprime (v : ZMod L).val L := ZMod.val_coe_unit_coprime v
  have hc' : IsCoprime (((v : ZMod L).val : ℕ) : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨x, y, hxy⟩ := hc'
  refine ⟨⟨!![x, -y; (L : ℤ), (((v : ZMod L).val : ℕ) : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hxy
  · simp
  · simp only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val, Int.cast_natCast]

theorem forms_of_characters_independent : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L →
    (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  intro k L N a hL hNL hmf hsum ε₀
  have hN : N ≠ 0 := by rintro rfl; exact hL.ne' (Nat.eq_zero_of_zero_dvd hNL)
  haveI : NeZero N := ⟨hN⟩
  set f : DirichletCharacter ℂ N → ℍ → ℂ := fun ε => qs (a ε) with hf
  have hfs : ∑ ε, f ε = 0 := by
    rw [hf, ← qs_finset_sum _ _ (fun ε => (hmf ε).1), hsum]; exact GlobalTheory.EisM.Lin.qs_zero

  have key : ∀ (b : ZMod N) (τ : ℍ), ∑ ε, ε b * f ε τ = 0 := by
    intro b τ
    by_cases hb : IsUnit b
    · obtain ⟨u, rfl⟩ := hb
      obtain ⟨γ, h10, h11⟩ := exists_gamma L N hL hNL u
      have hdiv : (L : ℤ) ∣ γ 1 0 := by rw [h10]
      have hj : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) ≠ 0 := by
        apply pow_ne_zero
        intro h0
        have him := congrArg Complex.im h0
        simp only [h10, Int.cast_natCast, Complex.add_im, Complex.mul_im, Complex.natCast_re,
          Complex.natCast_im, Complex.intCast_im, zero_mul, add_zero, Complex.zero_im] at him
        have : (0 : ℝ) < (L : ℝ) * (τ : ℂ).im := mul_pos (by exact_mod_cast hL) τ.im_pos
        linarith
      have e : ∀ ε, f ε (γ • τ) = ε (u : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * f ε τ := by
        intro ε
        rw [hf]; dsimp only
        rw [(hmf ε).2 γ hdiv τ, ch, h11]
      have h0 : ∑ ε, f ε (γ • τ) = 0 := by
        have := congrFun hfs (γ • τ); simpa [Finset.sum_apply] using this
      simp only [e] at h0
      have h1 : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * ∑ ε, ε (u : ZMod N) * f ε τ = 0 := by
        rw [Finset.mul_sum, ← h0]; exact Finset.sum_congr rfl (fun ε _ => by ring)
      exact (mul_eq_zero.mp h1).resolve_left hj
    · exact Finset.sum_eq_zero (fun ε _ => by rw [MulChar.map_nonunit ε hb, zero_mul])
  funext n
  have hq : f ε₀ = 0 := by
    funext τ
    have hT : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = 0 :=
      Finset.sum_eq_zero (fun b _ => by rw [key b τ, mul_zero])
    have hT' : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = ∑ ε, f ε τ * ∑ b : ZMod N, (ε₀⁻¹ * ε) b := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [MulChar.coeToFun_mul, Pi.mul_apply]; ring
    rw [hT'] at hT
    rw [Finset.sum_eq_single ε₀] at hT
    · rw [inv_mul_cancel, MulChar.sum_one_eq_card_units] at hT
      have hc : ((Fintype.card (ZMod N)ˣ : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simpa [hc, hN] using hT
    · intro ε _ hne
      rw [MulChar.sum_eq_zero_of_ne_one, mul_zero]
      intro h1; apply hne
      have := congrArg (ε₀ * ·) h1
      simpa using this
    · intro h; exact absurd (Finset.mem_univ _) h
  have := qs_injective (a ε₀) 0 (hmf ε₀).1 GlobalTheory.EisM.Lin.polyB_zero (by rw [GlobalTheory.EisM.Lin.qs_zero]; exact hq)
  simpa using congrFun this n

end GlobalTheory.EisM.Indep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmulStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCocycle_value_expansion_eq_logDeriv_smul : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (cw : ℤ → Ω) (w w' r : Ω), Ev ψ cw w w' → w ≠ 0 → IsInt (p := p) w⁻¹ → r ^ (p ^ n) = w →
  ∀ a lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) r a → IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * (w' / w) * ((lq g).val : Ω)) := by
  first | exact @GlobalTheory.K5.GeoKummer.geo_cob | exact GlobalTheory.K5.GeoKummer.geo_cob | (intros; apply GlobalTheory.K5.GeoKummer.geo_cob <;> assumption)
end

