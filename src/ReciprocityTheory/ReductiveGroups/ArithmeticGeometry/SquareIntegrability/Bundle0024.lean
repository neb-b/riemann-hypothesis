module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaNA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanBn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModePointwiseBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusD
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex MeasureTheory

noncomputable section

theorem ct_expo_vec {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (w ua y : V)
    {q M1 r : ℝ} (hq : 0 < q) (hw : ‖w‖ ≤ r)
    (hc6 : |2 * inner ℝ (q • ua) y| ≤ M1 * ‖y‖ ^ 2) :
    Real.pi * q * ‖ua‖ ^ 2 - Real.pi * q * ‖w - (ua + y)‖ ^ 2 ≤
      2 * Real.pi * r * (q * ‖ua‖ + q * ‖y‖) - Real.pi * (q - M1) * ‖y‖ ^ 2 := by
  have e1 : ‖w - (ua + y)‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w ua - 2 * inner ℝ w y + ‖ua‖ ^ 2 +
      2 * inner ℝ ua y + ‖y‖ ^ 2 := by
    rw [@norm_sub_sq_real, @norm_add_sq_real, inner_add_right]
    ring
  have hua := norm_nonneg ua
  have hy := norm_nonneg y
  have hpq : 0 ≤ Real.pi * q := by positivity
  have t1 : Real.pi * q * inner ℝ w ua ≤ Real.pi * q * (r * ‖ua‖) :=
    mul_le_mul_of_nonneg_left ((real_inner_le_norm w ua).trans (mul_le_mul_of_nonneg_right hw hua)) hpq
  have t2 : Real.pi * q * inner ℝ w y ≤ Real.pi * q * (r * ‖y‖) :=
    mul_le_mul_of_nonneg_left ((real_inner_le_norm w y).trans (mul_le_mul_of_nonneg_right hw hy)) hpq
  have h3 : -(2 * inner ℝ (q • ua) y) ≤ M1 * ‖y‖ ^ 2 := (neg_le_abs _).trans hc6
  rw [real_inner_smul_left] at h3
  have t3 : Real.pi * (-(2 * (q * inner ℝ ua y))) ≤ Real.pi * (M1 * ‖y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
  have t4 : 0 ≤ Real.pi * q * ‖w‖ ^ 2 := by positivity
  rw [e1]
  nlinarith [t1, t2, t3, t4]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem ct_cabPoly_zero {ι : Type} [Fintype ι] : cabPoly (0 : EuclideanSpace ℂ ι) 0 = 1 := by
  simp [cabPoly]

theorem ct_beta (hA : PropAStatement) (hS : GSupStatement) (hI : IsSplit P I) (hP : Ext.PackingCount)
    (w : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) (c : ℕ) (hc : c ≤ DF) :
    ∃ βt ∈ (ctY (Col.YB hI hP P.q) w).Sec P.q,
      βt 0 = 1 ∧ (∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j βt 0 = 0) ∧
      (ctY (Col.YB hI hP P.q) w).l2 P.q βt ≤ 6 ∧
      ∀ t, (ctY (Col.YB hI hP P.q) w).ptN2 P.q βt t ≤ 12 * (5.12 : ℝ) ^ Col.gB (IR I) := by
  classical
  have hq2 : (2 : ℝ) ≤ P.q := cab_q_ge P
  have hq2n : 2 ≤ P.q := by exact_mod_cast hq2
  have hR0sq := P.hR0
  have hR0ne : P.R0 ≠ 0 := by intro h; rw [h] at hR0sq; norm_num at hR0sq
  have hR0pos : 0 < |P.R0| := abs_pos.mpr hR0ne
  have hlat : ∀ γ ∈ lat (ctY (Col.YB hI hP P.q) w).b, γ ≠ 0 →
      |P.R0| ≤ Real.sqrt (P.q * Real.pi) * ‖γ‖ := cab_YB_abs hI hP P.q
  have hGle : Col.gB (IR I) ≤ X.gA := cab_gB_le (IR I)
  have hGle' : (Col.gB (IR I) : ℝ) ≤ X.gA := by exact_mod_cast hGle
  have hcD : (c : ℝ) ≤ DF := by exact_mod_cast hc
  have h90 : 90 * ((Fintype.card (Fin (Col.gB (IR I))) : ℝ) + c) ≤ |P.R0| ^ 2 := by
    rw [sq_abs, Fintype.card_fin]; nlinarith [hR0sq.2]
  obtain ⟨β, hβ, hjet, hl2⟩ := hA (Fin (Col.gB (IR I))) (ctY (Col.YB hI hP P.q) w) P.q c |P.R0| P.hq
    (ctY_coc _ _ _ (Col.YB_coc hI hP P.q)) hR0pos hlat
    (by rw [sq_abs]; exact hR0sq.1) h90 (cabPoly 0 0) (by rw [ct_cabPoly_zero]; simp)
  rw [ct_cabPoly_zero] at hjet hl2
  have hJ := cab_J_le (0 : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) (by simp) 0 P.q P.hq
  rw [ct_cabPoly_zero, Fintype.card_fin] at hJ
  have hl2' : (ctY (Col.YB hI hP P.q) w).l2 P.q β ≤
      6 * ((Nat.factorial 0 : ℕ) * (2 / (P.q * Real.pi)) ^ 0 * (2 / P.q) ^ Fintype.card (Fin (Col.gB (IR I)))) := by
    rw [Fintype.card_fin]; simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul] at hJ ⊢
    linarith
  have h90' : 90 * (Fintype.card (Fin (Col.gB (IR I))) : ℝ) ≤ |P.R0| ^ 2 := by
    have : (0 : ℝ) ≤ 90 * c := by positivity
    linarith
  have hβc : ContDiff ℂ (⊤ : ℕ∞) β := (cab_contDiff_top hβ.1).of_le (by exact_mod_cast le_top)
  obtain ⟨hb0, hbj⟩ := ct_jet_one_iter β hβc c hjet
  refine ⟨β, hβ, hb0, hbj, ?_, fun t => ?_⟩
  · refine hl2'.trans ?_
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, Fintype.card_fin]
    have : (2 / (P.q : ℝ)) ^ Col.gB (IR I) ≤ 1 :=
      pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 hq2)
    linarith
  · have := cab_sup hS (ctY (Col.YB hI hP P.q) w) P.q 0 hq2n |P.R0| hR0pos hlat h90' β hβ hl2' t
    simpa [Fintype.card_fin] using this

def ctA {dim : (E →+* ℂ) → ℕ} (x0 : Vsp dim) (q : ℕ) : Vsp dim := (1 / (q : ℂ)) • x0

def ctC {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (q : ℕ) (a : Vsp dim) : ℂ :=
  cexp ((q * Real.pi / 2 : ℂ) * Col.S (IR I) a - q * Real.pi * Hf a a / 2 +
    q * Real.pi * Hf (Col.wmap (IR I) a) (Col.wmap (IR I) a) / 2)

def ctS (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ)
    (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (a : Vsp X.dim) : (Fin 1 → Vsp X.dim) → ℂ :=
  (ctC I q a)⁻¹ • X.U q (fun _ => a) (Col.colS X I q β)

theorem ct_uc_A (x0 : Vsp X.dim) (q : ℕ) :
    Col.uc (IR I) (ctA x0 q) = (1 / (q : ℝ)) • Col.uc (IR I) x0 := by
  unfold Col.uc Col.z ctA
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Col.Hf_smul_l, smul_smul]
  congr 1
  rw [show (1 / (q : ℂ)) = ((1 / (q : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]

theorem ct_norm_C (hI : IsSplit P I) (q : ℕ) (a : Vsp X.dim) :
    ‖ctC I q a‖ = Real.exp (-(q * Real.pi * ‖Col.uc (IR I) a‖ ^ 2)) := by
  have hK := Col.hK_of hI
  unfold ctC
  rw [Complex.norm_exp]
  congr 1
  have h1 := Col.norm_sq_decomp hK a
  have h2 := Col.norm_wmap hK a
  have h3 := Col.norm_uc_sq (IR I) a
  rw [Col.Hf_self a, Col.Hf_self (Col.wmap (IR I) a), h2, h3]
  have hS : (Col.S (IR I) a).re = ∑ k, ((Col.z (IR I) k a).re ^ 2 - (Col.z (IR I) k a).im ^ 2) := by
    unfold Col.S; rw [Complex.re_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq, Complex.mul_re]; ring
  have hn : ∀ k, ‖Col.z (IR I) k a‖ ^ 2 = (Col.z (IR I) k a).re ^ 2 + (Col.z (IR I) k a).im ^ 2 := by
    intro k; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
  rw [hS, h1]
  simp only [hn, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  norm_num
  ring

theorem l2_U_eq_l2 {q : ℕ} {F : (Fin 1 → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q 1) (a : Fin 1 → Vsp X.dim) :
    X.l2 q (X.U q a F) = X.l2 q F := by
  unfold PT.l2
  simp_rw [pointwiseNormSq_translate X]
  have hc : Continuous (fun v => X.ptN2 q F v) := by
    have := hF.1.continuous
    unfold PT.ptN2 HC Hf
    fun_prop
  exact TiledBoundaries.stepT E X 1 ℝ (fun v => X.ptN2 q F v) hc (fun γ hγ v => pointwiseNormSq_add_period X hF hγ v) a

theorem ct_fun (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (a : Vsp X.dim) :
    ctS X I q β a = fun w => (ctC I q a)⁻¹ *
      (cexp (q * Real.pi * Hf (w 0) a - q * Real.pi * Hf a a / 2) * Col.sP X I q β (w 0 - a)) := by
  funext w
  simp [ctS, PT.U, HC, Col.colS]

theorem ct_main (hI : IsSplit P I) (σ : E →+* ℂ) (q c : ℕ)
    (βt : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (hβt : Differentiable ℂ βt) (hb0 : βt 0 = 1)
    (hbj : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j βt 0 = 0) (ua : Vsp X.dim)
    (xs : Fin c → Vsp X.dim) (hxs : ∀ k, InPart σ (xs k)) :
    iteratedFDeriv ℂ c (fun v => cexp (-(2 * Real.pi * q : ℂ) * Complex.I * Hf v ua) * Col.F0 I q βt v) 0 xs =
      ∏ k, (-(2 * Real.pi * q : ℂ) * Complex.I * Hf (xs k) ua) := by
  set c0 : ℂ := -(2 * Real.pi * q : ℂ) * Complex.I with hc0
  set ℓL : Vsp X.dim →L[ℂ] ℂ := c0 • innerSL ℂ ua with hℓ
  have hℓv : ∀ v, ℓL v = c0 * Hf v ua := by
    intro v; rw [hℓ, ContinuousLinearMap.smul_apply, innerSL_apply_apply, Col.Hf_eq_inner, smul_eq_mul]
  have hf1 : (fun v => cexp (c0 * Hf v ua) * Col.F0 I q βt v) =
      fun v => cexp (ℓL v) * Col.F0 I q βt v := by funext v; rw [hℓv]
  rw [hf1]
  set W := Col.wmap (IR I) with hW
  have hexpc : ContDiff ℂ (⊤ : ℕ∞) (fun v => cexp (ℓL v)) := ℓL.contDiff.cexp
  have hgc : ContDiff ℂ (⊤ : ℕ∞) (fun v => βt (W v)) :=
    (cab_contDiff_top (hβt.comp W.differentiable)).of_le (by exact_mod_cast le_top)
  have hF0c : ContDiff ℂ (⊤ : ℕ∞) (Col.F0 I q βt) :=
    (cab_contDiff_top (differentiable_zeroModeLift I q βt hβt)).of_le (by exact_mod_cast le_top)
  have hle : ((c : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hr := cab_restrict (cabVP σ) (c := c) (f := fun v => cexp (ℓL v) * Col.F0 I q βt v)
    (g := fun v => cexp (ℓL v) * βt (W v)) ((hexpc.mul hF0c).of_le hle) ((hexpc.mul hgc).of_le hle)
    (fun v hv => by simp only [zeroModeLift_on_part hI q βt σ v hv, hW]) xs hxs
  rw [hr]
  have hj : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j (fun v => βt (W v)) 0 = 0 := by
    intro j hj1 hjc
    have hβj : ContDiff ℂ j βt := contDiff_of_differentiable_fd hβt j
    have := W.iteratedFDeriv_comp_right hβj (0 : Vsp X.dim) le_rfl
    show iteratedFDeriv ℂ j (βt ∘ W) 0 = 0
    rw [this, map_zero, hbj j hj1 hjc]
    ext x; simp
  have hm := ct_iter_mul_jet_one (fun v => cexp (ℓL v)) (fun v => βt (W v)) hexpc hgc c
    (by simp [hb0]) hj
  rw [hm, ct_iter_cexp_apply]
  have h0 : Hf (0 : Vsp X.dim) ua = 0 := by simp [Hf]
  simp [hℓv, h0]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FibreParseval
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem fibre_parseval (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) :
    HasSum (fun n => ‖zmC hI s n v‖ ^ 2)
      (∫ t in zmBox (Module.finrank ℝ (IR I)), ‖zmG I s (v + tb hI t)‖ ^ 2) :=
  tof_torus_parseval (fun t => zmG I s (v + tb hI t)) (fib_continuous hI hs v)
    (fun t n => fib_periodic hI hs v t n)

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Imports
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem char (hx : Ext.All) : CharStatement :=
  ChA.char_main hx

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ThresholdGeDimension
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField MeasureTheory
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace Col

theorem lint_fd_shift {ι : Type} [Fintype ι] {κ : Type} [Finite κ]
    (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (F : EuclideanSpace ℂ ι → ℝ≥0∞)
    (hF : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ x, F (x + γ) = F x) (a : EuclideanSpace ℂ ι) :
    ∫⁻ x in ZSpan.fundamentalDomain b, F (x + a) = ∫⁻ x in ZSpan.fundamentalDomain b, F x := by
  haveI : VAddInvariantMeasure (↥(Submodule.span ℤ (Set.range b))) (EuclideanSpace ℂ ι) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℂ ι) s⟩
  have hfd := ZSpan.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℂ ι))
  have ht := hfd.preimage_of_equiv (measurePreserving_sub_right volume a).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g x => add_sub_assoc (g : EuclideanSpace ℂ ι) x a)
  have hpre : (fun x => x + a) ⁻¹' ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b) =
      ZSpan.fundamentalDomain b := by
    ext x; simp
  have h1 := (measurePreserving_add_right (volume : Measure (EuclideanSpace ℂ ι)) a).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding F ((fun y => y - a) ⁻¹' ZSpan.fundamentalDomain b)
  rw [hpre] at h1
  refine Eq.trans h1 (ht.setLIntegral_eq hfd F fun g x => ?_)
  show F ((g : EuclideanSpace ℂ ι) + x) = F x
  rw [add_comm]
  exact hF _ g.2 x

variable {E : Type} [Field E] [NumberField E]

theorem three_le_exp : (3 : ℝ) ≤ Real.exp (3 / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  norm_num at h
  linarith

theorem num1 (n : ℕ) (x : ℝ) (hx : 2 * (n : ℝ) + 3 ≤ x) :
    2 * 3 ^ n * Real.exp (-(Real.pi / 4 * x)) ≤ 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx0 : 0 ≤ x := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have h1 : 3 / 2 * (n : ℝ) + 9 / 4 ≤ Real.pi / 4 * x := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpi.le) hx0]
  have h2 : (3 : ℝ) ^ n ≤ Real.exp (3 / 2 * n) := by
    rw [show (3 / 2 * (n : ℝ)) = n * (3 / 2) by ring, Real.exp_nat_mul]
    have h3e := three_le_exp
    gcongr
  have h3 : (2 : ℝ) ≤ Real.exp (9 / 4) := by linarith [Real.add_one_le_exp (9 / 4 : ℝ)]
  have h4 : Real.exp (3 / 2 * n) * Real.exp (9 / 4) ≤ Real.exp (Real.pi / 4 * x) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 h1
  have h5 : Real.exp (Real.pi / 4 * x) * Real.exp (-(Real.pi / 4 * x)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(Real.pi / 4 * x))
  have h6 : 2 * 3 ^ n ≤ Real.exp (Real.pi / 4 * x) := by
    have := mul_le_mul h2 h3 (by norm_num) (Real.exp_pos _).le
    linarith
  calc 2 * 3 ^ n * Real.exp (-(Real.pi / 4 * x)) ≤ Real.exp (Real.pi / 4 * x) * Real.exp (-(Real.pi / 4 * x)) :=
        mul_le_mul_of_nonneg_right h6 hpos.le
    _ = 1 := h5

section Wsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem threshold_ge_dimension : 2 * (dK (IR I) : ℝ) + 3 ≤ P.q * b0 (E := E) P.q P.R0 := by
  obtain ⟨ρ, hρ, hr⟩ := hI.rank
  have h6 : (X.gA : ℝ) * Real.log 2 + 2 * dstar (E := E) P.m + 3 +
      (DF + 1) * (X.r * Real.log X.r + 3 * X.r + 3) ≤ P.q * b0 (E := E) P.q P.R0 := P.C6
  have hdK : (dK (IR I) : ℝ) ≤ dstar (E := E) P.m := by
    have h : Module.finrank ℝ (IR I) ≤ 2 * PT.f E * P.m := by
      rw [hr]; exact Nat.mul_le_mul_left _ hρ
    exact_mod_cast h
  have hlog : 0 ≤ (X.r : ℝ) * Real.log X.r := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hg : (0 : ℝ) ≤ X.gA * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  have hDF : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

theorem finite_uQ (hP : Ext.PackingCount) (R : ℝ) : {c : Qc X I | ‖uQ X I c‖ ≤ R}.Finite := by
  classical
  by_contra hinf
  have hb := cutoff_pos P
  set δ := Real.sqrt (b0 (E := E) P.q P.R0)
  have hδ : 0 < δ := Real.sqrt_pos.2 hb
  set R' := max R δ
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 * R' / δ) ^ (dK (IR I)))
  obtain ⟨T, hT, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hinj : Set.InjOn (uQ X I) T := by
    intro c _ c' _ h
    by_contra hne
    have := uQ_dist hI hne
    rw [h, dist_self] at this
    exact absurd this (not_le.2 hδ)
  have := pack_K hP (IR I) (T.image (uQ X I))
    (fun u hu => by obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu; exact uQ_mem c) δ R' hδ
    (le_max_right _ _)
    (fun u hu => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hu
      exact (hT hc).trans (le_max_left _ _))
    (fun u hu u' hu' hne => by
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hu'
      exact uQ_dist hI (fun h => hne (by rw [h])))
  rw [Finset.card_image_of_injOn hinj, hTc] at this
  linarith

end Wsec

theorem cs_tsum {κ : Type} (w N : κ → ℝ) (hw : ∀ c, 0 ≤ w c) (hN : ∀ c, 0 ≤ N c) (h1 : Summable w)
    (h2 : Summable (fun c => w c * N c ^ 2)) (h3 : Summable (fun c => w c * N c)) :
    (∑' c, w c * N c) ^ 2 ≤ (∑' c, w c) * ∑' c, w c * N c ^ 2 := by
  have key : ∀ t : ℝ, 0 ≤ (∑' c, w c) * t * t + (-2 * ∑' c, w c * N c) * t + ∑' c, w c * N c ^ 2 := by
    intro t
    have e : ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c) =
        (∑' c, w c * N c ^ 2) - 2 * t * (∑' c, w c * N c) + t ^ 2 * ∑' c, w c := by
      rw [(h2.sub (h3.mul_left _)).tsum_add (h1.mul_left _), h2.tsum_sub (h3.mul_left _), tsum_mul_left,
        tsum_mul_left]
    have hnn : 0 ≤ ∑' c, (w c * N c ^ 2 - 2 * t * (w c * N c) + t ^ 2 * w c) :=
      tsum_nonneg fun c => by nlinarith [mul_nonneg (hw c) (sq_nonneg (N c - t))]
    nlinarith [e, hnn]
  have hd := discrim_le_zero (a := ∑' c, w c) (b := -2 * ∑' c, w c * N c) (c := ∑' c, w c * N c ^ 2)
    (fun t => by nlinarith [key t])
  unfold discrim at hd
  nlinarith [hd]

section Wsec2

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound)
include hI hP hA

theorem sum_w_le (u : Vsp X.dim) :
    Summable (fun c : Qc X I => Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2)) ∧
      ∑' c : Qc X I, Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2) ≤ 2 := by
  have hpi := Real.pi_gt_three
  set g : Qc X I → ℝ := fun c => Real.exp (-(Real.pi / 4 * P.q) * ‖uQ X I c‖ ^ 2) with hg
  have hgs : Summable g := summable_gauss hI hP hA (Real.pi / 4) (by linarith)
  have htail := tailQ hI hP hA (Real.pi / 4) (by positivity) (cond_tail hI (Real.pi / 4) (by linarith))
  have hsplit : ∑' c, g c = g 0 + ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, g c := by
    rw [← hgs.sum_add_tsum_compl (s := {0}), Finset.sum_singleton]
    rfl
  have hg0 : g 0 = 1 := by simp [hg]
  have hnum := num1 (dK (IR I)) (P.q * b0 (E := E) P.q P.R0) (threshold_ge_dimension hI)
  have hgle : ∑' c, g c ≤ 2 := by
    rw [hsplit, hg0]
    have h2 := htail.2
    rw [show Real.pi / 4 * P.q * b0 (E := E) P.q P.R0 = Real.pi / 4 * (P.q * b0 (E := E) P.q P.R0) by ring] at h2
    linarith
  obtain ⟨c0, -, hmin⟩ := Set.exists_min_image {c : Qc X I | ‖uQ X I c‖ ≤ 2 * ‖u‖}
    (fun c => ‖u - uQ X I c‖) (finite_uQ hI hP _) ⟨0, by simp⟩
  have hglob : ∀ c, ‖u - uQ X I c0‖ ≤ ‖u - uQ X I c‖ := by
    intro c
    by_cases hc : ‖uQ X I c‖ ≤ 2 * ‖u‖
    · exact hmin c hc
    · have h0 := hmin 0 (by simp)
      simp only [map_zero, sub_zero] at h0
      push Not at hc
      have : ‖uQ X I c‖ - ‖u‖ ≤ ‖u - uQ X I c‖ := by
        have := norm_sub_norm_le (uQ X I c) u
        rw [norm_sub_rev] at this; exact this
      linarith
  have hpt : ∀ c, Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2) ≤ g (c - c0) := by
    intro c
    simp only [hg, map_sub]
    apply Real.exp_le_exp.2
    have h1 : ‖uQ X I c - uQ X I c0‖ ≤ 2 * ‖u - uQ X I c‖ := by
      calc ‖uQ X I c - uQ X I c0‖ = ‖(u - uQ X I c0) - (u - uQ X I c)‖ := by congr 1; abel
        _ ≤ ‖u - uQ X I c0‖ + ‖u - uQ X I c‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hglob c]
    have h2 : ‖uQ X I c - uQ X I c0‖ ^ 2 ≤ 4 * ‖u - uQ X I c‖ ^ 2 := by
      nlinarith [norm_nonneg (uQ X I c - uQ X I c0), norm_nonneg (u - uQ X I c)]
    have hq : (0 : ℝ) ≤ P.q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Real.pi / 4 * P.q)]
  have hgs' : Summable (fun c => g (c - c0)) := (Equiv.subRight c0).summable_iff.2 hgs
  have hs : Summable (fun c : Qc X I => Real.exp (-(P.q * Real.pi) * ‖u - uQ X I c‖ ^ 2)) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hpt hgs'
  refine ⟨hs, (hs.tsum_le_tsum hpt hgs').trans ?_⟩
  have := (Equiv.subRight c0).tsum_eq g
  simp only [Equiv.subRight_apply] at this
  rw [this]
  exact hgle

end Wsec2

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmMem
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

theorem zm_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ZM.zmB hI s ∈ (Col.YB hI hP 1).Sec 1 :=
  zeroMode_mem_sections hI hP hs

theorem zm_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (w : Vsp X.dim) (T M : ℝ)
    (hT : ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T)
    (hM : ∀ t, (Col.YB hI hP 1).ptN2 1 (ZM.zmB hI s) t ≤ M) :
    Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T :=
  zeroMode_pointwise_bound hI hP hs w T M hT hM

end ReciprocityTheory.ChartRestriction.G.I2
end

