module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.NormMono
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvXI
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsShift
section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

theorem cls_shift {n : ℕ} (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y = cls s z p q R y := by
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul]
  ring

theorem wr_of : Gauss → ClsBound → ClsGain → IBP → Integr → Dens → WRSt := by
  intro hG hB hGain hIBP hI hD m n ε c t hc ht P
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.2 hc.ne'
  have hs' : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left; simp [hc.ne']
    · right; simp [hc.ne']
  generalize ((t / c : ℝ) : ℂ) = s at hR hs'
  have hs := hs'
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hR
  generalize (Finset.univ.filter fun a => ε a = false).card = q at hR
  obtain ⟨-, hint⟩ := hI n
  obtain ⟨g, hgc, hgd, hgv⟩ := hD m n ε c t hc ht P (n ^ 2 + 1) (by
    push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  refine ⟨g, hgc, hgd, fun β hβ => ?_⟩
  have hGN := fun N => hGain n s hs p q N R
  choose J a G hGc hGb hGeq using hGN
  choose CG hCG using hGb
  have hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := fun N j y => by
    have := hCG N j y
    rwa [neg_div] at this
  set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK
  let Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ := fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y
  let WN : ℕ → ℂ → ℂ := fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z
  let U : ℕ → Set ℂ := fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2}
  let orig : ℂ → ℂ := fun z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
  have hUopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N) := by
    intro N
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    exact (a N j).differentiable.differentiableOn.mul
      (holo hI t β (hGc N j) (((p + q + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))

  have hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 →
      ∫ y, (Delta^[N] (cls s z p q R)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z := by
    intro N z hz
    have e : (fun y => (Delta^[N] (cls s z p q R)) y * chr t β y) =
        fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y) := by
      funext y
      rw [hGeq N z y, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z := by
    intro N z hz
    have e1 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => cls s z p q R y * chr t β y := by
      funext y
      rw [hR y, ← cls_shift s z]
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    have good : Good (cls s z p q R) := by
      refine ⟨(hB n s hs p q R z).1, fun L => ?_⟩
      obtain ⟨C, hC⟩ := (hB n s hs p q R z).2 L
      exact ⟨fun y => C * dP y ^ (-(z.re + ((p : ℝ) + q) / 2)), (hint _ (by linarith)).const_mul C, hC⟩
    have hz' : (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    show KK ^ N * _ = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
    rw [e1, ibp_iter hIBP good t β ht0 hβ N, hsum N z hz']
  have agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N) := by
    intro N N' hNN'
    have hsub : U N ⊆ U N' := fun z hz => by
      simp only [U, Set.mem_ofPred_eq] at hz ⊢
      have : ((p + q + N : ℕ) : ℝ) ≤ ((p + q + N' : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have hA : AnalyticOnNhd ℂ (WN N) (U N) := (hWdiff N).analyticOnNhd (hUopen N)
    have hA' : AnalyticOnNhd ℂ (WN N') (U N) := ((hWdiff N').mono hsub).analyticOnNhd (hUopen N)
    have hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((p + q + N : ℕ) : ℝ) / 2 < z.re} := by
      ext z
      simp only [U, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hpre : IsPreconnected (U N) := by
      rw [hU]; exact (convex_halfSpace_re_gt _).isPreconnected
    set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1
    have hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1 := by rw [hz1, Complex.ofReal_re]
    have hz1U : z1 ∈ U N := by
      simp only [U, Set.mem_ofPred_eq, hz1re]
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := by
      simp only [Set.mem_ofPred_eq, hz1re]; linarith
    have hev : WN N =ᶠ[𝓝 z1] WN N' :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm
    exact hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev
  have agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z := by
    intro N N' z hz hz'
    rcases le_total N N' with h | h
    · exact agree N N' h hz
    · exact (agree N' N h hz').symm
  obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1 := ⟨_, fun _ => rfl⟩
  have hNf : ∀ z, z ∈ U (Nf z) := by
    intro z
    show (n : ℝ) ^ 2 / 2 < z.re + ((p + q + Nf z : ℕ) : ℝ) / 2
    rw [hNfdef z]
    have h1 := Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)
    push_cast
    have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
    linarith
  refine ⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · intro z0
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0) :=
      Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz
    exact (((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev
  · have e2 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y * chr t β y := by
      funext y; rw [hR y]
    rw [e2]
    obtain ⟨C, hC⟩ := (hB n s hs p q R 0).2 []
    have hC0 : ∀ y, ‖cls s 0 p q R y‖ ≤ C * dP y ^ (-(((p : ℝ) + q) / 2)) := by
      intro y
      have := hC y
      simp only [List.foldr_nil, Complex.zero_re, zero_add] at this
      exact this
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    exact integ_term hI t β (hB n s hs p q R 0).1.continuous hC0 (by linarith)
  · exact hbig (Nf z) z hz
  · have hN0 : Nf 0 = n ^ 2 + 1 := by
      rw [hNfdef, Complex.zero_re, mul_zero, sub_zero,
        show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
    show WN (Nf 0) 0 = _
    rw [hN0, hgv β hβ]
    have hfun : (fun y => secN ε c t P (herm y)) = cls s 0 p q R := funext hR
    rw [hfun, hsum (n ^ 2 + 1) 0 (by
      simp only [Complex.zero_re, zero_add]
      push_cast
      have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
      linarith)]
    show KK ^ (n ^ 2 + 1) * _ = _
    rw [hKK]
    ring

end PositivityTheory.Rg.Sw.WR.T
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousGramX
section
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

theorem integP : IntegP := GI.integP

lemma map_smul_volume {m n : ℕ} (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = volume := by
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) :=
    ((ζ • LinearMap.id : (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ))).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq, hζ]
    simp
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ)))
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at this
  calc Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = Measure.map (⇑L) volume := rfl
    _ = volume := by rw [this]; simp

lemma evX_smul_mono {m n : ℕ} (ζ : ℂ) (d : (Fin m × Fin n × Bool) →₀ ℕ) (hd : ∀ k, k.2.2 = true → d k = 0)
    (x : Fin m → Fin n → ℂ) :
    evX (monomial d 1) (ζ • x) = ζ ^ (d.sum fun _ e => e) * evX (monomial d 1) x := by
  unfold evX
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod,
    Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk2 : k.2.2 = false := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hd k (by simpa using h))
  simp [hk2, mul_pow]

lemma gs_smul {m n : ℕ} (c : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) : gs c (ζ • x) = gs c x := by
  unfold gs
  simp [hζ]

lemma gramX_smul {m n : ℕ} (ε : Fin m → Bool) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) :
    gramX ε (ζ • x) = gramX ε x := by
  have h1 : (starRingEnd ℂ) ζ * ζ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]; simp
  have key : ∀ u v : ℂ, (starRingEnd ℂ) (ζ * u) * (ζ * v) = (starRingEnd ℂ) u * v := by
    intro u v
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) u * v) * h1
  ext _i _j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, evX, Qp, Qb, map_sub, map_sum, map_mul, MvPolynomial.eval_X]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
    simp only [Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, if_true, if_false] <;>
    exact key _ _

lemma continuous_gramX {m n : ℕ} (ε : Fin m → Bool) : Continuous fun x : Fin m → Fin n → ℂ => gramX ε x :=
  continuous_pi fun i => continuous_pi fun j => GI.continuous_evX _

theorem rot : Rot := by
  intro m n ε c t hc b hb d hd hd0
  set N := d.sum fun _ e => e with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hd0
    ext k
    have := (Finset.sum_eq_zero_iff.mp h) k
    by_cases hk : k ∈ d.support
    · simpa using this hk
    · simpa using hk
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  set ζ : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) with hζdef
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, Complex.norm_exp_ofReal_mul_I]
  have hζN : ζ ^ N = -1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (((Real.pi / N : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  let F : (Fin m → Fin n → ℂ) → ℂ := fun x =>
    evX (monomial d 1) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
  have hcont : Continuous F :=
    ((GI.continuous_evX _).mul (GI.continuous_gs c)).mul (Complex.continuous_exp.comp
      (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace)))
  have hcomp : (fun x => F (ζ • x)) = fun x => ζ ^ N * F x := by
    funext x
    simp only [F, evX_smul_mono ζ d hd, gs_smul c ζ hζ, gramX_smul ε ζ hζ]
    ring
  have hint : ∫ x, F (ζ • x) = ∫ x, F x := by
    rw [← integral_map (μ := volume) (φ := fun x : Fin m → Fin n → ℂ => ζ • x)
      (continuous_const_smul ζ).measurable.aemeasurable
      (by rw [map_smul_volume ζ hζ]; exact hcont.aestronglyMeasurable), map_smul_volume ζ hζ]
  have h2 : ∫ x, F x = -∫ x, F x := by
    conv_lhs => rw [← hint, hcomp, integral_const_mul, hζN, neg_one_mul]
  show ∫ x, F x = 0
  linear_combination (1 / 2 : ℂ) * h2

end PositivityTheory.Rg.Sw.WR.G
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DerivF
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}

theorem FP_eq_integral_Fi (P : PX m n) (y : E n) : FP ε c t P y = ∫ x, Fi ε c t P y x := rfl

theorem fderiv_FP_apply (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    fderiv ℝ (FP ε c t P) y w = ∫ x, Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  rw [(hasFDerivAt_FP hI hq hc P y).fderiv, ContinuousLinearMap.integral_apply (integrable_Fd hI hq hc P y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

theorem integrable_Fi_mul (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    Integrable fun x => Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  have h := (integrable_Fd (t := t) hI hq hc P y).apply_continuousLinearMap w
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

theorem dirC_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n)
    (v : Fin n → Fin n → ℂ) (y : E n) :
    dirC (FP ε c t P) v y =
      ∫ x, Fi ε c t P y x * (Complex.I * t) * ∑ a, ∑ b, v a b * (qX ε x a b : ℂ) := by
  unfold dirC
  rw [fderiv_FP_apply hI hq hc, fderiv_FP_apply hI hq hc, ← integral_const_mul,
    ← integral_add (integrable_Fi_mul hI hq hc P y _) ((integrable_Fi_mul hI hq hc P y _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have e : ∀ a b, v a b = ((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ) := fun a b => by
    rw [mul_comm]; exact (Complex.re_add_im (v a b)).symm
  simp only [ip, Complex.ofReal_sum, Complex.ofReal_mul]
  conv_rhs => rw [show (∑ a, ∑ b, v a b * (qX ε x a b : ℂ)) =
    ∑ a, ∑ b, (((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ)) * (qX ε x a b : ℂ) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [← e]]
  simp only [add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  ring_nf

theorem sum_ite_pair (k l : Fin n) (α : ℂ) (f : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, (if a = k ∧ b = l then α else 0) * f a b = α * f k l := by
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_vkl (hA : AlgA) (k l : Fin n) (x : Fin m → Fin n → ℂ) :
    ∑ a, ∑ b, vkl k l a b * (qX ε x a b : ℂ) = evX (Qp ε k l) x := by
  have h := congrFun (congrFun ((hA m n ε).2.1 x) k) l
  have g : gramX ε x k l = evX (Qp ε k l) x := rfl
  rw [← g, ← h]
  simp only [vkl, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_pair k l _ (fun a b => (qX ε x a b : ℂ)), sum_ite_pair l k _ (fun a b => (qX ε x a b : ℂ))]
  simp only [herm]
  push_cast
  ring

theorem Dkl_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) (k l : Fin n) :
    Dkl k l (FP ε c t P) = FP ε c t (MvPolynomial.C (Complex.I * t) * Qp ε k l * P) := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  unfold Dkl
  rw [dirC_FP hI hq hc]
  unfold FP
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [sum_vkl hA]
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]
  ring

theorem FP_add (hI : IntG) (hA : AlgA) (hc : 0 < c) (P Q : PX m n) :
    FP ε c t (P + Q) = FP ε c t P + FP ε c t Q := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  simp only [Pi.add_apply]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, FP_eq_integral_Fi,
    ← integral_add (integrable_Fi hI hq hc P y) (integrable_Fi hI hq hc Q y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_add (f := _)]; ring

theorem FP_C_mul (a : ℂ) (P : PX m n) :
    FP ε c t (MvPolynomial.C a * P) = a • FP ε c t P := by
  funext y
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]; ring

theorem FP_sum (hI : IntG) (hA : AlgA) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    FP ε c t (∑ i ∈ s, f i) = ∑ i ∈ s, FP ε c t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext y
    simp only [Finset.sum_empty, Finset.sum_apply, Pi.zero_apply]
    rw [FP_eq_integral_Fi]
    simp [Fi, evX]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, FP_add hI hA hc, ih]

theorem foldr_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (σ : Equiv.Perm (Fin n)) (L : List (Fin n)) (P : PX m n) :
    L.foldr (fun k g => Dkl k (σ k) g) (FP ε c t P) =
      FP ε c t ((L.map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod * P) := by
  induction L with
  | nil => simp
  | cons k L ih =>
    rw [List.foldr_cons, ih, Dkl_FP hI hA hc, List.map_cons, List.prod_cons]
    congr 1; ring

theorem sum_perm_eq_det :
    ∑ σ : Equiv.Perm (Fin n), MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod)
      = MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε := by
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod =
        MvPolynomial.C ((Complex.I * t) ^ n) * ∏ k, Qp ε k (σ k) := by
    intro σ
    rw [← Fin.prod_univ_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      map_pow]
  simp only [hprod]
  rw [detQ, ← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [show (MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) : PX m n) = (((Equiv.Perm.sign σ : ℤ) : PX m n)) by
    simp]
  ring

theorem Delta_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) :
    Delta (FP ε c t P) = FP ε c t (MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε * P) := by
  unfold Delta
  simp only [foldr_FP hI hA hc]
  rw [← sum_perm_eq_det (ε := ε) (t := t), Finset.sum_mul, FP_sum hI hA hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, FP_C_mul]

theorem derivF_of (hI : IntG) (hA : AlgA) : DerivF := by
  intro m n ε c t hc P N
  have hq := (hA m n ε).2.2.2.2
  refine ⟨continuous_iff_continuousAt.2 fun y => (hasFDerivAt_FP hI hq hc P y).continuousAt, ?_⟩
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, Delta_FP hI hA hc, pow_succ]
    congr 1; ring

theorem derivF : DerivF := derivF_of intG algA

end PositivityTheory.Rg.Sw.WR.D
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBLagr
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

theorem lagr : Lagr := by
  intro D
  set V : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ := Matrix.vandermonde fun i => ((i : ℕ) : ℂ) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hij : i < j := (Finset.mem_Ioi.1 hj)
    intro h
    have : ((j : ℕ) : ℂ) = ((i : ℕ) : ℂ) := by linear_combination h
    have := Nat.cast_injective this
    exact absurd (Fin.ext this) (ne_of_gt hij)
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.2 hdet
  set W := V⁻¹ with hW
  refine ⟨∑ j, ∑ i, ‖W j i‖, fun c B hB j hj => ?_⟩
  set cv : Fin (D + 1) → ℂ := fun j => c j with hcv
  have hvals : ∀ i : Fin (D + 1), V.mulVec cv i = ∑ j ∈ Finset.range (D + 1), (((i : ℕ) : ℕ) : ℂ) ^ j * c j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hcv]
    rw [Fin.sum_univ_eq_sum_range (fun k => ((i : ℕ) : ℂ) ^ k * c k)]
  have hB' : ∀ i : Fin (D + 1), ‖V.mulVec cv i‖ ≤ B := fun i => by
    rw [hvals i]; exact hB i (Nat.lt_succ_iff.1 i.2)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  have hinv : W.mulVec (V.mulVec cv) = cv := by
    rw [Matrix.mulVec_mulVec, hW, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  set jj : Fin (D + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hc : c j = ∑ i, W jj i * V.mulVec cv i := by
    have := congrFun hinv jj
    simp only [Matrix.mulVec, dotProduct, hcv] at this ⊢
    rw [this]
  rw [hc]
  calc ‖∑ i, W jj i * V.mulVec cv i‖ ≤ ∑ i, ‖W jj i * V.mulVec cv i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖W jj i‖ * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' i) (norm_nonneg _)
    _ = (∑ i, ‖W jj i‖) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ i, ‖W j i‖) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact Finset.single_le_sum (f := fun j => ∑ i, ‖W j i‖) (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _)
          (Finset.mem_univ jj)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

