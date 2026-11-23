module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConnA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
section
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma sgn_cast_eq (p0 r : ℕ) : (fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) = sv p0 := by
  funext a
  unfold sgn sv
  split_ifs <;> simp

lemma pos_conj_mul {s : ℝ} {c d : ℂ} (hc : c ≠ 0) (h : 0 < s * d.re) : 0 < s * (c * d * conj c).re := by
  have hn := Complex.normSq_pos.mpr hc
  rw [mul_comm c d, mul_assoc, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h2 : s * (d.re * Complex.normSq c) = (s * d.re) * Complex.normSq c := by ring
  rw [h2]
  exact mul_pos h hn

lemma mem_dom_of_ok {r : ℕ} (X : Data E r) (P : X.Ψ → Matrix (Fin r) (Fin r) ℂ)
    (hP : ∀ τ, (P τ).det ≠ 0 ∧ gram τ.1 X.Gm (P τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, Ok X.p0 (y τ)) :
    (fun τ => (P τ * y τ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ X.dom := by
  intro τ
  have hg : gram τ.1 X.Gm (P τ * y τ) = Gy X.p0 (y τ) := by
    rw [FrameDegreeData.gram_mul, (hP τ).2, sgn_cast_eq]
    rfl
  refine ⟨?_, fun i => ?_⟩
  · show (P τ * y τ).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (hP τ).1 (det_ne_of_ok (hy τ))
  · show 0 < psgn X.p0 i * (lminor (gram τ.1 X.Gm (P τ * y τ)) i).re
    rw [hg]
    unfold psgn sgn lminor
    exact lead_pos (hy τ) i (Nat.le_of_lt_succ i.isLt)

lemma rmul_mem {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [FrameDegreeData.dmin_rmul X x hb τ i]
    exact pos_conj_mul (Finset.prod_ne_zero_iff.2 fun j _ => FrameDegreeData.bdiag_ne X hb τ _) ((hx τ).2 i)

theorem flag_domain_frames_connected : GGConnStatement (E := E) := by
  intro r X
  choose P hP using X.signature
  let K : Set (X.Ψ → Matrix (Fin r) (Fin r) ℂ) := {y | ∀ τ, Ok X.p0 (y τ)}
  let φ : (X.Ψ → Matrix (Fin r) (Fin r) ℂ) → Frame X.Ψ r := fun y τ => (P τ * y τ : Matrix (Fin r) (Fin r) ℂ)
  have hφc : Continuous φ := continuous_pi fun τ => continuous_const.matrix_mul (continuous_apply τ)
  have hK : ∀ y ∈ K, φ y ∈ X.dom := fun y hy => mem_dom_of_ok X P hP y hy
  have hKc : IsPreconnected (φ '' K) := isPreconnected_ok.image φ hφc.continuousOn
  have hss : ∀ a : Fin r, sv X.p0 a * sv X.p0 a = 1 := fun a => by
    unfold sv
    split_ifs <;> norm_num
  have h1 : (1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) ∈ K := fun τ =>
    ok_of_blk (fun k a hka => by
      have hne : k ≠ a := by
        rintro rfl
        exact hka Iff.rfl
      simp [Matrix.one_apply_ne hne]) (by simp)
  refine ⟨⟨φ 1, hK 1 h1⟩, isPreconnected_of_forall (φ 1) fun x hx => ?_⟩
  obtain ⟨b, hb, hort⟩ := (orthonormalFlagTranslate_holds r X).1 x hx
  let y0 : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (P τ)⁻¹ * mat (rmul x b) τ
  have hy0τ : ∀ τ, P τ * y0 τ = mat (rmul x b) τ := fun τ =>
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hP τ).1)
  have hy0 : φ y0 = rmul x b := funext fun τ => hy0τ τ
  have hy0K : y0 ∈ K := by
    intro τ
    have hg : Gy X.p0 (y0 τ) = diagonal (sv X.p0) := by
      have h2 : gram τ.1 X.Gm (P τ * y0 τ) = Gy X.p0 (y0 τ) := by
        rw [FrameDegreeData.gram_mul, (hP τ).2, sgn_cast_eq]
        rfl
      rw [← h2, hy0τ τ, hort τ, sgn_cast_eq]
    unfold Ok
    rw [hg, diagonal_mul_diagonal]
    simp only [hss]
    rw [diagonal_one]
    exact PosDef.one
  have hB : IsPreconnected (Bor X.Ψ r) := isPreconnected_upper (ι := X.Ψ) (r := r)
  have h1B : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := fun τ =>
    ⟨by
      show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      simp, fun a c hca => Matrix.one_apply_ne (ne_of_gt hca)⟩
  have hxB : rmul x (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = x := by
    funext τ
    exact Matrix.mul_one (mat x τ)
  have hrc : Continuous fun b' : Frame X.Ψ r => rmul x b' :=
    continuous_pi fun τ => continuous_const.matrix_mul (continuous_apply τ)
  refine ⟨(fun b' => rmul x b') '' Bor X.Ψ r ∪ φ '' K, ?_, Or.inr ⟨1, h1, rfl⟩, Or.inl ⟨_, h1B, hxB⟩, ?_⟩
  · rintro z (⟨b', hb', rfl⟩ | ⟨y, hy, rfl⟩)
    · exact rmul_mem X hx hb'
    · exact hK y hy
  · exact IsPreconnected.union (rmul x b) ⟨b, hb, rfl⟩ ⟨y0, hy0K, hy0⟩ (hB.image _ hrc.continuousOn) hKc

end

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeRatio
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf

section Chars

variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]

theorem two_mul_eq_zero {x : k} (h : 2 * x = 0) : x = 0 := by
  have h2 : algebraMap ℚ k (1 / 2) * 2 = 1 := by
    rw [show (2 : k) = algebraMap ℚ k 2 from (map_ofNat (algebraMap ℚ k) 2).symm, ← map_mul]
    norm_num
  calc x = (algebraMap ℚ k (1 / 2) * 2) * x := by rw [h2, one_mul]
    _ = algebraMap ℚ k (1 / 2) * (2 * x) := by ring
    _ = 0 := by rw [h, mul_zero]

theorem pair_prod (c : k) (s s' : O →+* k)
    (h : ∀ a, c * (s a * s (star a) + s' a * s' (star a) - 2 * s a * s' a) = 0) (a : O) :
    c * ((s a - s (star a)) * (s a - s' (star a))) = 0 := by
  apply two_mul_eq_zero
  have h0 := h a
  have h1 := h (a + 1)
  have h2 := h (a * a)
  have h3 := h (a * a + 1)
  simp only [map_add (f := _), map_one, map_mul, star_add, star_one, star_mul] at h1 h2 h3
  linear_combination (-1 : k) * (h3 - h2) + (s' a + s (star a) + s' (star a) - s a) * (h1 - h0)

variable {T : Type} (χ : T → O →+* k) (cc : T → T) (hcc : ∀ σ a, χ (cc σ) a = χ σ (star a))
  (hunit : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
include hunit

theorem either {c : k} (hc : c ≠ 0) (σ τ₁ τ₂ : T)
    (P : ∀ a, c * ((χ σ a - χ τ₁ a) * (χ σ a - χ τ₂ a)) = 0) : σ = τ₁ ∨ σ = τ₂ := by
  by_contra hne
  push_neg at hne
  obtain ⟨a₁, hu₁⟩ := hunit σ τ₁ hne.1
  obtain ⟨a₂, hu₂⟩ := hunit σ τ₂ hne.2
  have e1 : c * (χ σ a₁ - χ τ₂ a₁) = 0 := by
    have h' : (χ σ a₁ - χ τ₁ a₁) * (c * (χ σ a₁ - χ τ₂ a₁)) = 0 := by linear_combination P a₁
    exact hu₁.mul_right_eq_zero.1 h'
  have e2 : c * (χ σ a₂ - χ τ₁ a₂) = 0 := by
    have h' : (χ σ a₂ - χ τ₂ a₂) * (c * (χ σ a₂ - χ τ₁ a₂)) = 0 := by linear_combination P a₂
    exact hu₂.mul_right_eq_zero.1 h'
  have e3 := P (a₁ + a₂)
  simp only [map_add (f := _)] at e3
  have e4 : ((χ σ a₁ - χ τ₁ a₁) * (χ σ a₂ - χ τ₂ a₂)) * c = 0 := by
    linear_combination e3 - ((χ σ a₁ - χ τ₁ a₁) + (χ σ a₂ - χ τ₁ a₂)) * e1 - (χ σ a₂ - χ τ₂ a₂) * e2
  exact hc ((hu₁.mul hu₂).mul_right_eq_zero.1 e4)

include hcc in
theorem cc_cc {c : k} (hc : c ≠ 0) (σ : T) : cc (cc σ) = σ := by
  by_contra hne
  obtain ⟨a, ha⟩ := hunit _ _ hne
  rw [hcc, hcc, star_star, sub_self] at ha
  have h01 := isUnit_zero_iff.1 ha
  apply hc
  calc c = c * 1 := (mul_one c).symm
    _ = c * 0 := by rw [h01]
    _ = 0 := mul_zero c

include hcc in
theorem pair_index {c : k} (hc : c ≠ 0) (σ σ' : T)
    (h : ∀ a, c * (χ σ a * χ σ (star a) + χ σ' a * χ σ' (star a) - 2 * χ σ a * χ σ' a) = 0) : σ' = cc σ := by
  have P1 : ∀ a, c * ((χ σ a - χ (cc σ) a) * (χ σ a - χ (cc σ') a)) = 0 := by
    intro a
    rw [hcc, hcc]
    exact pair_prod c (χ σ) (χ σ') h a
  have h' : ∀ a, c * (χ σ' a * χ σ' (star a) + χ σ a * χ σ (star a) - 2 * χ σ' a * χ σ a) = 0 := by
    intro a
    linear_combination h a
  have P2 : ∀ a, c * ((χ σ' a - χ (cc σ') a) * (χ σ' a - χ (cc σ) a)) = 0 := by
    intro a
    rw [hcc, hcc]
    exact pair_prod c (χ σ') (χ σ) h' a
  rcases either χ hunit hc σ _ _ P1 with h1 | h1
  · rcases either χ hunit hc σ' _ _ P2 with h2 | h2
    · by_contra hne
      have hne' : σ ≠ σ' := fun e => hne (by rw [← e]; exact h1)
      obtain ⟨a, ha⟩ := hunit σ σ' hne'
      have hs : χ σ (star a) = χ σ a := by rw [← hcc, ← h1]
      have hs' : χ σ' (star a) = χ σ' a := by rw [← hcc, ← h2]
      have e := h a
      rw [hs, hs'] at e
      have e' : ((χ σ a - χ σ' a) * (χ σ a - χ σ' a)) * c = 0 := by linear_combination e
      exact hc ((ha.mul ha).mul_right_eq_zero.1 e')
    · exact h2
  · rw [h1, cc_cc χ cc hcc hunit hc]

end Chars

section Series

variable {O k T : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k] [Fintype T] {rk : T → ℕ}
  (χ : T → O →+* k)

theorem coeff_scale (a : O) (f : MvPowerSeries (GLet T rk) k) (m : GLet T rk →₀ ℕ) :
    coeff m (scaleBy χ a f) = (m.prod fun l e => χ l.1 a ^ e) * coeff m f := by
  unfold scaleBy
  rw [MvPowerSeries.coeff_rescale]

theorem cc_scale (a : O) {f : MvPowerSeries (GLet T rk) k} (hf : constantCoeff f = 0) :
    constantCoeff (scaleBy χ a f) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_scale,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero]

theorem scale_exp (a : O) {f : MvPowerSeries (GLet T rk) k} (hf : constantCoeff f = 0) :
    scaleBy χ a (PowerSeries.subst f (PowerSeries.exp k)) = PowerSeries.subst (scaleBy χ a f) (PowerSeries.exp k) := by
  unfold scaleBy
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_eq_subst]
  refine WickVanishing.subst_exp _ (fun s => ?_) hf
  simp

theorem prod_two_pow (m : GLet T rk →₀ ℕ) : (m.prod fun _ e => (2 : k) ^ e) = 2 ^ m.degree := by
  unfold Finsupp.prod Finsupp.degree
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem prod_pair (g : GLet T rk → k) (l l' : GLet T rk) :
    ((Finsupp.single l 1 + Finsupp.single l' 1).prod fun l e => g l ^ e) = g l * g l' := by
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun x e => g x ^ e) (by simp),
    Finsupp.prod_single_index (h := fun x e => g x ^ e) (by simp), pow_one, pow_one]

theorem eq_zero_of_pow_sub {n : ℕ} (hn : n ≠ 2) {x : k} (h : ((2 : k) ^ n - 4) * x = 0) : x = 0 := by
  have hq : ((2 : ℚ) ^ n - 4) ≠ 0 := by
    intro h0
    have h4 : (2 : ℚ) ^ n = 2 ^ 2 := by linarith
    exact hn (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h4))
  have e : algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x = 0 := by
    rw [map_sub, map_pow, map_ofNat (algebraMap ℚ k) 2, map_ofNat (algebraMap ℚ k) 4]
    exact h
  calc x = algebraMap ℚ k (((2 : ℚ) ^ n - 4)⁻¹ * ((2 : ℚ) ^ n - 4)) * x := by
        rw [inv_mul_cancel₀ hq, map_one, one_mul]
    _ = algebraMap ℚ k (((2 : ℚ) ^ n - 4)⁻¹) * (algebraMap ℚ k ((2 : ℚ) ^ n - 4) * x) := by
        rw [map_mul, mul_assoc]
    _ = 0 := by rw [e, mul_zero]

end Series

theorem gaugeRatio : GaugeRatioSt := by
  unfold GaugeRatioSt
  intro O _ _ k _ _ T _ rk χ cc hcc hunit r hr hfe
  obtain ⟨q, hq0, hrq⟩ : ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧
      r = PowerSeries.subst q (PowerSeries.exp k) :=
    ⟨_, WickVanishing.constantCoeff_logS hr, (WickVanishing.exp_log hr).symm⟩
  have hA : ∀ b : O, constantCoeff (scaleBy χ b q) = 0 := fun b => cc_scale χ b hq0
  have hE : ∀ b : O, scaleBy χ b r = PowerSeries.subst (scaleBy χ b q) (PowerSeries.exp k) := by
    intro b
    rw [hrq]
    exact scale_exp χ b hq0
  have key : ∀ a : O, scaleBy χ (1 + a * star a) q =
      scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q := by
    intro a
    have h1 := hfe a
    rw [hE, hE, hE] at h1
    rw [hrq] at h1
    have s1 : constantCoeff (scaleBy χ a q + scaleBy χ a q) = 0 := by rw [map_add (f := _), hA, add_zero]
    have s2 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q) = 0 := by rw [map_add (f := _), s1, hq0, add_zero]
    have s3 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q) = 0 := by
      rw [map_add (f := _), s2, hA, add_zero]
    apply WickVanishing.exp_inj (hA _) s3
    rw [h1, WickVanishing.exp_add s2 (hA _), WickVanishing.exp_add s1 hq0, WickVanishing.exp_add (hA _) (hA _)]
    ring
  have hcoef : ∀ (a : O) (m : GLet T rk →₀ ℕ),
      (m.prod fun l e => χ l.1 (1 + a * star a) ^ e) * coeff m q =
        ((m.prod fun l e => χ l.1 a ^ e) + (m.prod fun l e => χ l.1 a ^ e) + 1 +
          (m.prod fun l e => χ l.1 (a * star a) ^ e)) * coeff m q := by
    intro a m
    have h := congrArg (fun f => coeff m f) (key a)
    rw [map_add (f := _), map_add (f := _), map_add (f := _)] at h
    simp only [coeff_scale] at h
    rw [h]
    ring
  refine ⟨q, hq0, ?_, ?_, hrq⟩
  · intro m hm
    by_contra hdeg
    have h := hcoef 1 m
    have t2 : ∀ l : GLet T rk, χ l.1 (1 + 1) = 2 := fun l => by
      rw [map_add (f := _), map_one, one_add_one_eq_two]
    have t1 : ∀ l : GLet T rk, χ l.1 1 = 1 := fun l => map_one _
    simp only [star_one, mul_one, t1, one_pow] at h
    simp only [t2] at h
    rw [prod_two_pow (k := k) m] at h
    have p1 : (m.prod fun (_ : GLet T rk) (_ : ℕ) => (1 : k)) = 1 := by simp [Finsupp.prod]
    rw [p1] at h
    exact hm (eq_zero_of_pow_sub hdeg (by linear_combination h))
  · intro l l' hne
    refine pair_index χ cc hcc hunit hne l.1 l'.1 (fun a => ?_)
    have h := hcoef a (Finsupp.single l 1 + Finsupp.single l' 1)
    rw [prod_pair, prod_pair, prod_pair] at h
    simp only [map_add (f := _), map_one, map_mul] at h
    linear_combination h

end ReciprocityTheory.ChartRestriction.G.TB.GRPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAdd
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

theorem exp_factor {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type} (f : MvPowerSeries σ k)
    (hf : constantCoeff f = 0) :
    ∃ Y : MvPowerSeries σ k, PowerSeries.subst f (PowerSeries.exp k) = 1 + f * Y := by
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf

  set E : PowerSeries k := PowerSeries.mk fun n => algebraMap ℚ k (1 / ((n + 1).factorial : ℚ)) with hE
  have hexp : PowerSeries.exp k = 1 + PowerSeries.X * E := by
    ext n
    rcases n with _ | n
    · simp [PowerSeries.coeff_exp]
    · simp [PowerSeries.coeff_exp, hE, PowerSeries.coeff_succ_X_mul]
  refine ⟨PowerSeries.subst f E, ?_⟩
  rw [hexp, ← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, map_mul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]

end ReciprocityTheory.ChartRestriction.G.TB.G2

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dAdd_add (u : Fin d → k) (b : Fin n) (f g : PS k n d) : dAdd u b (f + g) = dAdd u b f + dAdd u b g := by
  simp only [dAdd, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem dAdd_C (u : Fin d → k) (b : Fin n) (a : k) : dAdd u b (C a : PS k n d) = 0 := by
  unfold dAdd
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (C a : PS k n d) = algebraMap k (PS k n d) a from rfl, Derivation.map_algebraMap, mul_zero]

theorem dAdd_mul (u : Fin d → k) (b : Fin n) (f g : PS k n d) :
    dAdd u b (f * g) = dAdd u b f * g + f * dAdd u b g := by
  unfold dAdd
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem killAdd_of (hQ : QuadColDerivSt) : KillAddSt := by
  intro k _ _ d n ι _ u β P hP m g
  obtain ⟨h0, h1, h2⟩ := hQ k d n β
  obtain ⟨Y, hY⟩ := exp_factor (m • quadCol (n := n) β) (by simp [h0])
  have key := Gen.kill_gen (D := fun p : ι × Fin n => dAdd (u p.1) p.2) (κ := (C : k →+* PS k n d))
    (fun l f g => dAdd_add (u l.1) l.2 f g) (fun l a => dAdd_C (u l.1) l.2 a)
    (fun l f g => dAdd_mul (u l.1) l.2 f g) constantCoeff (fun a => by simp)
    (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0)
    (quadCol (n := n) β)
    (fun l l' => by
      by_cases h : l.2 = l'.2
      · rw [if_pos h, if_pos h.symm, add_comm]
      · rw [if_neg h, if_neg (Ne.symm h)])
    h0 (fun l => h1 (u l.1) l.2) (fun l l' => h2 (u l.1) (u l'.1) l.2 l'.2) P hP g (m • Y)
  have e : FB.expS k (m • quadCol (n := n) β) * g = g * (1 + quadCol (n := n) β * (m • Y)) := by
    rw [FB.expS, hY, mul_comm, smul_mul_assoc, mul_smul_comm]
  rw [e]
  exact key

end ReciprocityTheory.ChartRestriction.G.TB
end
end

