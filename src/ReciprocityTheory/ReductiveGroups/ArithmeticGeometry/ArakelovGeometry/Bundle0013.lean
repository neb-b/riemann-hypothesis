module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0012
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0010
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.SupStMonoNormSqPos

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem det_interp (M₀ M₁ : Matrix (Fin D) (Fin D) ℂ) (t : ℂ) :
    ((1 - t) • M₀ + t • M₁).det = ∑ i ∈ Finset.range (D + 1),
      (D.choose i : ℂ) * t ^ i * (1 - t) ^ (D - i) *
        mixedDisc (fun j : Fin D => if j.val < i then M₁ else M₀) := by
  rw [add_comm]
  exact ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc t (1 - t) M₁ M₀

theorem gaamix_cxHessian_comb {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (s u : ℝ)
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => s * a y' + u * b y') :
    cxHessian ψ y = (s : ℂ) • cxHessian a y + (u : ℂ) • cxHessian b y := by
  have hd : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => s • fderiv ℝ a y' + u • fderiv ℝ b y' := by
    filter_upwards [hψ.eventuallyEq_nhds, ha, hb] with y' h1 h2 h3
    rw [h1.fderiv_eq]
    have d2 := h2.differentiableAt (by norm_num)
    have d3 := h3.differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_mul s).add (d3.hasFDerivAt.const_mul u)).fderiv
  have hH : fderiv ℝ (fderiv ℝ ψ) y =
      s • fderiv ℝ (fderiv ℝ a) y + u • fderiv ℝ (fderiv ℝ b) y := by
    rw [hd.fderiv_eq]
    have d2 := (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have d3 := (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_smul s).add (d3.hasFDerivAt.const_smul u)).fderiv
  ext i j
  simp only [cxHessian, hH, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  push_cast
  ring

theorem gaamix_ne_zero_of_mcPts {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} (hz : z ∈ mcPts P) :
    z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz.1 ()
  rintro rfl
  exact hi rfl

theorem gaamix_contDiffAt_log {m : ConeMetric (C := ℂ) (ι := Ix κ)} (hm : IsSmoothMetric m)
    {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : γ y ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (m.ρ (γ y'))) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ m.ρ (γ y) :=
    hm.contDiffAt (isOpen_ne.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp ((hρ.comp y hc).log (m.pos _ hy).ne')) 2

theorem gaamix_log_interp (m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)) (t : ℝ) {z : Ix κ → ℂ} (hz : z ≠ 0) :
    Real.log ((interp m₀ m₁ t).ρ z) = (1 - t) * Real.log (m₀.ρ z) + t * Real.log (m₁.ρ z) := by
  have h₀ := m₀.pos z hz
  have h₁ := m₁.pos z hz
  show Real.log (m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) = _
  rw [Real.log_mul (Real.rpow_pos_of_pos h₀ _).ne' (Real.rpow_pos_of_pos h₁ _).ne',
    Real.log_rpow h₀, Real.log_rpow h₁]

theorem gbamix_maDensity_interp {m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) (t : ℝ) {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0) :
    maDensity (fun j y' => purePot (interp m₀ m₁ t) D j (γ y')) y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        maDensity (fun j y' => mixPot m₀ m₁ D i j (γ y')) y := by
  have hev : ∀ᶠ y' in 𝓝 y, ∀ᶠ y'' in 𝓝 y', DifferentiableAt ℂ γ y'' ∧ γ y'' ≠ 0 :=
    hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₀.ρ (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact gaamix_contDiffAt_log h₀ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (m₁.ρ (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact gaamix_contDiffAt_log h₁ (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) =ᶠ[𝓝 y]
      fun y' => (1 - t) * Real.log (m₀.ρ (γ y')) + t * Real.log (m₁.ρ (γ y')) := by
    filter_upwards [hγ] with y' hy'
    exact gaamix_log_interp m₀ m₁ t hy'.2
  have hH := gaamix_cxHessian_comb (1 - t) t ha hb hψ
  set H₀ := cxHessian (fun y'' => Real.log (m₀.ρ (γ y''))) y
  set H₁ := cxHessian (fun y'' => Real.log (m₁.ρ (γ y''))) y
  have hmix : ∀ i, (fun k => cxHessian (fun y' => mixPot m₀ m₁ D i k (γ y')) y) =
      fun j : Fin D => if j.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [mixPot, hk, if_true]; rfl
    · simp only [mixPot, hk, if_false]; rfl
  have hpure : (fun k => cxHessian (fun y' => purePot (interp m₀ m₁ t) D k (γ y')) y) =
      fun _ => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁ := by
    funext k
    show cxHessian (fun y' => Real.log ((interp m₀ m₁ t).ρ (γ y'))) y = _
    rw [hH]
    push_cast
    rfl
  simp only [maDensity]
  have hc : mixedDisc (fun _ : Fin D => (1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁) =
      ((1 - (t : ℂ)) • H₀ + (t : ℂ) • H₁).det := ReciprocityTheory.AnForm.A.mdisc_const _
  rw [hpure, hc, det_interp, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem gbamix_ne_zero_of_blocks {z : Ix κ → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz ()
  rintro rfl
  exact hi rfl

theorem gbamix_smoothHerm_ofCone {m : ConeMetric (C := ℂ) (ι := Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  exact (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0} from hm).mono
    fun z hz => gbamix_ne_zero_of_blocks hz

theorem gbamix_logRatio_deg {m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)} (c : Unit → ℂ) (z : Ix κ → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio m₀ m₁ (fun p => c p.1 * z p) = logRatio m₀ m₁ z := by
  have e : (fun p : Ix κ => c p.1 * z p) = c () • z := by
    funext p
    rfl
  unfold logRatio
  rw [e, m₀.smul, m₁.smul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 (hc ()))]

theorem gbamix_smooth_logRatio {m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio m₀ m₁) {z | z ≠ 0} := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀.ρ {z | z ≠ 0} := h₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁.ρ {z | z ≠ 0} := h₁
  show ContDiffOn ℝ _ (fun z => Real.log (m₁.ρ z / m₀.ρ z)) {z | z ≠ 0}
  exact (h1.div h0 fun z hz => (m₀.pos z hz).ne').log fun z hz =>
    (div_pos (m₁.pos z hz) (m₀.pos z hz)).ne'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem eval_smul_of_isHomogeneous {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : ℂ) (z : ι → ℂ) :
    eval (c • z) φ = c ^ n * eval z φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = n := by
    have h := hφ (mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem smul_mem_pts_coord {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩
  have hH := coordIdeal_isHomogIdeal ℤ x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous ((homogeneousComponent_isHomogeneous d f).map _),
    hz.2 _ (hH f hf d), mul_zero]

theorem dense_eval_ne_zero {N : ℕ} {Δ : MvPolynomial (Fin N) ℂ} (hΔ : Δ ≠ 0) :
    Dense {w | eval w Δ ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨w, hw⟩
  by_contra hne
  apply hΔ
  have h0 : ∀ v ∈ U, eval v Δ = 0 := fun v hv => by
    by_contra h
    exact hne ⟨v, hv, h⟩
  have han : AnalyticOnNhd ℂ (fun v => eval v Δ) Set.univ := AnalyticOnNhd.eval_mvPolynomial Δ
  have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ w) (Filter.eventually_of_mem (hU.mem_nhds hw) h0)
  exact MvPolynomial.funext fun v => by simpa using hz (Set.mem_univ v)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HasympAll
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem main_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (hSW : SymmAt (m + 1) W)
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W') :
    HAsymp L (m + 1) W := by
  have hblock (b : K) := block_step (L := L) hp hW hpW hdim hR4W IH b
  choose a0 C hC hb using hblock
  set a₁ := 1 + ∑ b, a0 b
  set Δ : (K → ℕ) → ℝ := fun a => lg W a - appr L (m + 1) W a with hΔ
  set B := coefB (m + 1) W
  have hB : 0 ≤ B := coefB_nonneg _ _
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  set Kst := ∑ b, C b + |L| * B * 2 ^ (m - 1) / m.factorial
  have hKst : 0 ≤ Kst := by
    have := Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => hC b
    positivity
  have hstep : ∀ a : K → ℕ, ∀ b, (∀ k, a₁ ≤ a k) → a₁ < a b →
      |Δ a - Δ (a - Pi.single b 1)| ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
    intro a b ha hab
    have ha0 : ∀ k, a0 b ≤ a k := fun k => by
      have h1 : a0 b ≤ ∑ b, a0 b := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
      have := ha k
      omega
    have h1 := hb b a ha0
    set x : K → ℤ := fun k => (a k : ℤ)
    have hx : (fun _ : Fin (m + 1) => fun k => ((a - (Pi.single b 1 : K → ℕ)) k : ℤ)) =
        fun _ => x - uv b := by
      funext _ k
      by_cases hk : k = b
      · subst hk
        have : 1 ≤ a k := by omega
        simp [x, uv, Nat.cast_sub this]
      · simp [x, uv, Pi.single_apply, hk]
    have h2 := geoNum_diff_est m W hSW x b
    rw [show nrm x = tdeg a from nrm_natCast a] at h2
    have hfs : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hid : Δ a - Δ (a - Pi.single b 1) =
        (lg W a - lg W (a - Pi.single b 1) -
          L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial) -
        L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))) := by
      simp only [hΔ, appr]
      rw [hx, hfs]
      field_simp
      ring
    have h3 : |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
          geoNum (m + 1) W (fun _ => x - uv b) -
          (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| ≤
        |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m + 1).factorial : ℝ)), hfs]
      have hN : (0 : ℝ) ≤ tdeg a := by positivity
      have h4 : ((tdeg a : ℝ) + 2) ^ (m + 1 - 2) ≤ 2 ^ (m - 1) * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
        rw [show m + 1 - 2 = m - 1 by omega, ← mul_pow]
        gcongr
        linarith
      calc |L| / ((m + 1) * m.factorial) * |(geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b))|
          ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * ((tdeg a : ℝ) + 2) ^ (m + 1 - 2))) := by
            gcongr
        _ ≤ |L| / ((m + 1) * m.factorial) * (B * ((m + 1) * m * (2 ^ (m - 1) *
              ((tdeg a : ℝ) + 1) ^ (m - 1)))) := by
            gcongr
        _ = |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
            field_simp
    have hCb : C b ≤ ∑ b, C b := Finset.single_le_sum (f := C) (fun b _ => hC b) (Finset.mem_univ b)
    rw [hid]
    calc _ ≤ |lg W a - lg W (a - Pi.single b 1) -
            L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial| +
          |L / ((m + 1).factorial : ℝ) * ((geoNum (m + 1) W (fun _ => x) : ℝ) -
            geoNum (m + 1) W (fun _ => x - uv b) -
            (m + 1) * geoNum (m + 1) W (Fin.snoc (fun _ => x) (uv b)))| := abs_sub _ _
      _ ≤ C b * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := add_le_add h1 h3
      _ ≤ (∑ b, C b) * m * ((tdeg a : ℝ) + 1) ^ (m - 1) +
          |L| * B * 2 ^ (m - 1) / m.factorial * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by gcongr
      _ = Kst * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by ring
  have hw := walk_bound Δ a₁ m hKst hstep
  refine ⟨a₁, |Δ (fun _ => a₁)| + Kst * m, by positivity, fun a ha => ?_⟩
  have h := hw a ha
  have hN : (0 : ℝ) ≤ tdeg a := by positivity
  have hp1 : (1 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ m := one_le_pow₀ (by linarith)
  have hkey : Kst * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) ≤ Kst * m * ((tdeg a : ℝ) + 1) ^ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have : ((tdeg a : ℝ) + 1) ^ m = ((tdeg a : ℝ) + 1) ^ (m - 1) * ((tdeg a : ℝ) + 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [this]
      have : (0 : ℝ) ≤ ((tdeg a : ℝ) + 1) ^ (m - 1) := by positivity
      have : (0 : ℝ) ≤ Kst * m := by positivity
      nlinarith
  simp only [Nat.add_sub_cancel]
  push_cast
  have hΔc := abs_nonneg (Δ (fun _ => a₁))
  have hKm : (0 : ℝ) ≤ Kst * m := by positivity
  change |Δ a| ≤ _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hA : (1 : ℝ) ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by nlinarith
  have hB1 : |Δ (fun _ => a₁)| ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) :=
    le_mul_of_one_le_right hΔc hA
  have hB2 : Kst * m * ((tdeg a : ℝ) + 1) ^ m ≤
      Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by
    have : ((tdeg a : ℝ) + 1) ^ m ≤ ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left this hKm
  calc |Δ a| ≤ |Δ (fun _ => a₁)| + Kst * m * ((tdeg a : ℝ) + 1) ^ m := by linarith
    _ ≤ |Δ (fun _ => a₁)| * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) +
        Kst * m * (((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m) := by linarith
    _ = (|Δ (fun _ => a₁)| + Kst * m) * ((m : ℝ) + 1) * ((tdeg a : ℝ) + 1) ^ m := by ring

theorem hasymp_all {L : ℝ} {p : ℕ} (hp : p.Prime)
    (hR4 : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ) (k : K) (i : ι k),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
      (X ⟨k, i⟩ : MRing ι) ∉ V →
      (a (Fin.last n) = fun k' => if k' = k then 1 else 0) →
      geoNum (n + 1) V a = ∑ᶠ W' ∈ divSupp V (X ⟨k, i⟩),
        (multAt (V ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum n W' (Fin.init a))
    (hSymm : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)),
      IsMultiProjPrime V → charOf V ≠ 0 →
      ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
      geoNum n V (a ∘ σ) = geoNum n V a)
    (hbase : ∀ W : Ideal (MRing ι), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) → HAsymp L 0 W) :
    ∀ (d : ℕ) (W : Ideal (MRing ι)), IsMultiProjPrime W → (p : MRing ι) ∈ W →
      ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L d W ∧ SymmAt d W := by
  intro d
  induction d with
  | zero =>
    intro W hW hpW hdim
    exact ⟨hbase W hW hpW hdim,
      fun a σ => hSymm 0 W a σ hW (charOf_ne_zero_of_mem hp.ne_zero hpW) hdim⟩
  | succ m ih =>
    intro W hW hpW hdim
    have hc := charOf_ne_zero_of_mem hp.ne_zero hpW
    have hS : SymmAt (m + 1) W := fun a σ => hSymm (m + 1) W a σ hW hc hdim
    exact ⟨main_step hp hW hpW hdim (fun a k i hX ha => hR4 m W a k i hW hc hdim hX ha) hS
      (fun W' hW' hpW' hdim' => ih W' hW' hpW' hdim'), hS⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

