module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0005
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0009

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XBirat
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.birat

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hom_mul {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k, Pi.add_apply]

theorem hom_add {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem hom_neg {f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (-f) a := by
  intro m hm k
  rw [support_neg] at hm
  exact hf m hm k

theorem hom_one : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hm
    exact hm rfl
  subst this
  simp

theorem hom_X (k : K) (i j : ι k) : ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) a ∧
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) a := by
  classical
  have key : ∀ i : ι k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)
      (fun k' => if k = k' then 1 else 0) := by
    intro i m hm k'
    rw [support_X, Finset.mem_singleton] at hm
    subst hm
    by_cases h : k = k'
    · subst h
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, h]
  exact ⟨_, key i, key j⟩

theorem ratio {Ω : Type} [Field Ω] (r : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, r ⟨k, c k⟩ = 1) (s : Ω)
    (hs : s ∈ Subfield.closure (Set.range r)) :
    ∃ (d : K → ℕ) (g h : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧ aeval r h ≠ 0 ∧ aeval r g = s * aeval r h := by
  induction hs using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    obtain ⟨a, h1, h2⟩ := hom_X k i (c k)
    exact ⟨a, _, _, h1, h2, by simp [hc], by simp [hc]⟩
  | one => exact ⟨0, 1, 1, hom_one, hom_one, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    obtain ⟨d', g', h', b1, b2, b3, b4⟩ := hy
    refine ⟨d + d', g * h' + h * g', h * h', hom_add (hom_mul a1 b2) (hom_mul a2 b1), hom_mul a2 b2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero a3 b3
    · rw [map_add (f := _), map_mul, map_mul, map_mul, a4, b4]; ring
  | neg x _ hx =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    exact ⟨d, -g, h, hom_neg a1, a2, a3, by rw [map_neg, a4]; ring⟩
  | inv x _ hx =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    by_cases h0 : x = 0
    · exact ⟨d, g, h, a1, a2, a3, by rw [a4, h0, inv_zero]⟩
    · exact ⟨d, h, g, a2, a1, by rw [a4]; exact mul_ne_zero h0 a3, by rw [a4, inv_mul_cancel_left₀ h0]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    obtain ⟨d', g', h', b1, b2, b3, b4⟩ := hy
    refine ⟨d + d', g * g', h * h', hom_mul a1 b1, hom_mul a2 b2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero a3 b3
    · rw [map_mul, map_mul, a4, b4]; ring

end PositivityTheory.Xgp.birat

open PositivityTheory.Xgp.birat in
theorem PositivityTheory.Xgp.t_birat : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∃ (Ω' : Type) (_ : Field Ω') (y' : (Σ k, ι k) → Ω'), mCoordIdeal y' = mCoordIdeal y ∧ Birational y' := by
  intro K _ ι _ Ω _ y hy
  choose c hc using hy
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  let F : Subfield Ω := Subfield.closure (Set.range r)
  let y' : (Σ k, ι k) → F := fun p => ⟨r p, Subfield.subset_closure ⟨p, rfl⟩⟩
  have hev : ∀ g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι, ((aeval y' g : F) : Ω) = aeval r g := fun g => by
    have : (F.subtype.toIntAlgHom).comp (aeval y') = aeval r := by
      ext p
      simp [y']
    exact AlgHom.congr_fun this g
  refine ⟨F, inferInstance, y', ?_, fun s => ?_⟩
  · let θ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩) * X k
    let θ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k
    have hθ : θ'.comp θ = AlgHom.id Ω _ := by
      refine MvPolynomial.algHom_ext fun k => ?_
      simp only [θ, θ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
    have hθi : Function.Injective θ := Function.LeftInverse.injective (g := θ') (AlgHom.congr_fun hθ)
    let ψ : MvPolynomial K F →+* MvPolynomial K Ω := θ.toRingHom.comp (MvPolynomial.map F.subtype)
    have hψ : Function.Injective ψ := hθi.comp (MvPolynomial.map_injective _ F.subtype.injective)
    have e : ψ.comp (mConeMap y').toRingHom = (mConeMap y).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
      have e1 : mConeMap y' (X p) = C (y' p) * X p.1 := aeval_X _ p
      have e2 : mConeMap y (X p) = C (y p) * X p.1 := aeval_X _ p
      show θ (MvPolynomial.map F.subtype (mConeMap y' (X p))) = mConeMap y (X p)
      rw [e1, e2]
      simp only [θ, map_mul, map_C, map_X, aeval_X, aeval_C, algebraMap_eq]
      rw [← mul_assoc, ← C_mul]
      congr 2
      exact div_mul_cancel₀ _ (hc _)
    ext g
    show mConeMap y' g = 0 ↔ mConeMap y g = 0
    rw [show mConeMap y g = ψ (mConeMap y' g) from (RingHom.congr_fun e g).symm]
    exact (map_eq_zero_iff ψ hψ).symm
  · obtain ⟨d, g, h, a1, a2, a3, a4⟩ := ratio r c (fun k => div_self (hc k)) s.1 s.2
    refine ⟨d, g, h, a1, a2, fun h0 => a3 (by rw [← hev, h0]; rfl), Subtype.ext ?_⟩
    rw [Subfield.coe_mul, hev, hev, a4]
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibStereo
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_stereo

open MeasureTheory Set
open scoped ENNReal NNReal

theorem measure_part (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    (Integrable (fun a : ℂ => f (nF a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
      Integrable (fun m : ReciprocityTheory.ChartRestriction.G.AI.S2 => f fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i)
        ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧
    ∫ a : ℂ, f (nF a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) =
      ∫ m : ReciprocityTheory.ChartRestriction.G.AI.S2, f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i)
        ∂ ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure := by
  set gE : GroundTheory.Heights₂.Heights.FlagBundles.E3 → ℝ := fun x => f (fun i => x i) with hgE
  have hgm : Measurable gE :=
    hf.comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
  set w : ℂ → ℝ≥0 := fun a => Real.toNNReal (wt a) with hw
  have hwm : Measurable w := Measurable.real_toNNReal (by unfold wt; fun_prop)
  have hmap : (volume.withDensity fun a : ℂ => (w a : ℝ≥0∞)).map nE =
      GroundTheory.Heights₂.Heights.FlagBundles.sphereMeasure.map
        (fun m : GroundTheory.Heights₂.Heights.FlagBundles.Sphere2 => (m : GroundTheory.Heights₂.Heights.FlagBundles.E3)) :=
    map_stereo
  have hpt : (fun a : ℂ => f (nF a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) =
      fun a => w a • gE (nE a) := by
    funext a
    have hnn : 0 ≤ wt a := by unfold wt; positivity
    rw [NNReal.smul_def, smul_eq_mul, hw, Real.coe_toNNReal _ hnn]
    show f (nF a) * _ = wt a * f (nF a)
    unfold wt
    ring
  have hnE := measurable_nE.aemeasurable (μ := volume.withDensity fun a : ℂ => (w a : ℝ≥0∞))
  have hco : AEMeasurable (fun m : GroundTheory.Heights₂.Heights.FlagBundles.Sphere2 =>
      (m : GroundTheory.Heights₂.Heights.FlagBundles.E3)) GroundTheory.Heights₂.Heights.FlagBundles.sphereMeasure :=
    measurable_subtype_coe.aemeasurable
  constructor
  · rw [hpt, ← integrable_withDensity_iff_integrable_smul₀ hwm.aemeasurable]
    refine (integrable_map_measure (g := gE) hgm.aestronglyMeasurable hnE).symm.trans ?_
    rw [hmap]
    exact integrable_map_measure hgm.aestronglyMeasurable hco
  · rw [hpt, ← integral_withDensity_eq_integral_smul hwm]
    refine (integral_map hnE hgm.aestronglyMeasurable).symm.trans ?_
    rw [hmap]
    exact integral_map hco hgm.aestronglyMeasurable

theorem logSin_part (a₀ a₁ : ℂ) :
    logSin 1 a₀ a₁ = (1 / 2) * Real.log ((1 - ∑ i, nF a₀ i * nF a₁ i) / 2) := by
  have hN : ∀ u : ℂ, ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := fun u => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e1 : ∀ u v : ℂ, herm2 1 ![1, u] ![1, v] = 1 + (starRingEnd ℂ) u * v := by
    intro u v
    simp [herm2, dotProduct, Fin.sum_univ_two]
  have e2 : ∀ u : ℂ, (herm2 1 ![1, u] ![1, u]).re = 1 + (u.re ^ 2 + u.im ^ 2) := by
    intro u
    rw [e1]
    simp [Complex.mul_re]
    ring
  have e3 : ‖herm2 1 ![1, a₀] ![1, a₁]‖ ^ 2 =
      (1 + (a₀.re * a₁.re + a₀.im * a₁.im)) ^ 2 + (a₀.re * a₁.im - a₀.im * a₁.re) ^ 2 := by
    rw [e1, hN]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hs : ∑ i, nF a₀ i * nF a₁ i =
      (2 * a₀.re / (1 + ‖a₀‖ ^ 2)) * (2 * a₁.re / (1 + ‖a₁‖ ^ 2)) +
      (2 * a₀.im / (1 + ‖a₀‖ ^ 2)) * (2 * a₁.im / (1 + ‖a₁‖ ^ 2)) +
      ((1 - ‖a₀‖ ^ 2) / (1 + ‖a₀‖ ^ 2)) * ((1 - ‖a₁‖ ^ 2) / (1 + ‖a₁‖ ^ 2)) := by
    rw [Fin.sum_univ_three]
    rfl
  unfold logSin
  rw [e2, e2, e3, hs, hN, hN]
  congr 2
  have p0 : (0 : ℝ) < 1 + (a₀.re ^ 2 + a₀.im ^ 2) := by positivity
  have p1 : (0 : ℝ) < 1 + (a₁.re ^ 2 + a₁.im ^ 2) := by positivity
  field_simp
  ring

end PositivityTheory.Xgp.fib_stereo
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolSec
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_pol_sec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 := by
  intro K _ ι _ Ω _ y α dβ hy hex
  obtain ⟨k, hk, e, he, hne⟩ := hex
  choose i hi using hy
  set D := ∑ κ, dβ κ with hDdef
  have hD : ∀ κ, dβ κ ≤ D := fun κ =>
    Finset.single_le_sum (f := dβ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)
  refine ⟨(D + 1) * k, le_trans hk (Nat.le_mul_of_pos_left k (Nat.succ_pos D)),
    e ^ (D + 1) * ∏ κ, y ⟨κ, i κ⟩ ^ (D - dβ κ), ?_, ?_⟩
  · intro c hc
    have h1 := he c hc
    have key : e ^ (D + 1) * (∏ κ, y ⟨κ, i κ⟩ ^ (D - dβ κ)) *
        ∏ κ, y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((((D + 1) * k : ℕ) : ℤ) * α κ - 1 - (dβ κ : ℤ))))
        = (e * ∏ κ, y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)))) ^ (D + 1) *
          ∏ κ, (y ⟨κ, i κ⟩ / y ⟨κ, c κ⟩) ^ (D - dβ κ) := by
      rw [mul_pow, ← Finset.prod_pow, mul_assoc, mul_assoc]
      congr 1
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun κ _ => ?_)
      have hyc : y ⟨κ, c κ⟩ ≠ 0 := hc κ
      rw [div_pow, ← zpow_natCast (y ⟨κ, c κ⟩) (D - dβ κ),
        ← zpow_natCast (y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)))) (D + 1), ← zpow_mul]
      have hexp : -(((1 : ℕ) : ℤ) * ((((D + 1) * k : ℕ) : ℤ) * α κ - 1 - (dβ κ : ℤ)))
          = -(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)) * ((D + 1 : ℕ) : ℤ) - ((D - dβ κ : ℕ) : ℤ) := by
        rw [Nat.cast_sub (hD κ)]
        push_cast
        ring
      rw [hexp, zpow_sub₀ hyc]
      ring
    rw [key]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ h1 _) (Subalgebra.prod_mem _ (fun κ _ => ?_))
    refine Subalgebra.pow_mem _ ?_ _
    unfold chartRingZ
    exact Algebra.subset_adjoin (Set.mem_range.2 ⟨⟨κ, i κ⟩, rfl⟩)
  · exact mul_ne_zero (pow_ne_zero _ hne)
      (Finset.prod_ne_zero_iff.2 fun κ _ => pow_ne_zero _ (hi κ))
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XReComb
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

private theorem isSmoothHerm_combLine' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type}
    [Fintype σ] (A : σ → HermLine ι) (hA : ∀ a, IsSmoothHerm (A a)) (d : σ → ℤ) :
    IsSmoothHerm (combLine A d) := by
  classical
  unfold IsSmoothHerm
  have hfun : (combLine A d).h = fun z => ∏ x : σ, (A x).h z ^ d x := funext (combLine_h A d)
  rw [hfun]
  apply contDiffOn_prod
  intro x _
  rcases Int.eq_nat_or_neg (d x) with ⟨m, hm | hm⟩
  · simp_rw [hm, zpow_natCast]
    exact (hA x).pow m
  · simp_rw [hm, zpow_neg, zpow_natCast]
    exact ((hA x).pow m).inv (fun z hz => pow_ne_zero _ ((A x).pos z hz).ne')

private theorem II_update_combLine (hML : MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι)
    (hA : ∀ a, IsSmoothHerm (A a)) (hP : IsArithVar P n) (L : Fin n → HermLine ι)
    (hL : ∀ r, IsSmoothHerm (L r)) (j : Fin n) (d : σ → ℤ) :
    II K ι P n (Function.update L j (combLine A d)) =
      ∑ a, (d a : ℝ) * II K ι P n (Function.update L j (A a)) := by
  classical
  have hsm : ∀ (M : HermLine ι), IsSmoothHerm M → ∀ r, IsSmoothHerm (Function.update L j M r) := by
    intro M hM r
    by_cases h : r = j
    · subst h
      simpa using hM
    · simpa [Function.update_of_ne h] using hL r
  have hloc : ∀ M M' : HermLine ι, IsSmoothHerm M → IsSmoothHerm M' → M.a = M'.a →
      (∀ z ∈ mcPts P, M.h z = M'.h z) →
      II K ι P n (Function.update L j M) = II K ι P n (Function.update L j M') := by
    intro M M' hM hM' ha hh
    apply hML K ι (II K ι) (hII.1 K ι) P n _ _ hP (hsm M hM) (hsm M' hM')
    · intro r
      by_cases h : r = j
      · subst h
        simp [ha]
      · simp [Function.update_of_ne h]
    · intro r z hz
      by_cases h : r = j
      · subst h
        simpa using hh z hz
      · simp [Function.update_of_ne h]
  let G : (σ → ℤ) → ℝ := fun d => II K ι P n (Function.update L j (combLine A d))
  have hadd : ∀ d d', G (d + d') = G d + G d' := by
    intro d d'
    have h1 : G (d + d') =
        II K ι P n (Function.update L j ((combLine A d).tensor (combLine A d'))) := by
      apply hloc _ _ (isSmoothHerm_combLine' A hA _)
        (by unfold IsSmoothHerm; exact (isSmoothHerm_combLine' A hA d).mul (isSmoothHerm_combLine' A hA d'))
      · funext k
        show (combLine A (d + d')).a k = (combLine A d).a k + (combLine A d').a k
        rw [combLine_a, combLine_a, combLine_a, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Pi.add_apply]
        ring
      · intro z hz
        show (combLine A (d + d')).h z = (combLine A d).h z * (combLine A d').h z
        rw [combLine_h, combLine_h, combLine_h, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x _ => ?_
        exact zpow_add₀ ((A x).pos z hz.1).ne' _ _
    rw [h1]
    exact hII.2.1 K ι P n L j _ _ hP hL (isSmoothHerm_combLine' A hA d) (isSmoothHerm_combLine' A hA d')
  have hsingle : ∀ a, G (Pi.single a 1) = II K ι P n (Function.update L j (A a)) := by
    intro a
    apply hloc _ _ (isSmoothHerm_combLine' A hA _) (hA a)
    · funext k
      rw [combLine_a]
      simp [Pi.single_apply]
    · intro z _
      rw [combLine_h, Finset.prod_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
  let Gh : (σ → ℤ) →+ ℝ := AddMonoidHom.mk' G hadd
  have hd : d = ∑ a, d a • Pi.single a (1 : ℤ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  show G d = _
  calc G d = Gh d := rfl
    _ = Gh (∑ a, d a • Pi.single a (1 : ℤ)) := by rw [← hd]
    _ = ∑ a, (d a : ℝ) * G (Pi.single a 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_zsmul, zsmul_eq_mul]
      rfl
    _ = _ := by simp_rw [hsingle]

private theorem II_combLine_eq_polar (hML : MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ)
    (hP : IsArithVar P n) (hA : ∀ a, IsSmoothHerm (A a)) :
    II K ι P n (fun r => combLine A (c r)) =
      polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  classical
  unfold polar
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨a0⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      congr 1
      funext r
      exact r.elim0
    · obtain ⟨j⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      haveI : IsEmpty (Fin n → σ) := ⟨fun w => hσ.elim (w j)⟩
      have e : (fun r => combLine A (c r)) =
          Function.update (fun r => combLine A (c r)) j (combLine A (c j)) := by simp
      rw [e, II_update_combLine hML II hII K ι σ P n A hA hP _ (fun r => isSmoothHerm_combLine' A hA (c r)) j (c j)]
      simp [Finset.univ_eq_empty]
  · let t : Finset (Fin n) → Fin n → Finset σ := fun S r => if r ∈ S then Finset.univ else {a0}
    let line : Finset (Fin n) → (Fin n → σ) → Fin n → HermLine ι :=
      fun S w r => if r ∈ S then A (w r) else combLine A (c r)
    have hsm : ∀ S w r, IsSmoothHerm (line S w r) := by
      intro S w r
      simp only [line]
      split_ifs
      · exact hA _
      · exact isSmoothHerm_combLine' A hA _
    have key : ∀ S : Finset (Fin n), II K ι P n (fun r => combLine A (c r)) =
        ∑ w ∈ Fintype.piFinset (t S), (∏ r ∈ S, (c r (w r) : ℝ)) * II K ι P n (line S w) := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · have h0 : Fintype.piFinset (t ∅) = {fun _ => a0} := by
          ext w
          simp [t, Fintype.mem_piFinset, funext_iff]
        rw [h0, Finset.sum_singleton]
        simp [line]
      · intro j S hj ih
        rw [ih]
        have hexp : ∀ w ∈ Fintype.piFinset (t S),
            (∏ r ∈ S, (c r (w r) : ℝ)) * II K ι P n (line S w) =
              ∑ a, (∏ r ∈ insert j S, (c r (Function.update w j a r) : ℝ)) *
                II K ι P n (line (insert j S) (Function.update w j a)) := by
          intro w _
          have hl : line S w = Function.update (line S w) j (combLine A (c j)) := by
            funext r
            by_cases h : r = j
            · subst h
              simp [line, hj]
            · simp [Function.update_of_ne h]
          rw [hl, II_update_combLine hML II hII K ι σ P n A hA hP _ (hsm S w) j (c j), Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          have hupd : Function.update (line S w) j (A a) = line (insert j S) (Function.update w j a) := by
            funext r
            by_cases h : r = j
            · subst h
              simp [line]
            · simp [line, Function.update_of_ne h, Finset.mem_insert, h]
          rw [hupd, Finset.prod_insert hj, Function.update_self]
          have hprod : ∏ r ∈ S, (c r (Function.update w j a r) : ℝ) = ∏ r ∈ S, (c r (w r) : ℝ) :=
            Finset.prod_congr rfl fun r hr => by
              have hrj : r ≠ j := fun h => hj (h ▸ hr)
              rw [Function.update_of_ne hrj]
          rw [hprod]
          ring
        rw [Finset.sum_congr rfl hexp, ← Finset.sum_product']
        apply Finset.sum_nbij' (fun p => Function.update p.1 j p.2) (fun w => (Function.update w j a0, w j))
        · rintro ⟨w, a⟩ hp
          simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
          intro r
          by_cases h : r = j
          · subst h
            simp [t]
          · rw [Function.update_of_ne h]
            have := hp.1 r
            simpa [t, Finset.mem_insert, h] using this
        · intro w hw
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true, Fintype.mem_piFinset] at hw ⊢
          intro r
          by_cases h : r = j
          · subst h
            simp [t, hj]
          · rw [Function.update_of_ne h]
            have := hw r
            simpa [t, Finset.mem_insert, h] using this
        · rintro ⟨w, a⟩ hp
          simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp
          have hwj : w j = a0 := by simpa [t, hj] using hp.1 j
          simp [Function.update_idem, ← hwj]
        · intro w _
          simp [Function.update_idem]
        · intro p _
          rfl
    rw [key Finset.univ]
    have hu : Fintype.piFinset (t Finset.univ) = Finset.univ := by
      ext w
      simp [t]
    rw [hu]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [line]

theorem PositivityTheory.Xgp.t_re_comb : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  intro hML II hII K _ ι _ σ _ P n A c hP hA
  exact ⟨fun r => isSmoothHerm_combLine' A hA (c r), II_combLine_eq_polar hML II hII K ι σ P n A c hP hA⟩
end

