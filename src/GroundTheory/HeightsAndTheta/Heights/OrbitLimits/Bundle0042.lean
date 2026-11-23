module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MemMCoordIdealIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section

namespace CurveVerticalPointSurjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ringHom_aeval {A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] (f : A →+* A')
    (z : (Σ k, ι k) → A) (g : MRing ι) : f (aeval z g) = aeval (fun p => f (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; rw [eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap_homog y hg, mul_eq_zero, C_eq_zero]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) (h : aeval y f = aeval y g) :
    f - g ∈ mCoordIdeal y := by
  rw [mem_mCoordIdeal_iff y (homog_sub hf hg), map_sub, h, sub_self]


omit [Fintype K] in
theorem homogD {f : MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (h : a = b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b :=
  h ▸ hf


omit [∀ k, Fintype (ι k)] in
theorem prod_pow_add {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e₁ e₂ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e₁ + e₂) k = (∏ k, y ⟨k, c k⟩ ^ e₁ k) * ∏ k, y ⟨k, c k⟩ ^ e₂ k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]


omit [∀ k, Fintype (ι k)] in
theorem chartMon_notMem {Q : Ideal (MRing ι)} (hQ : Q.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ Q) (n : K → ℕ) : chartMon c n ∉ Q := by
  intro h
  rw [chartMon] at h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ)).mp h
  exact hc k (hQ.mem_of_pow_mem _ hk)

theorem exists_form {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (b : curveRing y) :
    ∃ (e : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e ∧ aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k :=
  exists_form_of_mem_chartRingZ y c hc (mem_curveRing.mp b.2 c hc)

def formSet {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (Q : Ideal (MRing ι)) :
    Set (curveRing y) :=
  {b | ∃ (e : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e ∧
    aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q}

def formIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (Q : Ideal (MRing ι)) : Ideal (curveRing y) where
  carrier := formSet y c Q
  add_mem' := by
    classical
    rintro b₁ b₂ ⟨e₁, g₁, hg₁, hv₁, hQ₁⟩ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    refine ⟨e₁ + e₂, g₁ * chartMon c e₂ + g₂ * chartMon c e₁,
      homog_add (homog_mul hg₁ (homog_chartMon c e₂))
        (homogD (homog_mul hg₂ (homog_chartMon c e₁)) (add_comm _ _)), ?_,
      Q.add_mem (Q.mul_mem_right _ hQ₁) (Q.mul_mem_right _ hQ₂)⟩
    rw [map_add (f := _), map_mul, map_mul, aeval_chartMon, aeval_chartMon, hv₁, hv₂, prod_pow_add,
      Subring.coe_add]
    ring
  zero_mem' := ⟨0, 0, homog_zero _, by simp, Q.zero_mem⟩
  smul_mem' := by
    rintro b b₂ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine ⟨e + e₂, h * g₂, homog_mul hh hg₂, ?_, Q.mul_mem_left _ hQ₂⟩
    rw [map_mul, hv, hv₂, prod_pow_add, smul_eq_mul, Subring.coe_mul]
    ring

theorem mem_formIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {hc : ∀ k, y ⟨k, c k⟩ ≠ 0}
    {Q : Ideal (MRing ι)} {b : curveRing y} :
    b ∈ formIdeal y c hc Q ↔ ∃ (e : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e ∧
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q :=
  Iff.rfl

theorem le_of_minimal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hfin : Module.Finite ℤ (curveRing y)) (m : Ideal (curveRing y)) (hm : m.IsMaximal)
    (W Q : Ideal (MRing ι)) (hQ : Q.IsPrime) (hPQ : mCoordIdeal y ≤ Q) (hQW : Q ≤ W)
    (hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hWB : ∀ {g : MRing ι} {e : K → ℕ} (b : curveRing y), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ W ↔ b ∈ m))
    (hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n → f ∈ W →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧ (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k)
    (hWforms : IsMultiHomogIdeal W) {a b : curveRing y} (ha0 : a ≠ 0) {s : MRing ι} {d : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d) (hsQ : s ∈ Q) (hbx : (b : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k) :
    W ≤ Q := by
  classical
  have hmonQ : ∀ n, chartMon c n ∉ Q := chartMon_notMem hQ fun k h => hXc k (hQW h)
  have htr : ∀ {f g : MRing ι} {n : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n →
      aeval y f = aeval y g → g ∈ Q → f ∈ Q := by
    intro f g n hf hg he hgQ
    have h1 := Q.add_mem (hPQ (sub_mem_mCoordIdeal y hf hg he)) hgQ
    rwa [sub_add_cancel] at h1
  have hIQm : formIdeal y c hc Q ≤ m := by
    intro x hx
    obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp hx
    exact (hWB x hg hv).mp (hQW hgQ)
  have haIQ : a ∈ formIdeal y c hc Q := by
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine mem_formIdeal.mpr ⟨e + d, h * s, homog_mul hh hs, ?_, Q.mul_mem_left _ hsQ⟩
    rw [map_mul, hv, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ e k) * hbx
  have hIQprime : (formIdeal y c hc Q).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      intro h1
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h1
      refine hmonQ e (htr (homog_chartMon c e) hg ?_ hgQ)
      rw [aeval_chartMon, hv]
      simp
    · intro x₁ x₂ h12
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h12
      obtain ⟨e₁, h₁, hh₁, hv₁⟩ := exists_form y c hc x₁
      obtain ⟨e₂, h₂, hh₂, hv₂⟩ := exists_form y c hc x₂
      have hf : h₁ * h₂ * chartMon c e ∈ Q := by
        refine htr (homog_mul (homog_mul hh₁ hh₂) (homog_chartMon c e))
          (homogD (homog_mul hg (homog_chartMon c (e₁ + e₂))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (e₁ + e₂)) hgQ)
        simp only [map_mul, aeval_chartMon, hv₁, hv₂, hv, prod_pow_add, Subring.coe_mul]
        ring
      rcases hQ.mem_or_mem hf with h12 | h3
      · rcases hQ.mem_or_mem h12 with h1Q | h2Q
        · exact Or.inl (mem_formIdeal.mpr ⟨e₁, h₁, hh₁, hv₁, h1Q⟩)
        · exact Or.inr (mem_formIdeal.mpr ⟨e₂, h₂, hh₂, hv₂, h2Q⟩)
      · exact absurd h3 (hmonQ e)
  have hIQmax : (formIdeal y c hc Q).IsMaximal := by
    have : Algebra.IsIntegral ℤ (curveRing y) := Algebra.IsIntegral.of_finite ℤ _
    have hcomap : (formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 haIQ (Algebra.IsIntegral.isIntegral a)
    have : ((formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y))).IsPrime := Ideal.IsPrime.comap _
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (formIdeal y c hc Q)
      (IsPrime.to_maximal_ideal hcomap)
  have hIQeq : formIdeal y c hc Q = m := hIQmax.eq_of_le hm.ne_top hIQm

  obtain ⟨S, hS, hWS⟩ := hWforms
  intro f hfW
  rw [hWS] at hfW
  refine (Ideal.span_le.mpr ?_) hfW
  intro f hf
  obtain ⟨δ, hδ⟩ := hS f hf
  have hfW' : f ∈ W := by rw [hWS]; exact Ideal.subset_span hf
  obtain ⟨a', b', ha'm, hb'm, hv'⟩ := hWfrac hδ hfW'
  have ha'IQ : a' ∈ formIdeal y c hc Q := by rw [hIQeq]; exact ha'm
  obtain ⟨ea, ga, hga, hva, hgaQ⟩ := mem_formIdeal.mp ha'IQ
  obtain ⟨eb, hb, hhb, hvb⟩ := exists_form y c hc b'
  have hbQ : hb ∉ Q := by
    intro h
    have hbIQ : b' ∈ formIdeal y c hc Q := mem_formIdeal.mpr ⟨eb, hb, hhb, hvb, h⟩
    rw [hIQeq] at hbIQ
    exact hb'm hbIQ
  have h1 : hb * f * chartMon c ea ∈ Q := by
    refine htr (homog_mul (homog_mul hhb hδ) (homog_chartMon c ea))
      (homogD (homog_mul hga (homog_chartMon c (eb + δ))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (eb + δ)) hgaQ)
    simp only [map_mul, aeval_chartMon, hvb, hva, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ eb k) * (∏ k, y ⟨k, c k⟩ ^ ea k) * hv'
  rcases hQ.mem_or_mem h1 with h2 | h3
  · rcases hQ.mem_or_mem h2 with h4 | h5
    · exact absurd h4 hbQ
    · exact h5
  · exact absurd h3 (hmonQ ea)

theorem locLen_quot_eq_zero {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime] {a : R} (ha : a ∉ m) :
    locLen m (R ⧸ Ideal.span {a}) = 0 := by
  have key : ∀ w : LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}), w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h x t =>
      rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨a, ha⟩, ?_⟩
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  have hsub : Subsingleton (LocalizedModule m.primeCompl (R ⧸ Ideal.span {a})) :=
    ⟨fun u v => by rw [key u, key v]⟩
  rw [locLen, dite_eq_left ‹m.IsPrime›, Module.length_eq_zero_iff.mpr hsub]
  rfl

end CurveVerticalPointSurjective

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartConeComponent
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime)
open GroundTheory.Heights₂.Heights (segreChartComponents mem_segreChartComponents)

theorem ChartConeComponent.proof : ChartConeComponent.Statement := by
  intro K _ _ ι _ W m σ i hW W' hW'
  have hmin := mem_segreChartComponents.1 hW'
  have : W'.IsPrime := hmin.1.1
  let φ : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ := chartSubst σ i
  have : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
  have hle : W.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W'.comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show φ (MvPolynomial.map (Int.castRingHom ℂ) f) ∈ W'
    have h := ChartDivisorComponents.chartSection_mem hW.2.1 σ i hf
    rw [chartSection_eq_chartSubst] at h
    exact hmin.1.2 h
  obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨W'', hW'', Ideal.map_le_iff_le_comap.2 hW''le⟩

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple

noncomputable section

namespace CurveSectionQuotientLocal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  (y : (Σ k, ι k) → Ω)

theorem chart_mem_curveSectionMod (c : ∀ k, ι k) (d : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ d k ∈ curveSectionMod y (fun k => (d k : ℤ)) := by
  classical
  show _ ∈ chartLat y _ 1
  have h := chartLat_prod (y := y) Finset.univ (fun k => y ⟨k, c k⟩ ^ d k)
    (fun k => d k • (Pi.single k 1 : K → ℤ))
    (fun k _ => chartLat_pow (chartLat_var (y := y) ⟨k, c k⟩) (d k))
  convert h using 2
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_mul_mem_of_mem_chartRingZ (m : Ideal (curveRing y)) (hm : m.IsPrime) (c : ∀ k, ι k)
    (h : ∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a)
    {z : Ω} (hz : z ∈ chartRingZ y c) :
    ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * z = a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h p
  | algebraMap r =>
    refine ⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring
  | mul x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring

end CurveSectionQuotientLocal


open CurveSectionQuotientLocal in
theorem CurveSectionQuotLocal.proof : CurveSectionQuotLocal.Statement := by
  intro K _ ι _ Ω _ y s d _hy _hs _hsP m c hm hc hrat a b hb hba
  set x := aeval y s with hx_def
  set e₀ : Ω := ∏ k, y ⟨k, c k⟩ ^ d k with he₀_def
  have he₀ : e₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

  let e : curveSectionMod y (fun k => (d k : ℤ)) := ⟨e₀, chart_mem_curveSectionMod y c d⟩
  let φ : curveRing y →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)
  have hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e) := fun β => by
    simp [φ, Submodule.Quotient.mk_smul]
  have hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : Ω) * x = β * e₀ := by
    intro β
    rw [hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]
    rfl
  have hle : Ideal.span {a} ≤ LinearMap.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]
    exact ⟨b, hba⟩
  let ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    (Ideal.span {a}).liftQ φ hle

  have hker : ∀ q, ψ q = 0 → b • q = 0 := by
    intro q hq
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := (hφ0 β).mp hq
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Ideal.mem_span_singleton']
    refine ⟨γ, Subtype.ext ?_⟩
    push_cast
    apply mul_right_cancel₀ he₀
    rw [mul_assoc, ← hba, mul_assoc, ← hγ]
    ring

  have hsurj0 : ∀ n : curveSectionMod y (fun k => (d k : ℤ)),
      ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e := by
    intro n
    have hn : (n : Ω) ∈ chartLat y (fun k => (d k : ℤ)) 1 := n.2
    have hnc : (n : Ω) * e₀⁻¹ ∈ chartRingZ y c := by
      have h1 := (mem_chartLat_one y).mp hn c hc
      have h2 : ∏ k, y ⟨k, c k⟩ ^ (-((fun k => (d k : ℤ)) k)) = e₀⁻¹ := by
        rw [he₀_def, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [zpow_neg, zpow_natCast]
      rwa [h2] at h1
    obtain ⟨β, r, hr, hβ⟩ := exists_mul_mem_of_mem_chartRingZ y m hm c hrat hnc
    refine ⟨r, hr, β, Subtype.ext ?_⟩
    show (r : Ω) * n = β * e₀
    rw [← hβ]
    field_simp

  let S := m.primeCompl
  let Φ := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a}))
    (LocalizedModule.mkLinearMap S (curveSectionQuot y (fun k => (d k : ℤ)) x)) ψ
  have hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r :=
    fun q r => IsLocalizedModule.map_LocalizedModules S _ q r
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z
    refine LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z
    rw [hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul, ← map_smul] at hu
    have hq := hker _ hu
    rw [← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]
    refine ⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hq
  have hsurj : Function.Surjective Φ := by
    intro z
    refine LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨r', hr', β, hβ⟩ := hsurj0 n'
    refine ⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩
    rw [hΦ]
    have hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e) := by
      rw [← hφ]
      rfl
    rw [hψ, ← hβ, Submodule.Quotient.mk_smul]
    exact LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _
  have := hm
  let E := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S
    (Localization.AtPrime m)
  unfold locLen
  rw [dite_eq_left hm, dite_eq_left hm, E.length_eq]

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace CurveVerticalPointInjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem coord_ne_zero (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ)
    (hA : IsArithVar (mCoordIdeal y) 1) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d) {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  classical
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ K ι (mCoordIdeal y) s d hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ K ι _ W hJ hW.1)

end CurveVerticalPointInjective


open CurveVerticalPointInjective in
theorem CurveVertPointInj.proof (hCh : CurveVertPointChart.Statement) : CurveVertPointInj.Statement := by
  intro K _ ι _ Ω _ y s d hA hs hsP W hW W' hW' hWW'
  choose c hc using hW.2
  choose c' hc' using hW'.2
  obtain ⟨hmax, hrat, hform⟩ := hCh K ι Ω y s d hA hs hsP W hW c hc
  obtain ⟨-, -, hform'⟩ := hCh K ι Ω y s d hA hs hsP W' hW' c' hc'
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    coord_ne_zero y _ fun h => hc k (le_sup_left.trans hW.1.1.2 h)
  choose a' b' hb' hab' using fun k => hrat ⟨k, c' k⟩
  have hab'' : ∀ k, (b' k : Ω) * y ⟨k, c' k⟩ = a' k * y ⟨k, c k⟩ := fun k => by
    rw [← hab' k]; field_simp [hyc k]
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := isMultiHomogIdeal_of_mem_divSupp y s d hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' e g he).1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform e g he).2 ⟨a * ∏ k, a' k ^ e k, (∏ k, b' k ^ e k) * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · obtain ⟨k, -, hk⟩ := (hmax.isPrime.prod_mem_iff (s := Finset.univ)).1 h
        exact hb' k (hmax.isPrime.mem_of_pow_mem _ hk)
      · exact hb h
    · push_cast
      calc (∏ k, (b' k : Ω) ^ e k) * b * aeval y g
          = a * ∏ k, ((b' k : Ω) * y ⟨k, c' k⟩) ^ e k := by
            rw [mul_assoc, habg, Finset.prod_congr rfl fun k _ => mul_pow (b' k : Ω) _ (e k),
              Finset.prod_mul_distrib]; ring
        _ = (a * ∏ k, (a' k : Ω) ^ e k) * ∏ k, y ⟨k, c k⟩ ^ e k := by
            simp_rw [hab'', mul_pow, Finset.prod_mul_distrib]; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights.Targets
end

