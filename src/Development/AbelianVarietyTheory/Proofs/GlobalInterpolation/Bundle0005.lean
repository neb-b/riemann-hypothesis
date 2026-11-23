module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImage
section
namespace GlobalTheory

theorem linearEquiv_descends_of_preserves_image {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ))
    (h : ∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) :
    ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧
      LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
        f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  classical
  let F : (ι → K) → (ι → ℂ) := fun v i => f (v i)
  have hFinj : Function.Injective F := by
    intro v w hvw
    funext i
    exact f.injective (congrFun hvw i)
  choose G hG using h
  have hG' : ∀ v, u (F v) = F (G v) := hG
  have hFadd : ∀ v w, F (v + w) = F v + F w := by
    intro v w; funext i; simp [F]
  have hFsmul : ∀ (c : K) v, F (c • v) = f c • F v := by
    intro c v; funext i; simp [F]
  let Gl : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := G
      map_add' := fun v w => hFinj (by rw [← hG', hFadd, map_add (f := _), hG', hG', hFadd])
      map_smul' := fun c v => hFinj (by
        simp only [RingHom.id_apply]
        rw [← hG', hFsmul, map_smul, hG', hFsmul]) }
  have hGl : ∀ v, Gl v = G v := fun _ => rfl
  have hinj : Function.Injective Gl := by
    intro v w hvw
    apply hFinj
    apply u.injective
    rw [hG', hG']
    exact congrArg F hvw
  let g : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofInjectiveEndo Gl hinj
  have hg : ∀ v, g v = G v := fun v => by
    simp [g, hGl]
  have hsingle : ∀ j : ι, F (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij; simp [F]
    · simp [F, Pi.single_eq_of_ne hij]
  have hmat : LinearMap.toMatrix' (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
      (LinearMap.toMatrix' (g : (ι → K) →ₗ[K] (ι → K))).map f := by
    ext i j
    have := congrFun (hG' (Pi.single j 1)) i
    rw [hsingle j] at this
    simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
    simp only [LinearEquiv.coe_coe, hg]
    exact this
  refine ⟨g, fun v => ?_, ?_⟩
  · rw [hg]; exact hG v
  · rw [← LinearMap.det_toMatrix', hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      LinearMap.det_toMatrix']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralTsumOrbitUnfold
section
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_tsum_orbit_unfold (G G' V X : Type) [Group G] [Group G'] [MeasurableSpace G]
    [MeasurableSpace G'] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul G'] [MulAction G V]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (μ' : Measure G') [SFinite μ']
    [μ'.IsMulLeftInvariant] (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] [Countable Γ']
    (𝓕 : Set G) (𝓕' : Set G') (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (h𝓕' : IsFundamentalDomain Γ' 𝓕' μ') (φ : G' →* G) (hφm : Measurable φ)
    (hφi : Function.Injective φ) (hΓ : ∀ g, φ g ∈ Γ ↔ g ∈ Γ') (x : V)
    (hst : φ.range = MulAction.stabilizer G x) (c : X → V) (hc : Function.Injective c)
    (hcr : ∀ y, y ∈ Set.range c ↔ ∃ γ ∈ Γ, γ • x = y) (u : G → ℝ≥0∞) (hu : Measurable u)
    (Φ : V → ℝ≥0∞) (hΦ : ∀ h : G, Φ (h⁻¹ • x) = ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ') :
    ∫⁻ h in 𝓕, ∑' i, Φ (h⁻¹ • c i) ∂μ = μ' 𝓕' * ∫⁻ h, u h ∂μ := by
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Γ' G' := ⟨fun γ => measurable_const_mul (γ : G')⟩
  haveI : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Γ' G' μ' :=
    ⟨fun γ s _ => measure_preimage_mul μ' (γ : G') s⟩
  have hex : ∀ i, ∃ γ ∈ Γ, γ • x = c i := fun i => (hcr _).1 ⟨i, rfl⟩
  choose γ hγ hγx using hex
  have hfix : ∀ g, φ g • x = x := fun g => by
    have : φ g ∈ MulAction.stabilizer G x := hst ▸ ⟨g, rfl⟩
    exact this
  let f : X × Γ' → Γ := fun p => ⟨γ p.1 * φ p.2, Γ.mul_mem (hγ _) ((hΓ _).2 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have h1 : γ i * φ a = γ j * φ b := congrArg Subtype.val hab
      have h2 : i = j := by
        apply hc
        have := congrArg (· • x) h1
        simpa [mul_smul, hfix, hγx] using this
      subst h2
      have h3 : a = b := Subtype.ext (hφi (mul_left_cancel h1))
      rw [h3]
    · rintro ⟨δ, hδ⟩
      obtain ⟨i, hi⟩ := (hcr (δ • x)).2 ⟨δ, hδ, rfl⟩
      have h1 : (γ i)⁻¹ * δ ∈ φ.range := by
        rw [hst, MulAction.mem_stabilizer_iff, mul_smul, ← hi, ← hγx, inv_smul_smul]
      obtain ⟨a, ha⟩ := h1
      have ha' : a ∈ Γ' := (hΓ a).1 (ha ▸ Γ.mul_mem (Γ.inv_mem (hγ i)) hδ)
      refine ⟨(i, ⟨a, ha'⟩), Subtype.ext ?_⟩
      show γ i * φ a = δ
      rw [ha, mul_inv_cancel_left]
  let F : G → ℝ≥0∞ := fun h => ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ'
  have hK : Measurable (fun p : G × G' => u ((φ p.2)⁻¹ * p.1)) :=
    hu.comp (((hφm.comp measurable_snd).inv).mul measurable_fst)
  have hF : Measurable F := hK.lintegral_prod_right'
  have step : ∀ h : G, ∑' i, Φ (h⁻¹ • c i) = ∑' δ : Γ, F (δ⁻¹ • h) := by
    intro h
    rw [← (Equiv.ofBijective f hf).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun i => ?_
    have h1 : h⁻¹ • c i = ((γ i)⁻¹ * h)⁻¹ • x := by
      rw [mul_inv_rev, inv_inv, mul_smul, hγx]
    rw [h1, hΦ, h𝓕'.lintegral_eq_tsum'']
    refine tsum_congr fun a => ?_
    refine lintegral_congr fun g => ?_
    congr 1
    show (φ ((a : G') * g))⁻¹ * ((γ i)⁻¹ * h) = (φ g)⁻¹ * ((γ i * φ a)⁻¹ * h)
    simp [mul_assoc]
  simp_rw [step]
  rw [lintegral_tsum (f := fun (δ : Γ) h => F (δ⁻¹ • h)) (fun δ => (hF.comp (measurable_const_smul δ⁻¹)).aemeasurable),
    ← h𝓕.lintegral_eq_tsum' F]
  show ∫⁻ h, ∫⁻ g in 𝓕', u ((φ g)⁻¹ * h) ∂μ' ∂μ = _
  rw [lintegral_lintegral_swap hK.aemeasurable]
  simp_rw [lintegral_mul_left_eq_self u]
  rw [setLIntegral_const, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
section
open Real Filter Asymptotics

namespace GlobalTheory


open Filter Asymptotics in
theorem log_add_rpow_mul_log_pow_le_rpow :
    ∀ a b c C κ : ℝ, ∀ p : ℕ, 0 ≤ a → a < b → 0 < κ → ∃ x0 : ℝ, ∀ x ≥ x0,
      c * Real.log x + C * x ^ a * Real.log x ^ p + C ≤ κ * x ^ b := by
  intro a b c C κ p ha hab hκ
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have h1 : (fun x : ℝ => c * Real.log x) =o[atTop] fun x => x ^ b :=
    (isLittleO_log_rpow_atTop hb).const_mul_left c
  have h2 : (fun x : ℝ => C * x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
    have hl : (fun x : ℝ => Real.log x ^ p) =o[atTop] fun x => x ^ (b - a) := by
      have := isLittleO_log_rpow_rpow_atTop (p : ℝ) (sub_pos.2 hab)
      simpa [Real.rpow_natCast] using this
    have hm : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop]
        fun x => x ^ a * x ^ (b - a) :=
      (isBigO_refl (fun x : ℝ => x ^ a) atTop).mul_isLittleO hl
    have hm' : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
      refine hm.congr' (Eventually.of_forall fun _ => rfl) ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa [mul_assoc] using hm'.const_mul_left C
  have h3 : (fun _ : ℝ => C) =o[atTop] fun x => x ^ b := by
    rw [isLittleO_const_left]
    right
    exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hb)
  have h := (h1.add h2).add h3
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 ((h.bound hκ).and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hbd, hxpos⟩ := hx0 x hx
  have hpos : 0 < x ^ b := Real.rpow_pos_of_pos hxpos b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hbd
  exact (le_abs_self _).trans hbd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivEqOrderDivAddAnalytic
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem logDeriv_eq_order_div_add_analytic :
    ∀ (f : ℂ → ℂ) (p : ℂ), AnalyticAt ℂ f p → (¬ ∀ᶠ s in 𝓝 p, f s = 0) →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p, f s ≠ 0 ∧
        deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  intro f p hf hne
  have htop : analyticOrderAt f p ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; exact hne
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderNatAt_eq_iff htop (n := analyticOrderNatAt f p)).mp rfl
  set m := analyticOrderNatAt f p with hm
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have h1 : ∀ᶠ s in 𝓝 p, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have h2 : ∀ᶠ s in 𝓝 p, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have h3 := hfg.eventually_nhds
  have h4 : ∀ᶠ s in 𝓝[≠] p, s ≠ p := self_mem_nhdsWithin
  filter_upwards [h4, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3]
    with s hsp hs1 hs2 hs3
  have hsub : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hev : f =ᶠ[𝓝 s] fun z => (z - p) ^ m * g z := by
    filter_upwards [hs3] with z hz
    rw [hz, smul_eq_mul]
  have hfs : f s = (s - p) ^ m * g s := hev.eq_of_nhds
  have hd : HasDerivAt (fun z => (z - p) ^ m * g z)
      ((m : ℂ) * (s - p) ^ (m - 1) * 1 * g s + (s - p) ^ m * deriv g s) s :=
    (((hasDerivAt_id s).sub_const p).pow m).mul hs2.differentiableAt.hasDerivAt
  have hdf : deriv f s = (m : ℂ) * (s - p) ^ (m - 1) * 1 * g s + (s - p) ^ m * deriv g s := by
    rw [hev.deriv_eq, hd.deriv]
  refine ⟨by rw [hfs]; exact mul_ne_zero (pow_ne_zero _ hsub) hs1, ?_⟩
  rw [hdf, hfs]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0]; simp
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    field_simp
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivativeBound
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.logDerivativeThreeFourOne

lemma comb_nonneg {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have e := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at e
    nlinarith
  have e2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq]
  rw [e2]
  nlinarith [sq_nonneg (z.re + 1)]

lemma neg_logDeriv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ))) s n).re)
      (-(deriv (LFunction χ) s / LFunction χ s).re) := by
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  simpa [neg_div] using h'

lemma term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) n) *
          (fun n : ℕ => (vonMangoldt n : ℂ))) σ n).re
      + 4 * (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + t * I) n).re
      + (LSeries.term ((fun n : ℕ => (χ ^ 2) n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + 2 * t * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hA : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) σ
  set A : ℝ := (n : ℝ) ^ σ with hAdef
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  set b : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hbdef
  have ha : (n : ℂ) ^ (σ : ℂ) = (A : ℂ) := by
    rw [hAdef, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast
  have hb : ‖b‖ = 1 := by
    rw [hbdef, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hb0 : b ≠ 0 := by
    rintro h
    simp [h] at hb
  have e1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = A * b := by
    rw [cpow_add _ _ hn', ha]
  have e2 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I) = A * b ^ 2 := by
    rw [cpow_add _ _ hn', ha, hbdef, ← cpow_nat_mul]
    push_cast
    ring_nf
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  rw [e1, e2, ha]
  set c : ℝ := vonMangoldt n / A with hcdef
  have hc : 0 ≤ c := div_nonneg vonMangoldt_nonneg hA.le
  by_cases hu : IsUnit (n : ZMod q)
  · have hz : ‖χ n / b‖ = 1 := by
      rw [norm_div, hb, div_one]
      simpa using χ.unit_norm_eq_one hu.unit
    have k1 : (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / (A : ℂ) = (c : ℂ) := by
      rw [MulChar.one_apply hu, one_mul, hcdef, Complex.ofReal_div]
    have k2 : χ n * (vonMangoldt n : ℂ) / ((A : ℂ) * b) = (c : ℂ) * (χ n / b) := by
      rw [hcdef, Complex.ofReal_div]
      field_simp
    have k3 : (χ ^ 2) n * (vonMangoldt n : ℂ) / ((A : ℂ) * b ^ 2) = (c : ℂ) * (χ n / b) ^ 2 := by
      rw [MulChar.pow_apply' χ two_ne_zero, hcdef, Complex.ofReal_div]
      field_simp
    rw [k1, k2, k3, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hcomb := comb_nonneg hz
    nlinarith [mul_nonneg hc hcomb]
  · simp [MulChar.map_nonunit _ hu]

theorem three_four_one : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ), 1 < σ → 0 ≤ -(3 * (deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + 4 * (deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re + (deriv (LFunction (χ ^ 2)) (σ + 2 * t * I) / LFunction (χ ^ 2) (σ + 2 * t * I)).re) := by
  intro q _ χ σ t hσ
  have h1 := neg_logDeriv_eq (1 : DirichletCharacter ℂ q) (s := (σ : ℂ)) (by simpa using hσ)
  have h2 := neg_logDeriv_eq χ (s := (σ : ℂ) + t * I) (by simpa using hσ)
  have h3 := neg_logDeriv_eq (χ ^ 2) (s := (σ : ℂ) + 2 * t * I) (by simpa using hσ)
  have h := ((h1.mul_left 3).add (h2.mul_left 4)).add h3
  have hnn := h.nonneg (fun n => term_nonneg χ σ t n)
  linarith

end GlobalTheory.logDerivativeThreeFourOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureEqZeroOfFiniteInterLines
section
open MeasureTheory Topology

namespace GlobalTheory

theorem measure_eq_zero_of_finite_inter_lines
    (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V) (hZ : MeasurableSet Z) (y : V)
    (h : ∀ x : V, {t : K | x + t • y ∈ Z}.Finite) : μ Z = 0 := by
  let ν : Measure K := Measure.addHaar
  have hc : Continuous (fun p : V × K => p.1 + p.2 • y) := by fun_prop
  have hS : MeasurableSet {p : V × K | p.1 + p.2 • y ∈ Z} := hc.measurable hZ
  have h1 : (μ.prod ν) {p : V × K | p.1 + p.2 • y ∈ Z} = 0 := by
    rw [Measure.measure_prod_null hS]
    refine Filter.Eventually.of_forall fun x => ?_
    exact (h x).measure_zero ν
  rw [Measure.prod_apply_symm hS] at h1
  have h2 : ∀ t : K, μ ((fun x => (x, t)) ⁻¹' {p : V × K | p.1 + p.2 • y ∈ Z}) = μ Z := by
    intro t
    exact measure_preimage_add_right μ (t • y) Z
  simp only [h2, lintegral_const, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd h1 (by
      rw [Measure.measure_univ_eq_zero]
      exact NeZero.ne ν)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegSumLogDerivNonneg
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.TwoRealCharacters

theorem hasSum_re_neg_logDeriv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (χ n).re * (vonMangoldt n / (n : ℝ) ^ σ))
      (-(deriv (LFunction χ) σ / LFunction χ σ).re) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  convert (preTransparency := .reducible) h' using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
        ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp [Pi.mul_apply, Complex.div_ofReal_re, mul_div_assoc]
  · rw [neg_div, Complex.neg_re]

theorem re_sum_nonneg (q : ℕ) (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (a : ZMod q) :
    0 ≤ ((1 : DirichletCharacter ℂ q) a).re + (χ a).re + (ψ a).re + ((χ * ψ) a).re := by
  by_cases ha : IsUnit a
  · have hsq : ∀ φ : DirichletCharacter ℂ q, φ ^ 2 = 1 → φ a = 1 ∨ φ a = -1 := by
      intro φ hφ
      apply mul_self_eq_one_iff.mp
      have hval := congrArg (fun ξ : DirichletCharacter ℂ q => ξ a) hφ
      simp only [MulChar.pow_apply' φ two_ne_zero, MulChar.one_apply ha] at hval
      rw [← pow_two]
      exact hval
    rw [MulChar.one_apply ha, MulChar.coeToFun_mul, Pi.mul_apply]
    rcases hsq χ hχ with h1 | h1 <;> rcases hsq ψ hψ with h2 | h2 <;> norm_num [h1, h2]
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha,
      MulChar.map_nonunit _ ha]
    simp

theorem neg_sum_logDeriv_nonneg : ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) (σ : ℝ), χ ^ 2 = 1 → ψ ^ 2 = 1 → 1 < σ → 0 ≤ -((deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + (deriv (LFunction χ) σ / LFunction χ σ).re + (deriv (LFunction ψ) σ / LFunction ψ σ).re + (deriv (LFunction (χ * ψ)) σ / LFunction (χ * ψ) σ).re) := by
  intro q _ χ ψ σ hχ hψ hσ
  have h := (((hasSum_re_neg_logDeriv q 1 σ hσ).add (hasSum_re_neg_logDeriv q χ σ hσ)).add
    (hasSum_re_neg_logDeriv q ψ σ hσ)).add (hasSum_re_neg_logDeriv q (χ * ψ) σ hσ)
  have hnn := h.nonneg fun n => by
    have h1 := re_sum_nonneg q χ ψ hχ hψ (n : ZMod q)
    have h2 : 0 ≤ vonMangoldt n / (n : ℝ) ^ σ :=
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    have h3 := mul_nonneg h1 h2
    linarith
  linarith

end GlobalTheory.TwoRealCharacters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NoethLocalHausdorff
section
namespace GlobalTheory.NoetherianLocalHausdorff

theorem noeth_local_hausdorff : ∀ (B : Type) [inst : CommRing B] [inst_1 : IsLocalRing B] [IsNoetherianRing B],
    IsHausdorff (IsLocalRing.maximalIdeal B) B := by
  intro B _ _ _
  refine ⟨fun x hx => ?_⟩
  have h : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal B) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have := hx n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
    exact this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top] at h
  exact (Submodule.mem_bot B).1 h

end GlobalTheory.NoetherianLocalHausdorff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOver
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quadratic_at_most_two_primes_over (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (q : ℕ) (hq : q.Prime)
    (P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K))
    (h₁ : ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal) (h₂ : ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal)
    (h₃ : ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal) : P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  by_contra hne
  push Not at hne
  obtain ⟨h12, h13, h23⟩ := hne
  have hN : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 K)}) = q ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have : ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
    simp
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      P.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} := fun P hP =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hP)
  have hqd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      q ∣ Ideal.absNorm P.asIdeal := by
    intro P hP
    have h1 : Ideal.absNorm P.asIdeal ∣ q ^ 2 := hN ▸ map_dvd Ideal.absNorm (hd P hP)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hq).mp h1
    rcases i with _ | i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hi
      exact P.isPrime.ne_top hi
    · rw [hi]; exact dvd_pow_self q (Nat.succ_ne_zero i)
  have hc : ∀ P Q : HeightOneSpectrum (𝓞 K), P ≠ Q → IsCoprime P.asIdeal Q.asIdeal := by
    intro P Q h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact P.isMaximal.coprime_of_ne Q.isMaximal (fun e => h (HeightOneSpectrum.ext e))
  have hprod : P₁.asIdeal * P₂.asIdeal * P₃.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} :=
    IsCoprime.mul_dvd (IsCoprime.mul_left (hc _ _ h13) (hc _ _ h23))
      (IsCoprime.mul_dvd (hc _ _ h12) (hd _ h₁) (hd _ h₂)) (hd _ h₃)
  have h4 := map_dvd Ideal.absNorm hprod
  rw [hN, map_mul, map_mul] at h4
  have h5 : q * q * q ∣ q ^ 2 :=
    (mul_dvd_mul (mul_dvd_mul (hqd _ h₁) (hqd _ h₂)) (hqd _ h₃)).trans h4
  have h6 : q ^ 3 ∣ q ^ 2 := by rwa [show q ^ 3 = q * q * q by ring]
  have := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h6
  omega

end GlobalTheory
end

