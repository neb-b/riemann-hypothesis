module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralNonnegOfSums
section
open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.PosDefFT

theorem integral_prod_nonneg (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) := by
  set I := ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) with hI
  have key : ∀ k : ℕ, 0 ≤ (k : ℂ) * (ψ 0 - I + k * I) := by
    intro k
    let P : Measure (Fin k → ℝ) := Measure.pi (fun _ => μ)
    have hint : ∀ i j : Fin k, Integrable (fun t : Fin k → ℝ => ψ (t j - t i)) P := by
      intro i j
      refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
      exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have hval : ∀ i j : Fin k, ∫ t, ψ (t j - t i) ∂P = (if i = j then ψ 0 - I else 0) + I := by
      intro i j
      by_cases h : i = j
      · subst h
        simp
      · have hind : ProbabilityTheory.iIndepFun (fun (i : Fin k) (t : Fin k → ℝ) => t i) P :=
          ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
        have h2 := hind.indepFun h
        rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable] at h2
        have e : ∀ l : Fin k, P.map (fun t => t l) = μ := fun l =>
          (measurePreserving_eval (fun _ : Fin k => μ) l).map_eq
        rw [e, e] at h2
        rw [if_neg h, zero_add, hI, ← h2, integral_map (by fun_prop)]
        exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have h0 : 0 ≤ ∫ t, ∑ i, ∑ j, ψ (t j - t i) ∂P := integral_nonneg (fun t => hp k t)
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))] at h0
    simp_rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint _ j), hval] at h0
    simpa [Finset.sum_add_distrib, mul_add] using h0
  have key2 : ∀ k : ℕ, 0 ≤ (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I := by
    intro k
    have h1 := key (k + 1)
    have h2 : (0 : ℝ) ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by positivity
    have h3 := smul_nonneg h2 h1
    convert h3 using 1
    have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [Complex.real_smul]
    push_cast
    field_simp
  have hlim : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I) atTop
      (𝓝 ((0 : ℝ) • (ψ 0 - I) + I)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _).add_const _
  simpa using ge_of_tendsto' hlim key2

theorem integral_nonneg_of_sums (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hi : Integrable ψ)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i)) :
    0 ≤ ∫ s, ψ s := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let G : ℕ → ℝ → ℂ := fun n x => ∫ s in (-((n : ℝ) * x))..((n : ℝ) * (1 - x)), ψ s
  have hG : ∀ n x, G n x = (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := by
    intro n x
    have h := intervalIntegral.smul_integral_comp_mul_sub (f := ψ) (a := 0) (b := 1) (n : ℝ)
      ((n : ℝ) * x)
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
    simp only [G, μ, mul_sub]
    rw [h]
    simp
  have hint : ∀ n : ℕ, Integrable (fun p : ℝ × ℝ => ψ ((n : ℝ) * (p.2 - p.1))) (μ.prod μ) := by
    intro n
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  have hnn : ∀ n, 0 ≤ ∫ x, G n x ∂μ := by
    intro n
    have h := integral_prod_nonneg (fun s => ψ ((n : ℝ) * s)) (hc.comp (by fun_prop)) C
      (fun s => hb _) (fun k t => by simpa [mul_sub] using hp k (fun i => (n : ℝ) * t i)) μ
    rw [integral_prod _ (hint n)] at h
    simp_rw [hG, integral_smul]
    exact smul_nonneg (Nat.cast_nonneg n) h
  have hlim : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ _x, (∫ s, ψ s) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ s, ‖ψ s‖) ?_
      (integrable_const _) ?_ ?_
    · intro n
      have : G n = fun x => (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := funext (hG n)
      rw [this]
      exact ((hint n).integral_prod_left.smul (n : ℝ)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
      exact setIntegral_le_integral hi.norm (Eventually.of_forall fun _ => norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      refine intervalIntegral_tendsto_integral hi ?_ ?_
      · exact tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hx.1)
      · exact tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hx.2)
  simpa using ge_of_tendsto' hlim hnn

theorem fourier_nonneg : ∀ φ : ℝ → ℂ, Continuous φ →
    (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
    (∀ (k : ℕ) (t : Fin k → ℝ) (z : Fin k → ℂ),
      0 ≤ ∑ i, ∑ j, star (z i) * z j * φ (t j - t i)) →
    ∀ ξ : ℝ, 0 ≤ ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s := by
  rintro φ hc ⟨A, e, he, hb⟩ hp ξ
  have hn : ∀ s : ℝ, ‖Complex.exp (-(Complex.I * ξ * s)) * φ s‖ = ‖φ s‖ := by
    intro s
    rw [norm_mul, Complex.norm_exp]
    simp
  have hc' : Continuous fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s := by fun_prop
  have hA : 0 ≤ A := by simpa using (norm_nonneg _).trans (hb 0)
  refine integral_nonneg_of_sums _ hc' A (fun s => ?_) ?_ (fun k t => ?_)
  · rw [hn]
    refine (hb s).trans (mul_le_of_le_one_right hA ?_)
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  · have h1 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Ioi 0) := by
      refine (exp_neg_integrableOn_Ioi 0 he).congr_fun (fun s hs => ?_) measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.1 hs)]
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Iic 0) := by
      refine (integrableOn_exp_mul_Iic he 0).congr_fun (fun s hs => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.1 hs)]
    have h3 : Integrable (fun s : ℝ => Real.exp (-(e * |s|))) := by
      have := h2.union h1
      rwa [Set.Iic_union_Ioi, integrableOn_univ] at this
    refine (h3.const_mul A).mono' hc'.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [hn]
    exact hb s
  · convert hp k t (fun j => Complex.exp (-(Complex.I * ξ * t j))) using 4 with i _ j _
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp
    ring

end GlobalTheory.PosDefFT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegratedOperatorIsStarProjectionAndSandwich
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

private lemma inner_apply_eq_inner_apply_inv_of_isometric {G : Type} [Group G] {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (a : G) (u w : Hp) : ⟪π a u, w⟫_ℂ = ⟪u, π a⁻¹ w⟫_ℂ := by

  let L : Hp →ₗᵢ[ℂ] Hp := { toLinearMap := (π a : Hp →ₗ[ℂ] Hp), norm_map' := hiso a }
  have hback : π a (π a⁻¹ w) = w := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hL : ⟪L u, L (π a⁻¹ w)⟫_ℂ = ⟪u, π a⁻¹ w⟫_ℂ := L.inner_map_map _ _
  rw [← hL]
  show ⟪π a u, w⟫_ℂ = ⟪π a u, π a (π a⁻¹ w)⟫_ℂ
  rw [hback]

theorem integratedOperator_isStarProjection_and_sandwich :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [SigmaFinite μ] [μ.IsInvInvariant] (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ (φ m : G → ℂ), Integrable φ μ → (∀ g, star (φ g⁻¹) = φ g) → (∀ x y : G, ∫ g, φ g * φ (x⁻¹ * g⁻¹ * y) ∂μ = m x * φ y) → m 1 = 1 → ∀ P : Hp →L[ℂ] Hp, (∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ) → IsStarProjection P ∧ ∀ x : G, P ∘L π x ∘L P = m x • P := by
  intro G _ _ _ _ _ _ μ _ _ _ _ Hp _ _ _ π hiso hcont φ m hφ hstar hconv hm1 P hP

  have hsand : ∀ x : G, P ∘L π x ∘L P = m x • P := by
    intro x
    ext1 v
    refine ext_inner_left ℂ fun u => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, inner_smul_right, hP, hP]

    have step : ∀ g : G, ⟪u, π g (π x (P v))⟫_ℂ
        = ∫ k, φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ ∂μ := by
      intro g
      have e1 : ⟪u, π g (π x (P v))⟫_ℂ = ⟪π (g * x)⁻¹ u, P v⟫_ℂ := by
        rw [inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]
        simp only [map_mul, ContinuousLinearMap.mul_apply]
      have e2 : ∀ h : G, ⟪π (g * x)⁻¹ u, π h v⟫_ℂ = ⟪u, π (g * x * h) v⟫_ℂ := by
        intro h
        rw [inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]
        simp only [map_mul, ContinuousLinearMap.mul_apply]
      rw [e1, hP]
      simp_rw [e2]
      have htr := integral_mul_left_eq_self (μ := μ)
        (fun h => φ h * ⟪u, π (g * x * h) v⟫_ℂ) (g * x)⁻¹
      rw [← htr]
      congr 1
      funext k
      rw [mul_inv_cancel_left, mul_inv_rev]
    simp_rw [step]

    have hshift : Integrable (fun k => φ (x⁻¹ * k)) μ := hφ.comp_mul_left x⁻¹
    have hprod : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.2)) (μ.prod μ) :=
      hφ.mul_prod hshift
    have hsheared : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.1⁻¹ * z.2)) (μ.prod μ) := by
      have h := (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable hprod
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.comp, mul_assoc]
    have hcoef : Continuous fun k : G => ⟪u, π k v⟫_ℂ := continuous_const.inner (hcont v)
    have hbound : ∀ᵐ z ∂(μ.prod μ), ‖⟪u, π z.2 v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
      refine Filter.Eventually.of_forall fun z => ?_
      calc ‖⟪u, π z.2 v⟫_ℂ‖ ≤ ‖u‖ * ‖π z.2 v‖ := norm_inner_le_norm _ _
        _ = ‖u‖ * ‖v‖ := by rw [hiso]
    have hint : Integrable (Function.uncurry fun g k =>
        φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ)) (μ.prod μ) := by
      have h := hsheared.mul_bdd (hcoef.comp continuous_snd).aestronglyMeasurable hbound
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      rcases z with ⟨g, k⟩
      simp only [Function.uncurry_apply_pair, Function.comp]
      ring
    calc ∫ g, φ g * ∫ k, φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ ∂μ ∂μ
        = ∫ g, ∫ k, φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ) ∂μ ∂μ := by
          congr 1; funext g; rw [integral_const_mul]
      _ = ∫ k, ∫ g, φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ) ∂μ ∂μ :=
          integral_integral_swap hint
      _ = ∫ k, (m x * φ k) * ⟪u, π k v⟫_ℂ ∂μ := by
          congr 1; funext k
          rw [← hconv x k, ← integral_mul_const]
          congr 1; funext g; ring
      _ = m x * ∫ k, φ k * ⟪u, π k v⟫_ℂ ∂μ := by
          rw [← integral_const_mul]
          congr 1; funext k; ring

  have hsa : IsSelfAdjoint P := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro a b
    show ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ
    rw [← inner_conj_symm (P a) b, hP b a, hP a b, ← integral_conj]
    calc ∫ g, (starRingEnd ℂ) (φ g * ⟪b, π g a⟫_ℂ) ∂μ
        = ∫ g, (starRingEnd ℂ) (φ g) * ⟪a, π g⁻¹ b⟫_ℂ ∂μ := by
          congr 1; funext g; rw [map_mul, inner_conj_symm, inner_apply_eq_inner_apply_inv_of_isometric π hiso]
      _ = ∫ g, (starRingEnd ℂ) (φ g⁻¹) * ⟪a, π g⁻¹⁻¹ b⟫_ℂ ∂μ :=
          (integral_inv_eq_self (fun g => (starRingEnd ℂ) (φ g) * ⟪a, π g⁻¹ b⟫_ℂ) μ).symm
      _ = ∫ g, φ g * ⟪a, π g b⟫_ℂ ∂μ := by
          congr 1; funext g; rw [inv_inv, starRingEnd_apply, hstar]

  have hidem : IsIdempotentElem P := by
    have h := hsand 1
    rw [map_one, hm1, one_smul] at h
    show P * P = P
    ext v
    have hv := DFunLike.congr_fun h v
    simpa using hv
  exact ⟨⟨hidem, hsa⟩, hsand⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubtype
section
namespace GlobalTheory.SmulMemComapLattice

open NumberField

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (v : V) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hax
    · rw [mul_smul]; exact L.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap R K q ≠ 0 := by
      simpa using hq0
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have : (q * a) • (algebraMap R K p / algebraMap R K q) • x = p • a • x := by
      rw [← algebraMap_smul K (q * a), ← algebraMap_smul K p, ← algebraMap_smul K a x,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ hax

theorem isLattice_comap_subtype {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsFullLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Submodule.comap (LinearMap.restrictScalars (𝓞 K) W.subtype) Λ) := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (LinearMap.restrictScalars (𝓞 K) W.subtype) :=
      W.injective_subtype
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    exact Submodule.FG.of_le hΛ.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.SmulMemComapLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank
section
open NumberField UniqueFactorizationMonoid

namespace GlobalTheory.SplitRadical

theorem isRadical_of_squarefree {S : Type} [CommRing S] [IsDedekindDomain S] {I : Ideal S}
    (hI : Squarefree I) : I.IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h1 : I ∣ Ideal.span {x} ^ n := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 : I ∣ Ideal.span {x} := hI.isRadical n _ h1
  exact (Ideal.span_singleton_le_iff_mem I).1 (Ideal.dvd_iff_le.1 h2)

theorem isRadical_span_of_ncard_primesOver : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E →
    (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  intro E _ _ p hp hcard
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P ≠ ⊥ := by
    rw [hP, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.span {(p : 𝓞 E)} = P.map (algebraMap ℤ (𝓞 E)) := by
    rw [hP, Ideal.map_span, Set.image_singleton, map_natCast]
  have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank, ← hcard, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    ← Finset.card_univ, Finset.card_eq_sum_ones] at hsum

  have hge : ∀ q ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    haveI : q.1.IsPrime := q.2.1
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := ℤ) q.1).ne'
      (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ = 1 := by
    intro q
    have := (Finset.sum_eq_sum_iff_of_le hge).1 hsum.symm q (Finset.mem_univ q)
    exact Nat.eq_one_of_mul_eq_one_right this.symm

  rw [hmap]
  apply isRadical_of_squarefree
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmap0,
    Multiset.nodup_iff_count_le_one]
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors (P.map (algebraMap ℤ (𝓞 E)))
  · have hqprime : q.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor q hq)
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ q :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq)
    have hlo : q.LiesOver P :=
      ⟨hPmax.eq_of_le (Ideal.comap_ne_top _ hqprime.ne_top) (Ideal.map_le_iff_le_comap.1 hle)⟩
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count P q hmap0]
    exact (hone ⟨q, hqprime, hlo⟩).le
  · rw [Multiset.count_eq_zero.2 hq]
    exact zero_le_one

end GlobalTheory.SplitRadical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSliceIndicatorLintegralLe
section
open MeasureTheory

namespace GlobalTheory

theorem iwasawa_slice_lintegral_le :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (N M K : Subgroup G) (μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ : G → ENNReal) (κ : G → G) (D DN DM : Set G), Measurable δ → Measurable κ → MeasurableSet DN → MeasurableSet DM → μN (N : Set G)ᶜ = 0 → μM (M : Set G)ᶜ = 0 → μK (K : Set G)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ K, κ k ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) → (∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m) → (∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ D → u ∈ DN ∧ m * κ k ∈ DM) → ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN ≤ μN DN * ∫⁻ m in DM, δ m ∂μM := by
  intro G _ _ _ N M K μN μM μK _ _ _ δ κ D DN DM hδ hκ hDN hDM hN hM hK hK1 hκK hinv hδinv hD
  have aeM : ∀ᵐ m ∂μM, m ∈ (M : Set G) := mem_ae_iff.2 hM
  have aeK : ∀ᵐ k ∂μK, k ∈ (K : Set G) := mem_ae_iff.2 hK
  have aeN : ∀ᵐ u ∂μN, u ∈ (N : Set G) := mem_ae_iff.2 hN

  have htrans : ∀ l ∈ K ⊓ M,
      ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * l) ∂μM = ∫⁻ m in DM, δ m ∂μM := by
    intro l hl
    have hfun : (fun m => δ m * DM.indicator (1 : G → ENNReal) (m * l))
        =ᵐ[μM] fun m => DM.indicator δ (m * l) := by
      filter_upwards [aeM] with m hm
      have hδml := hδinv l hl m hm
      by_cases hml : m * l ∈ DM
      · simp [hml, hδml]
      · simp [hml]
    rw [lintegral_congr_ae hfun, ← lintegral_map (hδ.indicator hDM) (measurable_mul_const l),
      hinv l hl, lintegral_indicator hDM]

  have hF : Measurable (Function.uncurry
      (fun (m k : G) => δ m * DM.indicator (1 : G → ENNReal) (m * κ k))) :=
    (hδ.comp measurable_fst).mul
      ((measurable_one.indicator hDM).comp (measurable_fst.mul (hκ.comp measurable_snd)))

  have hinner : ∀ u ∈ (N : Set G),
      ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
        ≤ DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u := by
    intro u hu
    by_cases huD : u ∈ DN
    · rw [Set.indicator_of_mem huD]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ m, δ m * ∫⁻ k, DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            gcongr δ m * ?_
            apply lintegral_mono_ae
            filter_upwards [aeK] with k hk
            by_cases hmem : u * m * k ∈ D
            · have h2 := (hD u hu m hm k hk hmem).2
              simp [hmem, h2]
            · simp [hmem]
        _ = ∫⁻ m, ∫⁻ k, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_congr
            intro m
            have hmeas : Measurable (fun k => DM.indicator (1 : G → ENNReal) (m * κ k)) :=
              (measurable_one.indicator hDM).comp (measurable_const.mul hκ)
            exact (lintegral_const_mul (δ m) hmeas).symm
        _ = ∫⁻ k, ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μM ∂μK :=
            lintegral_lintegral_swap hF.aemeasurable
        _ = ∫⁻ _k, ∫⁻ m in DM, δ m ∂μM ∂μK := by
            apply lintegral_congr_ae
            filter_upwards [aeK] with k hk
            exact htrans (κ k) (hκK k hk)
        _ = ∫⁻ m in DM, δ m ∂μM := by
            rw [lintegral_const, hK1, mul_one]
    · have hind : DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u = 0 := by
        simp [huD]
      rw [hind]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ _m, (0 : ENNReal) ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            have hae : (fun k => D.indicator (1 : G → ENNReal) (u * m * k))
                =ᵐ[μK] fun _ => (0 : ENNReal) := by
              filter_upwards [aeK] with k hk
              have hmem : u * m * k ∉ D := fun h => huD (hD u hu m hm k hk h).1
              simp [hmem]
            rw [lintegral_congr_ae hae, lintegral_zero, mul_zero]
        _ = 0 := lintegral_zero
  calc ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN
      ≤ ∫⁻ u, DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u ∂μN := by
        apply lintegral_mono_ae
        filter_upwards [aeN] with u hu
        exact hinner u hu
    _ = μN DN * ∫⁻ m in DM, δ m ∂μM := by
        rw [lintegral_indicator hDN, setLIntegral_const]
        exact mul_comm _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixExtLast
section
namespace GlobalTheory.MatrixExtLast

theorem matrix_ext_last {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h₁ : ∀ i j : Fin k, M (Fin.castSucc i) (Fin.castSucc j) = N (Fin.castSucc i) (Fin.castSucc j))
    (h₂ : ∀ i : Fin k, M (Fin.castSucc i) (Fin.last k) = N (Fin.castSucc i) (Fin.last k))
    (h₃ : ∀ j : Fin k, M (Fin.last k) (Fin.castSucc j) = N (Fin.last k) (Fin.castSucc j))
    (h₄ : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h₄
    | cast j => exact h₃ j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h₂ i
    | cast j => exact h₁ i j

end GlobalTheory.MatrixExtLast
end

