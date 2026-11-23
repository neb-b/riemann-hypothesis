module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SBConv

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem eventually_translate {F : G → ℂ} (hF : F ∈ SB G) :
    ∀ᶠ x in nhds (0 : G), ∀ g, F (g - x) = F g := by
  have hlc : IsLocallyConstant F := hF.1
  have hK : IsCompact (tsupport F) := hF.2
  have hz : ∀ z, z ∉ tsupport F → F z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport F h)
  have step : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - x) = F y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hy := hlc.eventually_eq y
    have h1 : Filter.Tendsto (fun p : G × G => p.2 - p.1) (nhds ((0 : G), y)) (nhds y) := by
      simpa using (continuous_snd.tendsto ((0 : G), y)).sub (continuous_fst.tendsto ((0 : G), y))
    have h2 : Filter.Tendsto (fun p : G × G => p.2) (nhds ((0 : G), y)) (nhds y) :=
      continuous_snd.tendsto _
    filter_upwards [h1.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have step' : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - -x) = F y :=
    (continuous_neg.tendsto' (0 : G) 0 neg_zero).eventually step
  filter_upwards [step, step'] with x hx hx' g
  by_cases hg : g ∈ tsupport F
  · exact hx g hg
  · rw [hz g hg]
    by_cases hg' : g - x ∈ tsupport F
    · have h := hx' (g - x) hg'
      rw [sub_neg_eq_add, sub_add_cancel, hz g hg] at h
      exact h.symm
    · exact hz _ hg'

def translate (Ψ : SB G) (y : G) : SB G :=
  ⟨fun x => Ψ.1 (x - y), Ψ.2.1.comp_continuous (continuous_sub_right y),
    Ψ.2.2.comp_homeomorph (Homeomorph.subRight y)⟩

theorem isLocallyConstant_translate (Ψ : SB G) : IsLocallyConstant (translate Ψ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hmap : Filter.Tendsto (fun y' : G => y' - y) (nhds y) (nhds 0) := by
    simpa using (continuous_id.tendsto y).sub_const y
  filter_upwards [hmap.eventually (eventually_translate Ψ.2)] with y' hy'
  apply Subtype.ext
  funext x
  show Ψ.1 (x - y') = Ψ.1 (x - y)
  have h := hy' (x - y)
  rwa [sub_sub_sub_cancel_right] at h

theorem exists_conv [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (Φ Ψ : SB G) :
    ∃ w : SB G, (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂μ) ∧
      ∀ l : SB G →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (translate Ψ y) ∂μ := by
  have hT : IsLocallyConstant (fun y => Φ.1 y • translate Ψ y) :=
    IsLocallyConstant.comp₂ Φ.2.1 (isLocallyConstant_translate Ψ) (fun c f => c • f)
  have hz : ∀ y, y ∉ tsupport Φ.1 → Φ.1 y • translate Ψ y = 0 := by
    intro y hy
    have h0 : Φ.1 y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    rw [h0, zero_smul]
  obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact G μ (SB G)
    (fun y => Φ.1 y • translate Ψ y) hT (tsupport Φ.1) Φ.2.2.isCompact hz
  refine ⟨w, fun x => ?_, fun l => ?_⟩
  · exact hw ((LinearMap.proj x).comp (SB G).subtype)
  · rw [hw l]
    simp only [map_smul, smul_eq_mul]

end Abstract

theorem exists_convolution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ ν _ Φ Ψ
  have : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have : ν.Regular := inferInstance
  have : ν.IsNegInvariant := inferInstance
  obtain ⟨w, hw1, hw2⟩ := exists_conv (Measure.pi fun _ : n => ν) Φ Ψ
  refine ⟨translate Ψ, w, fun y x => rfl, hw1, fun x => ?_, hw2⟩
  rw [hw1 x]
  have h := integral_sub_left_eq_self (fun y => Φ.1 (x - y) * Ψ.1 y) (Measure.pi fun _ : n => ν) x
  simp only [sub_sub_cancel] at h
  refine h.trans ?_
  congr 1
  funext y
  exact mul_comm _ _

end GlobalTheory.SBConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CompactQuotientFourier

theorem setIntegral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

theorem inversion_at_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ _ χ hc hx ha hn hker hinj μ 𝓕 hμ h𝓕 h1 Φ hΦ hper hsum
  classical
  haveI := hμ
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hne : ∀ a x, χ a x ≠ 0 := fun a x h => by simpa [h] using hn a x
  have hχ0 : ∀ x, χ 0 x = 1 := fun x => by
    have h2 : χ 0 x * χ 0 x = χ 0 x * 1 := by rw [mul_one, ← ha, add_zero]
    exact mul_left_cancel₀ (hne 0 x) h2
  have hχx0 : ∀ a, χ a 0 = 1 := fun a => by
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [mul_one, ← hx, add_zero]
    exact mul_left_cancel₀ (hne a 0) h2
  have hstar : ∀ a x, star (χ a x) = χ (-a) x := fun a x => by
    have h1' : χ (-a) x * χ a x = 1 := by rw [← ha, neg_add_cancel, hχ0]
    have h2 : star (χ a x) * χ a x = 1 := by simp [Complex.conj_mul', hn]
    exact mul_right_cancel₀ (hne a x) (h2.trans h1'.symm)
  have hperχ : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := fun a γ hγ x => by
    rw [hx, (hker γ).2 hγ a, one_mul]
  have horth : ∀ a b, ∫ x in 𝓕, χ b x * star (χ a x) ∂μ = if a = b then 1 else 0 := by
    intro a b
    have he : ∀ x, χ b x * star (χ a x) = χ (b - a) x := fun x => by rw [hstar, ← ha, sub_eq_add_neg]
    simp_rw [he]
    split_ifs with hab
    · subst hab
      simp [hχ0, hvol]
    · have hc' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, χ (b - a) x₀ ≠ 1 := by
        by_contra h
        push_neg at h
        exact hc' (hinj _ h)
      have key := setIntegral_translate Γ μ 𝓕 h𝓕 (χ (b - a)) (hperχ _) x₀
      simp_rw [hx _ _ x₀] at key
      rw [integral_mul_const] at key
      have h3 : (∫ x in 𝓕, χ (b - a) x ∂μ) * (χ (b - a) x₀ - 1) = 0 := by
        rw [mul_sub, key, mul_one, sub_self]
      exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hx₀)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  have hΦb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← hper γ hγ x]
    exact hC _ hk
  have hint : ∀ f : G → ℂ, Continuous f → ∀ B, (∀ x, ‖f x‖ ≤ B) → Integrable f (μ.restrict 𝓕) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  set c : A → ℂ := fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ with hcdef
  have hterm : ∀ a x, ‖c a * star (χ a x)‖ = ‖c a‖ := fun a x => by
    rw [norm_mul, norm_star, hn, mul_one]
  let S : G → ℂ := fun x => ∑' a, c a * star (χ a x)
  have hScont : Continuous S :=
    continuous_tsum (fun a => continuous_const.mul (hc a).star) hsum (fun a x => (hterm a x).le)
  have hSper : ∀ γ ∈ Γ, ∀ x, S (γ + x) = S x := fun γ hγ x => by
    simp only [S, hperχ _ γ hγ]
  have hSb : ∀ x, ‖S x‖ ≤ ∑' a, ‖c a‖ := fun x => by
    have hs : Summable (fun a => ‖c a * star (χ a x)‖) := by simp_rw [hterm]; exact hsum
    calc ‖S x‖ ≤ ∑' a, ‖c a * star (χ a x)‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' a, ‖c a‖ := by simp_rw [hterm]
  have hcS : ∀ b, ∫ x in 𝓕, χ b x * S x ∂μ = c b := by
    intro b
    have e : ∀ x, χ b x * S x = ∑' a, χ b x * (c a * star (χ a x)) := fun x => tsum_mul_left.symm
    have hnorm : ∀ a x, ‖χ b x * (c a * star (χ a x))‖ = ‖c a‖ := fun a x => by
      rw [norm_mul, hn, one_mul, hterm]
    have hFi : ∀ a, Integrable (fun x => χ b x * (c a * star (χ a x))) (μ.restrict 𝓕) := fun a =>
      hint _ ((hc b).mul (continuous_const.mul (hc a).star)) ‖c a‖ fun x => (hnorm a x).le
    have hFs : Summable fun a => ∫ x in 𝓕, ‖χ b x * (c a * star (χ a x))‖ ∂μ := by
      simp_rw [hnorm]
      simpa [hvol] using hsum
    have e2 : ∀ a, ∫ x in 𝓕, χ b x * (c a * star (χ a x)) ∂μ = c a * (if a = b then 1 else 0) := fun a => by
      rw [← horth, ← integral_const_mul]
      congr 1
      funext x
      ring
    simp_rw [e]
    rw [← integral_tsum_of_summable_integral_norm hFi hFs]
    simp_rw [e2, mul_ite, mul_one, mul_zero]
    simp
  have hdiff := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha hχ0 hn hker
    μ 𝓕 hμ h𝓕 (Φ - S) (hΦ.sub hScont) (fun γ hγ x => by simp only [Pi.sub_apply, hper γ hγ, hSper γ hγ])
    (fun a => by
      simp only [Pi.sub_apply, mul_sub]
      have i1 : Integrable (fun x => χ a x * Φ x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hΦ) C fun x => by rw [norm_mul, hn, one_mul]; exact hΦb x
      have i2 : Integrable (fun x => χ a x * S x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hScont) _ fun x => by rw [norm_mul, hn, one_mul]; exact hSb x
      rw [integral_sub i1 i2, hcS, sub_self])
  have h0 := congrFun hdiff 0
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h0
  rw [h0]
  simp only [S, hχx0, star_one, mul_one]

end GlobalTheory.CompactQuotientFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

def box (n : Type*) (s : kˣ) : Set (n → k) := Set.univ.pi fun _ => cball s

omit [DecidableEq n] in
theorem isOpen_box (s : kˣ) : IsOpen (box n s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s

omit [Fintype n] [DecidableEq n] in
theorem isCompact_box (s : kˣ) : IsCompact (box n s) :=
  isCompact_univ_pi fun _ => isCompact_cball s

omit [DecidableEq n] in
theorem exists_box_subset {U : Set (n → k)} (hU : U ∈ 𝓝 (0 : n → k)) : ∃ s : kˣ, box n s ⊆ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  have h1 : (⋂ i, t i) ∈ 𝓝 (0 : k) := Filter.iInter_mem.mpr ht
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  exact ⟨s, fun x hx => hsub fun i _ => Set.mem_iInter.mp (hs (hx i trivial)) i⟩


omit [DecidableEq n] in
theorem exists_box_invariant {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∀ t ∈ box n s, ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : n → k), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_box_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · have := hs (show -t ∈ box n s from fun i _ => neg_mem_cball (ht i trivial)) _ hx'
    rw [← this, add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

omit [DecidableEq n] in
theorem continuous_dot : Continuous fun q : (n → k) × (n → k) => q.1 ⬝ᵥ q.2 :=
  continuous_fst.dotProduct continuous_snd

variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]

theorem fourier_eq_zero_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) {s : kˣ}
    {f : (n → k) → ℂ} (hs : ∀ t ∈ box n s, ∀ x, f (x + t) = f x) {y : n → k} (hy : y ∉ box n (c * s⁻¹)) :
    ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball (c * s⁻¹) := by
    by_contra hne
    push Not at hne
    exact hy fun i _ => hne i
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one s hi
  have hbox : (Pi.single i t : n → k) ∈ box n s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  have h1 := integral_add_right_eq_self (μ := μ) (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) (Pi.single i t)
  have h2 : ∀ x, f (x + Pi.single i t) * (ψ ((x + Pi.single i t) ⬝ᵥ y) : ℂ) =
      (ψ (t * y i) : ℂ) * (f x * (ψ (x ⬝ᵥ y) : ℂ)) := by
    intro x
    rw [hs _ hbox, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp only [h2, integral_const_mul] at h1
  have h3 : (ψ (t * y i) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
  refine (mul_eq_zero.mp ?_).resolve_left h3
  rw [sub_mul, h1, one_mul, sub_self]

theorem fourier_indicator_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) (s : kˣ)
    (x : n → k) :
    ∫ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) ∂μ =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x := by
  haveI := secondCountable k
  by_cases hx : x ∈ box n s
  · rw [Set.indicator_of_mem hx]
    have : ∀ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) =
        (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y := by
      intro y
      by_cases hy : y ∈ box n (c * s⁻¹)
      · have h1 : y ⬝ᵥ x ∈ cball c := by
          show valuation k (∑ i, y i * x i) ≤ valuation k (c : k)
          refine Valuation.map_sum_le (valuation k) fun i _ => ?_
          have h2 : valuation k (y i * x i) ≤ valuation k (((c * s⁻¹ : kˣ) : k) * s) := by
            rw [map_mul, map_mul]
            exact mul_le_mul' (hy i trivial) (hx i trivial)
          rwa [← Units.val_mul, inv_mul_cancel_right] at h2
        rw [h.eq_one h1, Circle.coe_one, mul_one]
      · simp [Set.indicator_of_notMem hy]
    simp only [this]
    rw [integral_indicator_const _ (isOpen_box _).measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    refine fourier_eq_zero_pi μ h (s := c * s⁻¹) (fun t ht y => ?_) (by simpa using hx)
    by_cases hy : y ∈ box n (c * s⁻¹)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem
        (show y + t ∈ box n (c * s⁻¹) from fun i _ => add_mem_cball (hy i trivial) (ht i trivial))]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro h1
      exact hy fun i _ => by simpa using add_mem_cball (h1 i trivial) (neg_mem_cball (ht i trivial))

theorem fourier_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) := by
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_,
    HasCompactSupport.intro (isCompact_box (c * s⁻¹)) fun y hy => fourier_eq_zero_pi μ h hs hy⟩
  have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport f, ψ (x ⬝ᵥ z) = ψ (x ⬝ᵥ y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => (ψ (q.2 ⬝ᵥ q.1), ψ (q.2 ⬝ᵥ y)) :=
      (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_fst)).prodMk
        (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_const))
    filter_upwards [h2.eventually_eq (y, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
  filter_upwards [h1] with z hz
  congr 1
  funext x
  by_cases hx : x ∈ tsupport f
  · rw [hz x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem fourier_inversion_pi (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∫ y, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∂μ =
      ((μ.real (box n s) * μ.real (box n (c * s⁻¹)) : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨s, ?_⟩
  set e : (n → k) → ℂ := (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) with he
  have h1 : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = ∫ x, f x * (e y * (ψ (y ⬝ᵥ x) : ℂ)) ∂μ := by
    intro y
    by_cases hy : y ∈ box n (c * s⁻¹)
    · simp [he, Set.indicator_of_mem hy, dotProduct_comm y]
    · simp [he, Set.indicator_of_notMem hy, fourier_eq_zero_pi μ h hs hy]
  have hei : Integrable e μ :=
    (integrable_indicator_iff (isOpen_box _).measurableSet).mpr
      (integrableOn_const (isCompact_box _).measure_lt_top.ne)
  have hfi : Integrable f μ := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hint : Integrable (Function.uncurry fun y x => f x * (e y * (ψ (y ⬝ᵥ x) : ℂ))) (μ.prod μ) := by
    have h2 := (hei.mul_prod hfi).mul_bdd (c := 1) (g := fun q : (n → k) × (n → k) => (ψ (q.1 ⬝ᵥ q.2) : ℂ))
      (Continuous.aestronglyMeasurable
        (continuous_subtype_val.comp (h.continuous.comp continuous_dot)))
      (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry]
    ring
  simp only [h1]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul, he, fourier_indicator_pi μ h s]
  have h3 : ∀ x, f x * (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ) * f 0) x := by
    intro x
    by_cases hx : x ∈ box n s
    · have := hs x hx 0
      rw [zero_add] at this
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, this, mul_comm]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_indicator_const _ (isOpen_box _).measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul]

theorem vol_mul_vol_dual {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν) (s : kˣ) :
    ν.real (cball s) * ν.real (cball (c * s⁻¹)) = 1 := by
  haveI := hν.1
  haveI := t2Space k
  have hcl : IsClopen (cball (1 : kˣ)) := ⟨(isCompact_cball 1).isClosed, isOpen_cball 1⟩
  have hf : (cball (1 : kˣ)).indicator (fun _ => (1 : ℂ)) ∈ SB k := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
      HasCompactSupport.intro (isCompact_cball 1) fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hx : x ∈ cball (1 : kˣ)
    · filter_upwards [hcl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]
  have h1 := (fourier_inversion ν h hf).symm.trans (hν.2 _ hf)
  rw [Set.indicator_of_mem (by simp [cball]), mul_one] at h1
  have h2 : ν.real (𝒪[k] : Set k) ^ 2 * nabs k c = 1 := by exact_mod_cast h1
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  rw [measureReal_cball, measureReal_cball, ← h2, h4]; ring

theorem fourier_pi_of_conductor {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧
      ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  refine ⟨fourier_mem_SB _ h hf, ?_⟩
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => ν) h hf
  have hb : ∀ r : kˣ, (Measure.pi fun _ : n => ν).real (box n r) = ν.real (cball r) ^ Fintype.card n := by
    intro r
    simp [Measure.real, box, Measure.pi_pi]
  rw [hs, hb, hb, ← mul_pow, vol_mul_vol_dual h hν]
  simp

theorem fourier_pi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), ∀ f ∈ SB (n → k), (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧ ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν f hf
  obtain ⟨c, h⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hc h1
  exact fourier_pi_of_conductor h hν hf

end GlobalTheory.SplitWeil.FourierPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
section
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.SatakeBound

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsBorelSph (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ) : Prop :=
  (∀ g : GL (Fin n) k, ∀ x ∈ KO k (Fin n), φ (g * x) = φ g) ∧
    ∀ b ∈ borel k (Fin n), ∀ t : Fin n → kˣ,
      (∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) → φ b = ∏ i, γ i ^ ord k (t i)

def HasBoundedSums (φ : GL (Fin n) k → ℂ) : Prop :=
  ∀ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)), (∀ x ∈ KO k (Fin n), ∀ c ∈ S, x • c ∈ S) →
    ‖∑ c ∈ S, φ c.out‖ ≤ S.card

theorem isBorelSph_one : IsBorelSph k (n := n) (fun _ => 1) fun _ => 1 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩

end GlobalTheory.SatakeBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero : ∀ {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ), AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k' ≠ 0 → Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  first | exact @GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | (intros; apply GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEqStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq : ∀ {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : (∀ l, V l) →ₘₗ[ℂ] ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l),
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) = a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  exact @GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
end

