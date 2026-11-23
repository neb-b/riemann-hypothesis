module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpNegMulSqrtDivPowLeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exp_neg_mul_div_rpow_pow_le_mul_sqrt : ∀ (a : ℝ) (D : ℕ), 0 < a → ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) / (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  first | exact @GlobalTheory.exp_neg_mul_sqrt_div_pow_le | exact GlobalTheory.exp_neg_mul_sqrt_div_pow_le | (intros; apply GlobalTheory.exp_neg_mul_sqrt_div_pow_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
section
noncomputable section

open scoped ContDiff Topology
open NumberField Matrix

namespace GlobalTheory.SmoothForms

section Chart

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G]

structure IsLieData (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) : Prop where
  anti : ∀ a b, σ (a * b) = σ b * σ a
  one : σ 1 = 1
  invol : ∀ a, σ (σ a) = a
  inj : Function.Injective j
  skew : ∀ X, σ X = -X ↔ ∃ Y, j Y = X
  mul : ∀ a b, σ a * a = 1 → σ b * b = 1 → s (a * b) = s a * s b

def expMap (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) (X : L) : G := s (NormedSpace.exp (j X))

def HasLog (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) : Prop :=
  ∃ Λ : 𝔸 → L, ContDiffAt ℝ ∞ Λ 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → NormedSpace.exp (j (Λ h)) = h) ∧
    ∀ᶠ X in 𝓝 (0 : L), Λ (NormedSpace.exp (j X)) = X

def Sm (e : L → G) (φ : G → ℂ) : Prop := ∀ g, ContDiff ℝ ∞ fun X : L => φ (g * e X)

def Der (e : L → G) (X : L) (φ : G → ℂ) : G → ℂ := fun g => deriv (fun t : ℝ => φ (g * e (t • X))) 0


open scoped ContDiff Topology in
open NumberField Matrix in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] in
theorem _root_.GlobalTheory.SmoothForms.contDiff_family [FiniteDimensional ℝ 𝔸] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸}
    {s : 𝔸 → G} (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s)
    (hl : _root_.GlobalTheory.SmoothForms.HasLog σ j) {φ : G → ℂ}
    (hφ : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * _root_.GlobalTheory.SmoothForms.expMap j s X)) 0)
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {c : P → 𝔸} (hc : ContDiff ℝ ∞ c)
    (hu : ∀ p, σ (c p) * c p = 1) (g : G) : ContDiff ℝ ∞ fun p => φ (g * s (c p)) := by
  have hmul := H.mul
  have anti := H.anti
  have invol := H.invol
  simp only [_root_.GlobalTheory.SmoothForms.expMap] at hφ
  haveI : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
  obtain ⟨Λ, hΛ, hexp, hlog⟩ := hl
  have hΛ0 : Λ 1 = 0 := by
    simpa using hlog.self_of_nhds
  rw [contDiff_iff_contDiffAt]
  intro p₀
  set u := c p₀
  have hu' : u * σ u = 1 := mul_eq_one_comm.mp (hu p₀)
  let k : P → 𝔸 := fun p => σ u * c p
  have hk : ContDiff ℝ ∞ k := contDiff_const.mul hc
  have hk0 : k p₀ = 1 := hu p₀
  have hku : ∀ p, σ (k p) * k p = 1 := by
    intro p
    simp only [k, anti, invol]
    calc σ (c p) * u * (σ u * c p) = σ (c p) * (u * σ u) * c p := by noncomm_ring
      _ = 1 := by rw [hu', mul_one, hu p]
  have hck : ∀ p, c p = u * k p := by
    intro p
    simp only [k]
    rw [← mul_assoc, hu', one_mul]
  have hev : ∀ᶠ p in 𝓝 p₀, NormedSpace.exp (j (Λ (k p))) = k p := by
    have := hk.continuous.continuousAt (x := p₀)
    rw [ContinuousAt, hk0] at this
    exact (this.eventually hexp).mono fun p hp => hp (hku p)
  have hF : ContDiffAt ℝ ∞ (fun p => φ ((g * s u) * s (NormedSpace.exp (j (Λ (k p)))))) p₀ := by
    have h1 : ContDiffAt ℝ ∞ (fun p => Λ (k p)) p₀ := by
      have : ContDiffAt ℝ ∞ Λ (k p₀) := by rw [hk0]; exact hΛ
      exact this.comp p₀ hk.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun X : L => φ ((g * s u) * s (NormedSpace.exp (j X)))) (Λ (k p₀)) := by
      rw [hk0, hΛ0]; exact hφ _
    exact ContDiffAt.comp (g := fun X : L => φ ((g * s u) * s (NormedSpace.exp (j X)))) p₀ h2 h1
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  rw [hp, hck p, hmul _ _ (hu p₀) (hku p), mul_assoc]

end Chart

section Words

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

def gelfA (E : Fin n → Fin n → A) (k : ℕ) : A :=
  ∑ idx : Fin (k + 1) → Fin n, (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).prod

def wordMap (E : Fin n → Fin n → A) (d : ℕ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ →ₗ[ℂ] A where
  toFun M := ∑ I, ∑ K, M I K • (List.ofFn fun a : Fin d => E (I a) (K a)).prod
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, mul_smul]

def filt (E : Fin n → Fin n → A) (d : ℕ) : Submodule ℂ A := ⨆ d' < d, LinearMap.range (wordMap E d')

def polar (n d : ℕ) (a b : Fin n) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∑ p, if I p = a ∧ K p = b ∧ ∀ q, q ≠ p → I q = K q then 1 else 0

def permMat (n d : ℕ) (π : Equiv.Perm (Fin d)) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => if I = K ∘ π then 1 else 0

end Words

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Sized {V : Type} [AddCommGroup V] [Module E V] (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ)
    (ν : V → ℝ) (B : ℝ) : Prop where
  symm : ∀ x y, h y x = star (h x y)
  nondeg : ∀ y, (∀ x, h y x = 0) → y = 0
  fg : Λ.FG
  stable : ∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ
  int : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)
  dual : ∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ
  two_le : 2 ≤ B
  nonneg : ∀ x, 0 ≤ ν x
  add_le : ∀ x y, ν (x + y) ≤ ν x + ν y
  smul_le : ∀ (a : E) x, ν (a • x) ≤ house a * ν x
  form_le : ∀ x y, house (h x y) ≤ ν x * ν y
  span : Submodule.span E {x | x ∈ Λ ∧ ν x ≤ B} = ⊤

open scoped ContDiff Topology in
open NumberField Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.SmoothForms.house_star (a : E) : house (star a) = house a := by
  have hs : star a = (NumberField.IsCMField.complexConj E) a := rfl
  have key : ∀ φ : E →+* ℂ, ‖canonicalEmbedding E (star a) φ‖ = ‖canonicalEmbedding E a φ‖ := by
    intro φ
    rw [canonicalEmbedding.apply_at, canonicalEmbedding.apply_at, hs,
      NumberField.IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  unfold house
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun φ => (key φ).le.trans (norm_le_pi_norm _ φ)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun φ => (key φ).ge.trans (norm_le_pi_norm _ φ)

variable (E)

def FrameSmall : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ[E] V →ₗ⋆[E] E)
    (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k

def ShortSmall : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ N : ℤ, N ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v ∈ Λ, v ≠ 0 ∧ house (h v v) ≤ C ∧ ν v ≤ B ^ k

def AnisoSmall : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ N : ℤ, N ≠ 0 → ∃ (S : Set E) (k : ℕ), S.Finite ∧ (0 : E) ∉ S ∧
    ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v ∈ Λ, h v v ∈ S ∧ ν v ≤ B ^ k

def OrthoSmall : Prop :=
  ∀ n : ℕ, ∀ N : ℤ, N ≠ 0 → ∃ (S : Set E) (k : ℕ), S.Finite ∧ (0 : E) ∉ S ∧
    ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (ν : V → ℝ) (B : ℝ), Module.finrank E V = n → Sized h Λ N ν B →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ∈ S ∧ ν (v i) ≤ B ^ k

end Lattices

end GlobalTheory.SmoothForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
section
open NumberField IsDedekindDomain MeasureTheory
open scoped Pointwise

namespace GlobalTheory


open Pointwise in
theorem measure_addFundamentalDomain_lt_top_of_cocompact {G : Type} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have hsub : F ⊆ ⋃ γ : Γ, ((γ +ᵥ K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨-(⟨γ, hγ⟩ : Γ), ?_, hg⟩
    rw [Set.mem_neg_vadd_set_iff]
    exact hk
  calc μ F ≤ μ (⋃ γ : Γ, ((γ +ᵥ K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

theorem meanSquare_addFundamentalDomain_of_cocompact : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) → (∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) → ∃ N : NNReal, ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = μ 𝓕 * N ∧ ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = (μ 𝓕).toReal * N := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov
  have : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G},
      IsAddFundamentalDomain Γ F μ → μ F ≠ 0 := fun μ _ F hF =>
    hF.measure_ne_zero (NeZero.ne μ)
  have hfin : ∀ (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G},
      IsAddFundamentalDomain Γ F μ → μ F ≠ ⊤ := fun μ _ F hF =>
    (measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ hF).ne
  have hex : ∃ (μ : Measure G) (𝓕 : Set G),
      μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
    obtain ⟨D, -, -, hD⟩ := exists_isAddFundamentalDomain_addSubgroup Γ
    have h0 := hne Measure.addHaar (hD _)
    have h1 := hfin Measure.addHaar (hD _)
    refine ⟨(Measure.addHaar D)⁻¹ • Measure.addHaar, D,
      Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
      hD _, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]
  refine ⟨hex, fun f hf hinv => ?_⟩
  obtain ⟨μ₀, F₀, hμ₀, hF₀, h1⟩ := hex
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ w, ‖f w‖ₑ ^ 2 ≤ ENNReal.ofReal C ^ 2 := fun w => by
    obtain ⟨γ, hγ, hk⟩ := hcov w
    have := hC _ hk
    rw [hinv γ hγ] at this
    rw [← ofReal_norm_eq_enorm]
    gcongr
  have hN : ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
    rw [setLIntegral_const, h1, mul_one]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨(∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal, fun μ F hμ hF => ?_⟩
  have key : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ =
      μ F * ((∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ₀).toNNReal : ENNReal) := by
    rw [ENNReal.coe_toNNReal hN]
    obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
    have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
    have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
    have e1 : μ F = μ F₀ := hF.measure_eq hF₀'
    have e2 : ∫⁻ w in F, ‖f w‖ₑ ^ 2 ∂μ = ∫⁻ w in F₀, ‖f w‖ₑ ^ 2 ∂μ :=
      hF.setLIntegral_eq hF₀' _ fun g x => by
        have := hinv g g.2 x
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← this]
        rfl
    rw [e1, e2, hc, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, h1]
    simp [ENNReal.smul_def]
  refine ⟨hne μ hF, hfin μ hF, key, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖f w‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow 2).aestronglyMeasurable]
  have : ∀ w, ENNReal.ofReal (‖f w‖ ^ 2) = ‖f w‖ₑ ^ 2 := fun w => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  simp only [this]
  rw [key, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubringStatement
section
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoStepUnipotent_compact_mod_subring : ∀ (S : Type) [Ring S] [TopologicalSpace S] [IsTopologicalRing S] (st : S →+ S) (S₀ : Subring S) (e₁ e₃ h : S) (K : Set S), Continuous st → (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → (∀ x ∈ S₀, st x ∈ S₀) → e₁ ∈ S₀ → h ∈ S₀ → e₁ * e₁ = e₁ → st e₁ = e₃ → e₁ * e₃ = 0 → e₃ * e₁ = 0 → h + h = 1 → (∀ x, h * x = x * h) → IsCompact K → (∀ x, ∃ y ∈ S₀, x - y ∈ K) → ∃ K' : Set Sˣ, IsCompact K' ∧ (∀ g ∈ K', (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0)) ∧ ∀ g : Sˣ, (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0) → ∃ γ : Sˣ, (st (γ : S) * (γ : S) = 1 ∧ ((γ : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((γ : S) - 1) * (1 - e₃) = 0) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧ γ * g ∈ K' := by
  first | exact @GlobalTheory.TwoStepUnipotent.compact_mod_subring | exact GlobalTheory.TwoStepUnipotent.compact_mod_subring | (intros; apply GlobalTheory.TwoStepUnipotent.compact_mod_subring <;> assumption)
end

