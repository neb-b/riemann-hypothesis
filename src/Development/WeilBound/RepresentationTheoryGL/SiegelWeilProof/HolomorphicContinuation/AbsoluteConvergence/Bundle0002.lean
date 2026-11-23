module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol
section
noncomputable section

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

def BanachHol : Prop := ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (U : Set ℂ) (F : ℂ → X → ℂ), IsOpen U →
  ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  ∃ Φ : ℂ → C(X, ℂ), DifferentiableOn ℂ Φ U ∧ ∀ z ∈ U, ∀ x, Φ z x = F z x

def DslopeFam : Prop := ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] (U : Set ℂ) (s₀ : ℂ) (F : ℂ → X → ℂ),
  IsOpen U → s₀ ∈ U → ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  (∀ x, F s₀ x = 0) →
  ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ univ) ∧
    ∀ x, DifferentiableOn ℂ (fun z => dslope (fun z => F z x) s₀ z) U

def FactorL : Prop := ∀ (G : Type) [TopologicalSpace G] (S : Submodule ℂ (G → ℂ)) (l : (G → ℂ) → ℂ) (C : Set G),
  IsCompact C → (∀ F ∈ S, Continuous F) → (∀ (a : ℂ), ∀ F ∈ S, ∀ F' ∈ S, l (a • F + F') = a * l F + l F') →
  (∀ F ∈ S, ∀ M : ℝ, (∀ x ∈ C, ‖F x‖ ≤ M) → ‖l F‖ ≤ M) →
  ∃ L : C(C, ℂ) →L[ℂ] ℂ, ∀ F ∈ S, ∀ (hF : Continuous F), l F = L ⟨fun x => F x, hF.comp continuous_subtype_val⟩

def KRCpt : Prop := ∀ n : ℕ, CompactSpace (KR n)

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSec
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def DN (ε : Fin m → Bool) (t : ℝ) (h : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  C (Complex.I * t) * (∑ i, ∑ j, C (h i j) * Qp ε j i) * R

def eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) * pderiv (a, j, false) R +
    (∑ i, X (a, i, true) * C (star (H i j))) * pderiv (a, j, true) R)

def DM (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  C ((m : ℂ) * H.trace) * R + eulH H R -
    C (2 * (c : ℂ)) * (∑ i, ∑ j, C (H i j) * (Qb ε true j i + Qb ε false j i)) * R

def SecDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n),
    R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) → ∀ (y : GR n)
    (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian →
    (∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL (DN ε t H R) ((k : GR n) * y)‖ ≤ δ) ∧
    (∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL (DM ε c H R) ((k : GR n) * y)‖ ≤ δ)

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GaussPart
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def bS (X : Fin n → ℝ) (h : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) * b * diagonal (fun j => (Real.exp (-(h * X j)) : ℂ))

def GaussPart : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (X : Fin n → ℝ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    ∀ Q : PX m n, HasDerivAt (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b))
      (secN ε c t (dil c X Q) b) 0

def GroupPart : Prop :=
  ∀ (n : ℕ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    (∀ s s', a (s + s') = a s * a s') ∧ a 0 = 1 ∧ (∀ s, IsUp (a s)) ∧ Continuous a ∧
    (∀ y : GR n, IsUp y → ∀ s, IsUp (y * a s)) ∧
    (∀ (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∃ (y₁ g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
      mR g = JJ n * nU b ∧ y = y₁ * g) ∧
    (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), mR g = JJ n * nU b → ∀ h, mR (a h * g * a h) = JJ n * nU (bS X h b)) ∧
    (∀ y : GR n, (mR y).toBlocks₂₁.det ≠ 0 → ∀ s, (mR (y * a s)).toBlocks₂₁.det ≠ 0) ∧
    Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ∧
    ∀ (p q : ℕ) (e : ℤ) (h : ℝ), F0 p q e (a (-h)) = Complex.exp (-((h * ((p + q : ℕ) * ∑ j, X j) : ℝ) : ℂ))

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam
section
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex

namespace PositivityTheory.Rg.Sw.AbsSt.HP

variable {X : Type} [TopologicalSpace X]

theorem eventually_unif {C : Set X} {U K : Set ℂ} {F : X → ℂ → ℂ}
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hK : IsCompact K) (hKU : K ⊆ U) {x₀ : X} (hx₀ : x₀ ∈ C)
    {η : ℝ} (hη : 0 < η) : ∀ᶠ x in 𝓝 x₀, ∀ ζ ∈ K, x ∈ C → ζ ∈ U → ‖F x ζ - F x₀ ζ‖ < η := by
  have key : ∀ ζ ∈ K, ∀ᶠ p : X × ℂ in 𝓝 (x₀, ζ), p.1 ∈ C → p.2 ∈ U → ‖F p.1 p.2 - F x₀ p.2‖ < η := by
    intro ζ hζ
    have hc := hF (x₀, ζ) ⟨hx₀, hKU hζ⟩
    have h1 : ∀ᶠ p : X × ℂ in 𝓝 (x₀, ζ), p ∈ C ×ˢ U → dist (F p.1 p.2) (F x₀ ζ) < η / 2 :=
      eventually_nhdsWithin_iff.mp (hc.eventually (Metric.ball_mem_nhds _ (half_pos hη)))
    have hg : Tendsto (fun p : X × ℂ => (x₀, p.2)) (𝓝 (x₀, ζ)) (𝓝 (x₀, ζ)) := by
      have hcont : Continuous (fun p : X × ℂ => (x₀, p.2)) := by fun_prop
      simpa using hcont.tendsto (x₀, ζ)
    have h2 := hg.eventually h1
    filter_upwards [h1, h2] with p hp1 hp2 hpC hpU
    have a := hp1 ⟨hpC, hpU⟩
    have b : dist (F x₀ p.2) (F x₀ ζ) < η / 2 := hp2 ⟨hx₀, hpU⟩
    rw [← dist_eq_norm]
    calc dist (F p.1 p.2) (F x₀ p.2) ≤ dist (F p.1 p.2) (F x₀ ζ) + dist (F x₀ p.2) (F x₀ ζ) :=
          dist_triangle_right _ _ _
      _ < η / 2 + η / 2 := add_lt_add a b
      _ = η := add_halves η
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x ζ => x ∈ C → ζ ∈ U → ‖F x ζ - F x₀ ζ‖ < η) key] with x hx ζ hζ hxC hζU
  exact hx ζ hζ hxC hζU

theorem continuousOn_deriv {C : Set X} {U : Set ℂ} {F : X → ℂ → ℂ} (hU : IsOpen U)
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ x ∈ C, DifferentiableOn ℂ (F x) U) :
    ContinuousOn (fun y : X × ℂ => deriv (F y.1) y.2) (C ×ˢ U) := by
  intro ⟨x₀, z₀⟩ ⟨hx₀, hz₀⟩
  have hT : TendstoLocallyUniformlyOn F (F x₀) (𝓝[C] x₀) U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [nhdsWithin_le_nhds (eventually_unif hF hK hKU hx₀ hε), self_mem_nhdsWithin]
      with x hx hxC ζ hζ
    rw [dist_comm, dist_eq_norm]
    exact hx ζ hζ hxC (hKU hζ)
  have hD : ∀ᶠ x in 𝓝[C] x₀, DifferentiableOn ℂ (F x) U := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hd x hx
  have hT' := hT.deriv hD hU
  have hc : ContinuousAt (deriv (F x₀)) z₀ :=
    (((hd x₀ hx₀).deriv hU).continuousOn z₀ hz₀).continuousAt (hU.mem_nhds hz₀)
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  obtain ⟨t, ht, hA⟩ := (Metric.tendstoLocallyUniformlyOn_iff.mp hT') (ε / 2) (half_pos hε) z₀ hz₀
  have hB := (Metric.continuousAt_iff'.mp hc) (ε / 2) (half_pos hε)
  have hB' : ∀ᶠ y in 𝓝[U] z₀, y ∈ t ∧ dist (deriv (F x₀) y) (deriv (F x₀) z₀) < ε / 2 :=
    Filter.inter_mem ht (nhdsWithin_le_nhds hB)
  rw [nhdsWithin_prod_eq]
  filter_upwards [Filter.prod_mem_prod hA hB'] with q hq
  have h1 : dist (deriv (F x₀) q.2) (deriv (F q.1) q.2) < ε / 2 := hq.1 q.2 hq.2.1
  have h2 : dist (deriv (F x₀) q.2) (deriv (F x₀) z₀) < ε / 2 := hq.2.2
  show dist (deriv (F q.1) q.2) (deriv (F x₀) z₀) < ε
  have h3 := dist_triangle (deriv (F q.1) q.2) (deriv (F x₀) q.2) (deriv (F x₀) z₀)
  rw [dist_comm] at h1
  linarith

theorem eqOn_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ} (h : EqOn f g U) :
    ∀ r : ℕ, EqOn (iteratedDeriv r f) (iteratedDeriv r g) U := by
  intro r
  induction r with
  | zero => simpa using h
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact (ih.eventuallyEq_of_mem (hU.mem_nhds hz)).deriv_eq

variable [MeasurableSpace X] [BorelSpace X]

theorem aesm_of {μ : Measure X} {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0) {f : X → ℂ}
    (hf : ContinuousOn f C) : AEStronglyMeasurable f μ := by
  set t := (toMeasurable μ Cᶜ)ᶜ with ht
  have htm : MeasurableSet t := (measurableSet_toMeasurable μ Cᶜ).compl
  have htC : t ⊆ C := by
    intro x hx
    by_contra hxC
    exact hx (subset_toMeasurable μ Cᶜ hxC)
  have hμ : μ.restrict t = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have e : {a | ¬ a ∈ t} = toMeasurable μ Cᶜ := by
      ext a
      simp [ht]
    rw [e, measure_toMeasurable]
    exact hCn
  have hh := hf.aestronglyMeasurable_of_subset_isCompact (μ := μ) hC htm htC
  rwa [hμ] at hh

theorem hasDerivAt_int {μ : Measure X} [IsFiniteMeasure μ] {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0)
    {U : Set ℂ} {F : X → ℂ → ℂ} (hU : IsOpen U)
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ x ∈ C, DifferentiableOn ℂ (F x) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) : HasDerivAt (fun z => ∫ x, F x z ∂μ) (∫ x, deriv (F x) z₀ ∂μ) z₀ := by
  have hcz : ∀ z ∈ U, ContinuousOn (fun x => F x z) C := fun z hz =>
    hF.comp (by fun_prop : Continuous fun x : X => (x, z)).continuousOn (fun x hx => ⟨hx, hz⟩)
  have hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun x => F x z) μ :=
    fun z hz => aesm_of hC hCn (hcz z hz)
  have hae : ∀ᵐ x ∂μ, x ∈ C := ae_iff.mpr hCn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hsub : closedBall z₀ (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hD := continuousOn_deriv hU hF hd
  obtain ⟨M, hM⟩ := (hC.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    (hD.mono (prod_mono subset_rfl hsub))
  obtain ⟨M0, hM0⟩ := (hC.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    (hF.mono (prod_mono subset_rfl hsub))
  have hint : Integrable (fun x => F x z₀) μ := by
    refine Integrable.of_bound (hmeas z₀ hz₀) M0 ?_
    filter_upwards [hae] with x hx
    exact hM0 (x, z₀) ⟨hx, mem_closedBall_self (half_pos hε).le⟩
  have hcd : ContinuousOn (fun x => deriv (F x) z₀) C :=
    hD.comp (by fun_prop : Continuous fun x : X => (x, z₀)).continuousOn (fun x hx => ⟨hx, hz₀⟩)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z x => F x z)
    (F' := fun z x => deriv (F x) z) (bound := fun _ => M)
    (closedBall_mem_nhds z₀ (half_pos hε))
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) hmeas) hint (aesm_of hC hCn hcd)
    (by filter_upwards [hae] with x hx z hz using hM (x, z) ⟨hx, hz⟩)
    (integrable_const M)
    (by
      filter_upwards [hae] with x hx z hz
      exact (((hd x hx) z (hsub hz)).differentiableAt (hU.mem_nhds (hsub hz))).hasDerivAt)
  exact key.2

theorem main {μ : Measure X} [IsFiniteMeasure μ] {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0)
    {U : Set ℂ} (hU : IsOpen U) : ∀ (r : ℕ) (F : X → ℂ → ℂ), ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U) →
      (∀ x ∈ C, DifferentiableOn ℂ (F x) U) →
      ∀ z ∈ U, iteratedDeriv r (fun z => ∫ x, F x z ∂μ) z = ∫ x, iteratedDeriv r (F x) z ∂μ := by
  intro r
  induction r with
  | zero =>
    intro F _ _ z _
    simp
  | succ n ih =>
    intro F hF hd z hz
    have hEq : EqOn (deriv (fun z => ∫ x, F x z ∂μ)) (fun z => ∫ x, deriv (F x) z ∂μ) U :=
      fun w hw => (hasDerivAt_int hC hCn hU hF hd hw).deriv
    rw [iteratedDeriv_succ', eqOn_iteratedDeriv hU hEq n hz,
      ih (fun x => deriv (F x)) (continuousOn_deriv hU hF hd) (fun x hx => (hd x hx).deriv hU) z hz]
    simp_rw [iteratedDeriv_succ']

end PositivityTheory.Rg.Sw.AbsSt.HP

namespace PositivityTheory.Rg.Sw.AbsSt

theorem holParam : HolParam := by
  intro X _ _ _ μ _ C hC hCn U F hU hF hd
  exact ⟨fun z hz => (HP.hasDerivAt_int hC hCn hU hF hd hz).differentiableAt.differentiableWithinAt,
    fun z hz r => HP.main hC hCn hU r F hF hd z hz⟩

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.InGBlocks
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.IwaPf

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [JJ, fromBlocks_multiply, Matrix.one_apply]

theorem inG_blocks (g : M2 n) (h : InG g) :
    g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁ = 0 ∧
    g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂ = 1 ∧
    g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂ = 0 := by
  have h' := h
  unfold InG at h'
  rw [← fromBlocks_toBlocks g, fromBlocks_conjTranspose, JJ, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at h'
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; abel
  · rw [← h2]; abel
  · rw [← h4]; abel

theorem inG_rows (g : M2 n) (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := JJ_mul_self
  have h1 : (-(JJ n * gᴴ * JJ n)) * g = 1 := by
    have e : gᴴ * JJ n * g = JJ n := h
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, e, hJ, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have h3 : g * (JJ n * gᴴ * JJ n) = -1 := by
    rw [Matrix.mul_neg] at h2
    exact neg_eq_iff_eq_neg.mp h2
  calc g * JJ n * gᴴ = -(g * (JJ n * gᴴ * JJ n) * JJ n) := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    _ = JJ n := by rw [h3, Matrix.neg_mul, Matrix.one_mul, neg_neg]

theorem key (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : aᴴ * c - cᴴ * a = 0) (E2 : aᴴ * d - cᴴ * b = 1)
    (E3 : bᴴ * d - dᴴ * b = 0) (s : ℂ) :
    (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b) = (star s - s) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have e := congrArg conjTranspose E2
    simpa [conjTranspose_sub, conjTranspose_mul] using e
  have expand : (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b)
      = (star s * s) • (aᴴ * c - cᴴ * a) + star s • (aᴴ * d - cᴴ * b)
        - s • (dᴴ * a - bᴴ * c) + (bᴴ * d - dᴴ * b) := by
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [expand, E1, E2, E2', E3]
  module

theorem det_ne (g : M2 n) (h : InG g) (s : ℂ) (hs : star s - s ≠ 0) : (s • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  obtain ⟨E1, E2, E3⟩ := inG_blocks g h
  intro hdet
  obtain ⟨v, hv, hYv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have K := key g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ E1 E2 E3 s
  set X := s • g.toBlocks₁₁ + g.toBlocks₁₂
  set Y := s • g.toBlocks₂₁ + g.toBlocks₂₂
  have L : star v ⬝ᵥ ((Xᴴ * Y - Yᴴ * X) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_zero, zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec,
      hYv, star_zero, zero_dotProduct, neg_zero]
  rw [K, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at L
  rcases mul_eq_zero.mp L with h0 | h0
  · exact hs h0
  · exact hv (dotProduct_star_self_eq_zero.mp h0)

end PositivityTheory.Rg.Sw.AbsSt.IwaPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpA
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.LocOpA

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [← fromBlocks_one, fromBlocks_neg]
  simp [JJ, fromBlocks_multiply]

theorem inG_blocks {g : M2 n} (h : InG g) :
    -(g.toBlocks₂₁ᴴ * g.toBlocks₁₁) + g.toBlocks₁₁ᴴ * g.toBlocks₂₁ = 0 ∧
    -(g.toBlocks₂₁ᴴ * g.toBlocks₁₂) + g.toBlocks₁₁ᴴ * g.toBlocks₂₂ = 1 ∧
    -(g.toBlocks₂₂ᴴ * g.toBlocks₁₁) + g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = -1 ∧
    -(g.toBlocks₂₂ᴴ * g.toBlocks₁₂) + g.toBlocks₁₂ᴴ * g.toBlocks₂₂ = 0 := by
  have h' := h
  unfold InG at h'
  rw [← fromBlocks_toBlocks g] at h'
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, Matrix.neg_mul] at h'
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h'
  exact ⟨h1, h2, h3, h4⟩

theorem key_identity {g : M2 n} (h : InG g) (s : ℂ) (hs : star s = -s) :
    (s • g.toBlocks₁₁ + g.toBlocks₁₂)ᴴ * (s • g.toBlocks₂₁ + g.toBlocks₂₂) -
      (s • g.toBlocks₂₁ + g.toBlocks₂₂)ᴴ * (s • g.toBlocks₁₁ + g.toBlocks₁₂) = (-(2 * s)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := inG_blocks h
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set C := g.toBlocks₂₁
  set D := g.toBlocks₂₂
  have e1 : Aᴴ * C = Cᴴ * A := by rw [← sub_eq_zero, sub_eq_neg_add]; exact h1
  have e2 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h2]; abel
  have e3 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h3]; abel
  have e4 : Bᴴ * D = Dᴴ * B := by rw [← sub_eq_zero, sub_eq_neg_add]; exact h4
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [e1, e2, e3, e4, hs]
  module

theorem det_ne_zero_of_key {P Q : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : c ≠ 0) (hk : Pᴴ * Q - Qᴴ * P = c • 1) :
    Q.det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have e : star x ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ x) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
      dotProduct_zero, dotProduct_mulVec, ← Matrix.star_mulVec, hx, star_zero, zero_dotProduct, sub_zero]
  rw [hk] at e
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at e
  rcases e with e | e
  · exact hc e
  · exact hx0 (dotProduct_star_self_eq_zero.1 e)

theorem det_first_block_ne_zero_group {g : M2 n} (h : InG g) : (u1 g).det ≠ 0 := by
  have hk := key_identity h Complex.I (by simp)
  refine det_ne_zero_of_key (c := -(2 * Complex.I)) (P := Complex.I • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_
  unfold u1
  exact hk

theorem det_second_cayley_block_ne {g : M2 n} (h : InG g) : (u2 g).det ≠ 0 := by
  have hk := key_identity h (-Complex.I) (by simp)
  refine det_ne_zero_of_key (c := -(2 * -Complex.I)) (P := (-Complex.I) • g.toBlocks₁₁ + g.toBlocks₁₂) (by simp) ?_
  unfold u2
  rw [← neg_smul]
  exact hk

def linv (M : M2 n) : M2 n := -(JJ n * Mᴴ * JJ n)

theorem linv_mul {M : M2 n} (h : InG M) : linv M * M = 1 := by
  unfold linv InG at *
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, h, JJ_mul_JJ, neg_neg]

theorem mul_linv {M : M2 n} (h : InG M) : M * linv M = 1 := mul_eq_one_comm.1 (linv_mul h)

def mkG (M : M2 n) (h : InG M) : GR n := ⟨⟨M, linv M, mul_linv h, linv_mul h⟩, h⟩

@[simp] theorem mR_mkG (M : M2 n) (h : InG M) : mR (mkG M h) = M := rfl

theorem inG_of (g : GR n) : InG (mR g) := g.2

theorem continuous_mR : Continuous (fun g : GR n => mR g) := by unfold mR; fun_prop

theorem continuous_mkG {X : Type} [TopologicalSpace X] {f : X → M2 n} (hf : Continuous f) (h : ∀ x, InG (f x)) :
    Continuous (fun x => mkG (f x) (h x)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact hf
  change Continuous fun x => linv (f x)
  unfold linv
  fun_prop

theorem herm_isHermitian (x : Fin n → Fin n → ℝ) : (herm x).IsHermitian := by
  ext i j
  refine Complex.ext ?_ ?_ <;> (simp [herm, conjTranspose_apply]; try ring)

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG nU JJ
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one, conjTranspose_zero, hb.eq]
  simp

theorem continuous_herm : Continuous (herm (n := n)) := by
  unfold herm
  fun_prop

def nbEl (x : Fin n → Fin n → ℝ) : GR n := mkG (nU (herm x)) (inG_nU (herm_isHermitian x))

theorem continuous_nbEl : Continuous (nbEl (n := n)) := by
  unfold nbEl
  refine continuous_mkG ?_ _
  unfold nU
  exact Continuous.matrix_fromBlocks continuous_const continuous_herm continuous_const continuous_const

end PositivityTheory.Rg.Sw.AbsSt.LocOpA
end
end

