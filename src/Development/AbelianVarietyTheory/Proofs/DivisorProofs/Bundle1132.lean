module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFami
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.Cusp.SmoothParam

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]


omit [SecondCountableTopology G] [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem aestronglyMeasurable_out {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E]
    {Φ : G → E} (hΦ : Continuous Φ) (hinv : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (g : G)
    (μ : Measure (Quot (Γ.subgroupOf N))) :
    AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => Φ ((q.out : N) * g)) μ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hl : LeftInv (Γ.subgroupOf N) (fun n : N => Φ (n * g)) := fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _
  have hm : Measurable (fun n : N => Φ (n * g)) :=
    (hΦ.comp ((continuous_subtype_val).mul continuous_const)).measurable
  have hq : Measurable (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) := by
    refine measurable_from_quotient.2 ?_
    have e : (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) ∘ Quotient.mk'' = fun n : N => Φ (n * g) :=
      hl.lift_descend
    rw [e]; exact hm
  exact hq.aestronglyMeasurable


omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem exists_bound {T E : Type} [TopologicalSpace T] [NormedAddCommGroup E] (hc : Cocompact Γ N)
    {Ψ : G → T → E} (hΨ : Continuous fun p : G × T => Ψ p.1 p.2) (hinv : ∀ γ ∈ Γ, ∀ x t, Ψ (γ * x) t = Ψ x t)
    (g : G) {S : Set T} (hS : IsCompact S) : ∃ C, ∀ (n : N) t, t ∈ S → ‖Ψ (n * g) t‖ ≤ C := by
  obtain ⟨K, hK, hs⟩ := hc
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn (f := fun p : N × T => Ψ (p.1 * g) p.2)
    (hΨ.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)).continuousOn
  refine ⟨C, fun n t ht => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs n
  have e : Ψ (((γ * n : N) : G) * g) t = Ψ (n * g) t := by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _ _
  exact e ▸ hC (γ * n, t) ⟨hk, ht⟩

theorem hasFDerivAt_param {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hc : Cocompact Γ N) (H : G → (Fin k → ℝ) → E)
    (hinv : ∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) (hd : ∀ x, Differentiable ℝ (H x))
    (h0 : Continuous fun p : G × (Fin k → ℝ) => H p.1 p.2)
    (h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2) (g : G) (t₀ : Fin k → ℝ) :
    HasFDerivAt (fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N)
      (∫ q, fderiv ℝ (H ((q.out : N) * g)) t₀ ∂probMeasure Γ N) t₀ := by
  have := hc.isProbabilityMeasure
  have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
    rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
  obtain ⟨C, hC⟩ := exists_bound (Ψ := fun x t => fderiv ℝ (H x) t) hc h1 hinv' g (isCompact_closedBall t₀ 1)
  obtain ⟨C0, hC0⟩ := exists_bound (Ψ := H) hc h0 hinv g (isCompact_closedBall t₀ 1)
  have hm : ∀ t, AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => H ((q.out : N) * g) t) (probMeasure Γ N) :=
    fun t => aestronglyMeasurable_out (Φ := fun x => H x t) (h0.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv γ hγ x t) g _
  have hm' : AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => fderiv ℝ (H ((q.out : N) * g)) t₀)
      (probMeasure Γ N) :=
    aestronglyMeasurable_out (Φ := fun x => fderiv ℝ (H x) t₀) (h1.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv' γ hγ x t₀) g _
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds t₀ one_pos) (.of_forall hm)
    (Integrable.of_bound (hm t₀) C0 (.of_forall fun q => hC0 _ t₀ (Metric.mem_closedBall_self zero_le_one))) hm'
    (.of_forall fun q t ht => hC _ t (Metric.ball_subset_closedBall ht)) (integrable_const C)
    (.of_forall fun q t _ => (hd _ t).hasFDerivAt)


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem iteratedFDeriv_fderiv_eq {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin k → ℝ) → E) (m : ℕ) (t : Fin k → ℝ) :
    iteratedFDeriv ℝ m (fderiv ℝ f) t =
      (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E) (iteratedFDeriv ℝ (m + 1) f t) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_of_iteratedFDeriv_zero {X : Type} [TopologicalSpace X] {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : X → (Fin k → ℝ) → E}
    (h : Continuous fun p : X × (Fin k → ℝ) => iteratedFDeriv ℝ 0 (H p.1) p.2) :
    Continuous fun p : X × (Fin k → ℝ) => H p.1 p.2 := by
  have e : (fun p : X × (Fin k → ℝ) => H p.1 p.2) =
      fun p => continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E (iteratedFDeriv ℝ 0 (H p.1) p.2) := by
    funext p; simp [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  rw [e]; exact (continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E).continuous.comp h

theorem contDiff_param (hc : Cocompact Γ N) (g : G) {k : ℕ} (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : G → (Fin k → ℝ) → E),
      (∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) → (∀ x, ContDiff ℝ ∞ (H x)) →
      (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (H p.1) p.2) →
      ContDiff ℝ n fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N := by
  induction n with
  | zero =>
    intro E _ _ _ H hinv hs hm
    have h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2 := by
      refine continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) ?_
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ 0 (Fin k → ℝ) E).continuous.comp (hm 1)
    refine contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => ?_)
    exact (hasFDerivAt_param hc H hinv (fun x => (hs x).differentiable (by simp))
      (continuous_of_iteratedFDeriv_zero (hm 0)) h1 g t).continuousAt
  | succ n ih =>
    intro E _ _ _ H hinv hs hm
    have hm' : ∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (fderiv ℝ (H p.1)) p.2 := by
      intro m
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E).continuous.comp (hm (m + 1))
    have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
      rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih (fun x => fderiv ℝ (H x)) hinv'
      (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).2) hm', fun t => ?_⟩
    exact hasFDerivAt_param hc H hinv (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).1)
      (continuous_of_iteratedFDeriv_zero (hm 0))
      (continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) (hm' 0)) g t

end GlobalTheory.Cusp.SmoothParam

theorem GlobalTheory.Cusp.contDiff_constTermOn_param : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ]
    [LocallyCompactSpace N], GlobalTheory.Cusp.Cocompact Γ N → ∀ {k : ℕ} (F : G → (Fin k → ℝ) → ℂ),
    (∀ γ ∈ Γ, ∀ x t, F (γ * x) t = F x t) → (∀ x, ContDiff ℝ ∞ (F x)) →
    (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (F p.1) p.2) →
    ∀ g : G, ContDiff ℝ ∞ fun t => GlobalTheory.Cusp.constTermOn Γ N (fun x => F x t) g := by
  intro G _ _ _ _ _ _ Γ N _ _ hc k F hinv hs hm g
  exact contDiff_infty.2 fun n => GlobalTheory.Cusp.SmoothParam.contDiff_param hc g n F hinv hs hm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivRealOneParamProductLevel
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UAut.JointDer

theorem prod_ofFn_append {G : Type} [Monoid G] {d k : ℕ} (δ : Fin d → ℝ → G) (γ : Fin k → ℝ → G) (s : Fin d → ℝ)
    (t : Fin k → ℝ) :
    (List.ofFn fun i => Fin.append δ γ i (Fin.append s t i)).prod =
      (List.ofFn fun a => δ a (s a)).prod * (List.ofFn fun i => γ i (t i)).prod := by
  have e : (fun i => Fin.append δ γ i (Fin.append s t i)) = Fin.append (fun a => δ a (s a)) (fun i => γ i (t i)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  rw [e, List.ofFn_fin_append, List.prod_append]

theorem contDiff_append {d k : ℕ} : ContDiff ℝ ∞ fun q : (Fin d → ℝ) × (Fin k → ℝ) => Fin.append q.1 q.2 := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact (contDiff_apply ℝ (fun _ => ℝ) a).comp contDiff_fst
  · simp only [Fin.append_right]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_snd

theorem iteratedFDeriv_slice {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] {H : A × B → ℂ} (hH : ContDiff ℝ ∞ H) (m : ℕ) (a : A) (t : B) :
    iteratedFDeriv ℝ m (fun t => H (a, t)) t =
      (iteratedFDeriv ℝ m H (a, t)).compContinuousLinearMap fun _ => ContinuousLinearMap.inr ℝ A B := by
  have e : (fun t => H (a, t)) = (fun q => H ((a, 0) + q)) ∘ ContinuousLinearMap.inr ℝ A B := by
    funext t; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _
    (show ContDiff ℝ ∞ fun q => H ((a, 0) + q) from hH.comp (contDiff_const.add contDiff_id)) _
    (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem commute_prod_realLine {k : ℕ} {γ : Fin k → ℝ → GAd σ J} (hγ : ∀ i, IsRealLine σ J (γ i)) (t : Fin k → ℝ)
    {u : GAd σ J} (hu : u ∈ finPts σ J) : Commute (List.ofFn fun i => γ i (t i)).prod u := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  obtain ⟨w, τ, Z, -, h⟩ := hγ i
  obtain ⟨y, e, -⟩ := h (t i)
  show Commute (γ i (t i)) u
  rw [e]
  exact commute_embArch σ J y (mem_finPts_iff_forall.1 hu w)

end GlobalTheory.UAut.JointDer


open GlobalTheory.UAut.JointDer in
theorem GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) → (∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧ ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u) → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → IsSm σ J φ → ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ m : ℕ, Continuous fun p : GAd σ J × (Fin k → ℝ) => iteratedFDeriv ℝ m (fun t : Fin k → ℝ => φ (p.1 * (List.ofFn fun i => γ i (t i)).prod)) p.2 := by
  intro F E _ _ _ _ _ σ _ n J _ d δ hδ hchart φ hlev hsm k γ hγ m
  obtain ⟨U, hUo, hU⟩ := hlev
  obtain ⟨W, hW, s, hs, hWs⟩ := hchart _ (hUo.mem_nhds U.one_mem)
  set P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun i => γ i (t i)).prod with hP
  set Q : (Fin d → ℝ) → GAd σ J := fun s => (List.ofFn fun a => δ a (s a)).prod with hQ
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨x₀, t₀⟩ := p₀
  let H : (Fin d → ℝ) × (Fin k → ℝ) → ℂ := fun q => φ (x₀ * (Q q.1 * P q.2))
  have hH : ContDiff ℝ ∞ H := by
    have h1 := hsm (d + k) (Fin.append δ γ)
      (fun i => Fin.addCases (fun a => by simpa [Fin.append_left] using hδ a)
        (fun j => by simpa [Fin.append_right] using hγ j) i) x₀
    have h2 := h1.comp contDiff_append
    convert h2 using 1
    funext q
    simp [H, hP, hQ, prod_ofFn_append]
  have key : ∀ x, x₀⁻¹ * x ∈ W → ∀ t, φ (x * P t) = H (s (x₀⁻¹ * x), t) := by
    intro x hx t
    obtain ⟨u, huU, huf, e⟩ := hWs _ hx
    have hc : Commute (P t) u := commute_prod_realLine hγ t huf
    have hx' : x = x₀ * (Q (s (x₀⁻¹ * x)) * u) := by
      simp only [hQ]
      rw [← e]
      group
    calc φ (x * P t) = φ (x₀ * (Q (s (x₀⁻¹ * x)) * u) * P t) := by rw [← hx']
      _ = φ ((x₀ * (Q (s (x₀⁻¹ * x)) * P t)) * u) := by
          congr 1
          simp only [mul_assoc]
          rw [hc.eq]
      _ = H (s (x₀⁻¹ * x), t) := hU u huU huf _
  have hev : ∀ᶠ p : GAd σ J × (Fin k → ℝ) in 𝓝 (x₀, t₀),
      (iteratedFDeriv ℝ m H (s (x₀⁻¹ * p.1), p.2)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) =
      iteratedFDeriv ℝ m (fun t => φ (p.1 * P t)) p.2 := by
    have hmem : {p : GAd σ J × (Fin k → ℝ) | x₀⁻¹ * p.1 ∈ W} ∈ 𝓝 (x₀, t₀) :=
      (continuous_const.mul continuous_fst).continuousAt.preimage_mem_nhds (by simpa using hW)
    filter_upwards [hmem] with p hp
    rw [← iteratedFDeriv_slice hH, show (fun t => φ (p.1 * P t)) = fun t => H (s (x₀⁻¹ * p.1), t) from
      funext (key p.1 hp)]
  refine ContinuousAt.congr ?_ hev
  have hcont : Continuous fun q => (iteratedFDeriv ℝ m H q).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) :=
    (ContinuousMultilinearMap.continuous_precomp _).comp (hH.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hsx : ContinuousAt (fun p : GAd σ J × (Fin k → ℝ) => s (x₀⁻¹ * p.1)) (x₀, t₀) :=
    hs.comp_of_eq (continuous_const.mul continuous_fst).continuousAt (by simp)
  exact hcont.continuousAt.comp (hsx.prodMk continuousAt_snd)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryLocalComponentToLocalUnitaryGro
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem cLoc_fin_continuous {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) :
    Continuous (fun x : finU (E := E) (n := n) => cLoc w (x : UA E n)) := by
  have hf : Continuous ((pLoc E w).comp (pFin E)) := by
    show Continuous (fun x => pLoc E w (pFin E x))
    exact (RestrictedProduct.continuous_eval w).comp continuous_snd
  have hm : Continuous (((pLoc E w).comp (pFin E)).mapMatrix : Matrix (Fin n) (Fin n) (Ad E) →+* _) :=
    continuous_id.matrix_map hf
  exact (Continuous.units_map _ hm).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_toSub {X G : Type} [TopologicalSpace X] [Group G] [TopologicalSpace G] (H : Subgroup G) {f : X → G}
    (hf : Continuous f) (hH : ∀ x, f x ∈ H) : Continuous (fun x => toSub H (f x)) := by
  have : (fun x => toSub H (f x)) = fun x => (⟨f x, hH x⟩ : H) := by
    funext x; simp [toSub, hH x]
  rw [this]
  exact hf.subtype_mk _

theorem toSub_cLoc_continuous_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (hmem : ∀ x : finU (E := E) (n := n), cLoc w (x : UA E n) ∈ UL n w) :
    Continuous (fun x : finU (E := E) (n := n) => toSub (UL n w) (cLoc w (x : UA E n))) :=
  continuous_toSub _ (cLoc_fin_continuous w) hmem

theorem toSub_cLoc_fin_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ w : Pl E, Continuous (fun x : finU (E := E) (n := n) => toSub (UL n w) (cLoc w (x : UA E n))) := by
  intro E _ _ _ hE n w
  exact toSub_cLoc_continuous_of_mem w (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hE n w)

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMultiplicityCarriers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.SpanW

theorem iSup_wp3_eq_range_eH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → ∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hS hGS hCD hME hcar i
  obtain ⟨hCore, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hOk2 : A3.A.fam.Ok s := hOk.ok2
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk2.irr
  obtain ⟨h, -, -, -, hsum, -⟩ := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hCore hS hirr R.SF hSF i
  rw [← hsum]
  apply le_antisymm
  · refine iSup_le fun p => iSup₂_le fun c _ => ?_
    rw [hWc]
    exact le_iSup (fun c => Wcc R.toRealDat R.SF i c) c
  · refine iSup_le fun c => ?_
    by_cases h0 : Wcc R.toRealDat R.SF i c = ⊥
    · rw [h0]; exact bot_le
    · have hE0 : EEc R.toRealDat R.SF c ≠ ⊥ :=
        _root_.GlobalTheory.Hk3.eec_ne_bot_of_wcc_ne_bot R.toRealDat F.lv2 hOk2 hCore hS hGS hCD hME R.SF hSF i c h0
      obtain ⟨p, hp⟩ := hcar c (by rw [hE]; exact hE0)
      rw [← hWc]
      exact le_trans (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp) (le_iSup (fun p => R.Wp3 i p) p)

end GlobalTheory.SpanW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalComponentMemIntegralGLCofiniStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n), ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | exact GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | (intros; apply GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ChernDegreeBaseChange

theorem exists_baseChange {F E : Type} [Field F] [Field E] (ρ : F →+* E) (Y : Var F) :
    ∃ (Y' : Var E) (r : Y'.X ⟶ Y.X), Y'.dim = Y.dim ∧ IsPullback r Y'.str Y.str (spMap ρ) := by
  have H := IsPullback.of_hasPullback Y.str (spMap ρ)
  generalize Limits.pullback.fst Y.str (spMap ρ) = r at H
  generalize Limits.pullback.snd Y.str (spMap ρ) = q at H
  have hs : SmoothOfRelativeDimension Y.dim q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange Y.dim
    MorphismProperty.of_isPullback H Y.smooth_str
  have hg : GeometricallyIntegral q :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H Y.geometricallyIntegral_str
  have hc : GeometricallyConnected q :=
    ⟨fun _ _ y _ fst snd h =>
      have := GeometricallyIntegral.geometrically_isIntegral (f := q) y fst snd h
      inferInstance⟩
  obtain ⟨Y', e, hd, he⟩ := Var.exists_iso q Y.dim (ProjSpace.isProjOver_of_isPullback_spMap ρ H Y.isProjOver)
  refine ⟨Y', e.inv ≫ r, hd, ?_⟩
  refine H.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simpa using he.symm
  · simp
  · simp

theorem chernDegree_of_complex (h : GlobalTheory.Published.ChernDegreeComplex) : GlobalTheory.Published.ChernDegree := by
  intro F _ Y σ Δ L r hr φ hφ
  obtain ⟨Y', π, hd, H⟩ := exists_baseChange σ Y
  have := CxPts.compactSpace (RingHom.id ℂ) Y'.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (RingHom.id ℂ) Y'.isProjOver
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts Y'.str (RingHom.id ℂ) → CxPts Y.str σ, (∀ z, (m z).1 = z.1 ≫ π) ∧
      Function.Bijective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, bijective_bcMap H _⟩
  let Φ : CxPts Y'.str (RingHom.id ℂ) ≃ₜ CxPts Y.str σ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hb) (continuous_of_comp hm)
  have hΦ : ∀ z, (Φ z).1 = z.1 ≫ π := hm
  have hL' := LB.isLB_pull hr.isLB π
  obtain ⟨s, hs⟩ := exists_isRatSec hL'
  have hp := presents_divOfRatSec hL' hs
  obtain ⟨h₁, h₂⟩ := h Y' _ _ s hp (ChernTransfer.pullW hΦ φ) (ChernTransfer.isCInf_pullW hΦ hφ)
  have hi : Y'.inter (fun _ => divOfRatSec hL' hs) = Y.inter fun _ => Δ := by
    letI := σ.toAlgebra
    rw [Var.inter_eq_of_toPic_eq (fun _ => hL') (fun _ => hp.toPic_eq),
      Var.inter_eq_of_toPic_eq (fun _ => hr.isLB) (fun _ => hr.toPic_eq), hd]
    exact FieldChangeInter.interNum_pull (f := Y.str) (f' := Y'.str) H (L := fun _ => L) fun _ => hr.isLB
  have hsm : SmoothOfRelativeDimension Y.dim Y'.str := hd ▸ Y'.smooth_str
  have e (ε) := ChernTransfer.chernPart_pullW hΦ (AnRead.all _ _ Y.dim) (AnRead.all _ _ Y.dim) hφ ε
  rw [hi] at h₂
  rw [hd] at h₁ h₂
  simp only [Weight.ChernIntegrableOn, Weight.chernInt, integrableOn_univ, Measure.restrict_univ, e,
    integral_map_equiv, integrable_map_equiv] at h₁ h₂ ⊢
  exact ⟨h₁, h₂⟩

end GlobalTheory.ChernDegreeBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthEqChartValueAndSumStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧ ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  first | exact @GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | exact GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | (intros; apply GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ c : AlgChart X.str σ X.dim, DifferentiableOn ℂ (c.e ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.e.source) := by
  first | exact @GlobalTheory.GoodTop.holoChart_trans_algChart | exact GlobalTheory.GoodTop.holoChart_trans_algChart | (intros; apply GlobalTheory.GoodTop.holoChart_trans_algChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancySubQCartierCoeffNonpos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem GlobalTheory.PairStep.discrep_sub_le_zero_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ)
    (Δ D : X → ℚ) (η : RatForms p n) (x : X) (m mD : ℕ) (gG fD : X.functionFieldˣ) (δ : ℚ),
    IsEffQDiv Δ → IsQCart D → δ ≤ 1 → 0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) →
    ∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing x) → discrep E η m gG - (1 - δ) * (E.ord fD / mD) ≤ 0 := by
  intro X _ _ _ p n Δ D η x m mD gG fD δ hΔ hD hδ hm hmD hlog hDz E hE
  obtain ⟨z, hzx, hEz⟩ := (isPrimeOf_placeEquiv E x).1 hE
  rw [hlog.discrep_eq_neg hm hzx hEz, ← hDz z hzx E hEz]
  have h1 : 0 ≤ Δ z := hΔ.nonneg z
  have h2 : 0 ≤ D z := by
    obtain ⟨m₀, D₀, -, hD₀, rfl⟩ := hD
    refine div_nonneg (Int.cast_nonneg ?_) (Nat.cast_nonneg m₀)
    obtain ⟨g, hg⟩ := D₀.exists_isEqn z
    obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hD₀ z g hg
    by_cases hz : Order.coheight z = 1
    · rw [hg.mult_eq, ← ha, ord_algebraMap hz fun h => g.ne_zero (by rw [← ha, h, map_zero])]
      exact Int.natCast_nonneg _
    · rw [hg.mult_eq, Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have h3 : 0 ≤ 1 - δ := by linarith
  nlinarith [mul_nonneg h3 h2]
end

