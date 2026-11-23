module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormSheetedIffRootFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem monic_simpleRoot_isolated {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ)
    (hcont : ∀ j, ContinuousAt (a j) t)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hroot : τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0) :
    ∃ ε > 0, ∀ s, dist s t < ε → ∀ T₁ T₂ : ℂ, dist T₁ τ < ε → dist T₂ τ < ε →
      T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ) = 0 → T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ) = 0 → T₁ = T₂ := by

  set D : (Fin d → ℂ) × ℂ × ℂ → ℂ := fun v =>
    ∑ m ∈ Finset.range N, v.2.1 ^ m * v.2.2 ^ (N - 1 - m) +
      ∑ j : Fin N, a j v.1 * ∑ m ∈ Finset.range (j : ℕ), v.2.1 ^ m * v.2.2 ^ ((j : ℕ) - 1 - m) with hDdef
  have hkey : ∀ s T₁ T₂, (T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ)) - (T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ)) =
      D (s, T₁, T₂) * (T₁ - T₂) := by
    intro s T₁ T₂
    rw [hDdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hc : ∀ j, ContinuousAt (fun v : (Fin d → ℂ) × ℂ × ℂ => a j v.1) (t, τ, τ) :=
    fun j => (hcont j).comp continuousAt_fst
  have hcD : ContinuousAt D (t, τ, τ) := by
    rw [hDdef]
    fun_prop (disch := assumption)
  have hD0 : D (t, τ, τ) ≠ 0 := by
    have h1 := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ) (by
      simpa [Polynomial.eval₂_finsetSum] using hroot)
    convert h1 using 1
    simp only [hDdef, geom_sum₂_self, Polynomial.derivative_add, Polynomial.derivative_X_pow,
      Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, RingHom.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcD.eventually_ne hD0)
  refine ⟨ε, hε, fun s hs T₁ T₂ h₁ h₂ hr₁ hr₂ => ?_⟩
  have hne : D (s, T₁, T₂) ≠ 0 := hball (by simp [Prod.dist_eq, hs, h₁, h₂])
  have h := hkey s T₁ T₂
  rw [hr₁, hr₂, sub_zero, eq_comm] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hne)

theorem PrimitiveFormSheetedIffRootFull.proof : PrimitiveFormSheetedIffRootFull.Statement := by
  intro σ _ X w d A ℓ N a δ q ha hδ hq hP hsep hQ

  obtain ⟨UA, hUA, hUAo, hwUA⟩ := eventually_nhds_iff.1
    ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt).and hsep)))

  obtain ⟨UX, hUX, hUXo, hwUX⟩ := eventually_nhds_iff.1 (hP.and (eventually_all.2 hQ))
  set S : Set (σ → ℂ) := UX ∩ A ⁻¹' UA with hSdef
  have hSo : IsOpen S := hUXo.inter (hUAo.preimage A.continuous)
  set D : Set (Fin d → ℂ) := UA ∩ δ ⁻¹' {0}ᶜ with hDdef
  have hDo : IsOpen D := ContinuousOn.isOpen_inter_preimage
    (fun y hy => (hUA y hy).2.1.continuousAt.continuousWithinAt) hUAo isOpen_compl_singleton

  have hrep : ∀ x ∈ X, x ∈ S → δ (A x) ≠ 0 →
      (fun i => (∑ j, q i j (A x) * ℓ x ^ (j : ℕ)) / δ (A x)) = x := by
    intro x hxX hxS hδx
    funext i
    rw [← (hUX x hxS.1).2 i hxX, mul_div_cancel_left₀ _ hδx]
  filter_upwards [hSo.mem_nhds ⟨hwUX, hwUA⟩] with z hzS hzX hδz W hWo hzW
  have hzD : A z ∈ D := ⟨hzS.2, hδz⟩
  constructor
  · rintro ⟨O, V, g, hOo, hVo, hzV, hg, hAg, hXV⟩
    have hzg : z ∈ g '' O := by rw [← hXV]; exact ⟨hzX, hzV⟩
    obtain ⟨t₀, ht₀, hgt₀⟩ := hzg
    have hAz : A z = t₀ := by rw [← hgt₀, hAg t₀ ht₀]
    subst hAz
    have hO'o : IsOpen ((O ∩ g ⁻¹' (S ∩ W)) ∩ D) :=
      (hg.continuousOn.isOpen_inter_preimage hOo (hSo.inter hWo)).inter hDo
    refine ⟨(O ∩ g ⁻¹' (S ∩ W)) ∩ D, fun s => ℓ (g s), hO'o,
      ⟨⟨ht₀, by rw [Set.mem_preimage, hgt₀]; exact ⟨hzS, hzW⟩⟩, hzD⟩,
      fun s hs => (ℓ.analyticAt (g s)).comp (hg s hs.1.1), by simp only [hgt₀], fun s hs => ?_⟩
    have hgXV : g s ∈ X ∩ V := by rw [hXV]; exact Set.mem_image_of_mem g hs.1.1
    have hgs : (fun i => (∑ j, q i j s * ℓ (g s) ^ (j : ℕ)) / δ s) = g s := by
      have e := hrep (g s) hgXV.1 hs.1.2.1 (by rw [hAg s hs.1.1]; exact hs.2.2)
      rwa [hAg s hs.1.1] at e
    beta_reduce
    rw [hgs]
    exact ⟨⟨hgXV.1, hs.1.2.2⟩, hAg s hs.1.1, rfl⟩
  · rintro ⟨O, r, hOo, hzO, hr, hrz, hfull⟩
    set H : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hHdef
    have hfull' : ∀ s ∈ O, H s ∈ X ∩ W ∧ A (H s) = s ∧ ℓ (H s) = r s := hfull
    have hH : AnalyticOnNhd ℂ H (O ∩ D) := by
      intro s hs
      refine AnalyticAt.pi fun i => ?_
      exact (Finset.analyticAt_fun_sum _ fun j _ =>
        ((hUA s hs.2.1).2.2.1 i j).mul ((hr s hs.1).pow _)).div (hUA s hs.2.1).2.1 hs.2.2
    have hHz : H (A z) = z := by
      have e := hrep z hzX hzS hδz
      rw [← hrz] at e
      exact e
    obtain ⟨ε, hε, hiso⟩ := monic_simpleRoot_isolated a (A z) (ℓ z)
      (fun j => ((hUA (A z) hzS.2).1 j).continuousAt) ((hUA (A z) hzS.2).2.2.2 hδz) ((hUX z hzS.1).1 hzX)
    set B : Set (σ → ℂ) := S ∩ ℓ ⁻¹' Metric.ball (ℓ z) ε ∩ A ⁻¹' Metric.ball (A z) ε with hBdef
    have hBo : IsOpen B :=
      (hSo.inter (Metric.isOpen_ball.preimage ℓ.continuous)).inter (Metric.isOpen_ball.preimage A.continuous)
    have hzB : z ∈ B := ⟨⟨hzS, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩
    have hO₁o : IsOpen ((O ∩ D) ∩ H ⁻¹' B) := hH.continuousOn.isOpen_inter_preimage (hOo.inter hDo) hBo
    have hzO₁ : A z ∈ (O ∩ D) ∩ H ⁻¹' B := ⟨⟨hzO, hzD⟩, by rw [Set.mem_preimage, hHz]; exact hzB⟩
    refine ⟨(O ∩ D) ∩ H ⁻¹' B, B ∩ A ⁻¹' ((O ∩ D) ∩ H ⁻¹' B), H, hO₁o,
      hBo.inter (hO₁o.preimage A.continuous), ⟨hzB, hzO₁⟩, fun s hs => hH s hs.1,
      fun s hs => (hfull' s hs.1.1).2.1, ?_⟩
    ext x
    constructor
    · rintro ⟨hxX, hxB, hxO⟩
      refine ⟨A x, hxO, ?_⟩
      have hs := hfull' (A x) hxO.1.1
      have hHB : H (A x) ∈ B := hxO.2

      have hroot : r (A x) ^ N + ∑ j, a j (A x) * r (A x) ^ (j : ℕ) = 0 := by
        have e := (hUX _ hHB.1.1.1).1 hs.1.1
        rwa [hs.2.1, hs.2.2] at e
      have hℓx : ℓ x = r (A x) := hiso (A x) hxB.2 (ℓ x) (r (A x)) hxB.1.2
        (by rw [← hs.2.2]; exact hHB.1.2) ((hUX x hxB.1.1.1).1 hxX) hroot
      have e := hrep x hxX hxB.1.1 hxO.1.2.2
      rw [hℓx] at e
      exact e
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(hfull' s hs.1.1).1.1, hs.2, by rw [Set.mem_preimage, (hfull' s hs.1.1).2.1]; exact hs⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedCoverCycles
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

noncomputable section

private theorem differentiable_update_pow (e k : ℕ) :
    Differentiable ℂ (fun s : Fin (e + 1) → ℂ => Function.update s 0 (s 0 ^ k)) := by
  rw [differentiable_pi]
  intro i
  by_cases hi : i = 0
  · subst hi
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne hi]
    fun_prop

theorem PuncturedCoverCycles.proof (hCov : FibreSectionsCovering.Statement)
    (hCyc : FiniteCoverPuncturedPolydisc.Statement) : PuncturedCoverCycles.Statement := by
  intro n e N A c r X hr hc0 hXP hfib hsec
  have hX : Set.MapsTo (fun x => A *ᵥ x) X (Metric.ball c r ∩ {t | t 0 ≠ 0}) :=
    fun x hx => hXP x hx
  have hcov := hCov n e N A _ X hX (fun y hy => hfib y hy.1 hy.2) hsec
  have hfib' : ∀ z, (hX.restrict ⁻¹' {z}).encard = N := by
    intro z
    have himg : Subtype.val '' (hX.restrict ⁻¹' {z}) = {x | x ∈ X ∧ A *ᵥ x = z} := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact ⟨x'.2, congrArg Subtype.val hx'⟩
      · rintro ⟨hx, hxz⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxz, rfl⟩
    rw [← Subtype.val_injective.encard_image, himg]
    exact hfib z z.2.1 z.2.2
  obtain ⟨m, ord, δ, ψ, hδ0, hδ1, hsum, hord, hcont, hA, hinj, hdisj, hcover⟩ :=
    hCyc e N c r X hX.restrict hr hc0 hcov hfib'
  classical
  let Ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun b t =>
    if h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0} then (ψ b ⟨t, h⟩ : Fin n → ℂ) else 0
  have hΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}), Ψ b t = ψ b ⟨t, h⟩ :=
    fun b t h => dif_pos h
  have hAΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}),
      A *ᵥ Ψ b t = Function.update t 0 (t 0 ^ ord b) := by
    intro b t h
    rw [hΨ b t h]
    exact hA b ⟨t, h⟩
  have hopen : IsOpen (Metric.ball c δ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) :=
    Metric.isOpen_ball.inter (isOpen_ne_fun (continuous_apply 0) continuous_const)
  refine ⟨m, ord, Ψ, δ, hδ0, hδ1, hsum, hord, ?_, ?_, ?_, ?_, ?_⟩
  · intro b t ht
    have hcontΨ : ContinuousOn (Ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0}) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Metric.ball c δ ∩ {t | t 0 ≠ 0}).domRestrict (Ψ b) = fun s => (ψ b s : Fin n → ℂ) :=
        funext fun s => hΨ b s.1 s.2
      rw [this]
      exact continuous_subtype_val.comp (hcont b)
    obtain ⟨O, V', g, hO, hAO, hV', hxV', hg, -, hAg, hXV'⟩ := hsec _ (ψ b ⟨t, ht⟩).2
    have hqt : Function.update t 0 (t 0 ^ ord b) ∈ O := by
      rw [← hAΨ b t ht, hΨ b t ht]
      exact hAO
    have h1 : ∀ᶠ s in 𝓝 t, s ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0} := hopen.mem_nhds ht
    have h2 : ∀ᶠ s in 𝓝 t, Ψ b s ∈ V' :=
      (hcontΨ.continuousAt (hopen.mem_nhds ht)).preimage_mem_nhds
        (hV'.mem_nhds (by rw [hΨ b t ht]; exact hxV'))
    have heq : Ψ b =ᶠ[𝓝 t] fun s => g (Function.update s 0 (s 0 ^ ord b)) := by
      filter_upwards [h1, h2] with s hs hsV
      have hmem : Ψ b s ∈ X ∩ V' := ⟨by rw [hΨ b s hs]; exact (ψ b ⟨s, hs⟩).2, hsV⟩
      rw [hXV'] at hmem
      obtain ⟨o, ho, hgo⟩ := hmem
      have hAo : A *ᵥ Ψ b s = o := by rw [← hgo, hAg o ho]
      rw [← hgo, ← hAo, hAΨ b s hs]
    have hdiff : DifferentiableAt ℂ (fun s => g (Function.update s 0 (s 0 ^ ord b))) t :=
      (hg.differentiableAt (hO.mem_nhds hqt)).comp t (differentiable_update_pow e (ord b) t)
    exact (heq.differentiableAt_iff.mpr hdiff).differentiableWithinAt
  · intro b t ht
    rw [hΨ b t ht]
    exact ⟨(ψ b ⟨t, ht⟩).2, hA b ⟨t, ht⟩⟩
  · intro b t ht t' ht' h
    rw [hΨ b t ht, hΨ b t' ht'] at h
    exact congrArg Subtype.val (hinj b (Subtype.ext h))
  · intro b b' hbb t ht t' ht' h
    rw [hΨ b t ht, hΨ b' t' ht'] at h
    exact hdisj b b' hbb _ _ (Subtype.ext h)
  · intro x hx hdist
    obtain ⟨b, t, hbt⟩ := hcover ⟨x, hx⟩ hdist
    refine ⟨b, t.1, t.2, ?_⟩
    rw [hΨ b t.1 t.2]
    exact congrArg Subtype.val hbt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRankDeficientFibreInfinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

noncomputable section

namespace RankDeficientFibreInfinite


open HolomorphicFibreInfinite in
theorem proof : RankDeficientFibreInfinite.Statement := by
  intro k d U f hU hUne hf hinj
  classical
  have hfa : AnalyticOnNhd ℂ f U :=
    GroundTheory.Heights₂.Heights.ImplicitCurve.analyticOnNhd_of_differentiableOn hU hf

  let Q : ℕ → Prop := fun m => ∃ t ∈ U, ∃ v : Fin m → Fin k → ℂ,
    LinearIndependent ℂ (fun j => fderiv ℂ f t (v j))
  have hQ0 : Q 0 := by
    obtain ⟨t, ht⟩ := hUne
    exact ⟨t, ht, Fin.elim0, linearIndependent_empty_type⟩
  have hspec : Q (Nat.findGreatest Q k) := Nat.findGreatest_spec (Nat.zero_le k) hQ0
  have hle : ∀ m, m ≤ k → Q m → m ≤ Nat.findGreatest Q k := fun m hmk hm => Nat.le_findGreatest hmk hm
  generalize Nat.findGreatest Q k = r at hspec hle
  obtain ⟨s, hs, v, hv⟩ := hspec
  have hmax : ∀ t ∈ U, ∀ u : Fin (r + 1) → Fin k → ℂ,
      ¬ LinearIndependent ℂ (fun j => fderiv ℂ f t (u j)) := by
    intro t ht u hu
    have hu' : LinearIndependent ℂ u :=
      LinearIndependent.of_comp (fderiv ℂ f t : (Fin k → ℂ) →ₗ[ℂ] (Fin d → ℂ)) hu
    have hcard : r + 1 ≤ k := by simpa using hu'.fintype_card_le_finrank
    have := hle (r + 1) hcard ⟨t, ht, u, hu⟩
    omega

  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin d → ℂ) := Fintype.linearCombination ℂ (fun j => fderiv ℂ f s (v j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.1 hv c (by simpa [T, Fintype.linearCombination_apply] using hc) j
  obtain ⟨Λ, hΛ⟩ := T.exists_leftInverse_of_injective hT
  have hΛv : ∀ j, Λ (fderiv ℂ f s (v j)) = Pi.single j 1 := by
    intro j
    have := congrArg (fun g => g (Pi.single j (1 : ℂ))) hΛ
    simpa [T, Fintype.linearCombination_apply_single] using this
  let Λc : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap Λ
  have hΛc : ∀ y, Λc y = Λ y := fun y => rfl

  have hev : ∀ᶠ t in 𝓝 s, t ∈ U ∧ LinearIndependent ℂ (fun j => Λ (fderiv ℂ f t (v j))) := by
    have hUev : ∀ᶠ t in 𝓝 s, t ∈ U := hU.mem_nhds hs
    refine hUev.and ?_
    have hDcont : ContinuousAt (fderiv ℂ f) s := (hfa.fderiv s hs).continuousAt
    have hc : ContinuousAt (fun t => fun j => Λc (fderiv ℂ f t (v j))) s := by
      refine continuousAt_pi.2 fun j => ?_
      exact Λc.continuous.continuousAt.comp
        ((ContinuousLinearMap.apply ℂ (Fin d → ℂ) (v j)).continuous.continuousAt.comp hDcont)
    have h0 : LinearIndependent ℂ (fun j => Λc (fderiv ℂ f s (v j))) := by
      have : (fun j => Λc (fderiv ℂ f s (v j))) = ⇑(Pi.basisFun ℂ (Fin r)) := by
        funext j
        simp [hΛc, hΛv]
      rw [this]
      exact (Pi.basisFun ℂ (Fin r)).linearIndependent
    exact hc.eventually h0.eventually

  obtain ⟨w, hw, hw0⟩ : ∃ w, fderiv ℂ f s w = 0 ∧ w ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hinj s hs
    intro x y hxy
    exact sub_eq_zero.1 (hno _ (by rw [map_sub, hxy, sub_self]))
  have hw' : Λ (fderiv ℂ f s w) = 0 := by rw [hw, map_zero]

  let A' : ℂ × (Fin r → ℂ) →L[ℂ] (Fin k → ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin r → ℂ)).smulRight w +
      ∑ j, ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin r → ℂ))).smulRight (v j)
  have hA' : ∀ p : ℂ × (Fin r → ℂ), A' p = p.1 • w + ∑ j, p.2 j • v j := by
    intro p
    simp [A']
  have hLA : ∀ p : ℂ × (Fin r → ℂ), Λ (fderiv ℂ f s (A' p)) = p.2 := by
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hA', map_add (f := _), map_add (f := _), map_smul, map_smul, hw', smul_zero, zero_add, map_sum, map_sum]
    simp only [map_smul, hΛv]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  let H : ℂ × (Fin r → ℂ) → Fin r → ℂ := fun p => Λc (f (s + A' p))
  have hfs : AnalyticAt ℂ f s := hfa s hs
  have hHd : HasFDerivAt H (Λc.comp ((fderiv ℂ f s).comp A')) 0 := by
    have h1 : HasFDerivAt (fun p => s + A' p) A' (0 : ℂ × (Fin r → ℂ)) := A'.hasFDerivAt.const_add s
    have h2 : HasFDerivAt f (fderiv ℂ f s) (s + A' 0) := by
      simpa using hfs.differentiableAt.hasFDerivAt
    exact Λc.hasFDerivAt.comp _ (HasFDerivAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) h2 h1)
  have hHc : ContDiffAt ℂ 1 H 0 := by
    have hf1 : ContDiffAt ℂ 1 f (s + A' 0) := by simpa using hfs.contDiffAt
    exact Λc.contDiff.contDiffAt.comp _
      (ContDiffAt.comp (f := fun p => s + A' p) (0 : ℂ × (Fin r → ℂ)) hf1 (contDiff_const.add A'.contDiff).contDiffAt)
  have hinv : (fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ)).IsInvertible := by
    have : fderiv ℂ H 0 ∘L ContinuousLinearMap.inr ℂ ℂ (Fin r → ℂ) =
        ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
      rw [hHd.fderiv]
      refine ContinuousLinearMap.ext fun c => ?_
      simpa [hΛc] using hLA (0, c)
    rw [this]
    exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩

  have hψc := hHc.contDiffAt_implicitFunction one_ne_zero hinv
  set ψ := hHc.implicitFunction one_ne_zero hinv with hψ
  have hψ0 : ψ 0 = 0 := hHc.implicitFunction_apply_self one_ne_zero hinv
  have hψeq : ∀ᶠ z in 𝓝 (0 : ℂ), H (z, ψ z) = H 0 :=
    hHc.eventually_apply_implicitFunction one_ne_zero hinv
  have hψd : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ ψ z :=
    (hψc.eventually (by simp)).mono fun z hz => hz.differentiableAt one_ne_zero
  let P : ℂ → Fin k → ℂ := fun z => s + A' (z, ψ z)
  have hP0 : P 0 = s := by simp [P, hψ0, hA']
  have hPcont : ContinuousAt P 0 :=
    continuousAt_const.add (A'.continuous.continuousAt.comp (continuousAt_id.prodMk hψc.continuousAt))
  rw [← hP0] at hev
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (((hPcont.eventually hev).and hψeq).and hψd)
  have hPd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ P z := fun z hz =>
    (differentiableAt_const _).add (A'.differentiableAt.comp z (differentiableAt_id.prodMk (hball z hz).2))
  have hPU : ∀ z ∈ ball (0 : ℂ) δ, P z ∈ U := fun z hz => (hball z hz).1.1.1
  have hfd : ∀ z ∈ ball (0 : ℂ) δ, DifferentiableAt ℂ f (P z) := fun z hz =>
    (hf _ (hPU z hz)).differentiableAt (hU.mem_nhds (hPU z hz))
  have hgP : ∀ z ∈ ball (0 : ℂ) δ, Λc (f (P z)) = Λc (f s) := by
    intro z hz
    have := (hball z hz).1.2
    simpa [H, P] using this

  have hzero : Set.EqOn (fderiv ℂ (fun z => f (P z))) 0 (ball (0 : ℂ) δ) := by
    intro z hz
    have hcomp : fderiv ℂ (fun z => f (P z)) z = (fderiv ℂ f (P z)).comp (fderiv ℂ P z) :=
      fderiv_comp z (hfd z hz) (hPd z hz)
    have hloc : (fun z => Λc (f (P z))) =ᶠ[𝓝 z] fun _ => Λc (f s) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hgP
    have hg0 : fderiv ℂ (fun z => Λc (f (P z))) z = 0 := by
      rw [hloc.fderiv_eq]
      exact fderiv_const_apply _
    have hgc : fderiv ℂ (fun z => Λc (f (P z))) z = Λc.comp ((fderiv ℂ f (P z)).comp (fderiv ℂ P z)) := by
      rw [← hcomp]
      have h := fderiv_comp z Λc.differentiableAt ((hfd z hz).comp z (hPd z hz))
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hx : Λ (fderiv ℂ f (P z) (fderiv ℂ P z 1)) = 0 := by
      have := congrArg (fun L => L 1) (hgc.symm.trans hg0)
      simpa [hΛc] using this
    have := kernel_eq_of_maximal (fderiv ℂ f (P z)) v Λ (hmax _ (hPU z hz)) (hball z hz).1.1.2 hx
    rw [hcomp]
    refine ContinuousLinearMap.ext_ring ?_
    simpa using this
  have hconst : ∀ z ∈ ball (0 : ℂ) δ, f (P z) = f s := by
    intro z hz
    have := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      (fun z hz => ((hfd z hz).comp z (hPd z hz)).differentiableWithinAt) hzero hz (mem_ball_self hδ)
    simpa [hP0] using this

  have hPinj : Function.Injective P := by
    intro z z' hzz
    have hψz : ψ z = ψ z' := by
      have h1 := hLA (z, ψ z)
      have h2 := hLA (z', ψ z')
      have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
      rw [this] at h1
      exact h1.symm.trans h2
    have : A' (z, ψ z) = A' (z', ψ z') := add_left_cancel hzz
    rw [hA', hA', hψz] at this
    have h3 : z • w = z' • w := add_right_cancel this
    exact smul_left_injective ℂ hw0 h3
  refine ⟨f s, ?_⟩
  have hinf : (ball (0 : ℂ) δ).Infinite := infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 hδ)
  refine (hinf.image hPinj.injOn).mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨hPU z hz, hconst z hz⟩

end RankDeficientFibreInfinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

theorem exists_eval_ne_zero_of_isOpen_pi {σ : Type*} [Finite σ] {F : MvPolynomial σ ℂ} (hF : F ≠ 0)
    {S : Set (σ → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y F ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hF
  have hinf : ∀ i, (u i).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) ((hu i).1.mem_nhds (hu i).2)
  refine (funext_set_iff (p := F) (q := 0) u hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hsub hy)

theorem SliceReducedAway.proof (hZ : SliceReducedAwayZariski.Statement) :
    SliceReducedAway.Statement := by
  intro n d J q hJ
  obtain ⟨F, hF, hgood⟩ := hZ n d J q hJ
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let φ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hφ : Continuous φ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hL => hgood L hL⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ :=
      exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hφ) ⟨e L₀, hL₀⟩
    exact ⟨φ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CurveNormalisationFinite.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), IsRadicalAt I q →
    Module.Finite (curveLocalRing I q) (curveNormalisation I q)

end GroundTheory.Heights₂.Heights
end

