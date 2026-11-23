module

public import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PNormComparison

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeLeOfMetricBoundedMap
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

theorem norm_sq_eq_sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) :
    ‖FibreSpace.equiv E.metric σ x‖ ^ 2 = sqAt E σ x := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

theorem gram_map_le (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c) (σ : K →+* ℂ)
    (h : ∀ x : Fibre σ E.carrier, sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    {r : ℕ} {s : Fin r → E.carrier} (hs : LinearIndependent (𝓞 K) s) :
    gramDet E'.metric σ (fun i => φ (s i)) ≤ c ^ r * gramDet E.metric σ s := by
  have hnorm : ∀ x : Fibre σ E.carrier,
      ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ≤ Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖ := by
    intro x
    have h1 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 = sqAt E' σ (φ.lTensor (ComplexAt σ) x) := by
      rw [← CoverDenseAlt.norm_sq_eq_sqAt, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, FibreSpace.inner_equiv,
        FibreSpace.inner_equiv, HermitianMetric.comap_inner E'.metric φ hφ σ]
      rfl
    have h2 := h x
    rw [← h1, ← CoverDenseAlt.norm_sq_eq_sqAt] at h2
    have h3 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 ≤
        (Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      exact h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp h3
  have key := LatticeLemmas.gramDet_le_of_norm_le E.metric (E'.metric.comap φ hφ) σ (Real.sqrt c) hnorm hs
  rw [gramDet_comap] at key
  rwa [max_eq_left (Real.sqrt_nonneg c), Real.sq_sqrt hc.le] at key

theorem normDeg_map (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) (F : Submodule (𝓞 K) E.carrier) :
    E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c := by
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := F) (n := E.rank F) le_rfl
  have hv : LinearIndependent (𝓞 K) (fun i => (s i : E.carrier)) := hs.map' F.subtype F.ker_subtype
  have hw : LinearIndependent (𝓞 K) (fun i => φ (s i : E.carrier)) :=
    hv.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  let e := Submodule.equivMapOfInjective φ hφ F
  let t : Fin (E.rank F) → F.map φ := fun i => e (s i)
  have ht : LinearIndependent (𝓞 K) t := hs.map' e.toLinearMap e.ker
  have hrank : E'.rank (F.map φ) = E.rank F := (LinearEquiv.finrank_eq e).symm
  have hdF := E.degree_eq_of_linearIndependent F hs (Fintype.card_fin _)
  have hdG : E'.degree (F.map φ) = Real.log (Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t))) -
      1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) :=
    E'.degree_eq_of_linearIndependent (F.map φ) ht (by rw [Fintype.card_fin, hrank])
  have hcard : Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t)) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    refine (Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv).symm
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hgram : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) ≤
      E.rank F * Real.log c + Real.log (gramDet E.metric σ fun i => (s i : E.carrier)) := by
    intro σ
    have hle := gram_map_le E E' φ c hφ hc σ (h σ) hv
    have hpos' := gramDet_pos E'.metric σ hw
    have hpos := gramDet_pos E.metric σ hv
    calc _ ≤ Real.log (c ^ E.rank F * gramDet E.metric σ fun i => (s i : E.carrier)) :=
          Real.log_le_log hpos' hle
      _ = _ := by rw [Real.log_mul (pow_pos hc _).ne' hpos.ne', Real.log_pow]
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hgram σ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ,
    nsmul_eq_mul] at hsum
  have hq : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold HermitianBundle.normDegree
  rw [div_add' _ _ _ hq.ne', div_le_div_iff_of_pos_right hq, hdF, hdG, hcard]
  linarith

theorem normDegree_le_of_metric_bounded_map : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) := by
  intro K _ _ E E' φ c hφ hc h
  refine ⟨normDeg_map E E' φ c hφ hc h, iSup₂_le fun F hF => ?_⟩
  have hne : F.map φ ≠ ⊥ := by
    intro h0
    have := rank_map E E' φ hφ F
    rw [h0] at this
    have h1 := rank_pos E hF
    rw [← this] at h1
    simp [HermitianBundle.rank] at h1
  have hle : ((E'.slope (F.map φ) : ℝ) : EReal) ≤ E'.slopeMax := le_iSup₂_of_le (F.map φ) hne le_rfl
  refine le_trans ?_ (add_le_add_left hle _)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hr : (0 : ℝ) < E.rank F := by exact_mod_cast rank_pos E hF
  have hd := normDeg_map E E' φ c hφ hc h F
  unfold HermitianBundle.slope
  rw [rank_map E E' φ hφ, div_add' _ _ _ hr.ne']
  refine div_le_div_of_nonneg_right ?_ hr.le
  linarith

end CoverDenseAlt
end

-- bundled from Development.WeilBound.CoreStatements.AmpleLineBundles.StandardHermitianBundleSemistable
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

def tailIncl (K : Type) [Field K] (r : ℕ) : (Fin r → 𝓞 K) →ₗ[𝓞 K] (Fin (r + 1) → 𝓞 K) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [NumberField K] in
theorem coord_tail_zero (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin r → 𝓞 K)) :
    standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x) 0 = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, tailIncl]
  | add a b ha hb => simp only [map_add (f := _), PiLp.add_apply] at ha hb ⊢; rw [ha, hb, add_zero]

omit [NumberField K] in
theorem coord_tail_succ (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin r → 𝓞 K)) (j : Fin r) :
    standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x) j.succ =
      standardCoord K σ (Fin r) x j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, tailIncl]
  | add a b ha hb => simp only [map_add (f := _), PiLp.add_apply] at ha hb ⊢; rw [ha, hb]

omit [NumberField K] in
theorem coord_head (σ : K →+* ℂ) (r : ℕ) (x : Fibre σ (Fin (r + 1) → 𝓞 K)) :
    integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x) =
      standardCoord K σ (Fin (r + 1)) x 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [standardCoord, integersCoord]
  | add a b ha hb => simp only [map_add (f := _)] at ha hb ⊢; rw [ha, hb]; rfl

theorem coord_zero_of_orth (σ : K →+* ℂ) (r : ℕ) (v : Fibre σ (Fin (r + 1) → 𝓞 K))
    (hv : ∀ w : Fibre σ (Fin r → 𝓞 K), ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) w) v = 0) (j : Fin r) :
    standardCoord K σ (Fin (r + 1)) v j.succ = 0 := by
  have h := hv (1 ⊗ₜ Pi.single j 1)
  change inner ℂ (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) (1 ⊗ₜ Pi.single j 1)))
      (standardCoord K σ (Fin (r + 1)) v) = 0 at h
  rw [PiLp.inner_apply, Fin.sum_univ_succ] at h
  simp only [coord_tail_zero, coord_tail_succ, inner_zero_left, zero_add] at h
  simpa [standardCoord, Pi.single_apply] using h

theorem tail_iso (σ : K →+* ℂ) (r : ℕ) (x y : Fibre σ (Fin r → 𝓞 K)) :
    ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) x) ((tailIncl K r).lTensor (ComplexAt σ) y) =
      ((HermitianMetric.standard K (Fin r)).form σ).inner x y := by
  show inner ℂ (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) x))
      (standardCoord K σ (Fin (r + 1)) ((tailIncl K r).lTensor (ComplexAt σ) y)) =
    inner ℂ (standardCoord K σ (Fin r) x) (standardCoord K σ (Fin r) y)
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [coord_tail_zero, coord_tail_succ, inner_zero_left, zero_add]

theorem head_coiso (σ : K →+* ℂ) (r : ℕ) (x y : Fibre σ (Fin (r + 1) → 𝓞 K))
    (hy : ∀ w : Fibre σ (Fin r → 𝓞 K), ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner
      ((tailIncl K r).lTensor (ComplexAt σ) w) y = 0) :
    ((HermitianMetric.integers K).form σ).inner
      ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x)
      ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) y) =
      ((HermitianMetric.standard K (Fin (r + 1))).form σ).inner x y := by
  show inner ℂ (integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) x))
      (integersCoord K σ ((LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).lTensor (ComplexAt σ) y)) =
    inner ℂ (standardCoord K σ (Fin (r + 1)) x) (standardCoord K σ (Fin (r + 1)) y)
  rw [coord_head, coord_head, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [coord_zero_of_orth σ r y hy, inner_zero_right, Finset.sum_const_zero, add_zero]

def stdExt (K : Type) [Field K] [NumberField K] (r : ℕ) :
    HermitianExtension (HermitianBundle.standard K r) (HermitianBundle.standard K (r + 1))
      (HermitianBundle.integers K) where
  incl := tailIncl K r
  proj := (LinearMap.proj 0 : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K)
  incl_injective := fun a b h => funext fun j => congrFun h j.succ
  proj_surjective := fun a => ⟨fun _ => a, rfl⟩
  exact := by
    intro y
    constructor
    · intro hy
      refine ⟨fun j => y j.succ, funext fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (show y 0 = 0 from hy).symm
      · rfl
    · rintro ⟨a, rfl⟩
      rfl
  incl_isometric σ x y := tail_iso σ r x y
  proj_coisometric σ x y _ hy := head_coiso σ r x y hy

private theorem exists_injective_quotient_span_map {M N : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup N]
    [Module (𝓞 K) N] (φ : M →ₗ[𝓞 K] N) (hφ : Function.Injective φ) (m : M) :
    ∃ f : M ⧸ Submodule.span (𝓞 K) {m} → N ⧸ Submodule.span (𝓞 K) {φ m}, Function.Injective f := by
  have h : Submodule.span (𝓞 K) {m} ≤ (Submodule.span (𝓞 K) {φ m}).comap φ := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap]
    exact Submodule.mem_span_singleton_self _
  refine ⟨Submodule.mapQ _ _ φ h, fun x y hxy => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hxy
  exact Submodule.mem_span_singleton.2 ⟨c, hφ (by rw [map_smul, map_sub]; exact hc)⟩

set_option maxHeartbeats 400000 in
theorem integers_deg_le (G : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) :
    (HermitianBundle.integers K).degree G ≤ 0 := by
  by_cases hG : G = ⊥
  · rw [hG, HermitianBundle.degree_bot]
  obtain ⟨a, haG, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG
  let sG : Fin 1 → G := fun _ => ⟨a, haG⟩
  let sT : Fin 1 → (⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) :=
    fun _ => ⟨a, Submodule.mem_top⟩
  have liG : LinearIndependent (𝓞 K) sG :=
    linearIndependent_unique_iff.2 (fun h => ha0 (congrArg Subtype.val h))
  have liT : LinearIndependent (𝓞 K) sT :=
    linearIndependent_unique_iff.2 (fun h => ha0 (congrArg Subtype.val h))
  have rT : (HermitianBundle.integers K).rank ⊤ = 1 := by
    show Module.finrank (𝓞 K) (⊤ : Submodule (𝓞 K) (𝓞 K)) = 1
    rw [finrank_top, Module.finrank_self]
  have rG : (HermitianBundle.integers K).rank G = 1 := by
    refine le_antisymm ?_ ?_
    · show Module.finrank (𝓞 K) G ≤ 1
      calc Module.finrank (𝓞 K) G ≤ Module.finrank (𝓞 K) (𝓞 K) := Submodule.finrank_le G
        _ = 1 := Module.finrank_self _
    · have h := liG.fintype_card_le_finrank
      rw [Fintype.card_fin] at h
      exact h
  have hGd := (HermitianBundle.integers K).degree_eq_of_linearIndependent G liG (by simp [rG])
  have hTd := (HermitianBundle.integers K).degree_eq_of_linearIndependent ⊤ liT (by simp [rT])
  have hT0 : (HermitianBundle.integers K).degree ⊤ = 0 := by
    rw [HermitianBundle.degree_top_eq_arithDegree, HermitianBundle.arithDegree_integers]
  have hsame : (fun i => (sG i : (HermitianBundle.integers K).carrier)) =
      fun i => (sT i : (HermitianBundle.integers K).carrier) := rfl
  rw [hsame] at hGd
  rw [Set.range_const] at hGd hTd
  have hfin : Finite (𝓞 K ⧸ Ideal.span {(show 𝓞 K from a)}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by rw [Ne, Ideal.span_singleton_eq_bot]; exact ha0)
  obtain ⟨f1, hf1⟩ := exists_injective_quotient_span_map
    (⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier).subtype Subtype.val_injective (sT 0)
  obtain ⟨f2, hf2⟩ := exists_injective_quotient_span_map (Submodule.inclusion (le_top : G ≤ ⊤))
    (Submodule.inclusion_injective _) (sG 0)
  have hfinT : Finite ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
      Submodule.span (𝓞 K) {sT 0}) := by
    have : Finite ((HermitianBundle.integers K).carrier ⧸ Submodule.span (𝓞 K)
      {((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier).subtype (sT 0))}) := hfin
    exact Finite.of_injective f1 hf1
  have hfinT' : Finite ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
      Submodule.span (𝓞 K) {Submodule.inclusion (le_top : G ≤ ⊤) (sG 0)}) := hfinT
  have hfinG : Finite (G ⧸ Submodule.span (𝓞 K) {sG 0}) := Finite.of_injective f2 hf2
  have hle : Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) ≤
      Nat.card ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
        Submodule.span (𝓞 K) {sT 0}) :=
    Nat.card_le_card_of_injective f2 hf2
  have hpos : 0 < Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) := Nat.card_pos
  have hlog := Real.log_le_log (by exact_mod_cast hpos)
    (Nat.cast_le.2 hle : (Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0}) : ℝ) ≤ _)
  have e1 : (HermitianBundle.integers K).degree G =
      Real.log (Nat.card (G ⧸ Submodule.span (𝓞 K) {sG 0})) -
        1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet (HermitianBundle.integers K).metric σ
          fun i => (sT i : (HermitianBundle.integers K).carrier)) := hGd
  have e2 : (HermitianBundle.integers K).degree ⊤ =
      Real.log (Nat.card ((⊤ : Submodule (𝓞 K) (HermitianBundle.integers K).carrier) ⧸
        Submodule.span (𝓞 K) {sT 0})) -
        1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet (HermitianBundle.integers K).metric σ
          fun i => (sT i : (HermitianBundle.integers K).carrier)) := hTd
  linarith

theorem std_deg (r : ℕ) : (∀ F, (HermitianBundle.standard K r).degree F ≤ 0) ∧
    (HermitianBundle.standard K r).degree ⊤ = 0 := by
  induction r with
  | zero =>
    have hs : ∀ F : Submodule (𝓞 K) (HermitianBundle.standard K 0).carrier, F = ⊥ := by
      intro F
      refine (Submodule.eq_bot_iff F).2 fun x _ => ?_
      show (x : Fin 0 → 𝓞 K) = 0
      funext i
      exact i.elim0
    refine ⟨fun F => ?_, ?_⟩
    · rw [hs F, HermitianBundle.degree_bot]
    · rw [hs ⊤, HermitianBundle.degree_bot]
  | succ r ih =>
    refine ⟨fun F => ?_, ?_⟩
    · have h1 := ih.1 (Submodule.comap (stdExt K r).incl F)
      have h2 := integers_deg_le (Submodule.map (stdExt K r).proj F)
      have h3 := (stdExt K r).degree_submodule_le F
      linarith
    · rw [HermitianBundle.degree_top_eq_arithDegree, (stdExt K r).arithDegree_eq_add,
        ← HermitianBundle.degree_top_eq_arithDegree, ih.2,
        HermitianBundle.arithDegree_integers, add_zero]

theorem standard_hermitian_bundle_semistable : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ), (HermitianBundle.standard K r).slopeMax ≤ 0 ∧ (HermitianBundle.standard K r).normDegree ⊤ = 0 := by
  intro K _ _ r
  have h := std_deg (K := K) r
  refine ⟨?_, ?_⟩
  · refine iSup_le fun F => iSup_le fun _ => ?_
    have hF : HermitianBundle.slope _ F ≤ 0 := by
      unfold HermitianBundle.slope HermitianBundle.normDegree
      refine div_nonpos_iff.2 (Or.inr ⟨div_nonpos_iff.2 (Or.inr ⟨h.1 F, by positivity⟩), by positivity⟩)
    exact_mod_cast hF
  · simp [HermitianBundle.normDegree, h.2]

end CoverDenseAlt
end

