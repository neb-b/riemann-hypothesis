module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtA
section
noncomputable section

open scoped ComplexConjugate
open Set MeasureTheory

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def swAlg (A : Submodule ℂ (X → ℂ)) (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (K : Set X) : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {h | ∃ c : ℂ, ∃ a ∈ A, ∀ x : K, h x = c + a x}
  mul_mem' := by
    rintro h h' ⟨c, a, ha, hh⟩ ⟨c', a', ha', hh'⟩
    refine ⟨c * c', c • a' + c' • a + a * a', A.add_mem (A.add_mem (A.smul_mem _ ha') (A.smul_mem _ ha))
      (hmul _ ha _ ha'), fun x => ?_⟩
    simp only [ContinuousMap.mul_apply, hh, hh', Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  one_mem' := ⟨1, 0, A.zero_mem, fun x => by simp⟩
  add_mem' := by
    rintro h h' ⟨c, a, ha, hh⟩ ⟨c', a', ha', hh'⟩
    refine ⟨c + c', a + a', A.add_mem ha ha', fun x => ?_⟩
    simp only [ContinuousMap.add_apply, hh, hh', Pi.add_apply]
    ring
  zero_mem' := ⟨0, 0, A.zero_mem, fun x => by simp⟩
  algebraMap_mem' r := ⟨r, 0, A.zero_mem, fun x => by simp [Algebra.algebraMap_eq_smul_one]⟩
  star_mem' := by
    rintro h ⟨c, a, ha, hh⟩
    refine ⟨conj c, star a, hstar a ha, fun x => ?_⟩
    simp [ContinuousMap.star_apply, hh, Pi.star_apply]

theorem approx (A : Submodule ℂ (X → ℂ)) (hc : ∀ f ∈ A, Continuous f)
    (hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y) {K : Set X} (hK : IsCompact K) {b : X → ℂ} (hbA : b ∈ A)
    (hbK : ∀ x ∉ K, b x = 0) {g : X → ℂ} (hg : Continuous g) (hgb : ∀ x, g x ≠ 0 → b x = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ h ∈ A, ∀ x, ‖h x - g x‖ ≤ ε * ‖b x‖ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set S := swAlg A hmul hstar K
  have hS : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfxy⟩ := hsep x y (fun h => hxy (Subtype.ext h))
    let F : C(K, ℂ) := ⟨fun z => f z, (hc f hf).comp continuous_subtype_val⟩
    exact ⟨F, ⟨F, ⟨0, f, hf, fun z => by simp [F]⟩, rfl⟩, hfxy⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  let gK : C(K, ℂ) := ⟨fun z => g z, hg.comp continuous_subtype_val⟩
  have hgK : gK ∈ S.topologicalClosure := by rw [htop]; trivial
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hgK
  obtain ⟨p, hpS, hp⟩ := hgK ε hε
  obtain ⟨c, a, ha, hpa⟩ := hpS
  refine ⟨c • b + b * a, A.add_mem (A.smul_mem _ hbA) (hmul _ hbA _ ha), fun x => ?_⟩
  by_cases hx : x ∈ K
  · have h1 : ‖p ⟨x, hx⟩ - gK ⟨x, hx⟩‖ ≤ ε := by
      have := ContinuousMap.norm_coe_le_norm (p - gK) ⟨x, hx⟩
      rw [dist_comm, dist_eq_norm] at hp
      exact (this.trans hp.le)
    have h2 : g x = b x * g x := by
      by_cases h0 : g x = 0
      · simp [h0]
      · simp [hgb x h0]
    have h3 : c • b x + b x * a x - g x = b x * (p ⟨x, hx⟩ - gK ⟨x, hx⟩) := by
      rw [hpa ⟨x, hx⟩]
      simp only [gK, ContinuousMap.coe_mk]
      rw [h2] at *
      nth_rewrite 1 [h2]
      simp only [smul_eq_mul]
      ring
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply]
    rw [h3, norm_mul, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  · have hb := hbK x hx
    have hg0 : g x = 0 := by
      by_contra h0
      have := hgb x h0
      rw [hb] at this
      exact zero_ne_one this
    simp [hb, hg0]

theorem zero_of_le (d : ℂ) (C : ℝ) (h : ∀ ε : ℝ, 0 < ε → ‖d‖ ≤ ε * C) : d = 0 := by
  have hC : 0 ≤ C := by have := h 1 one_pos; linarith [norm_nonneg d]
  have : ∀ ε : ℝ, 0 < ε → dist d 0 ≤ ε := by
    intro ε hε
    rw [dist_zero_right]
    refine (h (ε / (C + 1)) (by positivity)).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  exact eq_of_forall_dist_le this

end PositivityTheory.Rg.Rsw.L.LPosExt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajA
section
noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LWMaj

open Metric

section Dyadic

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

def sc (j : ℕ) : Z →L[ℝ] Z := ((2 : ℝ) ^ j)⁻¹ • ContinuousLinearMap.id ℝ Z

omit [FiniteDimensional ℝ Z] in
theorem sc_apply (j : ℕ) (z : Z) : sc j z = ((2 : ℝ) ^ j)⁻¹ • z := rfl

omit [FiniteDimensional ℝ Z] in
theorem norm_sc_le (j : ℕ) : ‖(sc j : Z →L[ℝ] Z)‖ ≤ 1 := by
  refine (norm_smul_le _ _).trans ?_
  have h1 : ‖((2 : ℝ) ^ j)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Real.norm_two]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  calc ‖((2 : ℝ) ^ j)⁻¹‖ * ‖ContinuousLinearMap.id ℝ Z‖ ≤ 1 * 1 :=
        mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_sc (j : ℕ) (z : Z) : ‖sc j z‖ = ‖z‖ / 2 ^ j := by
  rw [sc_apply, norm_smul, norm_inv, norm_pow, Real.norm_two, div_eq_inv_mul]

def dy (ρ : ContDiffBump (0 : Z)) (j : ℕ) : Z → ℝ := fun z => ρ (sc j z)

theorem dy_eq (ρ : ContDiffBump (0 : Z)) (j : ℕ) : dy ρ j = ρ ∘ (sc j) := rfl

theorem contDiff_dy (ρ : ContDiffBump (0 : Z)) (j : ℕ) {n : ℕ∞} : ContDiff ℝ n (dy ρ j) := by
  rw [dy_eq]
  exact ρ.contDiff.comp (sc j).contDiff

theorem norm_iteratedFDeriv_dy_le (ρ : ContDiffBump (0 : Z)) (j k : ℕ) (z : Z) :
    ‖iteratedFDeriv ℝ k (dy ρ j) z‖ ≤ ‖iteratedFDeriv ℝ k ρ (sc j z)‖ := by
  rw [dy_eq, ContinuousLinearMap.iteratedFDeriv_comp_right (sc j) (ρ.contDiff (n := (k : ℕ∞))) z le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin k, ‖(sc j : Z →L[ℝ] Z)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_sc_le j)
  calc ‖iteratedFDeriv ℝ k ρ (sc j z)‖ * ∏ _i : Fin k, ‖(sc j : Z →L[ℝ] Z)‖
      ≤ ‖iteratedFDeriv ℝ k ρ (sc j z)‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := mul_one _

theorem exists_bound_iteratedFDeriv (ρ : ContDiffBump (0 : Z)) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (ρ.contDiff (n := (k : ℕ∞)).continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (ρ.hasCompactSupport.iteratedFDeriv k)
  exact ⟨M, (norm_nonneg _).trans (hM 0), hM⟩

theorem iteratedFDeriv_eq_zero_of_far (ρ : ContDiffBump (0 : Z)) (k : ℕ) {x : Z} (hx : ρ.rOut < ‖x‖) :
    iteratedFDeriv ℝ k ρ x = 0 := by
  have hx' : x ∉ tsupport ρ := by
    rw [ρ.tsupport_eq, mem_closedBall, dist_zero_right]
    exact not_le.2 hx
  exact Function.notMem_support.1 fun h => hx' (support_iteratedFDeriv_subset k h)

end Dyadic

section Coef

variable {Z : Type} [NormedAddCommGroup Z]

def env (S : Set (Z → ℂ)) (j : ℕ) : Set ℝ :=
  insert 0 {r | ∃ u ∈ S, ∃ z : Z, (j = 0 ∨ (2 : ℝ) ^ j ≤ 2 * ‖z‖) ∧ r = ‖u z‖}

def cf (S : Set (Z → ℂ)) (j : ℕ) : ℝ := sSup (env S j)

variable {S : Set (Z → ℂ)} {B : ℕ → ℝ}

theorem mem_env_le (hB : ∀ N, ∀ u ∈ S, ∀ z, (1 + ‖z‖) ^ N * ‖u z‖ ≤ B N) (N j : ℕ) :
    ∀ r ∈ env S j, r * ((2 : ℝ) ^ j) ^ N ≤ 2 ^ N * max (B N) 0 := by
  intro r hr
  rcases hr with rfl | ⟨u, hu, z, hz, rfl⟩
  · rw [zero_mul]; positivity
  · have h1 : ((2 : ℝ) ^ j) ^ N ≤ 2 ^ N * (1 + ‖z‖) ^ N := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      rcases hz with rfl | hz
      · rw [pow_zero]; nlinarith [norm_nonneg z]
      · nlinarith [norm_nonneg z]
    calc ‖u z‖ * ((2 : ℝ) ^ j) ^ N ≤ ‖u z‖ * (2 ^ N * (1 + ‖z‖) ^ N) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = 2 ^ N * ((1 + ‖z‖) ^ N * ‖u z‖) := by ring
      _ ≤ 2 ^ N * max (B N) 0 :=
          mul_le_mul_of_nonneg_left ((hB N u hu z).trans (le_max_left _ _)) (by positivity)

theorem bdd_env (hB : ∀ N, ∀ u ∈ S, ∀ z, (1 + ‖z‖) ^ N * ‖u z‖ ≤ B N) (j : ℕ) : BddAbove (env S j) := by
  refine ⟨max (B 0) 0, fun r hr => ?_⟩
  have := mem_env_le hB 0 j r hr
  simpa using this

theorem cf_nonneg (hB : ∀ N, ∀ u ∈ S, ∀ z, (1 + ‖z‖) ^ N * ‖u z‖ ≤ B N) (j : ℕ) : 0 ≤ cf S j :=
  le_csSup (bdd_env hB j) (Set.mem_insert 0 _)

theorem le_cf (hB : ∀ N, ∀ u ∈ S, ∀ z, (1 + ‖z‖) ^ N * ‖u z‖ ≤ B N) {j : ℕ} {u : Z → ℂ} (hu : u ∈ S) {z : Z}
    (hz : j = 0 ∨ (2 : ℝ) ^ j ≤ 2 * ‖z‖) : ‖u z‖ ≤ cf S j :=
  le_csSup (bdd_env hB j) (Set.mem_insert_of_mem _ ⟨u, hu, z, hz, rfl⟩)

theorem cf_mul_le (hB : ∀ N, ∀ u ∈ S, ∀ z, (1 + ‖z‖) ^ N * ‖u z‖ ≤ B N) (N j : ℕ) :
    cf S j * ((2 : ℝ) ^ j) ^ N ≤ 2 ^ N * max (B N) 0 := by
  have hp : (0 : ℝ) < ((2 : ℝ) ^ j) ^ N := by positivity
  rw [← le_div_iff₀ hp]
  refine csSup_le (Set.insert_nonempty 0 _) fun r hr => ?_
  rw [le_div_iff₀ hp]
  exact mem_env_le hB N j r hr

theorem summable_cf_mul (hB : ∀ N, ∀ u ∈ S, ∀ z, (1 + ‖z‖) ^ N * ‖u z‖ ≤ B N) (m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Summable fun j => cf S j * ((2 : ℝ) ^ j) ^ m * c := by
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (mul_nonneg (cf_nonneg hB j) (by positivity)) hc)
    (fun j => ?_) ((summable_geometric_two.mul_left (2 ^ (m + 1) * max (B (m + 1)) 0)).mul_right c)
  apply mul_le_mul_of_nonneg_right _ hc
  have h := cf_mul_le hB (m + 1) j
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [pow_succ, ← mul_assoc] at h
  rw [one_div_pow, ← div_eq_mul_one_div, le_div_iff₀ hp]
  exact h

end Coef

theorem schDom {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (S : Set (Z → ℂ))
    (hS : ∀ N : ℕ, ∃ B : ℝ, ∀ u ∈ S, ∀ z, (1 + ‖z‖) ^ N * ‖u z‖ ≤ B) :
    ∃ F : SchwartzMap Z ℂ, ∀ u ∈ S, ∀ z, ‖u z‖ ≤ ‖F z‖ := by
  choose B hB using hS
  let ρ : ContDiffBump (0 : Z) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  choose M hM0 hM using exists_bound_iteratedFDeriv ρ
  let f : ℕ → Z → ℝ := fun j => cf S j • dy ρ j
  have hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j) := fun j => by
    change ContDiff ℝ _ (fun y => cf S j • dy ρ j y)
    exact (contDiff_dy ρ j).const_smul _
  have hDf : ∀ (k j : ℕ) (x : Z), ‖iteratedFDeriv ℝ k (f j) x‖ = cf S j * ‖iteratedFDeriv ℝ k (dy ρ j) x‖ := by
    intro k j x
    rw [iteratedFDeriv_const_smul_apply ((contDiff_dy ρ j (n := (k : ℕ∞))).contDiffAt), norm_smul,
      Real.norm_of_nonneg (cf_nonneg hB j)]
  have hv : ∀ k : ℕ, ((k : ℕ∞) ≤ ⊤) → Summable fun j => cf S j * ((2 : ℝ) ^ j) ^ 0 * M k :=
    fun k _ => summable_cf_mul hB 0 (M k) (hM0 k)
  have h'f : ∀ (k j : ℕ) (x : Z), ((k : ℕ∞) ≤ ⊤) → ‖iteratedFDeriv ℝ k (f j) x‖ ≤ cf S j * ((2 : ℝ) ^ j) ^ 0 * M k := by
    intro k j x _
    rw [hDf, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left ((norm_iteratedFDeriv_dy_le ρ j k x).trans (hM k _)) (cf_nonneg hB j)
  let Fr : Z → ℝ := fun x => ∑' j, f j x
  have hFr : ContDiff ℝ (⊤ : ℕ∞) Fr := contDiff_tsum hf hv h'f

  have hw : ∀ (m k j : ℕ) (x : Z), ‖x‖ ^ m * ‖iteratedFDeriv ℝ k (f j) x‖ ≤ cf S j * ((2 : ℝ) ^ j) ^ m * (2 ^ m * M k) := by
    intro m k j x
    rw [hDf]
    by_cases hx : ‖x‖ ≤ 2 ^ j * 2
    · have h1 : ‖x‖ ^ m ≤ ((2 : ℝ) ^ j) ^ m * 2 ^ m := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hx m
      have h2 : ‖iteratedFDeriv ℝ k (dy ρ j) x‖ ≤ M k := (norm_iteratedFDeriv_dy_le ρ j k x).trans (hM k _)
      calc ‖x‖ ^ m * (cf S j * ‖iteratedFDeriv ℝ k (dy ρ j) x‖)
          ≤ (((2 : ℝ) ^ j) ^ m * 2 ^ m) * (cf S j * M k) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (cf_nonneg hB j)) (mul_nonneg (cf_nonneg hB j) (norm_nonneg _))
              (by positivity)
        _ = cf S j * ((2 : ℝ) ^ j) ^ m * (2 ^ m * M k) := by ring
    · have hfar : ρ.rOut < ‖sc j x‖ := by
        rw [norm_sc]
        show (2 : ℝ) < ‖x‖ / 2 ^ j
        rw [lt_div_iff₀ (by positivity)]
        linarith [not_le.1 hx]
      have h0 : ‖iteratedFDeriv ℝ k (dy ρ j) x‖ = 0 := by
        refine le_antisymm ((norm_iteratedFDeriv_dy_le ρ j k x).trans ?_) (norm_nonneg _)
        rw [iteratedFDeriv_eq_zero_of_far ρ k hfar, norm_zero]
      rw [h0, mul_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (cf_nonneg hB j) (by positivity)) (mul_nonneg (by positivity) (hM0 k))
  have hdecay : ∀ m k : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ m * ‖iteratedFDeriv ℝ k Fr x‖ ≤ C := by
    intro m k
    refine ⟨∑' j, cf S j * ((2 : ℝ) ^ j) ^ m * (2 ^ m * M k), fun x => ?_⟩
    have hs : Summable fun j => ‖iteratedFDeriv ℝ k (f j) x‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => h'f k j x le_top) (hv k le_top)
    rw [iteratedFDeriv_tsum_apply hf hv h'f le_top]
    calc ‖x‖ ^ m * ‖∑' j, iteratedFDeriv ℝ k (f j) x‖ ≤ ‖x‖ ^ m * ∑' j, ‖iteratedFDeriv ℝ k (f j) x‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) (by positivity)
      _ = ∑' j, ‖x‖ ^ m * ‖iteratedFDeriv ℝ k (f j) x‖ := (tsum_mul_left).symm
      _ ≤ ∑' j, cf S j * ((2 : ℝ) ^ j) ^ m * (2 ^ m * M k) :=
          Summable.tsum_le_tsum (fun j => hw m k j x) (hs.mul_left _)
            (summable_cf_mul hB m _ (mul_nonneg (by positivity) (hM0 k)))
  let F : SchwartzMap Z ℂ :=
    { toFun := fun x => ((Fr x : ℝ) : ℂ)
      smooth' := Complex.ofRealCLM.contDiff.comp hFr
      decay' := by
        intro m k
        obtain ⟨C, hC⟩ := hdecay m k
        refine ⟨C, fun x => ?_⟩
        have e : (fun x => ((Fr x : ℝ) : ℂ)) = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ Fr := rfl
        rw [e, LinearIsometry.norm_iteratedFDeriv_comp_left _ (hFr.contDiffAt (x := x))
          (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
        exact hC x }
  refine ⟨F, fun u hu z => ?_⟩
  have hF : ‖F z‖ = |Fr z| := by
    show ‖((Fr z : ℝ) : ℂ)‖ = _
    exact Complex.norm_real _
  rw [hF]
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt ‖z‖ (one_lt_two : (1 : ℝ) < 2)
  have hex : ∃ j : ℕ, ‖z‖ ≤ 2 ^ j := ⟨n0, hn0.le⟩
  classical
  let j := Nat.find hex
  have hj : ‖z‖ ≤ 2 ^ j := Nat.find_spec hex
  have hcond : j = 0 ∨ (2 : ℝ) ^ j ≤ 2 * ‖z‖ := by
    rcases Nat.eq_zero_or_eq_succ_pred j with h | h
    · exact Or.inl h
    · right
      have hmin := Nat.find_min hex (show j.pred < j by omega)
      rw [h, pow_succ]
      linarith [not_le.1 hmin]
  have hone : dy ρ j z = 1 := by
    apply ρ.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_sc]
    show ‖z‖ / 2 ^ j ≤ 1
    rw [div_le_one (by positivity)]
    exact hj
  have hnn : ∀ i, 0 ≤ f i z := fun i => mul_nonneg (cf_nonneg hB i) (ρ.nonneg)
  have hsum : Summable fun i => f i z := by
    refine Summable.of_nonneg_of_le hnn (fun i => ?_) (summable_cf_mul hB 0 1 zero_le_one)
    show cf S i * dy ρ i z ≤ cf S i * ((2 : ℝ) ^ i) ^ 0 * 1
    rw [pow_zero, mul_one, mul_one]
    exact mul_le_of_le_one_right (cf_nonneg hB i) ρ.le_one
  calc ‖u z‖ ≤ cf S j := le_cf hB hu hcond
    _ = f j z := by show cf S j = cf S j * dy ρ j z; rw [hone, mul_one]
    _ ≤ Fr z := hsum.le_tsum j (fun i _ => hnn i)
    _ ≤ |Fr z| := le_abs_self _

end PositivityTheory.Rg.Rsw.L.LWMaj

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LmajABumpDerivZero
section
noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

def lmajABump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

lemma lmajABump_bound (m : ℕ) : ∃ C, ∀ t : ℝ, ‖iteratedFDeriv ℝ m lmajABump t‖ ≤ C :=
  ((lmajABump.contDiff (n := ⊤)).continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
    (lmajABump.hasCompactSupport.iteratedFDeriv m)

lemma lmajABump_deriv_zero (m : ℕ) (t : ℝ) (ht : 2 < |t|) : iteratedFDeriv ℝ m lmajABump t = 0 := by
  by_contra hne
  have h1 : t ∈ tsupport (lmajABump : ℝ → ℝ) := support_iteratedFDeriv_subset m hne
  rw [lmajABump.tsupport_eq, mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  exact absurd h1 (by simp [lmajABump]; linarith)

theorem lmajASeqSchwartz (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ k : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ k)) :
    ∃ h : SchwartzMap ℝ ℂ, (∀ t, 0 ≤ (h t).re ∧ (h t).im = 0) ∧
      ∀ (n : ℕ) (t : ℝ), |t - n| ≤ 1 → b n ≤ (h t).re := by
  choose C hC using lmajABump_bound
  set φ : ℕ → ℝ → ℝ := fun n => b n • fun t => lmajABump (t - n) with hφ
  have hφc : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    ((lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)).const_smul (b n)
  have hD : ∀ m n t, iteratedFDeriv ℝ m (φ n) t = b n • iteratedFDeriv ℝ m lmajABump (t - n) := by
    intro m n t
    have hc : ContDiff ℝ m (fun t : ℝ => lmajABump (t - n)) :=
      (lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)
    rw [hφ]
    simp only
    rw [iteratedFDeriv_const_smul_apply hc.contDiffAt, iteratedFDeriv_comp_sub]
  have hs0 : Summable b := by simpa using hb 0
  have hv : ∀ m : ℕ, ((m : ℕ∞)) ≤ (⊤ : ℕ∞) → Summable (fun n => b n * C m) :=
    fun m _ => hs0.mul_right _
  have hbd : ∀ (m : ℕ) (n : ℕ) (t : ℝ), ((m : ℕ∞)) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ m (φ n) t‖ ≤ b n * C m := by
    intro m n t _
    rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
    exact mul_le_mul_of_nonneg_left (hC m _) (hb0 n)
  set g : ℝ → ℝ := fun t => ∑' n, φ n t with hg
  have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_tsum hφc hv hbd
  have hφv : ∀ n t, φ n t = b n * lmajABump (t - n) := fun n t => rfl
  have hφs : ∀ t, Summable (fun n => φ n t) := by
    intro t
    refine hs0.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
    · rw [hφv]; exact mul_le_of_le_one_right (hb0 n) (lmajABump.le_one)
  have hg0 : ∀ t, 0 ≤ g t := fun t => tsum_nonneg fun n => by
    rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
  have hdecay : ∀ k m : ℕ, ∀ t : ℝ, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m g t‖ ≤
      ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
    intro k m t
    rw [hg, iteratedFDeriv_tsum_apply hφc hv hbd (mod_cast le_top) t]
    have hsn : Summable (fun n => ‖iteratedFDeriv ℝ m (φ n) t‖) :=
      (hv m le_top).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd m n t le_top)
    calc ‖t‖ ^ k * ‖∑' n, iteratedFDeriv ℝ m (φ n) t‖
        ≤ ‖t‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ m (φ n) t‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsn) (by positivity)
      _ = ∑' n, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m (φ n) t‖ := (tsum_mul_left).symm
      _ ≤ ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
          refine (hsn.mul_left _).tsum_le_tsum (fun n => ?_) ((hb k).mul_right _)
          rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
          by_cases htn : |t - n| ≤ 2
          · have h1 : ‖t‖ ≤ (n : ℝ) + 2 := by
              rw [Real.norm_eq_abs]
              have := abs_sub_abs_le_abs_sub t n
              rw [Nat.abs_cast] at this
              linarith
            have h2 : ‖t‖ ^ k ≤ ((n : ℝ) + 2) ^ k := pow_le_pow_left₀ (norm_nonneg _) h1 k
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            calc ‖t‖ ^ k * (b n * ‖iteratedFDeriv ℝ m (lmajABump : ℝ → ℝ) (t - n)‖)
                ≤ ((n : ℝ) + 2) ^ k * (b n * C m) :=
                  mul_le_mul h2 (mul_le_mul_of_nonneg_left (hC m _) (hb0 n)) (mul_nonneg (hb0 n) (norm_nonneg _))
                    (by positivity)
              _ = b n * ((n : ℝ) + 2) ^ k * C m := by ring
          · rw [lmajABump_deriv_zero m _ (not_le.mp htn), norm_zero, mul_zero, mul_zero]
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            exact mul_nonneg (mul_nonneg (hb0 n) (by positivity)) hCm
  refine ⟨⟨Complex.ofRealLI ∘ g, ?_, ?_⟩, ?_, ?_⟩
  · exact Complex.ofRealLI.contDiff.comp hgc
  · intro k m
    refine ⟨∑' n, b n * ((n : ℝ) + 2) ^ k * C m, fun t => ?_⟩
    rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hgc.contDiffAt (mod_cast le_top)]
    exact hdecay k m t
  · intro t
    show 0 ≤ (Complex.ofRealLI (g t)).re ∧ (Complex.ofRealLI (g t)).im = 0
    simp [hg0 t]
  · intro n t ht
    have h1 : (t - n) ∈ closedBall (0 : ℝ) lmajABump.rIn := by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]; simpa [lmajABump] using ht
    have h2 : φ n t = b n := by rw [hφv, lmajABump.one_of_mem_closedBall h1, mul_one]
    show b n ≤ (Complex.ofRealLI (g t)).re
    simp only [Complex.ofRealLI_apply, Complex.ofReal_re]
    rw [← h2]
    exact (hφs t).le_tsum n (fun j _ => by rw [hφv]; exact mul_nonneg (hb0 j) (lmajABump.nonneg))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

