module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EchelonProjectorKernelFrobenius
section
open scoped NNReal

namespace GlobalTheory

open Matrix

theorem echelon_projector_frobenius (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l]
    (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C) (hA : A.det ≠ 0)
    (hY : Y.map (frobenius C l) = Y * A) :
    ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧
      (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧
      (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧
      Q = A * Q.map (frobenius C l) * Λ := by
  classical
  set N : Submodule C (Fin d → C) := LinearMap.ker (Matrix.toLin' Y) with hN
  let e : Fin d → (Fin d → C) := fun k => Pi.single k 1

  have hsupp : ∀ (S : Set (Fin d)) (v : Fin d → C), (∀ i, i ∉ S → v i = 0) →
      v ∈ Submodule.span C (e '' S) := by
    intro S v hv
    rw [show v = ∑ k, Pi.single k (v k) from (Finset.univ_sum_single v).symm]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k ∈ S
    · have : Pi.single k (v k) = v k • e k := by
        ext i; simp [e, Pi.single_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [hv k hk, Pi.single_zero]; exact Submodule.zero_mem _
  have hspan : Submodule.span C (Set.range (N.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span]
    have : Submodule.span C (Set.range e) = ⊤ := by
      rw [eq_top_iff]; intro v _
      have := hsupp Set.univ v (fun i hi => absurd (Set.mem_univ i) hi)
      rwa [Set.image_univ] at this
    rw [this, Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' C (N.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  set W : Submodule C (Fin d → C) := Submodule.span C (e '' Set.range a) with hW
  have hWeq : W = Submodule.span C (Set.range (e ∘ a)) := by rw [hW, Set.range_comp]
  have hWcoord : ∀ w ∈ W, ∀ i, i ∉ Set.range a → w i = 0 := by
    intro w hw i hi
    refine Submodule.span_induction (p := fun w _ => w i = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, ⟨m, rfl⟩, rfl⟩
      have : i ≠ a m := fun h => hi ⟨m, h.symm⟩
      simp [e, Pi.single_apply, this]
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro c x _ hx; simp [hx]
  have hc : IsCompl N W := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro y ⟨hyN, hyW⟩
      rw [hWeq] at hyW
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp hyW
      have h0 : ∑ j, c j • (N.mkQ ∘ e ∘ a) j = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Function.comp_apply, ← map_smul, ← map_sum]
        exact (Submodule.Quotient.mk_eq_zero N).mpr hyN
      have hc0 := Fintype.linearIndependent_iff.mp hli c h0
      simp [hc0]
    · rw [codisjoint_iff, ← Submodule.map_mkQ_eq_top, hWeq, Submodule.map_span, ← Set.range_comp]
      exact hsp.trans hspan
  set P := N.projection W hc with hP
  set Q : Matrix (Fin d) (Fin d) C := LinearMap.toMatrix' P with hQ
  have hQv : ∀ v, Q *ᵥ v = P v := fun v => by
    rw [← Matrix.toLin'_apply, hQ, Matrix.toLin'_toMatrix']
  have hPN : ∀ v, P v ∈ N := fun v => Submodule.projection_apply_mem hc v
  have hmemN : ∀ v, v ∈ N ↔ Y *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.toLin'_apply]
  have key : ∀ X Z : Matrix (Fin d) (Fin d) C, (∀ v, X *ᵥ v = Z *ᵥ v) → X = Z :=
    fun X Z h => Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)
  have hYQ : Y * Q = 0 := key _ _ fun v => by
    rw [← Matrix.mulVec_mulVec, hQv, Matrix.zero_mulVec]; exact (hmemN _).mp (hPN v)
  set I : Finset (Fin d) := Finset.univ.filter (fun i => i ∉ Set.range a) with hI
  have hmemI : ∀ i, i ∈ I ↔ i ∉ Set.range a := fun i => by simp [hI]
  have hrow : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0 := by
    intro i hi j
    rw [hQ, LinearMap.toMatrix'_apply]
    have h1 := hWcoord _ (Submodule.sub_projection_mem hc (Pi.single j (1 : C))) i ((hmemI i).mp hi)
    rw [Pi.sub_apply, sub_eq_zero, Pi.single_apply] at h1
    rw [← hP] at h1
    exact h1.symm
  have hcol : ∀ i, ∀ j ∉ I, Q i j = 0 := by
    intro i j hj
    rw [hmemI, not_not] at hj
    rw [hQ, LinearMap.toMatrix'_apply]
    have : Pi.single j (1 : C) ∈ W := Submodule.subset_span ⟨j, hj, rfl⟩
    rw [Submodule.projection_apply_of_mem_right hc this]; rfl

  set M : Matrix (Fin d) (Fin d) C := A * Q.map (frobenius C l) with hM
  have hYM : Y * M = 0 := by
    rw [hM, ← mul_assoc, ← hY, ← Matrix.map_mul, hYQ, Matrix.map_zero _ (map_zero _)]
  have hrangeN : LinearMap.range (Matrix.toLin' M) ≤ N := by
    rintro _ ⟨v, rfl⟩
    rw [hmemN, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hYM, Matrix.zero_mulVec]
  have hkerW : LinearMap.ker (Matrix.toLin' M) ≤ W := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hM, ← Matrix.mulVec_mulVec] at hv
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have h0 : Q.map (frobenius C l) *ᵥ v = 0 := by
      have := congrArg (fun x => A⁻¹ *ᵥ x) hv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← mul_assoc, Matrix.nonsing_inv_mul A hAu, one_mul] at this
    have := hsupp (Set.range a) v (fun i hi => by
      have hi' : i ∈ I := (hmemI i).mpr hi
      have h2 := congrFun h0 i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hrow i hi', Pi.zero_apply] at h2
      simpa [apply_ite] using h2)
    rwa [← hW] at this
  have hrange : LinearMap.range (Matrix.toLin' M) = N := by
    refine Submodule.eq_of_le_of_finrank_le hrangeN ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
    have h2 := Submodule.finrank_add_eq_of_isCompl hc
    have h3 := Submodule.finrank_mono hkerW
    omega
  have hex : ∀ j, ∃ w, Matrix.toLin' M w = P (Pi.single j 1) := fun j => by
    have : P (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' M) := hrange ▸ hPN _
    exact this
  choose lam hlam using hex
  refine ⟨I, Q, Matrix.of fun k j => lam j k, hYQ, fun v hv => ?_, hrow, hcol, ?_⟩
  · rw [hQv]; exact Submodule.projection_apply_of_mem_left hc ((hmemN v).mpr hv)
  · ext i j
    rw [← hM, Matrix.mul_apply]
    have := congrFun (hlam j) i
    rw [Matrix.toLin'_apply] at this
    rw [hQ, LinearMap.toMatrix'_apply, ← this]
    simp [Matrix.mulVec, dotProduct]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvectorMemOfSumMem
section
namespace GlobalTheory.EigenvectorOfSum

theorem eigenvector_mem_of_sum_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ (g : I), ∀ y ∈ U, (T g : Y → Y) y ∈ U) (S : Finset α) (y : α → Y)
    (hy : ∀ a ∈ S, ∀ (g : I), (T g : Y → Y) (y a) = χ a g • y a)
    (hs : ∑ a ∈ S, y a ∈ U) : ∀ a ∈ S, y a ∈ U := by
  classical
  induction S using Finset.strongInduction generalizing y with
  | H S ih =>
  intro a ha
  by_cases hex : ∃ b ∈ S, b ≠ a
  · obtain ⟨b, hb, hba⟩ := hex
    obtain ⟨g, hg⟩ : ∃ g, χ a g ≠ χ b g := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      exact hba (hχ (funext hcon)).symm
    set y' : α → Y := fun c => (χ c g - χ b g) • y c with hyq
    have hy' : ∀ c ∈ S.erase b, ∀ g', (T g' : Y → Y) (y' c) = χ c g' • y' c := by
      intro c hc g'
      rw [hyq, map_smul, hy c (Finset.mem_of_mem_erase hc) g', smul_comm]
    have hs' : ∑ c ∈ S.erase b, y' c ∈ U := by
      have h1 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c ∈ U :=
        U.sub_mem (hU g _ hs) (U.smul_mem _ hs)
      have h2 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c = ∑ c ∈ S.erase b, y' c := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hb]
        have hb0 : (T g : Y → Y) (y b) - χ b g • y b = 0 := by rw [hy b hb g, sub_self]
        rw [hb0, add_zero]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [hyq]
        dsimp only
        rw [sub_smul, hy c (Finset.mem_of_mem_erase hc) g]
      rwa [h2] at h1
    have hmem := ih (S.erase b) (Finset.erase_ssubset hb) y' hy' hs' a
      (Finset.mem_erase.2 ⟨hba.symm, ha⟩)
    have hne : χ a g - χ b g ≠ 0 := sub_ne_zero.2 hg
    have h3 := U.smul_mem (χ a g - χ b g)⁻¹ hmem
    rwa [hyq, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
  · simp only [ne_eq, not_exists, not_and, not_not] at hex
    have hS : S = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, hex⟩
    subst hS
    simpa using hs

end GlobalTheory.EigenvectorOfSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
section
namespace GlobalTheory

open Polynomial in
private lemma norm_le_one_of_monic_root_lemma {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p : K[X]} (hp : p.Monic) (hc : ∀ i, ‖p.coeff i‖ ≤ 1) {x : K} (hx : p.eval x = 0) :
    ‖x‖ ≤ 1 := by
  by_contra h
  push_neg at h
  rw [hp.as_sum] at hx
  simp only [eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum, eval_mul, eval_C] at hx
  set n := p.natDegree
  have hxn : x ^ n = -∑ i ∈ Finset.range n, p.coeff i * x ^ i := eq_neg_of_add_eq_zero_left hx
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at hxn
    simp at hxn
  have hle : ‖x ^ n‖ ≤ ‖x‖ ^ (n - 1) := by
    rw [hxn, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖p.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) := by
          gcongr
          · exact hc i
          · exact h.le
      _ = ‖x‖ ^ (n - 1) := one_mul _
  rw [norm_pow] at hle
  have hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith


open Polynomial in
theorem _root_.GlobalTheory.padicAlgCl_embedding_bounded_continuous (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O))
    (ι : O →+* PadicAlgCl l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) :
    (∀ a, ‖ι a‖ ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal O, ‖ι a‖ < 1) ∧ Continuous ι := by
  set g : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hg : ι.comp (algebraMap ℤ_[l] O) = g := by
    ext z
    exact hι z
  have h1 : ∀ a, ‖ι a‖ ≤ 1 := by
    intro a
    obtain ⟨p, hpm, hpa⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a
    have hroot : (p.map g).eval (ι a) = 0 := by
      rw [eval_map, ← hg, ← hom_eval₂]
      rw [hpa, map_zero]
    refine norm_le_one_of_monic_root_lemma (hpm.map g) (fun i => ?_) hroot
    rw [coeff_map]
    change ‖algebraMap ℚ_[l] (PadicAlgCl l) ((p.coeff i : ℤ_[l]) : ℚ_[l])‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact PadicInt.norm_le_one _
  have hunit : ∀ u : Oˣ, ‖ι u‖ = 1 := by
    intro u
    have hprod : ‖ι u‖ * ‖ι ↑u⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have ha := h1 u
    have hb := h1 ↑u⁻¹
    have ha0 := norm_nonneg (ι u)
    have hb0 := norm_nonneg (ι ↑u⁻¹)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖlt : ‖ι ϖ‖ < 1 := by
    refine lt_of_le_of_ne (h1 ϖ) fun heq => ?_
    set x := algebraMap ℤ_[l] O (l : ℤ_[l])
    have hx : ‖ι x‖ = ‖(l : ℚ_[l])‖ := by
      rw [hι, PadicAlgCl.norm_extends]
      push_cast
      rfl
    have hlt : ‖ι x‖ < 1 := hx ▸ Padic.norm_p_lt_one
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero, norm_zero] at hx
      have : (0 : ℝ) < ‖(l : ℚ_[l])‖ := by
        rw [Padic.norm_p]
        have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
        positivity
      linarith
    obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [hxu, map_mul, norm_mul, map_pow, norm_pow, heq, one_pow, mul_one, hunit] at hlt
    exact lt_irrefl _ hlt
  have hpow : ∀ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal O ^ n, ‖ι a‖ ≤ ‖ι ϖ‖ ^ n := by
    intro n a ha
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖ι b‖ * ‖ι ϖ‖ ^ n ≤ 1 * ‖ι ϖ‖ ^ n := by gcongr; exact h1 b
      _ = ‖ι ϖ‖ ^ n := one_mul _
  refine ⟨h1, fun a ha => ?_, ?_⟩
  · have := hpow 1 a (by rwa [pow_one])
    rw [pow_one] at this
    exact this.trans_lt hϖlt
  · refine continuous_of_continuousAt_zero ι ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖlt
    have hopen := (isAdic_iff.mp hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
    rw [dist_zero_right]
    exact (hpow n a ha).trans_lt hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqBotOrEqTopOfInvariant
section
namespace GlobalTheory.InvariantSupremum

theorem eq_bot_or_eq_top_of_invariant {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (P : Submodule ℂ W)
    (hP : ∀ g : G, ∀ w ∈ P, σ g w ∈ P) : P = ⊥ ∨ P = ⊤ := by
  let Q : Subrepresentation σ :=
    { toSubmodule := P
      apply_mem_toSubmodule := by
        intro g v hv
        exact hP g v hv }
  rcases @IsSimpleOrder.eq_bot_or_eq_top _ _ _ hσ Q with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem fixed_mem_of_mem_iSup_range {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ι : Type} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (f : ι → W →ₗ[ℂ] V)
    (hf : ∀ (i : ι) (g : G) (u : W), f i (σ g u) = ρ g (f i u)) (K : Set G)
    (Z : Submodule ℂ V) (hZ : ∀ (i : ι) (v : W), (∀ k ∈ K, σ k v = v) → f i v ∈ Z)
    (_hfix : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V) (hφ : ∀ k ∈ K, ρ k φ = φ)
    (hmem : φ ∈ ⨆ i : ι, LinearMap.range (f i)) : φ ∈ Z := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  clear hmem

  have inv : ∀ (t : Finset ι) (g : G), ∀ z ∈ ⨆ i ∈ t, LinearMap.range (f i),
      ρ g z ∈ ⨆ i ∈ t, LinearMap.range (f i) := by
    intro t g z hz
    have hle : (⨆ i ∈ t, LinearMap.range (f i)) ≤
        (⨆ i ∈ t, LinearMap.range (f i)).comap (ρ g) := by
      refine iSup₂_le fun i hi => ?_
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_comap, ← hf i g w]
      exact (le_iSup₂ (f := fun i (_ : i ∈ t) => LinearMap.range (f i)) i hi)
        (LinearMap.mem_range_self _ _)
    exact hle hz
  induction s using Finset.induction_on generalizing φ with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hs
    rw [hs]
    exact Z.zero_mem
  | @insert j s hj ih =>
    rw [Finset.iSup_insert, Submodule.mem_sup] at hs
    obtain ⟨y, ⟨u, rfl⟩, z, hz, rfl⟩ := hs

    rcases eq_bot_or_eq_top_of_invariant σ hσ ((⨆ i ∈ s, LinearMap.range (f i)).comap (f j)) (by
        intro g w hw
        rw [Submodule.mem_comap] at hw ⊢
        rw [hf]
        exact inv s g _ hw) with hN | hN
    ·
      have hu : ∀ k ∈ K, σ k u = u := by
        intro k hk
        have e : ρ k (f j u) - f j u = z - ρ k z := by
          rw [sub_eq_sub_iff_add_eq_add, ← map_add (f := _), hφ k hk, add_comm]
        have h1 : σ k u - u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [Submodule.mem_comap, map_sub, hf, e]
          exact Submodule.sub_mem _ hz (inv s k z hz)
        rw [hN, Submodule.mem_bot, sub_eq_zero] at h1
        exact h1
      have hzfix : ∀ k ∈ K, ρ k z = z := by
        intro k hk
        have h2 := hφ k hk
        rw [map_add (f := _), ← hf, hu k hk] at h2
        exact add_left_cancel h2
      exact Z.add_mem (hZ j u hu) (ih z hzfix hz)
    ·
      have hu : f j u ∈ ⨆ i ∈ s, LinearMap.range (f i) := by
        have h3 : u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [hN]
          trivial
        exact h3
      exact ih _ hφ (Submodule.add_mem _ hu hz)

end GlobalTheory.InvariantSupremum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq
section
namespace GlobalTheory

theorem eq_of_nodup_sum_multiset_of_eq (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by
  by_contra hne
  have hle : B i + B j ≤ ∑ k, B k := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hnd : (B i + B j).Nodup := Multiset.nodup_of_le hle h
  rw [← hij] at hnd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hi
  exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnit
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_root_congr_of_deriv_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω)
    (hβ : A.valuation β ≤ 1) (hβ' : A.valuation β' ≤ 1) (h0 : Polynomial.aeval β f = 0) (h0' : Polynomial.aeval β' f = 0)
    (hd : ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1) (hs : A.valuation (β - β') < 1) : β = β' := by
  by_contra hne
  have hb : β ∈ A := (A.valuation_le_one_iff β).mp hβ
  have hb' : β' ∈ A := (A.valuation_le_one_iff β').mp hβ'
  set b : A := ⟨β, hb⟩
  set b' : A := ⟨β', hb'⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map (algebraMap ℤ A)) b (b' - b)
  rw [add_sub_cancel, derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap] at hk
  have hc := congrArg (fun x : A => (x : Ω)) hk
  have e : ∀ (p : ℤ[X]) (x : A), ((aeval x p : A) : Ω) = aeval (x : Ω) p := by
    intro p x
    exact (aeval_algebraMap_apply Ω x p).symm
  push_cast at hc
  rw [e, e, e] at hc
  have hβ0 : (b : Ω) = β := rfl
  have hβ1 : (b' : Ω) = β' := rfl
  rw [hβ0, hβ1, h0, h0'] at hc
  have hne' : β' - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hD : aeval β (derivative f) = -((k : Ω) * (β' - β)) := by
    have : (β' - β) * (aeval β (derivative f) + (k : Ω) * (β' - β)) = 0 := by linear_combination -hc
    have := (mul_eq_zero.mp this).resolve_left hne'
    linear_combination this
  apply hd
  rw [hD, Valuation.map_neg, Valuation.map_mul, Valuation.map_sub_swap]
  have hk1 : A.valuation (k : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr k.2
  calc A.valuation (k : Ω) * A.valuation (β - β') ≤ 1 * A.valuation (β - β') := by gcongr
    _ = A.valuation (β - β') := one_mul _
    _ < 1 := hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOne
section
universe u_1

namespace GlobalTheory.PowerEqOneClose

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = (u ^ n - 1) * u + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans ih

theorem norm_geom_sum_sub_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ih (norm_pow_sub_one_le u hu n))

theorem eq_one_of_pow_eq_one {K : Type u_1} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = (1 : ℝ)) (u : K) (hu : u ^ m = (1 : K)) (h : ‖u - (1 : K)‖ < (1 : ℝ)) :
    u = (1 : K) := by
  have hu1 : ‖u‖ ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le norm_one.le)
  have hs := norm_geom_sum_sub_le u hu1 m
  have hg : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  rcases mul_eq_zero.mp hg with h0 | h0
  · rw [h0, zero_sub, norm_neg, hm] at hs
    exact absurd h (not_lt.mpr hs)
  · exact sub_eq_zero.mp h0

end GlobalTheory.PowerEqOneClose
end

