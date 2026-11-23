module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PrimeAvoidanceFibre
section
namespace ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre

open IsLocalRing

theorem avoid {B : Type*} [CommRing B] [IsNoetherianRing B] (M q : Ideal B) [hM : M.IsMaximal] (w : B)
    (hchain : ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M) :
    ∃ s ∉ M, ∀ P : Ideal B, P.IsPrime → q ≤ P → w ∈ P → s ∉ P → P = M := by
  classical
  haveI := hM.isPrime
  set I : Ideal B := q ⊔ Ideal.span {w} with hI
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  have hprop : ∀ p ∈ I.minimalPrimes, p.IsPrime ∧ I ≤ p := fun p hp => hp.1
  have hnot : ∀ p ∈ I.minimalPrimes, p ≠ M → ¬ p ≤ M := by
    intro p hp hne hle
    obtain ⟨hpp, hIp⟩ := hprop p hp
    exact hne (hchain p hpp (le_trans le_sup_left hIp) hle
      (hIp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self w))))
  have hex : ∀ p ∈ I.minimalPrimes, p ≠ M → ∃ x ∈ p, x ∉ M :=
    fun p hp hne => SetLike.not_le_iff_exists.mp (hnot p hp hne)
  let f : Ideal B → B := fun p =>
    if h : p ∈ I.minimalPrimes ∧ p ≠ M then (hex p h.1 h.2).choose else 1
  let T := hfin.toFinset.filter (· ≠ M)
  refine ⟨∏ p ∈ T, f p, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hpT, hpM⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset] at hpT
    have h1 := (hex p hpT.1 hpT.2).choose_spec.2
    simp only [f, dif_pos hpT] at hpM
    exact h1 hpM
  · intro P hP hqP hwP hsP
    have hIP : I ≤ P := sup_le hqP ((Ideal.span_singleton_le_iff_mem P).mpr hwP)
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le hIP
    by_cases hpM : p = M
    · rw [hpM] at hpP
      exact (hM.eq_of_le hP.ne_top hpP).symm
    · exfalso
      apply hsP
      apply Ideal.IsPrime.prod_mem_iff.mpr
      refine ⟨p, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hp, hpM⟩
      · simp only [f, dif_pos (And.intro hp hpM)]
        exact hpP (hex p hp hpM).choose_spec.1

theorem finite_of_fibre {O T : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing T] [IsDomain T] [IsNoetherianRing T] [Algebra O T]
    [Algebra.FiniteType O T] (ϖ : O) (hϖ : Irreducible ϖ)
    (hex : ∃ P : Ideal T, P.IsPrime ∧ algebraMap O T ϖ ∈ P)
    (huniq : ∀ P P' : Ideal T, P.IsPrime → P'.IsPrime → algebraMap O T ϖ ∈ P → algebraMap O T ϖ ∈ P' →
      P = P') : Module.Finite O T := by
  classical
  set w := algebraMap O T ϖ with hw
  set J : Ideal T := Ideal.span {w} with hJ
  obtain ⟨P0, hP0, hwP0⟩ := hex
  have hJtop : J ≠ ⊤ := fun h => hP0.ne_top (eq_top_iff.2 (h ▸ (Ideal.span_singleton_le_iff_mem P0).2 hwP0))

  have hdim : Ring.KrullDimLE 0 (T ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI.ne_top
    have hwI : w ∈ Ideal.comap (Ideal.Quotient.mk J) I := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self w)]
      exact I.zero_mem
    have hwN : w ∈ Ideal.comap (Ideal.Quotient.mk J) N := Ideal.comap_mono hIN hwI
    have e := huniq _ _ (Ideal.comap_isPrime _ I) (Ideal.comap_isPrime _ N) hwI hwN
    have : I = N := by
      have h1 := congrArg (Ideal.map (Ideal.Quotient.mk J)) e
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    rw [this]; exact hN
  have hart : IsArtinianRing (T ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

  have hmJ : maximalIdeal O ≤ Ideal.comap (algebraMap O T) J := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self w
  let _ : Algebra (O ⧸ maximalIdeal O) (T ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hmJ
  have hmk : ∀ c : O, algebraMap (O ⧸ maximalIdeal O) (T ⧸ J) (Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk J (algebraMap O T c) := fun c => rfl
  have : IsScalarTower O (O ⧸ maximalIdeal O) (T ⧸ J) := IsScalarTower.of_algebraMap_eq fun c => (hmk c).symm
  have : Algebra.FiniteType O (T ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O J) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (O ⧸ maximalIdeal O) (T ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have : IsJacobsonRing (O ⧸ maximalIdeal O) := by
    let _ := Ideal.Quotient.field (maximalIdeal O); infer_instance
  have : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ J) := Module.finite_of_isArtinianRing _ _
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := O ⧸ maximalIdeal O) (M := T ⧸ J)
  choose S hS using fun i => Ideal.Quotient.mk_surjective (g i)
  have hgen : ∀ x : T, ∃ c : Fin n → O, ∃ y : T, x = ∑ i, c i • S i + ϖ • y := by
    intro x
    have hx : Ideal.Quotient.mk J x ∈ Submodule.span (O ⧸ maximalIdeal O) (Set.range g) := by
      rw [hg]; trivial
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    choose c hc using fun i => Ideal.Quotient.mk_surjective (cb i)
    have hmem : x - ∑ i, c i • S i ∈ J := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, ← hcb, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc i, ← hS i, Algebra.smul_def, Algebra.smul_def, map_mul, hmk]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨c, y, ?_⟩
    rw [Algebra.smul_def, ← hw, mul_comm, hy]
    abel
  have hsep : ∀ x : T, (∀ k : ℕ, ∃ y : T, x = ϖ ^ k • y) → x = 0 := by
    intro x hx
    have h0 := Ideal.iInf_pow_eq_bot_of_isDomain J hJtop
    have : x ∈ ⨅ k : ℕ, J ^ k := by
      rw [Ideal.mem_iInf]
      intro k
      obtain ⟨y, rfl⟩ := hx k
      rw [hJ, Ideal.span_singleton_pow, Algebra.smul_def, map_pow, ← hw]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h0] at this
    exact (Submodule.mem_bot T).1 this
  have : IsAdicComplete (Ideal.span {ϖ}) O := hϖ.maximalIdeal_eq ▸ inferInstance
  have htop := SpanTopOfComplete.span_eq_top_of_complete ϖ hsep S hgen
  exact ⟨Submodule.fg_def.2 ⟨Set.range S, Set.finite_range S, htop⟩⟩

end ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule

theorem gtE_bound (m lam A Bt N : ℝ) (hm : 0 ≤ m) (hlam : 0 < lam) (hA0 : 0 ≤ A)
    (hA : A ≤ m ^ 2 / lam) (hB0 : 0 ≤ Bt) (hBt : Bt ≤ 1 / 2) (hN0 : 0 ≤ N)
    (hN : N ≤ (m + 1) / lam) : A ^ 2 + (Bt * N) ^ 2 ≤ ((m + 1) ^ 2 / lam) ^ 2 := by
  have hA' : A * lam ≤ m ^ 2 := by rwa [le_div_iff₀ hlam] at hA
  have hN' : N * lam ≤ m + 1 := by rwa [le_div_iff₀ hlam] at hN
  have h1 : (A * lam) ^ 2 ≤ (m ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hA' 2
  have hBN : Bt * (N * lam) ≤ 1 / 2 * (m + 1) :=
    mul_le_mul hBt hN' (by positivity) (by norm_num)
  have h2 : (Bt * (N * lam)) ^ 2 ≤ (1 / 2 * (m + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hBN 2
  have h3 : (m ^ 2) ^ 2 + (1 / 2 * (m + 1)) ^ 2 ≤ ((m + 1) ^ 2) ^ 2 := by
    nlinarith [pow_nonneg hm 3, sq_nonneg m, hm]
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (A ^ 2 + (Bt * N) ^ 2) * lam ^ 2 = (A * lam) ^ 2 + (Bt * (N * lam)) ^ 2 := by ring
    _ ≤ ((m + 1) ^ 2) ^ 2 := by linarith

private theorem exists_int_inner_of_mem_span_int' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (b : Fin k → E) (y : E) (h : ∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) (v : E)
    (hv : v ∈ span ℤ (Set.range b)) : ∃ m : ℤ, inner ℝ y v = m := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  choose f hf using h
  refine ⟨∑ j, c j * f j, ?_⟩
  rw [inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hf j]

theorem gtE_main (n : ℕ) : ∀ (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : ℝ), 0 < lam →
    (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) →
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam := by
  induction n with
  | zero =>
    intro b lam hlam hmin
    exact ⟨fun i ↦ Fin.elim0 i, linearIndependent_empty_type, fun i ↦ Fin.elim0 i,
      fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
    intro b lam hlam hmin
    classical
    obtain ⟨y1, hy1, hint1, hy1n⟩ := gtB_dual_short (Nat.succ_pos m) b lam hlam hmin
    obtain ⟨y0, xu, hxu, hy0, hint0, hy0n, h01⟩ := gtC_prim b y1 hy1 hint1
    obtain ⟨bW, hWL, hproj⟩ := gtD_lat b y0 xu hy0 hxu h01 hint0
    have hfin : Module.finrank ℝ (ℝ ∙ y0)ᗮ = m := by
      rw [Module.finrank_eq_card_basis bW, Fintype.card_fin]
    set φ : (ℝ ∙ y0)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
      ((stdOrthonormalBasis ℝ (ℝ ∙ y0)ᗮ).reindex (finCongr hfin)).repr with hφ
    set bE : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) := bW.map φ.toLinearEquiv with hbEdef
    have hbE : ∀ j, bE j = φ (bW j) := fun j ↦ rfl
    have hspanφ : ∀ p : (ℝ ∙ y0)ᗮ, p ∈ span ℤ (Set.range bW) → φ p ∈ span ℤ (Set.range bE) := by
      intro p hp
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_zsmul, hbE]
    have hspanφ' : ∀ x, x ∈ span ℤ (Set.range bE) → φ.symm x ∈ span ℤ (Set.range bW) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_zsmul, hbE, LinearIsometryEquiv.symm_apply_apply]
    have hminE : ∀ x ∈ span ℤ (Set.range bE), x ≠ 0 → lam ≤ ‖x‖ := by
      intro x hx hx0
      have h1 := hmin _ (hWL _ (hspanφ' x hx)) (by
        intro h
        apply hx0
        have h2 : φ.symm x = 0 := Subtype.ext h
        simpa using congrArg φ h2)
      exact h1.trans (le_of_eq (φ.symm.norm_map x))
    obtain ⟨z, hzli, hzint, hzn⟩ := ih bE lam hlam hminE
    set w : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ ((φ.symm (z i) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) with hw
    have hwy0 : ∀ i, inner ℝ y0 (w i) = 0 := fun i ↦
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (φ.symm (z i)).2
    have hwn : ∀ i, ‖w i‖ = ‖z i‖ := fun i ↦ φ.symm.norm_map (z i)
    have hwli : LinearIndependent ℝ w :=
      (hzli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker).map'
        (ℝ ∙ y0)ᗮ.subtype (Submodule.ker_subtype _)
    set u : Fin m → EuclideanSpace ℝ (Fin (m + 1)) :=
      fun i ↦ w i - (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) • y0 with hu
    refine ⟨Fin.cons y0 u, ?_, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hexp : ∑ i : Fin m, g i.succ • u i = ∑ i : Fin m, g i.succ • w i -
          (∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) • y0 := by
        simp only [hu, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
      rw [hexp] at hg
      have hin := congrArg (fun v ↦ inner ℝ y0 v) hg
      simp only [inner_add_right, inner_sub_right, inner_sum, real_inner_smul_right, hwy0,
        mul_zero, Finset.sum_const_zero, inner_zero_right, real_inner_self_eq_norm_sq] at hin
      have hy0sq : ‖y0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy0)
      have hg0 : g 0 = ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu)) := by
        have h3 : (g 0 - ∑ i : Fin m, g i.succ * (inner ℝ (w i) xu - round (inner ℝ (w i) xu))) *
            ‖y0‖ ^ 2 = 0 := by linear_combination hin
        rcases mul_eq_zero.mp h3 with h | h
        · linarith
        · exact absurd h hy0sq
      have hX : ∑ i : Fin m, g i.succ • w i = 0 := by
        have h4 := hg
        rw [hg0] at h4
        simpa using h4
      have hsucc : ∀ i : Fin m, g i.succ = 0 := Fintype.linearIndependent_iff.mp hwli _ hX
      intro i
      cases i using Fin.cases with
      | zero => rw [hg0]; simp [hsucc]
      | succ k => exact hsucc k
    · intro i j
      cases i using Fin.cases with
      | zero => simpa using hint0 j
      | succ k =>
        simp only [Fin.cons_succ]
        obtain ⟨p, hp, hpeq⟩ := hproj (b j) (Submodule.subset_span ⟨j, rfl⟩)
        obtain ⟨k0, hk0⟩ := hint0 j
        obtain ⟨mp, hmp⟩ := exists_int_inner_of_mem_span_int' bE (z k) (hzint k) (φ p) (hspanφ p hp)
        refine ⟨mp + k0 * round (inner ℝ (w k) xu), ?_⟩
        have hb : b j = (p : EuclideanSpace ℝ (Fin (m + 1))) + inner ℝ y0 (b j) • xu := by
          rw [hpeq]; abel
        have hwp : inner ℝ (w k) (p : EuclideanSpace ℝ (Fin (m + 1))) = inner ℝ (z k) (φ p) := by
          show inner ℝ ((φ.symm (z k) : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1)))
            (p : EuclideanSpace ℝ (Fin (m + 1))) = _
          rw [← Submodule.coe_inner, ← φ.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
        have h1 : inner ℝ (w k) (b j) = mp + k0 * inner ℝ (w k) xu := by
          conv_lhs => rw [hb]
          rw [inner_add_right, real_inner_smul_right, hk0, hwp, hmp]
        have h2 : inner ℝ (u k) (b j) = inner ℝ (w k) (b j) -
            (inner ℝ (w k) xu - round (inner ℝ (w k) xu)) * inner ℝ y0 (b j) := by
          simp only [hu, inner_sub_left, real_inner_smul_left]
        rw [h2, h1, hk0]
        push_cast
        ring
    · intro i
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        calc ‖y0‖ ≤ ‖y1‖ := hy0n
          _ ≤ ((m + 1 : ℕ) : ℝ) / lam := hy1n
          _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / lam := by gcongr; exact le_self_pow₀ h1 two_ne_zero
      | succ k =>
        simp only [Fin.cons_succ]
        have hc' : |inner ℝ (w k) xu - round (inner ℝ (w k) xu)| ≤ 1 / 2 := abs_sub_round _
        have hwy0' : inner ℝ (w k) y0 = 0 := by rw [real_inner_comm]; exact hwy0 k
        have hsq : ‖u k‖ ^ 2 = ‖w k‖ ^ 2 +
            (|inner ℝ (w k) xu - round (inner ℝ (w k) xu)| * ‖y0‖) ^ 2 := by
          simp only [hu]
          rw [norm_sub_sq_real, real_inner_smul_right, hwy0', norm_smul, Real.norm_eq_abs]
          ring
        have hA : ‖w k‖ ≤ (m : ℝ) ^ 2 / lam := by rw [hwn]; exact hzn k
        have hN : ‖y0‖ ≤ ((m : ℝ) + 1) / lam := by
          have := hy0n.trans hy1n
          simpa using this
        have hbd := gtE_bound m lam ‖w k‖ _ ‖y0‖ (Nat.cast_nonneg m) hlam (norm_nonneg _) hA
          (abs_nonneg _) hc' (norm_nonneg _) hN
        rw [← hsq] at hbd
        have h5 : ‖u k‖ ≤ ((m : ℝ) + 1) ^ 2 / lam :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hbd
        simpa using h5

theorem transference_dual {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : Fin n → EuclideanSpace ℝ (Fin n), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (b j) = m) ∧ ∀ i, ‖y i‖ ≤ (n : ℝ) ^ 2 / lam :=
  gtE_main n b lam hlam hmin

end ReciprocityTheory.ChartRestriction.G.T0
end

