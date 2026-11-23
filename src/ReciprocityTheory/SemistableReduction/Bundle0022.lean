module

public import ReciprocityTheory.SemistableReduction.Bundle0017
public import ReciprocityTheory.SemistableReduction.Bundle0018
public import ReciprocityTheory.SemistableReduction.Bundle0019
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.SemistableReduction.Bundle0021

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.ApproxGraph
section
namespace ReciprocityTheory.MultiplicativeHeights

open ApproximationGraph in
theorem approxGraph_holds : ApproxGraphStatement := by
  intro r p μ ρ X _ hμ hρ hρ1 hX
  exact ⟨fun w hw => approxGraph_one X hμ hρ hρ1 hX w hw,
    fun y hy hy0 => approxGraph_two X hμ hρ hρ1 hX y hy hy0,
    fun v y hy hvy => approxGraph_three X hμ hρ hρ1 hX v y hy hvy⟩

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.HeightLowerBound
section
namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial NumberField

theorem heightLowerBound_of_sj_of_sphereLogIntegrable (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) :
    HeightLowerBoundStatement := by
  intro K _ _ B n a f hn hf hmh
  classical
  obtain ⟨s, hs⟩ : ∃ s, s ∈ f.support :=
    Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have h1 := neg_log_norm_coeff_le_finitePlaces f s hs
  have h2 : ∀ σ : K →+* ℂ, Real.log ‖σ (f.coeff s)‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤
      blockSphereMean B n (MvPolynomial.map σ f) := by
    intro σ
    have hmap : IsMultiHomogeneous a (MvPolynomial.map σ f) := by
      intro t ht b
      rw [MvPolynomial.support_map_of_injective _ σ.injective] at ht
      exact hmh t ht b
    exact log_norm_coeff_sub_le_blockSphereLogMean hSJ hInt hn hmap s
      (by rw [MvPolynomial.coeff_map]; exact (map_ne_zero σ).mpr hc)
  have h3 := Finset.sum_le_sum fun (σ : K →+* ℂ) (_ : σ ∈ Finset.univ) ↦ h2 σ
  rw [Finset.sum_sub_distrib, sum_log_norm_embedding_eq _ hc, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul] at h3
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold h0
  rw [le_div_iff₀ hd]
  linarith

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.SJCore
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Set Real

theorem gaussLogC_div {a : ℝ} (ha : 0 < a) :
    gaussLogC a / gaussOneC = log a + radK 1 / radJ 1 := by
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h1 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => exp (-r ^ 2))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => log (a * r) * exp (-r ^ 2))
  rw [hdim] at h1 h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h1 h2
  set C : ℝ := (volume : Measure ℂ).real (Metric.ball 0 1) with hCdef
  have hC : 0 < C :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ℂ) one_pos).ne' measure_ball_lt_top.ne
  have hG : gaussOneC = 2 * C * radJ 1 := by
    unfold gaussOneC radJ
    rw [h1]
    simp only [pow_one]
    ring
  have hsplit : ∫ y in Ioi (0 : ℝ), y * (log (a * y) * exp (-y ^ 2)) =
      log a * radJ 1 + radK 1 := by
    have heq : EqOn (fun y : ℝ => y * (log (a * y) * exp (-y ^ 2)))
        (fun y : ℝ => log a * (y ^ 1 * exp (-y ^ 2)) + y ^ 1 * log y * exp (-y ^ 2)) (Ioi 0) := by
      intro y hy
      simp only
      rw [log_mul ha.ne' (ne_of_gt hy)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      integral_add ((integrableOn_radJ 1).const_mul (log a)) (integrableOn_radK le_rfl),
      integral_const_mul]
    rfl
  have hL : gaussLogC a = 2 * C * (log a * radJ 1 + radK 1) := by
    unfold gaussLogC
    rw [h2, hsplit]
    ring
  have hM := radJ_pos 1
  rw [hL, hG]
  field_simp

theorem sjCore_holds : SphereLinLogStatement := by
  intro n c hc
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim c 0) hc
    · exact h
  obtain ⟨hi, he⟩ := polar_mean hn c hc
  refine ⟨hi, ?_⟩
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [he, gaussLogC_div hcn, h2, radRatio_odd]
  ring

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegAB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_cases3 {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j : Fin n, i = (Fin.castSucc j).succ := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · exact Or.inl h
  · right
    induction j using Fin.lastCases with
    | last => left; simp
    | cast j => right; exact ⟨j, rfl⟩

def waExt {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) : Fin (n + 2) → α :=
  Fin.cons x (Fin.snoc f y : Fin (n + 1) → α)

@[simp] theorem waExt_zero {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f 0 = x := by
  simp [waExt]

@[simp] theorem waExt_last {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f (Fin.last (n + 1)) = y := by
  rw [waExt, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

@[simp] theorem waExt_mid {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) (j : Fin n) :
    waExt x y f (Fin.castSucc j).succ = f j := by
  rw [waExt, Fin.cons_succ, Fin.snoc_castSucc]

theorem wa_witt_apply {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i j : Fin r) :
    wittMat r m g i j = if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
      else if (i : ℕ) = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0 := by
  unfold wittMat
  simp only [Matrix.of_apply, Fin.val_inj]

theorem wa_main {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0) →
      ∃ (m : ℕ) (b : Fin n → Fin r → K) (g : Fin n → K), (∀ i, b i ∈ W) ∧ 2 * m ≤ n ∧
        (∀ i j, S.h (b i) (b j) = wittMat n m g i j) ∧
        ∀ t : Fin n → K, (∀ i : Fin n, (i : ℕ) < m ∨ n ≤ (i : ℕ) + m → t i = 0) →
          ∑ i, S.c (t i) * g i * t i = 0 → t = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW hnd
  by_cases hiso : ∃ x ∈ W, x ≠ 0 ∧ S.h x x = 0
  · obtain ⟨x, hxW, hx0, hxx⟩ := hiso
    obtain ⟨y, hyW, hxy, hyy⟩ := wa_hyp S W hnd x hxW hx0 hxx
    have hyx : S.h y x = 1 := by rw [wa_symm, hxy, map_one]
    have hf1 := wa_finrank_inf_ker W (waR S x) y hyW
      (by rw [waR_apply, hxy]; exact one_ne_zero)
    have hf2 := wa_finrank_inf_ker (W ⊓ LinearMap.ker (waR S x)) (waR S y) x
      (Submodule.mem_inf.mpr ⟨hxW, by rw [LinearMap.mem_ker, waR_apply, hxx]⟩)
      (by rw [waR_apply, hyx]; exact one_ne_zero)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 :=
      ⟨finrank K ↥(W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)), by omega⟩
    obtain ⟨m', b', g', hb'W, hm', hgram', hani'⟩ := ih n' (by omega)
      (W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)) (by omega)
      (wa_perp_nondeg S W hnd x y hxW hyW hxx hxy hyy)
    have hmem : ∀ j, b' j ∈ W ∧ S.h x (b' j) = 0 ∧ S.h y (b' j) = 0 := fun j => by
      have h := hb'W j
      rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, waR_apply,
        waR_apply] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have hbx : ∀ j, S.h (b' j) x = 0 := fun j => by rw [wa_symm, (hmem j).2.1, map_zero]
    have hby : ∀ j, S.h (b' j) y = 0 := fun j => by rw [wa_symm, (hmem j).2.2, map_zero]
    refine ⟨m' + 1, waExt x y b', waExt 0 0 g', fun i => ?_, by omega, fun i j => ?_,
      fun t ht hsum => ?_⟩
    · rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · simpa using hxW
      · simpa using hyW
      · simpa using (hmem j).1
    · rw [wa_witt_apply]
      rcases wa_cases3 i with rfl | rfl | ⟨i, rfl⟩ <;>
        rcases wa_cases3 j with rfl | rfl | ⟨j, rfl⟩ <;>
        simp only [waExt_zero, waExt_last, waExt_mid, Fin.val_zero, Fin.val_last, Fin.val_succ,
          Fin.val_castSucc] <;>
        try simp only [true_and]
      · rw [hxx, if_neg (by omega), if_neg (by omega)]
      · rw [hxy, if_pos (by omega)]
      · have := j.2
        rw [(hmem j).2.1, if_neg (by omega), if_neg (by omega)]
      · rw [hyx, if_pos (by omega)]
      · rw [hyy, if_neg (by omega), if_neg (by omega)]
      · have := j.2
        rw [(hmem j).2.2, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hbx, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hby, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        have := j.2
        rw [hgram', wa_witt_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
    · have ht0 : t 0 = 0 := ht 0 (Or.inl (by simp))
      have htl : t (Fin.last (n' + 1)) = 0 := ht _ (Or.inr (by simp only [Fin.val_last]; omega))
      have ht' : (fun j : Fin n' => t (Fin.castSucc j).succ) = 0 := by
        refine hani' _ (fun j hj => ht _ ?_) ?_
        · simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        · rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
          simpa [ht0, htl, Fin.succ_last] using hsum
      funext i
      rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · exact ht0
      · exact htl
      · exact congrFun ht' j
  · have han : ∀ x ∈ W, S.h x x = 0 → x = 0 := fun x hx hxx => by
      by_contra h0
      exact hiso ⟨x, hx, h0, hxx⟩
    obtain ⟨b, hbW, hb0, hbo⟩ := wa_diag S n W hW han
    have hg : ∀ k, S.h (b k) (b k) ≠ 0 := fun k h => hb0 k (han _ (hbW k) h)
    refine ⟨0, b, fun k => S.h (b k) (b k), hbW, by omega, fun i j => ?_, fun t _ hsum => ?_⟩
    · rw [wa_witt_apply]
      have := i.2
      by_cases hij : i = j
      · subst hij
        rw [if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩]
      · rw [hbo i j hij, if_neg (by omega), if_neg (fun h => hij (Fin.ext h.1))]
    · have hz : ∀ k, S.h (b k) (∑ i, t i • b i) = t k * S.h (b k) (b k) := fun k => by
        rw [wa_sum_right, Finset.sum_eq_single k
          (fun i _ hik => by rw [hbo k i (Ne.symm hik), mul_zero]) (by simp)]
      have hzz : S.h (∑ i, t i • b i) (∑ i, t i • b i) = 0 := by
        rw [wa_sum_left]
        simp only [hz]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
        beta_reduce
        ring
      have hz0 := han _ (W.sum_mem fun i _ => W.smul_mem _ (hbW i)) hzz
      funext k
      have h := hz k
      rw [hz0, wa_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hg k)

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegBB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField

theorem relIndex_span_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (M : Matrix (Fin k) (Fin k) (𝓞 K))
    (hM : M.det ≠ 0) :
    (((Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i))).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ M.det| := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hPdef
  set Q := Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i)) with hQdef
  have hbO : LinearIndependent (𝓞 K) b := hb.restrict_scalars' (𝓞 K)
  let bP : Module.Basis (Fin k) (𝓞 K) P := Module.Basis.span hbO
  let f : P →ₗ[𝓞 K] P := Matrix.toLin bP bP M
  have hfb : ∀ j, ((f (bP j) : P) : Fin r → K) = ∑ i, M i j • b i := by
    intro j
    simp only [f, Matrix.toLin_self, bP, Submodule.coe_sum, Submodule.coe_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [Module.Basis.span_apply]
  have hQ : Submodule.map P.subtype (LinearMap.range f) = Q := by
    rw [LinearMap.range_eq_map, ← bP.span_eq, Submodule.map_span, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp, hQdef]
    congr 2
    funext j
    exact hfb j
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := LinearMap.toMatrix_mulVec_repr bP bP f x
    rw [hx, map_zero, LinearMap.toMatrix_toLin] at h1
    have h2 : ⇑(bP.repr x) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using h1)
    have h3 : bP.repr x = 0 := DFunLike.coe_injective h2
    simpa using h3
  have hR : Q.toAddSubgroup.addSubgroupOf P.toAddSubgroup = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, ← hQ,
      Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have : Module.Free (𝓞 K) P := Module.Free.of_basis bP
  have : Module.Finite (𝓞 K) P := Module.Finite.of_basis bP
  have : Module.Free ℤ P := Module.Free.of_basis ((RingOfIntegers.basis K).smulTower bP)
  have : Module.Finite ℤ P := Module.Finite.of_basis ((RingOfIntegers.basis K).smulTower bP)
  set N : Submodule ℤ P := (LinearMap.range f).toAddSubgroup.toIntSubmodule with hN
  let e : P ≃+ N := (LinearEquiv.ofInjective f hf).toAddEquiv
  have hdet : N.subtype ∘ₗ e.toAddMonoidHom.toIntLinearMap = f.restrictScalars ℤ := by
    ext x
    rfl
  have key : (LinearMap.det (N.subtype ∘ₗ e.toAddMonoidHom.toIntLinearMap)).natAbs =
      Nat.card (P ⧸ N) := Submodule.natAbs_det_equiv N e
  rw [hdet, LinearMap.det_restrictScalars, LinearMap.det_toLin] at key
  rw [AddSubgroup.relIndex, hR]
  change ((Nat.card (P ⧸ N) : ℕ) : ℤ) = _
  rw [← key, Int.natCast_natAbs]

theorem comb_diagonal {K : Type} [Field K] [NumberField K] {r k : ℕ} (v : Fin k → Fin r → K)
    (D : 𝓞 K) : (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • v i) = fun j => D • v j := by
  funext j
  simp [Matrix.diagonal_apply, ite_smul]

theorem exists_smul_mem_span {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (x : Fin r → K) (hx : x ∈ Submodule.span K (Set.range b)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  obtain ⟨⟨d, hd⟩, hdc⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ c
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨e, he⟩ := hdc i (Finset.mem_univ i)
  have h1 : d • (c i • b i) = e • b i := by
    rw [← smul_assoc, ← algebraMap_smul K e (b i), he]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_smul_le_span {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (B : Submodule (𝓞 K) (Fin r → K)) (hB : B.FG)
    (hBb : ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)) :
    ∃ D : 𝓞 K, D ≠ 0 ∧ ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨s, hs⟩ := hB
  have hgen : ∀ g ∈ s, ∃ d : 𝓞 K, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 K) (Set.range b) :=
    fun g hg => exists_smul_mem_span b g (hBb g (by rw [← hs]; exact Submodule.subset_span hg))
  choose! d hd0 hdm using hgen
  refine ⟨∏ g ∈ s, d g, Finset.prod_ne_zero_iff.2 hd0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem d hg
    rw [ht, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hdm g hg)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem relIndex_span_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (B : Submodule (𝓞 K) (Fin r → K))
    (hbB : ∀ i, b i ∈ B) (D : 𝓞 K) (hD : D ≠ 0)
    (hDB : ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) := D • LinearMap.id
  have hD' : algebraMap (𝓞 K) K D ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 K) K)]
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hD
  have hφ : Function.Injective φ := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [φ, Algebra.smul_def] at this
    exact mul_left_cancel₀ hD' this
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hmapP : Submodule.map φ P = Submodule.span (𝓞 K)
      (Set.range (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • b i)) := by
    rw [comb_diagonal, hP, Submodule.map_span, ← Set.range_comp]
    rfl
  have h1 : (Submodule.map φ P).toAddSubgroup ≤ (Submodule.map φ B).toAddSubgroup :=
    Submodule.map_mono hPB
  have h2 : (Submodule.map φ B).toAddSubgroup ≤ P.toAddSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDB x hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have hdet : (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 := by
    simp [Matrix.det_diagonal, hD]
  have hidx := relIndex_span_comb b hb (Matrix.diagonal fun _ => D) hdet
  rw [← hmapP] at hidx
  have hne : (Submodule.map φ P).toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0] at hidx
    have hn : Algebra.norm ℤ (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr hdet
    simp only [Nat.cast_zero] at hidx
    exact hn (abs_eq_zero.mp hidx.symm)
  have heq : (Submodule.map φ P).toAddSubgroup.relIndex (Submodule.map φ B).toAddSubgroup =
      P.toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hφ
  rw [← heq]
  intro h0
  rw [h0, zero_mul] at hmul
  exact hne hmul.symm

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.TorusMean
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

theorem torusMean_holds : TorusMeanBasicStatement ∧ TorusCoeffStatement := by
  classical
  refine ⟨fun ι _ => ⟨fun f _ => tm_int f, fun f g hf hg => ?_, fun s c => ?_⟩,
    fun ι _ f i k hk hext => ?_⟩
  · show ∫ θ, tmLog (f * g) θ ∂(torusProb ι) =
      ∫ θ, tmLog f θ ∂(torusProb ι) + ∫ θ, tmLog g θ ∂(torusProb ι)
    rw [← integral_add (tm_int f) (tm_int g)]
    apply integral_congr_ae
    filter_upwards [tm_ae_ne f hf, tm_ae_ne g hg] with θ h1 h2
    simp only [tmLog, map_mul, norm_mul]
    exact Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)
  · have hm : ∀ θ, tmLog (MvPolynomial.monomial s c) θ = Real.log ‖c‖ := by
      intro θ
      simp [tmLog, MvPolynomial.eval_monomial, Finsupp.prod, norm_prod, norm_pow,
        norm_torusPoint]
    show ∫ θ, tmLog (MvPolynomial.monomial s c) θ ∂(torusProb ι) = Real.log ‖c‖
    simp_rw [hm]
    simp
  · show ∫ θ, tmLog (coeffIn i k f) θ ∂(torusProb ι) ≤ ∫ θ, tmLog f θ ∂(torusProb ι)
    have hFi : Integrable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      (tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable).mpr (tm_int f)
    rw [tm_integral_comp i (measurable_tmLog f).aestronglyMeasurable,
      integral_prod (fun p => tmLog f (tmUpd i p)) hFi]
    refine integral_mono_ae (tm_int _) hFi.integral_prod_left ?_
    filter_upwards [tm_ae_ne _ hk] with θ hθ
    show tmLog (coeffIn i k f) θ ≤ ∫ t, tmLog f (update θ i t) ∂unitIntervalMeasure
    simp_rw [tmLog_update]
    rw [integral_log_circ]
    have hc : (tmSlice i (torusPoint θ) f).coeff k = MvPolynomial.eval (torusPoint θ) (coeffIn i k f) :=
      tmSlice_coeff i _ f k
    have hk' : (tmSlice i (torusPoint θ) f).coeff k ≠ 0 := hc ▸ hθ
    show Real.log ‖MvPolynomial.eval (torusPoint θ) (coeffIn i k f)‖ ≤ _
    rw [← hc]
    rcases hext with htop | hbot
    · exact log_norm_coeff_top_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, htop k' hk'', map_zero]
    · exact log_norm_coeff_bot_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, hbot k' hk'', map_zero]

end ReciprocityTheory.MultiplicativeHeights
end
end

