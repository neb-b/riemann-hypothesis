module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfInjectiveModMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EqCOfPderivZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {σ τ : Type}

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv (R := k) t (subst a f) = ∑ s, subst a (pderiv (R := k) s f) * pderiv (R := k) t (a s) :=
  GlobalTheory.FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero ha) f t

theorem pderiv_comm (u v : τ) (g : MvPowerSeries τ k) : pderiv (R := k) u (pderiv (R := k) v g) = pderiv (R := k) v (pderiv (R := k) u g) := by
  classical
  ext n
  simp only [coeff_pderiv]
  by_cases h : u = v
  · subst h; rfl
  · rw [show n + Finsupp.single u 1 + Finsupp.single v 1 = n + Finsupp.single v 1 + Finsupp.single u 1 by abel]
    simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), add_zero]
    ring

theorem eq_C_of_pderiv_zero [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv (R := k) v g = 0) :
    g = C (constantCoeff g) := by
  classical
  ext n
  rw [coeff_C]
  split_ifs with hn
  · subst hn; rfl
  · obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    have hle : Finsupp.single v 1 ≤ n := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hv)
    have h1 := congrArg (coeff (n - Finsupp.single v 1)) (h v)
    rw [coeff_pderiv, map_zero, tsub_add_cancel_of_le hle] at h1
    have hc' : (n - Finsupp.single v 1 : τ →₀ ℕ) v + 1 = n v := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
    have hc : (((n - Finsupp.single v 1 : τ →₀ ℕ) v : ℕ) : k) + 1 = ((n v : ℕ) : k) := by
      rw [← hc']; push_cast; ring
    rw [hc] at h1
    have hu : IsUnit ((n v : ℕ) : k) := by
      have : ((n v : ℕ) : k) = algebraMap ℚ k (n v : ℚ) := by simp
      rw [this]; exact (IsUnit.mk0 _ (by exact_mod_cast hv)).map _
    rcases hu with ⟨w, hw⟩
    rw [← hw] at h1
    simpa using congrArg (· * ((w⁻¹ : kˣ) : k)) h1

end GlobalTheory.FormalLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeriesOfIsNoetherianRing
section
open IsLocalRing TensorProduct

namespace GlobalTheory.FiniteHeight

theorem flat_mvPowerSeries_of_isNoetherianRing :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries

end GlobalTheory.FiniteHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatQuotientWeaklyRegular
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem mkQ_mem_smul_top_iff_mem_sup {A : Type} [CommRing A] (J I : Ideal A) (a : A) :
    Submodule.mkQ J a ∈ (I • ⊤ : Submodule A (A ⧸ J)) ↔ a ∈ J ⊔ I := by
  rw [← Submodule.range_mkQ J, LinearMap.range_eq_map, ← Submodule.map_smul'',
    ← Submodule.mem_comap, Submodule.comap_map_mkQ, smul_eq_mul, Ideal.mul_top]

theorem flat_quotient_sup_span_singleton (V A : Type) [CommRing V] [IsNoetherianRing V]
    [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A]
    [IsLocalHom (algebraMap V A)] (J : Ideal A) [Module.Flat V (A ⧸ J)] (r : A)
    (hr : ∀ a : A, r * a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A) →
      a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A)) :
    Module.Flat V (A ⧸ (J ⊔ Ideal.span {r})) := by
  let u : (A ⧸ J) →ₗ[A] (A ⧸ J) := LinearMap.lsmul A (A ⧸ J) r
  have h := flat_coker_of_injective_mod_maximalIdeal V A (A ⧸ J) (A ⧸ J) u (by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J x
    rw [mkQ_mem_smul_top_iff_mem_sup]
    apply hr
    rw [← mkQ_mem_smul_top_iff_mem_sup]
    exact hx)
  have hu : LinearMap.range u = Submodule.map (Submodule.mkQ J) (Ideal.span {r}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J y
      exact ⟨r * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hb
      exact ⟨Submodule.mkQ J a, rfl⟩
  let e : ((A ⧸ J) ⧸ LinearMap.range u) ≃ₗ[A] (A ⧸ (J ⊔ Ideal.span {r})) :=
    (Submodule.quotEquivOfEq _ _ hu).trans
      (Submodule.quotientQuotientEquivQuotientSup J (Ideal.span {r}))
  exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm

theorem mem_sup_of_isSMulRegular_quotient_quotient {A : Type} [CommRing A] (I J : Ideal A) (r : A)
    (h : IsSMulRegular ((A ⧸ I) ⧸ (J • ⊤ : Submodule A (A ⧸ I))) r) (a : A)
    (ha : r * a ∈ J ⊔ I) : a ∈ J ⊔ I := by
  rw [sup_comm, ← mkQ_mem_smul_top_iff_mem_sup, ← Submodule.Quotient.mk_eq_zero] at ha ⊢
  apply h
  simp only [smul_zero]
  exact ha

theorem flat_quotient_ofList_of_isWeaklyRegular_closedFibre : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  intro V A _ _ _ _ _ _ _ _ _ rs _ hreg
  have key : ∀ i, i ≤ rs.length → Module.Flat V (A ⧸ Ideal.ofList (rs.take i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [List.take_zero, Ideal.ofList_nil]
      exact Module.Flat.of_linearEquiv
        ((Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl).restrictScalars V)
    | succ i ih =>
      intro hi
      have hi' : i < rs.length := hi
      haveI := ih hi'.le
      rw [List.take_succ_eq_append_getElem hi', Ideal.ofList_append, Ideal.ofList_singleton]
      exact flat_quotient_sup_span_singleton V A _ _
        (mem_sup_of_isSMulRegular_quotient_quotient _ _ _ (hreg.regular_mod_prev i hi'))
  have h := key rs.length le_rfl
  rwa [List.take_length] at h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JacobianSmulKaehlerEqZero
section
namespace GlobalTheory.FiniteQuotOmega

open MvPowerSeries IsLocalRing
open scoped TensorProduct

section General

variable {T Q σ : Type*} [CommRing T] [CommRing Q] [Algebra T Q] [Fintype σ]

theorem derivation_apply_eq_sum [IsNoetherianRing Q] {M : Type*} [AddCommGroup M] [Module T M]
    [Module Q M] [Module.Finite Q M] (φ : MvPowerSeries σ T →ₐ[T] Q)
    (hφ : Function.Surjective φ) (D : Derivation T Q M) (g : MvPowerSeries σ T) :
    D (φ g) = ∑ j, φ (pderiv (R := T) j g) • D (φ (X j)) := by
  classical
  set J : Ideal Q := Ideal.jacobson ⊥ with hJ
  have hX : ∀ i, φ (X i) ∈ J := by
    intro i
    rw [hJ, Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨h, rfl⟩ := hφ y
    have : IsUnit (X i * h + 1 : MvPowerSeries σ T) := by
      rw [isUnit_iff_constantCoeff]; simp
    simpa using this.map φ
  have key : ∀ (n : ℕ) (g : MvPowerSeries σ T),
      D (φ g) - ∑ j, φ (pderiv (R := T) j g) • D (φ (X j)) ∈ (J ^ n • ⊤ : Submodule Q M) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      obtain ⟨k, -, hk⟩ := exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g))
        fun d hd => by
          have : d = 0 := by
            rw [← Finsupp.degree_eq_zero_iff]; omega
          subst this
          simp
      have hg : g = C (constantCoeff g) + ∑ i, X i * k i := by rw [← hk]; ring
      have hC : ∀ c : T, D (φ (C c)) = 0 := fun c => by
        have : φ (C c) = algebraMap T Q c := φ.commutes c
        rw [this, Derivation.map_algebraMap]
      have h1 : ∀ i, ∑ j, φ (pderiv (R := T) j (X i * k i)) • D (φ (X j)) =
          φ (X i) • ∑ j, φ (pderiv (R := T) j (k i)) • D (φ (X j)) + φ (k i) • D (φ (X i)) := by
        intro i
        simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, add_smul,
          Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [pderiv_X_of_ne hj.symm]
        · simp
      have e : D (φ g) - ∑ j, φ (pderiv (R := T) j g) • D (φ (X j)) =
          ∑ i, φ (X i) • (D (φ (k i)) - ∑ j, φ (pderiv (R := T) j (k i)) • D (φ (X j))) := by
        generalize constantCoeff g = c at hg
        subst hg
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_add (f := _), hC, zero_add, pderiv_C, map_sum, Finset.sum_smul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h1, map_mul, Derivation.leibniz, smul_sub]
        abel
      rw [e, pow_succ', mul_smul]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hX i) (ih _)
  rw [← sub_eq_zero, ← Submodule.mem_bot Q,
    ← Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) J (by rw [hJ, Ideal.jacobson_bot]), Submodule.mem_iInf]
  exact fun n => key n g

theorem det_smul_kaehler_eq_zero [DecidableEq σ] [IsNoetherianRing T] [Module.Finite T Q]
    (φ : MvPowerSeries σ T →ₐ[T] Q) (hφ : Function.Surjective φ) (f : σ → MvPowerSeries σ T)
    (hf : ∀ i, φ (f i) = 0) (ω : KaehlerDifferential T Q) :
    φ (Matrix.det (Matrix.of fun i j => pderiv (R := T) j (f i))) • ω = 0 := by
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite T Q
  set D := KaehlerDifferential.D T Q with hD
  set A : Matrix σ σ Q := Matrix.of fun i j => φ (pderiv (R := T) j (f i)) with hA
  have hdet : φ (Matrix.det (Matrix.of fun i j => pderiv (R := T) j (f i))) = A.det := by
    rw [AlgHom.map_det]; rfl
  have hrel : ∀ i, ∑ j, A i j • D (φ (X j)) = 0 := fun i => by
    have := derivation_apply_eq_sum φ hφ D (f i)
    rw [hf, map_zero] at this
    exact this.symm
  have hx : ∀ l, A.det • D (φ (X l)) = 0 := fun l => by
    have h : ∑ j, (A.adjugate * A) l j • D (φ (X j)) = 0 := by
      simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hrel, smul_zero, Finset.sum_const_zero]
    rw [Matrix.adjugate_mul] at h
    simpa [Matrix.one_apply] using h
  rw [hdet]
  have hω : ω ∈ Submodule.span Q (Set.range D) := by
    rw [hD, KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x h =>
    obtain ⟨y, rfl⟩ := h
    obtain ⟨g, rfl⟩ := hφ y
    rw [derivation_apply_eq_sum φ hφ D g, Finset.smul_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [smul_comm, hx, smul_zero]
  | zero => simp
  | add x y _ _ h1 h2 => rw [smul_add, h1, h2, add_zero]
  | smul a x _ h => rw [smul_comm, h, smul_zero]

end General

theorem jacobian_smul_kaehler_eq_zero :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (σ : Type) [Fintype σ] [DecidableEq σ] (f : σ → MvPowerSeries σ T), Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → ∀ ω : KaehlerDifferential T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)), (Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => pderiv (R := T) j (f i)))) • ω = 0 := by
  intro T _ _ _ σ _ _ f hfin ω
  exact det_smul_kaehler_eq_zero (Ideal.Quotient.mkₐ T (Ideal.span (Set.range f)))
    Ideal.Quotient.mk_surjective f
    (fun i => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)) ω

end GlobalTheory.FiniteQuotOmega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
section
open IsLocalRing TensorProduct

namespace GlobalTheory.CompleteBaseChange

open MvPowerSeries

theorem monomial_one_mem_span_X_pow {R σ : Type*} [CommRing R] (α : σ →₀ ℕ) :
    (monomial α (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ α.degree := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : (monomial (a + b) (1 : R) : MvPowerSeries σ R) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_add (f := _), pow_add]
    exact Ideal.mul_mem_mul ha hb
  | single s n =>
    rw [← X_pow_eq, Finsupp.degree_single]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self s)) n

theorem exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by
  intro O _ J hJ hO σ τ _ _ f N hM g
  have := Fintype.ofFinite τ
  have hN : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : O) : MvPowerSeries σ O) ∈
      Ideal.span (Set.range f) ⊔ J.map (C : O →+* MvPowerSeries σ O) := fun α hα =>
    hM (hα ▸ monomial_one_mem_span_X_pow α)
  have : IsPrecomplete J (MvPowerSeries σ O) := isPrecomplete_pi (σ →₀ ℕ) hJ
  have : IsHausdorff J (MvPowerSeries σ O) := isHausdorff_pi (σ →₀ ℕ) hJ
  have : IsPrecomplete J (Option τ → MvPowerSeries σ O) := isPrecomplete_pi _ hJ
  let Φ : (Option τ → MvPowerSeries σ O) →ₗ[O] MvPowerSeries σ O :=
    { toFun := fun x => (truncTotal N (x none) : MvPolynomial σ O) + ∑ j, x (some j) * f j
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), MvPolynomial.coe_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, map_smul, MvPolynomial.coe_smul, smul_add, Finset.smul_sum,
          smul_mul_assoc, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mkQ_comp_surjective (I := J) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    have h1 := mem_of_coeff_eq_zero N _ hN (G - (truncTotal N G : MvPolynomial σ O)) fun d hd => by
      rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
    refine ⟨fun o => o.elim G c, ((Submodule.Quotient.eq _).2 ?_).symm⟩
    have h2 : G - Φ (fun o => o.elim G c) = b := by
      change G - (((truncTotal N G : MvPolynomial σ O) : MvPowerSeries σ O) + ∑ j, c j * f j) = b
      linear_combination -hab
    rw [h2, Ideal.smul_top_eq_map]
    exact hb
  obtain ⟨x, hx⟩ := hΦ g
  refine ⟨truncTotal N (x none), ?_,
    Ideal.mem_span_range_iff_exists_fun.2 ⟨fun j => x (some j), ?_⟩⟩
  · refine Finset.sup_le fun d hd => ?_
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hd (coeff_truncTotal_eq_zero _ ?_)
    exact (not_le.1 hlt).le
  · rw [← hx]
    exact (add_sub_cancel_left _ _).symm

end GlobalTheory.CompleteBaseChange
end

