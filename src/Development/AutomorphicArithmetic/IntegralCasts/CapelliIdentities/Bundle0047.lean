module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NoetherNormalizationChart
section
universe u

namespace UpperTheory.NoetherNormalizationChart

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

private noncomputable def shear (b : ℕ) (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval (Fin.cases (X 0) (fun i : Fin n => X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ))))

private lemma shear_zero (b : ℕ) (c : A) : shear (n := n) b c (X 0) = X 0 := by
  simp [shear]

private lemma shear_succ (b : ℕ) (c : A) (i : Fin n) :
    shear (n := n) b c (X i.succ) = X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ)) := by
  simp [shear]

private lemma shear_comp (b : ℕ) (c d : A) (h : c + d = 0) :
    (shear (n := n) b c).comp (shear b d) = AlgHom.id _ _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  cases i using Fin.cases with
  | zero => simp [shear_zero]
  | succ i =>
    rw [AlgHom.comp_apply, shear_succ, map_add (f := _), map_mul, map_pow, shear_zero, shear_succ,
      algHom_C, algebraMap_eq, add_assoc, ← add_mul, ← C_add, h]
    simp

private noncomputable def chart (A : Type u) [CommRing A] (n b : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A) :=
  (AlgEquiv.ofAlgHom (shear b 1) (shear b (-1)) (shear_comp b 1 (-1) (by simp))
    (shear_comp b (-1) 1 (by simp))).trans (finSuccEquiv A n)

private lemma chart_X [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (i : Fin (n + 1)) :
    (chart A n b (X i)).IsMonicOfDegree (b ^ (i : ℕ)) := by
  cases i using Fin.cases with
  | zero =>
    have : chart A n b (X 0) = Polynomial.X := by
      simp [chart, shear_zero, finSuccEquiv_X_zero]
    rw [this]
    exact ⟨by simp, Polynomial.monic_X⟩
  | succ i =>
    have : chart A n b (X i.succ)
        = Polynomial.X ^ (b ^ (i.succ : ℕ)) + Polynomial.C (X i) := by
      simp [chart, shear_succ, finSuccEquiv_X_zero, finSuccEquiv_X_succ, add_comm]
    rw [this]
    exact ⟨Polynomial.natDegree_X_pow_add_C, Polynomial.monic_X_pow_add_C _ (pow_ne_zero _ hb)⟩

private lemma chart_C (b : ℕ) (a : A) : chart A n b (C a) = Polynomial.C (C a) :=
  (chart A n b).commutes a

private lemma chart_monomial [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (v : Fin (n + 1) →₀ ℕ) :
    (chart A n b (monomial v 1)).IsMonicOfDegree (∑ i, v i * b ^ (i : ℕ)) := by
  have h : chart A n b (monomial v 1) = ∏ i, chart A n b (X i) ^ v i := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  have hm : ∀ i ∈ Finset.univ, (chart A n b (X i) ^ v i).Monic :=
    fun i _ => (chart_X hb i).monic.pow _
  rw [h]
  refine ⟨?_, Polynomial.monic_prod_of_monic _ _ hm⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(chart_X hb i).monic.natDegree_pow, (chart_X hb i).natDegree_eq]

private lemma weight_inj {m b : ℕ} (v w : Fin m → ℕ) (hv : ∀ i, v i < b) (hw : ∀ i, w i < b)
    (h : ∑ i, v i * b ^ (i : ℕ) = ∑ i, w i * b ^ (i : ℕ)) : v = w := by
  have key : (fun i => (⟨v i, hv i⟩ : Fin b)) = fun i => ⟨w i, hw i⟩ := by
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    exact h
  funext i
  exact congrArg Fin.val (congrFun key i)

end UpperTheory.NoetherNormalizationChart

open UpperTheory.NoetherNormalizationChart in
theorem UpperTheory.exists_monic_change_of_variables :
    ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (f : MvPolynomial (Fin (n + 1)) A), f ≠ 0 → ∃ (e : MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A)) (a : A), a ≠ 0 ∧ (e f).leadingCoeff = MvPolynomial.C a := by
  intro A _ _ n f hf
  classical
  set b := f.totalDegree + 1 with hbdef
  have hb : b ≠ 0 := Nat.succ_ne_zero _
  let wt : (Fin (n + 1) →₀ ℕ) → ℕ := fun v => ∑ i, v i * b ^ (i : ℕ)
  have hlt : ∀ v ∈ f.support, ∀ i, v i < b := fun v hv i =>
    Nat.lt_succ_of_le ((MvPolynomial.monomial_le_degreeOf i hv).trans
      (MvPolynomial.degreeOf_le_totalDegree f i))
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image f.support wt (MvPolynomial.support_nonempty.mpr hf)
  have ha : f.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hsum : chart A n b f = ∑ w ∈ f.support,
      Polynomial.C (MvPolynomial.C (f.coeff w)) * chart A n b (MvPolynomial.monomial w 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← chart_C b, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hdeg : (chart A n b f).natDegree ≤ wt v := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun w hw => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [(chart_monomial hb w).natDegree_eq]
    exact hmax w hw
  have hcoeff : (chart A n b f).coeff (wt v) = MvPolynomial.C (f.coeff v) := by
    rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single_of_mem v hv]
    · have h1 := (chart_monomial (A := A) hb v).monic.coeff_natDegree
      rw [(chart_monomial hb v).natDegree_eq] at h1
      rw [Polynomial.coeff_C_mul, h1, mul_one]
    · intro w hw hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [(chart_monomial hb w).natDegree_eq]
      refine lt_of_le_of_ne (hmax w hw) fun h => hne ?_
      exact DFunLike.coe_injective (weight_inj w v (hlt w hw) (hlt v hv) h)
  refine ⟨chart A n b, f.coeff v, ha, ?_⟩
  have hne : (chart A n b f).coeff (wt v) ≠ 0 := by
    rw [hcoeff]
    simpa using ha
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hne, hcoeff]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonSplitSequence
section
private theorem UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.step {A : Type} [NormedRing A] [NormedAlgebra ℝ A] (a : A)
    (h : ‖a - 1‖ ≤ (1 / 2 : ℝ)) : ‖a - 1‖ ≤ (2 / 3 : ℝ) * ‖a * a - 1‖ := by
  have e : (2 : ℝ) • (a - 1) = (a * a - 1) - (a - 1) * (a - 1) := by
    rw [two_smul]; noncomm_ring
  have h1 : ‖(2 : ℝ) • (a - 1)‖ = 2 * ‖a - 1‖ := by
    rw [norm_smul]; simp
  have h2 : ‖(a * a - 1) - (a - 1) * (a - 1)‖ ≤ ‖a * a - 1‖ + ‖a - 1‖ * ‖a - 1‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)
  rw [← e, h1] at h2
  have h3 : ‖a - 1‖ * ‖a - 1‖ ≤ ‖a - 1‖ * (1 / 2) :=
    mul_le_mul_of_nonneg_left h (norm_nonneg _)
  linarith

theorem UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.nss :
    ∀ {G A : Type} [inst : Group G]
    [inst_1 : NormedRing A] [NormedAlgebra ℝ A] (ρ : G →* A) (H : Subgroup G),
    (∀ g ∈ H, ‖(ρ : G → A) g - (1 : A)‖ ≤ (1 / 2 : ℝ)) → ∀ g ∈ H, (ρ : G → A) g = (1 : A) := by
  intro G A _ _ _ ρ H h
  have key : ∀ n : ℕ, ∀ g ∈ H, ‖ρ g - 1‖ ≤ (2 / 3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro g hg; have := h g hg; rw [pow_zero]; linarith
    | succ n ih =>
      intro g hg
      have h1 := UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.step (ρ g) (h g hg)
      have h2 := ih (g * g) (H.mul_mem hg hg)
      rw [map_mul] at h2
      rw [pow_succ]
      linarith
  intro g hg
  have lim : Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h0 : ‖ρ g - 1‖ ≤ 0 := ge_of_tendsto' lim (fun n => key n g hg)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonvanishingPoint
section
theorem UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (B : Type)
    [inst_2 : CommRing B] [inst_3 : Algebra k B] [Algebra.FiniteType k B] [IsReduced B] {c : B},
    c ≠ (0 : B) → ∃ (x : B →ₐ[k] k), (x : B → k) c ≠ (0 : k) := by
  intro k _ _ B _ _ _ _ c hc
  haveI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal B).IsRadical := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    exact (Ideal.mem_bot).2 (IsNilpotent.eq_zero ⟨n, (Ideal.mem_bot).1 hn⟩)
  have hj : (⊥ : Ideal B).jacobson = ⊥ := IsJacobsonRing.out ‹_› hrad
  have hcj : c ∉ (⊥ : Ideal B).jacobson := by
    rw [hj]
    exact fun h => hc ((Ideal.mem_bot).1 h)
  rw [Ideal.jacobson, Ideal.mem_sInf] at hcj
  push Not at hcj
  obtain ⟨m, ⟨-, hm⟩, hcm⟩ := hcj
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  let f : (B ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  intro h
  apply hcm
  have h1 : f (Ideal.Quotient.mk m c) = 0 := h
  have h2 : Ideal.Quotient.mk m c = 0 := (map_eq_zero f).1 h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormDetLe
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh58.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qh58.norm_det_le :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (ι : UpperTheory.Reformulated.B.Qh58.Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
      (R : ℝ),
      (1 : ℝ) ≤ R →
        (∀ (i j : Fin n), ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh58.Qbar l) (M i j)‖ ≤ R) →
          ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh58.Qbar l) M.det‖ ≤ R ^ n := by
  intro l _ ι n M R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_
  intro σ _
  rw [map_mul, map_prod, norm_mul, norm_prod, map_intCast]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : PadicAlgCl l)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  rw [h1, one_mul]
  calc ∏ i, ‖ι.symm (M (σ i) i)‖ ≤ ∏ _i : Fin n, R :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)
    _ = R ^ n := by simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormDetLeAlt
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh59.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qh59.norm_det_le :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (ι : UpperTheory.Reformulated.B.Qh59.Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
      (R : ℝ),
      (1 : ℝ) ≤ R →
        (∀ (i j : Fin n), ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) (M i j)‖ ≤ R) →
          ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) M.det‖ ≤ R ^ n := by
  intro l inst ι n M R hR h
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_
  intro σ _
  rw [map_mul, map_prod, norm_mul, norm_prod, map_intCast]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : UpperTheory.Reformulated.B.Qh59.Qbar l)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  have h2 : ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ R ^ n := by
    calc ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ ∏ _i : Fin n, R :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)
      _ = R ^ n := by simp
  calc _ ≤ 1 * R ^ n :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
    _ = R ^ n := one_mul _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormEqMulCE
section
noncomputable def UpperTheory.Reformulated.B.Qh29.cE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

theorem UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] [inst_2 : NumberField.IsCMField K] (y : K),
      (Algebra.algebraMap (↥(NumberField.maximalRealSubfield K)) K : ↥(NumberField.maximalRealSubfield K) → K)
          ((Algebra.norm ↥(NumberField.maximalRealSubfield K) : K → ↥(NumberField.maximalRealSubfield K)) y) =
        y * (UpperTheory.Reformulated.B.Qh29.cE K : K → K) y := by
  intro K _ _ _ y
  classical
  have hne := NumberField.IsCMField.complexConj_ne_one K
  have hcard : Nat.card (K ≃ₐ[NumberField.maximalRealSubfield K] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have huniv : (Finset.univ : Finset (K ≃ₐ[NumberField.maximalRealSubfield K] K)) =
      {1, NumberField.IsCMField.complexConj K} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne.symm, ← Nat.card_eq_fintype_card, hcard]
  have h := Algebra.norm_eq_prod_automorphisms (NumberField.maximalRealSubfield K) y
  rw [huniv, Finset.prod_pair hne.symm] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormEqOne
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk14.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qk14.norm_eq_one :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x : UpperTheory.Reformulated.B.Qk14.Qbar l},
      ‖x - (1 : UpperTheory.Reformulated.B.Qk14.Qbar l)‖ < (1 : ℝ) → ‖x‖ = (1 : ℝ) := by
  intro l _ x h
  have hne : ‖x - 1‖ ≠ ‖(1 : UpperTheory.Reformulated.B.Qk14.Qbar l)‖ := by
    rw [norm_one]
    exact h.ne
  have key := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [sub_add_cancel, norm_one] at key
  rw [key]
  exact max_eq_right h.le
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormIntegersLeOne
section
theorem UpperTheory.norm_integers_le_one :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact (Nat.Prime l)] (e : K →+* PadicAlgCl l) (x : NumberField.RingOfIntegers K), ‖e (algebraMap (NumberField.RingOfIntegers K) K x)‖ ≤ 1 := by
  intro K _ _ l _ e x
  have hx : IsIntegral ℤ (e (algebraMap (NumberField.RingOfIntegers K) K x)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map e.toIntAlgHom
  generalize e (algebraMap (NumberField.RingOfIntegers K) K x) = y at hx
  let S : Subring (PadicAlgCl l) := (NormedField.valuation (K := PadicAlgCl l)).integer
  have hS : IsIntegral S y := hx.tower_top
  have h := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral hS
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral
section
namespace UpperTheory.Reformulated.B.NormLeOneOfIsIntegral

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hle : ∀ y : PadicAlgCl l,
      y ∈ (PadicAlgCl.valued l).v.integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hmem : ∀ a : ℤ_[l],
      algebraMap ℤ_[l] (PadicAlgCl l) a ∈ (PadicAlgCl.valued l).v.integer := by
    intro a
    rw [hle, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans_le a.2
  have hint : IsIntegral (PadicAlgCl.valued l).v.integer x :=
    hx.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict _ hmem) (RingHom.id _) rfl
  exact (hle x).1 ((Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral hint)

end UpperTheory.Reformulated.B.NormLeOneOfIsIntegral
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne
section
namespace UpperTheory.Reformulated.B.NormLtOne

theorem norm_lt_one {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) : ‖y a‖ < 1 := by
  by_contra hx
  rw [not_lt] at hx
  have hx0 : y a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact absurd hx (by norm_num)
  have hu : ‖(y a)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have hint : IsIntegral ℚ_[l] (y a)⁻¹ := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly ℚ_[l] (y a)⁻¹).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] (y a)⁻¹).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmon]
    exact hu
  have hz := minpoly.aeval ℚ_[l] (y a)⁻¹
  generalize minpoly ℚ_[l] (y a)⁻¹ = P at hmon hc hz
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hz
  let c : ℕ → ℤ_[l] := fun i => ⟨P.coeff i, hc i⟩
  have hr : (∑ i ∈ Finset.range P.natDegree,
      algebraMap O R (algebraMap ℤ_[l] O (c i)) * a ^ (P.natDegree - i)) ∈ IsLocalRing.maximalIdeal R := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ha _ ?_)
    have := Finset.mem_range.mp hi
    omega
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem hr)
  apply (hunit.map y).ne_zero
  have hz' := congrArg (· * y a ^ P.natDegree) hz
  simp only [zero_mul, add_mul, Finset.sum_mul] at hz'
  rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow] at hz'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sub_neg_eq_add, map_add (f := _), map_one, map_sum, add_comm, ← hz']
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := (Finset.mem_range.mp hi).le
  rw [map_mul, map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), Algebra.smul_def, mul_assoc,
    pow_sub₀ _ hx0 hi', inv_pow, mul_comm (y a ^ P.natDegree)]
  rfl

end UpperTheory.Reformulated.B.NormLtOne
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormOnValuationRing
section
open scoped NNReal

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact PadicAlgCl.norm_extends l (a : ℚ_[l])

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one {l : ℕ} [Fact (Nat.Prime l)] {y : PadicAlgCl l}
    (hy : IsIntegral ℤ_[l] y) : ‖y‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) ℝ≥0 := NormedField.valuation
  have hv : ∀ z : PadicAlgCl l, z ∈ v.integer ↔ ‖z‖ ≤ 1 := fun z => by
    rw [Valuation.mem_integer_iff]
    exact NNReal.coe_le_coe.symm
  let f : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => (hv _).2 (by
      rw [UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap]; exact a.norm_le_one)
  have h : IsIntegral v.integer y :=
    hy.map_of_comp_eq f (RingHom.id _) (by ext a; rfl)
  exact (hv y).1 ((Valuation.integer.integers v).mem_of_integral h)

theorem UpperTheory.Reformulated.B.NormOnValuationRing.mem_max_iff :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {T : Type}
    [inst_1 : CommRing T] [inst_2 : IsLocalRing T] [inst_3 : Algebra ℤ_[l] T] [Algebra.IsIntegral ℤ_[l] T]
    (φ : T →ₐ[ℤ_[l]] PadicAlgCl l) (x : T), x ∈ IsLocalRing.maximalIdeal T ↔ ‖(φ : T → PadicAlgCl l) x‖ < (1 : ℝ) := by
  intro l _ T _ _ _ _ φ x
  have hle : ∀ t : T, ‖φ t‖ ≤ 1 := fun t =>
    UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) t).map φ)
  let P : Ideal T :=
    { carrier := {t | ‖φ t‖ < 1}
      add_mem' := fun {a b} ha hb => by
        change ‖φ (a + b)‖ < 1
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        change ‖φ (c * a)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ t : T, t ∈ P ↔ ‖φ t‖ < 1 := fun _ => Iff.rfl
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP, map_mul, norm_mul] at hab
      by_contra h
      rw [not_or, hP, hP, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)
  have hcomap : P.comap (algebraMap ℤ_[l] T) = IsLocalRing.maximalIdeal ℤ_[l] := by
    ext a
    rw [Ideal.mem_comap, hP, φ.commutes, UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  have hmax : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) P
    change (P.comap (algebraMap ℤ_[l] T)).IsMaximal
    rw [hcomap]
    exact IsLocalRing.maximalIdeal.isMaximal ℤ_[l]
  rw [← IsLocalRing.eq_maximalIdeal hmax, hP]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormPowSubPowLe
section
theorem UpperTheory.Reformulated.B.Qi18.norm_pow_sub_pow_le.{u_1} :
    ∀ {K : Type u_1} [inst : NormedField K]
    [IsUltrametricDist K] (x y : K), ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) → ∀ (e : ℕ), ‖x ^ e - y ^ e‖ ≤ ‖x - y‖ := by
  intro K _ _ x y hx hy e
  induction e with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)
end

