module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsUniqueFixedPoint
section
open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.Ydb5.le_order_iff {σ R : Type*} [CommRing R]
    (f g : MvPowerSeries σ R) (n : ℕ) :
    (n : ℕ∞) ≤ (f - g).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    have h0 : coeff d (f - g) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    rwa [map_sub, sub_eq_zero] at h0
  · intro h
    refine nat_le_order fun d hd => ?_
    rw [map_sub, h d hd, sub_self]

theorem UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint.{u_1, u_2} :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] (Φ : MvPowerSeries σ R → MvPowerSeries σ R),
      (∀ (f g : MvPowerSeries σ R) (n : ℕ), (↑n : ℕ∞) ≤ (f - g).order → (↑(n + (1 : ℕ)) : ℕ∞) ≤ (Φ f - Φ g).order) →
        ∃! f : MvPowerSeries σ R, Φ f = f := by
  intro σ R _ Φ h
  simp only [UpperTheory.Reformulated.B.Ydb5.le_order_iff] at h
  have step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k g
    induction k with
    | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h _ _ k ih
  let f : MvPowerSeries σ R := fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)
  have hf : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0) := fun _ => rfl
  have approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k d hd
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
    rw [hf, Function.iterate_add_apply Φ (Nat.succ _) m]
    exact (step _ _ d (Nat.lt_succ_self _)).symm
  refine ⟨f, ?_, ?_⟩
  · ext d
    rw [h f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']
  · intro g hg
    ext d
    rw [hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsValuationSubLeOne
section
theorem UpperTheory.Reformulated.B.ExistsValuationSubLeOne.exists_valuation_sub_le_one.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Type u_2} [inst_2 : Field K]
    [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K] (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (x : IsDedekindDomain.HeightOneSpectrum R → K),
    ∃ (k : K),
      (∀ v ∈ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) (k - x v) ≤
            (1 : WithZero (Multiplicative ℤ))) ∧
        ∀ v ∉ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) k ≤
            (1 : WithZero (Multiplicative ℤ)) := by
  classical
  intro R _ _ K _ _ _ S x
  obtain ⟨⟨d, hdm⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) S x
  simp only at hd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdm
  have hdK : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdm
  have hr : ∀ v, ∃ r : R, v ∈ S → algebraMap R K r = algebraMap R K d * x v := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hd v hv
      exact ⟨r, fun _ => by rw [hr, Algebra.smul_def]⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose r hr using hr
  have hI : Ideal.span {d} ≠ (0 : Ideal R) := by
    simpa using hd0
  let T : Finset (IsDedekindDomain.HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  have he : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      v.intValuation d = WithZero.exp (-(e v : ℤ)) := fun v => v.intValuation_if_neg hd0
  have he0 : ∀ v, v ∉ T → e v = 0 := by
    intro v hv
    have hmem : d ∉ v.asIdeal := by
      intro h
      apply hv
      simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact Or.inr (Ideal.dvd_span_singleton.2 h)
    have h1 := IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hmem
    rw [he, ← WithZero.exp_zero, WithZero.exp_inj] at h1
    omega
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : IsDedekindDomain.HeightOneSpectrum R => v.asIdeal) e
    (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then r v.1 else 0)
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (a : R), a ∈ v.asIdeal ^ e v →
      v.valuation K (algebraMap R K a / algebraMap R K d) ≤ 1 := by
    intro v a ha
    rw [map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, he]
    exact div_le_one_of_le₀ ((v.intValuation_le_pow_iff_mem a (e v)).2 ha) zero_le'
  refine ⟨algebraMap R K y / algebraMap R K d, fun v hv => ?_, fun v hv => ?_⟩
  · have hvT : v ∈ T := Finset.mem_union_left _ hv
    have h1 := hy v hvT
    simp only [hv, if_true] at h1
    have h2 := key v _ h1
    have h3 : algebraMap R K (y - r v) / algebraMap R K d =
        algebraMap R K y / algebraMap R K d - x v := by
      rw [map_sub, hr v hv]
      field_simp
    rwa [h3] at h2
  · apply key
    by_cases hvT : v ∈ T
    · have h1 := hy v hvT
      simpa [hv] using h1
    · simp [he0 v hvT]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExpSq
section
theorem UpperTheory.Reformulated.B.Qf11.expSq :
    ∀ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ),
    N * N = (0 : Matrix (Fin n) (Fin n) ℂ) → NormedSpace.exp N = (1 : Matrix (Fin n) (Fin n) ℂ) + N := by
  intro n N h
  have hz : ∀ k : ℕ, k ∉ Finset.range 2 → ((k.factorial : ℂ)⁻¹) • N ^ k = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by
      rw [Finset.mem_range] at hk
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    rw [pow_add, pow_two, h, zero_mul, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtIntegral
section
theorem UpperTheory.Reformulated.B.Qe16.ext_integral :
    ∀ {B S K : Type} [inst : CommRing B] [inst_1 : CommRing S]
    [inst_2 : Field K] [IsAlgClosed K] [inst_4 : Algebra B S] [Algebra.IsIntegral B S],
    Function.Injective (⇑(Algebra.algebraMap B S) : B → S) →
      ∀ (φ : B →+* K), ∃ (Φ : S →+* K), ∀ (b : B), (Φ : S → K) ((Algebra.algebraMap B S : B → S) b) = (φ : B → K) b := by
  intro B S K _ _ _ _ _ _ hinj φ
  haveI hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker φ) ⊥ (by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le)
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (B ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : Algebra.IsIntegral (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := B)
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Nontrivial (B ⧸ RingHom.ker φ) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  haveI : Algebra.IsAlgebraic (B ⧸ RingHom.ker φ) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : (S ⧸ Q) →ₐ[B ⧸ RingHom.ker φ] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun b => ?_⟩
  exact (f.commutes (Ideal.Quotient.mk _ b)).trans (RingHom.kerLift_mk φ b)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtendPt
section
theorem UpperTheory.Reformulated.B.Qi4.extendPt :
    ∀ (O Λ T K : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : CommRing T]
    [inst_3 : Field K] [IsAlgClosed K] [inst_5 : Algebra O Λ] [inst_6 : Algebra O T] [inst_7 : Algebra Λ T]
    [IsScalarTower O Λ T] [inst_9 : Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K),
    Ideal.comap (Algebra.algebraMap Λ T) P ≤ RingHom.ker y →
      ∃ (x : T →ₐ[O] K),
        P ≤ RingHom.ker x ∧ ∀ (a : Λ), (x : T → K) ((Algebra.algebraMap Λ T : Λ → T) a) = (y : Λ → K) a := by
  intro O Λ T K _ _ _ _ _ _ _ _ _ _ _ P y hP
  haveI hprime : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, hPQ, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker y) P hP
  change Q.comap (algebraMap Λ T) = RingHom.ker y at hQc
  have hker : ∀ a ∈ Q.comap (algebraMap Λ T), (y : Λ →+* K) a = 0 := by
    intro a ha
    rw [hQc] at ha
    exact ha
  let ybar : (Λ ⧸ Q.comap (algebraMap Λ T)) →+* K := Ideal.Quotient.lift _ (y : Λ →+* K) hker
  have hinj : Function.Injective ybar := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact ha
  letI : Algebra (Λ ⧸ Q.comap (algebraMap Λ T)) K := ybar.toAlgebra
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI hint : Algebra.IsIntegral (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let z : (T ⧸ Q) →ₐ[Λ ⧸ Q.comap (algebraMap Λ T)] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hz : ∀ a : Λ, z (Ideal.Quotient.mk Q (algebraMap Λ T a)) = y a := fun a =>
    z.commutes (Ideal.Quotient.mk _ a)
  refine ⟨{ (z : (T ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q) with commutes' := fun o => ?_ }, ?_, hz⟩
  · have h := hz (algebraMap O Λ o)
    rw [← IsScalarTower.algebraMap_apply, y.commutes] at h
    exact h
  · intro t ht
    have h0 : Ideal.Quotient.mk Q t = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hPQ ht)
    show z (Ideal.Quotient.mk Q t) = 0
    rw [h0, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FGe
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk42.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qk42.FGe :
    {R : Type} → [CommRing R] → (Fin (4 : ℕ) → ℤ) → ℤ → UpperTheory.Reformulated.B.Qk42.M4 R → Prop :=
    fun {R : Type} [CommRing R] (m : Fin (4 : ℕ) → ℤ) (p : ℤ) (X : UpperTheory.Reformulated.B.Qk42.M4 R) ↦
      ∀ (i j : Fin (4 : ℕ)), m i - m j < p → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qk42.mul :
    ∀ {R : Type} [inst : CommRing R] {m : Fin (4 : ℕ) → ℤ} {p q : ℤ} {A B : UpperTheory.Reformulated.B.Qk42.M4 R},
      UpperTheory.Reformulated.B.Qk42.FGe m p A → UpperTheory.Reformulated.B.Qk42.FGe m q B → UpperTheory.Reformulated.B.Qk42.FGe m (p + q) (A * B) := by
  intro R _ m p q A B hA hB i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : m i - m k < p
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (by omega), mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FInt
section
namespace YhaHelp
open MeasureTheory Set Real

private lemma F_int {c : ℝ} (hc : 0 < c) :
    Integrable ((Ici (0:ℝ)).indicator (fun x : ℝ => exp (-c * x))) := by
  rw [integrable_indicator_iff measurableSet_Ici]
  exact (exp_neg_integrableOn_Ioi (-1) hc).mono_set (fun x hx => by
    simp only [mem_Ici, mem_Ioi] at *; linarith)

end YhaHelp

theorem UpperTheory.Reformulated.B.Yha4.main :
    ∀ {c : ℝ}, (0 : ℝ) < c → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-c * |x|)) MeasureTheory.MeasureSpace.volume := by
  intro c hc
  have hF := YhaHelp.F_int hc
  have hG := hF.comp_neg
  refine (hF.add hG).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply, Set.indicator, Set.mem_Ici, Left.nonneg_neg_iff]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, if_pos h]
    split_ifs
    · linarith [Real.exp_pos (-c * -x)]
    · simp
  · rw [abs_of_neg h, if_neg (not_le.mpr h), if_pos h.le]
    simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorConjugationCancel
section
open MeasureTheory

private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] {a b : NNReal}
    (h : a • ν = b • ν) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have h1 : ν K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 : (a : ENNReal) * ν K = (b : ENNReal) * ν K := by
    have := congrArg (fun μ : Measure G => μ K) h
    simpa using this
  exact_mod_cast (ENNReal.mul_left_inj h0 h1).1 h2

private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (m : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] :
    ∃ a : NNReal, Measure.map (⇑m : G → G) ν = a • ν := by
  haveI : (Measure.map (⇑m : G → G) ν).IsAddHaarMeasure := m.isAddHaarMeasure_map ν
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩

theorem UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj :
    ∀ {G : Type} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_5 : MeasurableSpace G]
    [BorelSpace G] (m s : G ≃ₜ+ G) (ν : MeasureTheory.Measure G) [ν.IsAddHaarMeasure] (c : NNReal),
    (∀ (x : G), (s : G → G) ((s : G → G) x) = x) →
      MeasureTheory.Measure.map (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x)))) ν = (c * c) • ν →
        MeasureTheory.Measure.map (⇑m : G → G) ν = c • ν := by
  intro G _ _ _ _ _ _ _ m s ν _ c hs h
  obtain ⟨a, ha⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor m ν
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor s ν
  have mm : Measurable (⇑m : G → G) := m.continuous.measurable
  have ms : Measurable (⇑s : G → G) := s.continuous.measurable
  have hm' : ∀ r : NNReal, Measure.map (⇑m : G → G) (r • ν) = (r * a) • ν := by
    intro r
    rw [Measure.map_smul r mm.aemeasurable, ha, smul_smul]
  have hs' : ∀ r : NNReal, Measure.map (⇑s : G → G) (r • ν) = (r * b) • ν := by
    intro r
    rw [Measure.map_smul r ms.aemeasurable, hb, smul_smul]
  have hbb : b * b = 1 := by
    apply UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν
    rw [← hs', ← hb, Measure.map_map ms ms, one_smul]
    have : (⇑s ∘ ⇑s : G → G) = id := funext hs
    rw [this, Measure.map_id]
  have hcomp : (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x))))
      = (⇑s : G → G) ∘ ((⇑m : G → G) ∘ ((⇑s : G → G) ∘ (⇑m : G → G))) := rfl
  rw [hcomp, ← Measure.map_map ms (mm.comp (ms.comp mm)), ← Measure.map_map mm (ms.comp mm),
    ← Measure.map_map ms mm, ha, hs', hm', hs'] at h
  have h2 := UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν h
  have h3 : a * a = c * c := by
    rw [← h2]
    calc a * a = a * a * (b * b) := by rw [hbb, mul_one]
      _ = _ := by ring
  have h5 : (a : ℝ) * a = (c : ℝ) * c := by rw [← NNReal.coe_mul, ← NNReal.coe_mul, h3]
  have h4 : a = c := NNReal.eq ((mul_self_inj_of_nonneg a.coe_nonneg c.coe_nonneg).1 h5)
  rw [ha, h4]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorialTendstoZero
section
open Filter Topology NumberField IsDedekindDomain

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero {K : Type*} [NormedField K]
    (h1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (N : ℕ) (hN : 0 < N) (hlt : ‖(N : K)‖ < 1) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : K)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (norm_nonneg _),
    fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ha hlt
  filter_upwards [eventually_ge_atTop (N ^ k)] with n hn
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hN k) hn
  rw [hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (by positivity) (h1 m)).trans_lt hk

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  refine UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero (K := v.adicCompletion F) (fun n => ?_)
    (Ideal.absNorm v.asIdeal) (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)) ?_
  · have := FinitePlace.norm_le_one F v (n : 𝓞 F)
    rwa [map_natCast, map_natCast] at this
  · have := (FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
    rwa [map_natCast, map_natCast] at this

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto {F : Type} [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h : Tendsto (fun (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_subtype_rng]
    simpa using UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto v
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous
  exact (hc.tendsto _).comp h

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto {r : ℝ} (hr : 0 ≤ r)
    (h : Tendsto (fun n : ℕ => r ^ n.factorial) atTop (𝓝 1)) : r = 1 := by
  have hf : Tendsto Nat.factorial atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · exact absurd (tendsto_nhds_unique ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hlt).comp hf) h)
      zero_ne_one
  · exact heq
  · exact absurd h (not_tendsto_nhds_of_tendsto_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt hgt).comp hf) 1)

theorem UpperTheory.Reformulated.B.AdelicCharacterNormOne.norm_eq_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
    Continuous (⇑ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) →
      (∀ (a : F),
          (ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ)
              ((Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                  F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                a) =
            (1 : ℂ)) →
        ∀ (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F),
          ‖(ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) x‖ = (1 : ℝ) := by
  intro F _ _ ψ hψ htriv
  let i : InfiniteAdeleRing F → AdeleRing (𝓞 F) F := fun x => (x, 0)
  let j : FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F := fun y => (0, y)
  have hi : Continuous i := continuous_id.prodMk continuous_const
  have hj : Continuous j := continuous_const.prodMk continuous_id
  have hsplit : ∀ x : AdeleRing (𝓞 F) F, x = i x.1 + j x.2 := fun x =>
    Prod.ext (add_zero x.1).symm (zero_add x.2).symm
  have hfin : ∀ y, ‖ψ (j y)‖ = 1 := by
    intro y
    apply UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto (norm_nonneg _)
    have h1 := (UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto (F := F)).mul_const y
    rw [zero_mul] at h1
    have h2 := (((hψ.comp hj).norm).tendsto 0).comp h1
    have h0 : j 0 = 0 := rfl
    have hs : ∀ n : ℕ, j ((n : FiniteAdeleRing (𝓞 F) F) * y) = n • j y := fun n =>
      Prod.ext (nsmul_zero n).symm (nsmul_eq_mul n y).symm
    simp only [Function.comp_def, h0, hs, AddChar.map_zero_eq_one, norm_one,
      AddChar.map_nsmul_eq_pow, norm_pow] at h2
    exact h2
  have hinf : ∀ x, ‖ψ (i x)‖ = 1 := by
    intro x
    refine (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x
      (isClosed_eq (hψ.comp hi).norm continuous_const) fun a => ?_
    have h := congrArg norm (htriv a)
    rw [hsplit (algebraMap F _ a), AddChar.map_add_eq_mul, norm_mul, hfin, mul_one, norm_one] at h
    exact h
  intro x
  rw [hsplit x, AddChar.map_add_eq_mul, norm_mul, hfin, hinf, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinOfHom
section
theorem UpperTheory.Reformulated.B.Qh10.fin_of_hom :
    ∀ {S R M : Type} [inst : CommRing S] [inst_1 : CommRing R]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module S M] [inst_4 : _root_.Module R M] [Module.Finite S M] (f : S → R),
    (∀ (a : S) (m : M), a • m = f a • m) → Module.Finite R M := by
  intro S R M _ _ _ _ _ hfin f hf
  obtain ⟨T, hT⟩ := hfin.fg_top
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro m hm0
  clear hm0
  have hm : m ∈ Submodule.span S (T : Set M) := by
    rw [hT]
    exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [hf]
    exact Submodule.smul_mem _ _ hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormNatCastPrime
section
theorem UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], ‖(↑p : PadicAlgCl p)‖ = (↑p : ℝ)⁻¹ := by
  intro p _
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends p (p : ℚ_[p])).trans Padic.norm_p
end

