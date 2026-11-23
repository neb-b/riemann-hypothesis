module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import ReciprocityTheory.SemistableReduction.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PlaceResiduePowerBound

open WithZero

variable {F : Type} [Field F]

theorem pow_inj {e : ℕ} (he : e ≠ 0) {a b : ℤᵐ⁰} (h : a ^ e = b ^ e) : a = b :=
  le_antisymm ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.le)
    ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.ge)

theorem pow_le_one_iff' {e : ℕ} (he : e ≠ 0) {a : ℤᵐ⁰} : a ^ e ≤ 1 ↔ a ≤ 1 := by
  simpa using (pow_le_pow_iff_left₀ (zero_le' (a := a)) (zero_le' (a := (1 : ℤᵐ⁰))) he)

theorem pow_of_iff (v q : Valuation F ℤᵐ⁰) (hq : Function.Surjective q)
    (h : ∀ x, v x ≤ 1 ↔ q x ≤ 1) : ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  obtain ⟨π, hπ⟩ := hq (exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hvπ0 : v π ≠ 0 := (Valuation.ne_zero_iff v).2 hπ0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, v π = exp b := ⟨log (v π), (exp_log hvπ0).symm⟩
  have hb0 : b < 0 := by
    have h1 : v π ≤ 1 := (h π).2 (by rw [hπ, ← exp_zero, exp_le_exp]; norm_num)
    have h2 : v π ≠ 1 := by
      intro h1'
      have : q π⁻¹ ≤ 1 := (h _).1 (by rw [map_inv₀, h1', inv_one])
      rw [map_inv₀, hπ, ← exp_neg, ← exp_zero, exp_le_exp] at this
      norm_num at this
    rw [hb, ← exp_zero, exp_le_exp] at h1
    rw [hb, ne_eq, exp_eq_one] at h2
    omega
  have hbe : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
  refine ⟨(-b).toNat, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero, zero_pow (by omega)]
  have hqx : q x ≠ 0 := (Valuation.ne_zero_iff q).2 hx
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
  obtain ⟨c, hc⟩ : ∃ c : ℤ, q x = exp c := ⟨log (q x), (exp_log hqx).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a := ⟨log (v x), (exp_log hvx).symm⟩
  have hqu : q (x * π ^ c) = 1 := by
    rw [map_mul, map_zpow₀, hc, hπ, ← exp_zsmul, ← exp_add, exp_eq_one, smul_eq_mul]; ring
  have hvu : v (x * π ^ c) = exp (a + c * b) := by
    rw [map_mul, map_zpow₀, ha, hb, ← exp_zsmul, ← exp_add, smul_eq_mul]
  have h1 : v (x * π ^ c) ≤ 1 := (h _).2 hqu.le
  have h2 : v (x * π ^ c)⁻¹ ≤ 1 := (h _).2 (by rw [map_inv₀, hqu, inv_one])
  rw [hvu, ← exp_zero, exp_le_exp] at h1
  rw [map_inv₀, hvu, ← exp_neg, ← exp_zero, exp_le_exp] at h2
  have h3 : a + c * b = 0 := by omega
  rw [ha, hc, ← exp_nsmul, exp_inj, nsmul_eq_mul, hbe]
  linear_combination h3

theorem root (v : Valuation F ℤᵐ⁰) (hv : ∃ a, 1 < v a) :
    ∃ q : Valuation F ℤᵐ⁰, Function.Surjective q ∧ ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  classical
  have hS : ∃ n : ℕ, 0 < n ∧ ∃ x, v x = exp (n : ℤ) := by
    obtain ⟨a, ha⟩ := hv
    have ha0 : v a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
    obtain ⟨b, hb⟩ : ∃ b : ℤ, v a = exp b := ⟨_, (exp_log ha0).symm⟩
    rw [hb, ← exp_zero, exp_lt_exp] at ha
    exact ⟨b.toNat, by omega, a, by rw [hb, Int.toNat_of_nonneg ha.le]⟩
  have he0 : 0 < Nat.find hS := (Nat.find_spec hS).1
  obtain ⟨π, hπ⟩ := (Nat.find_spec hS).2
  have hdvd : ∀ x, x ≠ 0 → ∃ m : ℤ, v x = exp ((Nat.find hS : ℤ) * m) := by
    intro x hx
    obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a :=
      ⟨_, (exp_log ((Valuation.ne_zero_iff v).2 hx)).symm⟩
    refine ⟨a / (Nat.find hS : ℤ), ?_⟩
    have hr0 : 0 ≤ a % (Nat.find hS : ℤ) := Int.emod_nonneg _ (by omega)
    have hr1 : a % (Nat.find hS : ℤ) < Nat.find hS := Int.emod_lt_of_pos _ (by omega)
    have hdec := Int.mul_ediv_add_emod a (Nat.find hS : ℤ)
    by_contra hne
    have hr : 0 < a % (Nat.find hS : ℤ) := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; rw [ha, exp_inj]; linear_combination -hdec - h
    have hval : v (x * π ^ (-(a / (Nat.find hS : ℤ)))) = exp (((a % (Nat.find hS : ℤ)).toNat : ℕ) : ℤ) := by
      rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, Int.toNat_of_nonneg hr0, exp_inj,
        smul_eq_mul]
      linear_combination -hdec
    exact Nat.find_min hS (show (a % (Nat.find hS : ℤ)).toNat < Nat.find hS by omega)
      ⟨by omega, _, hval⟩
  have hroot : ∀ x, ∃ c : ℤᵐ⁰, c ^ Nat.find hS = v x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero, zero_pow he0.ne']⟩
    · obtain ⟨m, hm⟩ := hdvd x hx
      exact ⟨exp m, by rw [hm, ← exp_nsmul, nsmul_eq_mul]⟩
  choose qf hqf using hroot
  have hle : ∀ {a b : ℤᵐ⁰}, a ^ Nat.find hS ≤ b ^ Nat.find hS → a ≤ b :=
    fun h => (pow_le_pow_iff_left₀ zero_le' zero_le' he0.ne').1 h
  let q : Valuation F ℤᵐ⁰ :=
    { toFun := qf
      map_zero' := pow_inj he0.ne' (by rw [hqf, map_zero, zero_pow he0.ne'])
      map_one' := pow_inj he0.ne' (by rw [hqf, map_one, one_pow])
      map_mul' := fun x y => pow_inj he0.ne' (by rw [hqf, mul_pow, hqf, hqf, map_mul])
      map_add_le_max' := fun x y => by
        have h := v.map_add x y
        rw [← hqf x, ← hqf y, ← hqf (x + y)] at h
        rcases le_max_iff.1 h with h | h
        · exact le_max_of_le_left (hle h)
        · exact le_max_of_le_right (hle h) }
  have hqq : ∀ x, q x = qf x := fun _ => rfl
  refine ⟨q, ?_, Nat.find hS, he0, fun x => by rw [hqq, hqf]⟩
  have hqπ : q π = exp 1 :=
    pow_inj he0.ne' (by rw [hqq, hqf, hπ, ← exp_nsmul, nsmul_eq_mul, mul_one])
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨0, map_zero q⟩
  · refine ⟨π ^ log t, ?_⟩
    rw [map_zpow₀, hqπ, ← exp_zsmul, smul_eq_mul, mul_one, exp_log ht]

theorem exists_one_lt {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : Valuation E ℤᵐ⁰) (hp : Function.Surjective p) : ∃ a : F, 1 < p (algebraMap F E a) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hp (exp (1 : ℤ))
  have hy1 : 1 < p y := by rw [hy, ← exp_zero, exp_lt_exp]; norm_num
  obtain ⟨f, hfm, hfy⟩ := Algebra.IsIntegral.isIntegral (R := F) y
  rw [hfm.as_sum] at hfy
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hfy
  have hlt : p (∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i) <
      p y ^ f.natDegree := by
    apply p.map_sum_lt (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy1)))
    intro i hi
    rw [map_mul, map_pow]
    calc p (algebraMap F E (f.coeff i)) * p y ^ i ≤ 1 * p y ^ i := mul_le_mul_of_nonneg_right (hcon _) zero_le'
      _ = p y ^ i := one_mul _
      _ < p y ^ f.natDegree := pow_lt_pow_right₀ hy1 (Finset.mem_range.1 hi)
  have hs : ∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i =
      -(y ^ f.natDegree) := by linear_combination hfy
  rw [hs, Valuation.map_neg, map_pow] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory.Nef.PlaceResiduePowerBound

namespace GlobalTheory.Nef

open WithZero

theorem place_res_exists_pow : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E],
    (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p,
      ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧
        ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  intro k F E _ _ _ _ _ _ _ _
  refine ⟨?_, fun ρ hρ p => ?_⟩
  · have hex : ∀ p : Place k E, ∃ q : Place k F,
        ∀ x, p.1 (algebraMap F E x) ≤ 1 ↔ q.1 x ≤ 1 := by
      intro p
      obtain ⟨a, ha⟩ := PlaceResiduePowerBound.exists_one_lt (F := F) p.1 p.2.1
      obtain ⟨q, hq, e, he, hpow⟩ := PlaceResiduePowerBound.root (p.1.comap (algebraMap F E)) ⟨a, ha⟩
      refine ⟨⟨q, hq, fun c hc => ?_⟩, fun x => ?_⟩
      · apply PlaceResiduePowerBound.pow_inj he.ne'
        rw [← hpow, Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, p.2.2 c hc, one_pow]
      · have h := hpow x
        rw [Valuation.comap_apply] at h
        rw [h, PlaceResiduePowerBound.pow_le_one_iff' he.ne']
    choose ρ hρ using hex
    exact ⟨ρ, hρ⟩
  · obtain ⟨e, he, hpow⟩ :=
      PlaceResiduePowerBound.pow_of_iff (p.1.comap (algebraMap F E)) (ρ p).1 (ρ p).2.1 (fun x => hρ p x)
    refine ⟨e, he, fun x => hpow x, fun x => ?_⟩
    have h : p.1 (algebraMap F E x) = (ρ p).1 x ^ e := hpow x
    unfold ord
    rw [h, log_pow, nsmul_eq_mul]
    ring

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreserving
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.GaussMarginal

open Real

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succ,
      ← ih (fun i => f i.succ) (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
    refine lintegral_congr fun q => ?_
    simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e := (Fintype.equivFin ι).symm
  have h := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), ← e.prod_comp,
    ← lintegral_pi_fin _ μ (fun i => f (e i)) (fun i => hf _)]
  refine lintegral_congr fun q => ?_
  rw [← e.prod_comp]
  simp [MeasurableEquiv.coe_piCongrLeft]

theorem pi_withDensity_const {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [SigmaFinite μ] (f : E → ENNReal) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _), ← lintegral_indicator (hs _)]
  rw [← lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i trivial) _).symm
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem isProbabilityMeasure_complexGaussian_one :
    IsProbabilityMeasure (GlobalTheory.complexGaussian ℂ 1) :=
  GlobalTheory.isProbabilityMeasure_complexGaussian (by simp [Complex.finrank_real_complex])

theorem gaussProb_eq_complexGaussian (k : ℕ) :
    gaussProb k = GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k := by
  have hP := GlobalTheory.isProbabilityMeasure_complexGaussian (E := EuclideanSpace ℂ (Fin k)) (g := k)
    (by rw [GlobalTheory.finrank_real_euclideanSpace_complex, Fintype.card_fin])
  set ν := (volume : Measure (EuclideanSpace ℂ (Fin k))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hν
  have hm : Measurable fun x : EuclideanSpace ℂ (Fin k) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) := by
    fun_prop
  have hc : GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k = ENNReal.ofReal ((π ^ k)⁻¹) • ν := by
    ext s hs
    rw [Measure.smul_apply, GlobalTheory.complexGaussian, withDensity_apply _ hs, hν, withDensity_apply _ hs,
      smul_eq_mul, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have h1 := hP.measure_univ
  rw [hc, Measure.smul_apply, smul_eq_mul] at h1
  rw [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ, hc, ← hν,
    ← ENNReal.eq_inv_of_mul_eq_one_left h1]

theorem map_ofLp_gaussProb (k : ℕ) :
    (gaussProb k).map (WithLp.ofLp (p := 2) (V := Fin k → ℂ)) =
      Measure.pi fun _ : Fin k => GlobalTheory.complexGaussian ℂ 1 := by
  haveI := isProbabilityMeasure_complexGaussian_one
  have hmp := GlobalTheory.volume_preserving_ofLp_complex (Fin k)
  set f1 : ℂ → ENNReal := fun z => ENNReal.ofReal ((π ^ 1)⁻¹ * Real.exp (-‖z‖ ^ 2)) with hf1
  have hf1m : Measurable f1 := by fun_prop
  haveI : SigmaFinite ((volume : Measure ℂ).withDensity f1) :=
    inferInstanceAs (SigmaFinite (GlobalTheory.complexGaussian ℂ 1))
  have hG : Measurable fun y : Fin k → ℂ => ∏ i, f1 (y i) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmp.measurable hs, gaussProb_eq_complexGaussian, GlobalTheory.complexGaussian,
    withDensity_apply _ (hmp.measurable hs), show GlobalTheory.complexGaussian ℂ 1 = (volume : Measure ℂ).withDensity f1 from rfl,
    pi_withDensity_const _ f1 hf1m, ← volume_pi, withDensity_apply _ hs,
    ← hmp.setLIntegral_comp_preimage hs hG]
  refine lintegral_congr fun x => ?_
  simp only [hf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_neg_distrib, pow_one, inv_pow]

theorem measurePreserving_restrict_castLE {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {N n : ℕ} (h : N ≤ n) :
    MeasurePreserving (fun (y : Fin n → α) (j : Fin N) => y (Fin.castLE h j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hr : Measurable fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  refine ⟨hr, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  have hpre : (fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j)) ⁻¹' univ.pi s =
      univ.pi (Fin.append s fun _ : Fin m => (univ : Set α)) := by
    ext y
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hy i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hy j
      · rw [Fin.append_right]; exact mem_univ _
    · intro hy j
      have := hy (Fin.castAdd m j)
      rwa [Fin.append_left] at this
  rw [hpre, Measure.pi_pi, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem measurePreserving_firstCoords_gaussProb :
    ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  intro N n h
  haveI := isProbabilityMeasure_complexGaussian_one
  have hofn : Measurable (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).measurable
  have hofN : Measurable (WithLp.ofLp (p := 2) (V := Fin N → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin N)).measurable
  have htoN : Measurable (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N)) := by fun_prop
  have e1 : MeasurePreserving (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) (gaussProb n)
      (Measure.pi fun _ : Fin n => GlobalTheory.complexGaussian ℂ 1) := ⟨hofn, map_ofLp_gaussProb n⟩
  have e3 : MeasurePreserving (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N))
      (Measure.pi fun _ : Fin N => GlobalTheory.complexGaussian ℂ 1) (gaussProb N) := by
    refine ⟨htoN, ?_⟩
    rw [← map_ofLp_gaussProb N, Measure.map_map htoN hofN]
    convert Measure.map_id
    funext x
    rfl
  exact e3.comp ((measurePreserving_restrict_castLE _ h).comp e1)

end GlobalTheory.GaussMarginal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianRadialLawProbabilityLogIntegrableMean
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

namespace GlobalTheory.SphereMeanDrop

theorem radProb_log_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧
    Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧
    ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
  intro n hn
  set μ0 := Measure.volumeIoiPow (2 * n - 1) with hμ0
  set f : Ioi (0:ℝ) → NNReal := fun r => Real.toNNReal (Real.exp (-(r : ℝ) ^ 2)) with hf
  have hfm : Measurable f := by
    rw [hf]; exact (by fun_prop : Measurable fun r : Ioi (0:ℝ) => Real.exp (-(r : ℝ) ^ 2)).real_toNNReal
  have hν : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)))
      = μ0.withDensity fun r => (f r : ENNReal) := rfl
  have hJi : Integrable (fun r : Ioi (0 : ℝ) ↦ Real.exp (-(r : ℝ) ^ 2)) μ0 :=
    integrable_volumeIoiPow (k := 2 * n - 1) (g := fun r ↦ Real.exp (-r ^ 2)) (integrableOn_radJ _)
  have hKo : IntegrableOn (fun r : ℝ ↦ r ^ (2 * n - 1) * (Real.log r * Real.exp (-r ^ 2))) (Ioi 0) := by
    refine (integrableOn_radK (k := 2 * n - 1) (by omega)).congr_fun (fun r _ ↦ ?_)
      measurableSet_Ioi
    ring
  have hKi : Integrable (fun r : Ioi (0 : ℝ) ↦ Real.log r * Real.exp (-(r : ℝ) ^ 2)) μ0 :=
    integrable_volumeIoiPow (k := 2 * n - 1) (g := fun r ↦ Real.log r * Real.exp (-r ^ 2)) hKo
  have hJv : ∫ r : Ioi (0 : ℝ), Real.exp (-(r : ℝ) ^ 2) ∂μ0 = radJ (2 * n - 1) := by
    rw [hμ0, integral_volumeIoiPow (2 * n - 1) (fun r ↦ Real.exp (-r ^ 2))]; rfl
  have hKv : ∫ r : Ioi (0 : ℝ), Real.log r * Real.exp (-(r : ℝ) ^ 2) ∂μ0 = radK (2 * n - 1) := by
    rw [hμ0, integral_volumeIoiPow (2 * n - 1) (fun r ↦ Real.log r * Real.exp (-r ^ 2)), radK]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
    ring

  have hmass : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ
      = ENNReal.ofReal (radJ (2 * n - 1)) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← hJv,
      ofReal_integral_eq_lintegral_ofReal hJi (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le)]
  have hJpos := radJ_pos (2 * n - 1)
  have hm0 : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ ≠ 0 := by
    rw [hmass]; exact ENNReal.ofReal_pos.2 hJpos |>.ne'
  have hmt : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ ≠ ⊤ := by
    rw [hmass]; exact ENNReal.ofReal_ne_top
  have hcond : radProb n = ((μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ)⁻¹ •
      (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) := by
    rw [radProb, ProbabilityTheory.cond, Measure.restrict_univ]
  refine ⟨?_, ?_, ?_⟩
  · rw [radProb]; exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hm0 hmt
  · rw [hcond]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 hm0)
    rw [hν, integrable_withDensity_iff_integrable_smul hfm]
    refine hKi.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
    ring
  · rw [hcond, integral_smul_measure, hmass, hν, integral_withDensity_eq_integral_smul hfm]
    have : ∫ r : Ioi (0:ℝ), f r • Real.log (r : ℝ) ∂μ0 = radK (2 * n - 1) := by
      rw [← hKv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
      ring
    rw [this, ENNReal.toReal_inv, ENNReal.toReal_ofReal hJpos.le, smul_eq_mul, div_eq_inv_mul]

end GlobalTheory.SphereMeanDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HCXBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.HCTerms

variable (R : Type) [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (k : ℕ) :
    (chainsXIso R E k).inv ≫ ((chains R).map f).f (-(k : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl
  change (chainsXIso R E k).inv ≫ (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(k : ℤ)) = _
  rw [h]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem isZero_chains_X (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i : ℤ) = p at h
  omega

def termEval (F : Shv R) (n : ℤ) (k : ℕ) :
    (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)) where
  app E := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun β : Cochain ((chains R).obj E.unop) (res R F) n => (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega))
    (fun a b => by simp only [Cochain.add_v, Preadditive.comp_add]; rfl))
  naturality E E' f := by
    ext β
    revert β
    change ∀ β : Cochain ((chains R).obj E.unop) (res R F) n,
      (chainsXIso R E'.unop k).inv ≫ ((Cochain.ofHom ((chains R).map f.unop)).comp β (zero_add n)).v (-(k : ℤ)) (n - k) (by omega) =
      (free R).map (f.unop.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega)
    intro β
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_inv_map, Category.assoc]

variable {R}

def blk {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (p q : ℤ) (m : ℕ) (h1 : p = -(m : ℤ)) (h2 : n - m = q) : ((chains R).obj E).X p ⟶ (res R F).X q :=
  (((chains R).obj E).XIsoOfEq h1).hom ≫ (chainsXIso R E m).hom ≫ g m ≫ ((res R F).XIsoOfEq h2).hom

theorem blk_eq {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (k m : ℕ) (hm : m = k) (h1 : -(k : ℤ) = -(m : ℤ)) (h2 : n - m = n - k) :
    blk g (-(k : ℤ)) (n - k) m h1 h2 = (chainsXIso R E k).hom ≫ g k := by
  subst hm
  simp [blk]

def ofFam {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k)) :
    Cochain ((chains R).obj E) (res R F) n :=
  Cochain.mk fun p q hpq => if hp : p ≤ 0 then blk g p q (-p).toNat (by omega) (by omega) else 0

theorem HC_X_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ), ∃ π : ∀ k : ℕ, (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk (k)))).op ⋙ (free R).op ⋙ preadditiveYoneda.obj ((res R F).X (n - k)), ∀ E : Spcᵒᵖ, Function.Bijective (fun (x : ((HC R F).obj E).X n) (k : ℕ) => (π k).app E x) := by
  intro R _ F n
  refine ⟨termEval R F n, fun E => ⟨fun x y hxy => ?_, fun g => ?_⟩⟩
  · revert x y
    change ∀ x y : Cochain ((chains R).obj E.unop) (res R F) n, _ → x = y
    intro x y hxy
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (isZero_chains_X R E.unop p hp).eq_of_src _ _
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
      obtain rfl : q = n - k := by omega
      have h := congrFun hxy k
      change (chainsXIso R E.unop k).inv ≫ x.v (-(k : ℤ)) (n - k) _ = (chainsXIso R E.unop k).inv ≫ y.v (-(k : ℤ)) (n - k) _ at h
      exact (cancel_epi _).1 h
  · refine ⟨(ofFam (E := E.unop) g : Cochain ((chains R).obj E.unop) (res R F) n), funext fun k => ?_⟩
    change (chainsXIso R E.unop k).inv ≫ (ofFam g).v (-(k : ℤ)) (n - k) (by omega) = g k
    simp only [ofFam, Cochain.mk_v]
    rw [dite_eq_left (by omega), blk_eq g k _ (by omega)]
    erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.HCTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMulStatement
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseUnipotentVolume_conj_diagonalUnitsGL_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d e : n ⊕ Fin c → kˣ), invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) = invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) * invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  first | exact @GlobalTheory.FunObj.invVol_conj_diagGL_mul | exact GlobalTheory.FunObj.invVol_conj_diagGL_mul | (intros; apply GlobalTheory.FunObj.invVol_conj_diagGL_mul <;> assumption)
end

