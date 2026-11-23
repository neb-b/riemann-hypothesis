module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumePosSimplexLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentatives

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximation
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PatternApprox

theorem exists_clear {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [CommRing Ep] [Algebra Fp Ep] [Module.Finite Fp Ep]
    (O : Subring Ep) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[Fp] x) {ι : Type} [Fintype ι] (x : ι → Ep) :
    ∃ a : Fp, a ≠ 0 ∧ ∀ i, algebraMap Fp Ep a * x i ∈ O := by
  have hfr : IsFractionRing 𝒪[Fp] Fp := (Valuation.integer.integers (valuation Fp)).isFractionRing
  have halg : ∀ i, IsAlgebraic 𝒪[Fp] (x i) := fun i =>
    (IsFractionRing.isAlgebraic_iff 𝒪[Fp] Fp Ep).mpr (Algebra.IsIntegral.isIntegral (R := Fp) (x i)).isAlgebraic
  choose y hy0 hyi using fun i => (halg i).exists_integral_multiple
  have hym : ∀ k, algebraMap Fp Ep (y k : Fp) ∈ O := fun k => by
    rw [hO, show algebraMap Fp Ep (y k : Fp) = algebraMap 𝒪[Fp] Ep (y k) from
      (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y k)).symm]
    exact isIntegral_algebraMap
  refine ⟨∏ k, (y k : Fp), ?_, fun i => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _ h
    exact hy0 k (Subtype.ext (by simpa using h))
  · have h1 : algebraMap Fp Ep (y i : Fp) * x i ∈ O := by
      rw [hO, show algebraMap Fp Ep (y i : Fp) = algebraMap 𝒪[Fp] Ep (y i) from
        (IsScalarTower.algebraMap_apply 𝒪[Fp] Fp Ep (y i)).symm, ← Algebra.smul_def]
      exact hyi i
    rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k _ => hym k) h1

variable {R : Type} [CommRing R]

theorem det_eq_one {m : ℕ} (I : Fin m → Fin m → Prop) (hI : ∀ i j, I i j → i < j)
    (s : Matrix (Fin m) (Fin m) R) (hs : ∀ i j, ¬ I i j → s i j = if i = j then 1 else 0) : s.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [hs i i (fun h => lt_irrefl i (hI i i h))]
    simp
  · intro i j hji
    rw [hs i j (fun h => lt_asymm (hI i j h) hji)]
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hji
    simp [hne]

theorem adjugate_mem {m : ℕ} (O : Subring R) (s : Matrix (Fin m) (Fin m) R) (h : ∀ i j, s i j ∈ O) :
    ∀ i j, s.adjugate i j ∈ O := by
  let S : Matrix (Fin m) (Fin m) O := fun i j => ⟨s i j, h i j⟩
  have hS : O.subtype.mapMatrix S = s := by ext i j; rfl
  intro i j
  rw [← hS, ← RingHom.map_adjugate]
  exact (S.adjugate i j).2

end GlobalTheory.HL.PatternApprox


open GlobalTheory.HL.PatternApprox in
theorem GlobalTheory.HL.pattern_strong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A m I hlt _htr c hc s hs hsint
  have hinv : ∀ p, (s p)⁻¹ = (s p).adjugate := fun p => by
    rw [Matrix.inv_def, det_eq_one I hlt (s p) (hs p), Ring.inverse_one, one_smul]
  have hcl : ∀ p, ∃ a : ((A.loc p).Fp)ˣ, (IsIntM (A.L p) (s p) → a = 1) ∧
      ∀ i j, algebraMap (A.loc p).Fp (A.loc p).Ep (a : (A.loc p).Fp) * (s p)⁻¹ i j ∈ (A.L p).O := by
    intro p
    haveI := (A.loc p).lf
    haveI : Module.Free (A.loc p).Fp (A.loc p).Ep := (A.loc p).free
    haveI : Module.Finite (A.loc p).Fp (A.loc p).Ep := Module.finite_of_finrank_eq_succ (A.loc p).rank
    by_cases h : IsIntM (A.L p) (s p)
    · refine ⟨1, fun _ => rfl, fun i j => ?_⟩
      rw [Units.val_one, map_one, one_mul, hinv p]
      exact adjugate_mem (A.L p).O (s p) h i j
    · obtain ⟨a, ha0, ha⟩ := exists_clear (A.L p).O (A.L p).O_def
        (fun ij : Fin m × Fin m => (s p)⁻¹ ij.1 ij.2)
      exact ⟨Units.mk0 a ha0, fun h' => absurd h' h, fun i j => ha (i, j)⟩
  choose c' hc'1 hc'2 using hcl
  let d : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * c' p
  have hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite := by
    apply (hc.union hsint).subset
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    obtain ⟨⟨u, hu⟩, hint⟩ := hno
    exact hp ⟨u, by simp [d, hc'1 p hint, hu]⟩
  have hap := (_root_.GlobalTheory.HL.StrongApprox.strong_approx_additive A d hd).2.1
  have hx : ∀ i j, ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - s p i j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o :=
    fun i j => hap (fun p => s p i j) (hsint.subset fun p hp hi => hp (hi i j))
  choose x hx using hx
  refine ⟨fun i j => if I i j then x i j else if i = j then 1 else 0, fun i j h => by simp [h], fun p i j => ?_⟩
  set t : Matrix (Fin m) (Fin m) E := fun i j => if I i j then x i j else if i = j then 1 else 0 with ht
  have hD : ∀ k l, ∃ o ∈ (A.L p).O, (t.map (A.loc p).ιE - s p) k l =
      algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro k l
    by_cases hkl : I k l
    · obtain ⟨o, ho, he⟩ := hx k l p
      refine ⟨o, ho, ?_⟩
      rw [← he]
      show (A.loc p).ιE (t k l) - s p k l = (A.loc p).ιE (x k l) - s p k l
      rw [ht]
      simp only [hkl, if_true]
    · refine ⟨0, (A.L p).O.zero_mem, ?_⟩
      rw [Matrix.sub_apply, Matrix.map_apply, hs p k l hkl, mul_zero]
      simp only [ht, hkl, if_false]
      split_ifs <;> simp
  choose o ho hoeq using hD
  have hunit : (s p)⁻¹ * s p = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_eq_one I hlt (s p) (hs p)]; exact isUnit_one)
  have heq : (s p)⁻¹ * t.map (A.loc p).ιE - 1 = (s p)⁻¹ * (t.map (A.loc p).ιE - s p) := by
    rw [Matrix.mul_sub, hunit]
  refine ⟨∑ k, (algebraMap (A.loc p).Fp (A.loc p).Ep (c' p : (A.loc p).Fp) * (s p)⁻¹ i k) * o k j,
    (A.L p).O.sum_mem fun k _ => (A.L p).O.mul_mem (hc'2 p i k) (ho k j), ?_⟩
  rw [heq, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hoeq k j]
  simp only [d, Units.val_mul, map_mul]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegulatorLeSumSmallIdealsInClass
section
open MeasureTheory NumberField Finset

namespace GlobalTheory.RegulatorClassBound

open NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem Module
open scoped nonZeroDivisors

theorem exists_mem_box (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (c : InfinitePlace K → ℝ)
    (hc : ∑ w, (w.mult : ℝ) * c w = Real.log ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|)) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ w : InfinitePlace K, w (a : K) < Real.exp (c w) := by
  classical
  set n := finrank ℚ K with hn_def
  have hn : 0 < n := finrank_pos
  have hN : 0 < (Ideal.absNorm I : ℝ) :=
    Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2
      (mem_nonZeroDivisors_of_ne_zero (by simpa using hI)))
  have hD : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  set X : ℝ := (Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)| with hX_def
  have hX : 0 < X := mul_pos hN hD
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
  let f : InfinitePlace K → NNReal := fun w => ⟨Real.exp (c w), (Real.exp_pos _).le⟩
  have hL : (minkowskiBound K J).toReal =
      (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n := by
    simp_rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
      volume_fundamentalDomain_latticeBasis, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.coe_toReal, ENNReal.toReal_ofNat, mixedEmbedding.finrank]
    rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
    simp only [J, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Real.coe_sqrt,
      coe_nnnorm, Int.norm_eq_abs]
    ring
  have hV : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hR' : (volume (convexBodyLT K f)).toReal = (convexBodyLTFactor K : ℝ) * X := by
    rw [convexBodyLT_volume, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
    congr 1
    rw [NNReal.coe_prod]
    have e : ∀ x : InfinitePlace K, ((f x ^ x.mult : NNReal) : ℝ) = Real.exp (x.mult * c x) :=
      fun x => by rw [NNReal.coe_pow, Real.exp_nat_mul]; rfl
    rw [Finset.prod_congr rfl fun x _ => e x, ← Real.exp_sum, hc, Real.exp_log hX]
  have hfin : n = 2 * nrComplexPlaces K := IsTotallyComplex.finrank K
  have hr : nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h : minkowskiBound K J < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K J).ne hV, hL, hR']
    have h1 : (convexBodyLTFactor K : ℝ) = Real.pi ^ nrComplexPlaces K := by
      simp [convexBodyLTFactor, hr]
    have h3 : (2 : ℝ) ^ nrComplexPlaces K < Real.pi ^ nrComplexPlaces K :=
      pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) (by omega)
    have h4 : (2 : ℝ)⁻¹ ^ nrComplexPlaces K * 2 ^ n = 2 ^ nrComplexPlaces K := by
      rw [hfin, pow_mul, ← mul_pow]; norm_num
    calc (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n
        = ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * 2 ^ n) * X := by rw [hX_def]; ring
      _ < (convexBodyLTFactor K : ℝ) * X := by
        rw [h4, h1]; exact mul_lt_mul_of_pos_right h3 hX
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt K J h
  rw [Units.val_mk0, FractionalIdeal.mem_coeIdeal] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  refine ⟨x, hx, fun h0 => hne (by rw [h0, map_zero]), fun w => ?_⟩
  exact hlt w

theorem sum_mult_log (K : Type) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (a : K)) =
      Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  have ha' : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha
  have h := prod_eq_abs_norm (a : K)
  have h2 : (Ideal.absNorm (Ideal.span {a}) : ℝ) = ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) := by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast; rfl
  rw [h2, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (pos_iff.2 ha').ne')]
  simp [Real.log_pow]

theorem regulator_le_sum_class : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ (C : ClassGroup (𝓞 K)) (S : Finset (Ideal (𝓞 K))), (∀ I, I ∈ S ↔ ∃ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ = C ∧ (Ideal.absNorm I : ℝ) ≤ Real.sqrt |(discr K : ℝ)|) → Units.regulator K ≤ ∑ I ∈ S, Real.log (Real.sqrt |(discr K : ℝ)| / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) := by
  intro K _ _ hK C S hS
  classical
  set Y := Real.sqrt |(discr K : ℝ)| with hY
  have hD : 0 < Y := Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  obtain ⟨⟨J, hJ⟩, hJC⟩ := ClassGroup.mk0_surjective C⁻¹
  have hJ0 : J ≠ ⊥ := nonZeroDivisors.ne_zero hJ
  have hpos : ∀ I : Ideal (𝓞 K), I ∈ (Ideal (𝓞 K))⁰ → 0 < (Ideal.absNorm I : ℝ) := fun I hI =>
    Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2 hI)
  have hgen : ∀ I : Ideal (𝓞 K), ∃ y : 𝓞 K,
      (∃ x : 𝓞 K, Ideal.span {x} = J * I) → Ideal.span {y} = J * I := by
    intro I
    by_cases h : ∃ x : 𝓞 K, Ideal.span {x} = J * I
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose y hy using hgen
  let a : Ideal (𝓞 K) → logSpace K := fun I w => (w.1.mult : ℝ) * Real.log (w.1 (y I : K))
  let A : Ideal (𝓞 K) → Set (logSpace K) := fun I =>
    {t | (∀ i, a I i ≤ t i) ∧ ∑ i, (t i - a I i) ≤ Real.log (Y / Ideal.absNorm I)}
  have hL : ∀ I ∈ S, 0 ≤ Real.log (Y / Ideal.absNorm I) := by
    intro I hI
    obtain ⟨h1, -, h2⟩ := (hS I).1 hI
    exact Real.log_nonneg ((one_le_div (hpos I h1)).2 h2)
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = Units.rank K := by
    simp [Units.rank]
  have hmeas : ∀ I, MeasurableSet (A I) := by
    intro I
    refine IsClosed.measurableSet ?_
    have h1 : IsClosed {t : logSpace K | ∀ i, a I i ≤ t i} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    exact h1.inter (isClosed_le (f := fun t : logSpace K => ∑ i, (t i - a I i))
      (by fun_prop) continuous_const)
  have hcov : ∀ t : logSpace K, ∃ I ∈ S, ∃ l ∈ unitLattice K, t + l ∈ A I := by
    intro t
    let b : InfinitePlace K → ℝ := fun w =>
      if h : w = w₀ then Real.log ((Ideal.absNorm J : ℝ) * Y) - ∑ i, t i else t ⟨w, h⟩
    have hb : ∀ i : {w : InfinitePlace K // w ≠ w₀}, b i.1 = t i := fun i => dif_neg i.2
    have hbsum : ∑ w, b w = Real.log ((Ideal.absNorm J : ℝ) * Y) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
      simp only [hb]
      simp [b]
    have hm : ∀ w : InfinitePlace K, (0 : ℝ) < w.mult := fun w => Nat.cast_pos.2 mult_pos
    have hbc : ∀ w : InfinitePlace K, (w.mult : ℝ) * (b w / w.mult) = b w := fun w =>
      mul_div_cancel₀ _ (hm w).ne'
    obtain ⟨x, hxJ, hx0, hx⟩ := exists_mem_box K J hJ0 (fun w => b w / w.mult)
      (by simp only [hbc]; exact hbsum)
    have hx0' : (x : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hx0
    have hs : ∀ w : InfinitePlace K, 0 ≤ b w - (w.mult : ℝ) * Real.log (w (x : K)) := by
      intro w
      have h1 : Real.log (w (x : K)) ≤ b w / w.mult :=
        (Real.log_le_iff_le_exp (pos_iff.2 hx0')).2 (hx w).le
      have := mul_le_mul_of_nonneg_left h1 (hm w).le
      rw [hbc] at this
      linarith
    obtain ⟨I, hI⟩ : J ∣ Ideal.span {x} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxJ)
    have hI0 : I ∈ (Ideal (𝓞 K))⁰ := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rintro rfl
      rw [mul_zero] at hI
      exact hx0 (Ideal.span_singleton_eq_bot.1 hI)
    have hsum : ∑ w : InfinitePlace K, (b w - (w.mult : ℝ) * Real.log (w (x : K))) =
        Real.log (Y / Ideal.absNorm I) := by
      rw [Finset.sum_sub_distrib, hbsum, sum_mult_log K x hx0, hI, map_mul, Nat.cast_mul,
        Real.log_mul (hpos J hJ).ne' hD.ne', Real.log_mul (hpos J hJ).ne' (hpos I hI0).ne',
        Real.log_div hD.ne' (hpos I hI0).ne']
      ring
    have hIS : I ∈ S := by
      refine (hS I).2 ⟨hI0, ?_, ?_⟩
      · have : ClassGroup.mk0 ⟨J, hJ⟩ = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹ :=
          ClassGroup.mk0_eq_mk0_inv_iff.2 ⟨x, hx0, hI.symm⟩
        rw [hJC] at this
        exact (inv_injective this).symm
      · have h0 : 0 ≤ Real.log (Y / Ideal.absNorm I) :=
          hsum ▸ Finset.sum_nonneg fun w _ => hs w
        have := (Real.log_nonneg_iff (div_pos hD (hpos I hI0))).1 h0
        exact (one_le_div (hpos I hI0)).1 this
    have hyI : Ideal.span {x} = Ideal.span {y I} := hI.trans (hy I ⟨x, hI⟩).symm
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 hyI
    have key : ∀ i : {w : InfinitePlace K // w ≠ w₀},
        (t + logEmbedding K (Additive.ofMul u)) i - a I i =
          b i.1 - (i.1.mult : ℝ) * Real.log (i.1 (x : K)) := by
      intro i
      have h1 : ((y I : 𝓞 K) : K) = (x : K) * ((u : 𝓞 K) : K) := by
        rw [← hu]; simp
      simp only [a, Pi.add_apply, logEmbedding_component, hb, h1, map_mul]
      rw [Real.log_mul (pos_iff.2 hx0').ne' (Units.pos_at_place u i.1).ne']
      ring
    refine ⟨I, hIS, logEmbedding K (Additive.ofMul u), ⟨Additive.ofMul u, trivial, rfl⟩, ?_, ?_⟩
    · intro i
      have := hs i.1
      rw [← key] at this
      linarith
    · simp only [key]
      rw [← hsum, Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)]
      linarith [hs w₀]
  have h1 := GlobalTheory.covolume_le_sum_volume_of_cover _ (unitLattice K) _ S A hmeas hcov
  have h2 : ∑ I ∈ S, volume (A I) ≤ ∑ I ∈ S, ENNReal.ofReal
      (Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)) := by
    refine Finset.sum_le_sum fun I hI => ?_
    have := GlobalTheory.SimplexVolume.volume_simplex_le _ (a I) _ (hL I hI)
    rw [hcard] at this
    exact this
  have hnn : ∀ I ∈ S, 0 ≤
      Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) :=
    fun I hI => div_nonneg (pow_nonneg (hL I hI) _) (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)).1 (h1.trans h2)

end GlobalTheory.RegulatorClassBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexEqCardMap
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LevelFamilies

theorem relIndex_eq_card_map {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M A : Submodule O V) :
    M.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A.map M.mkQ) := by
  have h := AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom
  have hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup := by
    ext x
    simp [AddMonoidHom.mem_ker]
  rw [hk] at h
  rw [h]
  rfl

theorem ncard_classes {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M B A : Submodule O V) (hMB : M ≤ B) (hBA : B ≤ A) [Finite (A.map M.mkQ)] :
    Set.ncard {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      Nat.card (A.map M.mkQ) - Nat.card (B.map M.mkQ) := by
  have hinj : Function.Injective (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) := by
    intro c c' h
    obtain ⟨v, rfl⟩ := M.mkQ_surjective c
    have : v ∈ (M.mkQ ⁻¹' {c'} : Set V) := by
      have h' : (M.mkQ ⁻¹' {M.mkQ v} : Set V) = M.mkQ ⁻¹' {c'} := h
      rw [← h']; simp
    simpa using this
  have hpre : ∀ y : V, (M.mkQ ⁻¹' {M.mkQ y} : Set V) = {x | x - y ∈ M} := by
    intro y
    ext x
    simp [Submodule.Quotient.eq]
  have hmem : ∀ y : V, M.mkQ y ∈ B.map M.mkQ ↔ y ∈ B := by
    intro y
    constructor
    · rintro ⟨b, hb, hby⟩
      have h1 : b - y ∈ M := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y = b - (b - y) := by abel
      rw [h2]
      exact B.sub_mem hb (hMB h1)
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hset : {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) ''
        ((A.map M.mkQ : Set (V ⧸ M)) \ (B.map M.mkQ : Set (V ⧸ M))) := by
    ext C
    constructor
    · rintro ⟨y, hyA, hyB, rfl⟩
      exact ⟨M.mkQ y, ⟨⟨y, hyA, rfl⟩, fun h => hyB ((hmem y).1 h)⟩, hpre y⟩
    · rintro ⟨c, ⟨⟨y, hyA, rfl⟩, hc⟩, rfl⟩
      exact ⟨y, hyA, fun h => hc ((hmem y).2 h), hpre y⟩
  have hsub : (B.map M.mkQ : Set (V ⧸ M)) ⊆ (A.map M.mkQ : Set (V ⧸ M)) :=
    Submodule.map_mono hBA
  have hfin : (A.map M.mkQ : Set (V ⧸ M)).Finite := Set.toFinite _
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_diff hsub (hfin.subset hsub)]
  rfl

theorem two_le_resQ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : 2 ≤ resQ ϖ := by
  have h : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := hϖ.maximalIdeal_eq.symm
  have h1 : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [h]
    rfl
  rw [h1]
  exact Finite.one_lt_card

theorem exists_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.TypeBe d Λ → ∃ i J i' : ℕ, 1 ≤ i ∧ (i : ℤ) ≤ S.a ∧ 1 ≤ J ∧ J ≤ r ∧ i' < i ∧ S.InFF (S.q ^ i) J (S.q ^ i - S.q ^ i') d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB
  obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, -, -, -, hlev0, hlev⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hMA : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hq : 2 ≤ S.q := two_le_resQ S.ϖ S.ϖ_irr
  have hcard : Nat.card ((S.sat Λ).map (S.M d Λ).mkQ) = S.q ^ i := by
    rw [← hbe, ← relIndex_eq_card_map]; rfl
  haveI hfin : Finite ((S.sat Λ).map (S.M d Λ).mkQ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    positivity

  let P : ℕ → Prop := fun j => ∃ y ∈ S.sat Λ, S.levC d Λ y = j
  obtain ⟨y0, hy0A, hy0M⟩ : ∃ y ∈ S.sat Λ, y ∉ S.M d Λ := by
    by_contra h
    push_neg at h
    exact hB.1 (le_antisymm hMA h)
  let J := Nat.findGreatest P r
  have hle : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := fun y hy =>
    Nat.le_findGreatest (hB.2.1 y hy) ⟨y, hy, rfl⟩
  have hPJ : P J := Nat.findGreatest_spec (hB.2.1 y0 hy0A) ⟨y0, hy0A, rfl⟩
  have hJr : J ≤ r := Nat.findGreatest_le r
  have hJ1 : 1 ≤ J := by
    have h1 : S.levC d Λ y0 ≠ 0 := fun h => hy0M ((hlev0 y0 hy0A).1 h)
    have := hle y0 hy0A
    omega

  let B : Submodule L.O S.V := S.sat Λ ⊓
    ((S.spanTo S.f (J - 1) ⊔ S.spanTo S.f' (J - 1)).restrictScalars L.O ⊔ S.M d Λ)
  have hBmem : ∀ y ∈ S.sat Λ, y ∈ B ↔ S.levC d Λ y ≤ J - 1 := by
    intro y hy
    rw [hlev y hy]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.1 h
      exact ⟨u, hu, by simpa using hm⟩
    · rintro ⟨u, hu, hm⟩
      exact ⟨hy, Submodule.mem_sup.2 ⟨u, hu, y - u, hm, by abel⟩⟩
  have hMB : S.M d Λ ≤ B := le_inf hMA le_sup_right
  have hBA : B ≤ S.sat Λ := inf_le_left
  have hle' : B.map (S.M d Λ).mkQ ≤ (S.sat Λ).map (S.M d Λ).mkQ := Submodule.map_mono hBA
  haveI hfinB : Finite (B.map (S.M d Λ).mkQ) :=
    Finite.of_injective _ (Submodule.inclusion_injective hle')
  obtain ⟨i', hi'⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ S.ϖ_irr
    (B.map (S.M d Λ).mkQ)).1
  have hi'q : Nat.card (B.map (S.M d Λ).mkQ) = S.q ^ i' := hi'
  have hn : S.nLev d Λ J = S.q ^ i - S.q ^ i' := by
    rw [← hcard, ← hi'q, ← ncard_classes _ _ _ hMB hBA]
    unfold Frames.nLev
    congr 1
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, fun h => ?_, rfl⟩
      have := (hBmem y hy).1 h
      omega
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, ?_, rfl⟩
      have h1 := hle y hy
      have h2 : ¬ S.levC d Λ y ≤ J - 1 := fun h => hl ((hBmem y hy).2 h)
      omega
  have hlt : S.q ^ i' < S.q ^ i := by
    rw [← hcard, ← hi'q]
    obtain ⟨y, hy, hl⟩ := hPJ
    have hss : (B.map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) ⊂
        ((S.sat Λ).map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) := by
      refine ⟨hle', fun h => ?_⟩
      obtain ⟨b, hb, hby⟩ := h (⟨y, hy, rfl⟩ : (S.M d Λ).mkQ y ∈ (S.sat Λ).map (S.M d Λ).mkQ)
      have h1 : b - y ∈ S.M d Λ := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y ∈ B := by
        have h3 : y = b - (b - y) := by abel
        rw [h3]
        exact B.sub_mem hb (hMB h1)
      have := (hBmem y hy).1 h2
      omega
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have hii : i' < i := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
  exact ⟨i, J, i', by omega, hia, hJ1, hJr, hii, hB, hbe, hle, hPJ, hn⟩

end GlobalTheory.HL.LevelFamilies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentativesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termLevel_zero_and_bounded_representatives : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ (S.spanTo S.f j ⊔ S.spanTo S.f' j), y - y₁ ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ m ∈ S.M d Λ, S.levC d Λ (y + m) = S.levC d Λ y) ∧ ∀ (al al' : Fin (r + 1) → E) (j : ℕ), S.lev (S.fr d Λ) (S.fr' d Λ) (∑ i, al i • S.fr d Λ i + ∑ i, al' i • S.fr' d Λ i) ≤ j ↔ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := by
  first | exact @GlobalTheory.HL.LevelRep.level_rep | exact GlobalTheory.HL.LevelRep.level_rep | (intros; apply GlobalTheory.HL.LevelRep.level_rep <;> assumption)
end

