module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import GroundTheory.AutomorphicForms.Bundle0019
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsRatMulIdeleFinitePartMemCompactOfLeNorm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm :
    ∀ c : ℝ, 0 < c → ∃ (S : Set (A ℚ)ˣ) (Bu : ℝ), IsCompact S ∧ 1 ≤ Bu ∧ ∀ a : (A ℚ)ˣ, c ≤ ab a →
        ∃ (q : ℚ) (a' u : (A ℚ)ˣ), q ≠ 0 ∧ (a' : A ℚ) = rt q * (a : A ℚ) ∧ u ∈ S ∧ (a' : A ℚ).2 = (u : A ℚ).2 ∧
          ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 ∧ Bu⁻¹ ≤ |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ∧
          |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ≤ Bu * (ab a / c) := by
  intro c hc
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := ℚ) hc c
  have hv : Continuous fun u : IdeleGroup ℚ => ((u : IdeleGroup ℚ) : A ℚ) := Units.continuous_val
  have hi : Continuous fun u : IdeleGroup ℚ => (((u⁻¹ : IdeleGroup ℚ)) : A ℚ) := Units.continuous_coe_inv
  have hcont : Continuous fun u : IdeleGroup ℚ => ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ +
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ :=
    (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hv))).add
      (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hi)))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  set b := max M 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hb0 : 0 < b := one_pos.trans_le hb1
  refine ⟨S, b, hS, hb1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  set s := ab a / c with hsdef
  have hs0 : 0 < s := one_pos.trans_le hx
  set p : IdeleGroup ℚ := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) =
        ((IdeleGroup.ideleModule ℚ p : ℝ))⁻¹ * (IdeleGroup.ideleModule ℚ a : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab a := hc.trans_le ha
    rw [h1, hp, ideleModule_posIdele, Module.finrank_self, pow_one]
    change (ab a / c)⁻¹ * ab a = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal ℚ t * (p⁻¹ * a) with hu
  have hau : IdeleGroup.diagonal ℚ t * a = p * u := by
    rw [hu, mul_left_comm, mul_inv_cancel_left]
  have hp2 : (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite s hs0 v
  have hpi2 : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    have e : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 :=
      congrArg Prod.snd (Units.inv_mul p)
    rwa [hp2, mul_one] at e
  have hre : |UpperTheory.ConvolutionTheory.RankTwoDescent.re (((p * u : IdeleGroup ℚ)) : A ℚ)| = s * ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := by
    rw [abs_re]
    have e1 : (((p * u : IdeleGroup ℚ)) : A ℚ).1 Rat.infinitePlace =
        ((p : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace := by
      simp only [Units.val_mul]
      rfl
    rw [e1, norm_mul, hp, norm_posIdele_infinite]
  have hbd := hM u ht
  have hn1 : 0 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ := norm_nonneg _
  rw [Real.norm_of_nonneg (by positivity)] at hbd
  have hMb : M ≤ b := le_max_left _ _
  have hprod : ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ *
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ = 1 := by
    rw [← norm_mul]
    have e : ((u : IdeleGroup ℚ) : A ℚ).1 * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 = 1 :=
      congrArg Prod.fst (Units.mul_inv u)
    have e' := congrFun e Rat.infinitePlace
    change ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace = 1 at e'
    rw [e', norm_one]
  refine ⟨(t : ℚ), p * u, u, t.ne_zero, ?_, ht, ?_, ?_, ?_, ?_⟩
  · have h1 : ((IdeleGroup.diagonal ℚ t : IdeleGroup ℚ) : A ℚ) = rt (t : ℚ) := IdeleGroup.coe_diagonal _ _
    rw [← hau, Units.val_mul, h1]
  · change (((p * u : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [Units.val_mul]
    change (((p : IdeleGroup ℚ) : A ℚ)).2 * _ = _
    rw [hp2, one_mul]
  · change ((((p * u)⁻¹ : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [_root_.mul_inv_rev, Units.val_mul]
    change _ * (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = _
    rw [hpi2, mul_one]
  · rw [hre, inv_le_iff_one_le_mul₀ hb0]
    have h1 : 1 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ * b := by
      rw [← hprod]
      exact mul_le_mul_of_nonneg_left (by linarith) hn1
    nlinarith
  · rw [hre, mul_comm b]
    exact mul_le_mul_of_nonneg_left (by linarith) hs0.le
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FalseOfLandauNonnegEulerFactorsEntire
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

private lemma conv_prime_pow (a a' : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.convolution a a' (p ^ k) =
      PowerSeries.coeff k (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k))) := by
  rw [LSeries.convolution_def, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => a x * a' y), Nat.divisors_prime_pow hp, Finset.sum_map,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a (p ^ i) * a' (p ^ j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp [Nat.pow_div hik hp.pos]

private lemma toAF_mult (a : ℕ → ℂ) (h1 : a 1 = 1)
    (hm : ∀ m n, m.Coprime n → a (m * n) = a m * a n) :
    (toArithmeticFunction a).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm0 hn0 hmn => ?_⟩
  · simp [toArithmeticFunction, h1]
  · simp [toArithmeticFunction, hm0, hn0, hm m n hmn]

private lemma conv_nonneg_of_pp (b : ArithmeticFunction ℂ) (hb : b.IsMultiplicative)
    (hpp : ∀ p k : ℕ, p.Prime → 0 ≤ b (p ^ k)) (n : ℕ) : 0 ≤ b n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [hb.multiplicative_factorization _ hn]
  exact Finset.prod_nonneg fun p hp => hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))

theorem UpperTheory.false_of_landau_nonneg_euler_factors_entire :
    ∀ (a a' : ℕ → ℂ) (N : ℕ), 0 < N → a 1 = 1 → a' 1 = 1 → (∀ m n, m.Coprime n → a (m * n) = a m * a n) →
        (∀ m n, m.Coprime n → a' (m * n) = a' m * a' n) → (∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0) →
        (∀ p k : ℕ, p.Prime → p ∣ N → a' (p ^ (k + 1)) = 0) →
        (∀ p : ℕ, p.Prime → ¬ p ∣ N →
          (∀ k, 0 ≤ PowerSeries.coeff k (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k)))) ∧
          1 ≤ PowerSeries.coeff 4 (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k)))) →
        (∀ s : ℂ, 4 < s.re → LSeriesSummable a s) → (∀ s : ℂ, 4 < s.re → LSeriesSummable a' s) → Entire a → Entire a' → Landau → False := by
  intro a a' N hN h1 h1' hm hm' hbad hbad' hgood hs hs' hE hE' hL
  have hmul : (toArithmeticFunction a * toArithmeticFunction a').IsMultiplicative :=
    (toAF_mult a h1 hm).mul (toAF_mult a' h1' hm')
  have hcoe : ∀ n, LSeries.convolution a a' n = (toArithmeticFunction a * toArithmeticFunction a') n :=
    fun n => rfl
  have hone : LSeries.convolution a a' 1 = 1 := by rw [hcoe, hmul.map_one]
  have hpp : ∀ p k : ℕ, p.Prime → 0 ≤ LSeries.convolution a a' (p ^ k) := by
    intro p k hp
    by_cases hpN : p ∣ N
    · rcases k with _ | k
      · simp [hone]
      · have hz : LSeries.convolution a a' (p ^ (k + 1)) = 0 := by
          rw [conv_prime_pow a a' hp, PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun x hx => ?_
          obtain ⟨i, j⟩ := x
          have hij : i + j = k + 1 := by simpa using hx
          rcases i with _ | i
          · have hj : j = k + 1 := by omega
            subst hj
            simp [hbad' p k hp hpN]
          · simp [hbad p i hp hpN]
        exact hz.ge
    · rw [conv_prime_pow a a' hp]
      exact (hgood p hp hpN).1 k
  have hnn : ∀ n, 0 ≤ LSeries.convolution a a' n :=
    conv_nonneg_of_pp _ hmul hpp
  have hsum : ∀ s : ℂ, 4 < s.re → LSeriesSummable (LSeries.convolution a a') s :=
    fun s h => (hs s h).convolution (hs' s h)
  have hent : Entire (LSeries.convolution a a') := by
    obtain ⟨F, hF, hFe⟩ := hE
    obtain ⟨G, hG, hGe⟩ := hE'
    refine ⟨fun s => F s * G s, hF.mul hG, fun s h => ?_⟩
    rw [LSeries_convolution' (hs s h) (hs' s h)]
    show F s * G s = _
    rw [hFe s h, hGe s h]
  have hfin := hL _ hnn hone hsum hent
  have hfin' : ((fun p : ℕ => p ^ 4) ⁻¹' {n | 1 ≤ LSeries.convolution a a' n}).Finite :=
    hfin.preimage fun x _ y _ h => (Nat.pow_left_inj (by norm_num)).1 h
  obtain ⟨M, hM⟩ := hfin'.bddAbove
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (max M N + 1)
  have hpN : ¬ p ∣ N := fun h => by
    have := Nat.le_of_dvd hN h
    have := le_max_right M N
    omega
  have hmem : p ∈ (fun p : ℕ => p ^ 4) ⁻¹' {n | 1 ≤ LSeries.convolution a a' n} := by
    show 1 ≤ LSeries.convolution a a' (p ^ 4)
    rw [conv_prime_pow a a' hp]
    exact (hgood p hp hpN).2
  have := hM hmem
  have := le_max_left M N
  omega
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.GoodPrimeSplitOrInertOfQuadratic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

section

variable {E : Type} [Field E] [NumberField E]

private theorem norm_deg' (w : H.P E) : normV w = normV (w.under (𝓞 ℚ)) ^ w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 ℚ)).isMaximal
  simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 ℚ)).asIdeal w.asIdeal).symm

private theorem deg_le (h2 : Module.finrank ℚ E = 2) (v : H.P ℚ)
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 ℚ) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 ℚ) ℚ (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private theorem norm_sq (h2 : Module.finrank ℚ E = 2) {w : H.P E}
    (h : normV w ≠ normV (w.under (𝓞 ℚ))) : normV w = normV (w.under (𝓞 ℚ)) ^ 2 := by
  have := w.isPrime
  have hs := deg_le h2 (w.under (𝓞 ℚ)) {⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_singleton] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 ℚ)
  have h4 := norm_deg' w
  dsimp only at hs
  generalize w.asIdeal.inertiaDeg (𝓞 ℚ) = f at hs h3 h4
  interval_cases f
  · exact absurd (h4.trans (pow_one _)) h
  · exact h4

private theorem res_surj (w : H.P E) (hn : normV w = normV (w.under (𝓞 ℚ))) (x : 𝓞 E) :
    ∃ t : 𝓞 ℚ, x - algebraMap (𝓞 ℚ) (𝓞 E) t ∈ w.asIdeal := by
  have := (w.under (𝓞 ℚ)).isMaximal
  have := w.isPrime
  letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
  have : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  let φ : (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) →+* (𝓞 E ⧸ w.asIdeal) :=
    Ideal.quotientMap w.asIdeal (algebraMap (𝓞 ℚ) (𝓞 E)) le_rfl
  have hb : Function.Bijective φ := (RingHom.injective φ).bijective_of_nat_card_le hn.le
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ x)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, Ideal.Quotient.eq.1 (hc.symm.trans ?_ )⟩
  exact Ideal.quotientMap_mk

private theorem num_den (v : H.P ℚ) {δ : ℚ} (h : v.valuation ℚ δ = 1) :
    ((δ.num : ℤ) : 𝓞 ℚ) ∉ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  have hmem : ∀ a : 𝓞 ℚ, a ∈ v.asIdeal ↔ v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a) < 1 :=
    fun a => (v.valuation_lt_one_iff_mem a).symm
  have e : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.num : ℤ) : 𝓞 ℚ)) =
      v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((δ.den : ℕ) : 𝓞 ℚ)) := by
    rw [map_intCast, map_natCast, ← Rat.mul_den_eq_num δ, map_mul, h, one_mul]
  have hiff : ((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ↔ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hmem, hmem, e]
  have hc : IsCoprime ((δ.num : ℤ) : 𝓞 ℚ) ((δ.den : ℕ) : 𝓞 ℚ) := by
    have h1 : IsCoprime δ.num (δ.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact δ.reduced
    simpa using h1.map (Int.castRingHom (𝓞 ℚ))
  have hnot : ¬ (((δ.num : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ∧ ((δ.den : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) := by
    rintro ⟨h1, h3⟩
    obtain ⟨x, y, hxy⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hxy ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left x h1) (v.asIdeal.mul_mem_left y h3)))
  exact ⟨fun h1 => hnot ⟨h1, hiff.1 h1⟩, fun h3 => hnot ⟨hiff.2 h3, h3⟩⟩

private theorem val_two {K : Type} [Field K] [NumberField K] (v : H.P K) (h : Valued.v (2 : H.Kv v) = 1) :
    v.valuation K (2 : K) = 1 := by
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : K)).symm.trans ?_
  change Valued.v (algebraMap K (H.Kv v) 2) = 1
  rw [map_ofNat]
  exact h

private theorem no_ram (D : Dat ℚ E) (w : H.P E) (hG : H.Gd D.δ (w.under (𝓞 ℚ)))
    (hu : ∀ w' : H.P E, w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → w' = w)
    (hn : normV w = normV (w.under (𝓞 ℚ))) : False := by
  have hδ : (w.under (𝓞 ℚ)).valuation ℚ D.δ = 1 :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ D.δ).symm.trans hG.del
  have h2v : ((2 : ℕ) : 𝓞 ℚ) ∉ (w.under (𝓞 ℚ)).asIdeal := by
    have h := val_two _ hG.two
    have hmem : ((2 : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal ↔
        (w.under (𝓞 ℚ)).valuation ℚ (algebraMap (𝓞 ℚ) ℚ ((2 : ℕ) : 𝓞 ℚ)) < 1 :=
      ((w.under (𝓞 ℚ)).valuation_lt_one_iff_mem _).symm
    rw [hmem, map_natCast, Nat.cast_ofNat, h]
    exact lt_irrefl _
  obtain ⟨ha, hb⟩ := num_den _ hδ
  set n : ℤ := D.δ.num with hnum
  set d : ℕ := D.δ.den with hden
  have hnd : (d : E) * algebraMap ℚ E D.δ = (n : E) := by
    have := congrArg (algebraMap ℚ E) (Rat.mul_den_eq_num D.δ)
    rw [map_mul, map_natCast, map_intCast] at this
    rw [mul_comm]
    exact this
  have hsq : ((d : E) * D.θ) ^ 2 = ((d * n : ℤ) : E) := by
    rw [mul_pow, D.sq, pow_two, mul_assoc, hnd]
    push_cast
    rfl
  have hint : IsIntegral ℤ ((d : E) * D.θ) :=
    IsIntegral.of_pow two_pos (hsq ▸ isIntegral_algebraMap (R := ℤ) (x := (d * n : ℤ)))
  obtain ⟨T, hT⟩ : ∃ T : 𝓞 E, (T : E) = (d : E) * D.θ := ⟨⟨_, hint⟩, rfl⟩
  have hT2 : T ^ 2 = algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) := by
    refine RingOfIntegers.ext ?_
    simp only [map_pow, map_mul, map_natCast, map_intCast]
    rw [show (algebraMap (𝓞 E) E) T = (T : E) from rfl, hT, hsq]
    push_cast
    rfl
  let e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv D.σ.toRingEquiv
  have hcomm : ∀ a : 𝓞 ℚ, e (algebraMap (𝓞 ℚ) (𝓞 E) a) = algebraMap (𝓞 ℚ) (𝓞 E) a :=
    fun a => RingOfIntegers.ext (D.σ.commutes (a : ℚ))
  have h1 : w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective = w := by
    refine hu _ (HeightOneSpectrum.ext (Ideal.ext fun a => ?_))
    change e (algebraMap (𝓞 ℚ) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) a ∈ w.asIdeal
    rw [hcomm]
  have he : ∀ x, x ∈ w.asIdeal → e x ∈ w.asIdeal := by
    intro x hx
    have h3 : x ∈ (w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := by
      rw [h1]
      exact hx
    exact h3
  have heT : e T = -T := by
    refine RingOfIntegers.ext ?_
    change D.σ (T : E) = _
    rw [hT, map_mul, map_natCast, D.conj]
    simp [hT]
  obtain ⟨t, ht⟩ := res_surj w hn T
  have ht' := he _ ht
  rw [map_sub, heT, hcomm] at ht'
  have h2T : algebraMap (𝓞 ℚ) (𝓞 E) ((2 : ℕ) : 𝓞 ℚ) * T ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem ht ht'
    rw [map_natCast]
    convert this using 1
    push_cast
    ring
  have := w.isPrime
  rcases w.isPrime.mem_or_mem h2T with h | h
  · exact h2v h
  · have h5 : algebraMap (𝓞 ℚ) (𝓞 E) (((d : ℕ) : 𝓞 ℚ) * ((n : ℤ) : 𝓞 ℚ)) ∈ w.asIdeal := by
      rw [← hT2, pow_two]
      exact w.asIdeal.mul_mem_left _ h
    rcases (w.under (𝓞 ℚ)).isPrime.mem_or_mem (show _ ∈ (w.under (𝓞 ℚ)).asIdeal from h5) with h6 | h6
    · exact hb h6
    · exact ha h6

end

theorem UpperTheory.good_prime_split_or_inert_of_quadratic :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ), H.Gd D.δ v → (∃ w : H.P E, w.under (𝓞 ℚ) = v) ∧
        ∀ w : H.P E, w.under (𝓞 ℚ) = v → (normV w = normV v ∧ ∃ w' : H.P E, w' ≠ w ∧ w'.under (𝓞 ℚ) = v) ∨ normV w = normV v ^ 2 := by
  intro E _ _ D v hG
  have h2 : Module.finrank ℚ E = 2 := by simpa using Module.finrank_eq_card_basis D.b
  refine ⟨?_, fun w hw => ?_⟩
  · have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  · subst hw
    by_cases hn : normV w = normV (w.under (𝓞 ℚ))
    · refine Or.inl ⟨hn, ?_⟩
      by_contra hu
      push_neg at hu
      exact no_ram D w hG (fun w' h => by_contra fun hne => hu w' hne h) hn
    · exact Or.inr (norm_sq h2 hn)
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IsCompactIntegralIdeleUnitsAndAbsEqOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_iff' (t : IdeleGroup ℚ) :
    t ∈ UU ↔ IdeleGroup.toInfinite ℚ t = 1 ∧ IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ := by
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Units.ext h1, (mem_finiteIntegralUnits ℚ).2 fun v => ?_⟩
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨congrArg Units.val h1, fun v => ?_⟩
    obtain ⟨ha, hb⟩ := (mem_finiteIntegralUnits ℚ).1 h2 v
    exact eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) (by rw [mul_comm]; exact hinv v)

private lemma ofFinite_toFinite' {t : IdeleGroup ℚ} (h : IdeleGroup.toInfinite ℚ t = 1) :
    IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ t) = t := by
  refine (IdeleGroup.prodEquiv ℚ).injective (Prod.ext ?_ ?_)
  · change IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite _) = IdeleGroup.toInfinite ℚ t
    rw [IdeleGroup.toInfinite_ofFinite, h]
  · change IdeleGroup.toFinite ℚ (IdeleGroup.ofFinite _) = IdeleGroup.toFinite ℚ t
    rw [IdeleGroup.toFinite_ofFinite]

private lemma ab_ofFinite' {z : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hz : z ∈ finiteIntegralUnits ℚ) : ab (IdeleGroup.ofFinite z : IdeleGroup ℚ) = 1 := by
  have hmem : (IdeleGroup.ofFinite z : IdeleGroup ℚ) ∈ IdeleGroup.standardOpenSubgroup ℚ := hz
  have hinf : IdeleGroup.infiniteModule (IdeleGroup.ofFinite z : IdeleGroup ℚ) = 1 := by
    have e : ((IdeleGroup.ofFinite z : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
      change ((IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite z) : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = 1
      rw [IdeleGroup.toInfinite_ofFinite, Units.val_one]
    simp only [IdeleGroup.infiniteModule, e]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
  unfold ab
  rw [IdeleGroup.ideleModule_apply, hinf, IdeleGroup.finiteModule_eq_one_of_mem hmem, one_mul]

theorem UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one :
    IsCompact UU ∧ ∀ u ∈ UU, ab u = 1 := by
  have hset : (UU : Set (IdeleGroup ℚ)) =
      (fun z => (IdeleGroup.ofFinite z : IdeleGroup ℚ)) '' (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨h1, h2⟩ := (mem_UU_iff' t).1 ht
      exact ⟨_, h2, ofFinite_toFinite' h1⟩
    · rintro ⟨z, hz, rfl⟩
      refine (mem_UU_iff' _).2 ⟨IdeleGroup.toInfinite_ofFinite _, ?_⟩
      change IdeleGroup.toFinite ℚ (IdeleGroup.ofFinite z) ∈ _
      rwa [IdeleGroup.toFinite_ofFinite]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [hset]
    exact (isCompact_finiteIntegralUnits ℚ).image IdeleGroup.continuous_ofFinite
  · obtain ⟨h1, h2⟩ := (mem_UU_iff' u).1 hu
    rw [← ofFinite_toFinite' h1]
    exact ab_ofFinite' h2
end

