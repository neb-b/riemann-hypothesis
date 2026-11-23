module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitJPolynomialBoundedDenominators
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
section
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

noncomputable section

namespace GlobalTheory.Square.AwayClosure

variable {K : Type} [Field K] [NumberField K]


open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.of_integral {m k l : ℕ} {x : K} (hx : x ≠ 0) {a b : 𝓞 K}
    (ha : x * (m : K) ^ k = a) (hb : x⁻¹ * (m : K) ^ l = b) : _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hab : ((m : K)) ^ (k + l) = (a : K) * (b : K) := by
    rw [← ha, ← hb, pow_add]
    field_simp
  refine ⟨a, k, k + l, ⟨b, RingOfIntegers.coe_injective ?_⟩, ha⟩
  simpa using hab

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.of_pow_eq_one (m : ℕ) {x : K} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) :
    _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hk.ne'] at h
  have hxi : IsIntegral ℤ x := IsIntegral.of_pow hk (h ▸ isIntegral_one)
  have hxinv : IsIntegral ℤ x⁻¹ :=
    IsIntegral.of_pow hk (by rw [inv_pow, h, inv_one]; exact isIntegral_one)
  exact _root_.GlobalTheory.Square.AwayClosure.of_integral (k := 0) (l := 0) (a := ⟨x, hxi⟩)
    (b := ⟨x⁻¹, hxinv⟩) hx (by rw [pow_zero, mul_one]; rfl) (by rw [pow_zero, mul_one]; rfl)

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.of_dvd {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) :
    _root_.GlobalTheory.Square.IsAwayUnit m (a : K) :=
  ⟨a, 0, k, h, by simp⟩

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.mul {m : ℕ} {x y : K} (hx : _root_.GlobalTheory.Square.IsAwayUnit m x)
    (hy : _root_.GlobalTheory.Square.IsAwayUnit m y) : _root_.GlobalTheory.Square.IsAwayUnit m (x * y) :=
  by
    obtain ⟨a, k, j, ha, hx⟩ := hx
    obtain ⟨b, l, i, hb, hy⟩ := hy
    refine ⟨a * b, k + l, j + i, by rw [pow_add]; exact mul_dvd_mul ha hb, ?_⟩
    calc
      x * y * (m : K) ^ (k + l) = (x * (m : K) ^ k) * (y * (m : K) ^ l) := by rw [pow_add]; ring
      _ = ((a * b : 𝓞 K) : K) := by rw [hx, hy]; push_cast; rfl

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.inv {m : ℕ} (hm : 0 < m) {x : K} (hx : _root_.GlobalTheory.Square.IsAwayUnit m x) :
    _root_.GlobalTheory.Square.IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨c, hc⟩, hxa⟩ := hx
  have hcK : (m : K) ^ k' = (a : K) * (c : K) := by
    have := congrArg (fun t : 𝓞 K => (t : K)) hc
    simpa using this
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hxa
    rw [← hxa, zero_mul] at hcK
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne') hcK
  refine ⟨(m : 𝓞 K) ^ k * c, k', k + k', ⟨a, by rw [pow_add, hc]; ring⟩, ?_⟩
  push_cast
  rw [hcK, ← hxa]
  field_simp

end GlobalTheory.Square.AwayClosure

namespace GlobalTheory.Square

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma valuation_coe_integer_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (r : K) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (r : K))) := by
  have hspan : Ideal.span {r} ≠ 0 := by simpa using hr
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hr, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v hspan]

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma valuation_eq_exp_neg_count_spanSingleton_foundation (v : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) :
    v.valuation K y =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by simpa using hs0
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hy
  have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K s) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hsK]
  have hcount := congrArg (FractionalIdeal.count K v) hmul
  rw [FractionalIdeal.count_mul K v (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
    (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])] at hcount
  have hr' := valuation_coe_integer_eq_exp_neg_count v hr0
  have hs' := valuation_coe_integer_eq_exp_neg_count v hs0
  simp only [show ∀ t : 𝓞 K, (t : K) = algebraMap (𝓞 K) K t from fun _ => rfl] at hr' hs'
  rw [map_div₀, hr', hs', div_eq_iff (by simp), ← WithZero.exp_add, ← hcount]
  congr 1
  ring

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_integer_eq_of_count_nonneg {y : K} (hy : y ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
    ∃ b : 𝓞 K, y = b := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K y fun v => by
    rw [valuation_eq_exp_neg_count_spanSingleton_foundation v hy, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith [h v]
  exact ⟨b, hb.symm⟩

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_mul_pow_integer_of_count_eq_zero_coprime {m : ℕ} (hm : 0 < m) {y : K} (hy : y ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) = 0) :
    ∃ n : ℕ, ∃ b : 𝓞 K, y * (m : K) ^ n = b := by
  set I := FractionalIdeal.spanSingleton (𝓞 K)⁰ y with hIdef
  have hI : I ≠ 0 := by rwa [Ne, hIdef, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hfin : {w | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  set n := ∑ w ∈ hfin.toFinset, (FractionalIdeal.count K w I).natAbs
  have hbound : ∀ w, -(n : ℤ) ≤ FractionalIdeal.count K w I := by
    intro w
    by_cases hw : FractionalIdeal.count K w I = 0
    · rw [hw]
      simp
    · have hmem : w ∈ hfin.toFinset := by simpa using hw
      have hle : (FractionalIdeal.count K w I).natAbs ≤ n :=
        Finset.single_le_sum (f := fun w => (FractionalIdeal.count K w I).natAbs)
          (fun _ _ => Nat.zero_le _) hmem
      omega
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hm0 : (m : 𝓞 K) ≠ 0 := fun h0 => hmK (by simpa using congrArg (fun t : 𝓞 K => (t : K)) h0)
  have hmalg : (m : K) = algebraMap (𝓞 K) K (m : 𝓞 K) := by simp
  obtain ⟨b, hb⟩ := exists_integer_eq_of_count_nonneg (y := y * (m : K) ^ n)
    (mul_ne_zero hy (pow_ne_zero _ hmK)) fun w => by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow,
        FractionalIdeal.count_mul K w hI
          (pow_ne_zero _ (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])),
        FractionalIdeal.count_pow]
      have hc0 : 0 ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)) := by
        rw [hmalg, ← FractionalIdeal.coeIdeal_span_singleton]
        exact FractionalIdeal.count_coe_nonneg K w _
      by_cases hw : (m : 𝓞 K) ∈ w.asIdeal
      · have h1 : 1 ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)) := by
          rw [hmalg]
          exact _root_.Formalism.DivisionValues.idxChange_cnt_mem w hm0 hw
        nlinarith [hbound w]
      · rw [h w hw]
        positivity
  exact ⟨n, b, hb⟩


open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.isAwayUnit_closure : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K] (m : ℕ), 0 < m →
    (∀ (x : K) (k : ℕ), 0 < k → x ^ k = 1 → _root_.GlobalTheory.Square.IsAwayUnit m x) ∧
    (∀ (a : 𝓞 K) (k : ℕ), a ∣ (m : 𝓞 K) ^ k → _root_.GlobalTheory.Square.IsAwayUnit m (a : K)) ∧
    (∀ x y : K, _root_.GlobalTheory.Square.IsAwayUnit m x → _root_.GlobalTheory.Square.IsAwayUnit m y →
      _root_.GlobalTheory.Square.IsAwayUnit m (x * y)) ∧
    (∀ x : K, _root_.GlobalTheory.Square.IsAwayUnit m x → _root_.GlobalTheory.Square.IsAwayUnit m x⁻¹) ∧
    (∀ x : K, x ≠ 0 → (∀ w : _root_.Formalism.PairingDivisionLocalBalance.Pl K, (m : 𝓞 K) ∉ w.asIdeal → _root_.Formalism.DivisionValues.vw w x = 0) →
      _root_.GlobalTheory.Square.IsAwayUnit m x) := by
  intro K _ _ _ m hm
  refine ⟨fun x k hk h => _root_.GlobalTheory.Square.AwayClosure.of_pow_eq_one m hk h,
    fun a k h => _root_.GlobalTheory.Square.AwayClosure.of_dvd h,
    fun x y hx hy => _root_.GlobalTheory.Square.AwayClosure.mul hx hy,
    fun x hx => _root_.GlobalTheory.Square.AwayClosure.inv hm hx, fun x hx hv => ?_⟩
  have hI : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 0 :=
    fun w hw => hv w hw
  have hI' : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹) = 0 := by
    intro w hw
    rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, hI w hw, neg_zero]
  obtain ⟨k, a, ha⟩ := exists_mul_pow_integer_of_count_eq_zero_coprime hm hx hI
  obtain ⟨l, b, hb⟩ := exists_mul_pow_integer_of_count_eq_zero_coprime hm (inv_ne_zero hx) hI'
  exact _root_.GlobalTheory.Square.AwayClosure.of_integral hx ha hb

end GlobalTheory.Square
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOne
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.FracPrim

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Bd (X : Tower Ω ε) (x : X.K) : Prop :=
  ∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp x).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
    IsIntegral ℤ ((D : Ω) * (X.exp x).coeff r)

theorem bd_one (X : Tower Ω ε) : Bd X 1 := by
  refine ⟨∅, 1, one_pos, fun r => ?_⟩
  rw [map_one, HahnSeries.coeff_one]
  split_ifs
  · exact ⟨one_mem _, by simpa using isIntegral_one⟩
  · exact ⟨zero_mem _, by simpa using isIntegral_zero⟩

theorem bd_mul (X : Tower Ω ε) {x y : X.K} (hx : Bd X x) (hy : Bd X y) : Bd X (x * y) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hx
  obtain ⟨S', D', hD', h'⟩ := hy
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ?_⟩
  have hS : IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left)
  have hS' : IntermediateField.adjoin ℚ (S' : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right)
  rw [map_mul, HahnSeries.coeff_mul]
  refine ⟨sum_mem (fun ij _ => mul_mem (hS (h ij.1).1) (hS' (h' ij.2).1)), ?_⟩
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ (fun ij _ => ?_)
  have := (h ij.1).2.mul (h' ij.2).2
  convert this using 1
  push_cast; ring

theorem bd_prod (X : Tower Ω ε) {ι : Type} (s : Finset ι) (t : ι → X.K) (h : ∀ i ∈ s, Bd X (t i)) :
    Bd X (∏ i ∈ s, t i) :=
  Finset.prod_induction t (Bd X) (fun _ _ => bd_mul X) (bd_one X) h

end GlobalTheory.FracPrim

namespace GlobalTheory

open GlobalTheory.FracPrim

theorem exists_prim_frac_level_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ f : X.K, f ≠ 0 → ∃ (a b : X.K) (κ : Ω) (S : Finset Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧ (∀ γ : SL(2, ℤ), X.sl (ofSL γ) b = b) ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ (X.exp b).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X hj l _ A hl f hf
  classical
  obtain ⟨M, hM, hfM⟩ := X.level f
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    simp [Nat.add_mod]
  have hcM : 6 * M + 1 ≡ 1 [MOD M] :=
    ((Nat.modEq_iff_dvd' (by omega)).mpr (by simp)).symm
  have hfG := _root_.GlobalTheory.KZ.FracGen.fracGen ε X hj M (6 * M + 1) hM hc1 hc6 hcM f hfM
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := IntermediateField.mem_adjoin_iff_div.mp hfG
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hf (by simpa using hPQ)
  have hfQ : f * Q = P := by rw [hPQ, div_mul_cancel₀ _ hQ0]
  obtain ⟨M', hM', hQM'⟩ := X.level Q
  haveI : NeZero M' := ⟨hM'.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M').Normal := CongruenceSubgroup.Gamma_normal M'
  haveI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M') := Fintype.ofFinite _
  have tq : ∀ g g' : SL(2, ℤ), g⁻¹ * g' ∈ CongruenceSubgroup.Gamma M' → X.sl (ofSL g') Q = X.sl (ofSL g) Q := by
    intro g g' h
    have hc : g * (g⁻¹ * g') * g⁻¹ ∈ CongruenceSubgroup.Gamma M' :=
      (CongruenceSubgroup.Gamma_normal M').conj_mem _ h g
    have e : g' = (g * (g⁻¹ * g') * g⁻¹) * g := by group
    rw [e, map_mul, X.sl_mul, hQM' _ hc]
  set t : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M' → X.K := fun q => X.sl (ofSL q.out) Q with ht
  set b0 : X.K := ∏ q, t q with hb0def
  have hb0 : ∀ δ : SL(2, ℤ), X.sl (ofSL δ) b0 = b0 := by
    intro δ
    rw [hb0def, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M')) _ _ (fun q => ?_)
    simp only [ht, Equiv.coe_mulRight]
    rw [← X.sl_mul, ← map_mul]
    symm
    apply tq
    rw [← QuotientGroup.eq]
    simp
  have ht1 : t 1 = Q := by
    simp only [ht]
    rw [tq 1 _ (by rw [← QuotientGroup.eq]; simp), map_one, X.sl_one]
  have hbd : ∀ γ : SL(2, ℤ), Bd X (X.sl (ofSL γ) Q) := fun γ =>
    _root_.GlobalTheory.FracBd.frac_bd ε X M (6 * M + 1) hM hc1 hc6 hcM Q hQ γ
  have hPbd : Bd X P := by
    have := _root_.GlobalTheory.FracBd.frac_bd ε X M (6 * M + 1) hM hc1 hc6 hcM P hP 1
    rwa [map_one, X.sl_one] at this
  set R : X.K := ∏ q ∈ Finset.univ.erase 1, t q with hR
  have hbR : b0 = R * Q := by
    rw [hb0def, hR, ← ht1, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have ha0 : f * b0 = P * R := by rw [hbR, ← hfQ]; ring
  have hb0bd : Bd X b0 := bd_prod X _ _ (fun q _ => hbd _)
  have ha0bd : Bd X (f * b0) := by
    rw [ha0]; exact bd_mul X hPbd (bd_prod X _ _ (fun q _ => hbd _))
  have hb0ne : b0 ≠ 0 := by
    rw [hb0def]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => (map_ne_zero _).mpr hQ0)
  have ha0ne : f * b0 ≠ 0 := mul_ne_zero hf hb0ne
  obtain ⟨κa, hκa, hPa, Sa, hSa⟩ := _root_.GlobalTheory.PrimConst.prim_of_bounded ε X hj l A hl (f * b0) ha0ne ha0bd
  obtain ⟨κb, hκb, hPb, Sb, hSb⟩ := _root_.GlobalTheory.PrimConst.prim_of_bounded ε X hj l A hl b0 hb0ne hb0bd
  refine ⟨algebraMap Ω X.K κa * (f * b0), algebraMap Ω X.K κb * b0, κb / κa, Sa ∪ Sb, div_ne_zero hκb hκa, ?_, hPa, hPb,
    ?_, fun r => ⟨?_, ?_⟩⟩
  · have e : algebraMap Ω X.K (κb / κa) * algebraMap Ω X.K κa = algebraMap Ω X.K κb := by
      rw [← map_mul, div_mul_cancel₀ _ hκa]
    rw [← mul_assoc (algebraMap Ω X.K (κb / κa)), e]; ring
  · intro γ
    rw [map_mul, AlgEquiv.commutes, hb0]
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left) (hSa r)
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right) (hSb r)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRatios
section
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square.Ratio

open Formalism.DivisionValues.ValuationRepresentative (vw_mul vw_inv)

theorem away {K : Type} [Field K] [NumberField K] [StarRing K] {w : Pl K} {Qn : ℕ}
    (hQ : (Qn : 𝓞 K) ∉ w.asIdeal) {x : K} (h : IsAwayUnit Qn x) : x ≠ 0 ∧ vw w x = 0 := by
  obtain ⟨a, k, k', hd, hx⟩ := h
  have hQk : ∀ k, (Qn : 𝓞 K) ^ k ∉ w.asIdeal := fun k h => hQ (w.isPrime.mem_of_pow_mem k h)
  have ha : a ∉ w.asIdeal := fun h => hQk k' (Ideal.mem_of_dvd _ hd h)
  have ha0 : (a : K) ≠ 0 := by
    intro h; apply ha
    have : a = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  rw [← hx] at ha0
  have h1 := Formalism.DivisionValues.ReductionFirst.vw_unit w a ha
  have h2 := Formalism.DivisionValues.ReductionFirst.vw_unit w _ (hQk k)
  have e : (((Qn : 𝓞 K) ^ k : 𝓞 K) : K) = (Qn : K) ^ k := by simp
  rw [e] at h2
  rw [← hx, vw_mul w _ _ (left_ne_zero_of_mul ha0) (right_ne_zero_of_mul ha0), h2] at h1
  exact ⟨left_ne_zero_of_mul ha0, by simpa using h1⟩

theorem exists_ratios : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ), (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (e0 h : ℕ), e0 ≤ h → ∀ (L0 L1 : ℤ → ℂ) (zT zTd zψ Ep : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ) (er : ℝ), (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → L0 s ≠ 0 ∧ L1 s ≠ 0) → (∀ s : ℤ, 1 ≤ s → s ≤ h → zT s ≠ 0 ∧ zTd s ≠ 0 ∧ σ₀ (zψ s) * L0 s = σ₀ (zT s) * L1 s ∧ -(n0 s) ≤ ((vw w (zψ s) + gT s : ℤ) : ℝ) ∧ (vw w (zψ s) : ℝ) ≤ (vw w (zTd s) : ℝ) + er) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → IsAwayUnit Qn (Ep s) ∧ L1 s * L0 (1 - s) = σ₀ (Ep s) * (L1 (1 - s) * L0 s)) → ∃ ρ : ℤ → K, (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → ρ s ≠ 0 ∧ σ₀ (ρ s) * L0 s = L1 s) ∧ (∀ s : ℤ, 1 ≤ s → s ≤ h → (vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + |((vw w (zTd s) + gT s : ℤ) : ℝ)| + er ∧ -(vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + n0 s) ∧ (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) := by
  intro K _ _ _ σ₀ w Qn hQ e0 h he L0 L1 zT zTd zψ Ep gT n0 er hL hpos hneg
  have he' : (e0 : ℤ) ≤ h := by exact_mod_cast he
  have key : ∀ s : ℤ, 1 ≤ s → s ≤ h → zψ s ≠ 0 ∧ zψ s / zT s ≠ 0 ∧
      σ₀ (zψ s / zT s) * L0 s = L1 s := by
    intro s h1 h2
    obtain ⟨hT, -, hrel, -, -⟩ := hpos s h1 h2
    obtain ⟨-, hL1⟩ := hL s (by omega) h2
    have hT' : σ₀ (zT s) ≠ 0 := (map_ne_zero σ₀).2 hT
    have hψ : zψ s ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact mul_ne_zero hT' hL1 hrel.symm
    refine ⟨hψ, div_ne_zero hψ hT, ?_⟩
    rw [map_div₀]
    field_simp
    linear_combination hrel
  refine ⟨fun s => if 1 ≤ s then zψ s / zT s else Ep s * (zψ (1 - s) / zT (1 - s)), ?_, ?_, ?_⟩
  · intro s h1 h2
    by_cases hs : 1 ≤ s
    · simp only [hs, if_true]
      exact (key s hs h2).2
    · simp only [hs, if_false]
      obtain ⟨hu, hrel⟩ := hneg s h1 (by omega)
      obtain ⟨-, hne, hk⟩ := key (1 - s) (by omega) (by omega)
      refine ⟨mul_ne_zero (away hQ hu).1 hne, ?_⟩
      have hL0 := (hL (1 - s) (by omega) (by omega)).1
      apply mul_right_cancel₀ hL0
      rw [hrel, map_mul, ← hk]
      ring
  · intro s h1 h2
    simp only [h1, if_true]
    obtain ⟨hT, -, -, hb1, hb2⟩ := hpos s h1 h2
    have hψ := (key s h1 h2).1
    have hv : vw w (zψ s / zT s) = vw w (zψ s) - vw w (zT s) := by
      rw [div_eq_mul_inv, vw_mul w _ _ hψ (inv_ne_zero hT), vw_inv]; ring
    rw [hv]
    have a1 := le_abs_self ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a2 := neg_abs_le ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a3 := le_abs_self ((vw w (zTd s) + gT s : ℤ) : ℝ)
    generalize |((vw w (zT s) + gT s : ℤ) : ℝ)| = A at *
    generalize |((vw w (zTd s) + gT s : ℤ) : ℝ)| = B at *
    push_cast at *
    constructor <;> linarith
  · intro s h1 h2
    have hs : ¬ 1 ≤ s := by omega
    have hs' : 1 ≤ 1 - s := by omega
    simp only [hs, hs', if_true, if_false]
    obtain ⟨hu, -⟩ := hneg s h1 h2
    obtain ⟨hE, hv⟩ := away hQ hu
    rw [vw_mul w _ _ hE (key (1 - s) hs' (by omega)).2.1, hv, zero_add]

end GlobalTheory.Square.Ratio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumDosetIndSmul
section
namespace GlobalTheory.DoubleCosetIndicatorSum

theorem mul_mem_doubleCoset {G : Type} [Group G] {K : Subgroup G} {a g k : G}
    (hg : g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G) := by
  obtain ⟨h, hh, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  exact DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k' * k, K.mul_mem hk' hk, mul_assoc _ _ _⟩

private theorem dosetInd_smul_eq_sum_filter {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {x : V} (hx : x ∈ GlobalTheory.PRep.fixed ρ K) {a : G} {R : Finset G}
    (hR : ∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G))
    (hU : ∀ g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K)
    [DecidableEq (G ⧸ K)] (c : G ⧸ K) :
    Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x =
      ∑ γ ∈ R.filter (fun γ : G => (γ : G ⧸ K) = c), ρ γ x := by
  have hfix : ∀ k ∈ K, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 hx

  have hmk : ∀ γ : G, ((γ : G ⧸ K) = c ↔ γ⁻¹ * Quotient.out c ∈ K) := by
    intro γ
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  by_cases hc : Quotient.out c ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)
  ·
    rw [Formalism.UG.P.dosetInd_of_mem ℂ K a _ hc, one_smul]
    obtain ⟨γ₀, ⟨hγ₀R, hγ₀K⟩, huniq⟩ := hU _ hc
    have hfil : R.filter (fun γ : G => (γ : G ⧸ K) = c) = {γ₀} := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_singleton, hmk]
      constructor
      · rintro ⟨hγR, hγK⟩
        exact huniq γ ⟨hγR, hγK⟩
      · rintro rfl
        exact ⟨hγ₀R, hγ₀K⟩
    rw [hfil, Finset.sum_singleton]
    calc ρ (Quotient.out c) x = ρ (γ₀ * (γ₀⁻¹ * Quotient.out c)) x := by rw [mul_inv_cancel_left]
      _ = ρ γ₀ (ρ (γ₀⁻¹ * Quotient.out c) x) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ γ₀ x := by rw [hfix _ hγ₀K]
  ·
    rw [Formalism.UG.P.dosetInd_of_not_mem ℂ K a _ hc, zero_smul]
    refine (Finset.sum_eq_zero fun γ hγ => ?_).symm
    rw [Finset.mem_filter, hmk] at hγ
    refine absurd ?_ hc
    have h := mul_mem_doubleCoset (hR γ hγ.1) hγ.2
    rwa [mul_inv_cancel_left] at h

theorem main : (let d1 : {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : Module ℂ V] → Representation ℂ G V → Subgroup G → (G → ℂ) → V → V := @(fun {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (x : V) ↦ ∑ᶠ (c : G ⧸ K), h (Quotient.out c) • ((ρ : G → V →ₗ[ℂ] V) (Quotient.out c) : V → V) x); ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}, x ∈ GlobalTheory.PRep.fixed ρ K → ∀ {a : G} {R : Finset G}, (∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G)) → (∀ g ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K) → d1 ρ K (Formalism.UG.dosetInd ℂ K a) x = ∑ γ ∈ R, ((ρ : G → V →ₗ[ℂ] V) γ : V → V) x) := by
  intro d1 G V _ _ _ ρ K x hx a R hR hU
  classical
  show ∑ᶠ c : G ⧸ K, Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x = ∑ γ ∈ R, ρ γ x
  rw [finsum_congr (dosetInd_smul_eq_sum_filter hx hR hU)]
  rw [finsum_eq_sum_of_support_subset (s := R.image fun γ : G => (γ : G ⧸ K))]
  · exact Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem _ hγ) _
  · intro c hc
    obtain ⟨γ, hγ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Function.mem_support.1 hc)
    rw [Finset.mem_filter] at hγ
    exact Finset.mem_image.2 ⟨γ, hγ.1, hγ.2⟩

end GlobalTheory.DoubleCosetIndicatorSum
end

