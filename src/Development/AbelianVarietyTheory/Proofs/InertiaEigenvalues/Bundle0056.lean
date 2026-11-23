module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstOfLvlInvariant
section
noncomputable section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.LvlInv

theorem aeval_eq_zero_of_complex {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {R : Type} [CommRing R] {t : R} (ht : Polynomial.aeval t (Polynomial.cyclotomic N ℤ) = 0)
    (f : Polynomial ℤ) (hf : Polynomial.aeval ζ f = 0) : Polynomial.aeval t f = 0 := by
  have h := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hN) hf
  rw [← Polynomial.cyclotomic_eq_minpoly hζ hN] at h
  obtain ⟨q, rfl⟩ := h
  rw [map_mul, ht, zero_mul]

theorem exists_geom_int {w : ℂ} {n : ℕ} (h : w ^ n = 1) :
    ∃ c : ℤ, ∑ a ∈ Finset.range n, w ^ a = c := by
  by_cases hw : w = 1
  · exact ⟨n, by simp [hw]⟩
  · refine ⟨0, ?_⟩
    have := geom_sum_mul w n
    rw [h, sub_self] at this
    simpa using (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hw)

theorem exists_sum_int {l k : ℕ} (hl : 0 < l) {w : ℂ} (h : w ^ l ^ (k + 1) = 1) :
    ∃ c : ℤ, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), w ^ a = c := by
  obtain ⟨c, hc⟩ := exists_geom_int h
  obtain ⟨d, hd⟩ := exists_geom_int (w := w ^ l) (n := l ^ k) (by rw [← pow_mul, ← pow_succ', h])
  refine ⟨c - d, ?_⟩
  have e := Finset.sum_filter_add_sum_filter_not (Finset.range (l ^ (k + 1))) (fun a => l ∣ a)
    (fun a => w ^ a)
  have e2 : ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => l ∣ a), w ^ a =
      ∑ a ∈ Finset.range (l ^ k), (w ^ l) ^ a := by
    symm
    refine Finset.sum_bij (fun a _ => l * a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_filter] at ha ⊢
      exact ⟨by rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left ha hl, dvd_mul_right _ _⟩
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hl hab
    · intro b hb
      simp only [Finset.mem_range, Finset.mem_filter] at hb
      obtain ⟨h1, a, rfl⟩ := hb
      refine ⟨a, ?_, rfl⟩
      rw [pow_succ'] at h1
      exact Finset.mem_range.2 (Nat.lt_of_mul_lt_mul_left h1)
    · intro a _
      rw [pow_mul]
  rw [e2, hc, hd] at e
  push_cast
  linear_combination e

theorem aeval_cyc {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] (t : R) :
    Polynomial.aeval t (Polynomial.cyclotomic (l ^ (k + 1)) ℤ) =
      ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl]
  simp

theorem root_pow {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] {t : R}
    (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) {a : ℕ} (ha : ¬ l ∣ a) :
    ∑ i ∈ Finset.range l, ((t ^ a) ^ l ^ k) ^ i = 0 := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.pos _
  have hζ := Complex.isPrimitiveRoot_exp _ hN.ne'
  rw [← aeval_cyc hl] at ht ⊢
  have h := aeval_eq_zero_of_complex hN hζ ht
    ((Polynomial.cyclotomic (l ^ (k + 1)) ℤ).comp (Polynomial.X ^ a)) (by
      have h2 := hζ.pow_of_coprime a
        (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 ha).symm)
      have h3 := h2.isRoot_cyclotomic hN
      rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact h3)
  rwa [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X] at h

theorem sum_pow_int {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] {t : R}
    (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) (j : ℕ) :
    ∃ c : ℤ, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), (t ^ a) ^ j = c := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.pos _
  have hζ := Complex.isPrimitiveRoot_exp _ hN.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (l ^ (k + 1) : ℕ))
  obtain ⟨c, hc⟩ := exists_sum_int (k := k) hl.pos (w := ζ ^ j)
    (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  rw [← aeval_cyc hl] at ht
  have h := aeval_eq_zero_of_complex hN hζ ht
    (∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), (Polynomial.X ^ j) ^ a
      - (c : Polynomial ℤ)) (by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_pow, Polynomial.aeval_X, map_intCast, hc, sub_self])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_pow, Polynomial.aeval_X, map_intCast, sub_eq_zero] at h
  refine ⟨c, ?_⟩
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => by rw [← pow_mul, ← pow_mul, mul_comm]

theorem sum_aeval_const {l : ℕ} (hl : l.Prime) (k : ℕ) {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] {t : R} (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) (s : Polynomial O) :
    ∃ c : O, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a),
      Polynomial.aeval (t ^ a) s = algebraMap O R c := by
  induction s using Polynomial.induction_on' with
  | add r s hr hs =>
    obtain ⟨c, hc⟩ := hr
    obtain ⟨d, hd⟩ := hs
    exact ⟨c + d, by simp only [map_add (f := _), Finset.sum_add_distrib, hc, hd]⟩
  | monomial j x =>
    obtain ⟨c, hc⟩ := sum_pow_int hl k ht j
    refine ⟨x * c, ?_⟩
    simp only [Polynomial.aeval_monomial, ← Finset.mul_sum, hc, map_mul, map_intCast]

def lvlPoly (l : ℕ) (O : Type) [CommRing O] (k : ℕ) : Polynomial O :=
  ∑ i ∈ Finset.range l, ((1 + Polynomial.X : Polynomial O) ^ l ^ k) ^ i

theorem coe_lvlPoly (l : ℕ) (O : Type) [CommRing O] (k : ℕ) :
    ((lvlPoly l O k : Polynomial O) : O⟦X⟧) = lvl l O k := by
  unfold lvlPoly GlobalTheory.CycFr.lvl
  change Polynomial.coeToPowerSeries.ringHom _ = _
  rw [map_sum]
  simp only [map_pow, map_add (f := _), map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X]

theorem algHom_lvl (l : ℕ) {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (k : ℕ)
    (f : O⟦X⟧ →ₐ[O] R) : f (lvl l O k) = ∑ i ∈ Finset.range l, (f (1 + X) ^ l ^ k) ^ i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.CycFr.lvl, map_sum, map_pow]

theorem lvlPoly_monic {l : ℕ} (hl : l.Prime) (O : Type) [CommRing O] [Nontrivial O] (k : ℕ) :
    (lvlPoly l O k).Monic := by
  have : lvlPoly l O k =
      (Polynomial.cyclotomic (l ^ (k + 1)) O).comp (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl, lvlPoly]
    simp [Polynomial.sum_comp, add_comm]
  rw [this]
  exact (Polynomial.cyclotomic.monic _ _).comp_X_add_C _

theorem lvlPoly_map (l : ℕ) {O F : Type} [CommRing O] [CommRing F] (j : O →+* F) (k : ℕ) :
    (lvlPoly l O k).map j = lvlPoly l F k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lvlPoly, Polynomial.map_sum]

theorem lvlPoly_of_char {l : ℕ} [Fact l.Prime] {F : Type} [CommRing F] [IsDomain F]
    (h : (l : F) = 0) (k : ℕ) : lvlPoly l F k = Polynomial.X ^ (l ^ k * (l - 1)) := by
  have hl : l.Prime := Fact.out
  haveI : CharP F l := (CharP.charP_iff_prime_eq_zero hl).2 h
  have e := geom_sum_mul ((1 + Polynomial.X : Polynomial F) ^ l ^ k) l
  rw [← pow_mul, ← pow_succ] at e
  change lvlPoly l F k * _ = _ at e
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left,
    add_sub_cancel_left] at e
  apply mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)
  rw [e, ← pow_add]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
  simp [pow_succ, mul_add]

theorem lvlPoly_distinguished {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    (h : ¬ IsUnit (l : O)) (k : ℕ) :
    (lvlPoly l O k).IsDistinguishedAt (IsLocalRing.maximalIdeal O) := by
  have hm := lvlPoly_monic (l := l) Fact.out O k
  refine ⟨⟨fun {n} hn => ?_⟩, hm⟩
  have h0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact h
  have h1 := lvlPoly_map l (IsLocalRing.residue O) k
  rw [lvlPoly_of_char h0] at h1
  have h2 := hm.natDegree_map (IsLocalRing.residue O)
  rw [h1, Polynomial.natDegree_X_pow] at h2
  have h3 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h1
  rw [← h2] at hn
  simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3
  exact (IsLocalRing.residue_eq_zero_iff _).1 h3

end GlobalTheory.CycFr.LvlInv

namespace GlobalTheory.CycFr

open LvlInv

theorem exists_const_of_lvl_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    [Algebra ℤ_[l] O] (hu : ¬ IsUnit (l : O)) (k : ℕ) (b : O⟦X⟧)
    (hb : ∀ a : ℕ, ¬ l ∣ a → lvl l O k ∣ act O (a : ℤ_[l]) b - b) :
    ∃ c : O, lvl l O k ∣ b - C c := by
  have hl : l.Prime := Fact.out
  have H := lvlPoly_distinguished hu k
  set π := Ideal.Quotient.mkₐ O (Ideal.span {lvl l O k}) with hπ
  have hz : ∀ x, π x = 0 ↔ lvl l O k ∣ x := fun x => by
    rw [hπ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have ht : ∑ i ∈ Finset.range l, ((π (1 + X)) ^ l ^ k) ^ i = 0 := by
    rw [← algHom_lvl]
    exact (hz _).2 dvd_rfl
  obtain ⟨r, hr, q, hq⟩ := GlobalTheory.NB.LT.exists_poly_mod H b
  rw [coe_lvlPoly] at hq
  have hbr : b = r + lvl l O k * q := by rw [← hq]; ring
  obtain ⟨c, hc⟩ := sum_aeval_const hl k ht (r.comp (Polynomial.X - 1))
  set S := (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a) with hS
  have h1 : ∀ a ∈ S, Polynomial.aeval ((π (1 + X)) ^ a) (r.comp (Polynomial.X - 1)) = π r := by
    intro a ha
    have ha' : ¬ l ∣ a := (Finset.mem_filter.1 ha).2
    have e1 : π (act O (a : ℤ_[l]) (lvl l O k)) = 0 := by
      have := root_pow hl k ht ha'
      rw [← AlgHom.comp_apply, algHom_lvl, AlgHom.comp_apply, act_one_add_X, bin_nat, map_pow]
      exact this
    have e2 := (hz _).2 (hb a ha')
    rw [hbr] at e2
    simp only [map_sub, map_add (f := _), map_mul, e1, (hz _).2 dvd_rfl, zero_mul, add_zero,
      sub_eq_zero] at e2
    rw [← e2, GlobalTheory.NB.LT.algHom_coe, act_nat_X, ← Polynomial.aeval_algHom_apply,
      Polynomial.aeval_comp]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const] at hc
  have hn : S.card ≠ 0 := Finset.card_ne_zero.2 ⟨1, Finset.mem_filter.2
    ⟨Finset.mem_range.2 (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt), hl.not_dvd_one⟩⟩
  set p := lvlPoly l O k with hp
  have h6 : (p : O⟦X⟧) ∣
      ((Polynomial.C (S.card : O) * r - Polynomial.C c : Polynomial O) : O⟦X⟧) := by
    rw [hp, coe_lvlPoly, ← hz, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_C, map_natCast, map_sub, map_mul, map_natCast, algHom_C, ← hc, nsmul_eq_mul,
      sub_self]
  have h7 := GlobalTheory.NB.LT.poly_dvd_of_dvd H h6
  by_cases h0 : r = 0
  · exact ⟨0, q, by simpa [h0] using hq⟩
  have hpos : 0 < p.degree := (Polynomial.zero_le_degree_iff.2 h0).trans_lt hr
  have hn' : (S.card : O) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h8 : Polynomial.C (S.card : O) * r - Polynomial.C c = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h7 ?_
    refine (Polynomial.degree_sub_le _ _).trans_lt (max_lt ?_ (Polynomial.degree_C_le.trans_lt hpos))
    rwa [Polynomial.degree_C_mul hn']
  have h9 : r.degree ≤ 0 := by
    rw [← Polynomial.degree_C_mul (p := r) hn', sub_eq_zero.1 h8]
    exact Polynomial.degree_C_le
  refine ⟨r.coeff 0, q, ?_⟩
  rw [Polynomial.eq_C_of_degree_le_zero h9, Polynomial.coe_C] at hq
  exact hq

end GlobalTheory.CycFr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussPoint
section
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing

namespace GlobalTheory.GaussPoint

theorem C_dvd_iff {V : Type*} [CommRing V] (a : V) (f : PowerSeries V) :
    PowerSeries.C a ∣ f ↔ ∀ n, a ∣ PowerSeries.coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose c hc using h
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem isPrime_span_C {V : Type*} [CommRing V] {a : V} (ha : Prime a) :
    (Ideal.span {(PowerSeries.C a : PowerSeries V)}).IsPrime := by
  have h1 : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha.ne_zero).2 ha
  have h2 : Ideal.span {(PowerSeries.C a : PowerSeries V)} =
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
    ext f
    rw [Ideal.mem_span_singleton, C_dvd_iff, RingHom.mem_ker, PowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [h2]
  exact RingHom.ker_isPrime _

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem valV_irreducible {π : V} (hπ : Irreducible π) :
    valV V (algebraMap V K π) = WithZero.exp (-1 : ℤ) := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq

theorem valV_unit {u : V} (hu : IsUnit u) : valV V (algebraMap V K u) = 1 := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => h hu

theorem vV_map_eq {V' K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Field K'] [Algebra V' K'] [IsFractionRing V' K'] (f : V →+* V') (i : K →+* K')
    (hi : ∀ a, i (algebraMap V K a) = algebraMap V' K' (f a)) {π : V} (hπ : Irreducible π)
    (hπ' : Irreducible (f π)) (x : K) : vV V' (i x) = vV V x := by
  have key : ∀ a : V, valV V' (i (algebraMap V K a)) = valV V (algebraMap V K a) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [hi]
    simp only [map_mul, map_pow]
    rw [valV_unit u.isUnit, valV_unit (u.isUnit.map f), valV_irreducible hπ, valV_irreducible hπ']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  simp only [vV, map_div₀, key]

end Val

theorem exists_gaussPoint (T : CDVR) (ϖ : T.V) (hϖ : Irreducible ϖ) :
    ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧
      IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧
      (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧
      ∀ x, vV T'.V (i x) = vV T.V x := by
  let R := PowerSeries T.V
  let P : Ideal R := Ideal.span {(PowerSeries.C ϖ : PowerSeries T.V)}
  haveI hP : P.IsPrime := isPrime_span_C hϖ.prime
  let L := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L P.primeCompl_le_nonZeroDivisors
  have hm : maximalIdeal L = Ideal.span {algebraMap R L (PowerSeries.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hC0 : (PowerSeries.C ϖ : R) ≠ 0 := fun h =>
    hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))
  have hn : ¬ IsNilpotent (algebraMap R L (PowerSeries.C ϖ)) := by
    rw [IsNilpotent.map_iff hinj]
    exact fun h => hC0 h.eq_zero
  obtain ⟨_, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hm hn
  let S := AdicCompletion (maximalIdeal L) L
  let ev : R →+* S := (algebraMap L S).comp (algebraMap R L)
  have hev : Function.Injective ev :=
    (algebraMap_adicCompletion_injective_of_dvr L).comp hinj
  have hirr' : Irreducible (ev (PowerSeries.C ϖ)) :=
    irreducible_algebraMap_adicCompletion_of_dvr hirr
  have hunit : ∀ s : R, ¬ PowerSeries.C ϖ ∣ s → IsUnit (ev s) := fun s hs =>
    (IsLocalization.map_units L (⟨s, fun h => hs (Ideal.mem_span_singleton.1 h)⟩ :
      P.primeCompl)).map (algebraMap L S)
  haveI : CharZero S := charZero_of_injective_ringHom
    (f := ev.comp PowerSeries.C) (hev.comp PowerSeries.C_injective)
  let T' : CDVR := { V := S }
  let g : T.V →+* T'.Fr := (algebraMap T'.V T'.Fr).comp (ev.comp PowerSeries.C)
  have hg : Function.Injective g :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hev.comp PowerSeries.C_injective)
  have hi : ∀ a, IsFractionRing.lift (K := T.Fr) hg (algebraMap T.V T.Fr a) =
      algebraMap T'.V T'.Fr (ev (PowerSeries.C a)) := fun a => IsFractionRing.lift_algebraMap hg a
  refine ⟨T', ev, IsFractionRing.lift hg, hev, hunit _ ?_, fun s hs => ?_, hi,
    vV_map_eq (ev.comp PowerSeries.C) _ hi hϖ hirr'⟩
  · rw [C_dvd_iff]
    intro h
    have h1 := h 1
    rw [PowerSeries.coeff_one_X] at h1
    exact hϖ.not_isUnit (isUnit_of_dvd_one h1)
  · by_contra h
    exact hirr'.not_isUnit (isUnit_of_dvd_unit hs (hunit s h))

end GlobalTheory.GaussPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralPowerSeriesDivisionApprox
section
namespace GlobalTheory.BK.DivApprox

open PowerSeries GlobalTheory.BK

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_mul_le' {f g : K⟦X⟧} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ ≤ a) (hg : ∀ n, ‖coeff n g‖ ≤ b) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ a * b := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    ha hb (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

omit [IsUltrametricDist K] in
theorem eq_low_add_high (f : K⟦X⟧) (n₀ : ℕ) :
    f = (PowerSeries.mk fun n => if n < n₀ then coeff n f else 0) +
      X ^ n₀ * PowerSeries.mk fun n => coeff (n + n₀) f := by
  ext n
  rw [map_add (f := _), coeff_mk, coeff_X_pow_mul', coeff_mk]
  by_cases h : n < n₀
  · rw [if_pos h, if_neg (not_le.2 h), add_zero]
  · rw [if_neg h, if_pos (not_lt.1 h), zero_add, Nat.sub_add_cancel (not_lt.1 h)]

theorem exists_inv_mem_A {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {u : K⟦X⟧}
    (hu : u ∈ A O K) (h0 : ‖coeff 0 u‖ = 1) : ∃ w ∈ A O K, u * w = 1 := by
  obtain ⟨v, hv⟩ := (equivA O K).surjective ⟨u, hu⟩
  have hv' : PowerSeries.map (algebraMap O K) v = u := by
    rw [← coe_equivA, hv]
  have hc : algebraMap O K (constantCoeff v) = coeff 0 u := by
    rw [← hv', coeff_map, coeff_zero_eq_constantCoeff_apply]
  have hne : coeff 0 u ≠ 0 := by
    intro h
    rw [h, norm_zero] at h0
    exact zero_ne_one h0
  obtain ⟨c, hc'⟩ := (IsUnitBall.mem_range_iff (O := O) (coeff 0 u)⁻¹).2
    (by rw [norm_inv, h0, inv_one])
  have hunit : IsUnit (constantCoeff v) := by
    refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (O := O) (K := K) ?_)
    rw [map_mul, hc, hc', map_one, mul_inv_cancel₀ hne]
  obtain ⟨w, hw⟩ := (isUnit_iff_constantCoeff.2 hunit).exists_right_inv
  refine ⟨equivA O K w, (equivA O K w).2, ?_⟩
  rw [coe_equivA, ← hv', ← map_mul, hw, map_one]

theorem step {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ t) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ t) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ t) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ t * ρ := by
  have hfe := eq_low_add_high f n₀
  set r : K⟦X⟧ := PowerSeries.mk fun n => if n < n₀ then coeff n f else 0 with hr
  set fh : K⟦X⟧ := PowerSeries.mk fun n => coeff (n + n₀) f with hfh
  have hq : ∀ n, ‖coeff n (w * fh)‖ ≤ t := fun n => by
    have := norm_coeff_mul_le' zero_le_one ht hw (g := fh)
      (fun m => by rw [hfh, coeff_mk]; exact hf _) n
    rwa [one_mul] at this
  refine ⟨w * fh, r, hq, fun i hi => ?_, fun i => ?_, fun n => ?_⟩
  · rw [hr, coeff_mk, if_neg (not_lt.2 hi)]
  · rw [hr, coeff_mk]
    split_ifs
    · exact hf _
    · rwa [norm_zero]
  · have : f - w * fh * g - r = -(w * fh * p) := by
      rw [hg]
      linear_combination hfe - X ^ n₀ * fh * huw
    rw [this, map_neg, norm_neg]
    exact norm_coeff_mul_le' ht hρ hq hp n

theorem iterate {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k : ℕ) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ ρ ^ k := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp, by simp, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨q, r, hq, hr0, hr, he⟩ := ih
    obtain ⟨q', r', hq', hr0', hr', he'⟩ := step hρ (pow_nonneg hρ k) hg huw hw hp _ he
    have h1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ hρ1
    refine ⟨q + q', r + r', fun n => ?_, fun i hi => ?_, fun n => ?_, fun n => ?_⟩
    · rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hq n) ((hq' n).trans h1))
    · rw [map_add (f := _), hr0 i hi, hr0' i hi, add_zero]
    · rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr n) ((hr' n).trans h1))
    · have : f - (q + q') * g - (r + r') = f - q * g - r - q' * g - r' := by ring
      rw [this, pow_succ]
      exact he' n

theorem exists_div_approx (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧) (hg : g ∈ A O K) (n₀ : ℕ)
    (h1 : ‖coeff n₀ g‖ = 1) (hlt : ∀ i < n₀, ‖coeff i g‖ < 1) (δ : ℝ) (hδ : 0 < δ)
    (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧
      ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  set ρ : NNReal := (Finset.range n₀).sup (fun i => ‖coeff i g‖₊) with hρ
  have hρ1 : ρ < 1 := by
    rw [hρ, Finset.sup_lt_iff (by simp)]
    intro i hi
    exact_mod_cast hlt i (Finset.mem_range.1 hi)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  obtain ⟨w, hw, huw⟩ := exists_inv_mem_A (O := O)
    (u := PowerSeries.mk fun n => coeff (n + n₀) g)
    (fun n => by rw [coeff_mk]; exact hg _) (by rw [coeff_mk, zero_add, h1])
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hρ1'
  obtain ⟨q, r, hq, hr0, hr, he⟩ := iterate ρ.2 hρ1'.le (eq_low_add_high g n₀) huw hw
    (fun n => by
      rw [coeff_mk]
      split_ifs with h
      · exact_mod_cast Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 h)
      · rw [norm_zero]; exact ρ.2) f hf k
  exact ⟨q, hq, r, hr0, hr, fun n => (he n).trans hk.le⟩

end GlobalTheory.BK.DivApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvrStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_module_compact_adic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M] (ϖ : O), Irreducible ϖ → CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧ Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  first | exact @GlobalTheory.finite_free_compact_adic_dvr | exact GlobalTheory.finite_free_compact_adic_dvr | (intros; apply GlobalTheory.finite_free_compact_adic_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefectStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect : ∀ (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R) (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R), (∀ x : R, lr * x = 0 → x = 0) → (∃ v : Rˣ, e = lr * v) → (∃ v : Rˣ, e₀ = lr * v) → (∀ x, φ (σ x) = σ (φ x)) → φ lr = lr → σ lr = lr → σ e₀ = e₀ → A₀.map σ = A₀ → Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) → B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ) → e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ) → e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) = A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  first | (exact @GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (exact GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (intros; apply GlobalTheory.FrobeniusDefect.frobenius_defect_eq  <;> assumption)
end

