module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralBasisUnramifiedInvolutionExt
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.IntBasis

open IsLocalRing

abbrev adicVal (K : UQ) : Valuation K.E (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem adicVal_le_one_iff (K : UQ) (x : K.E) : adicVal K x ≤ 1 ↔ ∃ a : K.O, algebraMap K.O K.E a = x :=
  ⟨IsDiscreteValuationRing.exists_lift_of_le_one, by
    rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩

theorem adicVal_eq_one_iff (K : UQ) (a : K.O) : adicVal K (algebraMap K.O K.E a) = 1 ↔ IsUnit a := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  simp [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem adicVal_map (h : IsUnrExt K K' d φ) (x : K.E) : adicVal K' (φ x) = adicVal K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx
  have h1 := h.2.2.1 x
  unfold val at h1
  have h2 := neg_inj.1 h1
  have a1 : adicVal K' (φ x) ≠ 0 := (Valuation.ne_zero_iff _).2 hφ
  have a2 : adicVal K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [← WithZero.exp_log a1, ← WithZero.exp_log a2]
  exact congrArg WithZero.exp h2

theorem exists_lift (h : IsUnrExt K K' d φ) :
    ∃ ι : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
  let S := (algebraMap K'.O K'.E).range
  have hS : ∀ a : K.O, (φ.comp (algebraMap K.O K.E)) a ∈ S := fun a => by
    obtain ⟨b, hb⟩ := (adicVal_le_one_iff K' (φ (algebraMap K.O K.E a))).1 (by
      rw [adicVal_map h]; exact (adicVal_le_one_iff K _).2 ⟨a, rfl⟩)
    exact ⟨b, hb⟩
  let e : K'.O ≃+* S := RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective K'.O K'.E (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  refine ⟨e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict S hS), fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict S hS a))

theorem exists_key (h : IsUnrExt K K' d φ) :
    ∃ w : Fin d → K'.E, ∀ (a : Fin d → K.E) (m : Fin d), (∀ k, adicVal K (a k) ≤ adicVal K (a m)) →
      adicVal K' (∑ k, φ (a k) * w k) = adicVal K (a m) := by
  obtain ⟨ι, hι⟩ := exists_lift h
  haveI : IsLocalHom ι := ⟨fun a ha => by
    rw [← adicVal_eq_one_iff] at ha ⊢; rwa [hι, adicVal_map h] at ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ι).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hf : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have hc := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, K'.card_res, K.card_res, h.1, ← pow_mul,
      mul_comm, pow_mul] at hc
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← K.card_res]; exact Finite.one_lt_card
    exact (Nat.pow_right_injective h2 hc).symm
  haveI : Module.Finite (ResidueField K.O) (ResidueField K'.O) := Module.Finite.of_finite
  let bk := Module.finBasisOfFinrankEq _ _ hf
  choose w' hw' using fun i => residue_surjective (bk i)
  refine ⟨fun i => algebraMap K'.O K'.E (w' i), fun a m hm => ?_⟩
  by_cases ham : a m = 0
  · have h0 : ∀ k, a k = 0 := fun k => by
      have := hm k; rw [ham, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
    simp [h0]
  have hb : ∀ k, ∃ b : K.O, algebraMap K.O K.E b = a k / a m := fun k =>
    (adicVal_le_one_iff K _).1 (by rw [map_div₀]; exact div_le_one_of_le₀ (hm k) zero_le')
  choose b hb using hb
  have hbm : b m = 1 := IsFractionRing.injective K.O K.E (by rw [hb, div_self ham, map_one])
  set s : K'.O := ∑ k, ι (b k) * w' k with hs
  have hsum : ∑ k, φ (a k) * algebraMap K'.O K'.E (w' k) = φ (a m) * algebraMap K'.O K'.E s := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hι, hb, map_div₀, ← mul_assoc, mul_div_cancel₀ _ ((map_ne_zero φ).2 ham)]
  have hres : residue K'.O s ≠ 0 := by
    have e1 : residue K'.O s = ∑ k, residue K.O (b k) • bk k := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hw', Algebra.smul_def, RingHom.algebraMap_toAlgebra, ResidueField.map_residue]
    rw [e1]; intro h0
    have := Fintype.linearIndependent_iff.1 bk.linearIndependent _ h0 m
    rw [hbm, map_one] at this; exact one_ne_zero this
  have hsu : IsUnit s := by
    by_contra hn
    exact hres ((residue_eq_zero_iff s).2 ((mem_maximalIdeal s).2 hn))
  rw [hsum, Valuation.map_mul, (adicVal_eq_one_iff K' s).2 hsu, mul_one, adicVal_map h]

theorem intBasis : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    letI : Algebra K.E K'.E := φ.toAlgebra;
    ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  intro K K' d φ h hd
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, key⟩ := exists_key h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : ∀ a : Fin d → K.E, ∃ m, ∀ k, adicVal K (a k) ≤ adicVal K (a m) := fun a =>
    Finite.exists_max (fun k => adicVal K (a k))
  have hli : LinearIndependent K.E w := by
    rw [Fintype.linearIndependent_iff]; intro g hg
    obtain ⟨m, hm⟩ := hmax g
    have hk := key g m hm
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
    rw [hg, map_zero] at hk
    have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
    intro k; have := hm k; rw [hgm, map_zero] at this
    exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; exact h.2.2.2.2.symm)
  refine ⟨B, fun z => ?_⟩
  have hz : ∑ k, φ (B.repr z k) * w k = z := by
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨m, hm⟩ := hmax (B.repr z)
  have hv := key _ m hm
  rw [hz] at hv
  rw [← adicVal_le_one_iff K' z]
  constructor
  · intro hzO k; rw [← adicVal_le_one_iff]; exact (hm k).trans (hv ▸ hzO)
  · intro hall; rw [hv]; exact (adicVal_le_one_iff K _).2 (hall m)

end GlobalTheory.UnitLemma.Unr.IntBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnitUnramifiedQuadratic
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TraceUnit

section Ultra
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max_of_ultra (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem norm_sq_sub_sq_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x ^ 2 - y ^ 2‖ ≤ ‖x - y‖ := by
  have h1 : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [h1, norm_mul]
  have h2 : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  calc ‖x - y‖ * ‖x + y‖ ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖x - y‖ := mul_one _

theorem norm_pow_two_pow_sub_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ) :
    ‖x ^ 2 ^ k - y ^ 2 ^ k‖ ≤ ‖x - y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2 ^ k) ^ 2 := fun z => by rw [pow_succ, pow_mul]
    rw [e, e]
    exact (norm_sq_sub_sq_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy)).trans ih

theorem norm_sub_lt_one_of_sq {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (h : ‖x ^ 2 - y ^ 2‖ < 1) : ‖x - y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hle : ‖x - y‖ ≤ 1 := (norm_sub_le_max_of_ultra x y).trans (max_le hx hy)
  have heq : ‖x - y‖ = 1 := le_antisymm hle hc
  have e : x ^ 2 - y ^ 2 = (x - y) ^ 2 + 2 * y * (x - y) := by ring
  have hA : ‖(x - y) ^ 2‖ = 1 := by rw [norm_pow, heq, one_pow]
  have hB : ‖2 * y * (x - y)‖ < 1 := by
    rw [norm_mul, norm_mul, heq, mul_one]
    calc ‖(2 : K)‖ * ‖y‖ ≤ ‖(2 : K)‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h2
  have h3 : ‖(x - y) ^ 2 + 2 * y * (x - y)‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hA]; exact hB.ne'), hA]
    exact max_eq_left hB.le
  rw [e, h3] at h
  exact lt_irrefl _ h

theorem norm_sub_lt_one_of_pow {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ)
    (h : ‖x ^ 2 ^ k - y ^ 2 ^ k‖ < 1) : ‖x - y‖ < 1 := by
  induction k generalizing x y with
  | zero => simpa using h
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2) ^ 2 ^ k := fun z => by rw [pow_succ', pow_mul]
    rw [e, e] at h
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hy2 : ‖y ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    exact norm_sub_lt_one_of_sq h2 hx hy (ih hx2 hy2 h)

theorem exists_pow_close [ProperSpace K] {w : K} (hw : ‖w‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ ‖w ^ 2 ^ i - w ^ 2 ^ j‖ < 1 := by
  have hmem : ∀ n : ℕ, w ^ 2 ^ n ∈ Metric.closedBall (0 : K) 1 := fun n => by
    rw [mem_closedBall_zero_iff, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : K) 1).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (1 / 2) (by norm_num)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 : dist (w ^ 2 ^ φ N) a < 1 / 2 := hN N le_rfl
  have h2 : dist (w ^ 2 ^ φ (N + 1)) a < 1 / 2 := hN (N + 1) (Nat.le_succ N)
  rw [← dist_eq_norm]
  calc dist (w ^ 2 ^ φ N) (w ^ 2 ^ φ (N + 1)) ≤ dist (w ^ 2 ^ φ N) a + dist a (w ^ 2 ^ φ (N + 1)) :=
        dist_triangle _ _ _
    _ < 1 / 2 + 1 / 2 := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = 1 := by norm_num

end Ultra

theorem exists_trace_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E],
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
      ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by
  intro F E _ _ _ _ hU htr
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : CharZero F := hU.charZero
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  have h20 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have h2le : ‖(2 : E)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one E 2
    simpa using this
  rcases h2le.lt_or_eq with h2 | h2
  swap
  ·
    refine ⟨2⁻¹, by rw [norm_inv, h2, inv_one], ?_⟩
    have hs : star (2⁻¹ : E) = 2⁻¹ := by
      have : (2⁻¹ : E) = algebraMap F E 2⁻¹ := by rw [map_inv₀, map_ofNat]
      rw [this, hU.star_fix]
    rw [← norm_algebraMap' E, htr, hs, ← two_mul, mul_inv_cancel₀ h20, norm_one]

  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ a : F, y - algebraMap F E a ≠ 0 := fun a h => hy (by rw [sub_eq_zero.1 h, hU.star_fix])
  have hcont : Continuous fun a : F => ‖y - algebraMap F E a‖ := by fun_prop
  obtain ⟨x, -, hx⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    (Metric.nonempty_closedBall.2 (norm_nonneg _)) hcont.continuousOn
  have hmin : ∀ a : F, ‖y - algebraMap F E x‖ ≤ ‖y - algebraMap F E a‖ := by
    intro a
    have h0 : ‖y - algebraMap F E x‖ ≤ ‖y‖ := by
      have := isMinOn_iff.1 hx 0 (Metric.mem_closedBall_self (norm_nonneg y))
      simpa using this
    by_cases ha : ‖a‖ ≤ ‖y‖
    · exact isMinOn_iff.1 hx a (mem_closedBall_zero_iff.2 ha)
    · push_neg at ha
      have hm : ‖a‖ ≤ max ‖y‖ ‖y - algebraMap F E a‖ := by
        have := norm_sub_le_max_of_ultra y (y - algebraMap F E a)
        rwa [sub_sub_cancel, norm_algebraMap'] at this
      rcases le_max_iff.1 hm with h | h <;> linarith
  obtain ⟨t, ht⟩ := hU.unram (y - algebraMap F E x)
  have hd : 0 < ‖y - algebraMap F E x‖ := norm_pos_iff.2 (hyF x)
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [← norm_algebraMap' E t, h0, norm_zero] at ht
    linarith
  set u := (y - algebraMap F E x) * (algebraMap F E t)⁻¹ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_inv, norm_algebraMap', ← ht, mul_inv_cancel₀ hd.ne']
  have hfar : ∀ a : F, 1 ≤ ‖u - algebraMap F E a‖ := by
    intro a
    have e : u - algebraMap F E a = (y - algebraMap F E (x + t * a)) * (algebraMap F E t)⁻¹ := by
      rw [hu, map_add (f := _), map_mul]
      field_simp
      ring
    rw [e, norm_mul, norm_inv, norm_algebraMap', ← ht, le_mul_inv_iff₀ hd, one_mul]
    exact hmin _
  refine ⟨u, hu1.le, ?_⟩
  have hle : ‖Algebra.trace F E u‖ ≤ 1 := by
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu1.le (by rw [hU.norm_star]; exact hu1.le))
  refine le_antisymm hle (not_lt.1 fun hs => ?_)

  set n := u * star u with hn
  have hnn : star n = n := by rw [hn, star_mul, star_star, mul_comm]
  set v : F := -(Algebra.trace F E n / 2) with hvd
  have hv : algebraMap F E v = -n := by
    rw [hvd, map_neg, map_div₀, htr, hnn, map_ofNat]
    field_simp
    ring
  have hvn : ‖algebraMap F E v‖ ≤ 1 := by
    rw [hv, norm_neg, hn, norm_mul, hU.norm_star, hu1, one_mul]
  have hq : ‖u ^ 2 - algebraMap F E v‖ < 1 := by
    have e : u ^ 2 - algebraMap F E v = algebraMap F E (Algebra.trace F E u) * u := by
      rw [hv, htr, hn]; ring
    rw [e, norm_mul, norm_algebraMap', hu1, mul_one]
    exact hs
  obtain ⟨i, j, hij, hc⟩ := exists_pow_close hu1.le
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  have e1 : u ^ 2 ^ (i + (m + 1)) = (u ^ 2 ^ (m + 1)) ^ 2 ^ i := by
    rw [← pow_mul, ← pow_add, Nat.add_comm (m + 1) i]
  rw [e1] at hc
  have hpow1 : ‖u ^ 2 ^ (m + 1)‖ ≤ 1 := by rw [norm_pow, hu1, one_pow]
  have hA : ‖u - u ^ 2 ^ (m + 1)‖ < 1 := norm_sub_lt_one_of_pow h2 hu1.le hpow1 i hc
  have e2 : u ^ 2 ^ (m + 1) = (u ^ 2) ^ 2 ^ m := by rw [pow_succ', pow_mul]
  have hB : ‖(u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m‖ < 1 :=
    (norm_pow_two_pow_sub_le (by rw [norm_pow, hu1, one_pow]) hvn m).trans_lt hq
  have hC : ‖u - algebraMap F E (v ^ 2 ^ m)‖ < 1 := by
    rw [map_pow]
    have e3 : u - (algebraMap F E v) ^ 2 ^ m =
        (u - u ^ 2 ^ (m + 1)) + ((u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m) := by
      rw [e2]; ring
    rw [e3]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hA hB)
  linarith [hfar (v ^ 2 ^ m)]

end GlobalTheory.TraceUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLastMaxOfMem
section
open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK.HatInj

def LastMax (w : ℕ → ℝ) (d : ℕ) : Prop := (∀ n, w n ≤ w d) ∧ ∀ n, d < n → w n < w d

theorem LastMax.unique {w : ℕ → ℝ} {d d' : ℕ} (h : LastMax w d) (h' : LastMax w d') : d = d' := by
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · exact absurd (h.2 d' hlt) (not_lt.mpr (h'.1 d))
  · exact heq
  · exact absurd (h'.2 d hgt) (not_lt.mpr (h.1 d'))

theorem exists_lastMax {w : ℕ → ℝ} (hw : Tendsto w atTop (𝓝 0)) {n₀ : ℕ} (h₀ : 0 < w n₀) :
    ∃ d, LastMax w d := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hw.eventually (gt_mem_nhds h₀))
  have hn₀ : n₀ < N := by
    by_contra hc
    exact lt_irrefl _ (hN n₀ (not_lt.mp hc))
  obtain ⟨a, ha, hmax⟩ := (Finset.range N).exists_max_image w ⟨n₀, Finset.mem_range.mpr hn₀⟩
  have hbig : ∀ n, N ≤ n → w n < w a := fun n hn =>
    (hN n hn).trans_le (hmax n₀ (Finset.mem_range.mpr hn₀))
  let T := (Finset.range N).filter (fun n => w n = w a)
  have hTne : T.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  have hda : w (T.max' hTne) = w a := (Finset.mem_filter.mp (T.max'_mem hTne)).2
  refine ⟨T.max' hTne, fun n => ?_, fun n hn => ?_⟩
  · rw [hda]
    rcases lt_or_ge n N with hnN | hnN
    · exact hmax n (Finset.mem_range.mpr hnN)
    · exact (hbig n hnN).le
  · rw [hda]
    rcases lt_or_ge n N with hnN | hnN
    · refine lt_of_le_of_ne (hmax n (Finset.mem_range.mpr hnN)) fun heq => ?_
      have hT : n ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN, heq⟩
      exact absurd (T.le_max' n hT) (not_le.mpr hn)
    · exact hbig n hnN
private theorem coeff_E_mul' {K : Type} [NormedField K] [IsUltrametricDist K] (l e : ℕ)
    (h : K⟦X⟧) (n : ℕ) :
    coeff n (E K l e * h) = (if e ≤ n then coeff (n - e) h else 0) + (l : K) * coeff n h := by
  rw [E, add_mul, map_add (f := _), coeff_X_pow_mul', ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul]

variable {K : Type} [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem lastMax_E_mul {h : K⟦X⟧} {d : ℕ}
    (H : LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d) :
    LastMax (fun n => ‖coeff n (E K l e * h)‖ * rad l (1 / e) ^ n) (d + e) := by
  have hr : 0 < rad l (1 / (e : ℝ)) := rad_pos l _
  have hre : rad l (1 / (e : ℝ)) ^ e = ‖(l : K)‖ := rad_pow l e
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (l_ne_zero (K := K) l)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hlow : ∀ n, n < e → ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n =
      ‖(l : K)‖ * (‖coeff n h‖ * rad l (1 / (e : ℝ)) ^ n) := by
    intro n hn
    rw [coeff_E_mul', if_neg (not_le.mpr hn), zero_add, norm_mul]
    ring
  have hhigh : ∀ k, ‖coeff (k + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (k + e) ≤
      max (‖(l : K)‖ * (‖coeff k h‖ * rad l (1 / (e : ℝ)) ^ k))
        (‖(l : K)‖ * (‖coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e))) := by
    intro k
    rw [coeff_E_mul', if_pos (Nat.le_add_left e k), Nat.add_sub_cancel]
    calc ‖coeff k h + (l : K) * coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e)
        ≤ max ‖coeff k h‖ ‖(l : K) * coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e) :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (pow_nonneg hr.le _)
      _ = _ := by
          rw [max_mul_of_nonneg _ _ (pow_nonneg hr.le _)]
          congr 1
          · rw [pow_add, hre]; ring
          · rw [norm_mul]; ring
  have htop : ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e) =
      ‖(l : K)‖ * (‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ d) := by
    rw [coeff_E_mul', if_pos (Nat.le_add_left e d), Nat.add_sub_cancel]
    have hsmall : ‖(l : K) * coeff (d + e) h‖ < ‖coeff d h‖ := by
      have hlt := mul_lt_mul_of_pos_left (H.2 (d + e) (by omega)) hl
      refine lt_of_mul_lt_mul_right ?_ (pow_pos hr (d + e)).le
      calc ‖(l : K) * coeff (d + e) h‖ * rad l (1 / (e : ℝ)) ^ (d + e)
          = ‖(l : K)‖ * (‖coeff (d + e) h‖ * rad l (1 / (e : ℝ)) ^ (d + e)) := by
            rw [norm_mul]; ring
        _ < ‖(l : K)‖ * (‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ d) := hlt
        _ = ‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ (d + e) := by rw [pow_add, hre]; ring
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsmall.ne', max_eq_left hsmall.le,
      pow_add, hre]
    ring
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · show ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n ≤ ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e)
    rw [htop]
    rcases lt_or_ge n e with hne | hne
    · rw [hlow n hne]
      exact mul_le_mul_of_nonneg_left (H.1 n) hl.le
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hne
      exact (hhigh k).trans (max_le (mul_le_mul_of_nonneg_left (H.1 k) hl.le)
        (mul_le_mul_of_nonneg_left (H.1 (k + e)) hl.le))
  · show ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n < ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e)
    rw [htop]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show e ≤ n by omega)
    exact (hhigh k).trans_lt (max_lt (mul_lt_mul_of_pos_left (H.2 k (by omega)) hl)
      (mul_lt_mul_of_pos_left (H.2 (k + e) (by omega)) hl))

theorem lastMax_E_pow_mul {h : K⟦X⟧} {d : ℕ}
    (H : LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d) (m : ℕ) :
    LastMax (fun n => ‖coeff n (E K l e ^ m * h)‖ * rad l (1 / e) ^ n) (d + m * e) := by
  induction m with
  | zero => simpa using H
  | succ m ih =>
    have h' := lastMax_E_mul l e ih
    rw [← mul_assoc, ← pow_succ'] at h'
    have hidx : d + (m + 1) * e = d + m * e + e := by ring
    rw [hidx]
    exact h'

theorem exists_lastMax_of_mem {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {h : K⟦X⟧}
    (hh : h ∈ Rpi O K l e) (h0 : h ≠ 0) :
    ∃ d, LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d := by
  have hmem : Tendsto (fun n => ‖coeff n h‖ * rad l (1 / (e : ℝ)) ^ n) atTop (𝓝 0) :=
    mem_R.mp (show h ∈ R O K l (1 / (e : ℝ)) from hh)
  obtain ⟨n₀, hn₀⟩ : ∃ n, coeff n h ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (PowerSeries.ext fun n => by simpa using hc n)
  exact exists_lastMax hmem (mul_pos (norm_pos_iff.mpr hn₀) (pow_pos (rad_pos l _) n₀))

end GlobalTheory.BK.HatInj

namespace GlobalTheory.BK


open HatInj in
theorem toHat_injective (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Function.Injective (toHat O K l e) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hdiv : ∀ m : ℕ, ∃ y : Rpi O K l e, (x : K⟦X⟧) = E K l e ^ m * y := by
    intro m
    have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {EIn l e (invL l (A O K))}) m) hx
    unfold toHat at h1
    generalize_proofs p1 p2 p3 p4 p5 p6 p7 at h1
    unfold SameJets.toCompl SameJets.jet at h1
    erw [AdicCompletion.evalₐ_liftRingHom, map_zero, RingHom.comp_apply] at h1
    have h2 := (map_eq_zero_iff _ (RingEquiv.injective _)).mp h1
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
    obtain ⟨y, hy⟩ := h2
    refine ⟨y, ?_⟩
    rw [← hy]
    simp [mul_comm]
  by_contra hx0
  have hx0' : (x : K⟦X⟧) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨d, hd⟩ := exists_lastMax_of_mem (l := l) (e := e) x.2 hx0'
  obtain ⟨y, hy⟩ := hdiv (d + 1)
  have hy0 : (y : K⟦X⟧) ≠ 0 := by
    intro h
    apply hx0'
    rw [hy, h, mul_zero]
  obtain ⟨d', hd'⟩ := exists_lastMax_of_mem (l := l) (e := e) y.2 hy0
  have h3 := lastMax_E_pow_mul (l := l) (e := e) hd' (d + 1)
  rw [← hy] at h3
  have h4 := hd.unique h3
  have he : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (NeZero.ne e)
  have h5 : d + 1 ≤ (d + 1) * e := Nat.le_mul_of_pos_right _ he
  omega

end GlobalTheory.BK
end

