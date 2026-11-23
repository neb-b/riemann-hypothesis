module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsTer
section
namespace GlobalTheory.IntSmulMemLattice

open NumberField

theorem exists_int_smul_mem {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  have hden : ∀ a : E, ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a) := fun a =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
  have hv : v ∈ Submodule.span E (L : Set V) := by rw [hL]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    have e1 : (m * k) • x = k • (m • x) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • y = m • (k • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem hmx k) (zsmul_mem hky m)
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := hden a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩

    let b : RingOfIntegers E := ⟨d • a, hint⟩
    have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := by
      change d • a = (d : E) * a
      rw [zsmul_eq_mul]
    have e : (d * m) • (a • x) = b • (m • x) := by
      rw [← algebraMap_smul E b (m • x), hb, ← Int.cast_smul_eq_zsmul E (d * m),
        ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact L.smul_mem b hmx

end GlobalTheory.IntSmulMemLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntTraceModEqSumResiduesSplitPrime
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SplitTrace

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton, show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp,
    Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

theorem split_of_card (p : ℕ) (hp : p.Prime) {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K))
    (he : Function.Injective e) (hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal)
    (hcard : Fintype.card ι = Module.finrank ℚ K) :
    (∀ i, Ideal.absNorm (e i).asIdeal = p) ∧ Ideal.span {(p : 𝓞 K)} = ⨅ i, (e i).asIdeal := by
  classical
  set n := Module.finrank ℚ K
  have hcop : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      IsCoprime (e i).asIdeal (e j).asIdeal := fun i _ j _ hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  have hJ : ∏ i, (e i).asIdeal = ⨅ i, (e i).asIdeal := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]; simp
  have hle : Ideal.span {(p : 𝓞 K)} ≤ ∏ i, (e i).asIdeal := by
    rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_iInf.2 hmem
  have hdvd_i : ∀ i, Ideal.absNorm (e i).asIdeal ∣ p ^ n := fun i => by
    rw [← absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (hmem i))
  choose k hkn hk using fun i => (Nat.dvd_prime_pow hp).1 (hdvd_i i)
  have hk1 : ∀ i, 1 ≤ k i := fun i => by
    rcases Nat.eq_zero_or_pos (k i) with h | h
    · exfalso
      have h1 := hk i
      rw [h, pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact (e i).isPrime.ne_top h1
    · exact h
  have hprod : Ideal.absNorm (∏ i, (e i).asIdeal) = p ^ ∑ i, k i := by
    rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => hk i
  have hsum_le : ∑ i, k i ≤ n := by
    have h := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hprod, absNorm_span_natCast] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hsum_eq : ∑ i, k i = ∑ _i : ι, 1 := by
    refine le_antisymm ?_ (Finset.sum_le_sum fun i _ => hk1 i)
    simpa [hcard] using hsum_le
  have hkeq : ∀ i, k i = 1 := fun i =>
    ((Finset.sum_eq_sum_iff_of_le (fun j _ => hk1 j)).1 hsum_eq.symm i (Finset.mem_univ i)).symm
  refine ⟨fun i => by rw [hk i, hkeq i, pow_one], ?_⟩
  rw [← hJ]
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hle
  have hnL : Ideal.absNorm L = 1 := by
    have h := congrArg Ideal.absNorm hL
    rw [map_mul, hprod, absNorm_span_natCast, show ∑ i, k i = n by simpa [hcard] using hsum_eq] at h
    have hpn : 0 < p ^ n := pow_pos hp.pos n
    exact Nat.eq_of_mul_eq_mul_left hpn (by rw [mul_one]; exact h.symm)
  rw [hL, Ideal.absNorm_eq_one_iff.1 hnL, Ideal.mul_top]

theorem trace_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (z : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) z = ∑ i, Algebra.trace R (A i) (z i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
  rw [show z * Pi.single i (b i k) = Pi.single i (z i * b i k) by
    funext j; by_cases h : j = i
    · subst h; simp
    · simp [h]]
  simp

theorem intTrace_modEq_sum : ∀ {K : Type} [Field K] [NumberField K] (p : ℕ), p.Prime → ∀ {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K)), Function.Injective e → (∀ W : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ W.asIdeal ↔ ∃ i, e i = W) → Fintype.card ι = Module.finrank ℚ K → ∀ (x : 𝓞 K) (b : ι → ℤ), (∀ i, x - (b i : 𝓞 K) ∈ (e i).asIdeal) → ((Algebra.intTrace ℤ (𝓞 K) x : ℤ) : ZMod p) = ∑ i, (b i : ZMod p) := by
  intro K _ _ p hp ι _ e he hW hcard x b hxb
  classical
  have hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal := fun i => (hW (e i)).2 ⟨i, rfl⟩
  obtain ⟨hnorm, hspan⟩ := split_of_card p hp e he hmem hcard
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = ⨅ i, (e i).asIdeal := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hspan
  have hPv : ∀ i, P ≤ (e i).asIdeal.comap (algebraMap ℤ (𝓞 K)) := fun i => by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact iInf_le _ i
  letI : ∀ i, Algebra (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.algebraQuotientOfLEComap (hPv i)
  haveI : ∀ i, IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => .of_algebraMap_eq' rfl
  haveI : ∀ i, Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Module.Finite.of_restrictScalars_finite ℤ _ _
  letI : ∀ i, Field (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.field _
  have hcop : Pairwise (Function.onFun IsCoprime fun i => (e i).asIdeal) := fun i j hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  let φ : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] (∀ i, 𝓞 K ⧸ (e i).asIdeal) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientInfRingEquivPiQuotient _ hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hφ : φ (Ideal.Quotient.mk _ x) = fun i => Ideal.Quotient.mk (e i).asIdeal x := rfl
  have hx1 : ∀ i, Ideal.Quotient.mk (e i).asIdeal x =
      algebraMap (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) (Ideal.Quotient.mk P (b i)) := fun i => by
    rw [Ideal.Quotient.eq.mpr (hxb i)]
    show _ = Ideal.Quotient.mk (e i).asIdeal (algebraMap ℤ (𝓞 K) (b i))
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfr : ∀ i, Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) = 1 := fun i => by
    have hcardv : Nat.card (𝓞 K ⧸ (e i).asIdeal) = p := by
      rw [← hnorm i, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ (e i).asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P (∑ i, b i) := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv φ, hφ, trace_pi]
    simp_rw [hx1, Algebra.trace_algebraMap, hfr, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  rw [← Int.cast_sum, ZMod.intCast_eq_intCast_iff_dvd_sub]
  obtain ⟨m, hm⟩ := key
  exact ⟨-m, by linear_combination -hm⟩

end GlobalTheory.SplitTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralOfFiniteBaseChangeImage
section
open TensorProduct

namespace GlobalTheory

theorem integral_of_finite_base_change_image : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ (ω : L ⊗[F] K) (p : Polynomial (U ⊗[T] C)), p.Monic → p.eval₂ φ ω = 0 → IsIntegral U ω := by
  intro T U C F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ ω p hp h
  letI : Algebra (U ⊗[T] C) (L ⊗[F] K) := φ.toAlgebra
  have hmap : algebraMap (U ⊗[T] C) (L ⊗[F] K) = φ := rfl
  haveI : IsScalarTower U (U ⊗[T] C) (L ⊗[F] K) := by
    refine IsScalarTower.of_algebraMap_eq fun u => ?_
    rw [hmap]
    change algebraMap U (L ⊗[F] K) u = φ (u ⊗ₜ 1)
    rw [hφ, map_one]
    rfl
  have hint : IsIntegral (U ⊗[T] C) ω := ⟨p, hp, h⟩
  haveI : Algebra.IsIntegral U (U ⊗[T] C) := inferInstance
  exact isIntegral_trans ω hint

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntertwineAeval
section
namespace GlobalTheory.IntertwineAeval

theorem intertwine_pow {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (n : ℕ) (v : M) : r ((T ^ n) v) = (T' ^ n) (r v) := by
  induction n generalizing v with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

theorem intertwine_aeval {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (p : Polynomial ℂ) (v : M) :
    r (Polynomial.aeval T p v) = Polynomial.aeval T' p (r v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, intertwine_pow r h]

end GlobalTheory.IntertwineAeval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidef
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem inv_entry_norm_le_of_sub_posSemidef (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ)
    (hc : 0 < c) (hY : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (i j : Fin g) :
    ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by

  have hq : ∀ x : Fin g → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
    intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h
    linarith

  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hYv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hq v
    rw [hYv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := le_antisymm (by nlinarith [dotProduct_self_star_nonneg v]) (by
      simpa using dotProduct_self_star_nonneg v)
    exact hv (by simpa using h2)
  have hYinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hdet

  have hmap : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [show Y.map Complex.ofReal = Y.map Complex.ofRealHom from rfl,
      show Y⁻¹.map Complex.ofReal = Y⁻¹.map Complex.ofRealHom from rfl, ← Matrix.map_mul, hYinv]
    simp
  rw [hmap, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]

  set w : Fin g → ℝ := Y⁻¹ *ᵥ Pi.single j 1 with hw
  have hYw : Y *ᵥ w = Pi.single j 1 := by
    rw [hw, mulVec_mulVec, hYinv, one_mulVec]
  have hwi : ∀ k, w k = Y⁻¹ k j := by
    intro k; simp [hw, mulVec_single_one]
  have hqw : c * (w ⬝ᵥ w) ≤ w j := by
    have := hq w
    rw [hYw, dotProduct_single, mul_one] at this
    exact this
  have hsq : ∀ k, w k ^ 2 ≤ w ⬝ᵥ w := by
    intro k
    rw [dotProduct]
    have := Finset.single_le_sum (f := fun l => w l * w l) (fun l _ => mul_self_nonneg (w l))
      (Finset.mem_univ k)
    simpa [sq] using this
  have hj1 := hsq j
  have hi1 := hsq i
  have hwj0 : 0 ≤ w j := by nlinarith [sq_nonneg (w j)]
  have hcwj : c * w j ≤ 1 := by
    rcases hwj0.lt_or_eq with h | h
    · nlinarith
    · rw [← h]; linarith
  have hci1 : c * w i ^ 2 ≤ w j := le_trans (mul_le_mul_of_nonneg_left hi1 hc.le) hqw
  have hci : (c * w i) ^ 2 ≤ 1 := by
    calc (c * w i) ^ 2 = c * (c * w i ^ 2) := by ring
      _ ≤ c * w j := mul_le_mul_of_nonneg_left hci1 hc.le
      _ ≤ 1 := hcwj
  have habs : |c * w i| ≤ 1 := sq_le_one_iff_abs_le_one _ |>.1 hci
  rw [← hwi i, le_div_iff₀ hc]
  rw [abs_mul, abs_of_pos hc] at habs
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued
section
open IsDedekindDomain NumberField
namespace GlobalTheory
namespace DegreeOneUniformiser

open IsDedekindDomain NumberField in
private theorem adicCompletionIntegers_integers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers F) :=
  ⟨Subtype.val_injective, fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2,
    fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr hx⟩, rfl⟩⟩


open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F)
    (h : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hI := adicCompletionIntegers_integers v
  have hunit : ∀ x : v.adicCompletionIntegers F, IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
    fun x => hI.isUnit_iff_valuation_eq_one
  have hle : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) ≤ 1 :=
    fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (hunit π).mp hu
    rw [h] at this
    exact absurd this (by decide)
  · have hv : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
      rw [← h, hab, Subring.coe_mul, map_mul]
    have ha0 : Valued.v (a : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
    have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (a : v.adicCompletion F) = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ha0).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (b : v.adicCompletion F) = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hb0).symm⟩
    have ha := hle a
    have hb := hle b
    rw [hm, hn, ← WithZero.exp_add, WithZero.exp_inj] at hv
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    rw [hunit, hunit, hm, hn, ← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega


open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (ψ : E →+* v.adicCompletion F), (∀ a : F, ψ (algebraMap F E a) = algebraMap F (v.adicCompletion F) a) → (∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ψ ((x : E)⁻¹) ∉ v.adicCompletionIntegers F)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ π : v.adicCompletionIntegers F, Irreducible π ∧ (π : v.adicCompletion F) = ψ (ϖ : E) := by
  intro F E _ _ _ _ _ v P ψ hψ hint hP ϖ hϖP hϖP2
  have hle : ∀ x : 𝓞 E, Valued.v (ψ (x : E)) ≤ 1 := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hint x)
  have hne : ∀ x : 𝓞 E, x ≠ 0 → Valued.v (ψ (x : E)) ≠ 0 := by
    intro x hx
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ ψ.injective]
    exact_mod_cast hx
  have hone : ∀ x : 𝓞 E, x ∉ P.asIdeal → Valued.v (ψ (x : E)) = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ P.asIdeal.zero_mem)
    have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp
      (not_not.mp (mt (hP x hx0).mpr hx))
    rw [map_inv₀, map_inv₀] at h1
    exact le_antisymm (hle x) ((inv_le_one₀ (zero_lt_iff.mpr (hne x hx0))).mp h1)
  have hϖ0 : ϖ ≠ 0 := fun h => hϖP2 (h ▸ Ideal.zero_mem _)
  have hlt : Valued.v (ψ (ϖ : E)) < 1 := by
    have h1 := (hP ϖ hϖ0).mp hϖP
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀] at h1
    exact (one_lt_inv₀ (zero_lt_iff.mpr (hne ϖ hϖ0))).mp h1
  obtain ⟨u, hu⟩ := v.intValuation_exists_uniformizer
  let f : 𝓞 E := ⟨algebraMap F E (u : F), (RingOfIntegers.isIntegral_coe u).algebraMap⟩
  have hf : Valued.v (ψ (f : E)) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (ψ (algebraMap F E (u : F))) = _
    rw [hψ, ← hu, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (u : F)
  have hf0 : f ≠ 0 := fun h => by
    rw [h] at hf
    simp only [ZeroMemClass.coe_zero, map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have hfP : f ∈ P.asIdeal := by
    rw [hP f hf0, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, map_inv₀, map_inv₀, hf,
      ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr hϖP : Ideal.span {ϖ} ≤ P.asIdeal)
  have hJP : ¬ J ≤ P.asIdeal := fun hJP => hϖP2 (by
    have hmem : ϖ ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton_self ϖ
    rw [hJ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hJP hmem)
  obtain ⟨t, htJ, htP⟩ := Set.not_subset.mp hJP
  have hft : f * t ∈ Ideal.span {ϖ} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hfP htJ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hft
  have hval := congrArg (fun x : 𝓞 E => Valued.v (ψ (x : E))) hs
  simp only [MulMemClass.coe_mul, map_mul] at hval
  rw [hone t htP, mul_one, hf] at hval
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v (ψ (ϖ : E)) := by
    rw [← hval]
    calc Valued.v (ψ (s : E)) * Valued.v (ψ (ϖ : E)) ≤ 1 * Valued.v (ψ (ϖ : E)) :=
          mul_le_mul' (hle s) le_rfl
      _ = Valued.v (ψ (ϖ : E)) := one_mul _
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (ψ (ϖ : E)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log (hne ϖ hϖ0)).symm⟩
  rw [hm, WithZero.exp_le_exp] at hge
  rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  have hm1 : m = -1 := by omega
  refine ⟨⟨ψ (ϖ : E), hint ϖ⟩, _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued v _ ?_, rfl⟩
  rw [← hm1]
  exact hm

end DegreeOneUniformiser
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralDetOfPreservesLattice
section
open Polynomial

namespace GlobalTheory.IsIntegralDetLattice

theorem isIntegral_of_isRoot_charpoly {R K : Type} [CommRing R] [Field K] [Algebra R K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (hA : IsIntegral R A) (x : K) (hx : A.charpoly.IsRoot x) :
    IsIntegral R x := by
  obtain ⟨p, hp, hpA⟩ := hA

  have hmem : x ∈ spectrum K A := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hx
  have h2 := spectrum.subset_polynomial_aeval A (p.map (algebraMap R K)) ⟨x, hmem, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hpA, spectrum.mem_iff, sub_zero] at h2
  refine ⟨p, hp, ?_⟩
  rw [eval₂_eq_eval_map]
  by_contra hne
  exact h2 ((Ne.isUnit hne).map (algebraMap K (Matrix (Fin N) (Fin N) K)))

theorem isIntegral_det {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) E) (hA : IsIntegral R A) : IsIntegral R A.det := by

  let φ : E →ₐ[R] AlgebraicClosure E := IsScalarTower.toAlgHom R E (AlgebraicClosure E)
  have hA' : IsIntegral R (A.map (algebraMap E (AlgebraicClosure E))) := by
    exact hA.map (φ.mapMatrix (m := Fin N))
  have hdet : (A.map (algebraMap E (AlgebraicClosure E))).det = algebraMap E (AlgebraicClosure E) A.det := by
    rw [RingHom.map_det]; rfl
  rw [← isIntegral_algHom_iff φ (algebraMap E (AlgebraicClosure E)).injective]
  show IsIntegral R (algebraMap E (AlgebraicClosure E) A.det)
  rw [← hdet, Matrix.det_eq_prod_roots_charpoly]
  exact multiset_prod_mem (S := integralClosure R (AlgebraicClosure E)) _
    fun r hr => isIntegral_of_isRoot_charpoly _ hA' r (Polynomial.isRoot_of_mem_roots hr)

theorem isIntegral_of_preserves {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (L : Submodule R (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ := by
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL

  let f : Module.End R L := ((Matrix.mulVecLin γ).restrictScalars R).restrict hγ
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (n : ℕ) (v : Fin N → E) (hv : v ∈ L),
      (γ ^ n).mulVec v = ((f ^ n) ⟨v, hv⟩ : Fin N → E) := by
    intro n
    induction n with
    | zero => intro v hv; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih v hv, Module.End.mul_apply]
      rfl
  have key : ∀ (q : R[X]) (v : Fin N → E) (hv : v ∈ L),
      (aeval γ q).mulVec v = ((aeval f q) ⟨v, hv⟩ : Fin N → E) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v hv; simp [Matrix.add_mulVec, hp v hv, hq v hv]
    | monomial n a =>
      intro v hv
      simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hpow n v hv]
  have hz : Matrix.toLin' (aeval γ p) = 0 := by
    refine LinearMap.ext_on hs fun v hv => ?_
    simp [Matrix.toLin'_apply, key p v hv, hpf]
  exact ⟨p, hp, by rw [← aeval_def]; exact Matrix.toLin'.map_eq_zero_iff.mp hz⟩

theorem isIntegral_det_of_preserves_lattice {E : Type} [Field E] [NumberField E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det := by
  exact isIntegral_trans _ (isIntegral_det γ (isIntegral_of_preserves L hL hs γ hγ))

end GlobalTheory.IsIntegralDetLattice
end

