module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AdjoinNilFinite
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.adjoin_nil_finite :
    ∀ {A G : Type} [CommRing A] [IsLocalRing A] [CommRing G] [Algebra A G] [Nontrivial G] (P : Submodule A G), P.FG → (∀ y ∈ P, ∃ a : A, IsNilpotent (y - algebraMap A G a)) → Module.Finite A (Algebra.adjoin A (P : Set G)) ∧ IsLocalRing (Algebra.adjoin A (P : Set G)) ∧ ∀ y ∈ Algebra.adjoin A (P : Set G), ∃ a : A, IsNilpotent (y - algebraMap A G a) := by
  intro A G _ _ _ _ _ P hP hnil
  let N : Subalgebra A G :=
    { carrier := {y | ∃ a : A, IsNilpotent (y - algebraMap A G a)}
      mul_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        have e : x * y - algebraMap A G (a * b) =
            (x - algebraMap A G a) * y + algebraMap A G a * (y - algebraMap A G b) := by
          rw [map_mul]; ring
        rw [e]
        obtain ⟨k, hk⟩ := ha
        obtain ⟨m, hm⟩ := hb
        exact (Commute.all _ _).isNilpotent_add ⟨k, by rw [mul_pow, hk, zero_mul]⟩
          ⟨m, by rw [mul_pow, hm, mul_zero]⟩
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        have e : x + y - algebraMap A G (a + b) =
            (x - algebraMap A G a) + (y - algebraMap A G b) := by
          rw [map_add (f := _)]; ring
        rw [e]
        exact (Commute.all _ _).isNilpotent_add ha hb
      algebraMap_mem' := fun r => ⟨r, by simp⟩ }
  have hS : Algebra.adjoin A (P : Set G) ≤ N := Algebra.adjoin_le (fun y hy => hnil y hy)
  have hint : ∀ y, (∃ a : A, IsNilpotent (y - algebraMap A G a)) → IsIntegral A y := by
    rintro y ⟨a, k, hk⟩
    have hn : IsIntegral A (y - algebraMap A G a) :=
      ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
    have := hn.add (isIntegral_algebraMap (x := a))
    simpa using this
  refine ⟨?_, ?_, fun y hy => hS hy⟩
  · obtain ⟨s, hs⟩ := hP
    rw [← hs, Algebra.adjoin_span]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun y hy => hint y (hnil y (hs ▸ Submodule.subset_span hy)))
  · apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro y
    obtain ⟨a, ha⟩ := hS y.2
    let n : Algebra.adjoin A (P : Set G) :=
      ⟨(y : G) - algebraMap A G a, Subalgebra.sub_mem _ y.2 (Subalgebra.algebraMap_mem _ a)⟩
    have hn : IsNilpotent n := by
      obtain ⟨k, hk⟩ := ha
      exact ⟨k, Subtype.ext (by simpa [n] using hk)⟩
    have hy : y = algebraMap A _ a + n := Subtype.ext (by simp [n])
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
    · left
      rw [hy, add_comm]
      exact hn.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
    · right
      have e : 1 - y = algebraMap A _ (1 - a) + (-n) := by
        rw [hy, map_sub, map_one]; ring
      rw [e, add_comm]
      exact hn.neg.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AlghomOfUnits
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.alghom_of_units :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (e : ∀ s, d s → d s → E), (∀ s i j k, e s i j * e s j k = e s i k) → (∀ s i j k l, j ≠ k → e s i j * e s k l = 0) → (∀ s t i j k l, s ≠ t → e s i j * e t k l = 0) → ∑ s, ∑ i, e s i i = 1 → ∃ j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E, ∀ s i k, j (Pi.single s (single i k 1)) = e s i k := by
  intro K E _ _ _ σ _ _ d _ _ _ e hmul horth hst hsum
  let f : (∀ s, Matrix (d s) (d s) K) → E := fun M => ∑ s, ∑ i, ∑ k, M s i k • e s i k
  have hadd : ∀ M N, f (M + N) = f M + f N := by
    intro M N
    simp only [f, Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : K) M, f (c • M) = c • f M := by
    intro c M
    simp only [f, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have key : ∀ (N : ∀ s, Matrix (d s) (d s) K) s i j (a : K),
      (a • e s i j) * f N = ∑ k, (a * N s j k) • e s i k := by
    intro N s i j a
    simp only [f]
    rw [Finset.mul_sum, Finset.sum_eq_single s]
    · rw [Finset.mul_sum, Finset.sum_eq_single j]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_mul_smul_comm, hmul]
      · intro l _ hl
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [smul_mul_smul_comm, horth s i j l k (Ne.symm hl), smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro t _ ht
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [smul_mul_smul_comm, hst s t i j l k (Ne.symm ht), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hm : ∀ M N, f (M * N) = f M * f N := by
    intro M N
    have : f M * f N = ∑ s, ∑ i, ∑ j, ∑ k, (M s i j * N s j k) • e s i k := by
      show (∑ s, ∑ i, ∑ k, M s i k • e s i k) * f N = _
      simp only [Finset.sum_mul, key]
    rw [this]
    simp only [f, Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  have h1 : f 1 = 1 := by
    simp only [f, Pi.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hsum
  let L : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E :=
    { toFun := f, map_add' := hadd, map_smul' := hsmul }
  refine ⟨AlgHom.ofLinearMap L h1 hm, ?_⟩
  intro s i k
  show f (Pi.single s (Matrix.single i k 1)) = e s i k
  simp only [f]
  rw [Finset.sum_eq_single s]
  · rw [Pi.single_eq_same]
    simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [if_neg]
        exact fun h => hb h.2.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      exact fun h => hb h.1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro t _ ht
    simp [Pi.single_eq_of_ne ht]
  · intro h; exact absurd (Finset.mem_univ _) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetField
section
open IsLocalRing

private theorem UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero {K : Type} [Field K] (V : ValuationSubring K)
    {ι : Type} [Fintype ι] [Nonempty ι] (w : ι → K) (hw : w ≠ 0) :
    ∃ c, w c ≠ 0 ∧ ∀ j, w j / w c ∈ V := by
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun j => V.valuation (w j))
    Finset.univ_nonempty
  have hwc : w c ≠ 0 := by
    intro h0
    apply hw
    funext j
    have hj := hc j (Finset.mem_univ j)
    rw [h0, map_zero] at hj
    exact (Valuation.zero_iff _).mp (le_antisymm hj zero_le')
  refine ⟨c, hwc, fun j => ?_⟩
  rw [← V.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hc j (Finset.mem_univ j)) zero_le'

theorem UpperTheory.V.AlgebraTools.exists_kernel_vector :
    ∀ (K : Type) [Field K] (V : ValuationSubring K) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (z : Matrix ι ι K) (m : ι → K), z.mulVec m = 0 → z.det = 0 →
      ∃ (c : ι) (l : ι → K), l c = 1 ∧ (∀ j, l j ∈ V) ∧ z.mulVec l = 0 ∧ ∀ j, m j = l j * m c := by
  intro K _ V ι _ _ _ z m hm hdet
  have key : ∀ w : ι → K, z.mulVec w = 0 → ∀ c, w c ≠ 0 →
      z.mulVec (fun j => w j / w c) = 0 := by
    intro w hw c _
    have e : (fun j => w j / w c) = (w c)⁻¹ • w := by
      funext j
      simp [div_eq_inv_mul]
    rw [e, Matrix.mulVec_smul, hw, smul_zero]
  by_cases h0 : m = 0
  · obtain ⟨w, hw, hzw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V w hw
    exact ⟨c, fun j => w j / w c, div_self hc, hV, key w hzw c hc, fun j => by simp [h0]⟩
  · obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V m h0
    exact ⟨c, fun j => m j / m c, div_self hc, hV, key m hm c hc,
      fun j => (div_mul_cancel₀ _ hc).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDvrPs
section
open IsLocalRing

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      (p : ℕ) [Fact p.Prime] [CharP A p] [Finite (ResidueField A)] (t : A), Irreducible t →
      ∃ e : PowerSeries (ResidueField A) ≃+* A, e PowerSeries.X = t ∧
        ∀ c, residue A (e (PowerSeries.C c)) = c := by
  intro A _ _ _ _ p _ _ _ t ht
  classical
  haveI : Fintype (ResidueField A) := Fintype.ofFinite _
  have hH : ∀ x y : A, (∀ n : ℕ, x - y ∈ maximalIdeal A ^ n) → x = y := by
    intro x y h
    rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)]
    intro n
    rw [SModEq.sub_mem]
    simpa [Ideal.smul_eq_mul] using h n
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have htm : t ∈ maximalIdeal A := by
    rw [hm]
    exact Ideal.subset_span rfl
  have hpk : CharP (ResidueField A) p := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
    rw [← map_natCast (residue A), CharP.cast_eq_zero, map_zero]
  have hder : ∀ (n : ℕ) (a : A), (n : A) = 0 →
      Polynomial.eval a (Polynomial.derivative (Polynomial.X ^ n - Polynomial.X : Polynomial A))
        = -1 := by
    intro n a hn
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, hn,
      zero_mul, zero_sub]
  obtain ⟨nf, -, hq⟩ := FiniteField.card (ResidueField A) p
  set q := Fintype.card (ResidueField A) with hqdef
  have hq2 : 1 < q := Fintype.one_lt_card
  have hq0 : (q : A) = 0 := by
    rw [hq]
    push_cast
    simp [CharP.cast_eq_zero]
  have hU : ∀ x y : A, x ^ q = x → y ^ q = y → residue A x = residue A y → x = y := by
    intro x y hx hy hxy
    have hz : (x - y) ^ q = x - y := by
      rw [hq, sub_pow_char_pow, ← hq, hx, hy]
    have hzm : x - y ∈ maximalIdeal A := Ideal.Quotient.eq.mp hxy
    rw [← sub_eq_zero]
    have h1 : (x - y) * (1 - (x - y) ^ (q - 1)) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq2.le, hz, sub_self]
    have hu : IsUnit (1 - (x - y) ^ (q - 1)) := by
      apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      exact (mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ hzm _ (by omega))
    exact (mul_eq_zero.mp h1).resolve_right hu.ne_zero
  have hE : ∀ c : ResidueField A, ∃ x : A, x ^ q = x ∧ residue A x = c := by
    intro c
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective c
    have hmon : (Polynomial.X ^ q - Polynomial.X : Polynomial A).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hq2
    have he1 : Polynomial.eval a₀ (Polynomial.X ^ q - Polynomial.X : Polynomial A)
        ∈ maximalIdeal A := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ha₀, FiniteField.pow_card,
        sub_self]
    have he2 : IsUnit (Ideal.Quotient.mk (maximalIdeal A) (Polynomial.eval a₀
        (Polynomial.derivative (Polynomial.X ^ q - Polynomial.X : Polynomial A)))) := by
      rw [hder q a₀ hq0, map_neg, map_one]
      exact isUnit_one.neg
    obtain ⟨a, ha, ham⟩ := HenselianRing.is_henselian (I := maximalIdeal A)
      (Polynomial.X ^ q - Polynomial.X : Polynomial A) hmon a₀ he1 he2
    refine ⟨a, ?_, ?_⟩
    · have h' := ha
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X] at h'
      exact sub_eq_zero.mp h'
    · rw [← ha₀]
      exact Ideal.Quotient.eq.mpr ham
  choose s0 hs0 using hE
  have hsq : ∀ c, s0 c ^ q = s0 c := fun c => (hs0 c).1
  have hsr : ∀ c, residue A (s0 c) = c := fun c => (hs0 c).2
  have hq0' : q ≠ 0 := by omega
  let s : ResidueField A →+* A :=
    { toFun := s0
      map_one' := hU _ _ (hsq 1) (one_pow _) (by rw [hsr, map_one])
      map_mul' := fun a b => hU _ _ (hsq _) (by rw [mul_pow, hsq, hsq])
        (by rw [hsr, map_mul, hsr, hsr])
      map_zero' := hU _ _ (hsq 0) (zero_pow hq0') (by rw [hsr, map_zero])
      map_add' := fun a b => hU _ _ (hsq _) (by rw [hq, add_pow_char_pow, ← hq, hsq, hsq])
        (by rw [hsr, map_add (f := _), hsr, hsr]) }
  have hsr' : ∀ c, residue A (s c) = c := hsr
  have hev : ∀ n (f : PowerSeries (ResidueField A)),
      (PowerSeries.trunc n f).eval₂ s t =
        ∑ i ∈ Finset.range n, s (PowerSeries.coeff i f) * t ^ i := fun n f =>
    PowerSeries.eval₂_trunc_eq_sum_range t s n f
  have key : ∀ n (P Q : Polynomial (ResidueField A)), (∀ i < n, P.coeff i = Q.coeff i) →
      Ideal.Quotient.mk (maximalIdeal A ^ n) (P.eval₂ s t) =
        Ideal.Quotient.mk (maximalIdeal A ^ n) (Q.eval₂ s t) := by
    intro n P Q h
    rw [Ideal.Quotient.eq, ← Polynomial.eval₂_sub]
    obtain ⟨R, hR⟩ := (Polynomial.X_pow_dvd_iff (f := P - Q) (n := n)).mpr
      (fun d hd => by rw [Polynomial.coeff_sub, h d hd, sub_self])
    rw [hR, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n)
  let g : (n : ℕ) → PowerSeries (ResidueField A) →+* A ⧸ maximalIdeal A ^ n := fun n =>
    { toFun := fun f => Ideal.Quotient.mk (maximalIdeal A ^ n) ((PowerSeries.trunc n f).eval₂ s t)
      map_one' := by
        rw [key n _ 1 (fun i hi => ?_), Polynomial.eval₂_one, map_one]
        simp [PowerSeries.coeff_trunc, hi, PowerSeries.coeff_one, Polynomial.coeff_one]
      map_mul' := fun f g' => by
        rw [← map_mul, ← Polynomial.eval₂_mul]
        apply key
        intro i hi
        rw [← PowerSeries.trunc_trunc_mul_trunc, PowerSeries.coeff_trunc, if_pos hi,
          ← Polynomial.coe_mul, Polynomial.coeff_coe]
      map_zero' := by simp [hev]
      map_add' := fun f g' => by simp [hev, add_mul, Finset.sum_add_distrib] }
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (g n) = g m := by
    intro m n hle
    ext f
    show Ideal.Quotient.factorPow (maximalIdeal A) hle
        (Ideal.Quotient.mk _ ((PowerSeries.trunc n f).eval₂ s t)) =
      Ideal.Quotient.mk _ ((PowerSeries.trunc m f).eval₂ s t)
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    apply key
    intro i hi
    simp [PowerSeries.coeff_trunc, hi, lt_of_lt_of_le hi hle]
  let e0 := IsAdicComplete.liftRingHom (maximalIdeal A) g hg
  have hme : ∀ n f, Ideal.Quotient.mk (maximalIdeal A ^ n) (e0 f) = g n f :=
    fun n f => IsAdicComplete.mk_liftRingHom (maximalIdeal A) g hg n f
  have hEq : ∀ n f, e0 f - (PowerSeries.trunc n f).eval₂ s t ∈ maximalIdeal A ^ n :=
    fun n f => Ideal.Quotient.eq.mp (hme n f)
  have hres : ∀ f, residue A (e0 f) = PowerSeries.constantCoeff f := by
    intro f
    have h1 := hEq 1 f
    rw [pow_one, hev, Finset.sum_range_one, pow_zero, mul_one] at h1
    have h2 : residue A (e0 f) = residue A (s (PowerSeries.coeff 0 f)) :=
      Ideal.Quotient.eq.mpr h1
    rw [h2, hsr', PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hmono : ∀ x : A, (∀ n, x ∈ maximalIdeal A ^ (n + 2)) → ∀ n, x ∈ maximalIdeal A ^ n :=
    fun x h n => Ideal.pow_le_pow_right (by omega) (h n)
  have hX : e0 PowerSeries.X = t := by
    apply hH
    apply hmono
    intro n
    have h1 := hEq (n + 2) PowerSeries.X
    have h2 : (PowerSeries.trunc (n + 2) PowerSeries.X).eval₂ s t = t := by
      rw [hev, Finset.sum_range_succ', Finset.sum_range_succ']
      simp [PowerSeries.coeff_X]
    rwa [h2] at h1
  have hinj : Function.Injective e0 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hdec := PowerSeries.X_pow_order_mul_divXPowOrder (f := f)
    have hu : residue A (e0 (PowerSeries.divXPowOrder f)) ≠ 0 := by
      rw [hres]
      exact (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff).not.mpr hne
    have hu' : e0 (PowerSeries.divXPowOrder f) ≠ 0 := fun h => hu (by rw [h, map_zero])
    rw [← hdec, map_mul, map_pow, hX] at hf
    exact mul_ne_zero (pow_ne_zero _ ht.ne_zero) hu' hf
  have hδ : ∀ x : A, ∃ y, y * t = x - s (residue A x) := by
    intro x
    rw [← Ideal.mem_span_singleton', ← hm, ← IsLocalRing.residue_eq_zero_iff, map_sub, hsr',
      sub_self]
  choose δ hδ using hδ
  have hsurj : Function.Surjective e0 := by
    intro x
    let F : PowerSeries (ResidueField A) := PowerSeries.mk fun n => residue A (δ^[n] x)
    have hc : ∀ n, x = (PowerSeries.trunc n F).eval₂ s t + t ^ n * δ^[n] x := by
      intro n
      induction n with
      | zero => simp [hev]
      | succ n ih =>
        rw [hev, Finset.sum_range_succ, ← hev, Function.iterate_succ_apply']
        have hcn : PowerSeries.coeff n F = residue A (δ^[n] x) := PowerSeries.coeff_mk _ _
        rw [hcn]
        linear_combination ih - t ^ n * hδ (δ^[n] x)
    refine ⟨F, hH _ _ fun n => ?_⟩
    have h1 := hEq n F
    have h2 : e0 F - x = (e0 F - (PowerSeries.trunc n F).eval₂ s t) - t ^ n * δ^[n] x := by
      linear_combination -(hc n)
    rw [h2]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n))
  refine ⟨RingEquiv.ofBijective e0 ⟨hinj, hsurj⟩, hX, fun c => ?_⟩
  show residue A (e0 (PowerSeries.C c)) = c
  rw [hres, PowerSeries.constantCoeff_C]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaSuppBc
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.mem_support_baseChange :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      (Q : PrimeSpectrum B), Q ∈ Module.support B (TensorProduct R B M) ↔
        PrimeSpectrum.comap (algebraMap R B) Q ∈ Module.support R M := by
  intro R B _ _ _ M _ _ _ Q
  let p := PrimeSpectrum.comap (algebraMap R B) Q
  let φ := Ideal.ResidueField.mapₐ p.asIdeal Q.asIdeal (Algebra.ofId R B) rfl
  letI : Algebra p.asIdeal.ResidueField Q.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField Q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B Q.asIdeal.ResidueField
      Q.asIdeal.ResidueField M).nontrivial_congr,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField
      Q.asIdeal.ResidueField Q.asIdeal.ResidueField M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CardEqPowLength
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field {A X : Type} [CommRing A] [IsLocalRing A] [AddCommGroup X] [Module A X] [IsSimpleModule A X] : Nonempty (X ≃ ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)
  have : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
  subst this
  exact ⟨e.toEquiv⟩

private theorem UpperTheory.V.AlgebraTools.card_finite_length_module {A : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] {X : Type} [AddCommGroup X] [Module A X] (h : IsFiniteLength A X) :
    Finite X ∧ Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨Finite.of_subsingleton, ?_⟩
    rw [Module.length_eq_zero]
    simp [Nat.card_eq_one_iff_unique]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨e⟩ := UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field (A := A) (X := M ⧸ N)
    have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField A) := Nat.card_congr e
    have hNt : Module.length A N ≠ ⊤ := Module.length_ne_top_iff.mpr hN
    have hlen : Module.length A M = Module.length A N + 1 := by
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]
    have hc : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
    have hq0 : Nat.card (ResidueField A) ≠ 0 := Nat.card_pos.ne'
    have hM : Nat.card M = Nat.card (ResidueField A) ^ ((Module.length A N).toNat + 1) := by
      rw [hc, hq, hcard, pow_succ, mul_comm]
    refine ⟨Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hq0), ?_⟩
    rw [hM, hlen, ENat.toNat_add hNt ENat.one_ne_top]
    simp

theorem UpperTheory.V.AlgebraTools.card_eq_pow_length :
    ∀ {A X : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] [AddCommGroup X] [Module A X], (Finite X ↔ Module.length A X ≠ ⊤) ∧ (Finite X → Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat) := by
  intro A X _ _ _ _ _
  have key : Finite X → Module.length A X ≠ ⊤ := fun h => by
    haveI := h
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, isArtinian_of_finite⟩)
  refine ⟨⟨key, fun h => (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp h)).1⟩, fun h => ?_⟩
  exact (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp (key h))).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ComapPowLe
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.comap_pow_le :
    ∀ {A M M' : Type} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (I : Ideal A) (f : M →ₗ[A] M'), ∃ c : ℕ, ∀ m : ℕ, (I ^ (m + c) • (⊤ : Submodule A M')).comap f ≤ LinearMap.ker f ⊔ I ^ m • (⊤ : Submodule A M) := by
  intro A M M' _ _ _ _ _ _ _ I f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun m x hx => ?_⟩
  have h1 : f x ∈ I ^ (m + k) • (⊤ : Submodule A M') ⊓ LinearMap.range f :=
    ⟨hx, LinearMap.mem_range_self f x⟩
  rw [hk (m + k) (Nat.le_add_left k m), Nat.add_sub_cancel] at h1
  have h2 : f x ∈ I ^ m • LinearMap.range f :=
    Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  have h3 : x ∈ ((I ^ m • (⊤ : Submodule A M)).map f).comap f := h2
  rw [Submodule.comap_map_eq, sup_comm] at h3
  exact h3
end

