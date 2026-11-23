module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulMemIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdPowMemOfLe
section
open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem mem_std {x : Fin r → K} :
    x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔
      ∀ i, x i ∈ (algebraMap O K).range := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      rw [Pi.basisFun_apply, Pi.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero => intro i; exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz => intro i; exact add_mem (hy i) (hz i)
    | smul a y _ hy =>
      intro i
      rw [Pi.smul_apply, Algebra.smul_def]
      exact mul_mem ⟨a, rfl⟩ (hy i)
  · intro hx
    choose a ha using hx
    have : x = ∑ i, a i • Pi.basisFun K (Fin r) i := by
      funext j
      simp [Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem hf_mulVec (cK : K ≃+* K) (J g : Matrix (Fin r) (Fin r) K)
    (hU : (g.map cK).transpose * J * g = J) (x y : Fin r → K) :
    hf cK J (g.mulVec x) (g.mulVec y) = hf cK J x y := by
  have e1 : (fun i => cK (g.mulVec x i)) = (g.map cK).mulVec (fun i => cK (x i)) := by
    funext i
    exact RingHom.map_mulVec cK.toRingHom g x i
  unfold hf
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hU]

theorem std_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    (J : Matrix (Fin r) (Fin r) O) (hJ : IsUnit J.det) :
    IsSD cK (J.map (algebraMap O K)) (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) := by
  classical
  intro x
  constructor
  · intro hx y hy
    rw [mem_std] at hx hy
    unfold hf
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Subring.sum_mem _ fun i _ => mul_mem (conj_mem_range c cK hcK (hx i)) ?_
    exact Subring.sum_mem _ fun j _ => mul_mem ⟨_, rfl⟩ (hy j)
  · intro h
    rw [mem_std]
    set w : Fin r → K := Matrix.vecMul (fun i => cK (x i)) (J.map (algebraMap O K)) with hw
    have hwR : ∀ j, w j ∈ (algebraMap O K).range := by
      intro j
      have hej : Pi.single j (1 : K) ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) :=
        Submodule.subset_span ⟨j, Pi.basisFun_apply K (Fin r) j⟩
      have := h _ hej
      unfold hf at this
      rwa [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    have hJJ : J.map (algebraMap O K) * J⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]
    have hx' : (fun i => cK (x i)) = Matrix.vecMul w (J⁻¹.map (algebraMap O K)) := by
      rw [hw, Matrix.vecMul_vecMul, hJJ, Matrix.vecMul_one]
    intro i
    have hi : cK (x i) ∈ (algebraMap O K).range := by
      rw [show cK (x i) = (fun i => cK (x i)) i from rfl, hx']
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
      exact Subring.sum_mem _ fun j _ => mul_mem (hwR j) ⟨_, rfl⟩
    rw [← hc2 (x i)]
    exact conj_mem_range c cK hcK hi

theorem exists_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) (y : K) :
    ∃ k : ℕ, algebraMap O K (ϖ ^ k) * y ∈ (algebraMap O K).range := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  refine ⟨k, u * a, ?_⟩
  have hb' : algebraMap O K b ≠ 0 := by
    intro h; exact hb0 (IsFractionRing.injective O K (by simpa using h))
  rw [← hu, map_mul, map_mul]
  field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem std_pow_mem_of_le {ϖ : O} {x : Fin r → K} {k : Fin r → ℕ}
    (hk : ∀ i, algebraMap O K (ϖ ^ k i) * x i ∈ (algebraMap O K).range) :
    (ϖ ^ (∑ i, k i)) • x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) := by
  rw [mem_std]
  intro i
  have hle : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [Pi.smul_apply, Algebra.smul_def, ← Nat.sub_add_cancel hle, pow_add, map_mul, mul_assoc]
  exact mul_mem ⟨_, rfl⟩ (hk i)

theorem idx_std {ϖ : O} (hϖ : Irreducible ϖ) :
    idx ϖ (Submodule.span O (Set.range (Pi.basisFun K (Fin r))) : Submodule O (Fin r → K)) =
      Nat.card (IsLocalRing.ResidueField O) ^ r := by
  classical
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r)))
  have hex : ∀ (x : L0.toAddSubgroup) (i : Fin r), ∃ a : O, algebraMap O K a = (x : Fin r → K) i :=
    fun x i => mem_std.1 x.2 i
  choose a ha using hex
  have hadd : ∀ x y i, a (x + y) i = a x i + a y i := by
    intro x y i
    apply IsFractionRing.injective O K
    rw [map_add (f := _), ha, ha, ha]; rfl
  let ψ : L0.toAddSubgroup →+ (Fin r → IsLocalRing.ResidueField O) :=
    AddMonoidHom.mk' (fun x i => IsLocalRing.residue O (a x i)) (by
      intro x y; funext i; simp [hadd])
  have hker : (L0.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
      L0.toAddSubgroup = ψ.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (x : Fin r → K) ∈ L0.map _ ↔ (fun i => IsLocalRing.residue O (a x i)) = 0
    rw [funext_iff]
    simp only [Pi.zero_apply, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy, hyx⟩ i
      obtain ⟨b, hb⟩ := mem_std.1 hy i
      refine ⟨b, IsFractionRing.injective O K ?_⟩
      rw [ha, ← hyx, map_mul, hb]
      simp [Algebra.smul_def]
    · intro h
      choose b hb using h
      refine ⟨fun i => algebraMap O K (b i), mem_std.2 fun i => ⟨b i, rfl⟩, ?_⟩
      funext i
      show (ϖ • (fun i => algebraMap O K (b i))) i = (x : Fin r → K) i
      rw [Pi.smul_apply, Algebra.smul_def, ← map_mul, ← hb, ha]
  have hsurj : Function.Surjective ψ := by
    intro z
    choose b hb using fun i => IsLocalRing.residue_surjective (z i)
    have hm : (fun i => algebraMap O K (b i)) ∈ L0.toAddSubgroup := mem_std.2 fun i => ⟨b i, rfl⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    funext i
    change IsLocalRing.residue O (a ⟨_, hm⟩ i) = z i
    have : a ⟨_, hm⟩ i = b i := IsFractionRing.injective O K (by rw [ha])
    rw [this, hb]
  unfold idx
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r),
    Fintype.card_fin]

end GlobalTheory.HermNbr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableInvAbsNormPrimesOfNotPrimeNorm
section
open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory

open NumberField IsDedekindDomain in
open scoped Classical in
private lemma exists_prime_liesOver_absNorm_eq_pow (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) ∧
      ∃ f : ℕ, Ideal.absNorm P.asIdeal = q ^ f := by
  set I : Ideal ℤ := P.asIdeal.under ℤ with hI
  have hN : (Ideal.absNorm P.asIdeal : ℤ) ∈ I := by
    rw [hI, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem P.asIdeal
  have hN0 : (Ideal.absNorm P.asIdeal : ℤ) ≠ 0 := by
    have := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
    omega
  have hIbot : I ≠ ⊥ := fun h => hN0 (by simpa [h] using hN)
  have hprime := Submodule.IsPrincipal.prime_generator_of_isPrime I hIbot
  set g := Submodule.IsPrincipal.generator I
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Int.span_natAbs, Ideal.span_singleton_generator]
  · have hpr : Prime ((g.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hprime.abs
    haveI : P.asIdeal.LiesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) :=
      ⟨by rw [Int.span_natAbs, Ideal.span_singleton_generator]⟩
    exact ⟨_, (Ideal.absNorm_eq_pow_inertiaDeg P.asIdeal hpr).trans (by rw [Int.natAbs_natCast])⟩


open NumberField IsDedekindDomain in
open scoped Classical in
theorem _root_.GlobalTheory.summable_inv_absNorm_of_not_prime :
    ∀ (K : Type) [Field K] [NumberField K],
      Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} =>
        ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  intro K _ _
  choose q hq hlies f hf using exists_prime_liesOver_absNorm_eq_pow K
  set d := Module.finrank ℚ K
  have hfib : ∀ (T : Finset {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime})
      (r : ℕ), (T.filter fun P => q P.1 = r).card ≤ d := by
    intro T r
    by_cases hr : ∃ P ∈ T, q P.1 = r
    · obtain ⟨P₀, -, rfl⟩ := hr
      have hspan : Ideal.span {((q P₀.1 : ℕ) : ℤ)} ≠ ⊥ := by
        simpa using (hq P₀.1).ne_zero
      haveI hsp : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by simpa using (hq P₀.1).ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp (hq P₀.1))
      haveI : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsMaximal := hsp.isMaximal hspan
      calc (T.filter fun P => q P.1 = q P₀.1).card
          ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((q P₀.1 : ℕ) : ℤ)}) (𝓞 K)).card := by
            refine Finset.card_le_card_of_injOn (fun P => P.1.asIdeal) ?_ ?_
            · intro P hP
              rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hspan]
              have hPq := (Finset.mem_filter.mp hP).2
              haveI := hlies P.1
              exact ⟨P.1.isPrime, by rw [← hPq]; infer_instance⟩
            · intro P _ P' _ h
              exact Subtype.ext (HeightOneSpectrum.ext h)
        _ ≤ d := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hspan
    · push_neg at hr
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr hr)]
      exact Nat.zero_le _
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  refine summable_of_sum_le (c := d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) (fun P => by positivity) ?_
  intro T
  have hle : ∀ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ ≤ 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := by
    intro P _
    have h2 := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P.1
    have hf2 : 2 ≤ f P.1 := by
      rcases Nat.lt_or_ge (f P.1) 2 with h | h
      · interval_cases hfP : f P.1
        · rw [hf P.1, hfP] at h2; simp at h2
        · exact absurd (by rw [hf P.1, hfP, pow_one]; exact hq P.1) P.2
      · exact h
    rw [one_div]
    apply inv_anti₀ (by have := (hq P.1).pos; positivity)
    rw [hf P.1]
    exact_mod_cast Nat.pow_le_pow_right (hq P.1).pos hf2
  calc ∑ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹
      ≤ ∑ P ∈ T, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum hle
    _ = ∑ r ∈ T.image (fun P => q P.1), ∑ P ∈ T with q P.1 = r, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ r ∈ T.image (fun P => q P.1),
          ((T.filter fun P => q P.1 = r).card : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ r ∈ T.image (fun P => q P.1), (d : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun r _ => ?_
        gcongr
        exact_mod_cast hfib T r
    _ = d * ∑ r ∈ T.image (fun P => q P.1), 1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
        gcongr
        exact hsum.sum_le_tsum _ (fun n _ => by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtension
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

def intMap (hU : IsUnrExt K K' d φ) : K.O →+* K'.O where
  toFun a := Classical.choose (exists_int_image hU a)
  map_one' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 1)]; simp)
  map_mul' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a * b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_mul, h2, h3])
  map_zero' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 0)]; simp)
  map_add' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a + b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_add (f := _), h2, h3])

theorem intMap_spec (hU : IsUnrExt K K' d φ) (a : K.O) :
    algebraMap K'.O K'.E (intMap hU a) = φ (algebraMap K.O K.E a) :=
  Classical.choose_spec (exists_int_image hU a)

theorem intMap_injective (hU : IsUnrExt K K' d φ) : Function.Injective (intMap hU) := by
  intro a b h
  apply IsFractionRing.injective K.O K.E
  apply φ.injective
  rw [← intMap_spec hU, ← intMap_spec hU, h]

theorem val_mul_ne (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]; ring

theorem val_irreducible (K : UQ) {ϖ : K.O} (h : Irreducible ϖ) : val K.O (algebraMap K.O K.E ϖ) = 1 := by
  unfold val
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ h.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h), WithZero.log_exp]; rfl

theorem val_pow_ne (K : UQ) {x : K.E} (hx : x ≠ 0) (n : ℕ) : val K.O (x ^ n) = n * val K.O x := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_ne K (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem val_isUnit (K : UQ) {u : K.O} (hu : IsUnit u) : val K.O (algebraMap K.O K.E u) = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 : (algebraMap K.O K.E (w : K.O)) ≠ 0 := by simp
  have h2 : (algebraMap K.O K.E ((w⁻¹ : K.Oˣ) : K.O)) ≠ 0 := by simp
  have h := val_mul_ne K h1 h2
  rw [← map_mul, Units.mul_inv, map_one] at h
  have h3 := val_algebraMap_nonneg K (w : K.O)
  have h4 := val_algebraMap_nonneg K ((w⁻¹ : K.Oˣ) : K.O)
  have h5 : val K.O (1 : K.E) = 0 := by simp [val]
  omega

theorem irreducible_of_val_one (K : UQ) {x : K.O} (hx : val K.O (algebraMap K.O K.E x) = 1) :
    Irreducible x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp [val] at hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hu0 : algebraMap K.O K.E (u : K.O) ≠ 0 := by simp
  rw [map_mul, map_pow, val_mul_ne K hu0 (pow_ne_zero _ hϖ0), val_pow_ne K hϖ0,
    val_isUnit K u.isUnit, val_irreducible K hϖ] at hx
  have hn : n = 1 := by omega
  subst hn
  rw [pow_one]
  exact (irreducible_units_mul u).2 hϖ

theorem map_maximalIdeal (hU : IsUnrExt K K' d φ) :
    Ideal.map (intMap hU) (IsLocalRing.maximalIdeal K.O) = IsLocalRing.maximalIdeal K'.O := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have h1 := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have h2 : Irreducible (intMap hU ϖ) :=
    irreducible_of_val_one K' (by rw [intMap_spec, hU.2.2.1, val_irreducible K hϖ])
  rw [h1, Ideal.map_span, Set.image_singleton,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 h2]


open scoped nonZeroDivisors in
theorem exists_trace_unit_of_span (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ)
    (hB : ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i)) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.O := (intMap hU).toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K.O K'.O K'.E := IsScalarTower.of_algebraMap_eq fun a => (intMap_spec hU a).symm
  have hmap : ∀ a : K.O, algebraMap K.O K'.O a = intMap hU a := fun _ => rfl

  obtain ⟨u, hu⟩ := hB
  haveI hfin : Module.Finite K.O K'.O := by
    classical
    refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hmap, intMap_spec]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  haveI : FaithfulSMul K.O K'.O :=
    (faithfulSMul_iff_algebraMap_injective K.O K'.O).2 (intMap_injective hU)
  haveI : Module.Free K.O K'.O := Module.free_of_finite_type_torsion_free'

  haveI : IsLocalization (Algebra.algebraMapSubmonoid K'.O K.O⁰) K'.E := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have hφϖ : φ (algebraMap K.O K.E ϖ) ≠ 0 := by simpa using hϖ0
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := hy
      refine IsUnit.mk0 _ ?_
      change algebraMap K'.O K'.E (intMap hU r) ≠ 0
      rw [intMap_spec]
      simpa using nonZeroDivisors.ne_zero hr
    · intro z
      by_cases hz : z = 0
      · exact ⟨⟨0, 1⟩, by simp [hz]⟩
      obtain ⟨s, hs⟩ := mem_range_of_val_nonneg K'
        (z * φ (algebraMap K.O K.E ϖ) ^ (-(val K'.O z)).toNat) (by
          rw [val_mul_ne K' hz (pow_ne_zero _ hφϖ), val_pow_ne K' hφϖ, hU.2.2.1, val_irreducible K hϖ]
          omega)
      refine ⟨⟨s, ⟨algebraMap K.O K'.O (ϖ ^ (-(val K'.O z)).toNat),
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨_, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) _⟩⟩⟩, ?_⟩
      change z * algebraMap K'.O K'.E (intMap hU (ϖ ^ (-(val K'.O z)).toNat)) = algebraMap K'.O K'.E s
      rw [hs, intMap_spec, map_pow, map_pow]
    · intro x y h
      exact ⟨1, by rw [IsFractionRing.injective K'.O K'.E h]⟩

  have hpS : Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O) =
      IsLocalRing.maximalIdeal K'.O := map_maximalIdeal hU
  haveI hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hpS]; infer_instance
  letI : Field (K.O ⧸ IsLocalRing.maximalIdeal K.O) := Ideal.Quotient.field _
  letI : Field (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Ideal.Quotient.field _
  haveI : Finite (K'.O ⧸ IsLocalRing.maximalIdeal K'.O) := K'.fin
  haveI : Finite (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Finite.of_equiv _ (Ideal.quotEquivOfEq hpS).symm.toEquiv
  haveI : Finite (K.O ⧸ IsLocalRing.maximalIdeal K.O) := K.fin
  haveI : FiniteDimensional (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  haveI : Algebra.IsSeparable (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (K.O ⧸ IsLocalRing.maximalIdeal K.O)
    (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have htr := Algebra.trace_quotient_mk (R := K.O) (S := K'.O) y
  rw [hz] at htr
  refine ⟨y, Algebra.trace K.O K'.O y, ?_, ?_⟩
  · by_contra h
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal K.O) (Algebra.trace K.O K'.O y) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h0] at htr
    exact one_ne_zero htr
  · exact Algebra.trace_localization K.O K.O⁰ (Rₘ := K.E) (Sₘ := K'.E) y

theorem exists_trace_unit (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  exists_trace_unit_of_span K K' d φ hU (exists_int_basis_of_unr K K' d φ hU)

end GlobalTheory.UnitLemma.Unr
end
end

