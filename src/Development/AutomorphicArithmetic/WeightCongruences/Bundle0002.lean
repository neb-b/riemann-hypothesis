module

public import Mathlib
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WeightCongruences.DvdNormSubOneOfIdempotentInterpolationRelNormOne
section
open NumberField IsDedekindDomain

private theorem prod_interp_mod {Ω ι : Type*} [CommRing Ω] (n : ℕ) (e t : Ω) (he : e * e - e = n * t)
    (hei : IsIntegral ℤ e) (hti : IsIntegral ℤ t) (f g : ι → Ω) (hf : ∀ i, IsIntegral ℤ (f i))
    (hg : ∀ i, IsIntegral ℤ (g i)) (s : Finset ι) :
    ∃ z, IsIntegral ℤ z ∧ ∏ i ∈ s, (e * f i + (1 - e) + n * g i) = e * ∏ i ∈ s, f i + (1 - e) + n * z := by
  classical
  have hn : IsIntegral ℤ (n : Ω) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := (n : ℤ)))
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z, hz, hprod⟩ := ih
    set P := ∏ i ∈ s, f i with hP
    have hPi : IsIntegral ℤ P := IsIntegral.prod _ fun i _ => hf i
    refine ⟨t * f a * P - t * f a - t * P + t + g a * (e * P + (1 - e)) +
      z * (e * f a + (1 - e)) + n * g a * z, ?_, ?_⟩
    · have h1e : IsIntegral ℤ (1 - e) := isIntegral_one.sub hei
      exact ((((((hti.mul (hf a)).mul hPi).sub (hti.mul (hf a))).sub (hti.mul hPi)).add hti).add
        ((hg a).mul ((hei.mul hPi).add h1e))).add (hz.mul ((hei.mul (hf a)).add h1e)) |>.add
        ((hn.mul (hg a)).mul hz)
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, hprod]
      linear_combination (f a * P - f a - P + 1) * he

private theorem descend_mod {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n : ℕ) (a : F) (z : Ω)
    (hz : IsIntegral ℤ z) (h : algebraMap F Ω a = 1 + n * z) :
    ∃ w : F, IsIntegral ℤ w ∧ a = 1 + n * w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, isIntegral_zero, ?_⟩
    apply (algebraMap F Ω).injective
    simpa using h
  · have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨(a - 1) / n, ?_, by field_simp; ring⟩
    have hmap : algebraMap F Ω ((a - 1) / n) = z := by
      have hnΩ : (n : Ω) ≠ 0 := by
        rw [← map_natCast (algebraMap F Ω)]
        exact (map_ne_zero _).mpr hnF
      rw [map_div₀, map_sub, map_one, map_natCast, h]
      field_simp
      ring
    rw [← isIntegral_algebraMap_iff (B := Ω), hmap]
    exact hz

theorem UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one :
    ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (n : ℕ) (e t δ y : 𝓞 E), (e : E) ∈ K → e * e - e = n * t →
      Algebra.norm K (δ : E) = 1 → (n : ℤ) ∣ Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) - 1 := by
  intro E _ _ K n e t δ y heK he hδ
  classical
  let Ω := AlgebraicClosure E
  have hint : ∀ u : 𝓞 E, IsIntegral ℤ (u : E) := fun u => u.2
  have hintΩ : ∀ (u : 𝓞 E) (σ : E →ₐ[K] Ω), IsIntegral ℤ (σ u) := fun u σ =>
    (hint u).map (σ.restrictScalars ℚ).toRingHom.toIntAlgHom
  have hσe : ∀ σ : E →ₐ[K] Ω, σ (e : E) = algebraMap E Ω e := by
    intro σ
    have h := σ.commutes (⟨e, heK⟩ : K)
    rw [IsScalarTower.algebraMap_apply K E Ω] at h
    exact h
  have heE : ((e : E) * e - e) = n * (t : E) := by
    have h := congrArg (fun u : 𝓞 E => (u : E)) he
    simpa using h
  have heΩ : algebraMap E Ω e * algebraMap E Ω e - algebraMap E Ω e = n * algebraMap E Ω t := by
    have h := congrArg (algebraMap E Ω) heE
    simpa using h
  obtain ⟨z, hz, hprod⟩ := prod_interp_mod n (algebraMap E Ω e) (algebraMap E Ω t) heΩ
    ((hint e).map (IsScalarTower.toAlgHom ℤ E Ω)) ((hint t).map (IsScalarTower.toAlgHom ℤ E Ω))
    (fun σ : E →ₐ[K] Ω => σ δ) (fun σ => σ y) (fun σ => hintΩ δ σ) (fun σ => hintΩ y σ) Finset.univ
  have hδΩ : ∏ σ : E →ₐ[K] Ω, σ δ = 1 := by
    rw [← Algebra.norm_eq_prod_embeddings, hδ, map_one]
  have hK : algebraMap K Ω (Algebra.norm K ((e * δ + (1 - e) + n * y : 𝓞 E) : E)) = 1 + n * z := by
    rw [Algebra.norm_eq_prod_embeddings]
    have hσ : ∀ σ : E →ₐ[K] Ω, σ ((e * δ + (1 - e) + n * y : 𝓞 E) : E) =
        algebraMap E Ω e * σ δ + (1 - algebraMap E Ω e) + n * σ y := by
      intro σ
      push_cast
      rw [map_add (f := _), map_add (f := _), map_mul, map_sub, map_one, map_mul, map_natCast, hσe]
    simp_rw [hσ]
    rw [hprod, hδΩ]
    ring
  obtain ⟨w, hw, hwK⟩ := descend_mod n _ z hz hK
  let Ω₂ := AlgebraicClosure K
  obtain ⟨z₂, hz₂, hprod₂⟩ := prod_interp_mod (Ω := Ω₂) n 1 0 (by simp) isIntegral_one isIntegral_zero
    (fun _ : K →ₐ[ℚ] Ω₂ => 1) (fun τ => τ w) (fun _ => isIntegral_one)
    (fun τ => hw.map τ.toRingHom.toIntAlgHom) Finset.univ
  simp only [one_mul, sub_self, add_zero, Finset.prod_const_one] at hprod₂
  have hQ : algebraMap ℚ Ω₂ (Algebra.norm ℚ (1 + n * w)) = 1 + n * z₂ := by
    rw [Algebra.norm_eq_prod_embeddings]
    simp_rw [map_add (f := _), map_one, map_mul, map_natCast]
    exact hprod₂
  obtain ⟨w₂, hw₂, hw₂Q⟩ := descend_mod n _ z₂ hz₂ hQ
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hw₂
  have hnorm : ((Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) : ℤ) : ℚ) = 1 + n * m := by
    rw [Algebra.coe_norm_int, ← Algebra.norm_norm (S := K), hwK, hw₂Q, ← hm]
    simp
  have hZ : Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) = 1 + n * m := by
    exact_mod_cast hnorm
  exact ⟨m, by rw [hZ]; ring⟩
end

-- bundled from Development.AutomorphicArithmetic.WeightCongruences.ExistsShiftWeightCongruenceLtTorsionOrder
section
open NumberField IsDedekindDomain

theorem UpperTheory.exists_shift_weightCongruence_lt_torsionOrder :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (φ : ι → E →+* K) (e : ι → ℤ) (i₀ : ι),
      ∃ s : ℕ, s < NumberField.Units.torsionOrder E ∧ UpperTheory.MU φ (fun i => e i + if i = i₀ then (s : ℤ) else 0) := by
  intro E K _ _ _ ι _ _ φ e i₀
  obtain ⟨μ, hμ⟩ : ∃ μ : NumberField.Units.torsion E,
      orderOf μ = NumberField.Units.torsionOrder E :=
    IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers E) E)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : E, IsPrimitiveRoot ζ (NumberField.Units.torsionOrder E) := ⟨_, hμ⟩
  have hw0 : 0 < NumberField.Units.torsionOrder E := NumberField.Units.torsionOrder_pos E
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hw0.ne'
  have hψ : IsPrimitiveRoot (φ i₀ ζ) (NumberField.Units.torsionOrder E) :=
    hζ.map_of_injective (φ i₀).injective
  have hc0 : (∏ i, (φ i ζ) ^ e i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ((map_ne_zero _).mpr hζ0)
  have hcw : ((∏ i, (φ i ζ) ^ e i)⁻¹) ^ (NumberField.Units.torsionOrder E) = 1 := by
    rw [inv_pow, ← Finset.prod_pow]
    have h1 : ∀ i ∈ (Finset.univ : Finset ι),
        ((φ i ζ) ^ e i) ^ (NumberField.Units.torsionOrder E) = 1 := by
      intro i _
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow,
        hζ.pow_eq_one, map_one, one_zpow]
    rw [Finset.prod_eq_one h1, inv_one]
  obtain ⟨s, hs, hsc⟩ := hψ.eq_pow_of_pow_eq_one hcw
  refine ⟨s, hs, ?_⟩
  have key : ∏ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0) = 1 := by
    have hsplit : ∀ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0) =
        (φ i ζ) ^ e i * (if i = i₀ then (φ i ζ) ^ s else 1) := by
      intro i
      rw [zpow_add₀ ((map_ne_zero _).mpr hζ0)]
      split_ifs <;> simp
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _), hsc,
      mul_inv_cancel₀ hc0]
  intro z hz
  obtain ⟨m, hm, hzm⟩ := hz
  have hzw : z ^ (NumberField.Units.torsionOrder E) = 1 := by
    have hpos : 0 < orderOf z :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hzm⟩)
    haveI : NeZero (orderOf z) := ⟨hpos.ne'⟩
    obtain ⟨k, hk⟩ :=
      NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.orderOf z)
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hzw
  calc ∏ i, (φ i (ζ ^ j)) ^ (e i + if i = i₀ then (s : ℤ) else 0)
      = (∏ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0)) ^ j := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    _ = 1 := by rw [key, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.WeightCongruences.IffNum
section
namespace UpperTheory.MUQ

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {φ : ι → E →+* K} {e : ι → ℚ}

theorem num (h : MUQ φ e) : MU φ (fun i => (e i).num) := by
  obtain ⟨a, ha, hMU⟩ := h
  have : (fun i => (e i).num) = a := by
    funext i
    rw [ha i, Rat.num_intCast]
  rw [this]
  exact hMU

end UpperTheory.MUQ
end

-- bundled from Development.AutomorphicArithmetic.WeightCongruences.NormRootOfUnityQuadraticSubfield
section
open NumberField IntermediateField

namespace UpperTheory.RootOfUnityNormQuadraticSubfield
open Polynomial

private lemma minpoly_eq {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (hc : ∀ b : F, b ^ 2 ≠ c) :
    minpoly F t = X ^ 2 - C c := by
  symm
  refine minpoly.eq_of_irreducible_of_monic
    (X_pow_sub_C_irreducible_of_prime Nat.prime_two hc) ?_ (monic_X_pow_sub_C c two_ne_zero)
  simp [ht]

private lemma isInt {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) : IsIntegral F t :=
  ⟨X ^ 2 - C c, monic_X_pow_sub_C c two_ne_zero, by simp [ht]⟩

private lemma finrank_eq {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (hc : ∀ b : F, b ^ 2 ≠ c) :
    Module.finrank F F⟮t⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank (isInt t c ht), minpoly_eq t c ht hc,
    natDegree_X_pow_sub_C _]

private lemma repr_mem {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (x : E) (hx : x ∈ F⟮t⟯) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * t :=
  _root_.UpperTheory.Reformulated.B.ReprMem.repr_mem t c ht x hx

private lemma sq_cases {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (t : E) (c : F)
    (ht : t ^ 2 = algebraMap F E c) (hc : ∀ b : F, b ^ 2 ≠ c) (x : E) (hx : x ∈ F⟮t⟯) (e : F)
    (he : x ^ 2 = algebraMap F E e) : (∃ a : F, e = a ^ 2) ∨ ∃ b : F, e = c * b ^ 2 := by
  obtain ⟨a, b, rfl⟩ := repr_mem t c ht x hx
  have inj := (algebraMap F E).injective
  by_cases ha : a = 0
  · right
    refine ⟨b, inj ?_⟩
    rw [← he, ha, map_mul, map_pow, ← ht, map_zero]; ring
  by_cases hb : b = 0
  · left
    refine ⟨a, inj ?_⟩
    rw [← he, hb, map_pow, map_zero]; ring
  exfalso
  have h2 : (2 * a * b : F) ≠ 0 := by simp [ha, hb]
  apply hc ((e - a ^ 2 - b ^ 2 * c) / (2 * a * b))
  apply inj
  rw [← ht, map_pow]
  congr 1
  have h3 : algebraMap F E (2 * a * b) ≠ 0 := by
    rwa [Ne, map_eq_zero]
  rw [map_div₀, div_eq_iff h3]
  simp only [map_sub, map_mul, map_pow, ← he, ← ht, map_ofNat]
  ring

private lemma rat_nsq (d c : ℕ) (hd : d.Prime) (hc : 0 < c) (hcd : c < d) (b : ℚ) :
    (c : ℚ) ≠ d * b ^ 2 := by
  intro h
  have h1 : IsSquare ((c * d : ℕ) : ℚ) := ⟨d * b, by push_cast; rw [h]; ring⟩
  rw [Rat.isSquare_natCast_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have h2 : d ∣ k := by
    have : d ∣ k * k := ⟨c, by rw [← hk]; ring⟩
    exact (hd.dvd_mul.mp this).elim id id
  obtain ⟨l, rfl⟩ := h2
  have h3 : c = d * (l * l) := by
    apply Nat.eq_of_mul_eq_mul_right hd.pos
    rw [hk]; ring
  exact absurd (Nat.le_of_dvd hc ⟨_, h3⟩) (by omega)

private lemma exists_neg_one {R : Type} [Field R] (a : ℕ) :
    ∀ y : R, y ^ 2 ^ a = 1 → y ≠ 1 → ∃ j : ℕ, y ^ j = -1 := by
  induction a with
  | zero => intro y h h'; simp at h; exact absurd h h'
  | succ a ih =>
    intro y h h'
    by_cases h2 : y ^ 2 = 1
    · exact ⟨1, by simpa [h'] using (sq_eq_one_iff.mp h2)⟩
    · obtain ⟨j, hj⟩ := ih (y ^ 2) (by rw [← pow_mul, ← pow_succ', h]) h2
      exact ⟨2 * j, by rw [pow_mul, hj]⟩

section
variable {E : Type} [Field E] [NumberField E] (s : E) (d : ℕ) (hd : d.Prime) (h3 : 3 < d)
  (hs : s ^ 2 = -(d : E))
include hd h3 hs

omit hd in
private lemma d_nsq : ∀ b : ℚ, b ^ 2 ≠ -(d : ℚ) := by
  intro b h
  have : (3 : ℚ) < d := by exact_mod_cast h3
  nlinarith [sq_nonneg b]

omit hd h3 in
private lemma hs' : s ^ 2 = algebraMap ℚ E (-(d : ℚ)) := by simp [hs]

private lemma neg_nsq (c : ℕ) (hc : 0 < c) (hc3 : c ≤ 3) (k : ℚ⟮s⟯) : k ^ 2 ≠ -(c : ℚ⟮s⟯) := by
  intro h
  have h1 : (k : E) ^ 2 = algebraMap ℚ E (-(c : ℚ)) := by
    have := congrArg (fun x : ℚ⟮s⟯ => (x : E)) h
    simpa using this
  have hc' : (0 : ℚ) < c := by exact_mod_cast hc
  rcases sq_cases s _ (hs' s d hs) (d_nsq s d h3 hs) k k.2 _ h1 with ⟨a, ha⟩ | ⟨b, hb⟩
  · nlinarith [sq_nonneg a]
  · exact rat_nsq d c hd hc (by omega) b (by linarith)

private lemma two_nsq (k : ℚ⟮s⟯) : k ^ 2 ≠ 2 := by
  intro h
  have h1 : (k : E) ^ 2 = algebraMap ℚ E 2 := by
    have := congrArg (algebraMap ℚ⟮s⟯ E) h
    rw [map_pow, map_ofNat] at this
    rw [map_ofNat]
    exact this
  have hd' : (3 : ℚ) < d := by exact_mod_cast h3
  rcases sq_cases s _ (hs' s d hs) (d_nsq s d h3 hs) k k.2 _ h1 with ⟨a, ha⟩ | ⟨b, hb⟩
  · refine rat_nsq 2 1 Nat.prime_two one_pos one_lt_two (a / 2) ?_
    push_cast
    nlinarith
  · nlinarith [sq_nonneg b]

private lemma odd_root (w : ℚ⟮s⟯) (o : ℕ) (ho : Odd o) (hw : w ^ o = 1) : w = 1 := by
  by_contra hne
  have hdvd : orderOf w ∣ o := orderOf_dvd_of_pow_eq_one hw
  have hn1 : orderOf w ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have hnodd : Odd (orderOf w) := ho.of_dvd_nat hdvd
  obtain ⟨p, hp, q, hq⟩ := Nat.exists_prime_and_dvd hn1
  have hu : IsPrimitiveRoot (w ^ q) p :=
    (IsPrimitiveRoot.orderOf w).pow hnodd.pos (by rw [hq, mul_comm])
  have hpodd : Odd p := hnodd.of_dvd_nat ⟨q, hq⟩
  have hle : p - 1 ≤ 2 := by
    rw [← Nat.totient_prime hp, ← natDegree_cyclotomic p ℚ,
      cyclotomic_eq_minpoly_rat hu hp.pos, ← finrank_eq s _ (hs' s d hs) (d_nsq s d h3 hs)]
    exact minpoly.natDegree_le _
  have hp3 : p = 3 := by
    have := hp.two_le
    obtain ⟨r, hr⟩ := hpodd
    omega
  subst hp3
  have h1 := hu.pow_eq_one
  have h2 := hu.ne_one (by norm_num)
  set u := w ^ q
  have h4 : u ^ 2 + u + 1 = 0 := by
    have : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)
  apply neg_nsq s d hd h3 hs 3 (by norm_num) le_rfl (2 * u + 1)
  push_cast
  linear_combination 4 * h4

private lemma two_pow_norm (h4 : 4 ∣ Module.finrank ℚ E) (y : E) (a : ℕ) (hy : y ^ 2 ^ a = 1) :
    Algebra.norm ℚ⟮s⟯ y = 1 := by
  by_cases h2 : y ^ 2 = 1
  · have hev : Even (Module.finrank ℚ⟮s⟯ E) := by
      rw [← Module.finrank_mul_finrank ℚ ℚ⟮s⟯ E,
        finrank_eq s _ (hs' s d hs) (d_nsq s d h3 hs)] at h4
      rw [even_iff_two_dvd]
      omega
    rcases (sq_eq_one_iff.mp h2) with rfl | rfl
    · simp
    · have : (-1 : E) = algebraMap ℚ⟮s⟯ E (-1) := by simp
      rw [this, Algebra.norm_algebraMap, hev.neg_one_pow]
  obtain ⟨j, hj⟩ := exists_neg_one a (y ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]) h2
  set K := ℚ⟮s⟯ with hK
  set i := y ^ j with hi
  have hi2 : i ^ 2 = algebraMap K E (-1) := by
    rw [hi, ← pow_mul, mul_comm, pow_mul, hj]; simp
  have hn : ∀ b : K, b ^ 2 ≠ -1 := fun b => by
    simpa using neg_nsq s d hd h3 hs 1 one_pos (by norm_num) b
  have hfr := finrank_eq i _ hi2 hn
  rw [← Algebra.norm_norm (S := K⟮i⟯)]
  have hv : (Algebra.norm K⟮i⟯ y) ^ 2 ^ a = 1 := by rw [← map_pow, hy, map_one]
  set v := Algebra.norm K⟮i⟯ y
  have hv4 : v ^ 4 = 1 := by
    by_contra hne
    obtain ⟨l, hl⟩ := exists_neg_one a (v ^ 4)
      (by rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]) hne
    have hw : (v ^ l) ^ 4 = -1 := by rw [← pow_mul, mul_comm, pow_mul, hl]
    set w := v ^ l
    have hx : (w - w ^ 3) ^ 2 = 2 := by linear_combination (w ^ 2 - 2) * hw
    have hx' : ((w - w ^ 3 : K⟮i⟯) : E) ^ 2 = algebraMap K E 2 := by
      have := congrArg (algebraMap K⟮i⟯ E) hx
      rw [map_pow, map_ofNat] at this
      rw [map_ofNat]
      exact this
    rcases sq_cases i _ hi2 hn _ (w - w ^ 3).2 _ hx' with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact two_nsq s d hd h3 hs b hb.symm
    · apply neg_nsq s d hd h3 hs 2 two_pos (by norm_num) b
      push_cast
      linear_combination hb
  have hm1 : Algebra.norm K (-1 : K⟮i⟯) = 1 := by
    have : (-1 : K⟮i⟯) = algebraMap K K⟮i⟯ (-1) := by simp
    rw [this, Algebra.norm_algebraMap, hfr]; norm_num
  have hg : Algebra.norm K (AdjoinSimple.gen K i) = 1 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis (isInt i _ hi2))
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen, minpoly_eq i _ hi2 hn, natDegree_X_pow_sub_C _] at this
    rw [this]; simp
  have hg2 : (AdjoinSimple.gen K i) ^ 2 = -1 := by
    apply Subtype.ext
    simpa using hi2
  set g := AdjoinSimple.gen K i
  have : (v - 1) * (v + 1) * (v - g) * (v + g) = 0 := by
    linear_combination hv4 - (v ^ 2 - 1) * hg2
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this
  rcases this with ((h | h) | h) | h
  · rw [h, map_one]
  · rw [h, hm1]
  · rw [h, hg]
  · rw [h, ← neg_one_mul, map_mul, hm1, hg, one_mul]

end
end UpperTheory.RootOfUnityNormQuadraticSubfield

theorem UpperTheory.norm_root_of_unity_quadratic_subfield :
    ∀ (E : Type) [Field E] [NumberField E] (s : E) (d : ℕ), d.Prime → 3 < d → s ^ 2 = -(d : E) → 4 ∣ Module.finrank ℚ E →
      ∀ z : E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → Algebra.norm ℚ⟮s⟯ z = 1 := by
  intro E _ _ s d hd h3 hs h4 z ⟨m, hm, hz⟩
  obtain ⟨a, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  apply UpperTheory.RootOfUnityNormQuadraticSubfield.odd_root s d hd h3 hs _ o ho
  rw [← map_pow]
  exact UpperTheory.RootOfUnityNormQuadraticSubfield.two_pow_norm s d hd h3 hs h4 _ a (by rw [← pow_mul, mul_comm, hz])
end

