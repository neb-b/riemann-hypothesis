module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRingHomToLocalFieldInducingPlace
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Sd

namespace UpperTheory

section

variable {k : Type} [NormedField k] [IsUltrametricDist k] {K : Type} [Field K]

private theorem norm_ringHom_integer_le_one (σ : K →+* k) (x : 𝓞 K) : ‖σ (x : K)‖ ≤ 1 := by
  have hy : IsIntegral ℤ (σ (x : K)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe x)
  have h : IsIntegral (NormedField.valuation (K := k)).integer (σ (x : K)) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := k))).mem_of_integral h
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h2
  exact_mod_cast h2

private def embeddingPrimeIdeal (σ : K →+* k) : Ideal (𝓞 K) where
  carrier := {x | ‖σ (x : K)‖ < 1}
  add_mem' := by
    intro x y hx hy
    change ‖σ (algebraMap (𝓞 K) K (x + y))‖ < 1
    rw [map_add (f := _), map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
  zero_mem' := by
    change ‖σ (algebraMap (𝓞 K) K 0)‖ < 1
    simp
  smul_mem' := by
    intro c x hx
    change ‖σ (algebraMap (𝓞 K) K (c * x))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_ringHom_integer_le_one σ c)) hx

private theorem norm_embedding_eq_one_of_not_mem (σ : K →+* k) (x : 𝓞 K) (hx : x ∉ embeddingPrimeIdeal σ) :
    ‖σ (algebraMap (𝓞 K) K x)‖ = 1 :=
  le_antisymm (norm_ringHom_integer_le_one σ x) (not_lt.1 hx)

private theorem embedding_ideal_prime (σ : K →+* k) : (embeddingPrimeIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : ‖σ (algebraMap (𝓞 K) K 1)‖ < 1 := (Ideal.eq_top_iff_one _).1 h
    simp at h1
  · intro x y hxy
    by_contra hc
    push Not at hc
    change ‖σ (algebraMap (𝓞 K) K (x * y))‖ < 1 at hxy
    rw [map_mul, map_mul, norm_mul, norm_embedding_eq_one_of_not_mem σ x hc.1, norm_embedding_eq_one_of_not_mem σ y hc.2, one_mul] at hxy
    exact lt_irrefl _ hxy

private theorem exists_embedding_prime_above [NumberField K] [CharZero k] [IsAlgClosed k] {l : ℕ} (hp : l.Prime) (hk : ‖(l : k)‖ < 1)
    (w : HeightOneSpectrum (𝓞 K)) (hl : (l : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* k, embeddingPrimeIdeal σ = w.asIdeal := by
  classical
  by_contra hne
  push Not at hne
  have σ0 : K →ₐ[ℚ] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hnot : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆ ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] k)) : Set (K →ₐ[ℚ] k)),
      (embeddingPrimeIdeal (σ : K →+* k) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => embedding_ideal_prime _)]
    rintro ⟨σ, -, hle⟩
    exact hne σ (((w.isPrime.isMaximal w.ne_bot).eq_of_le (embedding_ideal_prime _).ne_top hle).symm)
  obtain ⟨a, haw, ha⟩ := Set.not_subset.1 hnot
  have h1 : ∀ σ : K →ₐ[ℚ] k, ‖σ (a : K)‖ = 1 := by
    intro σ
    refine norm_embedding_eq_one_of_not_mem (σ : K →+* k) a fun h => ha ?_
    simp only [Set.mem_iUnion]
    exact ⟨σ, by simp, h⟩
  have hprod : ‖algebraMap ℚ k (Algebra.norm ℚ (a : K))‖ = 1 := by
    rw [Algebra.norm_eq_prod_embeddings, norm_prod]
    exact Finset.prod_eq_one (fun σ _ => h1 σ)
  have hmem : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 haw)) (Ideal.absNorm_mem _)
  have hdvd : l ∣ Ideal.absNorm (Ideal.span {a}) := by
    by_contra hnd
    have hc : IsCoprime (l : 𝓞 K) ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    obtain ⟨u, v, huv⟩ := hc
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← huv]
    exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hmem)
  have hn : ‖((Ideal.absNorm (Ideal.span {a}) : ℕ) : k)‖ = 1 := by
    rw [Ideal.absNorm_span_singleton, ← hprod, ← Algebra.coe_norm_int, eq_ratCast, Rat.cast_intCast,
      Nat.cast_natAbs]
    rcases abs_choice (Algebra.norm ℤ a) with h | h
    · rw [h]
    · rw [h, Int.cast_neg, norm_neg]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.cast_mul, norm_mul] at hn
  have hk1 : ‖(m : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
  have h2 : ‖(l : k)‖ * ‖(m : k)‖ ≤ ‖(l : k)‖ * 1 := mul_le_mul_of_nonneg_left hk1 (norm_nonneg _)
  linarith

end

theorem exists_ringHom_to_localField_inducing_place : UpperTheory.V.Sd.S2.EmbEx := by
  intro F _ _ _ l hl ι
  refine ⟨fun w hw => ?_, fun w w' τ τ' h h' e => ?_⟩
  · have hk : ‖(l : Qbar l)‖ < 1 := by
      have : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := (map_natCast _ l).symm
      rw [this, norm_algebraMap']
      exact Padic.norm_p_lt_one
    obtain ⟨σ, hσ⟩ := exists_embedding_prime_above hl.out hk w hw
    exact ⟨σ, fun x => by rw [← hσ]; rfl⟩
  · have e2 : ι.toRingHom.comp τ = ι.toRingHom.comp τ' := by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact e
      · rw [← e]
        exact (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)).symm
    have e3 : τ = τ' := RingHom.ext fun x => ι.injective (RingHom.congr_fun e2 x)
    subst e3
    exact HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)

end UpperTheory
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSplitPrimeCmDatum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.exists_splitPrime_cmDatum :
    UpperTheory.V.Sd.S3.SplitPrime := by
  intro Ω _ _ _ U hU hc M hM
  obtain ⟨N, hN, hNU⟩ := UpperTheory.V.CF.kwAbs Ω U hU hc
  obtain ⟨w, hw, hMw, hmod⟩ := Nat.exists_prime_gt_modEq_one M (Nat.mul_ne_zero hM.ne' hN.ne')
  have hwM : w ≡ 1 [MOD M] := Nat.ModEq.of_dvd (Dvd.intro N rfl) hmod
  have hwN : w ≡ 1 [MOD N] := Nat.ModEq.of_dvd (Dvd.intro_left M rfl) hmod
  refine ⟨w, hw, hMw, hwM, ?_⟩
  intro A hA g hg
  haveI : Fact (Nat.Prime w) := ⟨hw⟩
  have hcop : N.Coprime w := by
    have h := Nat.ModEq.gcd_eq hwN
    rw [Nat.gcd_one_left] at h
    exact Nat.Coprime.symm h
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w A hA N hcop g hg
  apply hNU
  intro ζ hζ
  rw [hk ζ hζ]
  have hpow : w ^ k % N = 1 % N := by
    have h := Nat.ModEq.pow k hwN
    rwa [one_pow] at h
  rw [← Nat.div_add_mod (w ^ k) N, pow_add, pow_mul, hζ, one_pow, one_mul, hpow]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by omega
    subst hN1
    simp only [pow_one] at hζ
    simp [hζ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSquareRootCharacter
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem sqrt_ex {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] (h2 : IsUnit (2 : O))
    (a : O) (ha : residue O a = 1) : ∃ x : O, x ^ 2 = a ∧ residue O x = 1 := by
  haveI : HenselianRing O (maximalIdeal O) := IsAdicComplete.henselianRing O (maximalIdeal O)
  have hev : eval 1 (X ^ 2 - C a) ∈ maximalIdeal O := by
    simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow]
    rw [← residue_eq_zero_iff, map_sub, map_one, ha, sub_self]
  have hd : eval 1 (derivative (X ^ 2 - C a)) = (2 : O) := by
    simp
    exact one_add_one_eq_two
  obtain ⟨x, hx, hx1⟩ := HenselianRing.is_henselian (X ^ 2 - C a) (monic_X_pow_sub_C a two_ne_zero) 1 hev
    (by rw [hd]; exact h2.map _)
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_one (residue O), ← map_sub, residue_eq_zero_iff]
    exact hx1

private theorem add_unit {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {x y : O}
    (hx : residue O x = 1) (hy : residue O y = 1) : IsUnit (x + y) := by
  rw [← residue_ne_zero_iff_isUnit, map_add (f := _), hx, hy]
  have h2' : residue O (2 : O) = 1 + 1 := by
    rw [← map_one (residue O), ← map_add (f := _), one_add_one_eq_two]
  rw [← h2']
  exact (residue_ne_zero_iff_isUnit (2 : O)).mpr h2

private theorem sqrt_uniq {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {x y : O}
    (hx : residue O x = 1) (hy : residue O y = 1) (h : x ^ 2 = y ^ 2) : x = y := by
  have hu := add_unit h2 hx hy
  have hz : (x - y) * (x + y) = 0 := by linear_combination h
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)

theorem UpperTheory.exists_square_root_character :
    UpperTheory.V.Sd.S3.SqrtChar := by
  intro O _ _ _ h2 Γ _ _ μ hμ hc
  have ex : ∀ g, ∃ x : O, x ^ 2 = (μ g : O) ∧ residue O x = 1 := fun g => sqrt_ex h2 _ (hμ g)
  choose s hs1 hs2 using ex
  have hsu : ∀ g, IsUnit (s g) := fun g =>
    (residue_ne_zero_iff_isUnit _).mp (by rw [hs2 g]; exact one_ne_zero)
  let η : Γ →* Oˣ :=
    { toFun := fun g => (hsu g).unit
      map_one' := by
        apply Units.ext
        show s 1 = 1
        exact sqrt_uniq h2 (hs2 1) (map_one _) (by rw [hs1, map_one, Units.val_one, one_pow])
      map_mul' := by
        intro g k
        apply Units.ext
        show s (g * k) = s g * s k
        refine sqrt_uniq h2 (hs2 _) (by rw [map_mul, hs2, hs2, one_mul]) ?_
        rw [mul_pow, hs1, hs1, hs1, map_mul, Units.val_mul] }
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · intro g
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hs1 g
  · intro g
    exact hs2 g
  · intro N
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    rw [isOpen_iff_forall_mem_open]
    intro g0 hg0
    refine ⟨_, ?_, (hc N).isOpen_fiber (Ideal.Quotient.mk _ (μ g0 : O)), rfl⟩
    intro g hg
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hg hg0 ⊢
    rw [← hg0]
    show Ideal.Quotient.mk (maximalIdeal O ^ N) (s g) = Ideal.Quotient.mk (maximalIdeal O ^ N) (s g0)
    rw [Ideal.Quotient.eq] at hg ⊢
    obtain ⟨w, hw⟩ := (add_unit h2 (hs2 g) (hs2 g0)).exists_right_inv
    have hd : s g - s g0 = ((μ g : O) - μ g0) * w := by
      rw [← hs1 g, ← hs1 g0]
      linear_combination (-(s g - s g0)) * hw
    rw [hd]
    exact Ideal.mul_mem_right _ _ hg
  · intro g hg
    apply Units.ext
    show s g = 1
    exact sqrt_uniq h2 (hs2 g) (map_one _) (by rw [hs1, hg, Units.val_one, one_pow])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSquareRootOfCharacterNearOne
section
section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

private theorem sub_eq (h2 : ‖(2 : K)‖ = 1) {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    ‖a - b‖ = ‖a ^ 2 - b ^ 2‖ := by
  have h := add_lt ha hb
  have h1 : ‖a + b‖ = 1 := by
    have e : a + b = 2 + ((a - 1) + (b - 1)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2]; exact h.ne'), h2]
    exact max_eq_left h.le
  have e : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by ring
  rw [e, norm_mul, h1, one_mul]

private theorem mul_lt {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) : ‖a * b - 1‖ < 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  rw [e]
  refine add_lt ?_ (add_lt ha hb)
  rw [norm_mul]
  nlinarith [norm_nonneg (a - 1), norm_nonneg (b - 1)]

omit [IsUltrametricDist K] in
private theorem ex_root [IsAlgClosed K] (y : Kˣ) (hy : ‖(y : K) - 1‖ < 1) :
    ∃ x : Kˣ, x ^ 2 = y ∧ ‖(x : K) - 1‖ < 1 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (y : K) (n := 2) (by norm_num)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hx]; ring)
  by_cases h : ‖x - 1‖ < 1
  · exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx), h⟩
  · refine ⟨Units.mk0 (-x) (neg_ne_zero.mpr hx0), Units.ext (by simpa using hx), ?_⟩
    have e : (y : K) - 1 = -((x - 1) * (-x - 1)) := by rw [← hx]; ring
    rw [e, norm_neg, norm_mul] at hy
    simp only [Units.val_mk0]
    by_contra h'
    push Not at h h'
    nlinarith

end

theorem UpperTheory.exists_square_root_of_character_near_one :
    UpperTheory.V.Sd.S2.SqrtChar := by
  intro l _ hl Γ _ _ η hη hc
  have h2 : ‖(2 : PadicAlgCl l)‖ = 1 := by
    have e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; norm_num
    rw [e]
    erw [PadicAlgCl.norm_extends]
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).mpr hl
  have hc' : ∀ g, ‖((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) - 1‖ < 1 := fun g => by
    simpa [UpperTheory.V.Sd.Cong] using hc g
  choose d hd hd1 using fun g => ex_root (η g) (hc' g)
  have hv : ∀ g, ((d g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ 2 = η g := fun g => by
    rw [← hd g]; simp
  have hmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    apply Units.ext
    have := sub_eq h2 (hd1 (g * h)) (mul_lt (hd1 g) (hd1 h))
    rw [mul_pow, hv, hv, hv, map_mul, Units.val_mul, sub_self, norm_zero, norm_eq_zero, sub_eq_zero] at this
    simpa using this
  refine ⟨MonoidHom.mk' d hmul, ?_, hd, fun g => ?_⟩
  · rw [Units.isEmbedding_val₀.continuous_iff]
    have hη' : Continuous fun g => ((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := Units.continuous_val.comp hη
    rw [continuous_iff_continuousAt]
    intro g
    have h1 := (hη'.continuousAt (x := g))
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
    refine h1.congr fun x => ?_
    simp only [Function.comp, MonoidHom.mk'_apply]
    rw [sub_eq h2 (hd1 x) (hd1 g), hv, hv]
  · simpa [UpperTheory.V.Sd.Cong] using hd1 g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsThetaCharacterCmDatum
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af

private theorem exists_nontrivial_l_torsion_character {A C : Type} [Group A] [Finite A] [IsCyclic A] [CommGroup C] {l : ℕ} (hl : l ∣ Nat.card A)
    {z : C} (hz : z ≠ 1) (hzl : z ^ l = 1) : ∃ φ : A →* C, φ ≠ 1 ∧ ∀ a, φ a ^ l = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have ho : orderOf z ∣ orderOf g := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    exact (orderOf_dvd_of_pow_eq_one hzl).trans hl
  have e : monoidHomOfForallMemZpowers hg ho g = z := monoidHomOfForallMemZpowers_apply_gen hg ho
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun h => hz (by rw [← e, h, MonoidHom.one_apply]), fun a => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  rw [map_zpow, e, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzl, one_zpow]

theorem UpperTheory.exists_theta_character_cmDatum : UpperTheory.V.Sd.S3.ThetaEx := by
  unfold UpperTheory.V.Sd.S3.ThetaEx
  intro Ω _ _ _ l _ w hw hwl
  unfold KillsMu
  haveI : Fact w.Prime := ⟨hw⟩
  have hlp : Nat.Prime l := Fact.out
  have hdvd : l ∣ Nat.card (ZMod w)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hw]
    exact (Nat.modEq_iff_dvd' hw.one_lt.le).1 hwl.symm
  haveI : IsAlgClosed (Qbar l) := inferInstance
  haveI : NeZero (l : Qbar l) := ⟨by exact_mod_cast hlp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) l
  let z : (Qbar l)ˣ := (hζ.isUnit hlp.ne_zero).unit
  have hz : z ≠ 1 := by
    intro h
    apply hζ.ne_one hlp.one_lt
    simpa [z] using congrArg Units.val h
  have hzl : z ^ l = 1 := by
    ext
    simp [z, hζ.pow_eq_one]
  obtain ⟨φ, hφ, hφl⟩ := exists_nontrivial_l_torsion_character (A := (ZMod w)ˣ) hdvd hz hzl
  refine ⟨φ.comp (UpperTheory.V.Chr.cls ℚ Ω w), ?_, ?_, ?_⟩
  · intro h
    apply hφ
    ext u
    obtain ⟨s, rfl⟩ := (UpperTheory.V.Chr.clsOnto Ω w).1 u
    have := DFunLike.congr_fun h s
    simpa using this
  · ext s
    simp [hφl]
  · intro s hs
    haveI : Fact (1 < w) := ⟨hw.one_lt⟩
    have h1 : UpperTheory.V.Chr.cls ℚ Ω w s = 1 :=
      (UpperTheory.V.Chr.clsFacts ℚ Ω w).2.2.1 s 1 (fun ζ hζ => by
        rw [Units.val_one, ZMod.val_one, pow_one]
        exact hs ζ hζ)
    rw [MonoidHom.comp_apply, h1, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepPropertiesInvariantUnderConjugation
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem isIrr_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩
  have key := h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by
    have h4 := hi s _ hv
    rw [hg s] at h4
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4)
  have hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)) := fun v =>
    ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  have e := Submodule.map_comap_eq_of_surjective hs W
  rcases key with key | key
  · left
    rw [← e, key, Submodule.map_bot]
  · right
    rw [← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]

private theorem ss_of_irrOpen {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k}
    (h : IrrOpen r) : IsSSRep r := by
  intro W hW
  obtain ⟨-, -, h3⟩ := h ⊤ (by simp)
  rcases h3 W le_top (fun s v hv => hW s v hv) with e | e
  · exact ⟨⊤, fun _ _ _ => Submodule.mem_top, e ▸ isCompl_bot_top⟩
  · refine ⟨⊥, fun s v hv => ?_, e ▸ isCompl_top_bot⟩
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, Matrix.mulVec_zero]

private theorem ordAt_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ : Fin n → G F Ω →* (Qbar l)ˣ} {A : ValuationSubring Ω}
    (h : RepIso r r') (H : OrdAt r m ψ A) : OrdAt r' m ψ A := by
  obtain ⟨κ, h1, h2⟩ := H
  exact ⟨κ, h1.of_iso h, h2⟩

private theorem irrOpen_iso {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
    (h : RepIso r r') (H : IrrOpen r) : IrrOpen r' := fun U hU => by
  obtain ⟨g, hg⟩ := h
  have e : RepIso (r.comp U.subtype) (r'.comp U.subtype) := ⟨g, fun s => hg s⟩
  exact isIrr_iso e (H U hU)

private theorem det_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') :
    Matrix.GeneralLinearGroup.det.comp r' = Matrix.GeneralLinearGroup.det.comp r := by
  obtain ⟨g, hg⟩ := h
  refine MonoidHom.ext fun s => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_mul, map_mul, map_inv,
    mul_comm _ (Matrix.GeneralLinearGroup.det (r s)), mul_inv_cancel_right]

private theorem resSum_iso {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} {r r' : Γ →* GL (Fin n) (Qbar l)}
    {χ : Fin n → Γ →* (Qbar l)ˣ} (h : RepIso r r') (H : ResSum r χ) : ResSum r' χ := by
  obtain ⟨g, hg⟩ := h
  intro s i
  rw [hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact H s i

private theorem attR_iso {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {ι : Qbar l ≃+* ℂ} {π} (h : RepIso r r')
    (hs : IsSSRep r') (H : AttR ι r π) : AttR ι r' π := by
  refine ⟨hs, H.2.mono fun w hw => ?_⟩
  obtain ⟨B, b1, b2⟩ := hw
  exact ⟨B, b1, b2.of_iso h⟩

private theorem away_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {τ : Fin n → G F Ω →* (Qbar l)ˣ}
    (h : RepIso r r') (H : TypeAway r τ) : TypeAway r' τ := fun A hA => (H A hA).of_iso h

theorem UpperTheory.galoisRep_properties_invariant_under_conjugation :
    UpperTheory.V.Sd.S2.MixConj := by
  intro Ω _ _ _ l _ k₀ _ _ ι x k t r r' H h
  have hirr : IrrOpen r' := irrOpen_iso h H.irr
  obtain ⟨π, h2, h3⟩ := H.att
  refine ⟨H.hk, H.ht, H.dvd, continuous_of_iso H.cont h, hirr, ⟨π, attR_iso h (ss_of_irrOpen hirr) h2, h3⟩,
    (det_iso h).trans H.det, resSum_iso h H.res, away_iso h H.away, ?_⟩
  intro A A' hA g hg hy
  rcases H.above A A' hA g hg hy with a | a
  · exact Or.inl ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩
  · exact Or.inr ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIsomorphism
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem diag_mul {R : Type} [CommRing R] {u : R} (hu : 3 * u = 1) :
    (Matrix.diagonal ![1, 1, -1, 3] * Matrix.diagonal ![1, 1, -1, u] : M4 R) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [hu]
end

