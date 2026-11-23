module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowDescentCyclotomic
section
open NumberField

namespace GlobalTheory

namespace CyclotomicKummerDescent

theorem geom_sum_valuation {l : ℕ} (hl : l.Prime) {t : ℕ} (ht1 : 1 < t)
    (ht : (l : ℤ) ^ 2 ∣ (t : ℤ) - 1) (r : ℕ) :
    l ^ r ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i ∧
      ¬ l ^ (r + 1) ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h1 : (l : ℤ) ∣ (t : ℤ) - 1 := (dvd_pow_self _ two_ne_zero).trans ht
  have h2 : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => hp.not_dvd_one (by simpa using dvd_sub h h1)
  have hlte : emultiplicity (l : ℤ) ((t : ℤ) ^ (l ^ r) - 1 ^ (l ^ r)) =
      emultiplicity (l : ℤ) ((t : ℤ) - 1) + r := by
    rcases hl.eq_two_or_odd' with rfl | hodd
    · have h := Int.two_pow_sub_pow' (x := t) (y := 1) (2 ^ r) (by simpa using ht)
        (by simpa using h2)
      have h3 : emultiplicity (2 : ℤ) ((2 ^ r : ℕ) : ℤ) = r := by
        push_cast
        exact emultiplicity_pow_self_of_prime Int.prime_two r
      rw [h3] at h
      simpa using h
    · rw [Int.emultiplicity_pow_sub_pow hl hodd h1 h2,
        emultiplicity_pow_self_of_prime hl.prime]
  rw [one_pow, ← geom_sum_mul, emultiplicity_mul hp, add_comm] at hlte
  have hfin : emultiplicity (l : ℤ) ((t : ℤ) - 1) ≠ ⊤ := by
    rw [← finiteMultiplicity_iff_emultiplicity_ne_top, Int.finiteMultiplicity_iff]
    refine ⟨by simpa using hl.ne_one, ?_⟩
    have : (1 : ℤ) < t := by exact_mod_cast ht1
    omega
  have h4 : emultiplicity (l : ℤ) (∑ i ∈ Finset.range (l ^ r), (t : ℤ) ^ i) = (r : ℕ∞) :=
    WithTop.add_left_cancel hfin hlte
  rw [emultiplicity_eq_coe] at h4
  exact_mod_cast h4

theorem exists_aut {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {g : ℕ}
    (hg : g.Coprime M) :
    ∃ τ : K ≃ₐ[E] K, τ ζ = ζ ^ (g ^ (Module.finrank ℚ E).factorial) := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  haveI : NumberField K := NumberField.of_module_finite E K
  set H := (hζ.autToPow E).range with hH
  have hcard : Nat.card H = Module.finrank E K := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (MonoidHom.ofInjective (hζ.autToPow_injective E)).toEquiv).symm
  have htot : M.totient ≤ Module.finrank ℚ E * Module.finrank E K := by
    rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic M ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos M)]
    exact minpoly.natDegree_le ζ
  have hidx : H.index * Nat.card H = M.totient := by
    rw [Subgroup.index_mul_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hle : H.index ≤ Module.finrank ℚ E := by
    rw [← hidx, hcard] at htot
    exact Nat.le_of_mul_le_mul_right htot Module.finrank_pos
  have hdvd : H.index ∣ (Module.finrank ℚ E).factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero H.index_ne_zero_of_finite) hle
  have hmem : ZMod.unitOfCoprime g hg ^ (Module.finrank ℚ E).factorial ∈ H := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    exact H.pow_mem (H.pow_index_mem _) c
  obtain ⟨τ, hτ⟩ := hmem
  refine ⟨τ, ?_⟩
  rw [← hζ.autToPow_spec E τ, hτ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    ← Nat.cast_pow, ZMod.val_natCast]
  exact (pow_eq_pow_mod _ hζ.pow_eq_one).symm

theorem descent {E K : Type} [Field E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {k n : ℕ}
    (τ : K ≃ₐ[E] K) (hτ : τ ζ = ζ ^ (k + 1))
    (hN : M ∣ (∑ i ∈ Finset.range n, (k + 1) ^ i) * k) {u : E} {w : K} (hw0 : w ≠ 0)
    (hw : w ^ M = algebraMap E K u) :
    ∃ (α : K) (v : E), α ^ M = 1 ∧ α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 ∧
      algebraMap E K v * α = w ^ k := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  have hext : ∀ σ σ' : K ≃ₐ[E] K, σ ζ = σ' ζ → σ = σ' := by
    intro σ σ' h
    apply hζ.autToPow_injective E
    rw [← hζ.autToPow_spec E σ, ← hζ.autToPow_spec E σ'] at h
    exact Units.ext (ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have hcomm : ∀ σ : K ≃ₐ[E] K, σ * τ = τ * σ := fun σ =>
    hζ.autToPow_injective E (by rw [map_mul, map_mul, mul_comm])
  have hroot : ∀ η : K, η ^ M = 1 → τ η = η ^ (k + 1) := by
    intro η hη
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
    rw [map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm]
  have hcoc : ∀ σ : K ≃ₐ[E] K, ∃ a : K, a ^ M = 1 ∧ σ w = a * w := by
    intro σ
    refine ⟨σ w / w, ?_, by field_simp⟩
    rw [div_pow, ← map_pow, hw, AlgEquiv.commutes, ← hw, div_self (pow_ne_zero _ hw0)]
  have hne : ∀ a : K, a ^ M = 1 → a ≠ 0 := by
    rintro a ha rfl
    rw [zero_pow (NeZero.ne M)] at ha
    exact zero_ne_one ha
  obtain ⟨α, hαM, hα⟩ := hcoc τ
  have hα0 := hne α hαM
  have hiter : ∀ m : ℕ, (τ ^ m) w = α ^ (∑ i ∈ Finset.range m, (k + 1) ^ i) * w ∧
      (τ ^ m) ζ = ζ ^ ((k + 1) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih.1, ih.2, map_mul, map_pow,
        map_pow, hτ, hα, hroot α hαM, geom_sum_succ]
      constructor <;> ring
  have hgeom : ∀ m : ℕ, (k + 1) ^ m = (∑ i ∈ Finset.range m, (k + 1) ^ i) * k + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, pow_succ, add_mul, mul_add, mul_one]; omega
  have hτn : τ ^ n = 1 := by
    apply hext
    obtain ⟨c, hc⟩ := hN
    rw [(hiter n).2, hgeom, hc, pow_succ, pow_mul, hζ.pow_eq_one]
    simp
  have hαN : α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 := by
    have h := (hiter n).1
    rw [hτn, AlgEquiv.one_apply] at h
    exact mul_right_cancel₀ hw0 (by rw [← h, one_mul])
  have hfix : ∀ σ : K ≃ₐ[E] K, σ (w ^ k / α) = w ^ k / α := by
    intro σ
    obtain ⟨a, haM, ha⟩ := hcoc σ
    have ha0 := hne a haM
    have h := congrArg (fun f : K ≃ₐ[E] K => f w) (hcomm σ)
    simp only [AlgEquiv.mul_apply] at h
    rw [hα, ha, map_mul, map_mul, ha, hα, hroot a haM] at h
    have hσα : σ α = a ^ k * α :=
      mul_right_cancel₀ (mul_ne_zero ha0 hw0) (by rw [h]; ring)
    rw [map_div₀, map_pow, hσα, ha, mul_pow]
    field_simp
  obtain ⟨v, hv⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  exact ⟨α, v, hαM, hαN, by rw [hv]; field_simp⟩

end CyclotomicKummerDescent


open CyclotomicKummerDescent in
theorem exists_pow_descent_cyclotomic :
    ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u →
        ∃ v : E, v ^ (l ^ r) = u := by
  intro E _ _ l r hl
  set m := (Module.finrank ℚ E).factorial with hm
  have ht1 : 1 < (1 + l ^ 2) ^ m :=
    Nat.one_lt_pow (Nat.factorial_ne_zero _) (by have := pow_pos hl.pos 2; omega)
  obtain ⟨k, hk⟩ : ∃ k, (1 + l ^ 2) ^ m = k + 1 := ⟨_, (Nat.sub_add_cancel ht1.le).symm⟩
  have hk0 : k ≠ 0 := by omega
  obtain ⟨s, e, he, hke⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 l hl.ne_one
  have hdiv : (l : ℤ) ^ 2 ∣ (((1 + l ^ 2) ^ m : ℕ) : ℤ) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + (l : ℤ) ^ 2) 1 m
    simpa using this
  obtain ⟨hN1, hN2⟩ := geom_sum_valuation hl ht1 hdiv r
  rw [hk] at hN1 hN2
  refine ⟨l ^ (r + s), pow_pos hl.pos _, pow_dvd_pow _ (by omega), ?_⟩
  intro Ω _ _ ζ hζ u w hwK hw
  haveI : NeZero (l ^ (r + s)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hint : IsIntegral E ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  set K := IntermediateField.adjoin E {ζ} with hK
  haveI : IsCyclotomicExtension {l ^ (r + s)} E K := by
    change IsCyclotomicExtension {l ^ (r + s)} E K.toSubalgebra
    rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension E
  let ζ' : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζ' : IsPrimitiveRoot ζ' (l ^ (r + s)) :=
    IsPrimitiveRoot.of_map_of_injective (f := K.val) hζ K.val.injective
  let w' : K := ⟨w, hwK⟩
  have hw' : w' ^ (l ^ (r + s)) = algebraMap E K u := Subtype.ext hw
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, zero_pow (pow_ne_zero _ hl.ne_zero)⟩
  have hw0 : w' ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne _), eq_comm, map_eq_zero] at hw'
    exact hu hw'
  have hg : (1 + l ^ 2).Coprime (l ^ (r + s)) := by
    apply Nat.Coprime.pow_right
    rw [sq, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left l
  obtain ⟨τ, hτ⟩ := exists_aut (E := E) hζ' hg
  rw [← hm, hk] at hτ
  obtain ⟨α, v, hαM, hαN, hv⟩ := descent hζ' (n := l ^ r) τ hτ
    (by rw [pow_add]; exact mul_dvd_mul hN1 ⟨e, hke⟩) hw0 hw'
  have hαr : α ^ (l ^ r) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hαM)
    have h1 := orderOf_dvd_of_pow_eq_one hαN
    rw [hj] at h1
    have hjr : j ≤ r := by
      by_contra hc
      exact hN2 ((pow_dvd_pow l (by omega)).trans h1)
    exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow l hjr)
  have hvu : v ^ (l ^ r) = u ^ e := by
    apply (algebraMap E K).injective
    have h := congrArg (· ^ (l ^ r)) hv
    simp only [mul_pow, hαr, mul_one] at h
    rw [map_pow, map_pow, h, ← hw', hke, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hco : IsCoprime (e : ℤ) ((l ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hl).mpr he).symm)
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨v ^ a * u ^ b, ?_⟩
  rw [mul_pow, ← zpow_natCast (v ^ a), ← zpow_natCast (u ^ b), ← zpow_mul, ← zpow_mul, mul_comm a,
    zpow_mul, zpow_natCast, hvu, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu, mul_comm _ a, hab,
    zpow_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

private lemma natAbs_eq_one_of_dvd_prime_pow_not_dvd {d : ℤ} {m k : ℕ} (hm : m.Prime) (h1 : d ∣ (m : ℤ) ^ k)
    (h2 : ¬ (m : ℤ) ∣ d) : d.natAbs = 1 := by
  have h1' : d.natAbs ∣ m ^ k := by
    have := Int.natAbs_dvd_natAbs.mpr h1
    simpa [Int.natAbs_pow] using this
  have hc : Nat.Coprime m d.natAbs := by
    rw [hm.coprime_iff_not_dvd]
    intro h
    exact h2 (Int.natCast_dvd.mpr h)
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hc).symm h1'

theorem irreducible_cyclotomic_of_not_dvd_discr (K : Type) [Field K] [NumberField K] (m : ℕ)
    (hm : m.Prime) (hd : ¬ (m : ℤ) ∣ discr K) : Irreducible (cyclotomic m K) := by
  have : NeZero m := ⟨hm.ne_zero⟩
  have : Fact m.Prime := ⟨hm⟩
  let E := CyclotomicField m K
  have : FiniteDimensional ℚ E := Module.Finite.trans K E
  have hζ := IsCyclotomicExtension.zeta_spec m K E
  set ζ := IsCyclotomicExtension.zeta m K E
  let A : IntermediateField ℚ E := IntermediateField.adjoin ℚ {ζ}
  let B : IntermediateField ℚ E := (IsScalarTower.toAlgHom ℚ K E).fieldRange
  have hAc : IsCyclotomicExtension {m} ℚ A := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hGal : IsGalois ℚ A := IsCyclotomicExtension.isGalois {m} ℚ A
  have hinf : A ⊓ B = ⊥ := by
    let F : IntermediateField ℚ E := A ⊓ B
    let _ : Algebra F A := (IntermediateField.inclusion (inf_le_left : F ≤ A)).toRingHom.toAlgebra
    let _ : Algebra F K := (((IsScalarTower.toAlgHom ℚ K E).equivFieldRange.symm.toAlgHom).comp
      (IntermediateField.inclusion (inf_le_right : F ≤ B))).toRingHom.toAlgebra
    have hFA : NumberField.discr F ∣ NumberField.discr A := NumberField.discr_dvd_discr F A
    have hFK : NumberField.discr F ∣ NumberField.discr K := NumberField.discr_dvd_discr F K
    have hA : NumberField.discr A = (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2) :=
      IsCyclotomicExtension.Rat.discr_prime m A
    have hpow : NumberField.discr F ∣ (m : ℤ) ^ (m - 2) := by
      have : NumberField.discr F ∣ (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2) := hA ▸ hFA
      exact (IsUnit.dvd_mul_left ((isUnit_neg_one).pow _)).mp this
    have hnd : ¬ (m : ℤ) ∣ NumberField.discr F := fun h => hd (h.trans hFK)
    have h1 : (NumberField.discr F).natAbs = 1 := natAbs_eq_one_of_dvd_prime_pow_not_dvd hm hpow hnd
    have hrank : Module.finrank ℚ F = 1 := by
      by_contra hne
      have hgt : 1 < Module.finrank ℚ F := lt_of_le_of_ne Module.finrank_pos (Ne.symm hne)
      have h2 := NumberField.abs_discr_gt_two hgt
      rw [Int.abs_eq_natAbs, h1] at h2
      norm_num at h2
    exact IntermediateField.finrank_eq_one_iff.mp hrank
  have hdis : A.LinearDisjoint B :=
    @IntermediateField.LinearDisjoint.of_inf_eq_bot _ _ _ _ _ A B (by exact hGal) _ _ hinf
  have e1 : (IsScalarTower.toAlgHom ℚ K E).range = B.toSubalgebra :=
    (AlgHom.fieldRange_toSubalgebra _).symm
  have hdisK : A.LinearDisjoint K := by
    rw [IntermediateField.linearDisjoint_iff, e1]
    exact IntermediateField.linearDisjoint_iff'.mp hdis
  have hrk : Module.rank K (IntermediateField.adjoin K (A : Set E)) = Module.rank ℚ A :=
    hdisK.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have htop : IntermediateField.adjoin K {ζ} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic ζ),
      IntermediateField.top_toSubalgebra]
    exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop' : IntermediateField.adjoin K (A : Set E) = ⊤ := by
    refine top_le_iff.mp (htop ▸ ?_)
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.subset_adjoin K (A : Set E) (IntermediateField.mem_adjoin_simple_self ℚ ζ)))
  have hfinA : Module.finrank ℚ A = m.totient := IsCyclotomicExtension.finrank A (cyclotomic.irreducible_rat hm.pos)
  have hfinE : Module.finrank K E = m.totient := by
    have h' : Module.finrank K (IntermediateField.adjoin K (A : Set E)) = m.totient := by
      rw [Module.finrank, hrk]
      exact hfinA
    rwa [htop', IntermediateField.finrank_top'] at h'
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hdeg : (minpoly K ζ).natDegree = m.totient := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hfinE]
  have hdvd : minpoly K ζ ∣ cyclotomic m K := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm.pos
  have heq : cyclotomic m K = minpoly K ζ :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m K) hdvd
      (by rw [natDegree_cyclotomic, hdeg])
  rw [heq]
  exact minpoly.irreducible hint

theorem exists_prime_dvd_sub_one_irreducible_cyclotomic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 →
      ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  intro K _ _ n hn
  obtain ⟨m, hmp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (NumberField.discr K).natAbs hn
  refine ⟨m, hmp, (Nat.modEq_iff_dvd' hmp.one_le).mp hmod.symm, ?_⟩
  apply irreducible_cyclotomic_of_not_dvd_discr K m hmp
  intro h
  have hne : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp h)
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentativesTwoElementOrbitsInvolution
section
namespace GlobalTheory

theorem involution_pair_representatives :
    ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι),
      (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧
        ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  intro ι _ s hs
  classical
  haveI := Fintype.ofFinite ι
  set enc : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with henc_def
  have henc : Function.Injective enc := fun a b h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set S : Finset ι := Finset.univ.filter (fun i => enc i < enc (s i)) with hS
  have memS : ∀ x : S, enc (x : ι) < enc (s x) := fun x => (Finset.mem_filter.1 x.2).2
  refine ⟨S.card, fun j => (S.equivFin.symm j : ι), ?_, ?_, ?_⟩
  · intro j k h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j k h
    simp only at h
    have hj := memS (S.equivFin.symm j)
    have hk := memS (S.equivFin.symm k)
    generalize (S.equivFin.symm j : ι) = a at h hj
    generalize (S.equivFin.symm k : ι) = b at h hk
    subst h
    rw [hs] at hk
    omega
  · intro i
    by_cases hi : s i = i
    · exact Or.inl hi
    right
    have hne : enc i ≠ enc (s i) := fun h => hi (henc h).symm
    rcases lt_or_gt_of_ne hne with h | h
    · have hm : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
      exact ⟨S.equivFin ⟨i, hm⟩, Or.inl (by simp)⟩
    · have hm : s i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hs]; exact h⟩
      exact ⟨S.equivFin ⟨s i, hm⟩, Or.inr (by simp [hs])⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRescaleEigenSeriesZero
section
open PowerSeries

namespace GlobalTheory

noncomputable def eigenSeriesCoeff {F : Type} [Field F] (a c : ℕ → F) : ℕ → F
  | 0 => 1
  | k + 1 => (a (k + 1))⁻¹ * ∑ i : Fin (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i)
decreasing_by omega

theorem eigenSeriesCoeff_succ {F : Type} [Field F] (a c : ℕ → F) (k : ℕ) (ha : a (k + 1) ≠ 0) :
    a (k + 1) * eigenSeriesCoeff a c (k + 1)
      = ∑ i ∈ Finset.range (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i) := by
  rw [eigenSeriesCoeff, mul_inv_cancel_left₀ ha]
  exact Fin.sum_univ_eq_sum_range (fun i => c (i + 1) * eigenSeriesCoeff a c (k - i)) (k + 1)

theorem exists_rescale_eigen_series_zero {F : Type} [Field F] (p : F⟦X⟧) (χ u : F)
    (hp : constantCoeff p ≠ 0) (hu : u ≠ 0) (hχ : ∀ k : ℕ, 0 < k → χ ^ k ≠ 1) :
    ∃ h : F⟦X⟧, constantCoeff h = 1 ∧
      C u * rescale χ h - h = C ((u - 1) / constantCoeff p) * (p * h) := by
  set L : F := (u - 1) / constantCoeff p with hL
  have hLp : L * coeff 0 p = u - 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, hL]
    field_simp
  refine ⟨PowerSeries.mk (eigenSeriesCoeff (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p)),
    ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, eigenSeriesCoeff]
  · ext k
    simp only [map_sub, coeff_C_mul, coeff_rescale, coeff_mk]
    rw [coeff_mul]
    simp only [coeff_mk]
    cases k with
    | zero =>
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero]
      rw [eigenSeriesCoeff]
      linear_combination -hLp
    | succ k =>
      have ha : u * (χ ^ (k + 1) - 1) ≠ 0 :=
        mul_ne_zero hu (sub_ne_zero.mpr (hχ (k + 1) (Nat.succ_pos k)))
      have key := eigenSeriesCoeff_succ (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p) k ha
      simp only [mul_assoc] at key
      rw [← Finset.mul_sum] at key
      rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Nat.succ_eq_add_one]
      linear_combination key - eigenSeriesCoeff (fun k => u * (χ ^ k - 1))
        (fun j => L * coeff j p) (k + 1) * hLp

theorem exists_rescale_eigen_series : ∀ {F : Type} [Field F] (p : F⟦X⟧) (χ κ : F) (n : ℕ), constantCoeff p ≠ 0 → κ ≠ 0 → χ ≠ 0 → (∀ k : ℕ, 0 < k → χ ^ k ≠ 1) → ∃ h : F⟦X⟧, constantCoeff h = 1 ∧ C κ * rescale χ (X ^ n * h) - X ^ n * h = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by
  intro F _ p χ κ n hp hκ hχ0 hχ
  obtain ⟨h, h0, hh⟩ :=
    exists_rescale_eigen_series_zero p χ (κ * χ ^ n) hp (mul_ne_zero hκ (pow_ne_zero n hχ0)) hχ
  refine ⟨h, h0, ?_⟩
  have hX : rescale χ (X ^ n * h) = C (χ ^ n) * X ^ n * rescale χ h := by
    rw [map_mul, map_pow, rescale_X, mul_pow, map_pow]
  rw [hX]
  calc C κ * (C (χ ^ n) * X ^ n * rescale χ h) - X ^ n * h
      = X ^ n * (C (κ * χ ^ n) * rescale χ h - h) := by rw [map_mul]; ring
    _ = X ^ n * (C ((κ * χ ^ n - 1) / constantCoeff p) * (p * h)) := by rw [hh]
    _ = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootsOfUnityCharacterHom
section
namespace GlobalTheory

theorem exists_rootsOfUnity_character_hom : ∀ {Γ F O LL : Type} [Group Γ] [Field F] [CommRing O] [Field LL] (n : ℕ), 0 < n → ∀ (f : F → Γ → ℂ), (∀ x, x ≠ 0 → f x 1 = 1) → (∀ x, x ≠ 0 → ∀ σ σ', f x (σ * σ') = f x σ * f x σ') → (∀ x y, x ≠ 0 → y ≠ 0 → ∀ σ, f (x * y) σ = f x σ * f y σ) → ∀ (ι : O →+* ℂ), Function.Injective ι → ∀ (ζ : O), IsPrimitiveRoot ζ n → ∀ (t : O →+* LL), ∃ Ψ : ↥(rootsOfUnity n F) →* (Γ →* LLˣ), ∀ (u : ↥(rootsOfUnity n F)) (σ : Γ), ∃ o : O, ι o = f (((u : Fˣ)) : F) σ ∧ ((Ψ u σ : LLˣ) : LL) = t o := by
  intro Γ F O LL _ _ _ _ n hn f hone hmul hx ι hι ζ hζ t
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : ∀ σ, f 1 σ = 1 := by
    intro σ
    have hne : f 1 σ ≠ 0 := by
      intro h
      have := hmul 1 one_ne_zero σ σ⁻¹
      rw [mul_inv_cancel, hone 1 one_ne_zero, h, zero_mul] at this
      exact one_ne_zero this
    have := hx 1 1 one_ne_zero one_ne_zero σ
    rw [mul_one] at this
    exact (mul_left_cancel₀ hne (by rw [mul_one]; exact this)).symm
  have hpow : ∀ x, x ≠ 0 → ∀ σ (k : ℕ), f (x ^ k) σ = f x σ ^ k := by
    intro x hx0 σ k
    induction k with
    | zero => simp [h1]
    | succ k ih => rw [pow_succ, hx _ _ (pow_ne_zero k hx0) hx0, ih, pow_succ]
  have hex : ∀ (u : rootsOfUnity n F) (σ : Γ), ∃ o : O, ι o = f ((u : Fˣ) : F) σ := by
    intro u σ
    have hu : (((u : Fˣ) : F)) ^ n = 1 := by
      have := u.2
      rw [mem_rootsOfUnity'] at this
      exact this
    have h2 : f ((u : Fˣ) : F) σ ^ n = 1 := by
      rw [← hpow _ (Units.ne_zero _), hu, h1]
    obtain ⟨j, -, hj⟩ := (hζ.map_of_injective hι).eq_pow_of_pow_eq_one h2
    exact ⟨ζ ^ j, by rw [map_pow, hj]⟩
  choose o ho using hex
  let g : rootsOfUnity n F → (Γ →* LL) := fun u =>
    { toFun := fun σ => t (o u σ)
      map_one' := by
        have : o u 1 = 1 := hι (by rw [ho, map_one, hone _ (Units.ne_zero _)])
        rw [this, map_one]
      map_mul' := by
        intro a b
        have : o u (a * b) = o u a * o u b :=
          hι (by rw [map_mul, ho, ho, ho, hmul _ (Units.ne_zero _)])
        rw [this, map_mul] }
  refine ⟨MonoidHom.mk' (fun u => (g u).toHomUnits) ?_, fun u σ => ⟨o u σ, ho u σ, rfl⟩⟩
  intro u v
  ext σ
  have : o (u * v) σ = o u σ * o v σ :=
    hι (by
      rw [map_mul, ho, ho, ho, Subgroup.coe_mul, Units.val_mul,
        hx _ _ (Units.ne_zero _) (Units.ne_zero _)])
  show t (o (u * v) σ) = t (o u σ) * t (o v σ)
  rw [this, map_mul]

end GlobalTheory
end

