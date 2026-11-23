module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ResidueFieldTeichmullerLiftExists
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem zero_one_mem_gammaSet_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q : ℕ} (hq2 : 2 ≤ q) {a : Ω} (ha : a ^ q = a) : a ∈ A := by
  rcases eq_or_ne a 0 with rfl | h0
  · exact A.zero_mem
  rcases A.mem_or_inv_mem a with h | h
  · exact h
  · have h1 : a * a ^ (q - 2) = 1 := by
      rw [← pow_succ', show q - 2 + 1 = q - 1 by omega]
      have : a ^ q = a ^ (q - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [this] at ha
      exact (mul_eq_right₀ h0).1 ha
    rw [eq_inv_of_mul_eq_one_left h1, ← inv_pow]
    exact A.pow_mem h _

private theorem eq_of_pow_eq_self_of_valuation_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q : ℕ} (hq : A.valuation (q : Ω) < 1) {a b : Ω} (ha : a ∈ A) (hb : b ∈ A) (ha' : a ^ q = a) (hb' : b ^ q = b) (hab : A.valuation (a - b) < 1) : a = b := by
  by_contra hne
  have hS : (∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i)) = 1 := by
    have h := geom_sum₂_mul a b q
    rw [ha', hb'] at h
    have hsub : a - b ≠ 0 := sub_ne_zero.2 hne
    exact (mul_eq_right₀ hsub).1 h
  set a' : A := ⟨a, ha⟩
  set b' : A := ⟨b, hb⟩
  have hS' : (∑ i ∈ Finset.range q, a' ^ i * b' ^ (q - 1 - i)) = 1 := by
    apply Subtype.ext
    simpa using hS
  have hr : IsLocalRing.residue A a' = IsLocalRing.residue A b' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hab
  have hq' : IsLocalRing.residue A (q : A) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hq
  have := congrArg (IsLocalRing.residue A) hS'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one] at this
  simp only [map_mul, map_pow, ← hr] at this
  rw [Finset.sum_congr rfl (fun i hi => by rw [← pow_add, Nat.add_sub_cancel' (by have := Finset.mem_range.1 hi; omega)])] at this
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← map_natCast (IsLocalRing.residue A), hq', zero_mul] at this
  exact zero_ne_one this

private theorem fin_lemma_3 {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l : ℕ} [hp : Fact l.Prime] (hl : A.valuation (l : Ω) < 1) (a : A) (halg : IsAlgebraic ℚ (a : Ω)) :
    ∃ q : ℕ, 2 ≤ q ∧ A.valuation (q : Ω) < 1 ∧ A.valuation ((a : Ω) ^ q - a) < 1 := by
  have hlK : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hl
  haveI : CharP (IsLocalRing.ResidueField A) l := (CharP.charP_iff_prime_eq_zero hp.out).2 hlK
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  obtain ⟨Q, hQ0, hQ⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 halg
  have hc0 : Q.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  have hQ'Ω : Polynomial.aeval (a : Ω) Q.primPart = 0 := by
    have h := hQ
    rw [Polynomial.eq_C_content_mul_primPart Q, map_mul, Polynomial.aeval_C] at h
    refine (mul_eq_zero.1 h).resolve_left ?_
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Ω]
    exact (map_ne_zero (algebraMap ℚ Ω)).2 (by simpa using hc0)
  have hQ'A : Polynomial.aeval a Q.primPart = 0 := by
    apply Subtype.ext
    change ((Polynomial.aeval a Q.primPart : A) : Ω) = (0 : Ω)
    rw [← hQ'Ω]
    exact (Polynomial.aeval_algHom_apply A.subtype.toIntAlgHom a Q.primPart).symm
  obtain ⟨i, hi⟩ : ∃ i, ¬ (l : ℤ) ∣ Q.primPart.coeff i := by
    by_contra hall
    push_neg at hall
    have hd : Polynomial.C (l : ℤ) ∣ Q.primPart := Polynomial.C_dvd_iff_dvd_coeff _ _ |>.2 hall
    have hu := Polynomial.isPrimitive_primPart Q _ hd
    rw [Int.isUnit_iff] at hu
    have := hp.out.two_le
    omega
  set Q2 := Q.primPart.map (Int.castRingHom (ZMod l))
  have hQ2 : Q2 ≠ 0 := by
    intro h
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) h
    simp only [Q2, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
    exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this)
  have hev : Polynomial.aeval (IsLocalRing.residue A a) Q2 = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (ZMod l) _).comp (Int.castRingHom _)) (algebraMap ℤ _), ← Polynomial.aeval_def]
    exact (Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a Q.primPart).trans (by
      change IsLocalRing.residue A (Polynomial.aeval a Q.primPart) = 0
      rw [hQ'A, map_zero])
  have hint : IsIntegral (ZMod l) (IsLocalRing.residue A a) := IsAlgebraic.isIntegral (⟨Q2, hQ2, hev⟩ : IsAlgebraic (ZMod l) (IsLocalRing.residue A a))
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})
  refine ⟨Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}), Fintype.one_lt_card, ?_, ?_⟩
  · have h0 := FiniteField.cast_card_eq_zero (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})
    have h1 : ((Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) : ℕ) : IsLocalRing.ResidueField A) = 0 := by
      have := congrArg (algebraMap (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) (IsLocalRing.ResidueField A)) h0
      rwa [map_natCast, map_zero] at this
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h1
    simpa using h1
  · have h0 := FiniteField.pow_card (⟨IsLocalRing.residue A a, IntermediateField.mem_adjoin_simple_self _ _⟩ : (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}))
    have h1 := congrArg Subtype.val h0
    simp only [IntermediateField.coe_pow] at h1
    rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h1
    simpa using h1

private theorem exists_r0_valuation_sub_lt_one_of_isAlgebraic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (hl : A.valuation (l : Ω) < 1) (a : A) (halg : IsAlgebraic ℚ (a : Ω)) :
    ∃ w ∈ R0 A, A.valuation (w - a) < 1 := by
  obtain ⟨q, hq2, hq, haq⟩ := fin_lemma_3 A hl a halg
  set T : Polynomial Ω := Polynomial.X ^ q - Polynomial.X with hT
  have hTm : T.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast (by omega : 1 < q))
  have hprod := (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hTm (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits T))).symm
  have hroot : ∀ w ∈ T.roots, w ^ q = w := by
    intro w hw
    have := (Polynomial.mem_roots hTm.ne_zero).1 hw
    simpa [T, sub_eq_zero] using this
  have hev : T.eval (a : Ω) = (T.roots.map fun w => (a : Ω) - w).prod := by
    conv_lhs => rw [hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hv : A.valuation (T.eval (a : Ω)) < 1 := by simpa [T] using haq
  rw [hev, map_multiset_prod, Multiset.map_map] at hv
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ T.roots, A.valuation ((a : Ω) - w) < 1 := by
    by_contra hno
    push_neg at hno
    have h1 : (T.roots.map (A.valuation ∘ fun w => (a : Ω) - w)).prod = 1 := by
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
      refine le_antisymm ?_ (hno w hw)
      exact (A.valuation_le_one_iff _).2 (A.sub_mem a.2 (zero_one_mem_gammaSet_one A hq2 (hroot w hw)))
    rw [h1] at hv
    exact lt_irrefl _ hv
  have hwA : w ∈ A := zero_one_mem_gammaSet_one A hq2 (hroot w hw)
  refine ⟨w, ⟨hwA, fun s hs => ?_⟩, ?_⟩
  · have hsq : (s w) ^ q = s w := by rw [← map_pow, hroot w hw]
    change s ∈ Inertia A at hs
    unfold Inertia at hs
    exact eq_of_pow_eq_self_of_valuation_sub_lt_one A hq (zero_one_mem_gammaSet_one A hq2 hsq) hwA hsq (hroot w hw) (hs.2 w ((A.valuation_le_one_iff _).2 hwA))
  · rw [Valuation.map_sub_swap]
    exact hwv

open Polynomial IsLocalRing in
theorem UpperTheory.Kd.C7.residue_field_teichmuller_lift_exists :
    UpperTheory.Kd.C7.FixedIntegersMonicHasRootModPrime := by
  intro l _ hl2 Ω _ _ _ A hA P hP hdeg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : A.valuation (l : Ω) < 1 := by
    obtain ⟨pl, hpl, hlpl⟩ := hA
    unfold IsPlaceOver at hpl
    have := (hpl (l : 𝓞 ℚ)).2 hlpl
    simpa using this
  set Pm := P.map (R0 A).subtype with hPm
  have hmon : Pm.Monic := hP.map _
  have hdeg' : Pm.natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective Subtype.val_injective P
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root Pm (by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg']
    exact_mod_cast hdeg.ne')
  have hcA : ∀ i, Pm.coeff i ∈ A := fun i => by
    rw [hPm, Polynomial.coeff_map]
    exact (P.coeff i).2.1
  have hαA : α ∈ A := by
    by_contra hn
    have hv1 : 1 < A.valuation α := by
      rw [← not_le, A.valuation_le_one_iff]
      exact hn
    have h0 : Pm.eval α = 0 := hα
    rw [hmon.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum] at h0
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h0
    have e : α ^ Pm.natDegree = -∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i := eq_neg_of_add_eq_zero_left h0
    have hle : A.valuation (∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i) ≤ A.valuation α ^ (Pm.natDegree - 1) := by
      apply Valuation.map_sum_le
      intro i hi
      rw [map_mul, map_pow]
      calc A.valuation (Pm.coeff i) * A.valuation α ^ i ≤ 1 * A.valuation α ^ i := by
            gcongr
            exact (A.valuation_le_one_iff _).2 (hcA i)
        _ = A.valuation α ^ i := one_mul _
        _ ≤ A.valuation α ^ (Pm.natDegree - 1) := by
            apply pow_le_pow_right₀ hv1.le
            have := Finset.mem_range.1 hi
            omega
    have := congrArg A.valuation e
    rw [Valuation.map_neg, map_pow] at this
    rw [← this] at hle
    have hlt : A.valuation α ^ (Pm.natDegree - 1) < A.valuation α ^ Pm.natDegree :=
      pow_lt_pow_right₀ hv1 (by omega)
    exact absurd hle (not_le.2 hlt)
  obtain ⟨w, hwR, hwv⟩ := exists_r0_valuation_sub_lt_one_of_isAlgebraic A hl ⟨α, hαA⟩ (Algebra.IsAlgebraic.isAlgebraic α)
  refine ⟨⟨w, hwR⟩, ?_⟩
  by_contra hnot
  obtain ⟨u, hu⟩ := inertia_invariant_valuation_uniformizer_bound l hl2 Ω A hA _ hnot
  have hsub : R0 A ≤ A.toSubring := fun x hx => hx.1
  set φ := Subring.inclusion hsub
  set PA := P.map φ
  have hcoe : ∀ y : A.toSubring, ((PA.eval y : A.toSubring) : Ω) = Pm.eval (y : Ω) := by
    intro y
    have : Pm = PA.map A.toSubring.subtype := by
      rw [hPm, Polynomial.map_map]
      rfl
    rw [this, Polynomial.eval_map (p := PA)]
    exact (Polynomial.eval₂_hom (p := PA) A.toSubring.subtype y).symm
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (⟨w, hwR.1⟩ : A.toSubring) ⟨α, hαA⟩ PA
  have hPw : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = (w - α) * (c : Ω) := by
    have h1 : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = Pm.eval w := by
      rw [hPm, Polynomial.eval_map]
      exact (Polynomial.eval₂_hom (R0 A).subtype _).symm
    have h2 := congrArg (fun z : A.toSubring => (z : Ω)) hc
    push_cast [hcoe] at h2
    rw [h1, ← sub_zero (Pm.eval w), ← (show Pm.eval α = 0 from hα)]
    exact h2
  have hsmall : A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) < 1 := by
    rw [hPw, map_mul]
    calc A.valuation (w - α) * A.valuation (c : Ω) ≤ A.valuation (w - α) * 1 := by
          gcongr
          exact (A.valuation_le_one_iff _).2 c.2
      _ = A.valuation (w - α) := mul_one _
      _ < 1 := hwv
  have hinv : ((u : R0 A) : Ω) * ((u⁻¹ : (R0 A)ˣ) : R0 A) = 1 := by
    rw [← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
  have hv2 := congrArg A.valuation hinv
  rw [map_mul, map_one, hu] at hv2
  have hle1 : A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 ((u⁻¹ : (R0 A)ˣ) : R0 A).2.1
  have : A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) * A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' hle1) hsmall
  rw [hv2] at this
  exact lt_irrefl _ this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ToBasis
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.ToBasisLogarithm

variable {l : ℕ} [Fact l.Prime]

private theorem norm_alg_le (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact z.2

private theorem norm_nat_le (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 := by
  simpa using norm_alg_le (l := l) (a : ℤ_[l])

private theorem cg_sum {ι : Type} [Fintype ι] (n : ℕ) (f g : ι → Qbar l) (h : ∀ i, Cg n (f i) (g i)) :
    Cg n (∑ i, f i) (∑ i, g i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => h i

private theorem cg_mul {n : ℕ} {a b y : Qbar l} (h : Cg n a b) (hy : ‖y‖ ≤ 1) : Cg n (a * y) (b * y) := by
  unfold Cg at *
  rw [← sub_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans h

private theorem cg_trans {n : ℕ} {a b c : Qbar l} (h : Cg n a b) (h' : Cg n b c) : Cg n a c := by
  unfold Cg at *
  rw [show a - c = (a - b) + (b - c) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cg_nat {n x y : ℕ} (h : (x : ZMod (l ^ n)) = y) : Cg n (x : Qbar l) y := by
  obtain ⟨e, he⟩ := (Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm)
  have he' : (x : Qbar l) - y = (l : Qbar l) ^ n * (e : Qbar l) := by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) he
  have hn : ‖(e : Qbar l)‖ ≤ 1 := by simpa using norm_alg_le (l := l) (e : ℤ_[l])
  unfold Cg
  rw [he', norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hn

private theorem coords {c : Coef l} (β : Bas c) (hβ : ∀ i, ‖β.val i‖ ≤ 1) (n : ℕ) (o : Qbar l) (ho : o ∈ c.O) :
    ∃ a : Fin β.d → ℕ, Cg n o (∑ i, β.val i * (a i : Qbar l)) := by
  refine ⟨fun i => (β.e.repr ⟨o, ho⟩ i).appr n, ?_⟩
  have h1 : o = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i) := by
    have := congrArg (fun x : c.O => (x : PadicAlgCl l)) (β.e.sum_repr ⟨o, ho⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]; rfl
  refine cg_trans (b := ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i)) ?_ (cg_sum n _ _ fun i => ?_)
  · unfold Cg; rw [← h1, sub_self, norm_zero]; exact norm_nonneg _
  · rw [mul_comm (β.val i), mul_comm (β.val i)]
    refine cg_mul ?_ (hβ i)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n (β.e.repr ⟨o, ho⟩ i))
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
    rw [map_mul, map_pow, map_natCast, map_sub, map_natCast] at this
    unfold Cg
    rw [← this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_alg_le e)

private theorem cg_swap {ι : Type} [Fintype ι] {d n : ℕ} (b : Fin d → Qbar l) (o y : ι → Qbar l) (a : ι → Fin d → ℕ)
    (h : ∀ k, Cg n (o k) (∑ i, b i * (a k i : Qbar l))) (hy : ∀ k, ‖y k‖ ≤ 1) :
    Cg n (∑ k, o k * y k) (∑ i, b i * ∑ k, (a k i : Qbar l) * y k) := by
  have e : ∑ i, b i * ∑ k, (a k i : Qbar l) * y k = ∑ k, (∑ i, b i * (a k i : Qbar l)) * y k := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e]
  exact cg_sum n _ _ fun k => cg_mul (h k) (hy k)

private theorem logd {Ω : Type} [Field Ω] {ι : Type} (S : Finset ι) (P : ι → Polynomial Ω) (a : ι → ℕ) (z : Ω)
    (hP : ∀ k, (P k).eval z ≠ 0) :
    z * (Polynomial.derivative (∏ k ∈ S, P k ^ a k)).eval z / (∏ k ∈ S, P k ^ a k).eval z =
      ∑ k ∈ S, (a k : Ω) * (z * (Polynomial.derivative (P k)).eval z / (P k).eval z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h0 : (∏ k ∈ S, P k ^ a k).eval z ≠ 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [Polynomial.eval_pow]; exact pow_ne_zero _ (hP k)
    have hk0 := hP k
    rw [Finset.prod_insert hk, Finset.sum_insert hk, ← ih, Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rcases a k with _ | r
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      field_simp

private theorem pv_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) {z : Ω} (hz : z ∈ A) :
    (P.map (R0 A).subtype).eval z ∈ A := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.eval_add]; exact A.add_mem _ _ hp hq
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    exact A.mul_mem _ _ a.2.1 (A.toSubring.pow_mem hz n)

private theorem pv_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (z : Ω)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    (P.map (R0 A).subtype).eval (s z) = s ((P.map (R0 A).subtype).eval z) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.eval_add, Polynomial.eval_add, map_add (f := _), hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial, map_mul, map_pow]
    congr 1
    exact (a.2.2 s hs).symm

private theorem root_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {z : Ω} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with h | h
  · exact h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have e : z = (z⁻¹) ^ k := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_right (by rw [← hz, pow_succ])
    rw [e]; exact A.toSubring.pow_mem h k

private theorem ex_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}
    (h : ∀ u : ℤ_[l]ˣ, ∃ s ∈ Ine (F := ℚ) A, cycZ ℚ Ω l s = u) {m : ℕ} (hm : 1 ≤ m) {z : Ω} (hz : z ^ l ^ m = 1)
    (b : (ZMod (l ^ m))ˣ) : ∃ s ∈ Ine (F := ℚ) A, s z = z ^ (b : ZMod (l ^ m)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hc : ((b : ZMod (l ^ m)).val).Coprime l :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self l (by omega)) (ZMod.val_coe_unit_coprime b)
  have hu : IsUnit (((b : ZMod (l ^ m)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 hc.symm
  obtain ⟨s, hs, hs'⟩ := h hu.unit
  refine ⟨s, hs, ?_⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) z hz
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)) = hu.unit := hs'
  rw [h2, IsUnit.unit_spec, map_natCast, ZMod.natCast_zmod_val] at h1
  exact h1

end UpperTheory.Kd.C7.ToBasisLogarithm

open UpperTheory.Kd.C7.ToBasisLogarithm in
theorem UpperTheory.Kd.C7.pToBasis :
    UpperTheory.Kd.C7.SToBasis := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ j hj Z m n ι _ P o hm hP ho hK
  classical
  obtain ⟨hprim, hnm, hu, ho1, hpres⟩ := hK
  have hβ := ((pBasEx l c).2 β).1
  have hfr := (pFrobEx l hl Ω A hA).2.2
  choose a ha using fun k => coords β hβ n (o k) (ho k)
  have hQ : ∀ k, ∃ Q : Polynomial (R0 A), Q.map (R0 A).subtype = P k := fun k =>
    ⟨(P k).toSubring (R0 A) (fun x hx => hP k x hx), Polynomial.map_toSubring _ _ _⟩
  choose Q hQ using hQ
  have hmap : ∀ i, (∏ k, Q k ^ a k i).map (R0 A).subtype = ∏ k, P k ^ a k i := fun i => by
    simp only [Polynomial.map_prod, Polynomial.map_pow, hQ]
  have hpv : ∀ i, pv (∏ k, Q k ^ a k i) (ζ m) = ∏ k, (P k).eval (ζ m) ^ a k i := fun i => by
    rw [pv, Polynomial.eval₂_eq_eval_map, hmap, Polynomial.eval_prod]
    simp only [Polynomial.eval_pow]
  refine ⟨fun i => ∏ k, Q k ^ a k i, ⟨hprim, hnm, fun i => ?_, hβ, fun s hs hc hz => ?_⟩, fun b => ?_⟩
  · dsimp only
    rw [hpv]
    refine ⟨A.toSubring.prod_mem fun k _ => A.toSubring.pow_mem (hu k).1 _,
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hu k).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact A.toSubring.prod_mem fun k _ => by rw [← inv_pow]; exact A.toSubring.pow_mem (hu k).2.2 _
  · obtain ⟨κ, hκ, hcg⟩ := hpres s hs hc hz
    have hKA := (pKumAlg l hl Ω A hA ζ hζ m n hnm s ⟨hs, hc⟩).1
    refine ⟨fun i => ∑ k, (a k i : ZMod (l ^ n)) * κ k, fun i => ?_, ?_⟩
    · dsimp only
      rw [hpv]
      generalize (Finset.univ : Finset ι) = S
      induction S using Finset.induction_on with
      | empty => simpa using kumVal_one (l := l) n (ζ n) s
      | insert k S hk ih =>
        rw [Finset.prod_insert hk, Finset.sum_insert hk]
        exact (hKA _ _ _ _ ((hKA _ _ _ _ (hκ k) (hκ k)).2.2 (a k i)) ih).1
    · refine cg_trans hcg (cg_trans (cg_swap β.val o _ a ha fun k => norm_nat_le _) (cg_sum n _ _ fun i => ?_))
      rw [mul_comm (β.val i), mul_comm (β.val i)]
      refine cg_mul ?_ (hβ i)
      haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      have := cg_nat (l := l) (n := n) (x := ∑ k, a k i * (κ k).val) (y := (∑ k, (a k i : ZMod (l ^ n)) * κ k).val)
        (by simp)
      simpa using this
  · obtain ⟨s, hs, hsz⟩ := ex_conj hfr hm (hζ m).1.pow_eq_one b
    have hzA : ζ m ∈ A := root_mem A (pow_pos (Fact.out : l.Prime).pos m) (hζ m).1.pow_eq_one
    have hz : ζ m ^ (b : ZMod (l ^ m)).val ∈ A := A.toSubring.pow_mem hzA _
    have hev : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) = s ((P k).eval (ζ m)) := fun k => by
      rw [← hsz, ← hQ, pv_conj _ _ hs]
    have hne : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) ≠ 0 := fun k => by
      rw [hev]; exact (map_ne_zero s).2 (hu k).2.1
    unfold htv
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hmap, logd _ P _ _ hne, map_sum, map_mul j, map_natCast]
    refine cg_swap β.val o _ a ha fun k => hj _ ?_
    rw [div_eq_mul_inv]
    refine A.mul_mem _ _ (A.mul_mem _ _ hz ?_) ?_
    · rw [← hQ, Polynomial.derivative_map]; exact pv_mem _ hz
    · rw [hev, ← map_inv₀, apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs)]; exact (hu k).2.2
end

