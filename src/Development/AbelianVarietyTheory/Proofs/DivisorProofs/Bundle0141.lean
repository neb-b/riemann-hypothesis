module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfSpanningNumberFieldLattice
section
open NumberField

namespace GlobalTheory

theorem exists_pos_nat_smul_mem_of_span_eq_top (E : Type) [Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (h : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ q : ℕ, 0 < q ∧ (q : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZero
section
open TensorProduct

namespace GlobalTheory

theorem exists_pow_eq_of_kaehler_D_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (K : Type) [Field K] [Algebra k K] (f : K), KaehlerDifferential.D k K f = 0 → ∃ h : K, h ^ p = f := by
  intro p hp k _ _ hk K _ _ f hf
  by_contra hne
  have hK : (p : K) = 0 := by
    have := congrArg (algebraMap k K) hk
    simpa using this
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 hK
  let F : Subfield K := (frobenius K p).fieldRange
  have hF : ∀ y : K, y ^ p ∈ F := fun y => ⟨y, by simp [frobenius_def]⟩
  have hfF : f ∉ F := by
    rintro ⟨h, hh⟩
    exact hne ⟨h, by simpa [frobenius_def] using hh⟩
  obtain ⟨L, hFL, hfL, htop⟩ := _root_.GlobalTheory.cfmax_main p K F hF f hfF
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.exists_derivation_eq_one_of_pow_mem p K L f hfL (hFL (hF f)) htop
  have hkL : ∀ a : k, algebraMap k K a ∈ L := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    rw [← hb, map_pow]
    exact hFL (hF _)
  have hD0 : ∀ a : k, D (algebraMap k K a) = 0 := fun a =>
    D.map_algebraMap (⟨_, hkL a⟩ : L)
  let D' : Derivation k K K := Derivation.mk'
    { toFun := D
      map_add' := fun x y => map_add D x y
      map_smul' := fun a x => by
        simp only [Algebra.smul_def, RingHom.id_apply, Derivation.leibniz, hD0, smul_eq_mul]
        simp }
    (fun a b => D.leibniz a b)
  have h1 : D' f = 1 := hD
  have h2 := D'.liftKaehlerDifferential_comp_D f
  rw [hf, map_zero, h1] at h2
  exact zero_ne_one h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
section
open Polynomial GlobalTheory.EtC

namespace GlobalTheory

theorem exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [hP : P.IsMaximal] (b : B) :
    ∃ c : k, b - algebraMap k B c ∈ P := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  let φ : (B ⧸ P) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ (Ideal.Quotient.mk P b), ?_⟩
  have h : algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) = Ideal.Quotient.mk P b := by
    apply φ.toRingHom.injective
    simp
  have h2 : Ideal.Quotient.mk P (algebraMap k B (φ (Ideal.Quotient.mk P b))) =
      algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) := rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h2, h, sub_self]

theorem exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ) (hq : IsUnit (q : k))
    (P : Ideal B) [hP : P.IsMaximal] (b : B) (hb : b ∉ P) :
    ∀ m : ℕ, ∃ r : B, b - r ^ q ∈ P ^ (m + 1) := by
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hq
    · exact h
  have hqB : IsUnit (q : B) := by
    have := hq.map (algebraMap k B); simpa using this
  intro m
  induction m with
  | zero =>
    obtain ⟨c, hc⟩ := exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed k B P b
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hq0
    refine ⟨algebraMap k B z, ?_⟩
    rw [← map_pow, hz]; simpa using hc
  | succ m ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, e = b - r ^ q := ⟨_, rfl⟩
    rw [← he] at hr
    have hrP : r ∉ P := by
      intro h
      apply hb
      have h1 : r ^ q ∈ P := P.pow_mem_of_mem h q hq0
      have h2 : e ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero m) hr
      have : b = e + r ^ q := by rw [he]; ring
      rw [this]; exact P.add_mem h2 h1
    have hderP : (q : B) * r ^ (q - 1) ∉ P := by
      intro h
      rcases hP.isPrime.mem_or_mem h with h | h
      · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P h hqB)
      · exact hrP (hP.isPrime.mem_of_pow_mem _ h)
    obtain ⟨w, i, hi, hw⟩ := hP.exists_inv hderP
    obtain ⟨t, ht⟩ := binomExpansion (X ^ q : B[X]) r (e * w)
    simp [derivative_X_pow] at ht
    refine ⟨r + e * w, ?_⟩
    have key : b - (r + e * w) ^ q = e * i - t * w ^ 2 * e ^ 2 := by
      rw [ht]; linear_combination (-e) * hw - he
    rw [key]
    refine Ideal.sub_mem _ ?_ ?_
    · rw [pow_succ]; exact Ideal.mul_mem_mul hr hi
    · apply Ideal.mul_mem_left
      have h3 : e ^ 2 ∈ (P ^ (m + 1)) ^ 2 := Ideal.pow_mem_pow hr 2
      rw [← pow_mul] at h3
      exact Ideal.pow_le_pow_right (by omega) h3

theorem exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ),
    IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b c : B, b * c - 1 ∈ Ideal.span {f} →
      ∃ r : B, b - r ^ q ∈ Ideal.span {f} := by
  intro k B _ _ _ _ _ _ q hq f hf b c hbc
  classical
  have hI : Ideal.span {f} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf
  have hroot : ∀ P : (UniqueFactorizationMonoid.factors (Ideal.span {f})).toFinset, ∃ r : B,
      b - r ^ q ∈ (P : Ideal B) ^ Multiset.count (P : Ideal B)
        (UniqueFactorizationMonoid.factors (Ideal.span {f})) := by
    intro P
    have hmem := Multiset.mem_toFinset.mp P.prop
    have hprime : Prime (P : Ideal B) := UniqueFactorizationMonoid.prime_of_factor _ hmem
    have hne : (P : Ideal B) ≠ ⊥ := hprime.ne_zero
    haveI hmax : (P : Ideal B).IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hne
    have hle : Ideal.span {f} ≤ (P : Ideal B) :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hmem)
    have hb : b ∉ (P : Ideal B) := by
      intro h
      apply hmax.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 := hle hbc
      have : (1 : B) = b * c - (b * c - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h) h1
    obtain ⟨r, hr⟩ := exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed k B q hq (P : Ideal B) b hb
      (Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors (Ideal.span {f})))
    exact ⟨r, Ideal.pow_le_pow_right (Nat.le_succ _) hr⟩
  choose r hr using hroot
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    ((IsDedekindDomain.quotientEquivPiFactors hI).symm (fun P => Ideal.Quotient.mk _ (r P)))
  refine ⟨s, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (IsDedekindDomain.quotientEquivPiFactors hI).injective
  rw [map_zero]
  funext P
  have h1 := congrFun (congrArg (IsDedekindDomain.quotientEquivPiFactors hI) hs) P
  rw [RingEquiv.apply_symm_apply, IsDedekindDomain.quotientEquivPiFactors_mk] at h1
  simp only at h1
  rw [IsDedekindDomain.quotientEquivPiFactors_mk]
  show Ideal.Quotient.mk _ (b - s ^ q) = 0
  rw [map_sub, map_pow, h1, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hr P

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChangeStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  first | (exact @GlobalTheory.projective_baseChange_presentation_matrix) | (exact GlobalTheory.projective_baseChange_presentation_matrix) | (intros; apply GlobalTheory.projective_baseChange_presentation_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemForallGtEqMaximalIdeal
section
open IsLocalRing

namespace GlobalTheory

theorem exists_prime_not_mem_forall_gt_eq_maximalIdeal (C : Type) [CommRing C] [IsDomain C]
    [IsLocalRing C] [IsNoetherianRing C] (x : C) (hx : x ≠ 0) (hxm : x ∈ maximalIdeal C) :
    ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  classical

  have hnil : ¬ IsNilpotent x := fun h => hx (IsNilpotent.eq_zero h)
  haveI : Nontrivial (Localization.Away x) :=
    (IsLocalization.injective (Localization.Away x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)).nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization.Away x)
  set q : Ideal C := M.comap (algebraMap C (Localization.Away x)) with hqdef
  have hMp : M.IsPrime := hM.isPrime
  have hqd := (IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) M).mp hMp
  have hqp : q.IsPrime := hqd.1
  have hxq : x ∉ q := fun h =>
    Set.disjoint_left.mp hqd.2 (Submonoid.mem_powers x) h

  have habove : ∀ P : Ideal C, P.IsPrime → q < P → x ∈ P := by
    intro P hP hlt
    by_contra hxP
    have hdisj : Disjoint (Submonoid.powers x : Set C) P := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ h
      exact hxP (hP.mem_of_pow_mem n h)
    have hPL := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) P hP hdisj
    have hcomap := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) hP hdisj
    have hMle : M ≤ P.map (algebraMap C (Localization.Away x)) := by
      rw [← IsLocalization.map_under (Submonoid.powers x) (Localization.Away x) M]
      exact Ideal.map_mono hlt.le
    have heq := hM.eq_of_le hPL.ne_top hMle
    have : q = P := by rw [hqdef, heq]; exact hcomap
    exact hlt.ne this
  refine ⟨q, hqp, hxq, fun P hP hlt => ?_⟩

  set f := Ideal.Quotient.mk q with hfdef
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = q := Ideal.mk_ker
  haveI : IsDomain (C ⧸ q) := Ideal.Quotient.isDomain q
  set m' : Ideal (C ⧸ q) := (maximalIdeal C).map f with hm'
  have hqm : q ≤ maximalIdeal C := le_maximalIdeal hqp.ne_top
  have hm'p : m'.IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hqm)
  have hx0 : f x ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hxq
  have hht : m'.height ≤ 1 := by
    refine height_le_one_of_forall_mem m' hx0 ?_
    intro p' hp' hp'0 _
    have hcp : (p'.comap f).IsPrime := Ideal.comap_isPrime f p'
    have hqc : q < p'.comap f := by
      refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        simp [Ideal.mem_comap, hfdef, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · intro e
        apply hp'0
        rw [← Ideal.map_comap_of_surjective f hsurj p', ← e]
        exact (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge
    exact habove _ hcp hqc
  have hPp' : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hlt.le)
  have hP0 : P.map f ≠ ⊥ := by
    intro e
    rw [Ideal.map_eq_bot_iff_le_ker, hker] at e
    exact hlt.ne (le_antisymm hlt.le e)
  have hPm : P.map f ≤ m' := Ideal.map_mono (le_maximalIdeal hP.ne_top)
  have hPeq : P.map f = m' := by
    by_contra hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPm hne)
    have h3 : (⊥ : Ideal (C ⧸ q)).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hht)
    simp at h3
    exact absurd h3 (by decide)
  have hPc : P = (P.map f).comap f := by
    rw [Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hlt.le]
  have hmc : maximalIdeal C = m'.comap f := by
    rw [hm', Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hqm]
  rw [hPc, hPeq, ← hmc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveElementSeparabilityCertificate
section
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

namespace GlobalTheory.SepPoint

theorem exists_clear_poly {k F : Type} [Field k] [Field F] [Algebra k F] (s : Set F)
    (p : (IntermediateField.adjoin k s)[X]) :
    ∃ q : (Algebra.adjoin k s)[X], ∃ b : Algebra.adjoin k s, b ≠ 0 ∧
      q.map (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s)) =
        C (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s) b) * p := by
  obtain ⟨b, hb, h⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Algebra.adjoin k s)) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (Algebra.adjoin k s)) p, b,
    nonZeroDivisors.ne_zero hb, ?_⟩
  rw [h, ← IsScalarTower.algebraMap_smul (IntermediateField.adjoin k s) b p, Polynomial.smul_eq_C_mul]

theorem aeval_mem_adjoin_insert {k F : Type} [Field k] [Field F] [Algebra k F]
    (R : Subalgebra k F) (θ : F) (g : R[X]) :
    aeval θ g ∈ Algebra.adjoin k (insert θ (R : Set F)) := by
  rw [aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (g.coeff i).2))
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)

theorem exists_common_mul_mem {k F : Type} [Field k] [Field F] [Algebra k F]
    (R S : Subalgebra k F) (hRS : R ≤ S) (T : Finset F)
    (h : ∀ x ∈ T, ∃ b : R, b ≠ 0 ∧ (b : F) * x ∈ S) :
    ∃ B : R, B ≠ 0 ∧ ∀ x ∈ T, (B : F) * x ∈ S := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a T ha ih =>
    obtain ⟨B, hB, hBT⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨b, hb, hba⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨b * B, mul_ne_zero hb hB, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have : ((b * B : R) : F) * x = (B : F) * ((b : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS B.2) hba
    · have : ((b * B : R) : F) * x = (b : F) * ((B : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS b.2) (hBT x hx)

end GlobalTheory.SepPoint

namespace GlobalTheory.SepPoint

theorem exists_primitive_sep_certificate (k F : Type) [Field k] [Field F] [Algebra k F]
    (s : Finset F) (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F) (T : Finset F) :
    ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧
      ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧
        ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)),
          U * minpoly (Algebra.adjoin k (s : Set F)) θ +
              V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) =
            Polynomial.C H ∧
          ∀ x ∈ T, (H : F) * x ∈
            Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  classical
  haveI hIC := isIntegrallyClosed_adjoin k F s hs.1
  have hr : Set.range ((↑) : s → F) = (s : Set F) := Subtype.range_coe
  have halg : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F := by
    have := hs.isAlgebraic
    rw [hr] at this
    exact this

  let E := IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) (T : Set F)
  haveI : FiniteDimensional (IntermediateField.adjoin k (s : Set F)) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral _ x
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) E :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ E F
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (IntermediateField.adjoin k (s : Set F)) E
  have hE : E = IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {(α : F)} := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]

  obtain ⟨c, hc, hcint⟩ := IsAlgebraic.exists_integral_multiple (halg.isAlgebraic (α : F))
  set θ : F := c • (α : F) with hθdef
  refine ⟨θ, hcint, ?_⟩

  have hmin : minpoly (IntermediateField.adjoin k (s : Set F)) θ =
      (minpoly (Algebra.adjoin k (s : Set F)) θ).map
        (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F))) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hcint
  have hsepθ : (minpoly (IntermediateField.adjoin k (s : Set F)) θ).Separable :=
    Algebra.IsSeparable.isSeparable _ θ
  obtain ⟨u, v, huv⟩ := hsepθ
  obtain ⟨u', b₁, hb₁, hu'⟩ := exists_clear_poly (k := k) (s : Set F) u
  obtain ⟨v', b₂, hb₂, hv'⟩ := exists_clear_poly (k := k) (s : Set F) v

  have hden : ∀ x ∈ T, ∃ b : Algebra.adjoin k (s : Set F), b ≠ 0 ∧ (b : F) * x ∈
      Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
    intro x hx
    have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ hx
    rw [hE] at hxE
    have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
    have hcmem : (c : F) ∈ IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ} :=
      IntermediateField.algebraMap_mem _
        (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F)) c)
    have hαmem : (α : F) ∈ IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ} := by
      have : (α : F) = (c : F)⁻¹ * θ := by
        show (α : F) = (c : F)⁻¹ * ((c : F) * (α : F))
        rw [← mul_assoc, inv_mul_cancel₀ hcF, one_mul]
      rw [this]
      exact mul_mem (inv_mem hcmem) (IntermediateField.mem_adjoin_simple_self _ _)
    have hxθ := IntermediateField.adjoin_simple_le_iff.mpr hαmem hxE
    have hθint : IsIntegral (IntermediateField.adjoin k (s : Set F)) θ :=
      Algebra.IsSeparable.isIntegral _ θ
    have hxθ' : x ∈ (IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ}).toSubalgebra :=
      hxθ
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hxθ'
    obtain ⟨g, hg⟩ := hxθ'
    obtain ⟨q, b, hb, hq⟩ := exists_clear_poly (k := k) (s : Set F) g
    refine ⟨b, hb, ?_⟩
    have : (b : F) * x = aeval θ q := by
      rw [← hg, ← Polynomial.aeval_map_algebraMap (IntermediateField.adjoin k (s : Set F)) θ q, hq,
        Polynomial.aeval_mul, Polynomial.aeval_C]
      rfl
    rw [this]
    exact aeval_mem_adjoin_insert _ θ q
  obtain ⟨B, hB, hBT⟩ := exists_common_mul_mem (Algebra.adjoin k (s : Set F))
    (Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)))
    (fun y hy => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)) T hden
  refine ⟨b₁ * b₂ * B, mul_ne_zero (mul_ne_zero hb₁ hb₂) hB, C (b₂ * B) * u', C (b₁ * B) * v', ?_, ?_⟩
  · apply Polynomial.map_injective
      (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F)))
      (IsFractionRing.injective _ _)
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, ← Polynomial.derivative_map,
      ← hmin, hu', hv', map_mul]
    linear_combination (C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) b₁) *
      C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) b₂) *
      C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) B)) * huv
  · intro x hx
    have : ((b₁ * b₂ * B : Algebra.adjoin k (s : Set F)) : F) * x =
        ((b₁ * b₂ : Algebra.adjoin k (s : Set F)) : F) * ((B : F) * x) := by push_cast; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (b₁ * b₂).2))
      (hBT x hx)

end GlobalTheory.SepPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdealOfIdempotentStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_ideal_of_idempotent' : ∀ (A : Type) [CommRing A] (I : Type) [Fintype I] (n : ℕ) (P : I → Matrix (Fin n) (Fin n) A),
    (∀ i, P i * P i = P i) → ∀ (m : ℕ), ∃ x : A, ∀ (T : Type) [CommRing T] (f : A →+* T),
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : I),
          Module.rankAtStalk (LinearMap.range (P i).mulVecLin)
            (⟨RingHom.ker (h.comp f), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = m) ↔ f x = 0) := by
  first | (exact @GlobalTheory.exists_rank_ideal_of_idempotent) | (exact GlobalTheory.exists_rank_ideal_of_idempotent) | (intros; apply GlobalTheory.exists_rank_ideal_of_idempotent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteIntStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C] [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k), ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  first | (exact @GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (exact GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (intros; apply GlobalTheory.ringHom_exists_sep_of_moduleFinite_int  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemRangeOfSurjectiveLocalizedMapStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map : ∀ (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) → ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  exact @GlobalTheory.exists_smul_mem_range_of_surjective_localization_map
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjPiQuotPowKerEqStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq : ∀ {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A), P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d → ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧ ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  first | (exact @GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (exact GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (intros; apply GlobalTheory.exists_surj_pi_quot_pow_ker_eq  <;> assumption)
end

