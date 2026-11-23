module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveMonicSeparableSpecialization
section
open Polynomial IntermediateField

noncomputable section

namespace GlobalTheory.PrimTransc

theorem exists_separable_specialization {D : ℕ} (P : (MvPolynomial (Fin D) ℚ)[X])
    (h : (P.map (algebraMap (MvPolynomial (Fin D) ℚ) (FractionRing (MvPolynomial (Fin D) ℚ)))).Separable) :
    ∃ c : Fin D → ℚ, (P.map (MvPolynomial.eval c)).Separable := by
  set R := MvPolynomial (Fin D) ℚ
  set F := FractionRing R
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨da, hda, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨db, hdb, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors R) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors R) b
  have key : (C db * A) * P + (C da * B) * derivative P = C (da * db) := by
    apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
    have hA' : A.map (algebraMap R F) = C (algebraMap R F da) * a := by
      rw [hA, ← algebraMap_smul F da a, smul_eq_C_mul]
    have hB' : B.map (algebraMap R F) = C (algebraMap R F db) * b := by
      rw [hB, ← algebraMap_smul F db b, smul_eq_C_mul]
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, hA', hB',
      ← derivative_map, map_mul]
    linear_combination (C (algebraMap R F da) * C (algebraMap R F db)) * hab
  have hδ : da * db ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hda) (nonZeroDivisors.ne_zero hdb)
  obtain ⟨c, hc⟩ : ∃ c : Fin D → ℚ, MvPolynomial.eval c (da * db) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hδ (MvPolynomial.funext fun c => by simpa using hno c)
  refine ⟨c, ?_⟩
  have key' := congrArg (Polynomial.map (MvPolynomial.eval c)) key
  simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, ← derivative_map] at key'
  have hinv : C (MvPolynomial.eval c (da * db))⁻¹ * C (MvPolynomial.eval c (da * db)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  refine ⟨C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c db) * A.map (MvPolynomial.eval c)),
    C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c da) * B.map (MvPolynomial.eval c)), ?_⟩
  linear_combination C (MvPolynomial.eval c (da * db))⁻¹ * key' + hinv

theorem exists_mul_mem_adjoin {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F {θ}) :
    ∃ d : R, d ≠ 0 ∧ algebraMap R K d * z ∈ Algebra.adjoin R {θ} := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R F K h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 θ z hz; exact @_root_.GlobalTheory.TargetInequalityLemmas.target)
  | exact @_root_.GlobalTheory.TargetInequalityLemmas.target
  | exact _root_.GlobalTheory.TargetInequalityLemmas.target
  | (apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetInequalityLemmas.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetInequalityLemmas.target ..)

theorem exists_primitive_monic_separable_specialization :
    ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x →
      ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ))
        (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧
        (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧
        (P.map (MvPolynomial.eval c)).Separable := by
  intro K _ _ D x hx J _ e
  classical
  have := Fintype.ofFinite J
  let R := MvPolynomial (Fin D) ℚ
  let F := FractionRing R
  let φ : R →ₐ[ℚ] K := MvPolynomial.aeval x
  have φinj : Function.Injective φ := hx.1
  letI : Algebra R K := φ.toRingHom.toAlgebra
  have hφ : ∀ r : R, algebraMap R K r = φ r := fun r => rfl
  haveI : IsScalarTower ℚ R K := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 φinj
  letI : Algebra F K := FractionRing.liftAlgebra R K
  haveI : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K
  haveI : CharZero F := RingHom.charZero (algebraMap F K)
  haveI : Algebra.IsAlgebraic R K :=
    haveI := hx.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hx.1.aevalEquiv.symm.toRingHom) (g := RingHom.id K)
      (Algebra.IsAlgebraic.isAlgebraic y) hx.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hx.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra, φ]))⟩
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R F)

  let E := IntermediateField.adjoin F (Set.range e)
  haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
    (fun y _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) y).isIntegral)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hαE : F⟮(α : K)⟯ = E := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congrArg IntermediateField.lift hα
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic (R := R) (α : K))
  set θ : K := y • (α : K) with hθdef
  have hθF : IsIntegral F θ := (Algebra.IsAlgebraic.isAlgebraic (R := F) θ).isIntegral
  have hyF : algebraMap R F y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hy0
  have hαθ : (α : K) ∈ F⟮θ⟯ := by
    have : (α : K) = algebraMap F K (algebraMap R F y)⁻¹ * θ := by
      rw [hθdef, Algebra.smul_def, IsScalarTower.algebraMap_apply R F K, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hyF, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F θ)
  have heθ : ∀ j, e j ∈ Algebra.adjoin F {θ} := by
    intro j
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθF.isAlgebraic]
    have h1 : E ≤ F⟮θ⟯ := hαE ▸ IntermediateField.adjoin_simple_le_iff.2 hαθ
    exact h1 (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  choose d hd0 hdm using fun j => exists_mul_mem_adjoin (R := R) (F := F) θ (e j) (heθ j)

  let P := minpoly R θ
  let ψ₀ : AdjoinRoot P →ₐ[R] K := AdjoinRoot.liftAlgHom P (Algebra.ofId R K) θ (minpoly.aeval R θ)
  let ψ : AdjoinRoot P →ₐ[ℚ] K := ψ₀.restrictScalars ℚ
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun q hq => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective q
    have hq' : Polynomial.aeval θ q = 0 := hq
    exact AdjoinRoot.mk_eq_zero.2 ((minpoly.isIntegrallyClosed_dvd_iff hyint q).1 hq')
  have hrange : Algebra.adjoin R {θ} ≤ ψ₀.range := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨AdjoinRoot.root P, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
  have hsep : (P.map (algebraMap R F)).Separable := by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F hyint]
    exact (minpoly.irreducible hθF).separable
  obtain ⟨c, hc⟩ := exists_separable_specialization P hsep
  refine ⟨P, ψ, algebraMap R K (∏ j, d j), c, minpoly.monic hyint, hψinj, fun i => ?_, ?_, fun j => ?_, hc⟩
  · show ψ₀ (AdjoinRoot.of P (MvPolynomial.X i)) = x i
    rw [← AdjoinRoot.algebraMap_eq, AlgHom.commutes, hφ]
    exact MvPolynomial.aeval_X x i
  · exact (map_ne_zero_iff _ φinj).2 (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j)
  · have hm : algebraMap R K (∏ j, d j) * e j ∈ Algebra.adjoin R {θ} := by
      rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ j), mul_comm (d j), map_mul, mul_assoc]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdm j)
    obtain ⟨a, ha⟩ := hrange hm
    exact ⟨a, ha⟩

end GlobalTheory.PrimTransc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueIdempotent
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.AzumayaResidue

theorem isSimpleRing_of_isAzumaya (k B : Type) [Field k] [Ring B] [Algebra k B]
    [IsAzumaya k B] [Nontrivial B] : IsSimpleRing B := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases h : I = ⊥
  · exact Or.inl h
  right
  obtain ⟨z, hzI, hz0⟩ : ∃ z ∈ I, z ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h
    ext x
    rw [TwoSidedIdeal.mem_bot]
    exact ⟨hc x, fun hx => hx ▸ I.zero_mem⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k B, φ z ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz0 ((Module.forall_dual_apply_eq_zero_iff k z).1 hc)
  let f : B →ₗ[k] B := (φ z)⁻¹ • φ.smulRight (1 : B)
  have hf : f z = 1 := by
    simp [f, hφ]
  obtain ⟨t, ht⟩ := (IsAzumaya.bij (R := k) (A := B)).2 f
  have key : ∀ t : B ⊗[k] Bᵐᵒᵖ, AlgHom.mulLeftRight k B t z ∈ I := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [I.zero_mem]
    | tmul a b =>
      rw [AlgHom.mulLeftRight_apply]
      exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hzI)
    | add x y hx hy =>
      rw [map_add (f := _), LinearMap.add_apply]
      exact I.add_mem hx hy
  rw [← TwoSidedIdeal.one_mem_iff, ← hf, ← ht]
  exact key t

theorem exists_rankOne_idempotent (k B : Type) [Field k] [Finite k] [Ring B] [Algebra k B]
    [IsAzumaya k B] [Nontrivial B] :
    ∃ x : B, x * x = x ∧ (∀ y : B, ∃ c : k, x * y * x = c • x) ∧
      ∃ (N : ℕ) (a b : Fin N → B), ∑ i, a i * x * b i = 1 := by
  classical
  haveI : IsSimpleRing B := isSimpleRing_of_isAzumaya k B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
  haveI : Finite D := Module.finite_of_finite k
  have hcomm : ∀ a b : D, a * b = b * a := (littleWedderburn D).mul_comm
  have hD : ∀ d : D, ∃ c : k, algebraMap k D c = d := by
    intro d
    have hcen : e.symm (Matrix.scalar (Fin n) d) ∈ Subalgebra.center k B := by
      rw [Subalgebra.mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
      ext i j
      simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hcomm]
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (Algebra.IsCentral.out hcen)
    refine ⟨c, ?_⟩
    have h2 := congrArg e hc
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes] at h2
    have h3 := congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero hn.out⟩) ⟨0, Nat.pos_of_ne_zero hn.out⟩
    simpa [Matrix.algebraMap_eq_diagonal] using h3
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn.out⟩
  let E : Matrix (Fin n) (Fin n) D := Matrix.single i₀ i₀ 1
  refine ⟨e.symm E, ?_, ?_, n, fun i => e.symm (Matrix.single i i₀ 1),
    fun i => e.symm (Matrix.single i₀ i 1), ?_⟩
  · rw [← map_mul]
    simp [E, Matrix.single_mul_single_same]
  · intro y
    obtain ⟨c, hc⟩ := hD (e y i₀ i₀)
    refine ⟨c, ?_⟩
    apply e.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, map_smul, AlgEquiv.apply_symm_apply]
    simp only [E, Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, ← hc]
    rw [Algebra.algebraMap_eq_smul_one]
  · apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      simp [E, map_sum, Matrix.single_mul_single_same, Matrix.sum_single_one]

end GlobalTheory.AzumayaResidue

namespace GlobalTheory.AzumayaResidue

theorem mem_smul_top_of_one_tmul_eq_zero (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type)
    [Ring Λ] [Algebra A Λ] (y : Λ) (h : (1 : ResidueField A) ⊗ₜ[A] y = 0) :
    y ∈ (maximalIdeal A) • (⊤ : Submodule A Λ) := by
  have := TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := Λ) (maximalIdeal A) y
  rw [← Submodule.Quotient.mk_eq_zero, ← this]
  exact (congrArg (TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal A)) h).trans (map_zero _)

theorem one_tmul_surjective (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type)
    [Ring Λ] [Algebra A Λ] (z : ResidueField A ⊗[A] Λ) : ∃ y : Λ, (1 : ResidueField A) ⊗ₜ[A] y = z := by
  first
  | exact @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq
  | exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq
  | (apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneTensorExistence.exists_one_tmul_eq ..)

theorem exists_residue_idempotent : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] [Nontrivial Λ], ∃ x : Λ, x * x - x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) ∧ (∀ y : Λ, ∃ c : A, x * y * x - c • x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) ∧ ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * x * b i - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) := by
  intro A _ _ _ Λ _ _ _ _ _
  classical
  let k := ResidueField A
  haveI : IsAzumaya k (k ⊗[A] Λ) := GlobalTheory.isAzumaya_baseChange A k Λ
  haveI : Nontrivial (k ⊗[A] Λ) := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    have : (0 : k) = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (α := k ⊗[A] Λ) fun _ => Subsingleton.elim _ _
    exact zero_ne_one this
  let π : Λ →ₐ[A] k ⊗[A] Λ := Algebra.TensorProduct.includeRight
  have hπ : ∀ y, π y = (1 : k) ⊗ₜ[A] y := fun y => rfl
  have hker : ∀ y, π y = 0 → y ∈ (maximalIdeal A) • (⊤ : Submodule A Λ) := fun y h =>
    mem_smul_top_of_one_tmul_eq_zero A Λ y ((hπ y).symm.trans h)
  have hsurj : ∀ z, ∃ y, π y = z := one_tmul_surjective A Λ
  obtain ⟨xb, hxx, hxy, N, ab, bb, hsum⟩ := exists_rankOne_idempotent k (k ⊗[A] Λ)
  obtain ⟨x, rfl⟩ := hsurj xb
  choose a ha using fun i => hsurj (ab i)
  choose b hb using fun i => hsurj (bb i)
  refine ⟨x, hker _ ?_, fun y => ?_, N, a, b, hker _ ?_⟩
  · rw [map_sub, map_mul, hxx, sub_self]
  · obtain ⟨cb, hc⟩ := hxy (π y)
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective cb
    refine ⟨c, hker _ ?_⟩
    rw [map_sub, map_mul, map_mul, hc, map_smul, ← ResidueField.algebraMap_eq,
      algebraMap_smul, sub_self]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sub, map_sum, map_mul, map_one, ha, hb, hsum, sub_self]

end GlobalTheory.AzumayaResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootOfUnitZeroDimensional
section
namespace GlobalTheory

theorem pow_idempotent_combination {R : Type} [CommRing R] {g : R} (hg : IsIdempotentElem g)
    (a b : R) (n : ℕ) : (g * a + (1 - g) * b) ^ n = g * a ^ n + (1 - g) * b ^ n := by
  induction n with
  | zero => ring
  | succ n ih =>
    rw [pow_succ, ih]
    linear_combination (a ^ n * a + b ^ n * b - a ^ n * b - b ^ n * a) * hg.eq

theorem exists_unit_pow_eq_of_krullDimLE_zero : ∀ (R : Type) [CommRing R] [Ring.KrullDimLE 0 R]
    (q : ℕ), 0 < q → IsUnit (q : R) → ∀ u : Rˣ,
    (∀ m : Ideal R, m.IsMaximal → ∃ x : R, x ^ q - (u : R) ∈ m) → ∃ v : Rˣ, v ^ q = u := by
  intro R _ _ q hq hqu u hloc
  have hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal := fun P hP => hP.isMaximal'
  let S : Set R := {g | IsIdempotentElem g ∧ ∃ x : R, IsNilpotent (g * (x ^ q - u))}
  have hjoin : ∀ g ∈ S, ∀ h ∈ S, g + h - g * h ∈ S := by
    rintro g ⟨hg, x, hx⟩ h ⟨hh, z, hz⟩
    refine ⟨?_, g * x + (1 - g) * z, ?_⟩
    · show (g + h - g * h) * (g + h - g * h) = g + h - g * h
      linear_combination (1 - 2 * h + h ^ 2) * hg.eq + (1 - g) * hh.eq
    · have key : (g + h - g * h) * ((g * x + (1 - g) * z) ^ q - u)
          = g * (x ^ q - u) + (1 - g) * (h * (z ^ q - u)) := by
        rw [pow_idempotent_combination hg]
        linear_combination (x ^ q - z ^ q - h * x ^ q + h * z ^ q) * hg.eq
      rw [key]
      exact Commute.isNilpotent_add (Commute.all _ _) hx ((Commute.all _ _).isNilpotent_mul_left (show IsNilpotent (h * (z ^ q - u)) from hz))
  have hcover : ∀ m : Ideal R, m.IsMaximal → ∃ g ∈ S, g ∉ m := by
    intro m hm
    obtain ⟨x, hx⟩ := hloc m hm
    obtain ⟨e, b, he, hab, hep⟩ := exists_isIdempotentElem_mul_of_forall_isMaximal hR (x ^ q - u)
    refine ⟨1 - e, ⟨he.one_sub, x, ?_⟩, ?_⟩
    · rw [nilpotent_iff_mem_prime]
      intro p hp
      by_cases ha : x ^ q - (u : R) ∈ p
      · exact p.mul_mem_left _ ha
      · have hep' := hep p hp ha
        have h0 : e * (1 - e) ∈ p := by
          have : e * (1 - e) = 0 := by linear_combination -he.eq
          rw [this]; exact p.zero_mem
        rcases hp.mem_or_mem h0 with h | h
        · exact absurd h hep'
        · exact p.mul_mem_right _ h
    · intro h
      have hem : e ∈ m := hab ▸ m.mul_mem_right b hx
      apply hm.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using m.add_mem h hem
  have hspan : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgS, hgm⟩ := hcover m hm
    exact hgm (hle (Ideal.subset_span hgS))
  have hfin : ∀ T : Finset R, (↑T ⊆ S) → ∃ G ∈ S, ∀ g ∈ T, g * G = g := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, ⟨IsIdempotentElem.zero, 0, by simp⟩, by simp⟩
    | insert a T ha ih =>
      intro hT
      have haS : a ∈ S := hT (by simp)
      obtain ⟨G, hG, hGT⟩ := ih (fun y hy => hT (by simp [hy]))
      refine ⟨a + G - a * G, hjoin a haS G hG, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · linear_combination (1 - G) * haS.1.eq
      · have := hGT g hg
        linear_combination (1 - a) * this
  have h1 : (1 : R) ∈ Ideal.span S := by rw [hspan]; trivial
  obtain ⟨n, f, g, hf⟩ := Submodule.mem_span_set'.mp h1
  classical
  obtain ⟨G, hG, hGT⟩ := hfin (Finset.univ.image fun i => (g i : R)) (by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact (g i).2)
  have hG1 : G = 1 := by
    have : (∑ i, f i • (g i : R)) * G = ∑ i, f i • (g i : R) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, hGT _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    rw [hf, one_mul] at this
    exact this
  obtain ⟨x, hx⟩ := hG.2
  rw [hG1, one_mul] at hx
  have hxq : IsUnit (x ^ q) := by
    have := hx.isUnit_add_left_of_commute u.isUnit (Commute.all _ _)
    simpa using this
  have hxu : IsUnit x := (isUnit_pow_iff hq.ne').mp hxq
  let P : Polynomial R := Polynomial.X ^ q - Polynomial.C (u : R)
  have hP : ∀ y : R, Polynomial.aeval y P = y ^ q - u := by
    intro y; simp [P]
  have hdP : Polynomial.aeval x (Polynomial.derivative P) = (q : R) * x ^ (q - 1) := by
    simp [P, Polynomial.derivative_X_pow]
  obtain ⟨v, ⟨-, hv⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := P) (x := x)
    (by rw [hP]; exact hx) (by rw [hdP]; exact hqu.mul (hxu.pow _))
  rw [hP, sub_eq_zero] at hv
  have hvu : IsUnit v := (isUnit_pow_iff hq.ne').mp (hv ▸ u.isUnit)
  exact ⟨hvu.unit, Units.ext (by simp [hv])⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzPartitionOfUnityLattice
section
open scoped ContDiff Topology

namespace GlobalTheory.LatticeSumOne

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_radius (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ R : ℝ, ∀ x : V, ∃ l : Λ, ‖x + l‖ ≤ R := by
  obtain ⟨t, ht⟩ := GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun k : V => {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1})
    (fun k => by
      have : {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1} =
          ⋃ l : Λ, (fun z : V => z + l) ⁻¹' Metric.ball k 1 := by
        ext z; simp
      rw [this]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (by fun_prop))
    (fun k l z hz => by
      obtain ⟨m, hm⟩ := hz
      refine ⟨m - l, ?_⟩
      simpa [add_sub_cancel, add_assoc, sub_eq_add_neg] using hm)
    (fun z => ⟨z, 0, by simp⟩)
  refine ⟨1 + ∑ k ∈ t, ‖k‖, fun x => ?_⟩
  obtain ⟨k, hk, l, hl⟩ := ht x
  refine ⟨l, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hl
  have h1 : ‖k‖ ≤ ∑ k ∈ t, ‖k‖ := Finset.single_le_sum (f := fun k => ‖k‖) (fun _ _ => norm_nonneg _) hk
  calc ‖x + l‖ = ‖(x + l - k) + k‖ := by abel_nf
    _ ≤ ‖x + l - k‖ + ‖k‖ := norm_add_le _ _
    _ ≤ 1 + ∑ k ∈ t, ‖k‖ := by linarith

theorem exists_schwartz_lattice_sum_one (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  obtain ⟨R, hR⟩ := exists_radius Λ
  set R' : ℝ := max R 1 with hR'
  let φ : ContDiffBump (0 : V) := ⟨R', R' + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  have hφc : HasCompactSupport (φ : V → ℝ) := φ.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (φ : V → ℝ) := φ.contDiff
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => φ.nonneg
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ (φ : V → ℝ) hφc
  set S : V → ℝ := fun z => ∑ᶠ l : Λ, φ (z + l) with hSdef
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : Λ) (z : V) => φ (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSper : ∀ (l : Λ) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hR z
    have h1 := single_le_finsum (f := fun m : Λ => φ (z + m)) l (hlf.point_finite z)
      (fun m => hφ0 _)
    have h2 : φ (z + l) = 1 := φ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hl.trans (le_max_left _ _))
    have : 1 ≤ S z := by rw [← h2]; exact h1
    linarith
  set g : V → ℂ := fun z => ((φ z * (S z)⁻¹ : ℝ) : ℂ) with hgdef
  have hgc : HasCompactSupport g := by
    have : HasCompactSupport (fun z => φ z * (S z)⁻¹) := hφc.mul_right
    exact this.comp_left (g := Complex.ofReal) (by simp)
  have hgs : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp (hφs.mul (hSs.inv fun z => (hSpos z).ne'))
  refine ⟨hgc.toSchwartzMap hgs, hgc, fun x => ?_⟩
  have hfin := hlf.point_finite x
  have hval : ∀ l : Λ, (hgc.toSchwartzMap hgs) (x + l) = ((φ (x + l) : ℝ) : ℂ) * ((S x)⁻¹ : ℝ) := by
    intro l
    show g (x + l) = _
    simp only [hgdef, hSper, Complex.ofReal_mul]
  simp_rw [hval]
  have hsum : HasSum (fun l : Λ => ((φ (x + l) : ℝ) : ℂ) * (((S x)⁻¹ : ℝ) : ℂ))
      (∑ l ∈ hfin.toFinset, ((φ (x + l) : ℝ) : ℂ) * (((S x)⁻¹ : ℝ) : ℂ)) :=
    hasSum_sum_of_ne_finset_zero fun l hl => by
      have : φ (x + l) = 0 := by
        by_contra hne
        exact hl (hfin.mem_toFinset.2 hne)
      simp [this]
  convert hsum using 1
  have hS : S x = ∑ l ∈ hfin.toFinset, φ (x + l) :=
    finsum_eq_sum_of_support_subset (fun l : Λ => φ (x + l)) (fun l hl => hfin.mem_toFinset.2 hl)
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← hS, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (hSpos x).ne', Complex.ofReal_one]

end GlobalTheory.LatticeSumOne

namespace GlobalTheory

theorem exists_schwartz_hasCompactSupport_latticeTranslates_sum_one :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  intro V _ _ _ Λ _ _
  exact LatticeSumOne.exists_schwartz_lattice_sum_one Λ

end GlobalTheory
end

