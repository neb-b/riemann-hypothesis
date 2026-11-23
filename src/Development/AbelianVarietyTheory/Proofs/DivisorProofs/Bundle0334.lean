module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarDvrOfIsSeparable
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

theorem isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsMaximal]
    [q.LiesOver p] [Algebra.EssFiniteType R S] (h : q.ramificationIdx R = 1)
    (hs : Algebra.IsSeparable (R ⧸ p) (S ⧸ q)) :
    Algebra.IsUnramifiedAt R q := by
  rw [Ideal.ramificationIdx_eq p q, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : Algebra.IsSeparable p.ResidueField q.ResidueField := inferInstance
  exact ⟨this, h⟩

theorem abhyankar_dvr_of_isSeparable : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale D (integralClosure D (TensorProduct S D L)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he hram hsep
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI hAd := GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain S π e hπ he0
  haveI hAv := GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible S π e hπ he0
  haveI : IsDomain D := φ.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing D :=
    IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
  haveI : IsLocalRing D := IsLocalRing.of_surjective' φ.symm.toRingHom φ.symm.surjective
  haveI : IsDiscreteValuationRing D :=
    { not_a_field' := by
        intro h
        apply IsDiscreteValuationRing.not_isField (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))
        refine MulEquiv.isField ?_ φ.symm.toMulEquiv
        exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 h }
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : FaithfulSMul S D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 : algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) a =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) b := by
      rw [← φ.commutes, ← φ.commutes, hab]
    set pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne') with hpb
    have hd : 0 < pb.dim := by
      rw [hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C _]; exact he0
    have h0 : pb.basis ⟨0, hd⟩ = 1 := by rw [PowerBasis.coe_basis]; simp
    have key : ∀ s : S, pb.basis.repr (algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) s)
        ⟨0, hd⟩ = s := by
      intro s
      rw [Algebra.algebraMap_eq_smul_one, ← h0, map_smul, Module.Basis.repr_self]
      simp
    rw [← key a, ← key b, h1]
  haveI : Module.Finite D (integralClosure D (TensorProduct S D L)) := _root_.GlobalTheory.NormFin.main S K L D
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  haveI : Module.Flat D (integralClosure D (TensorProduct S D L)) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have hinj : Function.Injective (LinearMap.rTensor L (LinearMap.mulLeft S (a : D))) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun y z h => (mul_right_injective₀ (nonZeroDivisors.ne_zero a.2)) h)
    have hsmul : ∀ z : TensorProduct S D L,
        (a : D) • z = LinearMap.rTensor L (LinearMap.mulLeft S (a : D)) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul y l => simp [TensorProduct.smul_tmul']
      | add u v hu hv => rw [smul_add, map_add (f := _), hu, hv]
    have h1 : (a : D) • (x : TensorProduct S D L) = 0 := congrArg Subtype.val hax
    rw [hsmul, ← map_zero (LinearMap.rTensor L (LinearMap.mulLeft S (a : D)))] at h1
    simp only [Submodule.mem_bot]
    exact Subtype.ext (hinj h1)
  haveI : Algebra.FinitePresentation D (integralClosure D (TensorProduct S D L)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hmax : ∀ (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
      Algebra.IsUnramifiedAt D Q := by
    intro Q hQ
    have hQu : Q.under D = maximalIdeal D :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap D
          (integralClosure D (TensorProduct S D L)))
          (algebraMap_isIntegral_iff.mpr inferInstance) Q)
    haveI : Q.LiesOver (maximalIdeal D) := ⟨hQu.symm⟩
    exact isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable (maximalIdeal D) Q
      (GlobalTheory.T.abhyankar_ramificationIdx_eq_one_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q) (GlobalTheory.T.abhyankar_residueField_isSeparable_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q)
  haveI : Algebra.FormallyUnramified D (integralClosure D (TensorProduct S D L)) := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    obtain ⟨Q, hQ, hqQ⟩ := Ideal.exists_le_maximal q.1 q.2.ne_top
    haveI := hQ
    have hU := hmax Q
    have hopen := Algebra.isOpen_unramifiedLocus (R := D)
      (A := integralClosure D (TensorProduct S D L))
    exact hopen.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes q ⟨Q, hQ.isPrime⟩).mp hqQ) hU
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasis
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def intSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp [AddValuation.map_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by simp [AddValuation.map_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, AddValuation.map_neg] at *
    exact ha

theorem isIntV_iff (v : AddValuation C (WithTop ℝ)) (x : C) : IsIntV v x ↔ x ∈ intSubring v :=
  Iff.rfl

theorem int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  show 0 ≤ v a
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := fun h' => hb ((AddValuation.top_iff v).1 h')
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hb'
  rcases eq_or_ne (v a) ⊤ with ha | ha
  · rw [ha]; exact le_top
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ha
  rw [← hr, ← hs, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [← hs]
  exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def Reduces (v : AddValuation C (WithTop ℝ)) {i n : ℕ} (M : Matrix (Fin i) (Fin n) C) : Prop :=
  ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ n ∧ (∀ a b, IsIntV v (g a b)) ∧
    v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e, (g * M) a e = 0

theorem pivot_step (v : AddValuation C (WithTop ℝ)) {i' n : ℕ}
    (ih : ∀ M' : Matrix (Fin i') (Fin n) C, Reduces v M')
    (M : Matrix (Fin (i' + 1)) (Fin (n + 1)) C) (h0 : M 0 0 ≠ 0)
    (hmin : ∀ b, v (M 0 0) ≤ v (M b 0)) : Reduces v M := by
  have hq : ∀ c : Fin i', IsIntV v (M c.succ 0 / M 0 0) := fun c =>
    int_of_le v h0 (by rw [div_mul_cancel₀ _ h0]; exact hmin c.succ)
  obtain ⟨g', cr', hc1, hc2, hint, hdet, hz⟩ :=
    ih (Matrix.of fun c e' => M c.succ e'.succ - M c.succ 0 / M 0 0 * M 0 e'.succ)
  have hw : ∀ a'', IsIntV v (-∑ c, g' a'' c * (M c.succ 0 / M 0 0)) := fun a'' =>
    (isIntV_iff v _).2 (neg_mem (Subring.sum_mem _ fun c _ =>
      mul_mem ((isIntV_iff v _).1 (hint a'' c)) ((isIntV_iff v _).1 (hq c))))
  refine ⟨Matrix.of fun a b => Fin.cases (motive := fun _ => C)
      (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
      (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
        (fun b'' => g' a'' b'') b) a,
    cr' + 1, by omega, by omega, ?_, ?_, ?_⟩
  · intro a b
    cases a using Fin.cases <;> cases b using Fin.cases <;>
      simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · simp [IsIntV]
    · simp [IsIntV]
    · exact hw _
    · exact hint _ _
  · have hsub : (Matrix.of fun a b => Fin.cases (motive := fun _ => C)
        (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
        (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
          (fun b'' => g' a'' b'') b) a).submatrix Fin.succ Fin.succ = g' := by
      ext a b
      simp
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, Fin.succAbove_zero, hsub,
      mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
    exact hdet
  · intro a ha e
    obtain ⟨a'', rfl⟩ := Fin.exists_succ_eq.2 (show a ≠ 0 by rintro rfl; simp at ha)
    have ha' : cr' ≤ a''.val := by rw [Fin.val_succ] at ha; omega
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    cases e using Fin.cases with
    | zero =>
      rw [neg_mul, Finset.sum_mul, neg_add_eq_zero]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_assoc, div_mul_cancel₀ _ h0]
    | succ e' =>
      have h1 := hz a'' ha' e'
      simp only [Matrix.mul_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib] at h1
      have e1 : ∑ c, g' a'' c * (M c.succ 0 / M 0 0 * M 0 e'.succ) =
          (∑ c, g' a'' c * (M c.succ 0 / M 0 0)) * M 0 e'.succ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [e1] at h1
      linear_combination h1

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

theorem one_int (v : AddValuation C (WithTop ℝ)) {i : ℕ} (a b : Fin i) :
    IsIntV v ((1 : Matrix (Fin i) (Fin i) C) a b) := by
  show 0 ≤ v _
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem reduces_all (v : AddValuation C (WithTop ℝ)) :
    ∀ (n i : ℕ) (M : Matrix (Fin i) (Fin n) C), Reduces v M := by
  intro n
  induction n with
  | zero =>
    intro i M
    exact ⟨1, 0, Nat.zero_le _, le_rfl, one_int v, by simp, fun a _ e => e.elim0⟩
  | succ n ih =>
    intro i M
    cases i with
    | zero => exact ⟨1, 0, le_rfl, Nat.zero_le _, one_int v, by simp, fun a _ => a.elim0⟩
    | succ i' =>
      obtain ⟨b0, -, hb0⟩ :=
        Finset.univ.exists_min_image (fun b => v (M b 0)) Finset.univ_nonempty
      by_cases h0 : M b0 0 = 0
      · have hcol : ∀ b, M b 0 = 0 := fun b => by
          have hb := hb0 b (Finset.mem_univ _)
          rw [h0, AddValuation.map_zero, top_le_iff] at hb
          exact (AddValuation.top_iff v).1 hb
        obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := ih (i' + 1) (Matrix.of fun a e => M a e.succ)
        refine ⟨g, cr, h1, by omega, hint, hdet, fun a ha e => ?_⟩
        cases e using Fin.cases with
        | zero => simp [Matrix.mul_apply, hcol]
        | succ e' => simpa [Matrix.mul_apply] using hz a ha e'
      · obtain ⟨g1, cr, h1, h2, hint, hdet, hz⟩ := pivot_step v (ih i')
          (M.submatrix (Equiv.swap 0 b0) id) (by simpa using h0)
          (fun b => by simpa using hb0 _ (Finset.mem_univ _))
        refine ⟨g1.submatrix id (Equiv.swap 0 b0), cr, h1, h2, fun a b => hint _ _, ?_,
          fun a ha e => ?_⟩
        · rw [Matrix.det_permute', AddValuation.map_mul, hdet, add_zero]
          rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (i' + 1)) b0)) with
            h | h <;> simp [h]
        · have key : ∑ b, g1 a (Equiv.swap 0 b0 b) * M b e =
              ∑ b, g1 a b * M (Equiv.swap 0 b0 b) e := by
            rw [← Equiv.sum_comp (Equiv.swap 0 b0) (fun b => g1 a b * M (Equiv.swap 0 b0 b) e)]
            simp [Equiv.swap_apply_self]
          simpa [Matrix.mul_apply, key] using hz a ha e

end

end GlobalTheory.LowU

theorem GlobalTheory.LowU.adapted_basis : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (i d : ℕ) (u : Fin i → Fin d → C) (S : Finset (Fin d)), IsSatFrame v u →
    ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ S.card ∧ (∀ a b, IsIntV v (g a b)) ∧
      v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e ∈ S, ∑ a', g a a' * u a' e = 0 := by
  intro C _ _ v i d u S _
  obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := GlobalTheory.LowU.reduces_all v S.card i
    (Matrix.of fun a k => u a (S.equivFin.symm k))
  refine ⟨g, cr, h1, h2, hint, hdet, fun a ha e he => ?_⟩
  simpa [Matrix.mul_apply] using hz a ha (S.equivFin ⟨e, he⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeSymmetricPowerFamily
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem symMat_upperTriangular {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    (symMat m A).BlockTriangular id := by
  intro a i hia
  simp only [symMat, Matrix.of_apply]
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hia)
  rw [← C_pow]
  refine (natDegree_mul_C_le _ _).trans ?_
  have h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1 := by compute_degree
  simpa using natDegree_pow_le_of_le (i : ℕ) h1

theorem symMat_diag {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (i : Fin (m + 1)) :
    symMat m A i i = A 1 1 ^ (i : ℕ) * A 0 0 ^ (m - i) := by
  simp only [symMat, Matrix.of_apply]
  rw [← C_pow, coeff_mul_C]
  congr 1
  have h1 : (C (A 0 1) + C (A 1 1) * X).natDegree ≤ 1 := by compute_degree
  have := coeff_pow_of_natDegree_le (m := (i : ℕ)) h1
  rw [mul_one] at this
  rw [this]
  simp

theorem det_symMat_of_upper {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) (h : A 1 0 = 0) :
    (symMat m A).det = A.det ^ (m * (m + 1) / 2) := by
  rw [Matrix.det_of_upperTriangular (symMat_upperTriangular m A)]
  simp only [symMat_diag]
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero]
  rw [Fin.prod_univ_eq_prod_range (fun i => A 1 1 ^ i * A 0 0 ^ (m - i)) (m + 1), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, mul_pow, mul_comm]
  have hs : ∑ i ∈ Finset.range (m + 1), i = m * (m + 1) / 2 := by
    rw [Finset.sum_range_id]; simp [mul_comm]
  have hr : ∑ i ∈ Finset.range (m + 1), (m - i) = m * (m + 1) / 2 := by
    rw [← hs]
    exact Finset.sum_range_reflect (fun i => i) (m + 1)
  rw [hs, hr]

theorem ord_pow' {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (N : ℕ) :
    ord v (x ^ N) = (N : ℤ) * ord v x := by
  simp only [ord, map_pow, WithZero.log_pow, nsmul_eq_mul, mul_neg]

theorem unimod_symMat {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) F) (hA : A 1 0 = 0) (hu : Unimod v A) : Unimod v (symMat m A) := by
  refine ⟨fun a i => ?_, ?_⟩
  · let A' : Matrix (Fin 2) (Fin 2) v.O := fun i j => ⟨A i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu.1 i j)⟩
    have e : A'.map v.O.subtype = A := by ext i j; rfl
    rw [← e, ← symMat_map]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (symMat m A' a i).2
  · rw [det_symMat_of_upper m A hA, map_pow, hu.2, one_pow]

theorem admissible_degree_symmetricPowerFamily : ∀ (k F : Type) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (m : ℕ)
    (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) →
      admitted (fun v => symMat m (g v)) ∧ deg (fun v => symMat m (g v)) = ((m * (m + 1) / 2 : ℕ) : ℤ) * deg g := by
  intro k F _ _ _ _ m g hg h0
  refine ⟨⟨fun v => ?_, hg.2.subset fun v hv hu => hv (unimod_symMat v m (g v) (h0 v) hu)⟩, ?_⟩
  · rw [det_symMat_of_upper m (g v) (h0 v)]
    exact pow_ne_zero _ (hg.1 v)
  · simp only [deg, det_symMat_of_upper m _ (h0 _), ord_pow']
    rw [mul_finsum]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeTwistFamilyAtPlaceByScalar
section
open scoped IntermediateField Polynomial RatFunc

open GlobalTheory.Nef Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem ord_mul_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ord v (x * y) = ord v x + ord v y := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_zpow_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x : F} (hx : x ≠ 0)
    (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [ord, map_zpow₀]
  rw [← WithZero.exp_log h0, ← WithZero.exp_zsmul, WithZero.log_exp, WithZero.log_exp, smul_eq_mul]
  ring

theorem admissible_degree_twistFamilyAtPlaceByScalar (k F : Type) [Field k] [Field F] [Algebra k F] [IsAlgClosed k] (n : ℕ)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (hh : admitted h) (v₀ : Place k F) (π : F) (hπ : π ≠ 0)
    (h1 : ord v₀ π = 1) (e : ℤ) :
    admitted (twistAt v₀ (π ^ (-e)) h) ∧ deg (twistAt v₀ (π ^ (-e)) h) = deg h - n * e := by
  classical
  have hc : π ^ (-e) ≠ 0 := zpow_ne_zero _ hπ
  have hdet : ∀ v, (twistAt v₀ (π ^ (-e)) h v).det =
      (if v = v₀ then (π ^ (-e)) ^ n else 1) * (h v).det := by
    intro v
    by_cases hv : v = v₀
    · subst hv
      rw [twistAt_self, Matrix.det_smul, Fintype.card_fin, if_pos rfl]
    · rw [twistAt_of_ne _ _ _ _ hv, if_neg hv, one_mul]
  have hord : ∀ v, ord v (twistAt v₀ (π ^ (-e)) h v).det =
      ord v (h v).det - if v = v₀ then (n : ℤ) * e else 0 := by
    intro v
    rw [hdet, ord_mul_of_ne _ (by split_ifs; exacts [pow_ne_zero _ hc, one_ne_zero]) (hh.1 v)]
    split_ifs with hv
    · subst hv
      rw [← zpow_natCast, ← zpow_mul, ord_zpow_of_ne _ hπ, h1]
      ring
    · simp [ord]
  refine ⟨⟨fun v => ?_, (hh.2.union (Set.finite_singleton v₀)).subset fun v hv => ?_⟩, ?_⟩
  · rw [hdet]
    exact mul_ne_zero (by split_ifs; exacts [pow_ne_zero _ hc, one_ne_zero]) (hh.1 v)
  · by_cases hv' : v = v₀
    · exact Or.inr hv'
    · exact Or.inl (show ¬ Unimod v (h v) from fun hu => hv (by rw [twistAt_of_ne _ _ _ _ hv']; exact hu))
  · have hfin : (Function.support fun v => ord v (h v).det).Finite := by
      refine hh.2.subset fun v hv => ?_
      intro hu
      exact hv (by simp [ord, hu.2])
    have hfin' : (Function.support fun v : Place k F => if v = v₀ then (n : ℤ) * e else 0).Finite :=
      (Set.finite_singleton v₀).subset fun v hv => by
        by_contra h'
        exact hv (if_neg h')
    rw [deg, deg, finsum_congr hord, finsum_sub_distrib hfin hfin', finsum_eq_single _ v₀ fun v hv => if_neg hv, if_pos rfl]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupLeibnizEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem aw_leibniz_rule : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)), μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ → δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂ := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hc h₁ h₂
  exact CupSpec.aw_leibniz μ rfl rfl rfl hc h₁ h₂

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIffStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.face_map_complex_quasi_iso_iff_epi_exact : ∀ (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C) (f : K ⟶ (SimplicialObject.const C).obj B), QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧ (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0, (ShortComplex.mk _ _ w).Exact) ∧ ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  first | (exact @GlobalTheory.EtC.AugExact.augmented_exact_iff) | (exact GlobalTheory.EtC.AugExact.augmented_exact_iff) | (intros; apply GlobalTheory.EtC.AugExact.augmented_exact_iff  <;> assumption)
end

