module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIntegralOfSplitPlaceComponent
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

section Idem

variable {R : Type} [CommRing R] {n : ℕ}

theorem matrix_mul_orthogonal_three_idempotents_smul (a b c : R) (hab : a * b = 0) (hac : a * c = 0) (hbc : b * c = 0) (ha : a * a = a)
    (hb : b * b = b) (hc : c * c = c) (M₁ M₂ M₃ N₁ N₂ N₃ : Matrix (Fin n) (Fin n) R) :
    (a • M₁ + b • M₂ + c • M₃) * (a • N₁ + b • N₂ + c • N₃) = a • (M₁ * N₁) + b • (M₂ * N₂) + c • (M₃ * N₃) := by
  have hba : b * a = 0 := by rw [mul_comm]; exact hab
  have hca : c * a = 0 := by rw [mul_comm]; exact hac
  have hcb : c * b = 0 := by rw [mul_comm]; exact hbc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hab, hac, hbc, hba, hca, hcb,
    ha, hb, hc, zero_smul, add_zero, zero_add]

theorem cT_smul' (τ : R →+* R) (a : R) (M : Matrix (Fin n) (Fin n) R) : cT τ (a • M) = τ a • cT τ M := by
  ext i j; simp [cT]

theorem cT_add' (τ : R →+* R) (M N : Matrix (Fin n) (Fin n) R) : cT τ (M + N) = cT τ M + cT τ N := by
  ext i j; simp [cT]

theorem cT_cT' (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (M : Matrix (Fin n) (Fin n) R) : cT τ (cT τ M) = M := by
  ext i j; simp [cT, hτ]

theorem map_idem3 (a b c : R) (X Y : Matrix (Fin n) (Fin n) R) {T : Type} [CommRing T] (f : R →+* T) :
    (a • X + b • Y + c • (1 : Matrix (Fin n) (Fin n) R)).map f
      = f a • X.map f + f b • Y.map f + f c • (1 : Matrix (Fin n) (Fin n) T) := by
  ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

theorem idem_split_inv (τ : R →+* R) (a b : R) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hGi : Gi * G = 1) (hX : X * Xi = 1) :
    (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) *
      (a • Xi + b • (Gi * cT τ X * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have h1 : Gi * cT τ Xi * G * (Gi * cT τ X * G) = 1 := by
    calc _ = Gi * (cT τ Xi * (G * Gi) * cT τ X) * G := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, Matrix.mul_one, ← cT_mul, hX, cT_one, Matrix.mul_one, hGi]
  rw [hX, h1, Matrix.mul_one, ← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]

theorem idem_split_unitary (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (a b : R) (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) (hτa : τ a = b)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hXi : Xi * X = 1) (hGh : cT τ G = G) :
    cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G *
      (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = G := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  have hτb : τ b = a := by rw [← hτa, hτ]
  have hτc : τ (1 - a - b) = 1 - a - b := by rw [map_sub, map_sub, map_one, hτa, hτb]; ring
  have hGc : cT τ Gi * G = 1 := by
    have : cT τ Gi * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    rwa [hGh] at this
  have hct : cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R))
      = a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [cT_add', cT_add', cT_smul', cT_smul', cT_smul', hτa, hτb, hτc, cT_one, cT_mul, cT_mul, hGh, cT_cT' τ hτ]
    abel
  have hGs : G = a • G + b • G + (1 - a - b) • G := by
    rw [← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]
  rw [hct, show (a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G
      = a • (G * (Xi * cT τ Gi) * G) + b • (cT τ X * G) + (1 - a - b) • (1 * G) by
    simp only [Matrix.add_mul, Matrix.smul_mul]]
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have e1 : G * (Xi * cT τ Gi) * G * X = G := by
    calc _ = G * (Xi * (cT τ Gi * G) * X) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hGc, Matrix.mul_one, hXi, Matrix.mul_one]
  have e2 : cT τ X * G * (Gi * cT τ Xi * G) = G := by
    calc _ = cT τ X * (G * Gi) * cT τ Xi * G := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hG, Matrix.mul_one, ← cT_mul, hXi, cT_one, Matrix.one_mul]
  rw [e1, e2, Matrix.one_mul, Matrix.mul_one, ← hGs]

end Idem

end GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

theorem exists_unitary_int_of_component {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type}
    [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a)
    (hS : ∀ a ∈ S, σ a ∈ S) (n : ℕ) (G : GL (Fin n) S)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
      = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (Q Q' : P) (hQ : σ (Z.e Q) = Z.e Q') (hne : Q ≠ Q') (y : GL (Fin n) (Z.O Q)) :
    ∃ u : GL (Fin n) S, bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      bc (Z.pO Q) u = y ∧ ∀ Q'', Q'' ≠ Q → Q'' ≠ Q' → bc (Z.pO Q'') u = 1 := by
  obtain ⟨x, hx1, hx2⟩ := Z.gl_single Q (bc (Z.O Q).subtype y)
  obtain ⟨X, hX⟩ := Z.gl_int (x := x) fun R => by
    by_cases h : R = Q
    · subst h; exact ⟨y, hx1.symm⟩
    · exact ⟨1, by rw [map_one, hx2 R h]⟩
  have hcomp : ∀ R, bc (Z.O R).subtype (bc (Z.pO R) X) = bc (Z.p R) x := fun R => by
    rw [← hX]; rfl
  have binj : ∀ R, Function.Injective (bc (n := Fin n) (Z.O R).subtype) := fun R g h e =>
    Units.ext (Matrix.map_injective Subtype.val_injective (congrArg Units.val e))
  have hXQ : bc (Z.pO Q) X = y := binj Q (by rw [hcomp, hx1])
  have hXR : ∀ R, R ≠ Q → bc (Z.pO R) X = 1 := fun R h => binj R (by rw [hcomp, hx2 R h, map_one])
  let τ : S →+* S := σ.restrict S S hS
  have hτv : ∀ s : S, (τ s : A) = σ s := fun s => rfl
  have hτ : ∀ s, τ (τ s) = s := fun s => Subtype.ext (by rw [hτv, hτv, hσ])
  let a : S := ⟨Z.e Q, Z.e_mem Q⟩
  let b : S := ⟨Z.e Q', Z.e_mem Q'⟩
  have ha : a * a = a := Subtype.ext (Z.e_idem Q)
  have hb : b * b = b := Subtype.ext (Z.e_idem Q')
  have hab : a * b = 0 := Subtype.ext (by
    show Z.e Q * Z.e Q' = 0
    refine Z.ext _ fun R => ?_
    rw [map_mul]
    by_cases h : R = Q
    · subst h; rw [Z.e_ne Q' R hne, mul_zero]
    · rw [Z.e_ne Q R h, zero_mul])
  have hτa : τ a = b := Subtype.ext hQ
  have hmap : ∀ M : Matrix (Fin n) (Fin n) S, (cT τ M).map S.subtype = cT σ (M.map S.subtype) := fun M => by
    ext i j; rfl
  have hGh : cT τ (G : Matrix (Fin n) (Fin n) S) = G :=
    Matrix.map_injective (f := (S.subtype : S → A)) S.subtype_injective ((hmap _).trans hG)
  let uM : Matrix (Fin n) (Fin n) S := a • (X : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let vM : Matrix (Fin n) (Fin n) S := a • ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ (X : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let u : GL (Fin n) S := ⟨uM, vM,
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.mul_inv X),
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.inv_mul X)⟩
  have hcompU : ∀ R, ((bc (Z.pO R) u : GL (Fin n) (Z.O R)) : Matrix (Fin n) (Fin n) (Z.O R)) =
      Z.pO R a • (X : Matrix (Fin n) (Fin n) S).map (Z.pO R) + Z.pO R b • _ + Z.pO R (1 - a - b) • 1 :=
    fun R => map_idem3 _ _ _ _ _ _
  refine ⟨u, ?_, ?_, ?_⟩
  · show cT σ (uM.map S.subtype) * (G : Matrix (Fin n) (Fin n) S).map S.subtype * uM.map S.subtype
      = (G : Matrix (Fin n) (Fin n) S).map S.subtype
    rw [← hmap, ← Matrix.map_mul, ← Matrix.map_mul,
      idem_split_unitary τ hτ a b ha hb hab hτa _ _ _ _ (Units.mul_inv G) (Units.inv_mul X) hGh]
  · have hpa : Z.pO Q a = 1 := Subtype.ext (Z.e_self Q)
    have hpb : Z.pO Q b = 0 := Subtype.ext (Z.e_ne Q' Q hne)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp only [one_smul, zero_smul, add_zero, sub_self]
    exact congrArg Units.val hXQ
  · intro R h1 h2
    have hpa : Z.pO R a = 0 := Subtype.ext (Z.e_ne Q R h1)
    have hpb : Z.pO R b = 0 := Subtype.ext (Z.e_ne Q' R h2)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp

end GlobalTheory.LevNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfConjIntegralGenerators
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section
namespace GlobalTheory.ScalConj

theorem single_conj_apply {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (a b i j : Fin n) :
    (A * (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) * B) i j = A i a * B b j := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

def conjInt {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K) :
    Subalgebra O (Matrix (Fin n) (Fin n) O) where
  carrier := {X | ∃ Y : Matrix (Fin n) (Fin n) O,
    Y.map O.subtype = (m : Matrix (Fin n) (Fin n) K) * X.map O.subtype * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  mul_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y * Y', ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, hY, hY']
    have : ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (m : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul m
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), this, Matrix.one_mul]
  add_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y + Y', ?_⟩
    rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hY, hY', Matrix.mul_add, Matrix.add_mul]
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap O _ r, ?_⟩
    have h : (algebraMap O (Matrix (Fin n) (Fin n) O) r).map O.subtype = (r : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.algebraMap_matrix_apply]
      · simp [Matrix.algebraMap_matrix_apply, h, Matrix.one_apply_ne h]
    rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]

theorem single_map_subtype {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (a b : Fin n) :
    (Matrix.single a b (1 : O)).map O.subtype = (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem entry_mul_inv_entry_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) (i a b j : Fin n) :
    (m : Matrix (Fin n) (Fin n) K) i a * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b j ∈ O := by
  have hle : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) ≤ conjInt O m := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx'⟩ := hc x hx
    exact ⟨x', congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hx'⟩
  rw [hT] at hle
  obtain ⟨Y, hY⟩ := hle (Algebra.mem_top : Matrix.single a b (1 : O) ∈ (⊤ : Subalgebra O (Matrix (Fin n) (Fin n) O)))
  have h := congrFun (congrFun hY i) j
  rw [single_map_subtype, single_conj_apply] at h
  rw [← h]
  exact (Y i j).2

theorem isScal_of_conj (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) : IsScal O m := by
  have H := entry_mul_inv_entry_mem O m T hT hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  set M : Matrix (Fin n) (Fin n) K := (m : Matrix (Fin n) (Fin n) K) with hM
  set N : Matrix (Fin n) (Fin n) K := ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  have hMN : M * N = 1 := Units.mul_inv m
  obtain ⟨⟨i0, a0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => O.valuation (M p.1 p.2)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  set c := M i0 a0 with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : ∀ i a, M i a = 0 := fun i a => by
      have h1 := hmax (i, a) (Finset.mem_univ _)
      simp only [h0, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    have h1 := congrFun (congrFun hMN ⟨0, hn⟩) ⟨0, hn⟩
    simp [Matrix.mul_apply, hz] at h1
  have hv : 0 < O.valuation c := (Valuation.pos_iff _).2 hc0
  have hy : ∀ i a, c⁻¹ * M i a ∈ O := fun i a => by
    rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hv).2 (hmax (i, a) (Finset.mem_univ _))
  have hz : ∀ b j, c * N b j ∈ O := fun b j => H i0 a0 b j
  let Y : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hy i j⟩
  let Z : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hz i j⟩
  have hYm : Y.map O.subtype = c⁻¹ • M := by ext i j; rfl
  have hZm : Z.map O.subtype = c • N := by ext i j; rfl
  have inj : Function.Injective fun X : Matrix (Fin n) (Fin n) O => X.map O.subtype :=
    Matrix.map_injective (Subtype.val_injective)
  have key : ∀ {A B : Matrix (Fin n) (Fin n) K}, A * B = 1 → (c⁻¹ • A) * (c • B) = 1 := fun {A B} h => by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, h]
  have hNM : N * M = 1 := Units.inv_mul m
  have e1 : Y * Z = 1 := inj (by
    show (Y * Z).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, key hMN])
  have e2 : Z * Y = 1 := inj (by
    show (Z * Y).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc0, one_smul, hNM])
  refine ⟨Units.mk0 c hc0, ⟨Y, Z, e1, e2⟩, ?_⟩
  show M = c • (Y.map O.subtype)
  rw [hYm, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end GlobalTheory.ScalConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KerReductionLeRangeReductionOfMulEqSmul
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem ker_map_subset_range_map_of_mul_eq_smul :
    ∀ {O : Type} [CommRing O] [IsDomain O] {k : Type} [Field k] (r : O →+* k),
      Function.Surjective r → ∀ {n : ℕ} (M N : Matrix (Fin n) (Fin n) O) (π : O), π ≠ 0 →
      (∀ t : O, r t = 0 → ∃ s, t = π * s) → M * N = π • (1 : Matrix (Fin n) (Fin n) O) →
      ∀ (v : Fin n → k), N.map r *ᵥ v = 0 → ∃ u, v = M.map r *ᵥ u := by
  intro O _ _ k _ r hr n M N π hπ hker hMN v hv
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (x : Fin n → O),
      (fun i => r ((A *ᵥ x) i)) = A.map r *ᵥ (fun i => r (x i)) := by
    intro A x
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  set v' : Fin n → O := fun i => Function.surjInv hr (v i) with hv'def
  have hv' : (fun i => r (v' i)) = v := funext fun i => Function.surjInv_eq hr (v i)
  have h0 : ∀ i, r ((N *ᵥ v') i) = 0 := by
    intro i
    have := congrFun (hmap N v') i
    rw [this, hv', hv]
    rfl
  choose w hw using fun i => hker _ (h0 i)
  have hNw : N *ᵥ v' = π • w := by
    funext i; simp [hw i]
  have key : π • v' = π • (M *ᵥ w) := by
    calc π • v' = (π • (1 : Matrix (Fin n) (Fin n) O)) *ᵥ v' := by
            rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (M * N) *ᵥ v' := by rw [hMN]
      _ = M *ᵥ (N *ᵥ v') := by rw [Matrix.mulVec_mulVec]
      _ = π • (M *ᵥ w) := by rw [hNw, Matrix.mulVec_smul]
  have hvw : v' = M *ᵥ w := smul_right_injective (Fin n → O) hπ key
  refine ⟨fun i => r (w i), ?_⟩
  rw [← hmap, ← hvw, hv']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaxUnramifiedResidueAlgClosedAndFrobeniusLift
section
noncomputable section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda.KurUnr

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_pow_sub_pow_le {y z : K} (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - z ^ i‖ ≤ ‖y - z‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - z ^ (i + 1) = y * (y ^ i - z ^ i) + (y - z) * z ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - z‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - z‖ * ‖z‖ ^ i ≤ ‖y - z‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz) (norm_nonneg _)
        _ = ‖y - z‖ := mul_one _

theorem norm_eval_sub_eval_le (f : Polynomial K) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {y z : K}
    (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) : ‖f.eval y - f.eval z‖ ≤ ‖y - z‖ := by
  rw [Polynomial.eval_eq_sum_range y, Polynomial.eval_eq_sum_range z, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖f.coeff i‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
        mul_le_mul (hf i) (norm_pow_sub_pow_le hy hz i) (norm_nonneg _) zero_le_one
    _ = ‖y - z‖ := one_mul _

theorem norm_root_le_one (f : Polynomial K) (hm : f.Monic) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {z : K}
    (hz : f.eval z = 0) : ‖z‖ ≤ 1 := by
  by_contra h
  push_neg at h
  set n := f.natDegree
  have e := hm.as_sum
  have h0 : z ^ n = -∑ i ∈ Finset.range n, f.coeff i * z ^ i := by
    have := congrArg (Polynomial.eval z) e
    rw [hz] at this
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C] at this
    linear_combination -this
  have hz0 : (0 : ℝ) ≤ ‖z‖ ^ (n - 1) := by positivity
  have hb : ‖∑ i ∈ Finset.range n, f.coeff i * z ^ i‖ ≤ ‖z‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hz0 fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖f.coeff i‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ (n - 1) :=
          mul_le_mul (hf i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖z‖ ^ (n - 1) := one_mul _
  rw [← norm_neg, ← h0, norm_pow] at hb
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn] at h0
  · have : ‖z‖ ^ (n - 1) < ‖z‖ ^ n := pow_lt_pow_right₀ h (by omega)
    linarith

theorem unr_of_unrOK (l : ℕ) (σ : K →+* K) (h : Formalism.InvariantFactorPaths.G7.UnrOK K l σ) : Unr K l σ := by
  obtain ⟨hp, hl2, hnl, hval, hfr⟩ := h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlK : (l : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnl
    exact (inv_pos.mpr hl0).ne' hnl.symm

  have hiso : ∀ a : K, ‖σ a‖ = ‖a‖ := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    obtain ⟨k, hk⟩ := hval a ha
    set u := a * (l : K) ^ k with hu
    have hc : ‖((l : K) ^ k)‖ = (l : ℝ)⁻¹ ^ k := by rw [norm_zpow, hnl]
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_mul, hc, hk, inv_zpow', ← zpow_add₀ hl0.ne', add_neg_cancel, zpow_zero]
    have hsu : ‖σ u‖ = 1 := by
      have h1 := hfr u hun.le
      have hup : ‖u ^ l‖ = 1 := by rw [norm_pow, hun, one_pow]
      have hne : ‖σ u - u ^ l‖ ≠ ‖u ^ l‖ := by rw [hup]; linarith
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, hup, max_eq_right (by linarith)] at this
      exact this
    have hσu : σ u = σ a * (l : K) ^ k := by rw [hu, map_mul, map_zpow₀, map_natCast]
    have hcne : ‖((l : K) ^ k)‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact zpow_ne_zero _ hlK
    have e1 : ‖σ a‖ * ‖((l : K) ^ k)‖ = ‖a‖ * ‖((l : K) ^ k)‖ := by
      rw [← norm_mul, ← norm_mul, ← hσu, ← hu, hsu, hun]
    exact mul_right_cancel₀ hcne e1
  refine ⟨hp, hl2, by rw [hnl]; exact hlinv, ?_, hiso, ?_⟩
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    obtain ⟨k, hk⟩ := hval x hx0
    rw [hnl, hk]
    have hkneg : k ≤ -1 := by
      by_contra hk1
      push_neg at hk1
      have : (1 : ℝ) ≤ (l : ℝ) ^ k := one_le_zpow₀ hl1.le (by omega)
      rw [← hk] at this
      linarith
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le hkneg
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  · intro x hx
    exact (hfr x hx).trans_lt hlinv

end GlobalTheory.Honda.KurUnr


open GlobalTheory.Honda.KurUnr in
theorem GlobalTheory.Honda.kur_resAlg_unr : ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  intro l _ _
  refine ⟨?_, fun σ hσ => unr_of_unrOK l σ hσ⟩
  intro f hm hdeg hf
  set g : Polynomial ℂ_[l] := f.map (MaximalUnramifiedExtension l).subtype with hg
  have hgm : g.Monic := hm.map _
  have hgdeg : g.natDegree = f.natDegree := Polynomial.natDegree_map _
  have hgc : ∀ n, ‖g.coeff n‖ ≤ 1 := fun n => by
    rw [hg, Polynomial.coeff_map]
    exact hf n
  have hdg : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast hdeg.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root g hdg
  have hz1 : ‖z‖ ≤ 1 := norm_root_le_one g hgm hgc hz
  obtain ⟨y, hyK, hy1, hzy⟩ := _root_.GlobalTheory.ResidueUnr.exists_near_kur l z hz1
  refine ⟨⟨y, hyK⟩, hy1, ?_⟩
  have hev : ((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l]) = g.eval y := by
    rw [hg, Polynomial.eval_map]
    exact (Polynomial.eval₂_hom (MaximalUnramifiedExtension l).subtype ⟨y, hyK⟩).symm
  change ‖((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1
  rw [hev, ← sub_zero (g.eval y), ← hz]
  calc ‖g.eval y - g.eval z‖ ≤ ‖y - z‖ := norm_eval_sub_eval_le g hgc hy1 hz1
    _ = ‖z - y‖ := norm_sub_rev _ _
    _ < 1 := hzy
end
end

