module

public import Formalism.CharacterColumnKernels.Statement
public import Formalism.CharacterColumnKernels.Bundle0001
public import Formalism.CharacterColumnKernels.StatementX
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001

@[expose] public section

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelLengthBound
section
open Finset

namespace Formalism.NG

private lemma padicValInt_eq_emultiplicity (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  change (multiplicity l z.natAbs : ℕ∞) = emultiplicity (l : ℤ) z
  rw [multiplicity_eq_emultiplicity hz',
    ← Int.natCast_emultiplicity, Int.natCast_natAbs]
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h, emultiplicity_neg]

private lemma padicValInt_pow_sub_one_eq_add (l : ℕ) [hl : Fact l.Prime] (s₀ : ℕ) (hs : 1 ≤ s₀) (hs2 : l = 2 → 2 ≤ s₀)
    (x : ℤ) (hx1 : (l : ℤ) ^ s₀ ∣ x - 1) (hx2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1)
    (n : ℕ) (hn0 : n ≠ 0) :
    x ^ n - 1 ≠ 0 ∧ padicValInt l (x ^ n - 1) = s₀ + padicValNat l n := by
  have hlp := hl.out
  have hE1 : emultiplicity (l : ℤ) (x - 1) = s₀ := emultiplicity_eq_coe.mpr ⟨hx1, hx2⟩
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h hdvd; simpa using this
    exact (Nat.prime_iff_prime_int.mp hlp).not_dvd_one h1
  have hE : emultiplicity (l : ℤ) (x ^ n - 1) = (s₀ : ℕ∞) + emultiplicity l n := by
    rcases hlp.eq_two_or_odd' with h2 | hodd
    · subst h2
      have h4 : (4 : ℤ) ∣ x - 1 := by
        have := (pow_dvd_pow ((2 : ℕ) : ℤ) (hs2 rfl)).trans hx1
        norm_num at this
        exact this
      push_cast at hlx hE1 ⊢
      have := Int.two_pow_sub_pow' n h4 hlx
      rw [one_pow] at this
      have hc := Int.natCast_emultiplicity 2 n
      push_cast at hc
      rw [this, hE1, hc]
    · have := Int.emultiplicity_pow_sub_pow hlp hodd (y := 1) hdvd hlx n
      rw [one_pow] at this
      rw [this, hE1]
  have hfin : emultiplicity (l : ℤ) (x ^ n - 1) = ((s₀ + padicValNat l n : ℕ) : ℕ∞) := by
    rw [hE, ← multiplicity_eq_emultiplicity hn0, Nat.padicValNat_def]
    norm_cast
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hfin
    exact ENat.top_ne_coe _ hfin
  refine ⟨hne, ?_⟩
  have := padicValInt_eq_emultiplicity l hne
  rw [hfin] at this
  exact_mod_cast this

theorem character_column_kernel_length_bound : characterColumnKernelLengthBound := by
  intro l hl s₀ hs hs2 x hx1 hx2 a b hab
  have hlp := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨hne, hv⟩ := padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (b - a) (by omega)
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x ^ a := by
    intro h
    have h' : (l : ℤ) ∣ x := hlp.dvd_of_dvd_pow h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h' hdvd; simpa using this
    exact hlp.not_dvd_one h1
  have hxa : x ^ a ≠ 0 := fun h ↦ hlx (h ▸ dvd_zero _)
  have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hab.le, mul_one]
  rw [e, padicValInt.mul hxa hne, padicValInt.eq_zero_of_not_dvd hlx, zero_add, hv]

end Formalism.NG
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.GenRelMapApply
section
open Finset

noncomputable section

namespace Formalism.NG

section GenKey

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma gen_relMap_apply {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b O) (v : b → KO O) (i : a) :
    relMap O (KO O) X v i = ∑ j, X i j • v j := rfl

lemma gen_relMap_mul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (X : Matrix a b O) (Y : Matrix b c O) :
    relMap O (KO O) (X * Y) = relMap O (KO O) X ∘ₗ relMap O (KO O) Y := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, gen_relMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

lemma gen_relMap_one {a : Type*} [Fintype a] [DecidableEq a] (v : a → KO O) :
    relMap O (KO O) (1 : Matrix a a O) v = v := by
  funext i
  simp [gen_relMap_apply, Matrix.one_apply, ite_smul]

lemma gen_key {M G : Type} [Fintype M] [DecidableEq M] [Fintype G] [DecidableEq G]
    (A : Matrix M G O) : ∃ (n : ℕ) (U : Matrix M M O) (f : Fin n ↪ M) (e : Fin n ↪ G),
      (∃ C0 : Matrix G M O, IsUnit (Matrix.of fun p q => (C0 * U) (e p) (f q)).det) ∧
      ∀ C' : Matrix G M O, IsUnit (Matrix.of fun p q => (C' * U) (e p) (f q)).det →
        LinearMap.ker (relMap O (KO O) (C' * A)) = LinearMap.ker (relMap O (KO O) A) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin A)).smithNormalForm (Pi.basisFun O M)
  set U : Matrix M M O := (Pi.basisFun O M).toMatrix snf.bM with hUdef
  set W : Matrix M M O := snf.bM.toMatrix (Pi.basisFun O M) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hn : n ≤ Fintype.card G := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    have h2 := LinearMap.finrank_range_le (Matrix.mulVecLin A)
    rw [h1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    exact h2
  let e : Fin n ↪ G := (Fin.castLEEmb hn).trans (Fintype.equivFin G).symm.toEmbedding
  refine ⟨n, U, snf.f, e, ?_, ?_⟩
  · refine ⟨Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0, ?_⟩
    have hZ : (Matrix.of fun p q =>
        ((Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0) * U) (e p) (snf.f q)) = 1 := by
      ext p q
      simp only [Matrix.of_apply, Matrix.mul_apply, e.injective.eq_iff, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [← Matrix.mul_apply, hWU]
      simp [Matrix.one_apply, snf.f.injective.eq_iff]
    rw [hZ, Matrix.det_one]
    exact isUnit_one
  · intro C' hC
    set Y : Matrix M G O := W * A with hYdef
    have hAY : A = U * Y := by rw [hYdef, ← Matrix.mul_assoc, hUW, Matrix.one_mul]
    have hY : ∀ k, k ∉ Set.range snf.f → ∀ j, Y k j = 0 := by
      intro k hk j
      have hmem : (fun l => A l j) ∈ LinearMap.range (Matrix.mulVecLin A) :=
        ⟨Pi.single j 1, by
          funext l
          simp⟩
      have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem⟩ hk
      rw [← Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O M)] at h0
      simpa [hYdef, Matrix.mulVec, dotProduct, Matrix.mul_apply] using h0
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      set y := relMap O (KO O) Y v with hydef
      have hy0 : ∀ k, k ∉ Set.range snf.f → y k = 0 := by
        intro k hk
        simp [hydef, gen_relMap_apply, hY k hk]
      have hv' : relMap O (KO O) (C' * U) y = 0 := by
        rw [hydef, ← LinearMap.comp_apply, ← gen_relMap_mul, Matrix.mul_assoc, ← hAY]
        exact hv
      set Z : Matrix (Fin n) (Fin n) O := Matrix.of fun p q => (C' * U) (e p) (snf.f q) with hZdef
      have hz : relMap O (KO O) Z (y ∘ snf.f) = 0 := by
        funext p
        have := congrFun hv' (e p)
        rw [gen_relMap_apply, Pi.zero_apply] at this
        rw [gen_relMap_apply, Pi.zero_apply]
        exact (Fintype.sum_of_injective snf.f snf.f.injective _ _
          (fun k hk => by simp [hy0 k hk]) (fun q => rfl)).trans this
      have hyf : y ∘ snf.f = 0 := by
        rw [← gen_relMap_one (y ∘ snf.f), ← Matrix.nonsing_inv_mul Z hC, gen_relMap_mul,
          LinearMap.comp_apply, hz, map_zero]
      have hy : y = 0 := by
        funext k
        by_cases hk : k ∈ Set.range snf.f
        · obtain ⟨q, rfl⟩ := hk
          exact congrFun hyf q
        · exact hy0 k hk
      rw [hAY, gen_relMap_mul, LinearMap.comp_apply, ← hydef, hy, map_zero]
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [gen_relMap_mul, LinearMap.comp_apply, hv, map_zero]

end GenKey

lemma gen_bigMat_mul {R O : Type*} [Ring R] [CommRing O] [Algebra O R] {m g d : Type*}
    [Fintype m] [Fintype d] [DecidableEq d] (ρ : R →ₐ[O] Matrix d d O) (C : Matrix g m R) (P : Matrix m g R) :
    bigMat (⇑ρ) (C * P) = bigRect (⇑ρ) C * bigRect (⇑ρ) P := by
  ext p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [bigMat, bigRect, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.LenCokerOfDetNeZero
section
open Finset Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.NG

section HomQuotAux

variable {R O M NN : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] [AddCommGroup NN] [Module R NN] {g : Type} [Fintype g]

end HomQuotAux

section KerHomAux

variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)

def uncurryEquiv : (g → LatQ O d ρ) ≃ₗ[O] (g × d → KO O) where
  toFun v p := v p.1 p.2
  invFun w j b := w (j, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [SMulCommClass R O (LatQ O d ρ)]

end KerHomAux

section LenCokerAux

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : Type} [Fintype ι] [DecidableEq ι]

end LenCokerAux

end Formalism.NG
end
end

