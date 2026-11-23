module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayer
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_unitary_of_skew_layer (R K : Type) [CommRing R] [Field K] [StarRing K]
    [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R)
    (hJ : Jᴴ = J) (hdet : J.det ≠ 0)
    (hw : algebraMap R K w + star (algebraMap R K w) = 1)
    (hA : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (_hadj : ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c)
    (c : ℕ) (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ A c) (hskew : J⁻¹ * Xᴴ * J = -X) :
    ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  classical
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have cL : ∀ B : Matrix (Fin n) (Fin n) K, J * (J⁻¹ * B) = B :=
    fun B => Matrix.mul_nonsing_inv_cancel_left J B hu
  have cL' : ∀ B : Matrix (Fin n) (Fin n) K, J⁻¹ * (J * B) = B :=
    fun B => Matrix.nonsing_inv_mul_cancel_left J B hu
  have cR : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have cR' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hJi : (J⁻¹)ᴴ = J⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hJ]
  have hanti : Antitone A := antitone_nat_of_succ_le hA
  have to0 : ∀ {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d → M ∈ A 0 :=
    fun h => hanti (Nat.zero_le _) h
  have smem : ∀ (r : R) {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d →
      algebraMap R K r • M ∈ A d := by
    intro r d M h
    rw [algebraMap_smul]
    exact (A d).smul_mem r h
  set β : K := algebraMap R K w with hβ
  have hst : star β = 1 - β := by rw [← hw]; ring

  have key : ∀ k : ℕ, ∃ Y ∈ A (c + 1),
      J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A (c + 1 + k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, (A (c + 1)).zero_mem, ?_⟩
      have hX' : Xᴴ = -(J * (X * J⁻¹)) := by
        calc Xᴴ = J * ((J⁻¹ * Xᴴ * J) * J⁻¹) := by
              simp only [mul_assoc, cR, mul_one, cL]
          _ = -(J * (X * J⁻¹)) := by rw [hskew]; simp only [neg_mul, mul_neg]
      have h0 : J⁻¹ * (1 + X + 0)ᴴ * J * (1 + X + 0) - 1 = -(X * X) := by
        simp only [add_zero, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX']
        simp only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, cL', cR']
        abel
      rw [h0, Nat.add_zero]
      exact (A (c + 1)).neg_mem (hmul c X hX X (to0 hX)).1
    | succ k ih =>
      obtain ⟨Y, hY, hE⟩ := ih
      set g := 1 + X + Y with hg
      set E := J⁻¹ * gᴴ * J * g - 1 with hEdef
      have hEE : E * E ∈ A (c + 1 + (k + 1)) := (hmul (c + 1 + k) E hE E (to0 hE)).1
      have hEEE : E * (E * E) ∈ A (c + 1 + (k + 1)) :=
        (hmul (c + 1 + k) E hE (E * E) (to0 hEE)).1
      refine ⟨Y - β • (g * E), ?_, ?_⟩
      · have hEc : E ∈ A (c + 1) := hanti (by omega) hE
        have hgE : g * E ∈ A (c + 1) := by
          rw [hg, add_mul, add_mul, one_mul]
          exact add_mem (add_mem hEc (hmul c X hX E (to0 hE)).1)
            (hanti (by omega) (hmul (c + 1) Y hY E (to0 hE)).1)
        exact sub_mem hY (smem w hgE)
      · have hgeq : 1 + X + (Y - β • (g * E)) = g - β • (g * E) := by rw [hg]; abel
        rw [hgeq]

        have hEH : J⁻¹ * Eᴴ * J = E := by
          rw [hEdef]
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, hJi, hJ, sub_mul, mul_sub, mul_one, mul_assoc, cR']
        have h1 : J⁻¹ * (Eᴴ * (gᴴ * J)) = E * (J⁻¹ * (gᴴ * J)) := by
          calc J⁻¹ * (Eᴴ * (gᴴ * J)) = (J⁻¹ * Eᴴ * J) * (J⁻¹ * (gᴴ * J)) := by
                simp only [mul_assoc, cL]
            _ = E * (J⁻¹ * (gᴴ * J)) := by rw [hEH]
        have hP' : J⁻¹ * (g - β • (g * E))ᴴ * J
            = J⁻¹ * (gᴴ * J) - star β • (E * (J⁻¹ * (gᴴ * J))) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
            mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, h1]
        have hPg0 : J⁻¹ * (gᴴ * (J * g)) = 1 + E := by
          rw [hEdef]; simp only [mul_assoc]; abel
        have hPg : ∀ M, J⁻¹ * (gᴴ * (J * (g * M))) = M + E * M := by
          intro M
          rw [hEdef]; simp only [sub_mul, one_mul, mul_assoc]; abel
        have hid : J⁻¹ * (g - β • (g * E))ᴴ * J * (g - β • (g * E)) - 1
            = (β - β * β - 1) • (E * E) + (β - β * β) • (E * (E * E)) := by
          rw [hP']
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, hPg, hPg0,
            mul_add, mul_one, smul_add, hst]
          module
        have s1 : β - β * β - 1 = algebraMap R K (w - w * w - 1) := by simp [hβ]
        have s2 : β - β * β = algebraMap R K (w - w * w) := by simp [hβ]
        rw [hid, s1, s2]
        exact add_mem (smem _ hEE) (smem _ hEEE)
  obtain ⟨Y, hY, hEm⟩ := key m
  refine ⟨Y, hY, ?_⟩
  have hz : J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A m := hanti (by omega) hEm
  rw [hm, Submodule.mem_bot, sub_eq_zero] at hz
  calc (1 + X + Y)ᴴ * J * (1 + X + Y)
      = J * (J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y)) := by simp only [mul_assoc, cL]
    _ = J := by rw [hz, mul_one]

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizer
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabRing

open Formalism.UG

theorem cT_add_rect {R : Type} [CommRing R] (σ : R →+* R) {a b : Type} (M N : Matrix a b R) :
    cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem exists_emb_block {R : Type} [CommRing R] (σ : R →+* R) {n m k : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (J : Matrix n n R) (J' : Matrix m m R) (X : Matrix n k R) (U : Matrix k n R)
    (A : Matrix n m R) (A' : Matrix m n R)
    (hB : IsUnit (cT σ X * J * X)) (hXA : cT σ X * J * A = 0) (hAX : cT σ A * J * X = 0)
    (hJ : cT σ A * J * A = J') (h1 : A' * A = 1) (h2 : A' * X = 0) (h3 : U * A = 0) (h4 : U * X = 1)
    (h5 : X * U + A * A' = 1) :
    ∃ j : UJ σ J' →* UJ σ J,
      (∀ g, ((j g : GL n R) : Matrix n n R) = X * U + A * ((g : GL m R) : Matrix m m R) * A') ∧
      ∀ h : UJ σ J, ((h : GL n R) : Matrix n n R) * X = X → h ∈ j.range := by
  have hmul : ∀ g g' : Matrix m m R,
      (X * U + A * g * A') * (X * U + A * g' * A') = X * U + A * (g * g') * A' := by
    intro g g'
    calc (X * U + A * g * A') * (X * U + A * g' * A')
        = X * (U * X) * U + X * (U * A) * g' * A' + (A * g * (A' * X) * U + A * g * (A' * A) * g' * A') := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [h1, h2, h3, h4]; simp [Matrix.mul_assoc]
  have hone : X * U + A * (1 : Matrix m m R) * A' = 1 := by rw [Matrix.mul_one, h5]
  have hform : ∀ g : Matrix m m R, cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
      = cT σ U * (cT σ X * J * X) * U + cT σ A' * (cT σ g * J' * g) * A' := by
    intro g
    calc cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
        = cT σ U * (cT σ X * J * X) * U + cT σ U * (cT σ X * J * A) * g * A'
          + (cT σ A' * cT σ g * (cT σ A * J * X) * U
            + cT σ A' * (cT σ g * (cT σ A * J * A) * g) * A') := by
          simp only [cT_add_rect, cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [hXA, hAX, hJ]; simp
  have hJJ : cT σ U * (cT σ X * J * X) * U + cT σ A' * J' * A' = J := by
    have := hform 1
    rw [hone] at this
    simpa [cT_one] using this.symm
  let j0 : GL m R → GL n R := fun g =>
    ⟨X * U + A * (g : Matrix m m R) * A', X * U + A * ((g⁻¹ : GL m R) : Matrix m m R) * A',
      by rw [hmul, Units.mul_inv, hone], by rw [hmul, Units.inv_mul, hone]⟩
  have hmem : ∀ g : UJ σ J', j0 g ∈ UJ σ J := by
    intro g
    have hg : cT σ ((g : GL m R) : Matrix m m R) * J' * ((g : GL m R) : Matrix m m R) = J' := g.2
    change cT σ (X * U + A * ((g : GL m R) : Matrix m m R) * A') * J
      * (X * U + A * ((g : GL m R) : Matrix m m R) * A') = J
    rw [hform, hg, hJJ]
  let j : UJ σ J' →* UJ σ J :=
    { toFun := fun g => ⟨j0 g, hmem g⟩
      map_one' := by
        apply Subtype.ext; apply Units.ext
        exact hone
      map_mul' := by
        intro g g'
        apply Subtype.ext; apply Units.ext
        exact (hmul _ _).symm }
  refine ⟨j, fun g => rfl, ?_⟩
  have hXJ : cT σ X * J = cT σ X * J * X * U := by
    calc cT σ X * J = cT σ X * J * (X * U + A * A') := by rw [h5, Matrix.mul_one]
      _ = cT σ X * J * X * U + cT σ X * J * A * A' := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = _ := by rw [hXA]; simp
  have key : ∀ h : Matrix n n R, cT σ h * J * h = J → h * X = X → A * (A' * h * A) = h * A := by
    intro h hh hX
    have e1 : cT σ X * J * X * (U * h * A) = 0 := by
      calc cT σ X * J * X * (U * h * A) = (cT σ X * J * X * U) * h * A := by
            simp only [Matrix.mul_assoc]
        _ = cT σ (h * X) * J * h * A := by rw [← hXJ, hX]
        _ = cT σ X * (cT σ h * J * h) * A := by simp only [cT_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hh, hXA]
    have e2 : U * h * A = 0 := by
      obtain ⟨b, hb⟩ := hB
      rw [← hb] at e1
      calc U * h * A = ((b⁻¹ : GL k R) : Matrix k k R) * (b : Matrix k k R) * (U * h * A) := by
            rw [Units.inv_mul, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
    calc A * (A' * h * A) = X * (U * h * A) + A * (A' * h * A) := by rw [e2]; simp
      _ = (X * U + A * A') * h * A := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = h * A := by rw [h5, Matrix.one_mul]
  intro h hX
  have hh : cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R) = J := h.2
  have hh' : cT σ (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * J
      * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) = J := (h⁻¹).2
  have hX' : (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * X = X := by
    conv_lhs => rw [← hX]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have k1 := key _ hh hX
  have k2 := key _ hh' hX'
  let g : GL m R := ⟨A' * ((h : GL n R) : Matrix n n R) * A,
    A' * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * A,
    by rw [Matrix.mul_assoc _ A, k2, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.mul_inv,
      Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc _ A, k1, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.inv_mul,
      Matrix.one_mul, h1]⟩
  have hg : g ∈ UJ σ J' := by
    change cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J'
      * (A' * ((h : GL n R) : Matrix n n R) * A) = J'
    calc cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J' * (A' * ((h : GL n R) : Matrix n n R) * A)
        = cT σ (A * (A' * ((h : GL n R) : Matrix n n R) * A)) * J
          * (A * (A' * ((h : GL n R) : Matrix n n R) * A)) := by
          rw [cT_mul σ A, ← hJ]; simp only [Matrix.mul_assoc]
      _ = cT σ A * (cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R)) * A := by
          rw [k1]; simp only [cT_mul, Matrix.mul_assoc]
      _ = J' := by rw [hh, hJ]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  change X * U + A * (A' * ((h : GL n R) : Matrix n n R) * A) * A' = ((h : GL n R) : Matrix n n R)
  rw [k1]
  calc X * U + ((h : GL n R) : Matrix n n R) * A * A'
      = ((h : GL n R) : Matrix n n R) * X * U + ((h : GL n R) : Matrix n n R) * A * A' := by rw [hX]
    _ = ((h : GL n R) : Matrix n n R) * (X * U + A * A') := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = _ := by rw [h5, Matrix.mul_one]

theorem exists_emb : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  intro R _ σ n m J J' x u A A' hB hXA hAX hJ h1 h2 h3 h4 h5
  have hc : cT σ (replicateCol Unit x) = replicateRow Unit (fun i => σ (x i)) := by
    ext i j; simp [cT]
  rw [vecMulVec_eq Unit] at h5 ⊢
  obtain ⟨j, hj1, hj2⟩ := exists_emb_block σ J J' (replicateCol Unit x) (replicateRow Unit u) A A'
    (by
      rw [hc, Matrix.mul_assoc, ← replicateCol_mulVec, replicateRow_mul_replicateCol,
        Matrix.isUnit_iff_isUnit_det]
      simpa using hB)
    (by rw [hc, Matrix.mul_assoc, ← replicateRow_vecMul, hXA]; simp)
    (by rw [Matrix.mul_assoc, ← replicateCol_mulVec, ← replicateCol_mulVec, hAX]; simp)
    hJ h1
    (by rw [← replicateCol_mulVec, h2]; simp)
    (by rw [← replicateRow_vecMul, h3]; simp)
    (by rw [replicateRow_mul_replicateCol, h4]; ext i j; simp)
    h5
  exact ⟨j, hj1, fun h hx => hj2 h (by rw [← replicateCol_mulVec, hx])⟩

end GlobalTheory.StabRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankMatricesLoweringFiltrationByEqSuccAdd
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LowDim

variable {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ}

theorem block_eq_zero (hB : Biorth r m U (fun b => (U b)ᴴ)) {s : ℕ} (hs : m ≤ s) : U s = 0 := by
  obtain ⟨-, h2, h3⟩ := hB
  calc U s = (∑ b ∈ range m, U b * (U b)ᴴ) * U s := by rw [h3, Matrix.one_mul]
    _ = 0 := by
      rw [Matrix.sum_mul]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' : b ≠ s := by have := Finset.mem_range.1 hb; omega
      rw [Matrix.mul_assoc, h2 b s hb', Matrix.mul_zero]

theorem mem_lowers_iff_blocks (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hB
  rw [mem_lowers]
  constructor
  · intro h s t hst
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have hy : U t *ᵥ Pi.single j 1 ∈ W (s + c + 1) := by
      rw [hW]
      intro b hb
      rw [Matrix.mulVec_mulVec, h2 b t (by omega), Matrix.zero_mulVec]
    have := (hW _ _).1 (h s _ hy) s le_rfl
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, Matrix.zero_mulVec]
  · intro h b y hy
    rw [hW]
    intro s hs
    have e : (U s)ᴴ *ᵥ Y *ᵥ y = ((U s)ᴴ * Y * ∑ t ∈ range m, U t * (U t)ᴴ) *ᵥ y := by
      rw [h3, Matrix.mul_one, Matrix.mulVec_mulVec]
    rw [e, Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    by_cases hst : t ≤ s + c
    · rw [h s t hst, Matrix.zero_mulVec]
    · rw [(hW _ _).1 hy t (by omega), Matrix.mulVec_zero]

noncomputable def layer (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (c : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) ℂ where
  toFun Y b := (U b)ᴴ * Y * U (b + c + 1)
  map_add' Y Z := by
    funext b
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a Y := by
    funext b
    simp

end GlobalTheory.RadCov.LowDim

namespace GlobalTheory.RadCov


open LowDim in
theorem finrank_lowers_eq_succ_add (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) :
    Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) +
      ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  have hle : lowers W (c + 1) ≤ lowers W c := by
    intro Y hY
    rw [mem_lowers_iff_blocks hB hW] at hY ⊢
    exact fun s t hst => hY s t (by omega)
  let φ := (layer m U c).domRestrict (lowers W c)
  have hker : LinearMap.ker φ = (lowers W (c + 1)).comap (lowers W c).subtype := by
    ext ⟨Y, hY⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      mem_lowers_iff_blocks hB hW]
    rw [mem_lowers_iff_blocks hB hW] at hY
    constructor
    · intro h s t hst
      by_cases h' : t ≤ s + c
      · exact hY s t h'
      · obtain rfl : t = s + c + 1 := by omega
        by_cases hs : s < m
        · exact congrFun h ⟨s, hs⟩
        · rw [block_eq_zero hB (not_lt.1 hs)]
          simp
    · intro h
      funext b
      exact h b (b + c + 1) le_rfl
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro Z
    obtain ⟨h1, h2, -⟩ := id hB
    have key : ∀ s t, (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U t
        = ∑ b : Fin m, ((U s)ᴴ * U b) * Z b * ((U (b + c + 1))ᴴ * U t) := by
      intro s t
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by simp only [Matrix.mul_assoc]
    refine ⟨⟨∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ, ?_⟩, ?_⟩
    · rw [mem_lowers_iff_blocks hB hW]
      intro s t hst
      rw [key]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : s = b
      · rw [h2 (b + c + 1) t (by omega), Matrix.mul_zero]
      · rw [h2 s b hb, Matrix.zero_mul, Matrix.zero_mul]
    · funext s
      change (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U (s + c + 1) = Z s
      rw [key, Finset.sum_eq_single s]
      · rw [h1, h1, Matrix.one_mul, Matrix.mul_one]
      · intro b _ hb
        rw [h2 s b (fun h => hb (Fin.ext h.symm)), Matrix.zero_mul, Matrix.zero_mul]
      · simp
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hrange, finrank_top, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    Module.finrank_pi_fintype] at h
  rw [← h, add_comm, ← Fin.sum_univ_eq_sum_range (fun b => r b * r (b + c + 1)) m]
  simp [Module.finrank_matrix]

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNull
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

private lemma continuous_det_of' (j : ℕ) :
    Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := by
  fun_prop

theorem measurable_haarLoc_density (j : ℕ) :
    Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) := by
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_det_of' j).measurable
  exact ENNReal.measurable_ofReal.comp ((hd.norm.pow_const 2).inv.pow_const j)

theorem measurePreserving_withDensity_of_invariant {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) {g : X → ENNReal} (hg : Measurable g) (hfg : ∀ x, g (f x) = g x) :
    MeasurePreserving f (μ.withDensity g) (μ.withDensity g) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  conv_rhs => rw [← hf.map_eq]
  rw [setLIntegral_map hs hg hf.measurable]
  simp only [hfg]

theorem haarLoc_conj_and_null : ∀ j : ℕ, MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (haarLoc j) (haarLoc j) ∧ haarLoc j {x | (Matrix.of x).det = 0} = 0 := by
  intro j
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (show Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det by fun_prop).measurable
  constructor
  ·
    have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
      have h := Complex.conjLIE.measurePreserving
      have e : (⇑Complex.conjLIE : ℂ → ℂ) = ⇑(starRingEnd ℂ) := funext Complex.conjLIE_apply
      rwa [e] at h
    have hv : MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s))
        (volume : Measure (Fin j → Fin j → ℂ)) volume :=
      volume_preserving_pi fun _ => volume_preserving_pi fun _ => hc
    refine measurePreserving_withDensity_of_invariant hv (measurable_haarLoc_density j) ?_
    intro x
    have hdet : (Matrix.of fun r s => starRingEnd ℂ (x r s)).det = starRingEnd ℂ (Matrix.of x).det :=
      ((starRingEnd ℂ).map_det (Matrix.of x)).symm
    simp only [hdet, Complex.norm_conj]
  ·
    have hS : MeasurableSet {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} :=
      measurableSet_eq_fun hd measurable_const
    rw [haarLoc, withDensity_apply _ hS, ← lintegral_indicator hS]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have : ({x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0}.indicator
          fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)) = 0 := by
        funext x
        by_cases hx : (Matrix.of x).det = 0
        · simp [hx, zero_pow hj.ne']
        · simp [Set.indicator_of_notMem (show x ∉ {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} from hx)]
      rw [this, Pi.zero_def, lintegral_zero]

end GlobalTheory.LeviIso
end

