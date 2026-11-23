module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumInvStabilizerEqTsumMulFiber
section
open scoped ENNReal

namespace GlobalTheory

open MulAction

theorem encard_fiber_orbit_mul_stabilizer {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) (x : L) (y : Y) (g : Γ)
    (hg : g • π x = y) :
    ({z : L | π z = y ∧ z ∈ orbit Γ x}).encard * (stabilizer Γ x : Set Γ).encard
      = (stabilizer Γ y : Set Γ).encard := by
  classical
  have hx0 : π (g • x) = y := by rw [hπ, hg]
  have hset : (orbit (stabilizer Γ y) (g • x) : Set L) = {z : L | π z = y ∧ z ∈ orbit Γ x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      have hh : (h : Γ) • y = y := mem_stabilizer_iff.mp h.2
      refine ⟨?_, (h : Γ) * g, ?_⟩
      · show π ((h : Γ) • g • x) = y
        rw [hπ, hx0, hh]
      · show ((h : Γ) * g) • x = (h : Γ) • g • x
        rw [mul_smul]
    · rintro ⟨hz, k, rfl⟩
      have hk : k * g⁻¹ ∈ stabilizer Γ y := by
        rw [mem_stabilizer_iff]
        calc (k * g⁻¹) • y = (k * g⁻¹) • g • π x := by rw [hg]
          _ = π (k • x) := by rw [mul_smul, inv_smul_smul, hπ]
          _ = y := hz
      exact ⟨⟨k * g⁻¹, hk⟩, show (k * g⁻¹) • g • x = k • x by rw [mul_smul, inv_smul_smul]⟩
  have e : stabilizer (stabilizer Γ y) (g • x) ≃ stabilizer Γ x :=
    { toFun := fun s => ⟨g⁻¹ * ((s : stabilizer Γ y) : Γ) * g, by
        have hs : ((s : stabilizer Γ y) : Γ) • g • x = g • x := mem_stabilizer_iff.mp s.2
        rw [mem_stabilizer_iff, mul_smul, mul_smul, hs, inv_smul_smul]⟩
      invFun := fun t => ⟨⟨g * (t : Γ) * g⁻¹, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          rw [mem_stabilizer_iff, ← hg, mul_smul, mul_smul, inv_smul_smul, ← hπ, ht]⟩, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          show (g * (t : Γ) * g⁻¹) • g • x = g • x
          rw [mul_smul, mul_smul, inv_smul_smul, ht]⟩
      left_inv := fun s => by
        apply Subtype.ext; apply Subtype.ext
        show g * (g⁻¹ * ((s : stabilizer Γ y) : Γ) * g) * g⁻¹ = ((s : stabilizer Γ y) : Γ)
        group
      right_inv := fun t => by
        apply Subtype.ext
        show g⁻¹ * (g * (t : Γ) * g⁻¹) * g = (t : Γ)
        group }
  have key := ENat.card_congr
    (Subgroup.groupEquivQuotientProdSubgroup (s := stabilizer (stabilizer Γ y) (g • x)))
  rw [ENat.card_prod, ← ENat.card_congr (orbitEquivQuotientStabilizer (stabilizer Γ y) (g • x)),
    ENat.card_congr e] at key
  rw [← hset]
  exact key.symm

theorem encard_eq_tsum_fibers {L Q : Type} (F : Set L) (q : L → Q) :
    (F.encard : ℝ≥0∞) = ∑' o : Q, (({z | z ∈ F ∧ q z = o}).encard : ℝ≥0∞) := by
  classical
  have h1 : ∑' _ : F, (1 : ℝ≥0∞) = ∑' _ : (Σ o : Q, {z : F // q z = o}), (1 : ℝ≥0∞) :=
    ((Equiv.sigmaFiberEquiv (fun z : F => q z)).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
  rw [← ENNReal.tsum_set_one F, h1, ENNReal.tsum_sigma']
  refine tsum_congr fun o => ?_
  simp only [ENNReal.tsum_one]
  congr 1
  exact ENat.card_congr
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma inv_coe_mul_mul_coe_eq_inv_coe (a b : ℕ∞) (h0 : a * b ≠ 0) (ht : a * b ≠ ⊤) :
    (((a * b : ℕ∞) : ℝ≥0∞))⁻¹ * (a : ℝ≥0∞) = (b : ℝ≥0∞)⁻¹ := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h0
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h0
  induction a using ENat.recTopCoe with
  | top => exact absurd (ENat.top_mul hb0) ht
  | coe m =>
    induction b using ENat.recTopCoe with
    | top => exact absurd (by rw [mul_comm]; exact ENat.top_mul ha0) ht
    | coe k =>
      have hm : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha0
      have hk : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb0
      rw [ENat.toENNReal_mul, ENat.toENNReal_coe, ENat.toENNReal_coe,
        ENNReal.mul_inv (Or.inl hm) (Or.inr hk), mul_comm (m : ℝ≥0∞)⁻¹, mul_assoc,
        ENNReal.inv_mul_cancel hm (ENNReal.natCast_ne_top m), mul_one]

private lemma quotient_mk_map_eq_of_mem_orbit {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) {a b : L} (h : a ∈ orbit Γ b) :
    Quotient.mk (orbitRel Γ Y) (π a) = Quotient.mk (orbitRel Γ Y) (π b) := by
  obtain ⟨g, rfl⟩ := h
  apply Quotient.sound
  show π (g • b) ∈ orbit Γ (π b)
  rw [hπ]
  exact mem_orbit _ g

theorem tsum_inv_stabilizer_eq_tsum_mul_fiber {Γ L Y : Type} [Group Γ] [MulAction Γ L]
    [MulAction Γ Y] (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x)
    (hfin : ∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) :
    (∑' o : MulAction.orbitRel.Quotient Γ L,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)
      = ∑' o : MulAction.orbitRel.Quotient Γ Y,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹
          * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by
  classical
  set φ : orbitRel.Quotient Γ L → orbitRel.Quotient Γ Y :=
    fun o => Quotient.mk (orbitRel Γ Y) (π o.out) with hφ
  have hsplit := ((Equiv.sigmaFiberEquiv φ).tsum_eq
      (fun o : orbitRel.Quotient Γ L => (((stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)).symm.trans
    (ENNReal.tsum_sigma' _)
  refine hsplit.trans (tsum_congr fun O => ?_)
  change ∑' o : {o // φ o = O}, (((stabilizer Γ o.1.out : Set Γ).encard : ℝ≥0∞))⁻¹ = _
  have hsupp : Function.support (fun o : orbitRel.Quotient Γ L =>
      ((({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).encard : ℕ∞) : ℝ≥0∞))
      ⊆ {o | φ o = O} := by
    intro o ho
    obtain ⟨z, hz, hzo⟩ : ({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).Nonempty := by
      rw [← Set.encard_pos, pos_iff_ne_zero]
      intro h0
      exact ho (by simp only [h0, ENat.toENNReal_zero])
    have hzo' : o.out ∈ orbit Γ z := by
      apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hzo.symm
    show Quotient.mk (orbitRel Γ Y) (π o.out) = O
    rw [quotient_mk_map_eq_of_mem_orbit π hπ hzo', show π z = O.out from hz]
    exact Quotient.out_eq O
  rw [encard_eq_tsum_fibers (π ⁻¹' {O.out}) (Quotient.mk (orbitRel Γ L)),
    ← tsum_subtype_eq_of_support_subset hsupp, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun o => ?_
  have hx : Quotient.mk (orbitRel Γ Y) (π o.1.out) = Quotient.mk (orbitRel Γ Y) O.out := by
    rw [Quotient.out_eq O]
    exact o.2
  obtain ⟨h, hh⟩ : π o.1.out ∈ orbit Γ O.out := orbitRel_apply.mp (Quotient.exact hx)
  have hg : h⁻¹ • π o.1.out = O.out := by rw [← hh, inv_smul_smul]
  have hF : {z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o.1}
      = {z : L | π z = O.out ∧ z ∈ orbit Γ o.1.out} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    refine and_congr Iff.rfl ⟨fun hz => ?_, fun hz => ?_⟩
    · apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hz
    · rw [← Quotient.out_eq o.1]
      exact Quotient.sound (orbitRel_apply.mpr hz)
  have hmul := encard_fiber_orbit_mul_stabilizer π hπ o.1.out O.out h⁻¹ hg
  have hfinY : Finite (stabilizer Γ O.out) := hfin O.out ⟨h⁻¹ • o.1.out, by rw [hπ, hg]⟩
  have hY0 : (stabilizer Γ O.out : Set Γ).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.mp ⟨1, (stabilizer Γ O.out).one_mem⟩
  have hYt : (stabilizer Γ O.out : Set Γ).encard ≠ ⊤ := by
    rw [Ne, Set.encard_eq_top_iff, Set.not_infinite]
    exact Set.toFinite _
  rw [hF, ← hmul]
  rw [← hmul] at hY0 hYt
  exact (inv_coe_mul_mul_coe_eq_inv_coe _ _ hY0 hYt).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentIsometryDefiniteEqOne
section
open Matrix Finset Real

namespace GlobalTheory


open scoped ComplexOrder in
theorem unipotent_isometry_definite_eq_one :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), c ≠ 0 → Aᴴ * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * A = c • 1 → (A - 1) ^ m = 0 → A = 1 := by
  intro n m A c hc hA hm

  have hU : Aᴴ * A = 1 := by
    have h1 : c • (Aᴴ * A) = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    exact smul_right_injective _ hc h1
  have hU' : A * Aᴴ = 1 := mul_eq_one_comm.mp hU

  have hcomm : Commute (A - 1)ᴴ (A - 1) := by
    show (A - 1)ᴴ * (A - 1) = (A - 1) * (A - 1)ᴴ
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, hU, hU',
      one_mul, mul_one]
    abel
  have hN : (A - 1) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]

  have hBh : ((A - 1)ᴴ * (A - 1))ᴴ = (A - 1)ᴴ * (A - 1) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hB : ((A - 1)ᴴ * (A - 1)) ^ (m + 1) = 0 := by
    rw [hcomm.mul_pow, hN, mul_zero]
  have key : ∀ k : ℕ, ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 → (A - 1)ᴴ * (A - 1) = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro hk
      apply ih
      have h2 : (((A - 1)ᴴ * (A - 1)) ^ (k + 1))ᴴ * ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 := by
        rw [Matrix.conjTranspose_pow, hBh, ← pow_add,
          show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, hk, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp (key m hB))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
section
open Matrix

namespace GlobalTheory

theorem map_transpose_mul_rev {R : Type} [CommRing R] (s : R →+* R) {l m n : Type} [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    ((A * B).map s)ᵀ = (B.map s)ᵀ * (A.map s)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem unitary_stabiliser_orthogonal_summand :
    ∀ (R : Type) [CommRing R] (s : R →+* R) (N ι κ : Type) [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R) (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R), Q * Qi = 1 → Qi * Q = 1 → (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G' → IsUnit G'.det → (∀ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G → ((Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi).map s)ᵀ * J * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) = J) ∧ ∀ h : Matrix N N R, (h.map s)ᵀ * J * h = J → (∀ b : κ, h *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) → ∃ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G ∧ h = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi := by
  intro R _ s N ι κ _ _ _ _ _ _ J G G' Q Qi h1 h2 hD hG'
  have h1s : (Qi.map s)ᵀ * (Q.map s)ᵀ = 1 := by
    rw [← map_transpose_mul_rev, h1, Matrix.map_one _ (map_zero s) (map_one s), transpose_one]
  have hblk : ∀ (y : Matrix ι ι R) (c : Matrix κ ι R),
      ((Matrix.fromBlocks y 0 c (1 : Matrix κ κ R)).map s)ᵀ * Matrix.fromBlocks G 0 0 G' *
        Matrix.fromBlocks y 0 c (1 : Matrix κ κ R) =
      Matrix.fromBlocks ((y.map s)ᵀ * G * y + (c.map s)ᵀ * G' * c) ((c.map s)ᵀ * G') (G' * c) G' := by
    intro y c
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero s) (map_one s),
      Matrix.map_zero _ (map_zero s)]
    simp
  refine ⟨fun y hy => ?_, fun h hh hfix => ?_⟩
  · have hb := hblk y 0
    rw [hy] at hb
    simp only [Matrix.mul_zero, add_zero, Matrix.map_zero _ (map_zero s), transpose_zero,
      Matrix.zero_mul] at hb
    rw [map_transpose_mul_rev, map_transpose_mul_rev]
    calc _ = (Qi.map s)ᵀ * (((Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)).map s)ᵀ *
            ((Q.map s)ᵀ * J * Q) * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = (Qi.map s)ᵀ * ((Q.map s)ᵀ * J * Q) * Qi := by rw [hD, hb]
      _ = ((Qi.map s)ᵀ * (Q.map s)ᵀ) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1s, h1, Matrix.one_mul, Matrix.mul_one]
  · set M : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Qi * h * Q with hM
    have hQM : Q * M = h * Q := by
      rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hhM : h = Q * M * Qi := by
      rw [hQM, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcol : ∀ x b, M x (Sum.inr b) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) x (Sum.inr b) := by
      intro x b
      rw [← h2, hM, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact congrFun (hfix b) i
    have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1 := by
      ext x z
      rcases z with z | z
      · rcases x with x | x <;> rfl
      · rw [hcol]
        rcases x with x | x <;> simp [Matrix.one_apply]
    have hU : (M.map s)ᵀ * Matrix.fromBlocks G 0 0 G' * M = Matrix.fromBlocks G 0 0 G' := by
      rw [← hD]
      calc _ = ((Q * M).map s)ᵀ * J * (Q * M) := by
            rw [map_transpose_mul_rev s Q M]; simp only [Matrix.mul_assoc]
        _ = (Q.map s)ᵀ * ((h.map s)ᵀ * J * h) * Q := by
            rw [hQM, map_transpose_mul_rev]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hh]
    rw [hMb, hblk, Matrix.fromBlocks_inj] at hU
    obtain ⟨ha, -, hc, -⟩ := hU
    have hc0 : M.toBlocks₂₁ = 0 := by
      have := congrArg (G'⁻¹ * ·) hc
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG'] using this
    rw [hc0] at ha hMb
    refine ⟨M.toBlocks₁₁, by simpa using ha, ?_⟩
    rw [← hMb]
    exact hhM

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperUnitriangularMul
section
namespace GlobalTheory.UpperUnitriangularMul

open Matrix

theorem upperUnitriangular_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge c a with h | h
    · rw [hU a c h, zero_mul]
    · rw [hW c b (lt_of_lt_of_le hba h), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU1, hW1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hU a c h, zero_mul]
      · rw [hW c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UpperUnitriangularMul
end

