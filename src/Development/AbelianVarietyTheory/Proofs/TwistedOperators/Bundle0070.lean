module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSums
section
open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

open Formalism.UG

section DosetSwapProof

variable {G : Type} [Group G] {K : Subgroup G}

def dosetOf (K : Subgroup G) (x : G ⧸ K) : Set G :=
  DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)

theorem mem_dosetOf_iff {x y : G ⧸ K} :
    y.out ∈ DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G) ↔ dosetOf K y = dosetOf K x := by
  constructor
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h
  · intro h
    unfold dosetOf at h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K _

theorem exists_of_dosetOf_eq {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    ∃ a b : K, y.out = (a : G) * x.out * b := by
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 (mem_dosetOf_iff.2 h)
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩

theorem finite_dosetOf_fibre (hK : IsCommensurated K) (S : Set G) :
    Finite {x : G ⧸ K // dosetOf K x = S} := by
  by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
  · obtain ⟨x₀, rfl⟩ := h
    have hf := Formalism.UG.P.finite_cosets_in_doset hK x₀.out
    have hs : {x : G ⧸ K | dosetOf K x = dosetOf K x₀} ⊆ {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * x₀.out * b} :=
      fun y hy => exists_of_dosetOf_eq hy
    exact (hf.subset hs).to_subtype
  · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
    infer_instance

theorem biInv_of_dosetOf_eq {F : G → ℂ} (hF : IsBiInv K F) {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    F y.out = F x.out := by
  obtain ⟨a, b, e⟩ := exists_of_dosetOf_eq h
  rw [e, hF a b]

theorem hAct_dosetInd_eq (hK : IsCommensurated K) (x₀ : G ⧸ K) (v : G → ℂ) :
    hAct K (dosetInd ℂ K x₀.out) v 1 = ∑' y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, v y.1.out := by
  set s : Set (G ⧸ K) := {x | dosetOf K x = dosetOf K x₀} with hs
  have e : ∀ x : G ⧸ K, dosetInd ℂ K x₀.out x.out • v (1 * x.out) = s.indicator (fun x => v x.out) x := by
    intro x
    by_cases h : dosetOf K x = dosetOf K x₀
    · have h' := mem_dosetOf_iff.2 h
      have hx : x ∈ s := h
      simp [dosetInd, Set.indicator_of_mem h', Set.indicator_of_mem hx]
    · have h' : x.out ∉ DoubleCoset.doubleCoset x₀.out (K : Set G) (K : Set G) := fun h' => h (mem_dosetOf_iff.1 h')
      have hx : x ∉ s := h
      simp [dosetInd, Set.indicator_of_notMem h', Set.indicator_of_notMem hx]
  have hfin : s.Finite := Set.finite_coe_iff.1 (finite_dosetOf_fibre hK (dosetOf K x₀))
  rw [hAct, finsum_congr e, ← tsum_eq_finsum (L := SummationFilter.unconditional (G ⧸ K)) ((hfin.subset (Set.support_indicator_subset)))]
  rw [← tsum_subtype]
  rfl

end DosetSwapProof

theorem dosetSwap : DosetSwap := by
  intro G _ K hK F w φ Z hF hw hH hZ
  haveI : ∀ S : Set G, Finite {x : G ⧸ K // dosetOf K x = S} := finite_dosetOf_fibre hK
  let e := Equiv.sigmaFiberEquiv (dosetOf K)
  let f₁ : G ⧸ K → ℂ := fun x => F x.out * φ x.out
  let f₂ : G ⧸ K → ℂ := fun x => F x.out * w x.out
  have hs : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 =
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₁ y.1 := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, rfl⟩ := h
      have e₂ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₂ y.1 = F x₀.out * w y.1.out :=
        fun y => by simp only [f₂, biInv_of_dosetOf_eq hF y.2]
      have e₁ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₁ y.1 = F x₀.out * φ y.1.out :=
        fun y => by simp only [f₁, biInv_of_dosetOf_eq hF y.2]
      rw [tsum_congr e₂, tsum_congr e₁, tsum_mul_left, tsum_mul_left, ← hAct_dosetInd_eq hK,
        ← hAct_dosetInd_eq hK, hH]
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have hn : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ ≤
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₁ y.1‖ := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, hx₀⟩ := h
      have c : ∀ y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 = F x₀.out * w x₀.out := fun y => by
        have hy : dosetOf K y.1 = dosetOf K x₀ := y.2.trans hx₀.symm
        simp only [f₂, biInv_of_dosetOf_eq hF hy, biInv_of_dosetOf_eq hw hy]
      have key : ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ =
          ‖∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1‖ := by
        rw [tsum_congr (fun y => congrArg norm (c y)), tsum_congr c, tsum_const, tsum_const, nsmul_eq_mul,
          nsmul_eq_mul]
        simp [norm_mul]
      rw [key, hs]
      exact norm_tsum_le_tsum_norm Summable.of_finite
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have h₁ : HasSum (f₁ ∘ e) Z := (e.hasSum_iff).2 hZ
  have h₁n : Summable fun p => ‖(f₁ ∘ e) p‖ := summable_norm_iff.2 h₁.summable
  have h₂n : Summable fun p => ‖(f₂ ∘ e) p‖ := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)] at h₁n ⊢
    refine ⟨fun S => Summable.of_finite, ?_⟩
    exact h₁n.2.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) hn
  have h₂ : Summable (f₂ ∘ e) := summable_norm_iff.1 h₂n
  have A := h₂.hasSum.sigma (fun S => (Summable.of_finite).hasSum)
  have B := h₁.sigma (fun S => (Summable.of_finite).hasSum)
  have hZ' : ∑' p, (f₂ ∘ e) p = Z := by
    refine A.unique ?_
    have : (fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₂ ∘ e) ⟨S, c⟩) =
        fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₁ ∘ e) ⟨S, c⟩ := funext hs
    rw [this]
    exact B
  have := h₂.hasSum
  rw [hZ', e.hasSum_iff] at this
  exact this

end GlobalTheory.InertZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl

namespace GlobalTheory.FrameCompletion

section Basic

variable {L : Type} [Field L] {σ : L →+* L}

theorem conjT_add {m p : Type} (A B : Matrix m p L) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j; simp [cT]

theorem conjT_sub {m p : Type} (A B : Matrix m p L) : cT σ (A - B) = cT σ A - cT σ B := by
  ext i j; simp [cT]

theorem conjT_neg {m p : Type} (A : Matrix m p L) : cT σ (-A) = -cT σ A := by
  ext i j; simp [cT]

theorem conjT_smul {m p : Type} (c : L) (A : Matrix m p L) : cT σ (c • A) = σ c • cT σ A := by
  ext i j; simp [cT]

theorem conjT_zero {m p : Type} : cT σ (0 : Matrix m p L) = 0 := by
  ext i j; simp [cT]

theorem conjT_conjT (hσσ : ∀ x, σ (σ x) = x) {m p : Type} (A : Matrix m p L) : cT σ (cT σ A) = A := by
  ext i j; simp [cT, hσσ]

theorem conjT_fromRows {m m' p : Type} (A : Matrix m p L) (B : Matrix m' p L) :
    cT σ (fromRows A B) = fromCols (cT σ A) (cT σ B) := by
  ext i (j | j) <;> simp [cT]

theorem conjT_fromCols {m p p' : Type} (A : Matrix m p L) (B : Matrix m p' L) :
    cT σ (fromCols A B) = fromRows (cT σ A) (cT σ B) := by
  ext (i | i) j <;> simp [cT]

theorem conjT_fromBlocks {m m' p p' : Type} (A : Matrix m p L) (B : Matrix m p' L) (C : Matrix m' p L)
    (D : Matrix m' p' L) : cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  ext (i | i) (j | j) <;> simp [cT]

theorem conjT_antiJ {n : ℕ} : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, antiJ, Matrix.transpose_apply, Matrix.map_apply]
  rw [add_comm j.val i.val]
  split_ifs <;> simp

theorem antiJ_mul_antiJ_mul [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {p : Type} (X : Matrix (Fin n) p L) : antiJ L n * (antiJ L n * X) = X := by
  rw [← Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]

def gramQ (L : Type) [Field L] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L :=
  fromBlocks (antiJ L n) 0 0 (-antiJ L n)

theorem conjT_gramQ {n : ℕ} : cT σ (gramQ L n) = gramQ L n := by
  rw [gramQ, conjT_fromBlocks, conjT_antiJ, conjT_zero, conjT_neg, conjT_antiJ]

theorem pair_symm (hσσ : ∀ x, σ (σ x) = x) {n : ℕ} {κ μ : Type} (X : Matrix (Fin n ⊕ Fin n) κ L)
    (X' : Matrix (Fin n ⊕ Fin n) μ L) : cT σ (cT σ X * gramQ L n * X') = cT σ X' * gramQ L n * X := by
  simp only [cT_mul, conjT_conjT hσσ, conjT_gramQ, Matrix.mul_assoc]

theorem pair_fromRows {n : ℕ} {κ μ : Type} (C D : Matrix (Fin n) κ L) (C' D' : Matrix (Fin n) μ L) :
    cT σ (fromRows C D) * gramQ L n * fromRows C' D' =
      cT σ C * antiJ L n * C' - cT σ D * antiJ L n * D' := by
  rw [conjT_fromRows, gramQ, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]

theorem pair_comb {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (s t s' t' : L) :
    cT σ (s • X + t • W) * Q * (s' • X + t' • W) =
      (σ s * s') • (cT σ X * Q * X) + (σ s * t') • (cT σ X * Q * W) + (σ t * s') • (cT σ W * Q * X) +
        (σ t * t') • (cT σ W * Q * W) := by
  simp only [conjT_add, conjT_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module

theorem pair_sub {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (M : Matrix κ κ L)
    (c : L) : cT σ (X - c • (W * M)) * Q * (X - c • (W * M)) =
      cT σ X * Q * X - c • (cT σ X * Q * W * M) - σ c • (cT σ M * (cT σ W * Q * X)) +
        (σ c * c) • (cT σ M * (cT σ W * Q * W) * M) := by
  simp only [conjT_sub, conjT_smul, cT_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module

end Basic

section Int

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem isInt_smul {ι κ : Type} {c : L} {M : Matrix ι κ L} (hc : c ∈ intL L) (hM : IsInt M) : IsInt (c • M) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

theorem isInt_neg {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) : IsInt (-M) := fun i j => neg_mem (hM i j)

theorem isInt_sub {ι κ : Type} {M N : Matrix ι κ L} (hM : IsInt M) (hN : IsInt N) : IsInt (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem isInt_conjT (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) :
    IsInt (cT σ M) := fun i j => by
  show Valued.v (σ (M j i)) ≤ 1
  rw [hσ]
  exact hM j i

theorem isInt_fromRows {ι ι' κ : Type} {A : Matrix ι κ L} {B : Matrix ι' κ L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromRows A B) := by
  rintro (i | i) j
  exacts [hA i j, hB i j]

theorem isInt_fromCols {ι κ κ' : Type} {A : Matrix ι κ L} {B : Matrix ι κ' L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromCols A B) := by
  rintro i (j | j)
  exacts [hA i j, hB i j]

theorem isInt_submatrix {ι κ ι' κ' : Type} {M : Matrix ι κ L} (hM : IsInt M) (f : ι' → ι) (g : κ' → κ) :
    IsInt (M.submatrix f g) := fun i j => hM (f i) (g j)

theorem isInt_antiJ {n : ℕ} : IsInt (antiJ L n) := fun i j => by
  unfold antiJ
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem isInt_gramQ {n : ℕ} : IsInt (gramQ L n) := by
  rintro (i | i) (j | j)
  · exact isInt_antiJ i j
  · exact zero_mem _
  · exact zero_mem _
  · exact isInt_neg isInt_antiJ i j

end Int

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem exists_frame (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) (g U V C : Matrix (Fin n) (Fin n) L) (hg : cT σ g * antiJ L n * g = antiJ L n)
    (hUi : IsInt U) (hVi : IsInt V) (hCi : IsInt C) (hDi : IsInt (g * C)) (h5 : (U + V * g) * C = 1) :
    ∃ K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt K ∧ cT σ K * gramQ L n * K = gramQ L n ∧
      ∀ x : Fin n → L, K *ᵥ Sum.elim x x = Sum.elim (C *ᵥ x) ((g * C) *ᵥ x) := by
  set Q := gramQ L n with hQ
  set Y : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows C (g * C) with hY
  set Z : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows (antiJ L n * cT σ U * antiJ L n) (-(antiJ L n * cT σ V * antiJ L n)) with hZ
  have hYY : cT σ Y * Q * Y = 0 := by
    rw [hY, hQ, pair_fromRows, cT_mul,
      show cT σ C * cT σ g * antiJ L n * (g * C) = cT σ C * (cT σ g * antiJ L n * g) * C by simp only [Matrix.mul_assoc], hg, sub_self]
  have hUC : cT σ C * cT σ U + cT σ (g * C) * cT σ V = 1 := by
    rw [← cT_mul, ← cT_mul, ← conjT_add, ← Matrix.mul_assoc V, ← Matrix.add_mul, h5, cT_one]
  have hYZ : cT σ Y * Q * Z = antiJ L n := by
    rw [hY, hZ, hQ, pair_fromRows]
    calc _ = (cT σ C * cT σ U + cT σ (g * C) * cT σ V) * antiJ L n := by
          simp only [Matrix.mul_neg, sub_neg_eq_add, Matrix.add_mul, Matrix.mul_assoc, antiJ_mul_antiJ_mul]
      _ = antiJ L n := by rw [hUC, Matrix.one_mul]
  have hZY : cT σ Z * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ, conjT_antiJ]
  set H := cT σ Z * Q * Z with hH
  have hHH : cT σ H = H := pair_symm hσσ Z Z
  set Z' := Z - τ • (Y * (antiJ L n * H)) with hZ'
  have hYZ' : cT σ Y * Q * Z' = antiJ L n := by
    rw [hZ', Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hYY, Matrix.zero_mul, smul_zero, sub_zero, hYZ]
  have hZ'Y : cT σ Z' * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ', conjT_antiJ]
  have hZ'Z' : cT σ Z' * Q * Z' = 0 := by
    rw [hZ', pair_sub, hYY, hZY, hYZ, ← hH, cT_mul, hHH, conjT_antiJ, antiJ_mul_antiJ_mul, Matrix.mul_zero,
      Matrix.zero_mul, smul_zero, add_zero, Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.mul_one,
      sub_sub, ← add_smul, hτ1, one_smul, sub_self]
  set a := τ • Y + (1 : L) • Z' with ha
  set b := σ τ • Y + (-1 : L) • Z' with hb
  have hInt : IsInt Y ∧ IsInt Z' := by
    have hYi : IsInt Y := isInt_fromRows hCi hDi
    refine ⟨hYi, isInt_sub (isInt_fromRows ?_ ?_) (isInt_smul hτ (hYi.mul (isInt_antiJ.mul ?_)))⟩
    · exact (isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ
    · exact isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ)
    · have hZi : IsInt Z := isInt_fromRows ((isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ)
        (isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ))
      exact ((isInt_conjT hσ hZi).mul isInt_gramQ).mul hZi
  have hστ : σ τ ∈ intL L := by
    show Valued.v (σ τ) ≤ 1
    rw [hσ]
    exact hτ
  refine ⟨fromCols a b, isInt_fromCols ?_ ?_, ?_, fun x => ?_⟩
  · exact (isInt_smul hτ hInt.1).add (isInt_smul (one_mem _) hInt.2)
  · exact (isInt_smul hστ hInt.1).add (isInt_smul (neg_mem (one_mem _)) hInt.2)
  · rw [conjT_fromCols, fromRows_mul, fromRows_mul_fromCols, ha, hb, pair_comb, pair_comb, pair_comb, pair_comb,
      hYY, hYZ', hZ'Y, hZ'Z', hQ, gramQ]
    simp only [smul_zero, add_zero, zero_add, map_one, map_neg, hσσ, mul_one, one_mul, mul_neg, neg_mul, neg_smul,
      neg_neg]
    rw [← add_smul, add_comm (σ τ), hτ1, one_smul, neg_add_cancel, add_neg_cancel, ← neg_add, ← add_smul, hτ1, one_smul]
  · rw [fromCols_mulVec_sumElim, ← Matrix.add_mulVec, ha, hb,
      show τ • Y + (1 : L) • Z' + (σ τ • Y + (-1 : L) • Z') = (τ + σ τ) • Y by module, hτ1, one_smul, hY,
      fromRows_mulVec]

end Main

theorem completion : Completion := by
  intro L _ _ ϖ σ q n hU g U V C hf
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  obtain ⟨hUi, hVi, hCi, hDi, h5⟩ := hf
  obtain ⟨K, hKi, hKQ, hKx⟩ := exists_frame hU.1 hU.2.1 hτ hτ1 (mat g) U V C g.2 hUi hVi hCi hDi h5
  set e := finSumFinEquiv (m := n) (n := n) with he
  set k := K.submatrix e.symm e.symm with hk
  have hQs : GlobalTheory.Doubling.dblGram e (antiJ L n) = (gramQ L n).submatrix e.symm e.symm := rfl
  have hkQ : cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = GlobalTheory.Doubling.dblGram e (antiJ L n) := by
    rw [hQs, hk, show cT σ (K.submatrix e.symm e.symm) = (cT σ K).submatrix e.symm e.symm from rfl,
      submatrix_mul_equiv, submatrix_mul_equiv, hKQ]
  have hQQ : GlobalTheory.Doubling.dblGram e (antiJ L n) * GlobalTheory.Doubling.dblGram e (antiJ L n) = 1 := by
    rw [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat_mul, neg_mul_neg, GlobalTheory.UnitarySwap.antiJ_mul_self,
      GlobalTheory.Doubling.blkMat_one]
  have hinv : GlobalTheory.Doubling.dblGram e (antiJ L n) * cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ k), hkQ, hQQ]
  have hQi : IsInt (GlobalTheory.Doubling.dblGram e (antiJ L n)) := by
    rw [hQs]
    exact isInt_submatrix isInt_gramQ _ _
  have hki : IsInt k := isInt_submatrix hKi _ _
  obtain ⟨W, hW, hWk⟩ := P.cartan_exists_glint (intL L) k _ (mul_eq_one_comm.1 hinv) hki
    ((hQi.mul (isInt_conjT hU.2.1 hki)).mul hQi)
  refine ⟨W, ?_, hW, fun x => ?_⟩
  · show cT σ (W : Matrix (Fin (n + n)) (Fin (n + n)) L) * _ * (W : Matrix (Fin (n + n)) (Fin (n + n)) L) = _
    rw [hWk, hkQ]
  · rw [hWk, hk, GlobalTheory.Doubling.pairVec, GlobalTheory.Doubling.pairVec, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id, hKx]

end GlobalTheory.FrameCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSum
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.DualLat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

def tw (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)

def IntT (t : L) (x : Fin N → L) : Prop := ∀ i, t * x i ∈ intL L

theorem IntT.add {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x + y) := fun i => by
  simp only [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)

theorem IntT.neg {t : L} {x : Fin N → L} (hx : IntT t x) : IntT t (-x) := fun i => by
  simp only [Pi.neg_apply, mul_neg]; exact neg_mem (hx i)

theorem IntT.sub {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IntT.mulVec {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hM : IsInt M) (hx : IntT t x) :
    IntT t (M *ᵥ x) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [mul_left_comm]; exact mul_mem (hM i k) (hx k)

theorem IntT.vecMul {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hx : IntT t x) (hM : IsInt M) :
    IntT t (x ᵥ* M) := fun j => by
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [← mul_assoc]; exact mul_mem (hx k) (hM k j)

theorem IntT.twist {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {t : L} {x : Fin N → L} (hx : IntT t x) :
    IntT t (tw σ x) := fun j => by
  show Valued.v (t * σ (x j.rev)) ≤ 1
  rw [map_mul, hσ, ← map_mul]; exact hx j.rev

theorem tw_tw {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x : Fin N → L) : tw σ (tw σ x) = x := by
  ext j; simp [tw, hσσ]

theorem tw_add (σ : L →+* L) (x y : Fin N → L) : tw σ (x + y) = tw σ x + tw σ y := by
  ext j; simp [tw]

theorem tw_neg (σ : L →+* L) (x : Fin N → L) : tw σ (-x) = -tw σ x := by
  ext j; simp [tw]

theorem tw_vecMul {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (g : GU σ N) (x : Fin N → L) :
    tw σ x ᵥ* mat g = tw σ (mat g⁻¹ *ᵥ x) := by
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tw, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mat_inv_apply, hσσ, Fin.rev_rev]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
  simp [mul_comm]

end GlobalTheory.InertZeta.DualLat

namespace GlobalTheory.InertZeta

open DualLat

theorem dual_inter_eq_sum : Dual := by
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσ, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hgC, e⟩ := hF
  have e' : C * (U + V * mat g) = 1 := mul_eq_one_comm.1 e
  have hr' : r = -tw σ b := by ext j; simp [tw, hr]
  have m1 : C * V * mat g = 1 - C * U := by
    rw [Matrix.mul_assoc, ← e', Matrix.mul_add]; abel
  have m2 : C * V * mat g * mat g⁻¹ = C * V := by rw [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
  have hCU : C * U = 1 - C * V * mat g := by rw [m1]; abel
  have m3 : mat g * C * U * mat g⁻¹ = 1 - mat g * C * V := by
    rw [Matrix.mul_assoc (mat g) C U, hCU]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, mat_mul_inv]
  change IntT t (r ᵥ* C) ↔ IntT t ((C * V * mat g) *ᵥ b) ∧ IntT t ((mat g * C * U) *ᵥ b)
  constructor
  · intro hρ
    have h1 : r = (r ᵥ* C) ᵥ* U + ((r ᵥ* C) ᵥ* V) ᵥ* mat g := by
      rw [Matrix.vecMul_vecMul (r ᵥ* C) V, ← Matrix.vecMul_add, Matrix.vecMul_vecMul, e', Matrix.vecMul_one]
    have hl₁ : IntT t (-tw σ ((r ᵥ* C) ᵥ* U)) := ((hρ.vecMul hUi).twist hσ).neg
    have hl₂ : IntT t (-tw σ ((r ᵥ* C) ᵥ* V)) := ((hρ.vecMul hVi).twist hσ).neg
    have htw : tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)) = -r := by
      rw [tw_add, ← tw_vecMul hσσ, tw_neg, tw_neg, tw_tw hσσ, tw_tw hσσ, Matrix.neg_vecMul]
      conv_rhs => rw [h1]
      abel
    have hb : b = -tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V) := by
      calc b = tw σ (tw σ b) := (tw_tw hσσ b).symm
        _ = tw σ (tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V))) := by
          rw [htw, hr', neg_neg]
        _ = _ := tw_tw hσσ _
    rw [hb]
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m2, m1, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (hl₁.sub (IntT.mulVec (hCi.mul hUi) hl₁)).add (IntT.mulVec (hCi.mul hVi) hl₂)
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m3, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (IntT.mulVec (hgC.mul hUi) hl₁).add (hl₂.sub (IntT.mulVec (hgC.mul hVi) hl₂))
  · rintro ⟨h1, h2⟩
    have hb : b = (C * V * mat g) *ᵥ b + (C * U) *ᵥ b := by
      rw [← Matrix.add_mulVec, m1, sub_add_cancel, Matrix.one_mulVec]
    have key : ∀ b₁ b₂ : Fin N → L,
        -tw σ (b₁ + b₂) ᵥ* C = -(tw σ b₁ ᵥ* C) - tw σ (mat g *ᵥ b₂) ᵥ* (mat g * C) := by
      intro b₁ b₂
      rw [← Matrix.vecMul_vecMul, tw_vecMul hσσ, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, tw_add,
        Matrix.neg_vecMul, Matrix.add_vecMul]
      abel
    have h2' : IntT t (mat g *ᵥ ((C * U) *ᵥ b)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]; exact h2
    rw [hr', hb, key]
    exact ((h1.twist hσ).vecMul hCi).neg.sub ((h2'.twist hσ).vecMul hgC)

end GlobalTheory.InertZeta

end
end

