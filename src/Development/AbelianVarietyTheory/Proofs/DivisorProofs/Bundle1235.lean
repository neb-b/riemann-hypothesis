module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

noncomputable section

namespace GlobalTheory.VacLn.TrNondeg

theorem trace_pi' {R : Type} [Field R] {ι : Type} [Fintype ι]
    {E : ι → Type} [∀ c, CommRing (E c)] [∀ c, Algebra R (E c)] [∀ c, Module.Finite R (E c)]
    (x : ∀ c, E c) : Algebra.trace R (∀ c, E c) x = ∑ c, Algebra.trace R (E c) (x c) := by
  classical
  let b : ∀ c, Module.Basis (Fin (Module.finrank R (E c))) R (E c) := fun c => Module.finBasis R (E c)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b c), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]

def conjM {F : Type} [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    mixedEmbedding.mixedSpace F :=
  (z.1, fun w => starRingEnd ℂ (z.2 w))

theorem trace_conjM_mul {F : Type} [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (conjM z * z) =
      ∑ w, z.1 w ^ 2 + ∑ w, 2 * Complex.normSq (z.2 w) := by
  rw [Algebra.trace_prod_apply, trace_pi', trace_pi']
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [conjM, Algebra.trace_self_apply, sq]
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [conjM, Algebra.trace_complex_apply, Complex.normSq_apply, Complex.mul_re]

theorem eq_zero_of_trace_conjM_mul {F : Type} [Field F] [NumberField F]
    (z : mixedEmbedding.mixedSpace F)
    (h : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (conjM z * z) = 0) : z = 0 := by
  rw [trace_conjM_mul] at h
  have h1 : 0 ≤ ∑ w, z.1 w ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (z.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => sq_nonneg (z.1 w)).1 (by linarith)
  have e2 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
    mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Complex.normSq_nonneg (z.2 w))).1 (by linarith)
  ext w
  · simpa using e1 w (Finset.mem_univ _)
  · have := e2 w (Finset.mem_univ _)
    have : Complex.normSq (z.2 w) = 0 := by linarith
    simpa using Complex.normSq_eq_zero.1 this

end GlobalTheory.VacLn.TrNondeg

namespace GlobalTheory.VacLn

theorem trPair_nondeg : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F),
    (∀ x, trPair F κ x y = 0) → y = 0 := by
  intro F _ _ κ _ y h
  have h0 := h (fun i => TrNondeg.conjM (y i))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [trPair_apply, map_sum] at h0
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (TrNondeg.conjM (y i) * y i) := by
    intro i
    rw [TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h0
  funext i
  exact TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

end GlobalTheory.VacLn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrix
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def rowOpMat (i₀ : A) (w : A → k) : Matrix A A k :=
  replicateCol Unit (Pi.single i₀ (1 : k)) * replicateRow Unit w

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowOpMat_apply (i₀ : A) (w : A → k) (i a : A) : rowOpMat i₀ w i a = if i = i₀ then w a else 0 := by
  by_cases h : i = i₀
  · subst h; simp [rowOpMat, Matrix.mul_apply]
  · simp [rowOpMat, Matrix.mul_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowOpMat_mul_self (i₀ : A) (w : A → k) (hw : w i₀ = 0) : rowOpMat i₀ w * rowOpMat i₀ w = 0 := by
  ext i j
  simp [Matrix.mul_apply, rowOpMat_apply, hw]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in
theorem rowOpMat_mul_apply (i₀ : A) (w : A → k) (X : Matrix A D k) (i : A) (j : D) :
    (rowOpMat i₀ w * X) i j = if i = i₀ then ∑ a, w a * X a j else 0 := by
  by_cases h : i = i₀
  · simp [Matrix.mul_apply, rowOpMat_apply, h]
  · simp [Matrix.mul_apply, rowOpMat_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_one_add_rowOpMat (i₀ : A) (w : A → k) (hw : w i₀ = 0) : (1 + rowOpMat i₀ w).det = 1 := by
  rw [rowOpMat, det_one_add_replicateCol_mul_replicateRow]
  simp [hw]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : GL A k :=
  ⟨1 + rowOpMat i₀ w, 1 - rowOpMat i₀ w,
    by simp [add_mul, mul_sub, rowOpMat_mul_self i₀ w hw],
    by simp [sub_mul, mul_add, rowOpMat_mul_self i₀ w hw]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gdet_unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : gdet (unipRowGL i₀ w hw) = 1 :=
  Units.ext (det_one_add_rowOpMat i₀ w hw)

theorem valuation_rowSum_le (i₀ : A) (w : A → k) (hw0 : w i₀ = 0) (hw : ∀ a, valuation k (w a) ≤ 1)
    (Z : A → k) (b : ValueGroupWithZero k) (hZ : ∀ a, a ≠ i₀ → valuation k (Z a) ≤ b) :
    valuation k (∑ a, w a * Z a) ≤ b := by
  refine Valuation.map_sum_le _ fun a _ => ?_
  by_cases ha : a = i₀
  · subst ha; simp [hw0]
  · rw [map_mul]
    exact (mul_le_mul' (hw a) (hZ a ha)).trans (by rw [one_mul])

theorem omA_unipRowGL_boxFn (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (i₀ : A) (w : A → k) (hw0 : w i₀ = 0)
    (hw : ∀ a, valuation k (w a) ≤ 1) (C : Matrix A D k) (m : ℕ) :
    omA ν β (unipRowGL i₀ w hw0) 1 (boxFn ϖ C (fun _ => m)) =
      boxFn ϖ (updateRow C i₀ (C i₀ + w ᵥ* C)) (fun _ => m) := by
  funext X
  rw [omA_one_apply, gdet_unipRowGL]
  simp only [map_one, inv_one, Units.val_one, apow_one, one_mul]
  have hinv : ((unipRowGL i₀ w hw0)⁻¹).val = 1 - rowOpMat i₀ w := rfl
  rw [hinv]
  set C' := updateRow C i₀ (C i₀ + w ᵥ* C)
  have hT : ∀ i j, ((1 - rowOpMat i₀ w : Matrix A A k) * X : Matrix A D k) i j - C i j =
      (X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) := by
    intro i j
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, rowOpMat_mul_apply]
    by_cases hi : i = i₀
    · subst hi
      simp only [C', updateRow_self, if_true, Pi.add_apply, vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    · simp [C', hi]
  have hrow : ∀ a, a ≠ i₀ → ∀ j, X a j - C' a j = X a j - C a j := fun a ha j => by simp [C', ha]
  have hbox : (1 - rowOpMat i₀ w) * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ C' (fun _ => m) := by
    simp only [box, Set.mem_setOf_eq]
    constructor
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hT, if_neg ha, sub_zero, hrow a ha] at this
      have := h i j
      rw [hT] at this
      rw [show X i j - C' i j = ((X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0)) +
        (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) by ring]
      refine Valuation.map_add_le _ this ?_
      split_ifs
      · exact hS
      · simp
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hrow a ha] at this
      rw [hT]
      refine Valuation.map_sub_le _ (h i j) ?_
      split_ifs
      · exact hS
      · simp
  unfold boxFn
  by_cases hX : X ∈ box ϖ C' (fun _ => m)
  · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (hbox.2 hX)]; rfl
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX (hbox.1 h))]
end GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (t : Fin r → k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → (∀ l, valuation k (t l) ≤ valuation k ((ϖ ^ c : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ (C i₀ + t ᵥ* (H * C))) (fun _ => m) - GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ r c m C H t hH0 hH ht
  have hw0 : (t ᵥ* H) i₀ = 0 := by simp [vecMul, dotProduct, hH0]
  have hw : ∀ a, valuation k ((t ᵥ* H) a) ≤ 1 := fun a => by
    show valuation k (∑ l, t l * H l a) ≤ 1
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    refine (mul_le_mul' (ht l) (hH l a)).trans (le_of_eq ?_)
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← vecMul_vecMul, ← GlobalTheory.RankCoinv.omA_unipRowGL_boxFn ν β ϖ i₀ (t ᵥ* H) hw0 hw C m]
  exact GlobalTheory.RankCoinv.sub_mem_twistSpan ν β _ (GlobalTheory.RankCoinv.boxFn_mem_SB ϖ C _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionDiagonalAction
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem omA_diag_boxFn_succ :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ C hC m n
  have hdet : GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ)) = ϖ := by
    rw [GlobalTheory.SplitFlip.gdet, GlobalTheory.SplitFlip.det_diagGL, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hinv : ((GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ))⁻¹).val =
      diagonal fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k) := rfl
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have key : ∀ X : Matrix A D k,
      (diagonal (fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k)) * X) ∈
        box ϖ C (Function.update (fun _ => m) i₀ n) ↔ X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
    intro X
    simp only [box, Set.mem_setOf_eq, diagonal_mul]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self, hC, sub_zero, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        pow_succ, Units.val_mul, map_mul, map_inv₀, map_pow]
      rw [inv_mul_le_iff₀ h0, mul_comm (valuation k (ϖ : k))]
    · simp [Function.update_of_ne hi]
  funext X
  rw [GlobalTheory.RankCoinv.omA_one_apply, hdet, Pi.smul_apply, smul_eq_mul, hinv]
  congr 1
  unfold boxFn
  by_cases hX : X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1))
  · rw [Set.indicator_of_mem ((key X).2 hX), Set.indicator_of_mem hX]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hX ((key X).1 h)), Set.indicator_of_notMem hX]

end GlobalTheory.RankCoinv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMaps
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def leftInv : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g}
  zero_mem' _ _ := rfl
  add_mem' {ψ ψ'} h h' γ g := by simp [h γ g, h' γ g]
  smul_mem' c ψ h γ g := by simp [h γ g]

theorem lie_mem_leftInv (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ leftInv E a) : lie E a X ψ ∈ leftInv E a := by
  intro γ g
  have e : chart ψ.1 (ratGL E a γ * g) = chart ψ.1 g := by
    funext x
    simp only [chart, mul_assoc]
    split_ifs
    · exact h γ _
    · rfl
  simp only [lie_apply, lieD, e]


variable (E a) in
def fixL (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ k ∈ L, finRep E a k ψ = ψ}
  zero_mem' k _ := map_zero _
  add_mem' {ψ ψ'} h h' k hk := by rw [map_add (f := _), h k hk, h' k hk]
  smul_mem' c ψ h k hk := by rw [map_smul, h k hk]

theorem lie_mem_fixL (L : Subgroup (GL (Fin a) (Af E))) (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ fixL E a L) :
    lie E a X ψ ∈ fixL E a L := by
  intro k hk
  have e := LinearMap.congr_fun (lie_rt_fin X k) ψ
  simp only [Module.End.mul_apply] at e
  change rt E a (finGL E a k) (lie E a X ψ) = lie E a X ψ
  rw [← e]
  exact congrArg (lie E a X) (h k hk)

theorem comp_mem_maps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W)
    (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  intro E _ _ _ a L W hW T hT z hz
  refine ⟨fun k w => ?_, fun w => ⟨?_, ?_, ?_⟩⟩
  · simp only [LinearMap.comp_apply, hT.1 k w]
    exact (LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E a k z hz) (T w))
  · exact Zalg_stable (V := tame E a) (fun X _ h => lie_mem_tame X h) hz _ (hT.2 w).1
  · exact Zalg_stable (V := leftInv E a) (fun X _ h => lie_mem_leftInv X h) hz _ (hT.2 w).2.1
  · exact Zalg_stable (V := fixL E a L) (fun X _ h => lie_mem_fixL L X h) hz _ (hT.2 w).2.2

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderiv
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polEval_pderiv :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  intro V _ _ ι _ m d hm f₀ hc h0 i p
  have hX : ∀ (j : ι) (q : MvPolynomial ι ℂ),
      polEval m hm f₀ (MvPolynomial.X j * q) = m j (polEval m hm f₀ q) := by
    intro j q
    simp [polEval, Module.End.mul_apply]
  have h1 : polEval m hm f₀ 1 = f₀ := by simp [polEval]
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : (MvPolynomial.C a : MvPolynomial ι ℂ) = a • (1 : MvPolynomial ι ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [MvPolynomial.pderiv_C, map_zero, hC, map_smul, h1, map_smul, h0, smul_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X q j hq =>
    have hv := LinearMap.congr_fun (hc i j) (polEval m hm f₀ q)
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at hv
    rw [mul_comm q, MvPolynomial.pderiv_mul, map_add (f := _), hX, hX, hq, hv]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
      simp [hij]

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifyStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HilbertSamuel.Data

theorem complexify_statement : Complexify := by
  intro F _ _ X β hF _ hS hB
  haveI := hF
  exact ⟨fun σ => hB.mulBoundAt σ, fun E _ _ _ => hS.baseChange E⟩

end GlobalTheory.HilbertSamuel.Data
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOne
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem coneChain_step_bounds {a : ℕ} {t ρ K : ℝ} (ht : 0 < t) (hKt : t⁻¹ ≤ K) (hK0 : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (hup : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hdown : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ k : ℕ, ∀ i j : Fin a, (j : ℕ) = i + k → r j ≤ K ^ k * r i ∧ r i ≤ ρ ^ k * r j := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hji : j = i := Fin.ext (by simpa using hij)
    subst hji
    simp
  | succ k ih =>
    intro i j hij
    have hja := j.isLt
    have hk : (i : ℕ) + k < a := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hk⟩ rfl
    have hmj : (j : ℕ) = ((⟨(i : ℕ) + k, hk⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have hu := hup _ j hmj
    have hd := hdown _ j hmj
    set m : Fin a := ⟨(i : ℕ) + k, hk⟩
    have hrj : r j ≤ t⁻¹ * r m := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    constructor
    · calc r j ≤ t⁻¹ * r m := hrj
        _ ≤ K * r m := mul_le_mul_of_nonneg_right hKt (hr m).le
        _ ≤ K * (K ^ k * r i) := mul_le_mul_of_nonneg_left h1.1 hK0
        _ = K ^ (k + 1) * r i := by ring
    · calc r i ≤ ρ ^ k * r m := h1.2
        _ ≤ ρ ^ k * (ρ * r j) := mul_le_mul_of_nonneg_left hd (pow_nonneg hρ0 _)
        _ = ρ ^ (k + 1) * r j := by ring

theorem coneCoord_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  intro a t ht
  obtain ⟨K, hK1, hKt⟩ : ∃ K : ℝ, 1 ≤ K ∧ t⁻¹ ≤ K := ⟨max 1 t⁻¹, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K ^ a, one_le_pow₀ hK1, ?_⟩
  intro r ρ hr hup hprod hρ hdown i
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have hC0 : 0 ≤ K ^ a * ρ ^ a := mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hρ0 _)
  have step := coneChain_step_bounds ht hKt hK0 hρ0 r hr hup hdown
  have pair : ∀ p q : Fin a, r p ≤ K ^ a * ρ ^ a * r q := by
    intro p q
    rcases le_total (q : ℕ) p with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := p.isLt; omega
      calc r p ≤ K ^ k * r q := (step k q p hk).1
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc K ^ k ≤ K ^ a := pow_le_pow_right₀ hK1 hka
            _ = K ^ a * 1 := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_left (one_le_pow₀ hρ) (pow_nonneg hK0 _)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := q.isLt; omega
      calc r p ≤ ρ ^ k * r q := (step k p q hk).2
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc ρ ^ k ≤ ρ ^ a := pow_le_pow_right₀ hρ hka
            _ = 1 * ρ ^ a := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_right (one_le_pow₀ hK1) (pow_nonneg hρ0 _)
  have hne : (Finset.univ : Finset (Fin a)).Nonempty := ⟨i, Finset.mem_univ _⟩
  have ex_le : ∃ j, r j ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (f := fun _ => (1 : ℝ)) (g := r)
      (fun _ _ => one_pos) (fun j _ => hcon j) hne
    simp [hprod] at this
  have ex_ge : ∃ j, 1 ≤ r j := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (f := r) (g := fun _ => (1 : ℝ))
      (fun j _ => hr j) (fun j _ => hcon j) hne
    simp [hprod] at this
  obtain ⟨j, hj⟩ := ex_le
  obtain ⟨l, hl⟩ := ex_ge
  constructor
  · calc r i ≤ K ^ a * ρ ^ a * r j := pair i j
      _ ≤ K ^ a * ρ ^ a * 1 := mul_le_mul_of_nonneg_left hj hC0
      _ = K ^ a * ρ ^ a := by ring
  · rw [inv_eq_one_div, div_le_iff₀ (hr i)]
    have := pair l i
    linarith

end GlobalTheory
end

