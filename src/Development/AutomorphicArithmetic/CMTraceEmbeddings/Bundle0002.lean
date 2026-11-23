module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0005
public import Development.AutomorphicArithmetic.CMTraceEmbeddings.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorMatrixBijectiveCmType
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private noncomputable def entL {E : Type} [Field E] [NumberField E] {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) E →ₗ[ℚ] E where
  toFun x := x i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def sgL {E : Type} [Field E] [NumberField E] {n : ℕ} (i j : Fin n) :
    E →ₗ[ℚ] Matrix (Fin n) (Fin n) E where
  toFun x := Matrix.single i j x
  map_add' a b := by simp [Matrix.single_add]
  map_smul' q a := by simp [Matrix.smul_single]

private theorem evaluation_baseChange_entry {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* ℂ) (i j : Fin n)
    (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    ev1 σ ((entL i j).baseChange ℝ z) = evM σ z i j := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]
    change r • σ (x i j) = _
    simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Matrix.add_apply]

private theorem evM_sg {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* ℂ) (i j : Fin n)
    (w : ℝ ⊗[ℚ] E) :
    evM σ ((sgL i j).baseChange ℝ w) = Matrix.single i j (ev1 σ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]
    ext a b
    simp [sgL, Matrix.single_apply]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.single_add]

private theorem sum_sg_ent {E : Type} [Field E] [NumberField E] {n : ℕ}
    (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    z = ∑ i, ∑ j, (sgL i j).baseChange ℝ ((entL i j).baseChange ℝ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp [TensorProduct.tmul_sum, entL, sgL]
    rfl
  | add a b ha hb =>
    conv_lhs => rw [ha, hb]
    simp only [map_add (f := _), ← Finset.sum_add_distrib]

theorem UpperTheory.cmField_real_tensor_matrix_bijective_cmType :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Function.Bijective (fun (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) (τ : Phi A) => evM τ.1 z) := by
  intro hT E _ _ _ A n
  have hb := UpperTheory.cmField_real_tensor_bijective_cmType hT A
  constructor
  · intro z₁ z₂ h
    have hent : ∀ i j, (entL i j).baseChange ℝ z₁ = (entL (E := E) i j).baseChange ℝ z₂ := by
      intro i j
      apply hb.1
      funext τ
      have := congrFun h τ
      simp only at this ⊢
      rw [evaluation_baseChange_entry, evaluation_baseChange_entry, this]
    rw [sum_sg_ent z₁, sum_sg_ent z₂]
    simp only [hent]
  · intro f
    choose w hw using fun i j => hb.2 (fun τ => f τ i j)
    refine ⟨∑ i, ∑ j, (sgL i j).baseChange ℝ (w i j), ?_⟩
    funext τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, evM_sg]
    have hw' : ∀ i j, ev1 τ.1 (w i j) = f τ i j := fun i j => congrFun (hw i j) τ
    simp only [hw']
    exact (Matrix.matrix_eq_sum_single (f τ)).symm
end

-- bundled from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmTypeTraceEmbeddingInjectiveOfLinearEquiv
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

theorem UpperTheory.cmType_trace_embedding_injective_of_linearEquiv :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (β : V ≃ₗ[ℚ] (Fin n → E)), Function.Injective (Th (fun τ : Phi A => τ.1) (β : V →ₗ[ℚ] (Fin n → E))) := by
  intro hT E _ _ _ A n V _ _ β z z' h
  have hb := (UpperTheory.cmField_real_tensor_bijective_cmType hT A).1
  set B : V →ₗ[ℚ] (Fin n → E) := (β : V →ₗ[ℚ] (Fin n → E)) with hBdef
  have key : ∀ j (y : ℝ ⊗[ℚ] V) (τ : Phi A), Th (fun τ : Phi A => τ.1) B y (τ, j) =
      ev1 τ.1 ((LinearMap.proj j ∘ₗ B).baseChange ℝ y) := by
    intro j y τ
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      rw [Th_tmul, LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul]
      rfl
    | add a b ha hb' =>
      rw [map_add (f := _), Pi.add_apply, ha, hb', map_add (f := _), map_add (f := _)]
  have hj : ∀ j, (LinearMap.proj j ∘ₗ B).baseChange ℝ z = (LinearMap.proj j ∘ₗ B).baseChange ℝ z' := by
    intro j
    apply hb
    funext τ
    simp only
    rw [← key, ← key, h]
  have hsum : ∀ y : ℝ ⊗[ℚ] (Fin n → E), y = ∑ j, (LinearMap.single ℚ (fun _ : Fin n => E) j).baseChange ℝ
      ((LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r v =>
      simp only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sum]
      congr 1
      simp [Finset.univ_sum_single v]
    | add a b ha hb' =>
      conv_lhs => rw [ha, hb']
      simp only [map_add (f := _), ← Finset.sum_add_distrib]
  have hc : ∀ j (y : ℝ ⊗[ℚ] V), (LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ (B.baseChange ℝ y) =
      (LinearMap.proj j ∘ₗ B).baseChange ℝ y := by
    intro j y
    rw [LinearMap.baseChange_comp]
    rfl
  have hB : B.baseChange ℝ z = B.baseChange ℝ z' := by
    rw [hsum (B.baseChange ℝ z), hsum (B.baseChange ℝ z')]
    simp only [hc, hj]
  have hid : ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ).comp (B.baseChange ℝ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hBdef, LinearEquiv.symm_comp, LinearMap.baseChange_id]
  have hl : ∀ x, ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ) (B.baseChange ℝ x) = x :=
    fun x => LinearMap.congr_fun hid x
  rw [← hl z, ← hl z', hB]
end

