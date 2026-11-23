module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0024
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdaptedMod
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

abbrev mQJ : Matrix (IdxD D) (IdxD D) (FpX X p) :=
  (Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ * (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ

theorem mQJ_unit : IsUnit (mQJ X p θ Q).det := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_reindex_self]
  exact (Units.isUnit (Matrix.GeneralLinearGroup.det Q)).mul (isUnit_det_split_form X p θ)

theorem secondCoords_eq_mulVec (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v = mQJ X p θ Q *ᵥ (pr2 θ v ∘ (idxEquiv X).symm) := by
  unfold crd2; rw [Matrix.mulVec_mulVec]

theorem crd_surj (a b : IdxD D → FpX X p) : ∃ x, crd1 X p θ Q x = a ∧ crd2 X p θ Q x = b := by
  set w1 := (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ a
  set w2 := (mQJ X p θ Q)⁻¹ *ᵥ b
  refine ⟨fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j)), ?_, ?_⟩
  · have : pr1 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w1 := by
      funext i; simp [pr1]
    unfold crd1; rw [this, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · have : pr2 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w2 := by
      funext i; simp [pr2]
    rw [secondCoords_eq_mulVec, this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (mQJ_unit X p θ Q), Matrix.one_mulVec]

theorem crd_inj (x : Fin X.B.I.n → TpX X p) (h1 : crd1 X p θ Q x = 0) (h2 : crd2 X p θ Q x = 0) : x = 0 := by
  have e1 : pr1 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ v) h1
    simp only [crd1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  have e2 : pr2 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (mQJ X p θ Q)⁻¹ *ᵥ v) h2
    simp only [secondCoords_eq_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (mQJ_unit X p θ Q),
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  funext j
  have a1 := congrFun e1 (idxEquiv X j)
  have a2 := congrFun e2 (idxEquiv X j)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] at a1 a2
  have : θ (x j) = 0 := Prod.ext a1 a2
  simpa using congrArg θ.symm this

theorem oEp_int (hL : LatBasis X p θ (reindex₂ X p Q)) (t : TpX X p) (ht : t ∈ OEp X p) :
    (θ t).1 ∈ OvA X p ∧ (θ t).2 ∈ OvA X p := by
  obtain ⟨j⟩ : Nonempty (IdxD D) := ⟨zI⟩
  obtain ⟨x1, hx1a, hx1b⟩ := crd_surj X p θ Q (Pi.single j 1) 0
  obtain ⟨x2, hx2a, hx2b⟩ := crd_surj X p θ Q 0 (Pi.single j 1)
  have hint : IntVec (OvA X p) (Pi.single j (1 : FpX X p)) := fun i => by
    by_cases h : i = j
    · subst h; simp [ValuationSubring.one_mem]
    · simp [h, ValuationSubring.zero_mem]
  have hz : IntVec (OvA X p) (0 : IdxD D → FpX X p) := fun _ => ValuationSubring.zero_mem _
  have l1 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x1).2 ⟨hx1a ▸ hint, hx1b ▸ hz⟩)
  have l2 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x2).2 ⟨hx2a ▸ hz, hx2b ▸ hint⟩)
  have c1 := ((latCrd_of X p θ Q hL _).1 l1).1 j
  have c2 := ((latCrd_of X p θ Q hL _).1 l2).2 j
  rw [firstCoords_tensor_smul, hx1a] at c1
  rw [secondCoords_tensor_smul, hx2b] at c2
  simp at c1 c2
  exact ⟨c1, c2⟩

def OEpSplit : Prop := θ.symm (1, 0) ∈ OEp X p ∧ θ.symm (0, 1) ∈ OEp X p

theorem splitA_of_lat (hL : LatBasis X p θ (reindex₂ X p Q)) (hO : OEpSplit X p θ) : SplitA X p θ Q :=
  splitA_of X p θ Q (oEp_int X p θ Q hL) hO.1 hO.2 (latCrd_of X p θ Q hL) (crd_inj X p θ Q) (crd_surj X p θ Q)

theorem reduction_image_of_adapted_mod (hb : AdBridgeIso X.B.I) (hC : LatCoreX)
    (h : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ OEpSplit X p θ ∧
      ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, hO, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted X p hb hC ⟨θ, hθ, Q, hL, splitA_of_lat X p θ Q hL hO, hA⟩

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulGL
section
noncomputable section

namespace MassDataIdxAdA

open Matrix

variable {K : Type*} [Field K] (O : ValuationSubring K) {ι : Type*} [Fintype ι] [DecidableEq ι]

def glK (c : GL ι O) : GL ι K := Units.map (RingHom.mapMatrix O.subtype).toMonoidHom c

theorem glK_val (c : GL ι O) : ((glK O c : GL ι K) : Matrix ι ι K) = (c : Matrix ι ι O).map O.subtype := rfl

theorem glK_inv (c : GL ι O) : (((glK O c)⁻¹ : GL ι K) : Matrix ι ι K) = ((c⁻¹ : GL ι O) : Matrix ι ι O).map O.subtype := by
  rw [glK, ← map_inv]; rfl

theorem intVec_mulVec {M : Matrix ι ι K} (hM : ∀ i j, M i j ∈ O) {w : ι → K} (hw : ∀ i, w i ∈ O) (i : ι) :
    (M *ᵥ w) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hw j)

theorem glK_int (c : GL ι O) (i j : ι) : ((glK O c : GL ι K) : Matrix ι ι K) i j ∈ O := by
  rw [glK_val]; exact ((c : Matrix ι ι O) i j).2

theorem glK_inv_int (c : GL ι O) (i j : ι) : (((glK O c)⁻¹ : GL ι K) : Matrix ι ι K) i j ∈ O := by
  rw [glK_inv]; exact (((c⁻¹ : GL ι O) : Matrix ι ι O) i j).2

theorem intVec_inv_iff (c : GL ι O) (w : ι → K) :
    (∀ i, ((((glK O c)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) i ∈ O) ↔ ∀ i, w i ∈ O := by
  constructor
  · intro h i
    have := intVec_mulVec O (glK_int O c) h i
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro h i
    exact intVec_mulVec O (glK_inv_int O c) h i

theorem intVec_tr_iff (c : GL ι O) (w : ι → K) :
    (∀ i, (((glK O c : GL ι K) : Matrix ι ι K)ᵀ *ᵥ w) i ∈ O) ↔ ∀ i, w i ∈ O := by
  constructor
  · intro h i
    have := intVec_mulVec O (M := (((glK O c)⁻¹ : GL ι K) : Matrix ι ι K)ᵀ) (fun a b => glK_inv_int O c b a) h i
    rwa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.one_mulVec] at this
  · intro h i
    exact intVec_mulVec O (M := (((glK O c : GL ι K) : Matrix ι ι K))ᵀ) (fun a b => glK_int O c b a) h i

end MassDataIdxAdA

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_mul_GL (c : GL (IdxD D) (OvA X p)) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ (Q * glK (OvA X p) c) v =
      (((glK (OvA X p) c)⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ crd1 X p θ Q v := by
  unfold crd1
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem secondCoords_mul_GL (c : GL (IdxD D) (OvA X p)) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ (Q * glK (OvA X p) c) v =
      ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *ᵥ crd2 X p θ Q v := by
  unfold crd2
  rw [Units.val_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]

theorem latRhs_iff (x : Fin X.B.I.n → TpX X p) :
    ((∀ i, (Matrix.mulVec (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))
        fun j => th1 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
    (∀ i, (Matrix.mulVec (Matrix.transpose ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        Matrix.transpose (J1 X p θ))
        fun j => th2 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x) := by
  have h1 : (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) := by
    unfold reindex₂; rw [← map_inv]; rfl
  have h2 : Matrix.transpose ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
      Matrix.transpose (J1 X p θ) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *
          (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ) := by
    rw [frA_reindex_mul, ← Matrix.transpose_reindex, ← Matrix.transpose_reindex]
    congr 2
    ext i j
    simp [Matrix.reindex_apply, J1, jm1, JR, th1]
  rw [h1, h2, frA_int_reindex, frA_int_reindex]
  unfold crd1 crd2 IntVec
  rw [Matrix.mulVec_mulVec]
  rfl

theorem latBasis_of_crd (h : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x)) : LatBasis X p θ (reindex₂ X p Q) := by
  intro x
  rw [h x, latRhs_iff]

theorem latBasis_mulGL (hL : LatBasis X p θ (reindex₂ X p Q)) (c : GL (IdxD D) (OvA X p)) :
    LatBasis X p θ (reindex₂ X p (Q * glK (OvA X p) c)) := by
  apply latBasis_of_crd
  intro x
  rw [latCrd_of X p θ Q hL x]
  unfold IntVec
  rw [firstCoords_mul_GL, secondCoords_mul_GL, intVec_inv_iff, intVec_tr_iff]

end Loc

end MassDataIdxSteps
end
end

