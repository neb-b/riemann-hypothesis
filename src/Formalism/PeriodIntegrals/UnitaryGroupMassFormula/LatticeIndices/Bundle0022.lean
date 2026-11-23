module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0021

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstEmbeddingAlgebraMap
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem hform_iota2 (hθ : IsSplitEquiv X p θ) (l l' : Fin X.B.I.n → X.B.I.E) :
    iota2 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l l') =
      (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secondEmbedding_eq_star X p θ hθ, Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star,
    herm_entry, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem hform_iota1 (hθ : IsSplitEquiv X p θ) (l x : Fin X.B.I.n → X.B.I.E) :
    iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) =
      (fun j => iota2 X p θ (l j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (x j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply, starRingEnd_apply,
    ← secondEmbedding_eq_star X p θ hθ, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem firstEmbedding_algebraMap (f : X.B.I.F) : iota1 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
  show ((θ (Algebra.TensorProduct.includeRight (algebraMap X.B.I.F X.B.I.E f))).1) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply X.B.I.F (FpX X p) (TpX X p), AlgEquiv.commutes]
  simp

def DenseF : Prop :=
  ∀ c ε : FpX X p, ε ≠ 0 → ∃ b : X.B.I.F, ∃ o ∈ OpX X p, algebraMap X.B.I.F (FpX X p) b - c = ε * o

def EpsLat : Prop :=
  ∃ ε : FpX X p, ε ≠ 0 ∧ ∀ u : Fin X.B.I.n → FpX X p, (∀ i, u i ∈ OpX X p) →
    ε • u ∈ Mlat1 X p θ ∧ ε • u ∈ Mlat2 X p θ

theorem approx_of (hθ : IsSplitEquiv X p θ) (hD : DenseF X p) (hE : EpsLat X p θ) : ApproxP X p θ := by
  intro z hz
  obtain ⟨ε, hε0, hε⟩ := hE
  obtain ⟨a, w, hw, hwa⟩ := unitElt_holds X p θ hθ
  set α1 := iota1 X p θ (a : X.B.I.E) with hα1
  set α2 := iota2 X p θ (a : X.B.I.E) with hα2
  have val : ∀ β : FpX X p, ∃ d : FpX X p, d ≠ 0 ∧ d ∈ OpX X p ∧ d * β ∈ OpX X p := by
    intro β
    by_cases hβ : β ∈ OpX X p
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hβ⟩
    · have hβ0 : β ≠ 0 := fun h => hβ (h ▸ zero_mem _)
      refine ⟨β⁻¹, inv_ne_zero hβ0, ?_, by rw [inv_mul_cancel₀ hβ0]; exact one_mem _⟩
      exact ((OpX X p).mem_or_inv_mem β).resolve_left hβ
  obtain ⟨d1, hd10, hd1, hd1α⟩ := val α1
  obtain ⟨d2, hd20, hd2, hd2α⟩ := val α2
  have hδ0 : d1 * d2 ≠ 0 := mul_ne_zero hd10 hd20
  have hδ1 : d1 * d2 * α1 ∈ OpX X p := by
    rw [mul_right_comm]
    exact mul_mem hd1α hd2
  have hδ2 : d1 * d2 * α2 ∈ OpX X p := by
    rw [mul_assoc]
    exact mul_mem hd1 hd2α
  have hεδ : ε * (d1 * d2) ≠ 0 := mul_ne_zero hε0 hδ0
  choose b o ho hb using fun j => hD (w * z j * α1) (ε * (d1 * d2)) hεδ
  choose b' o' ho' hb' using fun j => hD (-(w * z j)) (ε * (d1 * d2)) hεδ
  set x : Fin X.B.I.n → X.B.I.E := fun j =>
    algebraMap X.B.I.F X.B.I.E (b j) + algebraMap X.B.I.F X.B.I.E (b' j) * (a : X.B.I.E) with hx
  set u1 : Fin X.B.I.n → FpX X p := fun j => d1 * d2 * o j + o' j * (d1 * d2 * α1) with hu1
  set u2 : Fin X.B.I.n → FpX X p := fun j => d1 * d2 * o j + o' j * (d1 * d2 * α2) with hu2
  have hu1m : ∀ j, u1 j ∈ OpX X p := fun j =>
    add_mem (mul_mem (mul_mem hd1 hd2) (ho j)) (mul_mem (ho' j) hδ1)
  have hu2m : ∀ j, u2 j ∈ OpX X p := fun j =>
    add_mem (mul_mem (mul_mem hd1 hd2) (ho j)) (mul_mem (ho' j) hδ2)
  have e1 : (fun j => iota1 X p θ (x j)) = ε • u1 := by
    funext j
    simp only [hx, hu1, map_add (f := _), map_mul, firstEmbedding_algebraMap, Pi.smul_apply, smul_eq_mul]
    rw [← hα1]
    linear_combination hb j + α1 * hb' j
  have e2 : (fun j => iota2 X p θ (x j)) = z + ε • u2 := by
    funext j
    simp only [hx, hu2, map_add (f := _), map_mul, secondEmbedding_algebraMap, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← hα2]
    linear_combination hb j + α2 * hb' j + z j * hwa
  have M1mem : ε • u1 ∈ Mlat1 X p θ := (hε u1 hu1m).1
  have M2mem : ε • u2 ∈ Mlat2 X p θ := (hε u2 hu2m).2
  have mem1 : ∀ l ∈ X.B.I.L, (fun j => iota1 X p θ (l j)) ∈ Mlat1 X p θ := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  have mem2 : ∀ l ∈ X.B.I.L, (fun j => iota2 X p θ (l j)) ∈ Mlat2 X p θ := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  refine ⟨x, fun l hl => ⟨?_, ?_⟩, ?_⟩
  · rw [hform_iota1 X p θ hθ, e1]
    exact dual_fwd X p θ hθ _ (mem2 l hl) _ M1mem
  · rw [hform_iota2 X p θ hθ, e2, add_dotProduct]
    exact add_mem (hz _ (mem1 l hl)) (dual_fwd X p θ hθ _ M2mem _ (mem1 l hl))
  · rw [e2, sub_add_cancel_left]
    exact neg_mem M2mem

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulVec
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

theorem frA_reindex_mul {R m n : Type} [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A B : Matrix m m R) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem secondCoords_mulVec (hθ : IsSplitEquiv X p θ) (x : HAp X p) (Z : Matrix (IdxD D) (IdxD D) (FpX X p))
    (hZ : Z * (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) = 1) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ v) = Zᵀ *ᵥ crd2 X p θ Q v := by
  set e := idxEquiv X
  set M1 := Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ x) with hM1
  set M2 := Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ x) with hM2
  set J' := Matrix.reindex e e (jm1 X.B.I.J θ) with hJ'
  set Qm := (Q : Matrix (IdxD D) (IdxD D) (FpX X p))
  set Qi := ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hU : M1ᵀ * (J'ᵀ * M2) = J'ᵀ := by
    have h0 := cmp_unit X.B.I.cm.sig X.B.I.J θ hθ x
    have h1 := congrArg (fun A => Matrix.reindex e e Aᵀ) h0
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    rw [frA_reindex_mul, frA_reindex_mul] at h1
    simpa [hM1, hM2, hJ', Matrix.transpose_reindex] using h1
  have hYZ : (Qi * M1 * Qm) * Z = 1 := mul_eq_one_comm.mp hZ
  have hQY : Qm * (Qi * M1 * Qm) = M1 * Qm := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have key : Qmᵀ * (J'ᵀ * M2) = Zᵀ * (Qmᵀ * J'ᵀ) := by
    calc Qmᵀ * (J'ᵀ * M2) = ((Qi * M1 * Qm) * Z)ᵀ * (Qmᵀ * (J'ᵀ * M2)) := by
          rw [hYZ, Matrix.transpose_one, Matrix.one_mul]
      _ = Zᵀ * ((Qm * (Qi * M1 * Qm))ᵀ * (J'ᵀ * M2)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul Qm]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * (M1ᵀ * (J'ᵀ * M2))) := by
          rw [hQY, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * J'ᵀ) := by rw [hU]
  unfold crd2
  rw [secondProj_split_mulVec]
  have hr : ((((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)).map fun t => (θ t).2) *ᵥ pr2 θ v) ∘ e.symm =
      M2 *ᵥ (pr2 θ v ∘ e.symm) := by
    rw [hM2, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    have : (pr2 θ v ∘ e.symm) ∘ e.symm.symm = pr2 θ v := by funext i; simp
    rw [this]; rfl
  have key' : Qmᵀ * J'ᵀ * M2 = Zᵀ * Qmᵀ * J'ᵀ := by rw [Matrix.mul_assoc, key, Matrix.mul_assoc]
  rw [hr, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A => A *ᵥ (pr2 θ v ∘ e.symm)) key'

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsTensorSmul
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

theorem firstCoords_add (a b : Fin X.B.I.n → TpX X p) : crd1 X p θ Q (a + b) = crd1 X p θ Q a + crd1 X p θ Q b := by
  unfold crd1
  rw [map_add (f := _), show (pr1 θ a + pr1 θ b) ∘ (idxEquiv X).symm =
    pr1 θ a ∘ (idxEquiv X).symm + pr1 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_add]

theorem secondCoords_add (a b : Fin X.B.I.n → TpX X p) : crd2 X p θ Q (a + b) = crd2 X p θ Q a + crd2 X p θ Q b := by
  unfold crd2
  rw [map_add (f := _), show (pr2 θ a + pr2 θ b) ∘ (idxEquiv X).symm =
    pr2 θ a ∘ (idxEquiv X).symm + pr2 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_add, Matrix.mulVec_add]

theorem firstCoords_tensor_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q (t • v) = (θ t).1 • crd1 X p θ Q v := by
  unfold crd1
  have : pr1 θ (t • v : Fin X.B.I.n → TpX X p) ∘ (idxEquiv X).symm = (θ t).1 • (pr1 θ v ∘ (idxEquiv X).symm) := by
    funext i
    show (θ (t * v ((idxEquiv X).symm i))).1 = (θ t).1 * (θ (v ((idxEquiv X).symm i))).1
    rw [map_mul]; rfl
  rw [this, Matrix.mulVec_smul]

theorem secondCoords_tensor_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (t • v) = (θ t).2 • crd2 X p θ Q v := by
  unfold crd2
  have : pr2 θ (t • v : Fin X.B.I.n → TpX X p) ∘ (idxEquiv X).symm = (θ t).2 • (pr2 θ v ∘ (idxEquiv X).symm) := by
    funext i
    show (θ (t * v ((idxEquiv X).symm i))).2 = (θ t).2 * (θ (v ((idxEquiv X).symm i))).2
    rw [map_mul]; rfl
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem smulO_eq (c : OvA X p) (v : Fin X.B.I.n → TpX X p) :
    c • v = ((c : FpX X p) • v) := rfl

end Loc

end MassDataIdxSteps
end
end

