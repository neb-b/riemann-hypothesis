module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import GroundTheory.LocalFields.MainTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogIdealSupportFinite
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.AdBridge

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}

theorem Aof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Aof (M.map f) = (Aof M).map f := rfl
theorem Bof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Bof (M.map f) = (Bof M).map f := rfl
theorem Cof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Cof (M.map f) = (Cof M).map f := rfl
theorem Dof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Dof (M.map f) = (Dof M).map f := rfl

theorem inv_map_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]

theorem Yof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Yof (M.map f) = (Yof M).map f := by
  rw [Yof, Yof, Matrix.map_mul, Dof_map, Cof_map, inv_map_of_isUnit f _ h]

theorem Xof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Xof (M.map f) = (Xof M).map f := by
  rw [Xof, Xof, Matrix.map_mul, Dof_map, Bof_map, inv_map_of_isUnit f _ h]

theorem Scof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Scof (M.map f) = (Scof M).map f := by
  rw [Scof, Scof, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Aof_map, Dof_map, Bof_map, Cof_map,
    inv_map_of_isUnit f _ h]

theorem lowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map f = lowUni (Y.map f) := by
  ext i j
  simp only [lowUni, unblk, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (eqv m r i) with a | a <;> rcases (eqv m r j) with b | b <;>
    simp [Matrix.one_apply, apply_ite f]

theorem conjLowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).map f = conjLowUni (Y.map f) (k.map f) := by
  rw [conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, Matrix.map_neg _ (map_neg f)]

end Maps

section Ones

variable {R : Type} [CommRing R] {m r : ℕ}

theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  simp [blk]

theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]
theorem Yof_one : Yof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Yof, Cof_one, Matrix.mul_zero]
theorem Xof_one : Xof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Xof, Bof_one, Matrix.zero_mul]
theorem Scof_one : Scof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Scof, Aof_one, Bof_one, Cof_one]; simp

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := Matrix.submatrix_mul_equiv _ _ _ _ _

theorem unblk_one : unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) = 1 := by
  simp [unblk]

theorem lowUni_mul_neg (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : lowUni Y * lowUni (-Y) = 1 := by
  rw [lowUni, lowUni, unblk_mul, Matrix.fromBlocks_multiply]
  simp [unblk_one]

theorem conjLowUni_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, Matrix.mul_one, lowUni_mul_neg]

theorem det_lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : (lowUni (m := m) Y).det = 1 := by
  rw [lowUni, unblk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]; simp

theorem det_conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).det = k.det := by
  rw [conjLowUni, Matrix.det_mul, Matrix.det_mul, det_lowUni, det_lowUni]; ring

theorem det_eq_det_Dof_mul (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    M.det = (Dof M).det * (Scof M).det := by
  letI := Matrix.invertibleOfIsUnitDet _ h
  have e : Matrix.fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) = blk M := Matrix.fromBlocks_toBlocks _
  have h1 : M.det = (blk M).det := by rw [blk, Matrix.det_submatrix_equiv_self]
  rw [h1, ← e, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl

theorem isUnit_det_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hM : IsUnit M.det)
    (h : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  rw [det_eq_det_Dof_mul M h] at hM
  exact isUnit_of_mul_isUnit_right hM

end Ones

section Adeles

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem pInf_sFin_eq_zero (b : Af E) : pInf E (sFin E b) = 0 := map_zero (infEq E).symm

omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_sFin_eq (b : Af E) : pFin E (sFin E b) = b := rfl

theorem isUnit_of_parts {x : Ad E} (h1 : IsUnit (pInf E x)) (h2 : IsUnit (pFin E x)) : IsUnit x := by
  refine Prod.isUnit_iff.2 ⟨?_, h2⟩
  have e : (infEq E) (pInf E x) = x.1 := (infEq E).apply_symm_apply x.1
  rw [← e]; exact h1.map _

theorem map_pInf_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1 :=
  congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) (pInf_finGL k)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem map_pFin_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) = (k : Matrix (Fin n) (Fin n) (Af E)) :=
  congrArg (fun g : GL (Fin n) (Af E) => (g : Matrix (Fin n) (Fin n) (Af E))) (pFin_finGL k)

theorem coe_finGL_mkGL {n : ℕ} (M : Matrix (Fin n) (Fin n) (Ad E)) (hi : M.map (pInf E) = 1) (hu : IsUnit M.det) :
    (finGL E n (mkGL (M.map (pFin E))) : Matrix (Fin n) (Fin n) (Ad E)) = M := by
  have hu' : IsUnit (M.map (pFin E)).det := by
    have h := hu.map (pFin E)
    rwa [RingHom.map_det] at h
  ext i j
  refine ad_ext ?_ ?_
  · exact congrFun (congrFun ((map_pInf_finGL _).trans hi.symm) i) j
  · exact congrFun (congrFun ((map_pFin_finGL _).trans (coe_mkGL hu')) i) j

end Adeles

theorem schur_data_mul_finGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  intro E _ _ _ m r x k hD hD'
  rw [Units.val_mul]
  have hx : IsUnit (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  have hK : IsUnit (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (finGL E (m + r + 1 + 1) k).isUnit
  have hKi := map_pInf_finGL (E := E) k
  have hKf := map_pFin_finGL (E := E) k
  generalize (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = K at *
  generalize (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = g at *
  have hf : conjLowUni ((Yof g).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)) =
      (conjLowUni (Yof g) K).map (pFin E) := by rw [conjLowUni_map, hKf]
  have hi : (conjLowUni (Yof g) K).map (pInf E) = 1 := by rw [conjLowUni_map, hKi, conjLowUni_one]
  have hdet : IsUnit (conjLowUni (Yof g) K).det := by rwa [det_conjLowUni]
  rw [hf] at hD' ⊢
  have alg := GlobalTheory.T.lower_unipotent_conj_block_formulas (Ad E) m r g K hD
  generalize conjLowUni (Yof g) K = L at *
  have hDi : (Dof L).map (pInf E) = 1 := by rw [← Dof_map, hi, Dof_one]
  have hDL : IsUnit (Dof L).det := by
    refine isUnit_of_parts ?_ ?_
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, hDi, Matrix.det_one]; exact isUnit_one
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Dof_map]; exact hD'
  obtain ⟨a1, a2, a3, a4, a5⟩ := alg hDL
  have hS := isUnit_det_Scof g hx hD
  have hSL := isUnit_det_Scof L hdet hDL
  have hSi : (Scof L).map (pInf E) = 1 := by rw [← Scof_map _ _ hDL, hi, Scof_one]
  have hYi : (Yof L).map (pInf E) = 0 := by rw [← Yof_map _ _ hDL, hi, Yof_one]
  have hXi : (Xof L).map (pInf E) = 0 := by rw [← Xof_map _ _ hDL, hi, Xof_one]
  have hXi' : ∀ j l, pInf E (Xof L j l) = 0 := fun j l => congrFun (congrFun hXi j) l
  refine ⟨hS, a1, Units.ext ?_, Units.ext ?_, fun i j => ?_, fun i j => ?_, ?_⟩
  · rw [coe_mkGL a1, Units.val_mul, coe_mkGL hD, Dof_map, coe_finGL_mkGL _ hDi hDL, a2]
  · have hSgK : IsUnit (Scof (g * K)).det := by rw [a4, Matrix.det_mul]; exact hS.mul hSL
    rw [coe_mkGL hSgK, Units.val_mul, coe_mkGL hS, Scof_map _ _ hDL, coe_finGL_mkGL _ hSi hSL, a4]
  · have h0 : pInf E (Yof L i j) = 0 := congrFun (congrFun hYi i) j
    rw [a3, Matrix.add_apply, map_add (f := _), h0, add_zero]
  · rw [a3, Matrix.add_apply, map_add (f := _), Yof_map _ _ hDL, Matrix.map_apply]
  · rw [a5, Matrix.add_apply, Xof_map _ _ hDL]
    congr 1
    refine ad_ext ?_ ?_
    · rw [pInf_sFin_eq_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, map_sum, map_mul, hXi', mul_zero, Finset.sum_const_zero, zero_mul]
    · rw [pFin_sFin_eq, Finset.sum_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]

end GlobalTheory.SchurExt.AdBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

namespace GlobalTheory.TypeIdent

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG

theorem irreducible_natCast_compl {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {g : ℕ}
    (hin : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hnot : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) :
    Irreducible ((g : ℕ) : 𝒪[w.adicCompletion E]) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hle : ∀ y : 𝒪[w.adicCompletion E], Valued.v (y : w.adicCompletion E) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[w.adicCompletion E], IsUnit y ↔ Valued.v (y : w.adicCompletion E) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (w.adicCompletion E))).isUnit_iff_valuation_eq_one
  have hv : Valued.v ((g : ℕ) : w.adicCompletion E) = w.intValuation ((g : ℕ) : 𝓞 E) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    congr 1
    exact ((map_natCast (algebraMap E (w.adicCompletion E)) g).symm).trans
      (congrArg (algebraMap E (w.adicCompletion E)) (map_natCast (algebraMap (𝓞 E) E) g).symm)
  have h1 : w.intValuation ((g : ℕ) : 𝓞 E) ≤ WithZero.exp (-1 : ℤ) := by
    simpa using (w.intValuation_le_pow_iff_mem ((g : ℕ) : 𝓞 E) 1).mpr (by rwa [pow_one])
  have h2 : WithZero.exp (-2 : ℤ) < w.intValuation ((g : ℕ) : 𝓞 E) := by
    by_contra hc
    exact hnot ((w.intValuation_le_pow_iff_mem _ 2).mp (by simpa using not_lt.1 hc))
  have hc : (((g : ℕ) : 𝒪[w.adicCompletion E]) : w.adicCompletion E) = (g : w.adicCompletion E) := by simp
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [hunit, hc, hv]
    intro e
    rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · have h3 : Valued.v (a : w.adicCompletion E) * Valued.v (b : w.adicCompletion E) =
        w.intValuation ((g : ℕ) : 𝓞 E) := by
      rw [← hv, ← map_mul, ← hc, hab]; rfl
    rw [← h3] at h1 h2
    have h0 := (zero_le.trans_lt h2).ne'
    have ha := left_ne_zero_of_mul h0
    have hb := right_ne_zero_of_mul h0
    have ha1 := hle a
    have hb1 := hle b
    rw [hunit, hunit]
    rw [← WithZero.exp_log ha] at h2 ha1 ⊢
    rw [← WithZero.exp_log hb] at h2 hb1 ⊢
    rw [← WithZero.exp_add, WithZero.exp_lt_exp] at h2
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
    rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

theorem nonempty_ident : ∀ D : D7, Nonempty (GlobalTheory.TypeRec.Ident D) := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ k v, ∃ φ : ℚ_[D.host.g k] ≃+* (D.naut.plGw k v).adicCompletion D.host.E, Continuous φ := by
    intro k v
    obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    haveI : CharZero ((D.naut.plGw k v).adicCompletion D.host.E) :=
      charZero_of_injective_ringHom (algebraMap D.host.E _).injective
    obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic ((D.naut.plGw k v).adicCompletion D.host.E) (D.host.g k)
      ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans (by
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1)) (irreducible_natCast_compl _ (D.naut.plGw_over k v) h2)
    exact ⟨φ, h⟩
  exact ⟨⟨fun k v => (key k v).choose, fun k v => (key k v).choose_spec⟩⟩

end GlobalTheory.TypeIdent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialOfNotRangeSubsetAbLocus
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

namespace GlobalTheory.BadReductionLattice

theorem nontrivial_of_not_range_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S : Scheme.{0}) (t₀ : SAB H S) (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (y : Sp T.V ⟶ S) (t : SAB H (Sp T'.V)) (_ : SABMap t t₀ (spMap g ≫ y)) (P : PELUnif (IsLocalRing.maximalIdeal T'.V) t), Function.Injective g → g.Finite → ¬ Set.range y ⊆ abLocus t₀.G → Nontrivial P.D.toPre.X := by
  intro E _ _ _ H S t₀ T T' g y t m P gi gf hy
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have hab := GlobalTheory.isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T'.V inferInstance
    P.D P.A t.G t.semi P.U hn
  have hp : IsProper t.G.hom := hab.proper
  apply hy
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ := gf.to_isIntegral.comap_surjective gi x
  exact GlobalTheory.ModelSum.range_subset_abLocus m hp ⟨x', rfl⟩

end GlobalTheory.BadReductionLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictEqInvLocalArtinMap
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
open GroundTheory.LocalField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompare

theorem restrict_eq_inv_localArtinMap : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ [IsSepClosure (w.adicCompletion E) (Kbar w)] (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w)) g =
        (localArtinMap (w.adicCompletion E) (Kbar w) (a σ))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg
  have hN := GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds
    GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha
  obtain ⟨θ, -, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ := fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩
  have e2 : ψ σ = g := by
    have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    show θ _ = g
    rw [← e, θ.apply_symm_apply]
  let r := (AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ
  have hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L]
      (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ) := fun τ L _ hL =>
    restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)
  have hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w))
      [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L],
      a τ ∈ (normUnits (w.adicCompletion E) L).range →
        restrictAb L (le_maximalAbelianExtension L) (r τ) = 1 := fun τ L _ hL hx => by
    have := (hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx
    rw [hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
    exact this
  let a' : Weil h →* (w.adicCompletion E)ˣ := invMonoidHom.comp a
  have ha' : Function.Surjective a' := inv_surjective.comp ha.surj
  have hker : a'.ker ≤ r.ker := fun τ hτ => by
    have h1 : a τ = 1 := inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)
    refine MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)
    rw [map_one]
    exact hnorm τ L (h1 ▸ Subgroup.one_mem _)
  let b := a'.liftOfSurjective ha' ⟨r, hker⟩
  have hb : ∀ τ, b (a τ)⁻¹ = r τ := fun τ =>
    MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ
  have hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w) := by
    refine eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)
    · obtain ⟨τ, rfl⟩ := ha' π
      have h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1 := by rw [map_inv]; exact hπ
      rw [ha.ord_eq, deg_inv, neg_neg] at h1
      have hF := (GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb, hr]
      refine (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_
      rw [unramifiedDegree_eq_ofAdd_one_iff]
      rintro ξ ⟨n, hn, hξ⟩
      have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := resCard_eq_normV w
      rw [hq] at hξ ⊢
      refine hF ξ n (Nat.pos_of_ne_zero hn) ?_
      have h2 : normV w ^ n = normV w ^ n - 1 + 1 :=
        (Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (one_lt_normV w)))).symm
      rw [h2, pow_succ, hξ, one_mul]
    · obtain ⟨τ, rfl⟩ := ha' x
      change restrictAb _ _ (b (a τ)⁻¹) = _
      rw [hb]
      exact hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)
  rw [← map_inv, ← hbφ, hb, ← e2]
  rfl

theorem restrict_eq_inv_reciprocity : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (Ω' : Type) [Field Ω'] [Algebra (w.adicCompletion E) Ω'] [IsSepClosure (w.adicCompletion E) Ω'] (j : Ω →+* Ω'),
    (∀ x : E, j (algebraMap E Ω x) = algebraMap (w.adicCompletion E) Ω' (algebraMap E (w.adicCompletion E) x)) →
    (∀ z : Ω, z ∈ A ↔ ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).IsIntegralElem (j z)) →
    ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
    ∀ (σ : Weil h) (g : Ω' ≃ₐ[w.adicCompletion E] Ω'), (∀ z : Ω, g (j z) = j ((σ : G E Ω) z)) →
      AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
        (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ ∧
      ∀ (M : IntermediateField (w.adicCompletion E) Ω') [FiniteDimensional (w.adicCompletion E) M]
        [IsAbelianGalois (w.adicCompletion E) M],
        AlgEquiv.restrictNormalHom M g =
          ((localReciprocityAbelian M).symm
            (a σ : (w.adicCompletion E)ˣ ⧸ (normUnits (w.adicCompletion E) M).range))⁻¹ := by
  intro E Ω _ _ _ _ _ A w h Ω' _ _ _ j hj hA a ha σ g hg
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have : IsSepClosure (w.adicCompletion E) (Kbar w) := ⟨inferInstance, inferInstance⟩
  let ε : Ω' ≃ₐ[w.adicCompletion E] Kbar w := IsSepClosure.equiv (w.adicCompletion E) Ω' (Kbar w)
  let ι : Ω →ₐ[E] Kbar w :=
    { (ε : Ω' →+* Kbar w).comp j with
      commutes' := fun x => by
        change ε (j (algebraMap E Ω x)) = _
        rw [hj, ε.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)] }
  have hιz : ∀ z, ι z = ε (j z) := fun _ => rfl
  have hc : (ε : Ω' →+* Kbar w).comp ((algebraMap (w.adicCompletion E) Ω').comp
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) =
      algebraMap (w.adicCompletionIntegers E) (Kbar w) := RingHom.ext fun x => by
    rw [IsScalarTower.algebraMap_apply (w.adicCompletionIntegers E) (w.adicCompletion E) (Kbar w)]
    exact ε.commutes _
  have hι : IsLocEmb A w ι := fun z => by
    rw [hA, hιz]
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      rw [← hc]
      have := congrArg (ε : Ω' →+* Kbar w) hp'
      rwa [Polynomial.hom_eval₂, map_zero] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (ε : Ω' →+* Kbar w).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hc]
      exact hp'
  let g' : GalLoc w := ε.symm.trans (g.trans ε)
  have hg' : Lifts ι g' σ := fun z => by
    change ε (g (ε.symm (ε (j z)))) = ε (j _)
    rw [ε.symm_apply_apply, hg]
  have H := restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ g' hg'
  have H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) Ω') g =
      (localArtinMap (w.adicCompletion E) Ω' (a σ))⁻¹ := by
    rw [← map_inv] at H ⊢
    ext y
    have h1 := localArtinMap_transport (RingEquiv.refl (w.adicCompletion E)) (fun _ _ => Iff.rfl)
      (ε : Ω' ≃+* Kbar w) (fun x => ε.commutes x) (a σ)⁻¹ y.2
    have h2 : Units.map (RingEquiv.refl (w.adicCompletion E)).toRingHom.toMonoidHom (a σ)⁻¹ = (a σ)⁻¹ :=
      Units.ext rfl
    rw [h2, ← H, AlgEquiv.restrictNormalHom_apply] at h1
    rw [AlgEquiv.restrictNormalHom_apply]
    apply ε.injective
    refine Eq.trans ?_ h1.symm
    change _ = ε (g (ε.symm (ε y)))
    rw [ε.symm_apply_apply]
  refine ⟨H1, fun M _ _ => ?_⟩
  rw [← restrictAb_localArtinMap, ← map_inv, ← H1]
  exact (restrictAb_topologicalAbelianizationEquiv M (le_maximalAbelianExtension M) g).symm

end GlobalTheory.ArtinCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuppFLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SuppLocal

theorem suppF_local : ∀ (D : D7) (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (k : GA D V),
    IsPrimeIdem P e f → SuppF V f k → k ∈ GfC V ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ≠ P.under (𝓞 D.host.F) →
      GlobalTheory.FinZeta.projV V v k = 1 := by
  intro D V P e f k h hk
  obtain ⟨x, rfl⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem V h rfl k).1 hk
  exact ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V _ x, fun v hv => GlobalTheory.AdelicU.proj_emb_ne _ _ hv x⟩

end GlobalTheory.SuppLocal
end
end

