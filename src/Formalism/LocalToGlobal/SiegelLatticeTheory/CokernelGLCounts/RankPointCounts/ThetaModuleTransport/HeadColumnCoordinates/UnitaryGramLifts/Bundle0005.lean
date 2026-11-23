module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.FormSplitP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.VecMulScCInr

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section FormSplit

theorem fs_add_left (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y Y' W : Ix r → O) :
    formG O cj qi Z T T' (Y + Y') W = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y' W := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add]
  ring

theorem fs_add_right (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y (W + W') = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y W' := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add, map_add (f := _)]
  ring

theorem splitSecondProj_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph2 g ((iota1 hs l i : M.L.O) : E) = 0 := by
  rcases i with a | a
  · rw [secondProj_apply, e_iota1_inl]
  · rw [secondProj_apply, e_iota1_inr]

theorem splitFirstProj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((iota2 hs l i : M.L.O) : E) = 0 := by
  rw [firstProj_apply, e_iota2]

theorem splitSecondProj_conj (x : E) : ph2 g ((M.L.cj : E →+* E) x) = ph1 g x := secondProj_conj_eq_firstProj x

theorem splitForm_iotaOne_iotaOne (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota1 hs l) (iota1 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitSecondProj_iotaOne, mul_zero, zero_mul,
    Finset.sum_const_zero]
  simp

theorem splitForm_iotaTwo_iotaTwo (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota2 hs l) (iota2 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitFirstProj_iotaTwo, mul_zero, zero_mul,
    Finset.sum_const_zero]
  simp

theorem fs_map_inv {n : Type} [Fintype n] [DecidableEq n] (f : E →+* E) (A : Matrix n n E) (hA : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

theorem fs_gram_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F) (i j : Ix r) :
    (M.L.cj : E →+* E) (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') j i) =
      gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') i j := by
  rcases i with a | a <;> rcases j with b | b <;> by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
    simp [gramG, cor, ha, hb, map_mul, map_add (f := _), map_neg, map_sub, M.L.cj_cj, AlgEquiv.commutes] <;> ring

theorem fs_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      (M.L.cj : E →+* E)
        (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') W Y) := by
  obtain ⟨G, hGd⟩ : ∃ G, gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') = G :=
    ⟨_, rfl⟩
  rw [hGd] at hU
  have hT : G.map (M.L.cj : E →+* E) = G.transpose := by
    ext i j; rw [Matrix.map_apply, Matrix.transpose_apply, ← hGd, fs_gram_herm]
  have hinv : ∀ i j, (M.L.cj : E →+* E) (G⁻¹ i j) = G⁻¹ j i := by
    intro i j
    have := congrFun (congrFun (fs_map_inv (M.L.cj : E →+* E) G hU) i) j
    rw [Matrix.map_apply] at this
    have h2 : (G.transpose)⁻¹ = (G⁻¹).transpose := by rw [Matrix.transpose_nonsing_inv]
    rw [this, hT, h2, Matrix.transpose_apply]
  have hcc : ∀ x : E, (M.L.cj : E →+* E) ((M.L.cj : E →+* E) x) = x := M.L.cj_cj
  unfold formG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hGd, map_sum, map_mul, hcc, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem fs_split (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs (cmp1 hs Y)) (iota2 hs (cmp2 hs W)) +
        (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
          (algebraMap F E T') (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) := by
  conv_lhs => rw [← iota_cmp hs Y, ← iota_cmp hs W]
  rw [fs_add_left, fs_add_right, fs_add_right, splitForm_iotaOne_iotaOne, splitForm_iotaTwo_iotaTwo,
    fs_herm Zh T T' _ hU (iota2 hs (cmp2 hs Y)) (iota1 hs (cmp1 hs W))]
  ring

theorem fs_rel (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) (Y Y₂ : Ix r → M.L.O) :
    thetaOf hs h₁ h₂ θ₁ θ₂ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ ↔
      θ₁ (QuotientAddGroup.mk (cmp1 hs Y)) = QuotientAddGroup.mk (cmp1 hs Y₂) ∧
        θ₂ (QuotientAddGroup.mk (cmp2 hs Y)) = QuotientAddGroup.mk (cmp2 hs Y₂) := by
  rw [thetaOf, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  simp [splitH, splitQ_mk, Prod.ext_iff]
  exact Iff.rfl

theorem formSplit_holds : FormSplitP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ θ₁ θ₂
  have hU₁ := unitGramG_holds F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁
  have hU₂ := unitGramG_holds F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂
  constructor
  · intro hF l l₂ w w₂ hl hw
    refine hF (iota1 hs l) (iota2 hs w) (iota1 hs l₂) (iota2 hs w₂) ?_ ?_
    · rw [fs_rel, firstComponent_iotaOne, firstComponent_iotaOne, secondComponent_iotaOne, secondComponent_iotaOne]
      exact ⟨hl, by simp⟩
    · rw [fs_rel, firstComponent_iotaTwo, firstComponent_iotaTwo, secondComponent_iotaTwo, secondComponent_iotaTwo]
      exact ⟨by simp, hw⟩
  · intro hB Y W Y₂ W₂ hY hW
    rw [fs_rel] at hY hW
    rw [fs_split hs Zh₂ T T' hU₂, fs_split hs Zh₁ T T' hU₁]
    have e1 := hB (cmp1 hs Y) (cmp1 hs Y₂) (cmp2 hs W) (cmp2 hs W₂) hY.1 hW.2
    have e2 := hB (cmp1 hs W) (cmp1 hs W₂) (cmp2 hs Y) (cmp2 hs Y₂) hW.1 hY.2
    have e2' : (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂
        (algebraMap F E T) (algebraMap F E T') (iota1 hs (cmp1 hs W₂)) (iota2 hs (cmp2 hs Y₂)) -
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) ∈ M.L.O := cj_mem_O M.L e2
    convert add_mem e1 e2' using 1
    rw [map_sub]
    ring

end FormSplit

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScPhiSymmApply
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA5

variable {E : Type} [CommRing E] {O : Subring E} {cj : E →+* E} {qi : E} {r : ℕ} {T T' α : E}

theorem dlast_mul_cj (h : ScHyp O cj qi T T' α) : dlast r α * dlast r (cj α) = 1 := by
  unfold dlast
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs
  · exact h.αn
  · exact mul_one 1

theorem scPhi_symm_apply (h : ScHyp O cj qi T T' α) (Y : Ix r → O) :
    (scPhi (r := r) h).symm Y = Matrix.vecMul Y (scA' h) := rfl

theorem relG_map (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (relG O cj qi Zh T T').map (scPhi (r := r) h).toLinearMap = relG O cj qi (Zh * dlast r α) T T' := by
  have hG := gramG_scale cj qi h.cjcj α T T' h.αn h.qic h.Tc h.T'c Zh
  have hG' : gramG cj qi Zh T T' = (scC r (cj α) (-((α - 1) * qi * cj α))).transpose *
      gramG cj qi (Zh * dlast r α) T T' * (scC r (cj α) (-((α - 1) * qi * cj α))).map cj := by
    have := gramG_scale cj qi h.cjcj (cj α) T T' (by rw [h.cjcj, mul_comm]; exact h.αn) h.qic h.Tc h.T'c
      (Zh * dlast r α)
    rw [Matrix.mul_assoc, dlast_mul_cj h, Matrix.mul_one] at this
    have hb : (cj α - 1) * qi = -((α - 1) * qi * cj α) := by linear_combination qi * h.αn
    rw [hb] at this
    exact this
  apply le_antisymm
  · rintro _ ⟨Y, hY, rfl⟩
    exact relC_fwd O cj _ _ _ _ h.C_mul hG (scA h) (by ext i j; rfl)
      (fun i j => scC_mem O _ _ h.cα_mem h.β'_mem j i) Y hY
  · intro y hy
    refine ⟨(scPhi h).symm y, ?_, by simp⟩
    rw [scPhi_symm_apply]
    exact relC_fwd O cj _ _ _ _ h.C'_mul hG' (scA' h) (by ext i j; rfl)
      (fun i j => scC_mem O _ _ h.αO h.βO j i) y hy

def scBar (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    DDg O cj qi Zh T T' ≃ₗ[O] DDg O cj qi (Zh * dlast r α) T T' :=
  Submodule.Quotient.equiv _ _ (scPhi h) (relG_map h Zh)

theorem scBar_mk (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y : Ix r → O) :
    scBar h Zh (Submodule.Quotient.mk Y) = Submodule.Quotient.mk (scPhi h Y) := rfl

theorem formG_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Y W : Ix r → O) :
    formG O cj qi (Zh * dlast r α) T T' (scPhi h Y) (scPhi h W) = formG O cj qi Zh T T' Y W := by
  have hu : IsUnit α := ⟨⟨α, cj α, h.αn, by rw [mul_comm]; exact h.αn⟩, rfl⟩
  have hcu : IsUnit (cj α) := ⟨⟨cj α, α, by rw [mul_comm]; exact h.αn, h.αn⟩, rfl⟩
  have e1 : ∀ V : Ix r → O, (fun i => ((scPhi (r := r) h V i : O) : E)) =
      Matrix.vecMul (fun i => (V i : E)) ((scC r α ((α - 1) * qi)).map cj) := fun V => funext (scPhi_coe h V)
  have := fG_invariant cj h.cjcj _ _ (scC r α ((α - 1) * qi))
    (gramG_scale cj qi h.cjcj α T T' h.αn h.qic h.Tc h.T'c Zh) (by rw [scC_det]; exact hu)
    (by rw [show ((scC r α ((α - 1) * qi)).map cj).det = cj (scC r α ((α - 1) * qi)).det from
      (RingHom.map_det cj _).symm, scC_det]; exact hcu) (fun i => (Y i : E)) (fun i => (W i : E))
  rw [← e1, ← e1] at this
  exact this

theorem inv_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    (Zh * dlast r α)⁻¹ = dlast r (cj α) * Zh⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (dlast_mul_cj h)]

theorem lamC_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (y : Fin (r + 1) → E) :
    lamC (Zh * dlast r α) y = cj α * lamC Zh y := by
  unfold lamC
  rw [inv_scale h, ← Matrix.mulVec_mulVec, dlast, Matrix.mulVec_diagonal]
  simp

theorem lamStarC_scale (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (y : Fin (r + 1) → E) :
    lamStarC cj (Zh * dlast r α) (fun b => cj (if b = Fin.last r then α else 1) * y b) = lamStarC cj Zh y := by
  unfold lamStarC
  rw [inv_scale h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dlast, Matrix.diagonal_mul]
  by_cases hb : b = Fin.last r
  · subst hb
    simp only [if_true, map_mul, h.cjcj]
    linear_combination (cj (Zh⁻¹ (Fin.last r) (Fin.last r)) * y (Fin.last r)) * h.αn
  · simp [hb]

end ScaleA5

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

