module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw.TypeDatum

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

theorem blkOf_le {n : ℕ} (ea : a = r + j * t) (i : Fin n) (hi : i.val < a) : blkOf r t i ≤ j := by
  unfold blkOf
  split_ifs with h
  · exact Nat.zero_le _
  · have : (i.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
    omega

theorem blkOf_eq (ea : a = r + j * t) (eb : b = r + (j + 1) * t) (i : Fin b) (hi : a ≤ i.val) :
    blkOf r t i = j + 1 := by
  unfold blkOf
  have h2 := i.2
  rw [if_neg (by omega), Nat.div_eq_of_lt_le (k := j) (by omega) (by omega)]

theorem mem_twoBlockTriangular_of_blockTriangular (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) : g ∈ blockTri (blk2 a) := by
  intro p q hpq
  refine hg ?_
  unfold blk2 at hpq
  have hq : q.val < a := by
    by_contra hq
    split_ifs at hpq <;> omega
  have hp : a ≤ p.val := by
    by_contra hp
    split_ifs at hpq <;> omega
  rw [blkOf_eq ea eb p hp]
  exact Nat.lt_succ_of_le (blkOf_le ea q hq)

theorem top_mem (hab : a ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a))
    (hg : g ∈ blockTri (blkOf r t)) : upperLeftBlock hab g ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro p q hpq
  rw [upper_block_val_submatrix hab h2]
  exact hg (show blkOf r t (Fin.castLE hab q) < blkOf r t (Fin.castLE hab p) from hpq)

theorem restrictTopBlock_restrictTopBlock (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a))
    (hg : g ∈ blockTri (blkOf r t)) : upperLeftBlock ha (upperLeftBlock hab g) = upperLeftBlock hb g := by
  apply Units.ext
  rw [upper_block_val_submatrix ha (blockTri_blkOf_le r t (top_mem hab h2 hg)), upper_block_val_submatrix hab h2, upper_block_val_submatrix hb (blockTri_blkOf_le r t hg)]
  rfl

theorem diagonalBlock_restrictTopBlock (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) {c : ℕ} (hc : c ≤ j) :
    dBlk (blkOf r t) c (upperLeftBlock hab g) = dBlk (blkOf r t) c g := by
  have h2 := mem_twoBlockTriangular_of_blockTriangular ea eb hg
  apply Units.ext
  rw [diag_block_det_val c (top_mem hab h2 hg), diag_block_det_val c hg, upper_block_val_submatrix hab h2]
  have hlt : ∀ i : {i : Fin b // blkOf r t i = c}, i.1.val < a := fun i => by
    by_contra hi
    have := blkOf_eq ea eb i.1 (not_lt.1 hi)
    have := i.2
    omega
  let e : {i : Fin a // blkOf r t i = c} ≃ {i : Fin b // blkOf r t i = c} :=
    { toFun := fun i => ⟨Fin.castLE hab i.1, i.2⟩
      invFun := fun i => ⟨⟨i.1.val, hlt i⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem det_top (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {g : GL (Fin b) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det (upperLeftBlock hab g) * dBlk (blkOf r t) (j + 1) g := by
  have h2 := mem_twoBlockTriangular_of_blockTriangular ea eb hg
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    diag_block_det_val _ hg, upper_block_val_submatrix hab h2,
    Matrix.twoBlockTriangular_det (g : Matrix (Fin b) (Fin b) κ) (fun i => i.val < a) (fun p hp q hq =>
      h2 (show blk2 a q < blk2 a p by simp [blk2, hp, hq]))]
  let e : Fin a ≃ {i : Fin b // i.val < a} :=
    { toFun := fun i => ⟨Fin.castLE hab i, i.2⟩
      invFun := fun i => ⟨i.1.val, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e' : {i : Fin b // blkOf r t i = j + 1} ≃ {i : Fin b // ¬ i.val < a} :=
    Equiv.subtypeEquivRight fun i =>
      ⟨fun h h' => by have := blkOf_le ea i h'; omega, fun h => blkOf_eq ea eb i (not_lt.1 h)⟩
  rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_submatrix_equiv_self e']
  rfl

theorem topL_apply (hab : a ≤ b) (y : Matrix (Fin b) (Fin a) κ) (p q : Fin a) :
    topL a y p q = y (Fin.castLE hab p) q := by
  unfold topL
  rw [dite_eq_left ⟨lt_of_lt_of_le p.2 hab, q.2⟩]
  rfl

theorem lowZero_mul {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a)) {y : Matrix (Fin b) (Fin a) κ}
    (hy : LowZero a y) (s : Matrix (Fin a) (Fin a) κ) : LowZero a (g.val * y * s) := by
  intro p q hp _
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun m _ => ?_, zero_mul]
  by_cases hm : m.val < a
  · rw [h2 (show blk2 a m < blk2 a p by simp [blk2, hm, not_lt.2 hp]), zero_mul]
  · rw [hy m l (not_lt.1 hm) l.2, mul_zero]

theorem topL_mul (hab : a ≤ b) {g : GL (Fin b) κ} (h2 : g ∈ blockTri (blk2 a)) {y : Matrix (Fin b) (Fin a) κ}
    (hy : LowZero a y) (s : Matrix (Fin a) (Fin a) κ) :
    topL a (g.val * y * s) = (upperLeftBlock hab g).val * topL a y * s := by
  ext p q
  rw [topL_apply hab, upper_block_val_submatrix hab h2, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective (Fin.castLE hab) (Fin.castLE_injective hab) _ _ (fun m hm => ?_) fun m => ?_).symm
  · have hm' : ¬ m.val < a := fun h => hm ⟨⟨m.val, h⟩, by ext; rfl⟩
    rw [hy m l (not_lt.1 hm') l.2, mul_zero]
  · rw [topL_apply hab]; rfl

def IsTop (t : ℕ) (ha : r ≤ a) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha g = 1

theorem IsTop.move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g gS : GL (Fin a) κ} {gT : GL (Fin b) κ} (h : IsTop t ha y g)
    (hS : gS ∈ blockTri (blkOf r t)) (hT : gT ∈ blockTri (blkOf r t)) (hST : upperLeftBlock ha gS = upperLeftBlock hb gT) :
    IsTop t ha ((gT⁻¹).val * y * gS.val) ((upperLeftBlock hab gT)⁻¹ * g * gS) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have t2 := mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := top_mem hab t2 hT
  have hinv : upperLeftBlock hab gT⁻¹ = (upperLeftBlock hab gT)⁻¹ := extendOne_inv _ t2
  refine ⟨lowZero_mul (Subgroup.inv_mem _ t2) h1 _, ?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3) hS, ?_⟩
  · rw [topL_mul hab (Subgroup.inv_mem _ t2) h1, hinv, ← h2, Units.val_mul, Units.val_mul]
  · have le := blockTri_blkOf_le (κ := κ) (n := a) r t
    have m1 : upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g * gS) = upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g) * upperLeftBlock ha gS :=
      extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3)) (le hS)
    have m2 : upperLeftBlock ha ((upperLeftBlock hab gT)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab gT)⁻¹ * upperLeftBlock ha g :=
      extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le h3)
    have m3 : upperLeftBlock ha (upperLeftBlock hab gT)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab gT))⁻¹ := extendOne_inv _ (le tm)
    rw [m1, m2, m3, h4, restrictTopBlock_restrictTopBlock hab ha hb t2 hT, hST, mul_one, inv_mul_cancel]

theorem char_law (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g gS : GL (Fin a) κ} {gT : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hS : gS ∈ blockTri (blkOf r t)) (hT : gT ∈ blockTri (blkOf r t)) :
    (χ (j + 1) (Matrix.GeneralLinearGroup.det gS) * (χ (j + 1) (Matrix.GeneralLinearGroup.det gT))⁻¹) *
      ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab gT)⁻¹ * g * gS))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab gT)⁻¹ * g * gS)))⁻¹) =
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gS)) *
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) gT))⁻¹ *
      ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have tm := top_mem hab (mem_twoBlockTriangular_of_blockTriangular ea eb hT) hT
  have e1 : ∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab gT)⁻¹ * g * gS)) =
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gT))⁻¹ *
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
      (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) gS)) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c hc => ?_
    have hi : dBlk (blkOf r t) (c + 1) (upperLeftBlock hab gT)⁻¹ = (dBlk (blkOf r t) (c + 1) (upperLeftBlock hab gT))⁻¹ :=
      extendOne_inv _ tm
    rw [diag_block_det_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) hg) hS, diag_block_det_mul (Subgroup.inv_mem _ tm) hg, hi,
      diagonalBlock_restrictTopBlock hab ea eb hT (Finset.mem_range.1 hc), map_mul, map_mul, map_inv]
  rw [e1, Finset.prod_range_succ, det_top hab ea eb hT]
  simp only [map_mul, map_inv, mul_inv, inv_inv]
  generalize χ (j + 1) (Matrix.GeneralLinearGroup.det gS) = x1
  generalize χ (j + 1) (Matrix.GeneralLinearGroup.det (upperLeftBlock hab gT)) = x2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t j : ℕ} (ha : r ≤ a) (Pg Q : Finset (Pl D.host.E))
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_isTop (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)) :
    omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) χj y =
      ((∏ PP : ↥Pg, ((∏ c ∈ Finset.range j, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : ∀ PP, h.2.choose PP = g PP := fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : ∀ x, (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B).P.chi x = 1 := fun _ => rfl
    rw [e2]
    simp only [e, Units.val_one, one_mul, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val]
    rfl
  · exfalso
    refine h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2.1, ?_⟩
    exact Subgroup.mem_bot.2 (funext fun PP => (hg PP).2.2.2)

theorem omegaG_of_not (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)) :
    omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP, congrFun (Subgroup.mem_bot.1 g3) PP⟩⟩
  · rfl

end Dat

theorem omegaG_law : ∀ (D : D7) (a b r t j : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + j * t → b = r + (j + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Pg, gS PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, gT PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, upperLeftBlock ha (gS PP) = upperLeftBlock hb (gT PP)) → (∀ PP ∈ Pg, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Pg, (((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ) * ((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ)⁻¹)) * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y' = ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gS PP)) : ℂˣ) : ℂ) * ((∏ PP ∈ Pg, ∏ c ∈ Finset.range (j + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gT PP)) : ℂˣ) : ℂ)⁻¹ * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y := by
  intro D a b r t j ha hb ea eb Pg Q χ ξ gS gT y y' hS hT hST hy
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y PP.1) (g PP)
  · obtain ⟨g, hg⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTop t ha (y' PP.1) ((upperLeftBlock hab (gT PP.1))⁻¹ * g PP * gS PP.1) := fun PP => by
      rw [hy PP.1 PP.2]
      exact (hg PP).move hab ha hb ea eb (hS _ PP.2) (hT _ PP.2) (hST _ PP.2)
    rw [omegaG_of_isTop ha Pg Q χ ξ _ y g hg, omegaG_of_isTop ha Pg Q χ ξ _ y' _ hg']
    simp only [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.coe_prod]
    congr 1
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort Pg, ← Finset.prod_coe_sort Pg,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun PP _ =>
      char_law hab ea eb (fun c => χ c PP.1) (hg PP).2.2.1 (hS _ PP.2) (hT _ PP.2)
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), ∀ PP : ↥Pg, IsTop t ha (y' PP.1) (g PP) := by
      rintro ⟨g, hg⟩
      refine h ⟨fun PP => (upperLeftBlock hab (gT PP.1)⁻¹)⁻¹ * g PP * (gS PP.1)⁻¹, fun PP => ?_⟩
      have e : y PP.1 = ((gT PP.1)⁻¹⁻¹).val * y' PP.1 * ((gS PP.1)⁻¹).val := by
        rw [hy PP.1 PP.2, inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.one_mul]
      have i1 : upperLeftBlock ha (gS PP.1)⁻¹ = (upperLeftBlock ha (gS PP.1))⁻¹ := extendOne_inv _ (blockTri_blkOf_le r t (hS _ PP.2))
      have i2 : upperLeftBlock hb (gT PP.1)⁻¹ = (upperLeftBlock hb (gT PP.1))⁻¹ := extendOne_inv _ (blockTri_blkOf_le r t (hT _ PP.2))
      rw [e]
      exact (hg PP).move hab ha hb ea eb (Subgroup.inv_mem _ (hS _ PP.2)) (Subgroup.inv_mem _ (hT _ PP.2))
        (by rw [i1, i2, hST _ PP.2])
    rw [omegaG_of_not ha Pg Q χ ξ _ y h, omegaG_of_not ha Pg Q χ ξ _ y' h', mul_zero, mul_zero]

end GlobalTheory.StepLaw.TypeDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
section
open MeasureTheory

namespace GlobalTheory.UnfoldNormal

theorem unfold_zero_mean : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ K F : H → ℂ, Measurable K → Measurable F → (∀ n ∈ N, ∀ h, K (n * h) = K h) → (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ h, ∫ n in 𝓝, F ((n : H) * h) ∂κ = 0) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → IntegrableOn (fun h => K h * F h) 𝓕 ν → ∫ h in 𝓕, K h * F h ∂ν = 0 := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t K F hKm hFm hKN hKΓ hFΓ h0 𝓕 h𝓕 hint
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaCompactSpace N := inferInstance
  haveI : SigmaFinite κ := inferInstance
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun y : Γ => (y : H)) hab
  have hR : ∀ n₀ : N, κ.map (· * n₀) = κ := GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain H Γ N hΓ hNc κ 𝓝 hκ h𝓝 h𝓝t
  have hI : κ.map (fun n => n⁻¹) = κ := by
    haveI : κ.IsMulRightInvariant := ⟨hR⟩
    exact (GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant κ).inv_eq_self
  have hC : ∀ γ (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ :=
    GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self H Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t
  have hemb : MeasurableEmbedding (shear N) := measurableEmbedding_shear hNc
  set G := pairGroup Γ N hN with hG
  set μ := (κ.prod ν).map (shear N) with hμ
  haveI : Countable G := by
    refine Function.Injective.countable (f := fun g : G => ((⟨(g : H × H).1, g.2.1⟩ : Γ), (⟨(g : H × H).2, g.2.2.1⟩ : Γ))) ?_
    intro a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    exact Subtype.ext (Prod.ext hab.1 hab.2)
  haveI : MeasurableConstSMul G (H × H) := inferInstance
  haveI : SMulInvariantMeasure G (H × H) μ := GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup H ν Γ N hNc hN κ hκ hC
  have hS : IsFundamentalDomain G (shear N '' (𝓝 ×ˢ 𝓕)) μ :=
    ⟨nullMeasurableSet_shear_image hNc κ ν h𝓝.nullMeasurableSet h𝓕.nullMeasurableSet,
      _root_.GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕, _root_.GlobalTheory.UnfoldNormal.aedisjoint_pairGroup_smul_shear_image H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕⟩
  have hsw : μ.map Prod.swap = μ := GlobalTheory.T.map_swap_sheared_product_measure_unimodular H ν N hNc κ hκ hI
  set S := shear N '' (𝓝 ×ˢ 𝓕) with hSdef
  set f : H → ℂ := fun x => K x * F x with hf
  have hmp : MeasurePreserving (shear N) (κ.prod ν) μ := ⟨hemb.measurable, rfl⟩
  have hsp : MeasurePreserving (Prod.swap : H × H → H × H) μ μ := ⟨measurable_swap, hsw⟩
  have hswemb : MeasurableEmbedding (Prod.swap : H × H → H × H) := MeasurableEquiv.prodComm.measurableEmbedding
  let e : G → G := fun g => ⟨(g : H × H).swap, by
    obtain ⟨h1, h2, h3⟩ := g.2
    refine ⟨h2, h1, ?_⟩
    have : (g : H × H).2 * ((g : H × H).1)⁻¹ = ((g : H × H).1 * ((g : H × H).2)⁻¹)⁻¹ := by group
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [this]; exact N.inv_mem h3⟩
  have he : Function.Bijective e := by
    have : Function.Involutive e := fun g => Subtype.ext (Prod.swap_swap _)
    exact this.bijective
  have hS2 : IsFundamentalDomain G (Prod.swap ⁻¹' S) μ := by
    refine hS.preimage_of_equiv hsp.quasiMeasurePreserving he fun g x => ?_
    rfl
  have hΦ : ∀ (g : G) (p : H × H), f (g • p).1 = f p.1 := by
    intro g p
    have hu : (g : H × H).1 ∈ Γ := g.2.1
    change K ((g : H × H).1 * p.1) * F ((g : H × H).1 * p.1) = K p.1 * F p.1
    rw [hKΓ _ hu, hFΓ _ hu]
  have step1 : ∫ p in S, f p.1 ∂μ = ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ :=
    hS.setIntegral_eq hS2 (f := fun p => f p.1) hΦ
  have step2 : ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ = ∫ p in S, f p.2 ∂μ :=
    hsp.setIntegral_preimage_emb hswemb (fun p => f p.2) S
  have step3 : ∀ g : H × H → ℂ, ∫ p in S, g p ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, g (shear N q) ∂(κ.prod ν) :=
    fun g => hmp.setIntegral_image_emb hemb g _

  have hint2 : IntegrableOn (fun p : H × H => f p.1) S μ := by
    rw [hS.integrableOn_iff hS2 (f := fun p => f p.1) hΦ]
    have h2 : IntegrableOn (fun p : H × H => f p.2) S μ := by
      rw [hmp.integrableOn_image hemb]
      haveI : IsFiniteMeasure (κ.restrict 𝓝) := isFiniteMeasure_restrict.2 h𝓝t
      change Integrable (fun q : N × H => f q.2) ((κ.prod ν).restrict (𝓝 ×ˢ 𝓕))
      rw [← Measure.prod_restrict]
      exact hint.comp_snd (κ.restrict 𝓝)
    exact (hsp.integrableOn_comp_preimage hswemb).2 h2
  have hint3 : Integrable (fun q : N × H => f ((q.1 : H) * q.2)) ((κ.restrict 𝓝).prod (ν.restrict 𝓕)) := by
    rw [Measure.prod_restrict]
    exact (hmp.integrableOn_image hemb).1 hint2
  have lhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) = 0 := by
    rw [← Measure.prod_restrict]
    change ∫ q : N × H, f ((q.1 : H) * q.2) ∂((κ.restrict 𝓝).prod (ν.restrict 𝓕)) = 0
    rw [integral_prod_symm _ hint3]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [shear, hf, Pi.zero_apply]
    have : ∀ x : N, K ((x : H) * y) * F ((x : H) * y) = K y * F ((x : H) * y) := fun x => by rw [hKN _ x.2]
    simp_rw [this]
    rw [integral_const_mul, h0, mul_zero]
  have rhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) = (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν := by
    rw [← Measure.prod_restrict]
    simp only [shear]
    rw [integral_fun_snd, measureReal_restrict_apply_univ]
    rfl
  have key : (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν = 0 := by
    have e1 : ∫ p in S, f p.1 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) := step3 _
    have e2 : ∫ p in S, f p.2 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) := step3 _
    rw [← rhs, ← e2, ← step2, ← step1, e1, lhs]
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hpos : (κ 𝓝).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hne, h𝓝t⟩
  exact (smul_eq_zero.1 key).resolve_left hpos

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisa
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LFun.ConjParam

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem conj_mem_hecke {h : G → ℂ} (hh : h ∈ Hecke ℂ K) : (fun g => starRingEnd ℂ (h g)) ∈ Hecke ℂ K := by
  obtain ⟨h1, S, hS⟩ := hh
  exact ⟨fun a b g => congrArg _ (h1 a b g), S, fun g hg => hS g fun h0 => hg (by simp [h0])⟩

theorem eigen_conj (hK : IsCommensurated K) (hinv : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, g⁻¹ = k₁ * g * k₂)
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.LGrp.IsUnitarisable ρ) {x : V} (h0 : x ≠ 0) (hx : x ∈ fixed ρ K)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ K) {a b : ℂ} (ha : heckeVec ρ K h x = a • x)
    (hb : heckeVec ρ K (fun g => starRingEnd ℂ (h g)) x = b • x) : starRingEnd ℂ b = a := by
  obtain ⟨B, hB, hpos, hinvB⟩ := hρ
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hreal : ∀ g, starRingEnd ℂ (B (ρ g x) x) = B (ρ g x) x := fun g => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hinv g
    have e1 : B x (ρ g x) = B (ρ g⁻¹ x) x := by
      rw [← hinvB g (ρ g⁻¹ x) x, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : B (ρ k₁ (ρ g x)) x = B (ρ g x) x := by
      rw [← hinvB k₁ (ρ g x) x, hfix k₁ hk₁]
    rw [← hB, e1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix k₂ hk₂, e2]
  have key : ∀ f ∈ Hecke ℂ K, B (heckeVec ρ K f x) x = ∑ᶠ c : G ⧸ K, f c.out * B (ρ c.out x) x := fun f hf => by
    refine ((B.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_)
    simp
  have hxx : starRingEnd ℂ (B x x) = B x x := (hB x x).symm
  have hne : B x x ≠ 0 := fun e => by simpa [e] using hpos x h0
  have e1 := key h hh
  have e2 := congrArg (starRingEnd ℂ) (key _ (conj_mem_hecke hh))
  rw [ha] at e1
  rw [hb, show ⇑(starRingEnd ℂ) = (starAddEquiv : ℂ ≃+ ℂ) from rfl, AddEquiv.map_finsum] at e2
  apply mul_right_cancel₀ hne
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at e1 e2
  rw [e1]
  refine Eq.trans ?_ (e2.trans (finsum_congr fun c => ?_))
  · change _ = starRingEnd ℂ _
    rw [map_mul, hxx]
  · change starRingEnd ℂ _ = _
    rw [map_mul, hreal]
    exact congrArg (· * _) (Complex.conj_conj _)

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem conj_satU {m : ℕ} (ϖ : L) (q : ℕ) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    starRingEnd ℂ (SatU ϖ q (fun g => starRingEnd ℂ (h g)) α) = SatU ϖ q h fun i => starRingEnd ℂ (α i) := by
  have hs : ∀ {ι : Type} (f : ι → ℂ), starRingEnd ℂ (∑ᶠ i, f i) = ∑ᶠ i, starRingEnd ℂ (f i) := fun f =>
    AddEquiv.map_finsum (starAddEquiv : ℂ ≃+ ℂ) f
  unfold SatU
  rw [hs]
  refine finsum_congr fun a => ?_
  rw [map_mul, hs, map_prod]
  congr 1
  · simp
  · refine finsum_congr fun c => ?_
    split_ifs <;> simp

theorem inv_mem {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g⁻¹ = k₁ * g * k₂ := by
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ (g := (g : GL (Fin n) L)) (by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

theorem satU_star_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecU ϖ q ρ x α → ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => ((star (α i) : ℂˣ) : ℂ)) = SatU ϖ q h (fun i => (α i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hρ hx h hh
  exact (conj_satU ϖ q h fun i => (α i : ℂ)).symm.trans
    (eigen_conj (P.isCommensurated_integral_unitary_of_unramified hU n) (inv_mem hU) hρ hx.1 hx.2.1 hh (hx.2.2 h hh) (hx.2.2 _ (conj_mem_hecke hh)))

end GlobalTheory.LFun.ConjParam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HtOrth

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped NNReal

variable {D : D7}


open Classical in
def vInf (w : InfinitePlace D.host.F) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊

def vFin (v : HeightOneSpectrum (𝓞 D.host.F)) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))

def vsize {n : ℕ} (x : Fin n → AE D) : ℝ :=
  (((∏ w, vInf w x) * ∏ᶠ v, vFin v x : ℝ≥0) : ℝ)

def seen (V : HSp D) (g : GA D V) (ξ : Fin V.rank → D.host.E) : Fin V.rank → AE D :=
  mt V g⁻¹ *ᵥ fun i => incA D (ξ i)

theorem vsize_nonneg {n : ℕ} (x : Fin n → AE D) : 0 ≤ vsize x := NNReal.coe_nonneg _

end GlobalTheory.HtOrth

end
end

