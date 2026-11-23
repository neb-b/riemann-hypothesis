module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLevelDatumEqFunctionOfResidueReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

variable {D : D7}

theorem isUnit_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    {x : v.adicCompletionIntegers D.host.F} (h : IsUnit (r x)) : IsUnit x := by
  by_contra hx
  have h1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hx
  have h2 : r x = 0 := (hr.2.1 x).2 h1
  rw [h2] at h
  exact not_isUnit_zero h

theorem redRel_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    (x : v.adicCompletionIntegers D.host.F) : RedRel φ PP (x : Fv D.host.F v) (r x) :=
  (hr.2.2.1 _ _).2 ⟨x.2, rfl⟩


set_option maxHeartbeats 1000000 in
theorem locDatum_eq_viaRed : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b t : ℕ) (ht : a + t = b) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam →
    ∀ (mu : (Fv D.host.F v)ˣ →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu χ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      localNewformFunction v J lam mu (rowsTB ht Y) = viaRed r (gLoc (b := b) L PP H c χ) Y := by
  intro D v φ PP r hr a b t ht L H c J lam hJ mu χ hmu Y
  have hinl : ∀ (i : Fin a) (j : Fin a), rowsTB ht Y (Sum.inl i) j = Y ⟨i.val, by omega⟩ j := fun _ _ => rfl
  have hinr : ∀ (i : Fin t) (j : Fin a), rowsTB ht Y (Sum.inr i) j = Y ⟨a + i.val, by omega⟩ j := fun _ _ => rfl

  unfold viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dite_eq_right hint]
    unfold localNewformFunction
    rw [dite_eq_right]
    rintro ⟨⟨k, hk⟩, hbot⟩
    apply hint
    intro i j
    by_cases hi : i.val < a
    · have h1 := congrFun (congrFun hk ⟨i.val, hi⟩) j
      rw [Matrix.submatrix_apply, hinl] at h1
      simp only [Matrix.map_apply, id] at h1
      rw [show i = ⟨i.val, by omega⟩ from rfl, ← h1]
      exact ((k : GL (Fin a) (v.adicCompletionIntegers D.host.F)) : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F)) ⟨i.val, hi⟩ j |>.2
    · have h1 := (hbot ⟨i.val - a, by omega⟩ j).1
      rw [hinr] at h1
      have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
      rwa [this] at h1
  rw [dite_eq_left hint]

  set y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) := Matrix.of fun i j => r ⟨Y i j, hint i j⟩ with hy
  let K : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y ⟨i.val, by omega⟩ j, hint _ _⟩
  have hKr : K.map r = topL a y := by
    ext i j
    simp only [topL, Matrix.map_apply]
    rw [dite_eq_left ⟨by omega, j.2⟩]
    rfl

  have hKk : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F),
      ((k : Matrix (Fin a) (Fin a) _).map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) =
        (rowsTB ht Y).submatrix Sum.inl id) → (k : Matrix (Fin a) (Fin a) _) = K := by
    intro k hk
    funext i j
    apply Subtype.ext
    have h1 := congrFun (congrFun hk i) j
    rw [Matrix.submatrix_apply, hinl] at h1
    exact h1

  have hred : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F), (k : Matrix (Fin a) (Fin a) _) = K →
      ((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      ∀ i j, RedRel φ PP (((k : Matrix (Fin a) (Fin a) _) i j : v.adicCompletionIntegers D.host.F) : Fv D.host.F v)
        (((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) i j) := by
    intro k hk
    refine ⟨?_, fun i j => redRel_of_isRedMap hr _⟩
    rw [← hKr, ← hk]
    rfl

  unfold gLoc localNewformFunction
  split_ifs with hP hG hG
  ·
    have hk0 := hP.1.choose_spec
    have hg0 := hG.2.choose_spec
    generalize hP.1.choose = k₀ at hk0 ⊢
    obtain ⟨k, hkJ⟩ := k₀
    have hK := hKk k hk0
    obtain ⟨hm, hrr⟩ := hred k hK
    have hkg : Matrix.GeneralLinearGroup.map r k = hG.2.choose := Units.ext (hm.trans hg0.1.symm)
    have hlam := (hJ _ _ hrr).2 hkJ
    rw [hkg, Formalism.L2.DIV.extendOne_of_mem _ hg0.2.2] at hlam
    have hdet : RedRel φ PP ((Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom
        (Matrix.GeneralLinearGroup.det k) : (Fv D.host.F v)ˣ) : Fv D.host.F v)
          ((Matrix.GeneralLinearGroup.det hG.2.choose : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) := by
      have e2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map r k) : (Formalism.L2.DIV.kP PP)ˣ) :
          Formalism.L2.DIV.kP PP) = r ((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers D.host.F)ˣ) :
            v.adicCompletionIntegers D.host.F) := by
        exact (RingHom.map_det r (k : Matrix (Fin a) (Fin a) _)).symm
      rw [← hkg, e2]
      exact redRel_of_isRedMap hr _
    rw [hlam, hmu _ _ hdet]
    push_cast
    rfl
  ·
    exfalso
    apply hG
    obtain ⟨⟨⟨k, hkJ⟩, hk⟩, hbot⟩ := hP
    have hK := hKk k hk
    obtain ⟨hm, hrr⟩ := hred k hK
    have hJk := ((hJ k _ hrr).1.1 hkJ)
    refine ⟨?_, Matrix.GeneralLinearGroup.map r k, hm, hJk⟩
    intro i j hi hj
    have h1 := hbot ⟨i.val - a, by omega⟩ ⟨j.val, hj⟩
    rw [hinr] at h1
    have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
    rw [this] at h1
    exact (hr.2.1 ⟨Y i ⟨j.val, hj⟩, hint _ _⟩).2 h1.2
  ·
    exfalso
    apply hP
    obtain ⟨hlow, g, hg, hgT, hgH⟩ := hG
    have hdet : IsUnit K.det := by
      apply isUnit_of_isRedMap hr
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hKr, ← hg]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    let k : GL (Fin a) (v.adicCompletionIntegers D.host.F) := ((Matrix.isUnit_iff_isUnit_det K).2 hdet).unit
    have hkK : (k : Matrix (Fin a) (Fin a) _) = K := rfl
    obtain ⟨hm, hrr⟩ := hred k hkK
    have hkg : Matrix.GeneralLinearGroup.map r k = g := Units.ext (hm.trans hg.symm)
    have hkJ : k ∈ J := (hJ k _ hrr).1.2 (hkg ▸ ⟨hgT, hgH⟩)
    refine ⟨⟨⟨k, hkJ⟩, ?_⟩, ?_⟩
    · funext i j
      rfl
    · intro i j
      rw [hinr]
      refine ⟨hint _ _, (hr.2.1 ⟨Y _ j, hint _ _⟩).1 ?_⟩
      exact hlow ⟨a + i.val, by omega⟩ j (by simp) j.2
  · rfl

end GlobalTheory.StepVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTwistDatumEqFunctionOfResidueReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem phiQ_eq_viaRed_qLoc : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b k : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu ξ⁻¹ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v k mu Y = viaRed r (qLoc k PP ξ) Y := by
  intro D v φ PP r hr a b k mu ξ hmu Y
  classical
  unfold phiQ viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dite_eq_right hint, dite_eq_right (fun h => hint h.2.2.1)]
  rw [dite_eq_left hint]

  set Yo : Matrix (Fin b) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y i j, hint i j⟩ with hYo
  have hy : (Matrix.of fun i j => r ⟨Y i j, hint i j⟩) = Yo.map r := rfl
  have htopY : topL k Y = (topL k Yo).map (v.adicCompletionIntegers D.host.F).subtype := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp [Yo]
  have htopy : topL k (Yo.map r) = (topL k Yo).map r := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp
  set d := (topL k Yo).det with hd
  have hdetY : (topL k Y).det = (d : Fv D.host.F v) := by
    rw [htopY]; exact (RingHom.map_det (v.adicCompletionIntegers D.host.F).subtype _).symm
  have hdety : (topL k (Yo.map r)).det = r d := by
    rw [htopy]; exact (RingHom.map_det r _).symm
  have hle : Valued.v (d : Fv D.host.F v) ≤ 1 := d.2
  have hunit : IsUnit (r d) ↔ Valued.v (d : Fv D.host.F v) = 1 := by
    constructor
    · intro hu
      refine le_antisymm hle (not_lt.mp fun hlt => ?_)
      exact hu.ne_zero ((hr.2.1 d).mpr hlt)
    · intro h1
      have hne : (d : Fv D.host.F v) ≠ 0 := by
        intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
      have hinv : ((d : Fv D.host.F v))⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
        show Valued.v ((d : Fv D.host.F v))⁻¹ ≤ 1
        rw [map_inv₀, h1, inv_one]
      have hdu : IsUnit d := by
        refine ⟨⟨d, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩ <;> ext <;> simp [hne]
      exact hdu.map r
  have hlow : LowZero k (Yo.map r) ↔ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
    unfold LowZero
    refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ => ?_
    exact hr.2.1 (Yo i j)
  rw [hy]
  unfold qLoc
  by_cases hc : Valued.v (d : Fv D.host.F v) = 1 ∧ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1
  · have hA : IsUnit (topL k Y).det ∧ Valued.v (topL k Y).det = 1 ∧ (∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
      refine ⟨?_, by rw [hdetY]; exact hc.1, hint, hc.2⟩
      rw [hdetY, isUnit_iff_ne_zero]
      intro h0; have := hc.1; rw [h0, map_zero] at this; exact zero_ne_one this
    have hB : LowZero k (Yo.map r) ∧ IsUnit (topL k (Yo.map r)).det :=
      ⟨hlow.mpr hc.2, by rw [hdety]; exact hunit.mpr hc.1⟩
    rw [dite_eq_left hA, dite_eq_left hB]
    have hrel : RedRel φ PP ((hA.1.unit : Fv D.host.F v)) ((hB.2.unit : Formalism.L2.DIV.kP PP)) := by
      refine (hr.2.2.1 _ _).mpr ⟨by convert d.2 using 2; rw [IsUnit.unit_spec, hdetY], ?_⟩
      rw [IsUnit.unit_spec hB.2, hdety]
      congr 1
      apply Subtype.ext
      simp [IsUnit.unit_spec, hdetY]
    have hm := hmu _ _ hrel
    rw [hm, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  · rw [dite_eq_right (fun h => hc ⟨by rw [← hdetY]; exact h.2.1, h.2.2.2⟩),
      dite_eq_right (fun h => hc ⟨hunit.mp (by rw [← hdety]; exact h.2), hlow.mp h.1⟩)]

end GlobalTheory.StepVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistDatumValueEqProdLocalResidueValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem omegaQ_one_eq_prod_qLoc : ∀ (D : D7) (a b r : ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)),
      omegaQ Q r ξ 1 y = ∏ PP ∈ Q, qLoc r PP (ξ PP) (y PP) := by
  intro D a b r Q ξ y
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dite_eq_left h, ← Finset.prod_attach Q (fun PP => qLoc r PP (ξ PP) (y PP))]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [zpow_one, qLoc, dite_eq_left (h PP.1 PP.2)]
  · rw [dite_eq_right h]
    push_neg at h
    obtain ⟨PP, hPP, hn⟩ := h
    refine (Finset.prod_eq_zero hPP ?_).symm
    rw [qLoc, dite_eq_right]
    rintro ⟨h1, h2⟩
    exact hn h1 h2

end GlobalTheory.StepVec
end

