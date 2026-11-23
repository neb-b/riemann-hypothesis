module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0086
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOnto
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0085

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLoUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hc | hc
    · rw [(h a c).1 hc, zero_mul]
    · rw [(h' c b).1 (lt_of_le_of_lt hc hab), mul_zero]
  · subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(h a a).2 rfl, (h' a a).2 rfl, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc' | hc'
      · rw [(h' c a).1 hc', mul_zero]
      · rw [(h a c).1 hc', zero_mul]
    · simp

theorem isUpUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first | exact GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul .. | (apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h h' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R

theorem isLoUni_one : IsLoUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne, fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isUpUni_one : IsUpUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isLoUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) : IsLoUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_lo (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [hb hc', mul_zero]
    · rw [(h a c).1 hc', zero_mul]
  · simp

theorem isUpUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) : IsUpUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_up (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [(h a c).1 hc', zero_mul]
    · rw [hb hc', mul_zero]
  · simp

end Uni

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def stZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) : Subgroup (Formalism.L2.SG.PairVal.GLR D) where
  carrier := stZSet M δ u u' Z L
  one_mem' := by
    refine ⟨1, ?_, isLoUni_one, 1, isUpUni_one, by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z' => ?_⟩⟩
    · simp [Matrix.nonsing_inv_mul L hL]
    · simp [zhatOM_zhatOM]
  mul_mem' := by
    rintro x y ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩ ⟨y', hy, hyl, by', hby, hyZ, hyp⟩
    refine ⟨x' * y', ?_, ?_, by' * bx, isUpUni_mul hby hbx, ?_, fun p => ?_⟩
    · rw [Units.val_mul, hx, hy, Units.val_mul]
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L * (L⁻¹ * (y' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) * (y' : Formalism.L2.SG.PairVal.MatR D) * L := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv L hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    · rw [Units.val_mul]
      exact isLoUni_mul hxl hyl
    · rw [Units.val_mul]
      calc (x' : Formalism.L2.SG.PairVal.MatR D) * (y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) * ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * by') * bx := by
            simp only [Matrix.mul_assoc]
        _ = ZhatOM Z := by rw [hyZ, hxZ]
    · obtain ⟨l1, ρ1, hl1, hρ1, h1⟩ := hxp p
      obtain ⟨l2, ρ2, hl2, hρ2, h2⟩ := hyp p
      refine ⟨l1 * l2, ρ2 * ρ1, intLow_mul _ hl1 hl2, intUp_mul _ hρ2 hρ1, fun Z' => ?_⟩
      have e : ((x' * y' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) *
            ZhatOM (ZhatOM ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * by')) * bx := by
        rw [zhatOM_zhatOM, Units.val_mul]
        simp only [Matrix.mul_assoc]
      rw [e, h1, h2]
      simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩
    obtain ⟨hxi, hxi1, hxi2⟩ := isLoUni_inv hxl
    obtain ⟨hbi, hbi1, hbi2⟩ := isUpUni_inv hbx
    have hZ : ((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx⁻¹ = ZhatOM Z := by
      rw [Matrix.coe_units_inv]
      calc (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ZhatOM Z * bx⁻¹ =
          (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx) * bx⁻¹ := by rw [hxZ]
        _ = ZhatOM Z := by
          simp only [← Matrix.mul_assoc]
          rw [hxi1, Matrix.one_mul, Matrix.mul_assoc, hbi2, Matrix.mul_one]
    refine ⟨x'⁻¹, ?_, by rw [Matrix.coe_units_inv]; exact hxi, bx⁻¹, hbi, hZ, fun p => ?_⟩
    · rw [Matrix.coe_units_inv, Matrix.coe_units_inv, hx]
      have hLi := Matrix.nonsing_inv_mul L hL
      have hiL := Matrix.mul_nonsing_inv L hL
      refine Matrix.inv_eq_left_inv ?_
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * L * (L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * (L * L⁻¹) * (x' : Formalism.L2.SG.PairVal.MatR D)) * L := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hiL, Matrix.mul_one, hxi1, Matrix.mul_one, hLi]
    · obtain ⟨l, ρ, hl, hρ, h⟩ := hxp p
      obtain ⟨hli, hli1, hli2⟩ := intLow_inv _ hl
      obtain ⟨hρi, hρi1, hρi2⟩ := intUp_inv _ hρ
      refine ⟨l⁻¹, ρ⁻¹, hli, hρi, fun Z' => ?_⟩
      have h2 := h (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹))
      have e : (x' : Formalism.L2.SG.PairVal.MatR D) *
          ZhatOM (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹)) * bx =
          ZhatOM Z' := by
        rw [zhatOM_zhatOM, Matrix.coe_units_inv]
        simp only [← Matrix.mul_assoc]
        rw [hxi2, Matrix.one_mul, Matrix.mul_assoc, hbi1, Matrix.mul_one]
      rw [e, zhatOM_zhatOM] at h2
      rw [h2]
      simp only [← Matrix.mul_assoc]
      rw [hli1, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hρi2, Matrix.mul_one]

theorem mem_CZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) (a : Formalism.L2.SG.PairVal.GLR D) :
    a ∈ CZ M δ u u' Z L ↔ a ∈ stZSet M δ u u' Z L := by
  have e : CZ M δ u u' Z L = stZ M δ u u' Z L hL := by
    unfold CZ
    exact Subgroup.closure_eq (stZ M δ u u' Z L hL)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolGrp

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfInputs
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem Hp_eq_Hsp (t : TauC Y u u') (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hL : IsLift Λ (lf D (X.Fu u))) (hL' : IsLift Λ t.frame) :
    Hp Λ (lf D (X.Fu u)) t.frame = Hsp (X.Fu u) t.frame.fl := by
  unfold Hp Hsp
  rw [UUE_eq_Asp Λ (by first | exact hΛ | exact hΛ.toIsLattice) _ _ hL hL']

theorem lemmaG3_of_inputs (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl ∈ (X.Fu u).X ∧
    (t1.lin * s'⁻¹ * t1.lin⁻¹) (omp t1.frame.fl (X.Fu u)) - omp t1.frame.fl (X.Fu u) ∈ t1.frame.fl.X ∧
    ∀ w ∈ Hsp (X.Fu u) t1.frame.fl, ∃ w0 ∈ Hsp (X.Fu u) t1.frame.fl,
      σ w - w0 ∈ (X.Fu u).X ∧ (t1.lin * s'⁻¹ * t1.lin⁻¹) w - w0 ∈ t1.frame.fl.X := by
  have line_occ (t0 t : TauC Y u u') (h0 : Gt t0 ≠ 0) (h : Gt t ≠ 0) (hR : RelC Y u u' t0 t) (hG : t.G = t0.G)
      (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') :
      (yT Y u u' t - coefA Y u u' t0 t • yT Y u u' t0 ∈ (X.Fu u).X ∧
        coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1) ∧
      (yT' Y u u' t - coefA' Y u u' t0 t • yT' Y u u' t0 ∈ (X.Fu u').X ∧
        coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1) := by
    have hdim := Formalism.L2.SG.Corank.finrank_VS D
    obtain ⟨hrow, hs0⟩ := hR
    have hlam : t.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
    have hlam' : t.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
    have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
    have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
    have hL1 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
    have hL2 : IsLift t0.lam t.frame := by rw [← hlam]; exact t.rep.2.2.2.2.1
    have hG1 : Gval (lf D (X.Fu u)) t0.frame ≠ 0 := by
      intro hG
      apply h0
      simp only [Formalism.L2.SG.TermOp.Gt]
      rw [if_pos]
      exact (Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _).trans hG
    have hG12 : Gval (lf D (X.Fu u)) t.frame = Gval (lf D (X.Fu u)) t0.frame := by
      rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, hG]
    have hs0' : Lat.s0 t0.lam (lf D (X.Fu u)) t0.frame t.frame (t.lin * t0.lin⁻¹) D.R.k = 1 := by
      have h1 : Formalism.L2.SG.TermOp.s0T t0 t = 1 := hs0
      unfold Formalism.L2.SG.TermOp.s0T at h1
      rw [if_pos ⟨hlam.symm, hlam'.symm⟩] at h1
      exact h1
    have hTh := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam
      (by first | exact hlat | exact hlat.toIsLattice) _ t0.frame t.frame _ hLF hL1 hG1).1 hs0'
    have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hTs : star ((Tu D u : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := star_natCast _
    have hTs' : star ((Tu D u' : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E) := star_natCast _
    refine ⟨line_pair D.R.k hdim t0.lam (by first | exact hlat | exact hlat.toIsLattice) (lf D (X.Fu u)) t0.frame t.frame _ hLF hL1 hL2 hG1 hG12 hTE hTs hTh,
      line_pair' D.R.k hdim t0.lam (by first | exact hlat | exact hlat.toIsLattice) (lf D (X.Fu u)) (lf D (X.Fu u')) t0.lin t.lin t0.rep.2.2.1 t.rep.2.2.1 hLF
        hL1 hL2 hG1 hG12 hTE' hTs' hTh⟩
  obtain ⟨⟨l1, -⟩, ⟨l1', -⟩⟩ := line_occ t0 t1 h0 h1 hR1 hG1 hT hT'
  obtain ⟨⟨l2, -⟩, ⟨l2', -⟩⟩ := line_occ t0 t2 h0 h2 hR2 hG2 hT hT'
  have hy : yT Y u u' t2 - yT Y u u' t1 ∈ (X.Fu u).X := by
    have := Submodule.sub_mem _ l2 l1
    rw [← ha] at this
    convert this using 1
    abel
  have hy' : yT' Y u u' t2 - yT' Y u u' t1 ∈ (X.Fu u').X := by
    have := Submodule.sub_mem _ l2' l1'
    rw [← ha'] at this
    convert this using 1
    abel
  obtain ⟨o1, o2, o3, o4⟩ := omp_terms Y t1 t2 σ s' hσ hs' he
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs'i := SRat_inv (lf D (X.Fu u')) hs'
  have hσm := hσ
  obtain ⟨hσi, hσf, hσz⟩ := hσm
  obtain ⟨hsi', hsf', hsz'⟩ := hs'i
  have hsymm : ∀ v, t2.lin.symm (σ v) = s'.symm (t1.lin.symm v) := by
    intro v
    apply t2.lin.injective
    rw [LinearEquiv.apply_symm_apply, he]
    show σ v = σ (t1.lin (s' (s'.symm (t1.lin.symm v))))
    simp
  refine ⟨?_, ?_, ?_⟩
  · have e : yT Y u u' t2 - yT Y u u' t1 =
        ((Tu D u : ℕ) : D.host.E) • (σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl) := by
      simp only [yT, yv, o1, o2, smul_sub]
      abel
    rw [e] at hy
    exact (Submodule.smul_mem_iff _ hTE).1 hy
  · set ω := omp t1.frame.fl (X.Fu u) with hω
    have e : yT' Y u u' t2 - yT' Y u u' t1 =
        ((Tu D u' : ℕ) : D.host.E) • (s'.symm (t1.lin.symm ω) - t1.lin.symm ω) := by
      simp only [yT', yv, o3, o4, frame_z_eq_lin_zu, map_add (f := _), map_smul, LinearEquiv.symm_apply_apply, hsymm, smul_sub]
      abel
    rw [e] at hy'
    have hv := (Submodule.smul_mem_iff _ hTE').1 hy'
    refine (mem_frameX Y t1 _).2 ?_
    convert hv using 1
    rw [map_sub]
    show t1.lin.symm (t1.lin (s'.symm (t1.lin.symm ω))) - t1.lin.symm ω = _
    rw [LinearEquiv.symm_apply_apply]
  · obtain ⟨hl1, hl2, hTh⟩ := th21 Y t0 t1 t2 h0 h1 h2 hR1 hR2
    have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
    have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
    have hL1 : IsLift t0.lam t1.frame := by rw [← hl1]; exact t1.rep.2.2.2.2.1
    have hL2 : IsLift t0.lam t2.frame := by rw [← hl2]; exact t2.rep.2.2.2.2.1
    have hH1 := Hp_eq_Hsp Y t1 t0.lam hlat hLF hL1
    have hH2 := Hp_eq_Hsp Y t2 t0.lam hlat hLF hL2

    have hX1A : t1.frame.fl.X ≤ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact X_le_Asp _ _
    have hz1A : t1.frame.fl.z ∈ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact z_mem_Asp _ _
    have hAsp : Asp (X.Fu u) t2.frame.fl ≤ (Asp (X.Fu u) t1.frame.fl).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [Asp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl a =>
        refine ⟨σ.symm ((X.Fu u).fvec a), ?_, by simp⟩
        induction a using Fin.lastCases with
        | last =>
          have e : σ.symm ((X.Fu u).fvec (Fin.last _)) =
              (X.Fu u).z + (σ.symm (X.Fu u).z - (X.Fu u).z) := by
            simp [FlagG.fvec, Fin.snoc_last]
          rw [e]
          exact Submodule.add_mem _ (z_mem_Asp _ _) (X_le_Asp _ _ (SRat_inv (lf D (X.Fu u)) hσ).2.2)
        | cast a =>
          simp only [FlagG.fvec, Fin.snoc_castSucc]
          refine X_le_Asp _ _ (X_pres (lf D (X.Fu u)) (SRat_inv (lf D (X.Fu u)) hσ).2.1 _ ?_)
          exact Submodule.subset_span ⟨a, rfl⟩
      | inr b =>
        refine ⟨t1.lin (s' ((X.Fu u').fvec b)), ?_, ?_⟩
        · induction b using Fin.lastCases with
          | last =>
            have e : t1.lin (s' ((X.Fu u').fvec (Fin.last _))) =
                t1.frame.fl.z + t1.lin (s' (X.Fu u').z - (X.Fu u').z) := by
              rw [frame_z_eq_lin_zu, map_sub]; simp [FlagG.fvec, Fin.snoc_last]
            rw [e]
            refine Submodule.add_mem _ hz1A (hX1A ((mem_frameX Y t1 _).2 ?_))
            rw [LinearEquiv.symm_apply_apply]
            exact hs'.2.2
          | cast b =>
            refine hX1A ((mem_frameX Y t1 _).2 ?_)
            rw [LinearEquiv.symm_apply_apply]
            simp only [FlagG.fvec, Fin.snoc_castSucc]
            exact X_pres (lf D (X.Fu u')) hs'.2.1 _ (Submodule.subset_span ⟨b, rfl⟩)
        · show σ (t1.lin (s' ((X.Fu u').fvec b))) = t2.frame.fl.fvec b
          rw [frame_fvec, he]
          rfl
    intro w hw
    have hσw : σ w ∈ Hp t0.lam (lf D (X.Fu u)) t2.frame := by
      rw [hH2]
      refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun y hy => ?_
      obtain ⟨a, ha, rfl⟩ := hAsp hy
      rw [LinearEquiv.coe_coe, hσi]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hw a ha
    rw [← hTh] at hσw
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hσw
    obtain ⟨-, hp2, hp12, hpβ⟩ := (CorankRelation.mem_ThPairs t0.lam _ t2.frame t1.frame _ p).1 hp
    simp only [LinearMap.fst_apply] at hp1
    refine ⟨p.2, by rw [← hH1]; exact hp2, ?_, ?_⟩
    · rw [← hp1]; exact hp12
    · have e : (t1.lin * t2.lin⁻¹) p.1 = (t1.lin * s'⁻¹ * t1.lin⁻¹) w := by
        rw [hp1]
        show t1.lin (t2.lin.symm (σ w)) = t1.lin (s'.symm (t1.lin.symm w))
        rw [hsymm]
      rw [← e]
      exact hpβ

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PpPosTypGen
section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pp_pos_typ_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩

  have hnt : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    obtain ⟨P, hPmax, -⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
        exact bot_le)
    obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
    intro h
    apply hnot
    have hθ : (t : X.B.I.E) = θ := by
      have h1 : X.B.I.cm.sig (θ : X.B.I.E) = star (θ : X.B.I.E) := rfl
      rw [h, AlgHom.id_apply] at h1
      have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
      rw [htθ', ← h1]
    have : θ - t = 0 := by ext; simp [hθ]
    rw [this]
    exact P.zero_mem

  have hid : ∃ x : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    have he := hTF.2.2.1
    unfold etaV at he
    rw [if_neg h] at he
    exact absurd he (by decide)
  have hS : PI.UnitaryGroupMassFormula.LocJacTyp.SplitHyp X.B.I.cm.sig v := ⟨X.B.I.cm.deg2, hnt, hid⟩
  have hg : 0 < gAt X v := hTF.1.pos
  have hA := SdW.sdFromAnn_holds ψ v (dV v) hψ X.B.I.cm.deg2 (dV_ne_zero v)
    (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v) Unit
  haveI := hA.1
  have hP := PI.UnitaryGroupMassFormula.LocJacTyp.parabolic_volume X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u')
    (absV v (dV v) ^ Fintype.card Unit) hS hg hTF.2.2.2.1 (sdE (E := X.B.I.E) ψ v Unit) hA.1 hA.2.2 l
  have hP' : ((sdE (E := X.B.I.E) ψ v Unit) ((fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹'
      PPTyp X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') l)).toReal =
      absV v (dV v) ^ Fintype.card Unit * PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) ^ 3 *
        (PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) ^ 4)⁻¹ := hP
  unfold PPX volC
  rw [if_pos hv, hP']
  have hd : 0 < absV v (dV v) := absV_pos v (dV_ne_zero v)
  have hgv : (gAt X v : Fv X.B.I.F v) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : 0 < PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hgv
  have ha : PI.LocJacTyp.alp v D.R.rS l ≠ 0 := alp_ne_zero v D.R.rS l
  have h2 : 0 < PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v ha
  positivity

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupFinal
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupFinal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG

theorem repAtTup_of_stab {D : D7} (Zd : TermLoc.LocDat D) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))
    (hS : Pf.TupGlob.StabApprox Zd u u') : Pf.FibPart.RepAtTup Zd.M Zd.δ u u' F0 what₂ :=
  Pf.TupOnto.repAtTup_of_glob Zd.M Zd.δ u u' F0 what₂ (Pf.TupGlob.globMove_of u u' hS (Pf.FibD.dict_holds Zd))

end Formalism.L2.SG.Pf.TupFinal
end
end

