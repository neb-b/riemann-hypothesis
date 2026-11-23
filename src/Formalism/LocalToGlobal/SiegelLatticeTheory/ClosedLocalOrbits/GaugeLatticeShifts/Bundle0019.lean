module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColFreePf
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section ColFreeBij

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

def colD (h h' : Hfin X u) : X.B.I.Gf := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)

def LeviOnto : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (s : Iof TR), ∃ h : Hfin X u,
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset ∧ colD h (cs.h (cs.base q.1)) ∈ X.B.I.Kset ∧
      levi TR (colD (cs.h (cs.base q.1)) h) = s

def ColLatRep (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂}) (h : Hfin X u) (ρ : cs.Cl) (γ : Gam X u) (κ : Ku X u hK),
    colD (cs.h (cs.base q.1)) h ∈ X.B.I.Kset → h = iotaF X u γ * cs.h ρ * (κ : Hfin X u) → cs.lamOf ρ = q.1

theorem UG_mul {x y : Iof TR} (hx : x ∈ UG TR) (hy : y ∈ UG TR) : x * y ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_mul (hx v) (hy v)

theorem UG_inv {x : Iof TR} (hx : x ∈ UG TR) : x⁻¹ ∈ UG TR := fun v =>
  Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_inv (hx v)

theorem colD_mul (h h' h'' : Hfin X u) : colD h h' * colD h' h'' = colD h h'' := by
  unfold colD; group

theorem colD_inv (h h' : Hfin X u) : (colD h h')⁻¹ = colD h' h := by
  unfold colD; group

theorem good_colD {h h' : Hfin X u} (hk : colD h h' ∈ X.B.I.Kset) : Good X (colD h h') :=
  colGood X u h h' hk (by have := K_inv X.B.I hk; rw [colD_inv] at this; exact this)

theorem scOf_eq (ρ : cs.Cl) : scOf TR cs ρ = levi TR (colD (cs.h (cs.base (cs.lamOf ρ))) (cs.h ρ)) := rfl

theorem colD_conj (γ h h' : Hfin X u) : colD h (γ * h) * colD h h' = colD h (γ * h') := by
  unfold colD; simp only [Subgroup.coe_mul]; group

theorem colD_ku (hK : X.LevelSubgroupCharacter) {h h' : Hfin X u} (hm : colD h h' ∈ X.K2) : h⁻¹ * h' ∈ Ku X u hK := by
  show (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2
  have e : (X.xu u)⁻¹ * ((h⁻¹ * h' : Hfin X u) : X.B.I.Gf) * X.xu u = colD h h' := by
    unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [e]; exact hm

theorem colFreeBij_of (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK) (hL : ColLatK cs)
    (hO : LeviOnto TR cs) (hRep : ColLatRep cs hK) (q : {Λ // Λ ∈ what₂}) :
    Function.Bijective (fun x : Aset TR cs q × {ρ : cs.Cl // lamQ cs ρ = q} × UG TR =>
      (x.1 : Iof TR) * scOf TR cs x.2.1.1 * (x.2.2 : Iof TR)) := by
  set hb : Hfin X u := cs.h (cs.base q.1) with hhb
  have hbl : cs.lamOf (cs.base q.1) = q.1 := cs.base_lam _ q.2
  have lamρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, cs.lamOf ρ.1 = q.1 := fun ρ => congrArg Subtype.val ρ.2
  have kK : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD hb (cs.h ρ) ∈ X.B.I.Kset := fun ρ hρ =>
    hL (cs.base q.1) ρ (hbl.trans hρ.symm)
  have kKi : ∀ ρ : cs.Cl, cs.lamOf ρ = q.1 → colD (cs.h ρ) hb ∈ X.B.I.Kset := fun ρ hρ =>
    hL ρ (cs.base q.1) (hρ.trans hbl.symm)
  have scρ : ∀ ρ : {ρ : cs.Cl // lamQ cs ρ = q}, scOf TR cs ρ.1 = levi TR (colD hb (cs.h ρ.1)) := fun ρ => by
    rw [scOf_eq, lamρ ρ]
  have aK : ∀ γ : Gam X u, ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf) *
      ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u) = colD hb (iotaF X u γ * hb) := fun γ => by
    unfold colD; rw [hhb, Subgroup.coe_mul]; group
  constructor
  · rintro ⟨⟨a1, ha1⟩, ρ1, w1⟩ ⟨⟨a2, ha2⟩, ρ2, w2⟩ heq
    obtain ⟨γ1, hγ1K, ha1e⟩ := ha1
    obtain ⟨γ2, hγ2K, ha2e⟩ := ha2
    simp only at heq
    rw [aK] at hγ1K hγ2K ha1e ha2e
    rw [ha1e, ha2e, scρ, scρ] at heq
    rw [← levi_mul TR (good_colD hγ1K) (good_colD (kK _ (lamρ ρ1))),
      ← levi_mul TR (good_colD hγ2K) (good_colD (kK _ (lamρ ρ2))), colD_conj, colD_conj] at heq
    have hP1 : colD hb (iotaF X u γ1 * cs.h ρ1.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ1K (kK _ (lamρ ρ1))
    have hP2 : colD hb (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_conj]; exact K_mul X.B.I hγ2K (kK _ (lamρ ρ2))
    have hmK : colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1) ∈ X.B.I.Kset := by
      rw [← colD_mul _ hb, ← colD_inv]; exact K_mul X.B.I (K_inv X.B.I hP1) hP2
    have hlm : levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) =
        (w1 : Iof TR) * (w2 : Iof TR)⁻¹ := by
      rw [← colD_mul _ hb, ← colD_inv, levi_mul TR (good_inv X (good_colD hP1)) (good_colD hP2),
        levi_inv TR (good_colD hP1)]
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, heq, mul_assoc, mul_inv_cancel, mul_one]
    have hmU : ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k
        (levi TR (colD (iotaF X u γ1 * cs.h ρ1.1) (iotaF X u γ2 * cs.h ρ2.1)) v) := by
      rw [hlm]; exact UG_mul TR w1.2 (UG_inv TR w2.2)
    have hm2 := mem_level_of_unitriangular TR (good_colD hmK) (ncong_colDiff u _ _ hmK) hmU
    have hku := colD_ku hK hm2

    have hρ : ρ1.1 = ρ2.1 := by
      have hu := hR (cs.h ρ2.1)
      refine hu.unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2⁻¹ * γ1, ⟨_, hku⟩, ?_⟩
      simp only [map_mul, map_inv]
      group
    have hρ' : ρ1 = ρ2 := Subtype.ext hρ
    subst hρ'

    have hγ : γ1 = γ2 := by
      have h0 : γ1⁻¹ * γ2 = 1 := by
        refine hN (cs.h ρ1.1) (γ1⁻¹ * γ2) ?_
        have e : (cs.h ρ1.1)⁻¹ * iotaF X u (γ1⁻¹ * γ2) * cs.h ρ1.1 =
            (iotaF X u γ1 * cs.h ρ1.1)⁻¹ * (iotaF X u γ2 * cs.h ρ1.1) := by
          simp only [map_mul, map_inv]; group
        rw [e]; exact hku
      rw [inv_mul_eq_one] at h0; exact h0
    subst hγ
    have ha : a1 = a2 := ha1e.trans ha2e.symm
    subst ha
    have hw : (w1 : Iof TR) = w2 := mul_left_cancel heq
    have : w1 = w2 := Subtype.ext hw
    subst this
    rfl
  · intro s
    obtain ⟨h, hk, hki, hs⟩ := hO q s
    obtain ⟨ρ, ⟨γ, κ, hh⟩, -⟩ := hR h
    have hlam : cs.lamOf ρ = q.1 := hRep q h ρ γ κ hk hh
    have hκ2 : colD 1 (κ : Hfin X u) ∈ X.K2 := by
      have := κ.2
      have e : colD 1 (κ : Hfin X u) = (X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u := by
        unfold colD; simp only [Subgroup.coe_one, one_mul]; group
      rw [e]; exact this
    have hκK : colD 1 (κ : Hfin X u) ∈ X.B.I.Kset := hκ2.1
    have haE : colD hb (iotaF X u γ * hb) = colD hb h * (colD 1 (κ : Hfin X u))⁻¹ * colD (cs.h ρ) hb := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    have haK : colD hb (iotaF X u γ * hb) ∈ X.B.I.Kset := by
      rw [haE]; exact K_mul X.B.I (K_mul X.B.I hk (K_inv X.B.I hκK)) (kKi ρ hlam)
    have ga := good_colD haK
    have gr := good_colD (kK ρ hlam)
    have gk := good_colD hκK
    refine ⟨⟨⟨levi TR (colD hb (iotaF X u γ * hb)), γ, by rw [aK]; exact haK, by rw [aK]⟩,
      ⟨ρ, Subtype.ext hlam⟩, ⟨levi TR (colD 1 (κ : Hfin X u)), fun v => unitriangular_reduction_of_mem_level TR gk hκ2 v⟩⟩, ?_⟩
    simp only
    rw [show scOf TR cs ρ = levi TR (colD hb (cs.h ρ)) by rw [scOf_eq, hlam], ← levi_mul TR ga gr,
      ← levi_mul TR (good_mul X ga gr) gk, colD_conj]
    have e2 : colD hb (iotaF X u γ * cs.h ρ) * colD 1 (κ : Hfin X u) = colD hb h := by
      rw [hh]; unfold colD; simp only [Subgroup.coe_mul, Subgroup.coe_one, one_mul]; group
    rw [e2, hs]

end ColFreeBij

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.EnergyCut

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem tens_onb (u' : D.what₂.Word) :
    Orthonormal ℂ (fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) =>
      X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v))) ∧
    ⊤ ≤ Submodule.span ℂ (Set.range (fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) =>
      X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)))) := by
  set b := fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) with hb
  set e := fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) => X.tensU u' (fun v => b v (i v)) with he
  have hon : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [he, X.tensU_inner]
    have hloc : ∀ v, ⟪b v (i v), b v (j v)⟫_ℂ = if i v = j v then 1 else 0 := fun v =>
      (orthonormal_iff_ite.1 (b v).orthonormal) (i v) (j v)
    simp only [hloc]
    by_cases hij : i = j
    · subst hij; simp
    · obtain ⟨v, hv⟩ := Function.ne_iff.1 hij
      rw [if_neg hij]
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
  refine ⟨hon, ?_⟩
  have hmem : ∀ x, X.tensU u' x ∈ Submodule.span ℂ (Set.range e) := by
    intro x
    have hp : X.tensU u' x = ∑ i, ⟪e i, X.tensU u' x⟫_ℂ • e i := by
      apply Formalism.L2.SG.RealObj.RankOneTensors.eq_of_inner_tens (X.tensU u') (X.tensU_span u')
      intro z
      rw [inner_sum, show ⟪X.tensU u' z, X.tensU u' x⟫_ℂ = ∏ v, ⟪z v, x v⟫_ℂ from X.tensU_inner u' z x]
      have hterm : ∀ i, ⟪X.tensU u' z, ⟪e i, X.tensU u' x⟫_ℂ • e i⟫_ℂ =
          ∏ v, (⟪z v, b v (i v)⟫_ℂ * ⟪b v (i v), x v⟫_ℂ) := by
        intro i
        rw [inner_smul_right]
        simp only [he, X.tensU_inner]
        rw [Finset.prod_mul_distrib, mul_comm]
      simp only [hterm]
      rw [← Fintype.prod_sum (fun v j => ⟪z v, b v j⟫_ℂ * ⟪b v j, x v⟫_ℂ)]
      exact Finset.prod_congr rfl fun v _ => ((b v).sum_inner_mul_inner (z v) (x v)).symm
    rw [hp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← X.tensU_span u', Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hmem x

theorem hilbert_schmidt_tensor_product_factor (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    hs2 (OOinf X u u' γ) = ∏ v, hs2 (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
      Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  obtain ⟨hon, hsp⟩ := tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by
    simp [B]
  have hF := Formalism.L2.SG.RealObj.RankOneTensors.OOFactor_holds X u u' γ
  unfold hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GoodV (u u' : D.what₂.Word) : Set (Fin (D.R.rS + 1) → ℂ) :=
  {cv | (∀ l, cv l ≠ 0) ∧ 0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)}

def wtV (u u' : D.what₂.Word) (cv : Fin (D.R.rS + 1) → ℂ) : ℝ :=
  Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv) ^ (D.R.k - 1) * JacV (Matrix.diagonal cv)

def dcV : Measure (Fin (D.R.rS + 1) → ℂ) := Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def JvX (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) :
    X.Vloc u' v →L[ℂ] X.Vloc u v :=
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) g

theorem gv_diag_cont (u u' : D.what₂.Word) :
    Continuous (fun cv : Fin (D.R.rS + 1) → ℂ => Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)) := by
  simp only [Gv, Dl, le_refl, Nat.le_succ, ↓reduceDIte]
  fun_prop

theorem goodV_meas (u u' : D.what₂.Word) : MeasurableSet (GoodV u u') := by
  have h1 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ | ∀ l, cv l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ |
      0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)} :=
    isOpen_lt continuous_const (gv_diag_cont u u')
  exact (h1.inter h2).measurableSet

theorem good_eq_pi (u u' : D.what₂.Word) : Good X u u' = Set.pi Set.univ (fun _ => GoodV u u') := by
  ext c
  simp [Good, GoodV, Set.mem_pi]

theorem wtV_nonneg (u u' : D.what₂.Word) {cv : Fin (D.R.rS + 1) → ℂ} (h : cv ∈ GoodV u u') :
    0 ≤ wtV u u' cv := by
  unfold wtV JacV
  exact mul_nonneg (pow_nonneg h.2.le _) (Finset.prod_nonneg fun _ _ => sq_nonneg _)

theorem wtV_cont (u u' : D.what₂.Word) : Continuous (wtV u u') := by
  have hJ : Continuous (fun cv : Fin (D.R.rS + 1) → ℂ => JacV (Matrix.diagonal cv)) := by
    unfold JacV
    refine continuous_finsetProd _ fun l hl => ?_
    have h : l ≤ D.R.rS + 1 := (Finset.mem_Icc.mp hl).2.trans (Nat.le_succ _)
    simp only [modC, Dl, dif_pos h]
    fun_prop
  unfold wtV
  exact ((gv_diag_cont u u').pow _).mul hJ

end Formalism.L2.SG.RealObj.EnergyCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntTor
section
noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

theorem tE_eq_one_of_mem_middle_block (μ : ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tE μ k r i = 1 := by
  unfold Formalism.L2.SG.Pf.Choice.tE
  rw [if_neg (by omega), if_neg (by omega)]

theorem torS_apply (μ : ℂ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (torS μ k r * m * torS μ⁻¹ k r) i j = tE μ k r i * m i j * tE μ⁻¹ k r j := by
  have e1 : torS μ k r = Matrix.diagonal (tE μ k r) := rfl
  have e2 : torS μ⁻¹ k r = Matrix.diagonal (tE μ⁻¹ k r) := rfl
  rw [e1, e2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tor_comm (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : torS μ k r * h = h * torS μ k r := by
  have hb := WeylGroupFacts.uw_block hh
  ext i j
  rw [torS_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hb.2 i j hi]
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · simp [hij]
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hb.1 i j hj]
      by_cases hij : i = j
      · subst hij; simp [mul_comm]
      · simp [hij]
    · rw [tE_eq_one_of_mem_middle_block μ i (by omega) (by omega), tE_eq_one_of_mem_middle_block μ j (by omega) (by omega), one_mul, mul_one]

theorem tor_conj_uw {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    torS μ k r * h * torS μ⁻¹ k r = h := by
  rw [tor_comm μ hh, Matrix.mul_assoc, torS_mul_inv μ hμ, Matrix.mul_one]

theorem tor_mulVec_wb (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : torS μ k r *ᵥ z = z := by
  funext i
  rw [show torS μ k r = Matrix.diagonal (tE μ k r) from rfl, Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · push_neg at h
    rw [tE_eq_one_of_mem_middle_block μ i h.1 h.2, one_mul]

theorem ell_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (torS μ k r * m * torS μ⁻¹ k r) = μ * ell k r z m := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [torS_apply, tE_eI, show eI k r ⟨a.val + 1, ha⟩ = eI k r ⟨a.val + 1, ha⟩ from rfl, tE_eI]
    simp only []
    have e : r - (a : ℕ) = (r - ((a : ℕ) + 1)) + 1 := by omega
    rw [e, pow_succ, inv_pow]
    field_simp
  · have hv : (torS μ k r * m * torS μ⁻¹ k r) *ᵥ z = torS μ k r *ᵥ (m *ᵥ z) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tor_mulVec_wb μ⁻¹ hz]
    rw [hv, torS_eq, Matrix.mulVec_diagonal, tE_eI]
    have e : r - (a : ℕ) = 1 := by have := a.isLt; omega
    rw [e, pow_one]

theorem psi_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c (torS μ k r * m * torS μ⁻¹ k r) = psi k r z (c * μ) m := by
  unfold Formalism.QuantumDeterminants.psi
  rw [ell_tor hμ hz m, ← mul_assoc]

theorem tor_mem_UH {μ : ℂ} (hμ : μ ≠ 0) : torS μ k r ∈ UH (Hpk k r) := torS_gram μ hμ

theorem UH_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b by
    simp only [Matrix.mul_assoc], ha', hb']

theorem tor_conj_N {μ : ℂ} (hμ : μ ≠ 0) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : torS μ k r * a * torS μ⁻¹ k r ∈ Nset k r := by
  obtain ⟨hU, hc1, hc2⟩ := ha
  refine ⟨UH_mul (UH_mul (tor_mem_UH hμ) hU) (tor_mem_UH (inv_ne_zero hμ)), fun b i hbi => ?_, fun i j h1 h2 h3 => ?_⟩
  · rw [torS_apply, hc1 b i hbi]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp
  · rw [torS_apply, hc2 i j h1 h2 h3]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp

end Formalism.L2.SG.RealObj.EnergyIntTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarSubIsHaarS
section
noncomputable section

open MeasureTheory Topology

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n : ℕ} {ε : Fin n → Bool}

def haarSub (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) : Measure (Formalism.REAL.UJ ε) :=
  haveI : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  (Measure.haar : Measure G).map Subtype.val

theorem haarSub_isHaarS (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) :
    IsHaarS (G : Set (Formalism.REAL.UJ ε)) (haarSub G hG) := by
  have : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb := hG.isClosedEmbedding_subtypeVal
  have hι : Measurable (Subtype.val : G → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have hfin : IsFiniteMeasureOnCompacts (haarSub G hG) := by
    refine ⟨fun K hK => ?_⟩
    rw [haarSub, Measure.map_apply hι hK.measurableSet]
    exact (hemb.isCompact_preimage hK).measure_lt_top
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin⟩
  · have := hfin
    infer_instance
  · rw [haarSub, Ne, Measure.map_eq_zero_iff hι.aemeasurable]
    exact NeZero.ne _
  · rw [haarSub, Measure.map_apply hι hG.measurableSet.compl]
    have hempty : (Subtype.val : G → Formalism.REAL.UJ ε) ⁻¹' (G : Set (Formalism.REAL.UJ ε))ᶜ = ∅ := by
      ext x
      simp
    rw [hempty, measure_empty]
  · intro s hs
    rw [haarSub, Measure.map_map (measurable_const_mul s) hι]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : G → Formalism.REAL.UJ ε) =
        Subtype.val ∘ (fun y : G => (⟨s, hs⟩ : G) * y) := rfl
    rw [hcomp, ← Measure.map_map hι (measurable_const_mul _), map_mul_left_eq_self]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealHermitianForms
section
noncomputable section

open Matrix Finset
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.RealHermitianForms

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

section Form

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_uj (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) : hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  have hg : Formalism.REAL.inUJ ε (uMat g) := g.2
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  simp [uMat]

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem hJ_inv_r (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat g⁻¹ *ᵥ y) = hJ ε (uMat g *ᵥ x) y := by
  rw [← hJ_uj ε g x (uMat g⁻¹ *ᵥ y), mulVec_mulVec, uMat_mul_inv, one_mulVec]

end Form

section Eich

variable {n : ℕ} (ε : Fin n → Bool)

end Eich

section Frame

variable {n r : ℕ} (ε : Fin n → Bool)

end Frame

end Formalism.L2.SG.RealObj.InfCut.RealHermitianForms
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds
section
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem StepReal_holds : StepReal :=
  stepReal_of_witt (fun _ _ ε x y hG hnd => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.witt_of_gram ε x y hG hnd)

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end

