module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0009
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0011

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHIter
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

variable {k r : ℕ}

def ItgSwap : Prop :=
  ∀ (k r : ℕ) (νN νb : Measure (Mt k r)), Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) νN →
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) νb →
    ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (f : Mt k r → ℝ≥0∞), Measurable f →
    (∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * g * Matrix.of p.2 * Matrix.of p.1.2) ∂((νN.prod νN).prod νb)) =
      ∫⁻ n, ∫⁻ m, ∫⁻ n', f (fun i j => (Matrix.of n * g * Matrix.of m * (Matrix.of n')⁻¹) i j) ∂νN ∂νb ∂νN

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHRA
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

abbrev dG (k r : ℕ) : ℕ := Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r)))

theorem gVol_mul (k r : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    gVol k r (a * s) = a ^ dG k r * gVol k r s := by
  unfold gVol
  rw [Measure.addHaar_ball_mul_of_pos volume _ ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem gVol_pos (k r : ℕ) {s : ℝ} (hs : 0 < s) : 0 < gVol k r s := by
  unfold gVol
  exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hs).ne' measure_ball_lt_top.ne

theorem rhs_bounds (hW : Sandwich) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      Vol k r μb ((1 - ε) * ρ) ≤ rhs k r μb ((wBall k r ρ).indicator 1) ∧
      rhs k r μb ((wBall k r ρ).indicator 1) ≤ Vol k r μb ((1 + ε) * ρ) := by
  obtain ⟨δ, hδ, hW'⟩ := hW k r ε hε0 hε1
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hN : ∀ᵐ x ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1), Matrix.of x ∈ Nset k r :=
    ae_iff.2 (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top).2.2.1
  have hB : ∀ᵐ x ∂μb, Matrix.of x ∈ Formalism.FourierDecayAlt.B2.UWb k r := ae_iff.2 hμb.1.2.2.1
  constructor
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    split_ifs with hQ
    · have hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
          wBall k r ρ := (hW' ρ hρ hρδ n c m n' hn hm hn').2 hQ
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply]
    · exact zero_le
  · unfold Vol rhs
    refine lintegral_mono fun c => mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine lintegral_mono_ae (hN.mono fun n hn => ?_)
    refine lintegral_mono_ae (hB.mono fun m hm => ?_)
    refine lintegral_mono_ae (hN.mono fun n' hn' => ?_)
    by_cases hx : (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j : Mt k r) ∈
        wBall k r ρ
    · have hQ := (hW' ρ hρ hρδ n c m n' hn hm hn').1 hx
      rw [Set.indicator_apply, if_pos hx, Pi.one_apply, if_pos hQ]
    · rw [Set.indicator_apply, if_neg hx]
      exact zero_le

theorem scale_lim (hV : VolLim) (k r : ℕ) (μb : Measure (Mt k r))
    (hμb : IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ρ : ℝ => (Vol k r μb (a * ρ)).toReal / gVol k r ρ) (𝓝[>] 0)
      (𝓝 (((2 : ℝ) ^ r)⁻¹ * a ^ dG k r)) := by
  have hsc : Tendsto (fun ρ : ℝ => a * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := ((continuous_const_mul a).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact mul_pos ha hρ
  have h1 := ((hV k r μb hμb).comp hsc).mul_const (a ^ dG k r)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hg := gVol_pos k r (s := ρ) hρ
  have ha' : a ^ dG k r ≠ 0 := pow_ne_zero _ ha.ne'
  simp only [Function.comp]
  rw [gVol_mul k r ha ρ]
  field_simp

theorem rhsLim_of (hW : Sandwich) (hV : VolLim) : RhsLim := by
  intro k r μb hμb
  set L : ℝ := ((2 : ℝ) ^ r)⁻¹ with hLdef
  have hL : 0 < L := by positivity

  have hfin : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), rhs k r μb ((wBall k r ρ).indicator 1) ≠ ∞ := by
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := 1 / 2) (by norm_num) (by norm_num)
    have h := scale_lim hV k r μb hμb (a := 1 + 1 / 2) (by norm_num)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h1 h2 h3
    have hg := gVol_pos k r (s := ρ) h2
    have h4 : 0 < (Vol k r μb ((1 + 1 / 2) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + 1 / 2) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    exact ne_top_of_le_ne_top (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h2 h3).2
  rw [tendsto_order]
  constructor
  · intro a haL
    have hc : Tendsto (fun ε : ℝ => L * (1 - ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 - ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).1 a haL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 - ε) (by linarith)
    have hlo := (tendsto_order.1 h).1 a (by simpa [mul_comm] using h1)
    filter_upwards [hlo, hfin, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h4 h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    refine lt_of_lt_of_le h3 (div_le_div_of_nonneg_right ?_ hg.le)
    exact ENNReal.toReal_mono h4 (hb ρ h5 h6).1
  · intro b hbL
    have hc : Tendsto (fun ε : ℝ => L * (1 + ε) ^ dG k r) (𝓝[>] 0) (𝓝 L) := by
      have : Continuous (fun ε : ℝ => L * (1 + ε) ^ dG k r) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨h1, h2⟩, h0⟩ :=
      (((tendsto_order.1 hc).2 b hbL).and ((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds)
        |>.and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hb⟩ := rhs_bounds hW k r μb hμb (ε := ε) h0 h2
    have h := scale_lim hV k r μb hμb (a := 1 + ε) (by linarith)
    have hup := (tendsto_order.1 h).2 b (by simpa [mul_comm] using h1)
    have hpos := (tendsto_order.1 h).1 0 (by positivity)
    filter_upwards [hup, hpos, self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with ρ h3 h3' h5 h6
    have hg := gVol_pos k r (s := ρ) h5
    have h4 : 0 < (Vol k r μb ((1 + ε) * ρ)).toReal := by
      by_contra hc
      replace hc := not_lt.1 hc
      have : (Vol k r μb ((1 + ε) * ρ)).toReal / gVol k r ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hg.le
      linarith
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hg.le) h3
    exact ENNReal.toReal_mono (ENNReal.toReal_pos_iff.1 h4).2.ne (hb ρ h5 h6).2

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def uH (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [adjH_add, show adjH X + adjH Y + (X + Y) = (adjH X + X) + (adjH Y + Y) by abel, hX, hY, add_zero]
  zero_mem' := by simp [adjH]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [← Complex.coe_smul, adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX, smul_zero]

def uWb (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0 ∧ ∀ i j, ¬ (Mid k r i ∧ Mid k r j) → X i j = 0}
  add_mem' := by
    intro X Y hX hY
    refine ⟨(uH k r).add_mem hX.1 hY.1, fun i j h => ?_⟩
    simp [hX.2 i j h, hY.2 i j h]
  zero_mem' := ⟨(uH k r).zero_mem, fun i j _ => rfl⟩
  smul_mem' := by
    intro c X hX
    refine ⟨(uH k r).smul_mem c hX.1, fun i j h => ?_⟩
    simp [hX.2 i j h]

def tv (k r : ℕ) (c : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then c ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - i.val, by have := i.isLt; omega⟩))⁻¹

def tM (k r : ℕ) (c : Fin r → ℂ) : Mat k r := Matrix.diagonal (tv k r c)

def dv (k r : ℕ) (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then x ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 0
  else -star (x ⟨2 * r + k - i.val, by have := i.isLt; omega⟩)

def tD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal (dv k r x)

def Phi (k r : ℕ) (X : Mat k r) (x : Fin r → ℂ) (Z X' : Mat k r) : Mat k r :=
  w0B k r * NormedSpace.exp X * w0B k r * tM k r (1 + x) * NormedSpace.exp Z * NormedSpace.exp (-X')

def LmL (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →ₗ[ℝ] Mat k r where
  toFun p := w0B k r * p.1 * w0B k r + tD k r p.2.1 + p.2.2.1 - p.2.2.2
  map_add' p q := by
    have : tD k r (p.2.1 + q.2.1) = tD k r p.2.1 + tD k r q.2.1 := by
      unfold tD; rw [Matrix.diagonal_add]; congr 1; funext i; unfold dv
      split_ifs <;> simp [star_add] <;> ring
    simp only [Prod.fst_add, Prod.snd_add, this, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c p := by
    have : tD k r (c • p.2.1) = c • tD k r p.2.1 := by
      have hd : ∀ i, dv k r (c • p.2.1) i = (c : ℂ) * dv k r p.2.1 i := by
        intro i; unfold dv; split_ifs <;> simp [Complex.real_smul]
      unfold tD; ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, hd]
      split_ifs <;> simp [Complex.real_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, this, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add,
      smul_sub]

def Lm (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LmL k r)

def Vs (k r : ℕ) : Submodule ℝ (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) :=
  (lieNS k r).prod ((⊤ : Submodule ℝ (Fin r → ℂ)).prod ((uWb k r).prod (lieNS k r)))

def LieG : Prop := ∀ k r : ℕ, Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL

def LieWb : Prop := ∀ k r : ℕ, (∀ Z ∈ uWb k r, NormedSpace.exp Z ∈ Formalism.FourierDecayAlt.B2.UWb k r) ∧
  Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r).map RL

def LIso : Prop := ∀ k r : ℕ, (∀ v ∈ Vs k r, Lm k r v ∈ uH k r) ∧ (∀ Y ∈ uH k r, ∃ v ∈ Vs k r, Lm k r v = Y) ∧
  ∀ v ∈ Vs k r, ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2

end Formalism.L2.SG.Pf.BH.Sw
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviColsPf
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section LeviHom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem leviM_mul_inv {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : leviM TR x v * leviM TR x⁻¹ v = 1 := by
  rw [← leviM_mul_par TR hx.1 hx.2 v, mul_inv_cancel, leviM_one]

theorem isUnit_det_leviM {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : IsUnit (leviM TR x v).det := by
  exact Matrix.isUnit_det_of_right_inverse (leviM_mul_inv TR hx v)

theorem levi_coe {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) :
    ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) = leviM TR x v := by
  unfold levi
  rw [dite_eq_left (isUnit_det_leviM TR hx v)]
  rfl

theorem levi_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : levi TR (x * y) = levi TR x * levi TR y := by
  funext v
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul, levi_coe TR (good_mul _ hx hy), levi_coe TR hx, levi_coe TR hy]
  exact leviM_mul_par TR hx.1 hy.1 v

theorem levi_one : levi TR (1 : X.B.I.Gf) = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR (good_one _) v, leviM_one]
  rfl

theorem levi_inv {x : X.B.I.Gf} (hx : Good X x) : levi TR x⁻¹ = (levi TR x)⁻¹ := by
  have h1 := levi_mul TR (good_inv _ hx) hx
  rw [inv_mul_cancel, levi_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

end LeviHom

section ColGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_hA_mL {d w : VA X.B.I} (hd : d ∈ mL X.B.I X.B.g) (hw : w ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I d w) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g (mL_Qs X.B.I X.B.g hw hd)

theorem colStab (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    (∀ a, X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.e0 a - X.e0 a ∈
      mL X.B.I X.B.g) ∧
    X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  set k := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) with hkdef
  obtain ⟨hE0, hF0, hZ0, -, -⟩ := frame_Lf X
  have hk' : k = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by rw [hkdef]; group
  have hfix : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y → X.B.I.fmat k *ᵥ incl X.B.I y = incl X.B.I y := by
    intro y hy hxu
    rw [hk']
    have h1 : X.B.I.fmat (h' : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := h'.2 y hy
    have h2 : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := fixes_inv X (h.2 y hy)
    exact fixes_mul X (fixes_inv X hxu) (fixes_mul X h2 (fixes_mul X h1 hxu))
  have hE : ∀ a, X.B.I.fmat k *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) := fun a =>
    hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)) ((X.xu_fix u a).1)
  have hZ : X.B.I.fmat k *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u))) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) := by
    rw [Matrix.mulVec_mulVec, ← fmat_mul]
    have e : k * (X.xu u)⁻¹ = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) := by rw [hkdef]; group
    rw [e, fmat_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have hy : X.crd (X.zu u) ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u := Or.inr rfl
    exact fixes_mul X (fixes_inv X (h.2 _ hy)) (h'.2 _ hy)
  have key : ∀ (w v : VA X.B.I), v ∈ X.B.I.Lf → X.B.I.fmat k *ᵥ w = w → InAt X.B.I X.B.g X.B.g (v - w) →
      X.B.I.fmat k *ᵥ v - v ∈ mL X.B.I X.B.g := by
    intro w v hv hw hvw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hk hv) hv) ?_
    have := congG_of_Kset X hk hvw
    have e : X.B.I.fmat k *ᵥ v - v = X.B.I.fmat k *ᵥ (v - w) - (v - w) := by
      rw [Matrix.mulVec_sub, hw]; abel
    rw [e]; exact this
  refine ⟨fun a => key _ _ (hE0 a) (hE a) (X.basisApprox a).1, key _ _ hZ0 hZ ?_⟩
  obtain ⟨c, hc, hcm⟩ := X.xu_z u
  refine ⟨c, hc, ?_⟩
  rw [show X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) =
    -(X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) - X.z0) by abel, smul_neg]
  exact Submodule.neg_mem _ hcm

theorem par_of_stab {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    (he : ∀ a, X.B.I.fmat k *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hie : ∀ a, X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hiz : X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g) : Par X k := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hk, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat k *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k *ᵥ X.e0 a - X.e0 a) by abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (mL_Mo X.B.I (he a))
  · refine mem_Mo_eb X (K_mv X.B.I hk (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a) by abel,
        hA_add_left]
      exact Z_add X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1 (Z_hA_mL X (hie a) (hB j))
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0) by abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (Z_hA_mL X hiz (hB j))
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem colGood (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset)
    (hki : ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    Good X (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by
  have e1 : (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) := by
    rw [_root_.mul_inv_rev, inv_inv]
  have e2 : (((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) := by
    rw [_root_.mul_inv_rev, inv_inv]
  obtain ⟨he, hz⟩ := colStab X u h h' hk
  obtain ⟨he', hz'⟩ := colStab X u h' h hki
  refine ⟨par_of_stab X hk he (by rw [e1]; exact he') (by rw [e1]; exact hz'), ?_⟩
  rw [e1]
  exact par_of_stab X hki he' (by rw [e2]; exact he) (by rw [e2]; exact hz)

end ColGood

section LeviColsPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0 F0') in
def AdmPar : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt)

theorem leviCols_of (hL : ColLatK cs) (hL' : ColLatK cs') (hA : AdmPar F0 F0' cs cs') :
    LeviCols TR F0 F0' cs cs' := by
  unfold LeviCols
  intro t ρ ρ' h1 h2
  have hK : Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt) := hA t
  unfold iotaOf scOf
  rw [h1, h2]
  unfold kOf at hK ⊢
  have lb : cs.lamOf (cs.base t.lam) = cs.lamOf ρ := by
    rw [h1]
    exact cs.base_lam _ (h1 ▸ cs.lam_mem ρ)
  have lb' : cs'.lamOf (cs'.base t.lam') = cs'.lamOf ρ' := by
    rw [h2]
    exact cs'.base_lam _ (h2 ▸ cs'.lam_mem ρ')
  have gA := colGood X u _ _ (hL _ _ lb) (hL _ _ lb.symm)
  have gB := colGood X u' _ _ (hL' _ _ lb') (hL' _ _ lb'.symm)
  have e : ((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * ((cs'.h ρ' : X.B.I.Gf) * X.xu u') =
      (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h ρ : X.B.I.Gf) * X.xu u))⁻¹ *
        (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 *
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    group
  rw [e, levi_mul TR (good_mul _ (good_inv _ gA) hK) gB, levi_mul TR (good_inv _ gA) hK, levi_inv TR gA]

end LeviColsPf

end Formalism.L2.SG.NormCut
end
end

