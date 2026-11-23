module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelFifth
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyKM
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.Pf.Carrier

namespace Formalism.L2.SG.Pf.Carrier.EnergyKM

theorem gam_eq (k r : ℕ) (κ δ : ℝ) : Formalism.FourierDecayAlt.D.GamLev k r κ δ 0 =
    (∏ a : Fin r, κ ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ))) / δ ^ (r + 1) := by
  have hI : ∀ f : ℕ → ℝ, ∏ l ∈ Finset.Ioc 0 r, f l = ∏ i : Fin r, f (i.val + 1) := by
    intro f
    have hset : Finset.Ioc 0 r = Finset.Ico (0 + 1) (r + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [Fin.prod_univ_eq_prod_range (fun i => f (i + 1)) r, Finset.range_eq_Ico,
      Finset.prod_Ico_add' f 0 r 1, hset]
  unfold Formalism.FourierDecayAlt.D.GamLev
  rw [Finset.prod_div_distrib, Finset.prod_const, Nat.card_Ioc, Nat.sub_zero,
    Finset.prod_Ioc_succ_top (Nat.zero_le r), hI]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, sub_self, mul_zero, zero_mul, neg_zero, zpow_zero, mul_one]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  have ha : a.val ≤ r := a.isLt.le
  simp only [Formalism.FourierDecayAlt.C.Mlev]
  push_cast [Nat.cast_sub ha]
  congr 1
  ring

theorem level_constant_mul_gamma (r k : ℕ) (g rd : ℝ) (hg : 0 < g) (hrd : 0 < rd) :
    (2 : ℝ) ^ (r + 1) * (∏ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^
      (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹) * Formalism.FourierDecayAlt.D.GamLev k r (Formalism.FourierDecayAlt.D.kapG g rd) (Formalism.FourierDecayAlt.D.deG g rd) 0 =
    rd ^ ((r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k)) * g ^ (3 * (r + 1)) := by
  rw [gam_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hper : ∀ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ *
      Formalism.FourierDecayAlt.D.kapG g rd ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ)) =
      rd ^ (4 * (r - a.val) * (2 * (r - a.val) + k)) := by
    intro a
    have hM : 2 * (r - a.val) * (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)) = 4 * (r - a.val) * (2 * (r - a.val) + k) := by
      unfold Formalism.QuantumDeterminants.Mdim
      rw [Nat.add_sub_cancel]
      ring
    rw [← pow_mul, hM, zpow_neg, zpow_natCast, ← mul_inv, ← mul_pow]
    unfold Formalism.FourierDecayAlt.D.kapG
    rw [show g / (2 * Real.pi) * (2 * Real.pi / (g * rd)) = rd⁻¹ by field_simp, inv_pow, inv_inv]
  rw [mul_div_assoc', mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun a _ => hper a),
    Finset.prod_pow_eq_pow_sum]
  unfold Formalism.FourierDecayAlt.D.deG
  rw [div_pow, div_div_eq_mul_div, pow_add]
  field_simp
  ring

theorem three_dvd (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, r = 3 * q ∨ r = 3 * q + 1 ∨ r = 3 * q + 2 := ⟨r / 3, by omega⟩
  · subst hq
    exact ⟨(3 * q + 1) * (24 * q ^ 2 + 10 * q + 1), by ring⟩
  · subst hq
    exact ⟨(3 * q + 2) * (2 * q + 1) * (12 * q + 7), by ring⟩
  · subst hq
    exact ⟨(q + 1) * (8 * (3 * q + 2) ^ 2 + 10 * (3 * q + 2) + 3), by ring⟩

theorem sum_closed (r k : ℕ) :
    3 * ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) = 4 * r * (r + 1) * (2 * r + 1) + 6 * k * r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem exp_eq (r k : ℕ) (hk : 1 ≤ k) :
    (r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      2 * r * (r + 1) * (k - 1) + (r + 1) * (8 * r ^ 2 + 10 * r + 3) / 3 := by
  have hs : ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 4 * (r - i) * (2 * (r - i) + k)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hj' : r - (r - 1 - j) = j + 1 := by omega
    simp only [hj']
  have h3 := sum_closed r k
  obtain ⟨W, hW⟩ := three_dvd r
  rw [hs, hW, Nat.mul_div_cancel_left W (by norm_num : 0 < 3)]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith [h3, hW]

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem kMatch_holds (P : Parts X u u') : EnergyPlace.KMatch P := by
  intro hg hrd hr hk hgpos hk1
  have hrdpos : 0 < Formalism.FourierDecayAlt.S6.rd D.host.E := by rw [hrd]; exact EnergyConst.rdE_pos'
  have hgpos' : (0 : ℝ) < P.S.g := by exact_mod_cast hgpos
  have hκ : 0 < Formalism.FourierDecayAlt.D.kapG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.kapG]; positivity
  have hδ : 0 < Formalism.FourierDecayAlt.D.deG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.deG]; positivity
  have hG : P.Gam0 ≠ 0 := by
    rw [Parts.Gam0, gam_eq]
    exact ne_of_gt (div_pos (Finset.prod_pos fun a _ => zpow_pos hκ _) (pow_pos hδ _))
  have key := level_constant_mul_gamma P.S.G.r P.S.G.k P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) hgpos' hrdpos
  rw [exp_eq _ _ hk1] at key
  rw [EnergyConst.Kexp, eq_div_iff hG]
  refine key.trans ?_
  rw [hrd, hg, hr, hk]
  rfl

end Formalism.L2.SG.Pf.Carrier.EnergyKM
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyMS
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain

namespace Formalism.L2.SG.Pf.Carrier.EnergyMS

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.Carrier.EnergyConst Formalism.L2.SG.Pf.Carrier.EnergyConst2 Formalism.L2.SG.TypedSets Function

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def dN (v : PlX X) : ℝ := ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) : ℕ) : ℝ)


open Classical in
def nT (v : PlX X) : ℝ :=
  if TypAt X v then ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1

end Defs

def MSOrd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, ¬ TypAt X v → localVolumeUnit X ψ v = dN X v ^ e1 D * ZZX X u u' ψ v

def MSTyp : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, TypAt X v → 0 < ZZX X u u' ψ v →
      localVolumeUnit X ψ v = dN X v ^ e1 D * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) *
        ZZX X u u' ψ v

def DiffProd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    HasFiniteMulSupport (dN X) ∧ ∏ᶠ v, dN X v = |((NumberField.discr X.B.I.F : ℤ) : ℝ)|

def DiscRd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f

def TypNorm : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    ∏ p : TypX X, ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ D.R.f

theorem lemmaMSStd_of (hO : MSOrd) (hT : MSTyp) (hD : DiffProd) (hR : DiscRd) (hN : TypNorm)
    {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : LemmaMSStd X u u' ψ := by
  classical
  intro hψ hstd hC
  set k := (D.R.rS + 1) * (2 * D.R.rS + 3) with hk
  have hZpos : ∀ v, 0 < ZZX X u u' ψ v := fun v => (hC.1 v).2.2.1
  have hU00m : Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) := hC.2.2.2.1
  have hZm : Multipliable (ZZX X u u' ψ) := hC.2.2.2.2.2.1
  have hloc : ∀ v, localVolumeUnit X ψ v = (dN X v ^ e1 D * nT X v) * ZZX X u u' ψ v := by
    intro v
    by_cases hv : TypAt X v
    · rw [hT D X u u' ψ hψ hstd v hv (hZpos v)]
      simp only [nT, if_pos hv]
    · rw [hO D X u u' ψ hψ hstd v hv]
      simp only [nT, if_neg hv, mul_one]
  obtain ⟨hDf, hDp⟩ := hD D X

  set s : Set (PlX X) := ↑(Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) with hs
  have hnTs : Function.mulSupport (nT X) ⊆ s := by
    intro v hv
    by_contra h
    exact hv (by unfold nT; exact if_neg (show ¬ TypAt X v from h))
  have hnTf : HasFiniteMulSupport (nT X) := (Finset.finite_toSet _).subset hnTs
  have hAf : HasFiniteMulSupport (fun v => dN X v ^ e1 D * nT X v) := (hDf.pow _).mul hnTf

  have h1 : (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = ∏' v, localVolumeUnit X ψ v := by
    have hsm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : s → PlX X)) := Multipliable.of_finite
    have hscm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : ↑sᶜ → PlX X)) := hU00m
    rw [← Multipliable.tprod_mul_tprod_compl hsm hscm, mul_comm]
    congr 1
    rw [tprod_fintype]
    rfl

  have h2 : ∏' v, localVolumeUnit X ψ v = (∏ᶠ v, (dN X v ^ e1 D * nT X v)) * ∏' v, ZZX X u u' ψ v := by
    rw [tprod_congr hloc, Multipliable.tprod_mul (multipliable_of_hasFiniteMulSupport hAf) hZm,
      tprod_eq_finprod hAf]

  have h3 : (∏ᶠ v, (dN X v ^ e1 D * nT X v)) =
      D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * k) := by
    have hDpow : HasFiniteMulSupport (fun v => dN X v ^ e1 D) := hDf.pow _
    rw [finprod_mul_distrib hDpow hnTf, ← finprod_pow hDf, hDp, hR D X, ← pow_mul]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (nT X) hnTs, pow_mul, ← hN D X, ← Finset.prod_pow]
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun p _ => ?_
    unfold nT
    exact if_pos (show TypAt X p.1 from p.2)
  unfold LemmaMS
  show (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = _ * (∏' v : PlX X, ZZX X u u' ψ v)
  rw [h1, h2, h3]

end Formalism.L2.SG.Pf.Carrier.EnergyMS
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPf
section
noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace DFrameAtPf

theorem matW_liftU {n k : ℕ} {ε : Fin n → Bool} (wb : Fin k → Fin n → ℂ)
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    (Matrix.of fun a b => hJ ε (wb a) (uMat (liftU wb hon U hU) *ᵥ wb b)) = U := by
  ext a b
  rw [Matrix.of_apply, liftU_mulVec]
  have h1 := congrFun (wCoord_liftM hon U (wb b)) a
  have h2 : wCoord ε wb (wb b) = Pi.single b 1 := by
    funext i
    show hJ ε (wb i) (wb b) = _
    rw [hon, Pi.single_apply]
  rw [h2, mulVec_single_one] at h1
  exact h1

end DFrameAtPf

open DFrameAtPf

variable {D : D7}

theorem dFrame_any (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (s0 sc : ℝ) (hsc : sc ≠ 0)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (γ : X.B.I.Ginf) (hG : ∀ v, 0 < GX X u u' s0 γ v) :
    ∃ h h', IsDFrameX X u u' sc i0 i0 γ h h' := by
  have hloc : ∀ v, ∃ h h' : Matrix (Fin D.R.k) (Fin D.R.k) ℂ,
      IsDFrame (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat (γ v)) (uMat ((γ v)⁻¹)) (X.wfr u v)
        (X.wfr u' v) (i0 v) (i0 v) h h' := fun v =>
    dframe_loc (frU X u v) (frU X u' v) rfl (i0 v) (γ v) sc hsc
      (gv_pos_scale (Tw u) (Tw u') (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
        (uMat (γ v)) s0 sc hsc (hG v))
  choose H H' hH using hloc
  have hon : ∀ uu v, ∀ i j, hJ (X.B.I.ε v) (X.wfr uu v i) (X.wfr uu v j) = if i = j then 1 else 0 :=
    fun uu v => X.wfr_on uu v
  have hmem : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ),
      (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v) : X.B.I.Ginf) ∈ HsetU X uu := by
    intro uu U hU v x hx
    show uMat (liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    rw [liftU_mulVec]
    refine liftM_fix _ _ fun i => ?_
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact (frU X uu v).we i a
    · exact (frU X uu v).wf i a
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X uu v).wz i
  have hmat : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ) v,
      Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr uu v) v (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) = U v :=
    fun uu U hU v => matW_liftU (X.wfr uu v) (hon uu v) (U v) (hU v)
  refine ⟨fun v => liftU (X.wfr u v) (hon u v) (H v) (hH v).1,
    fun v => liftU (X.wfr u' v) (hon u' v) (H' v) (hH v).2.1,
    hmem u H (fun v => (hH v).1), hmem u' H' (fun v => (hH v).2.1), fun v => ?_⟩
  rw [hmat u H (fun v => (hH v).1) v, hmat u' H' (fun v => (hH v).2.1) v]
  exact hH v

theorem dual_frame_at_places (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : DFrameAt X u u' sc i0 i0 := by
  intro hsc w _ hG
  exact dFrame_any X u u' D.host.rdE sc hsc.ne' i0 (gamW X u u' w) hG

end Formalism.L2.SG.Pf.Carrier
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelMeasure
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.ModelMeasure

open Formalism.MainNotions.BigCellDensity

theorem mp_modelK {r k : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1)) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {δ : Formalism.FourierDecayAlt.B.Mat k r} (hδ : δ ∈ Formalism.FourierDecayAlt.B.GV k r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx (wPt pN), ‖d (wPt pN q.1.1)‖ = ‖d (wPt pN q.1.2)‖)
    (hZ : Zhat k r Ds.z Ds.z' δ = Formalism.FourierDecayAlt.C2.monoP (wPt pN) d) (μ : Measure (Mt k r))
    (hconc : μ {x | Matrix.of x ∉ Formalism.FourierDecayAlt.C6.Rset δ} = 0) (c : ℝ≥0∞)
    (hmap : μ.map (fun x => Formalism.MainNotions.S.rootCoords k r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ))) = c • volume) :
    μ = c • Formalism.FourierDecayAlt.D.muR Ds δ (wPt pN) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt Ds.k_pos)
  exact Formalism.L2.SG.flagStabilizerModel.mp_model pN Ds hδ hd hdm hZ μ hconc c hmap

end Formalism.L2.SG.ModelMeasure

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExistsAlt
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (sOf hF))

theorem pvalForm_exists' (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists W hI (Formalism.L2.SG.Pf.WittFlags.WRowIso_holds D) hC hK hN

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WRowPinHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem WRowPin_holds {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} (hF : FinX Y)
    (hI : SIso D.s (sOf hF)) (W : Formalism.L2.SG.TermTieOf.WittDat X) (H : Formalism.L2.SG.TermTieOf.TieHyp W hI)
    (A : Formalism.L2.SG.TermTieOf.AmpDat X) (hV : Formalism.L2.SG.TermTieOf.PvalForm W hI A) :
    Formalism.L2.SG.LoopTieOf.WRowPin hF hI (Formalism.L2.SG.TermTieOf.termTieOf W hI H A hV) := by
  intro u u' p s hs
  have h2 : (Formalism.L2.SG.TermTieOf.tc hI (D.s.pfst p)).lam = s.lam :=
    (congrArg (fun t => t.lam) hs).symm
  show Formalism.MainNotions.S.wRow D (Formalism.L2.SG.TermTieOf.FlagOfWord W u) (Formalism.L2.SG.TermTieOf.lamOf W hI (D.s.pfst p)) = _
  unfold Formalism.L2.SG.TermTieOf.lamOf
  rw [h2]
  exact WRowIso_holds D (W.δ u) (W.isom u) (X.Fu u) s.lam

end Formalism.L2.SG.Pf.WittFlags
end
end

