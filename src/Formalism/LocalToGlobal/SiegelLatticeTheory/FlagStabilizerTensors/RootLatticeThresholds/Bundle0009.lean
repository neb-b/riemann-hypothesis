module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierParts
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVtPtSome
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

variable {D : D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
  [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wq x)]

theorem ptSome_of (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (hr : S.G.r = D.R.rS) : PtSome S := by
  intro p hp
  have hL : Formalism.L2.S.IsPtL (Formalism.L2.SG.DataInst.signPt D.R.rS p) (D.R.rS + 1) := by
    refine ⟨?_, ?_⟩
    · rw [show Formalism.L2.SG.DataInst.signPt D.R.rS p = Formalism.L2.SG.DataInst.signAux D.R.rS 1 p from rfl,
        Formalism.L2.SG.DataInst.sign_list_fst]
      have := hp.1
      unfold Formalism.FourierDecayAlt.TB.level at this
      rw [this, hr]
    · refine (Formalism.L2.SG.DataInst.sign_list_mem_nonzero D.R.rS 1 p).2 fun c hc => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
      exact hp.2 k hk
  refine ⟨(Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm ⟨Formalism.L2.SG.DataInst.signPt D.R.rS p, hL⟩, ?_⟩
  unfold Formalism.L2.SG.RealObj.ptOfL Formalism.L2.SG.DataInst.ptOfList
  rw [dite_eq_left hL]

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierBridge
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.DFrameBridge (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  P.FromX → P.Base i0 i0' → ∀ γ h h' : X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' γ h h' → ∀ v,
    Formalism.FourierDecayAlt.D.IsDFrame (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v))
      (trG (P.Q v) (P.Qi v) ((h⁻¹ * γ * h') v))

end Formalism.L2.SG.Pf.Carrier
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergy
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.Gam0 (P : Parts X u u') : ℝ :=
  Formalism.FourierDecayAlt.D.GamLev P.S.G.k P.S.G.r (Formalism.FourierDecayAlt.D.kapG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E))
    (Formalism.FourierDecayAlt.D.deG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0

def Parts.EnergyModel (P : Parts X u u') : Prop :=
  P.Built → (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace P.S P.T P.f P.χ v (P.L v) (P.j v) (P.lam v) P.c (P.Cm v) (P.σ v)) →
    ∀ v, Formalism.FourierDecayAlt.JCT.jvModel P.S P.j P.Cm v = (Formalism.FourierDecayAlt.B.normSq (P.T v).base (P.f v)).toReal / P.Gam0

def Parts.EnergyNorm (P : Parts X u u') (jn : ℝ) : Prop :=
  (∏ v, (Formalism.FourierDecayAlt.B.normSq (P.T v).base (P.f v)).toReal / P.Gam0) = jn

end Formalism.L2.SG.Pf.Carrier
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJoint
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def DFrameAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∃ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h'

def Parts.JointTensor (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ x : ∀ v, X.Vloc u' v,
      (X.piU u h⁻¹) ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.piU u' h' (X.tensU u' x))) =
        X.tensU u (fun v => P.eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
            ((P.eQ v).symm (x v))))

end Formalism.L2.SG.Pf.Carrier
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConjDiEqSelf
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.MainNotions.S.Pv.Frames

variable {k r : ℕ}

private lemma apply_eq_ite_of_mulVec_bvec_eq' {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (hj : h *ᵥ bvec j = bvec j) (i : Fin n) : h i j = if i = j then 1 else 0 := by
  have e := congrFun hj i
  simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using e

private lemma Hpk_apply_sig_ne_zero {n : ℕ} {h H : Matrix (Fin n) (Fin n) ℂ} (hU : hᴴ * H * h = H) {p q : Fin n}
    (hcol : ∀ l, h l p = if l = p then 1 else 0) (hrow : ∀ m, H p m = if m = q then 1 else 0)
    (j : Fin n) : h q j = if q = j then 1 else 0 := by
  have hcolS : ∀ l, star (h l p) = if l = p then 1 else 0 := by
    intro l; rw [hcol]; split_ifs <;> simp
  have e1 : ∀ m, (hᴴ * H) p m = H p m := by
    intro m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcolS, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e : (hᴴ * H * h) p j = H p j := by rw [hU]
  rw [Matrix.mul_apply] at e
  simp only [e1, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  rw [e]
  by_cases hq : q = j
  · subst hq; simp
  · simp [hq, Ne.symm hq]

private lemma Hpk_esI_apply_eq_ite_eI (a : Fin r) (m : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) m = if m = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hm := m.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma Hpk_eI_apply_eq_ite_esI (a : Fin r) (m : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) m = if m = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hm := m.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem fix_gen (d : Fin (2 * r + k + 1) → ℂ) (d0 : ℂ) (hmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = d0)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : h ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, h *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ h *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i j : Fin (2 * r + k + 1)) (hne : h i j ≠ 0) : d i = d j := by
  have hUe : hᴴ * Hpk k r * h = Hpk k r := hU
  have colE : ∀ a : Fin r, ∀ l, h l (eI k r a) = if l = eI k r a then 1 else 0 :=
    fun a => apply_eq_ite_of_mulVec_bvec_eq' h _ (hfix a).1
  have colS : ∀ a : Fin r, ∀ l, h l (esI k r a) = if l = esI k r a then 1 else 0 :=
    fun a => apply_eq_ite_of_mulVec_bvec_eq' h _ (hfix a).2
  have rowE : ∀ a : Fin r, ∀ q, h (eI k r a) q = if eI k r a = q then 1 else 0 :=
    fun a => Hpk_apply_sig_ne_zero hUe (colS a) (Hpk_esI_apply_eq_ite_eI a)
  have rowS : ∀ a : Fin r, ∀ q, h (esI k r a) q = if esI k r a = q then 1 else 0 :=
    fun a => Hpk_apply_sig_ne_zero hUe (colE a) (Hpk_eI_apply_eq_ite_esI a)
  have out : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) →
      (∀ q, h p q = if p = q then 1 else 0) ∧ (∀ l, h l p = if l = p then 1 else 0) := by
    intro p hp
    rcases hp with hp | hp
    · have e : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
      rw [← e]
      exact ⟨rowE _, colE _⟩
    · have hp2 := p.isLt
      have e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p :=
        Fin.ext (show 2 * r + k - (2 * r + k - p.val) = p.val by omega)
      rw [← e]
      exact ⟨rowS _, colS _⟩
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [(out i hi).1 j] at hne
    by_cases hij : i = j
    · rw [hij]
    · exact absurd (if_neg hij) hne
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [(out j hj).2 i] at hne
      by_cases hij : i = j
      · rw [hij]
      · exact absurd (if_neg hij) hne
    · push_neg at hi hj
      rw [hmid i hi.1 hi.2, hmid j hj.1 hj.2]

variable {δ : ℝ}

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
section
noncomputable section

open scoped Classical
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LTL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lemmas

open scoped ComplexConjugate

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  first
  | exact inner_self_nonneg (𝕜 := ℂ) (x := A (stdOrthonormalBasis ℂ Wq i))
  | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; positivity)

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (c • A) = Complex.normSq c * hsNormSq A := by
  unfold hsNormSq hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, ← mul_assoc]
  rw [← Finset.mul_sum]
  first
  | rw [Complex.mul_conj]
  | rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.re_ofReal_mul]

theorem isQuotMeas_smul {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : IsQuotMeas μG μS ν) {c : ENNReal}
    (h0 : c ≠ 0) (hT : c ≠ ⊤) : IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf]
  simp only [MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  rw [MeasureTheory.lintegral_const_mul' c _ hT, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

theorem locJ_smul {k r : ℕ} {W : LocW k r} (A : LocS W) (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (c : ENNReal)
    (γ : MatKR k r) : A.J (c • ν) γ = ((c.toReal : ℝ) : ℂ) • A.J ν γ := by
  simp only [Formalism.MainNotions.S.LocS.J, Formalism.MainNotions.S.ampJ, MeasureTheory.integral_smul_measure]
  rw [Complex.coe_smul]
  exact smul_comm _ _ _

end Lemmas

section Tr

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem star_dot_conjT {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem hJ_smul_real {n : ℕ} (ε : Fin n → Bool) (r s : ℝ) (x y : Fin n → ℂ) :
    hJ ε ((r : ℂ) • x) ((s : ℂ) • y) = ((r * s : ℝ) : ℂ) * hJ ε x y := by
  simp only [hJ]
  simp [Matrix.mulVec_smul, smul_eq_mul]
  try push_cast
  try ring

theorem frS_pow (D : D7) (a : Fin (D.R.rS + 1)) (h : a.val < D.R.rS) :
    frS D ^ (D.R.rS - a.val) = ((rhoF D a : ℝ) : ℂ) := by
  have hk : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    have hpi := Real.pi_pos.ne'
    rcases eq_or_ne D.host.rdE 0 with h0 | h0
    · rw [h0]
      simp
    · field_simp
      try ring
  have hnn : 0 ≤ D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hc : ((D.R.rS - a.val : ℕ) : ℝ) = (D.R.rS : ℝ) - (a.val : ℝ) := by
    rw [Nat.cast_sub h.le]
  unfold frS rhoF
  rw [hk, ← hc, Real.rpow_neg hnn, Real.rpow_natCast, ← inv_pow]
  push_cast
  try ring

theorem rhoF_last (D : D7) : rhoF D (Fin.last D.R.rS) = 1 := by
  simp [rhoF, Fin.val_last]

theorem Q_fvec (u : D.what₂.Word) (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • rv X.B.I (vOf X τ) (X.crd ((X.Fu u).fvec a)) := by
  obtain ⟨_, hQQi, _, hEv⟩ := C.isT τ
  by_cases h : a.val < D.R.rS
  · have h1 := (hEv ⟨a.val, h⟩ ⟨a.val, h⟩ rfl).1
    have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    have h2 : (X.Fu u).fvec (Fin.castSucc ⟨a.val, h⟩) = X.eX ⟨a.val, h⟩ := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact congrFun (X.Fu_e u) _
    rw [← ha] at h2
    rw [h2, ← frS_pow D a h, Formalism.QuantumDeterminants.fvec, dite_eq_left h, Formalism.QuantumDeterminants.bvec, h1]
    rfl
  · have ha : a = Fin.last D.R.rS := Fin.ext (by have := a.isLt; simp; omega)
    subst ha
    have h3 : (X.Fu u).fvec (Fin.last D.R.rS) = X.zu u := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact X.flagZVector u
    rw [h3, rhoF_last, Formalism.QuantumDeterminants.fvec, dite_eq_right h]
    simp only [zB, Complex.ofReal_one, one_smul]
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rfl

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  exact D.eTau.nonempty

theorem trG_mem {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (H : Matrix (Fin m) (Fin m) ℂ) (hQQi : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (g : Formalism.REAL.UJ ε) :
    Formalism.L2.SG.RealObj.trG Q Qi g ∈ Formalism.QuantumDeterminants.UH H := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := by
    first
    | exact g.2
    | (unfold uMat; exact g.2)
    | simpa [uMat] using g.2
  have h1 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Qiᴴ * (Qᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Q * (Qi * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
  have h3 : ∀ X : Matrix (Fin n) (Fin m) ℂ,
      (uMat g)ᴴ * (Formalism.REAL.Jm ε * (uMat g * X)) = Formalism.REAL.Jm ε * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  show (Qi * uMat g * Q)ᴴ * H * (Qi * uMat g * Q) = H
  rw [← hH]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, h1, h2, h3]

theorem tz_zB (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) = ((Tu D u : ℕ) : ℝ) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hT' : (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) =
      -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [show X.zR u = X.crd (X.zu u) from rfl, Formalism.L2.SG.Pf.Level.toV_crd, X.zu_norm]
  have hι := Formalism.L2.SG.Pf.Level.iota_hE (X := X) (X.zR u) (X.zR u)
  rw [hT'] at hι
  have hJv := Formalism.L2.SG.Pf.Level.hJ_rv (X := X) (vOf X τ) (X.zR u) (X.zR u)
  rw [X.φ_eq, hι] at hJv
  simp only [hJ, map_neg, map_natCast] at hJv
  unfold Formalism.QuantumDeterminants.Tz zB Formalism.QuantumDeterminants.herm
  rw [← hH, Matrix.mulVec_mulVec,
    Matrix.mul_assoc ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (C.Q τ) (C.Qi τ), hQQi,
    Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec, hJv]
  simp [Tu]

end Tr

end Formalism.L2.SG.Pf.LTL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairMeasScaleN
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ} {κ τ : ℝ}

theorem phiP_stabAct (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) (x : PairSp k r) :
    phiP k r κ τ (stabAct g a x) = stabAct (cj k r κ τ g) (cj k r κ τ a) (phiP k r κ τ x) := by
  obtain ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩ := x
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · show (fun i j => cj k r κ τ (a * Matrix.of x2) i j) =
      fun i j => (cj k r κ τ a * Matrix.of (cjT k r κ τ x2)) i j
    rw [cj_mul hκ hτ]
    rfl
  · show (fun i j => cj k r κ τ (g⁻¹ * a * g * Matrix.of x4) i j) =
      fun i j => ((cj k r κ τ g)⁻¹ * cj k r κ τ a * cj k r κ τ g * Matrix.of (cjT k r κ τ x4)) i j
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
    rfl

theorem isOrbQuot_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (h : IsOrbQuot L g μR ν) :
    IsOrbQuot (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') (cj k r κ τ g)
      (μR.map (cjT k r κ τ)) (ν.map (phiP k r κ τ)) := by
  intro f hf
  rw [pairMeas_trD hκ hτ]
  have exp_product_square_inv : (pairMeas L).map (phiP k r κ τ) = (pairMeas L).map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [exp_product_square_inv, lintegral_map_equiv]
  rw [h (fun x => f (phiE hκ hτ x)) (hf.comp (phiE hκ hτ).measurable)]
  have eP : ν.map (phiP k r κ τ) = ν.map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [eP, lintegral_map_equiv]
  refine lintegral_congr (fun x => ?_)
  have eT : μR.map (cjT k r κ τ) = μR.map (cjE (k := k) (r := r) hκ hτ) := rfl
  rw [eT, lintegral_map_equiv]
  refine lintegral_congr (fun a => ?_)
  show f (phiP k r κ τ (stabAct g (Matrix.of a) x)) =
    f (stabAct (cj k r κ τ g) (Matrix.of (cjT k r κ τ a)) (phiP k r κ τ x))
  rw [phiP_stabAct hκ hτ]
  rfl

theorem isRelStab_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} (h : IsRelStab L g) :
    IsRelStab (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') (cj k r κ τ g) := by
  intro a ha
  obtain ⟨b, rfl⟩ : ∃ b, a = cj k r κ τ b := ⟨cjI k r κ τ a, (cj_cjI hκ hτ a).symm⟩
  have hb : b ∈ RStab k r g := (cj_mem_RStab_iff hκ hτ g b).1 ha
  have e : (cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g = cj k r κ τ (g⁻¹ * b * g) := by
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
  show psi k r ((τ : ℂ) • L.z) ((κ : ℂ) * L.c) (cj k r κ τ b) =
    psi k r ((τ : ℂ) • L.z') ((κ : ℂ) * L.c) ((cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g)
  rw [e, psi_cj hκ hτ L.hz.1, psi_cj hκ hτ L.hz'.1]
  exact h b hb

theorem isOrbQuot_smul {L L' : LocBessel k r} {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)}
    (h : IsOrbQuot L g μR ν) (t : ENNReal) (hP : pairMeas L' = t • pairMeas L) : IsOrbQuot L' g μR (t • ν) := by
  intro f hf
  rw [hP, lintegral_smul_measure, lintegral_smul_measure, h f hf]

theorem pairMeas_scaleN {L L' : LocBessel k r} (hW : L'.μW = L.μW) (hW' : L'.μW' = L.μW') (t : ENNReal)
    (hN : L'.μN = t • L.μN) : pairMeas L' = (t * t) • pairMeas L := by
  haveI : SFinite L.μN := sFinite_haarLie _ _
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  unfold pairMeas
  rw [hW, hW', hN, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_left, smul_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

