module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpStmt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.NormCut

section ChiN

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def CongG (x y : VA X.B.I) : Prop := InAt X.B.I X.B.g X.B.g (x - y)

def ChiNBi : Prop :=
  ∀ κ k₁ k₂ : X.B.I.Gf, κ ∈ X.B.I.Kset → k₁ ∈ X.B.I.Kset → k₂ ∈ X.B.I.Kset →
    (∀ a, CongG X (X.B.I.fmat k₁⁻¹ *ᵥ X.f0 a) (X.f0 a)) →
    (∀ a, CongG X (X.B.I.fmat k₂ *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a)) →
    chiN X (k₁ * κ * k₂) = chiN X κ

variable {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def ColLatK {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (cs : ColSys X u what₂) : Prop :=
  ∀ ρ σ : cs.Cl, cs.lamOf ρ = cs.lamOf σ →
    ((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h σ : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset

def ColFix (u : D.what₂.Word) : Prop :=
  ∀ h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u,
    ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset →
      (∀ a, CongG X (X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.f0 a) (X.f0 a)) ∧
      (∀ a, CongG X (X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ nxt X.e0 X.z0 a)
        (nxt X.e0 X.z0 a))

theorem mem_Kset_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset) : x * y ∈ X.B.I.Kset := by
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx hy ⊢
  exact Subgroup.mul_mem _ hx hy

theorem mem_Kset_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : x⁻¹ ∈ X.B.I.Kset := by
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx ⊢
  exact Subgroup.inv_mem _ hx

variable {X}

theorem chiNIndep_of {u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hB : ChiNBi X) (hL : ColLatK cs) (hL' : ColLatK cs')
    (hF : ColFix X u) (hF' : ColFix X u') : ChiNIndep F0 F0' cs cs' := by
  intro t ρ ρ' hρ hρ' hk
  have hk' : _ ∧ _ := hk
  have hκ : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.B.I.Kset := hk'.1
  have hbase : cs.lamOf (cs.base t.lam) = cs.lamOf ρ := by rw [cs.base_lam _ t.mem, hρ]
  have hbase' : cs'.lamOf (cs'.base t.lam') = cs'.lamOf ρ' := by rw [cs'.base_lam _ t.mem', hρ']
  have h1 := hL _ _ hbase
  have h1i := hL _ _ hbase.symm
  have h2 := hL' _ _ hbase'.symm
  obtain ⟨hf1, -⟩ := hF _ _ h1i
  obtain ⟨-, hf2⟩ := hF' _ _ h2
  have hf1' : ∀ a, CongG X (X.B.I.fmat (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
      ((cs.h ρ : X.B.I.Gf) * X.xu u))⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
    rw [_root_.mul_inv_rev, inv_inv]
    exact hf1
  have key := hB _ _ _ hκ h1 h2 hf1' hf2
  have heq : kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt =
      ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h ρ : X.B.I.Gf) * X.xu u) *
        kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt *
        (((cs'.h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) := by
    simp only [kOf]
    group
  rw [heq, key]

end ChiN

section ColFixPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fmat_mul (x y : X.B.I.Gf) : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := by
  rfl

theorem fmat_inv_mul (x : X.B.I.Gf) : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
  rw [← fmat_mul X, inv_mul_cancel]
  rfl

theorem fixes_mul {x y : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) (hy : X.B.I.fmat y *ᵥ v = v) :
    X.B.I.fmat (x * y) *ᵥ v = v := by
  rw [fmat_mul X, ← Matrix.mulVec_mulVec, hy, hx]

theorem fixes_inv {x : X.B.I.Gf} {v : VA X.B.I} (hx : X.B.I.fmat x *ᵥ v = v) : X.B.I.fmat x⁻¹ *ᵥ v = v := by
  calc X.B.I.fmat x⁻¹ *ᵥ v = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ v) := by rw [hx]
    _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul X, Matrix.one_mulVec]

theorem mem_mL_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (m : ℕ) {y : VA X.B.I} (hy : y ∈ mL X.B.I m) :
    X.B.I.fmat x *ᵥ y ∈ mL X.B.I m := by
  have hx' : ∀ z, z ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ z ∈ X.B.I.Lf := hx
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, hw, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨X.B.I.fmat x *ᵥ w, (hx' w).1 hw, Matrix.mulVec_smul _ _ _⟩
  | zero =>
    rw [Matrix.mulVec_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [Matrix.mulVec_add]
    exact add_mem ha hb
  | smul c a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c ha

theorem congG_of_Kset {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) {δ : VA X.B.I} (hδ : InAt X.B.I X.B.g X.B.g δ) :
    InAt X.B.I X.B.g X.B.g (X.B.I.fmat x *ᵥ δ - δ) := by
  obtain ⟨c, hc, hcδ⟩ := hδ
  refine ⟨c, hc, ?_⟩
  rw [smul_sub, ← Matrix.mulVec_smul]
  exact sub_mem (mem_mL_of_Kset X hx _ hcδ) hcδ

private theorem congG_fmat_mulVec_of_fixed_of_inAt_sub {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset) {F v : VA X.B.I}
    (hF : X.B.I.fmat k *ᵥ F = F) (hv : InAt X.B.I X.B.g X.B.g (v - F)) :
    CongG X (X.B.I.fmat k *ᵥ v) v := by
  have h1 := congG_of_Kset X hk hv
  have e : X.B.I.fmat k *ᵥ v - v = X.B.I.fmat k *ᵥ (v - F) - (v - F) := by
    rw [Matrix.mulVec_sub, hF]
    abel
  show InAt X.B.I X.B.g X.B.g (X.B.I.fmat k *ᵥ v - v)
  rw [e]
  exact h1

private theorem inAt_neg' {x : VA X.B.I} (h : InAt X.B.I X.B.g X.B.g x) :
    InAt X.B.I X.B.g X.B.g (-x) := by
  obtain ⟨c, hc, hx⟩ := h
  refine ⟨c, hc, ?_⟩
  rw [smul_neg]
  exact neg_mem hx

theorem column_fixed_holds (u : D.what₂.Word) : ColFix X u := by
  intro h h' hk
  have hm : ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ h.2) h'.2
  have hfix : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) *ᵥ incl X.B.I y = incl X.B.I y := hm
  have hk_eq : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) =
      (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) * X.xu u := by group
  have hfixes : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y →
      X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ incl X.B.I y =
        incl X.B.I y := by
    intro y hy hxu
    rw [hk_eq]
    exact fixes_mul X (fixes_mul X (fixes_inv X hxu) (hfix y hy)) hxu
  refine ⟨fun a => ?_, fun a => ?_⟩
  · exact congG_fmat_mulVec_of_fixed_of_inAt_sub X hk
      (hfixes (crdOf X.B.I X.ιE X.bas (X.fY a)) (Or.inl (Or.inr ⟨a, rfl⟩)) (X.xu_fix u a).2)
      (X.basisApprox a).2
  · unfold Formalism.L2.SG.HidaSetting.nxt
    split_ifs with hlt
    · exact congG_fmat_mulVec_of_fixed_of_inAt_sub X hk
        (hfixes (crdOf X.B.I X.ιE X.bas (X.eX ⟨a.1 + 1, hlt⟩)) (Or.inl (Or.inl ⟨_, rfl⟩))
          (X.xu_fix u _).1)
        (X.basisApprox _).1
    · have hz := inAt_neg' X (X.xu_z u)
      rw [neg_sub] at hz
      refine congG_fmat_mulVec_of_fixed_of_inAt_sub X hk ?_ hz
      have e1 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ =
          (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) := by group
      rw [Matrix.mulVec_mulVec, ← fmat_mul X, e1, fmat_mul X, ← Matrix.mulVec_mulVec,
        hfix (crdOf X.B.I X.ιE X.bas (X.zu u)) (Or.inr rfl)]

end ColFixPf

section ChiNFinal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem chiNIndep_of_lat (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (hB : ChiNBi X) (hL : ColLatK cs)
    (hL' : ColLatK cs') : ChiNIndep F0 F0' cs cs' :=
  chiNIndep_of cs cs' hB hL hL' (column_fixed_holds X u) (column_fixed_holds X u')

end ChiNFinal

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhs (k r : ℕ) (μb : Measure (Mt k r)) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
    ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j)
      ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1)

def w0B (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := bigCell k r 1 1

def gBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UH (Hpk k r)) ρ

def wBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) :=
  {x | (fun i j => (w0B k r * Matrix.of x) i j) ∈ gBall k r ρ}

def gVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (UH (Hpk k r))) ρ)).toReal

def IterGauge : Prop :=
  ∀ (k r : ℕ) (μ μb : Measure (Mt k r)), IsGaugeOn (UH (Hpk k r)) μ → IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ C : NNReal, 0 < C ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂μ = (C : ℝ≥0∞) * rhs k r μb φ

def GaugeShift : Prop :=
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μ → ∀ ρ : ℝ, 0 < ρ →
    MeasurableSet (wBall k r ρ) ∧ μ (wBall k r ρ) = μ (gBall k r ρ)

def RhsLim : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    Tendsto (fun ρ : ℝ => (rhs k r μb ((wBall k r ρ).indicator 1)).toReal / gVol k r ρ) (𝓝[>] 0)
      (𝓝 ((2 : ℝ) ^ r)⁻¹)

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.WB

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhsW (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ζ : ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k (Tz k r z) (Tz k r z') ζ) *
    ∫⁻ h, ∫⁻ h', φ (fun i j => (Matrix.of h * Formalism.FourierDecayAlt.B2.embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW

def zeta0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ := ((2 * Real.sqrt (Tz k r z * Tz k r z') : ℝ) : ℂ)

def mBase (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Formalism.FourierDecayAlt.B2.embWb k r (μsec (zeta0 k r z z'))

def bBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) ρ

def mBall (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ρ : ℝ) :
    Set (Mt k r) :=
  {x | (fun i j => ((mBase k r z z' μsec)⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}

def bVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) ρ)).toReal

structure WbData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop where
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  haarW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW
  haarW' : Formalism.MainNotions.S.IsHaarOn (UWset k r z') μW'
  a_pos : 0 < a
  a'_pos : 0 < a'
  massW : μW Set.univ = ENNReal.ofReal a
  massW' : μW' Set.univ = ENNReal.ofReal a'
  sec : IsSection k r z z' μsec

def RankGauge : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μb μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec → IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ C : NNReal, 0 < C ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ m, φ m ∂μb = (C : ℝ≥0∞) * rhsW k r z z' μW μW' μsec φ

def GaugeShiftW : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μb μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec → Formalism.MainNotions.S.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → ∀ ρ : ℝ, 0 < ρ →
      MeasurableSet (mBall k r z z' μsec ρ) ∧ μb (mBall k r z z' μsec ρ) = μb (bBall k r ρ)

def RhsWLim : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    Tendsto (fun ρ : ℝ => (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ)
      (𝓝[>] 0) (𝓝 (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹)

end Formalism.L2.SG.Pf.WB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoS
section
noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Matrix

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LeviOntoSPf

variable {D : D7}

def fixV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : Set (VA X.B.I) :=
  Set.range (fun a => incl X.B.I (X.eR a)) ∪ Set.range (fun a => incl X.B.I (X.fR a)) ∪
    {X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)}

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) (u : D.what₂.Word)

def KappaOnto : Prop :=
  ∀ s : Iof TR, ∃ κ : X.B.I.Gf, κ ∈ X.B.I.Kset ∧ (∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) ∧ levi TR κ = s

variable (X)

def IsDualFrame (η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (b d : Fin D.R.k → VA X.B.I) : Prop :=
  η ∈ IntAf X.B.I.F X.B.I.E ∧ η * η = η ∧ η * X.ew = η ∧ ZMod' X.B.I X.B.g (X.ew - η) ∧
    (∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      η * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = η) ∧
    (∀ i, b i ∈ X.B.I.Lf ∧ d i ∈ X.B.I.Lf ∧ η • b i = b i ∧ sigA X.B.I η • d i = d i) ∧
    (∀ y ∈ fixV X u, ∀ i, hA X.B.I y (b i) = 0 ∧ hA X.B.I y (d i) = 0) ∧
    (∀ i j, hA X.B.I (d i) (b j) = if i = j then η else 0) ∧
    ∀ i j, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (b j) - if i = j then X.ew else 0) ∧
      ZMod' X.B.I X.B.g (hA X.B.I (d i) (X.bw j) - if i = j then X.ew else 0)

def DualFrame : Prop := ∃ η b d, IsDualFrame X u η b d

def SIdem : Prop :=
  ∃ ε ∈ IntAf X.B.I.F X.B.I.E, ε * ε = ε ∧ sigA X.B.I ε = ε ∧ ZMod' X.B.I X.B.g (1 - ε) ∧
    ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      ε * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ε

def FrameOfS : Prop := SIdem X → DualFrame X u

variable {X}

def LeviElt : Prop :=
  ∀ η b d, IsDualFrame X u η b d → ∀ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
    (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) →
    η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) →
    η • (C' * C) = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) →
    ∃ κ : X.B.I.Gf, κ ∈ X.B.I.Kset ∧ (∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) ∧
      ∀ v, leviM TR κ v = C.map (resT TR v)

def MatLift : Prop :=
  ∀ η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, η ∈ IntAf X.B.I.F X.B.I.E → η * η = η → η * X.ew = η →
    ZMod' X.B.I X.B.g (X.ew - η) →
    (∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      η * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = η) →
    ∀ s : Iof TR, ∃ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) ∧
      η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) ∧
      η • (C' * C) = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) ∧
      ∀ v, C.map (resT TR v) = ((s v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v))

theorem kappaOnto_of (hF : DualFrame X u) (hE : LeviElt TR u) (hL : MatLift TR) : KappaOnto TR u := by
  intro s
  obtain ⟨η, b, d, hfr⟩ := hF
  obtain ⟨C, C', hint, hCC, hC'C, hres⟩ :=
    hL η hfr.1 hfr.2.1 hfr.2.2.1 hfr.2.2.2.1 hfr.2.2.2.2.1 s
  obtain ⟨κ, hκK, hfix, hlev⟩ := hE η b d hfr C C' hint hCC hC'C
  refine ⟨κ, hκK, hfix, ?_⟩
  funext v
  have hM : leviM TR κ v = ((s v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
    rw [hlev, hres]
  have hu : IsUnit (leviM TR κ v).det := by
    rw [hM]
    exact Matrix.isUnits_det_units (s v)
  simp only [levi, dif_pos hu]
  exact Units.ext hM

theorem LeviOntoS_xu_inv_fix (y : Fin X.B.I.n → X.B.I.E)
    (hy : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := by
  have e : X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat (X.xu u) = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y
      = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y) := by rw [hy]
    _ = incl X.B.I y := by rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]

theorem LeviOntoS_conj_mem (κ : X.B.I.Gf) (hfix : ∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) :
    X.xu u * κ * (X.xu u)⁻¹ ∈ Hfin X u := by
  have hmul : ∀ a b : X.B.I.Gf, X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := by
    intro a b
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have he : ∀ a, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) :=
    fun a => (X.xu_fix u a).1
  have hf : ∀ a, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) :=
    fun a => (X.xu_fix u a).2
  show ∀ y ∈ fixSet X u, X.B.I.fmat (X.xu u * κ * (X.xu u)⁻¹) *ᵥ incl X.B.I y = incl X.B.I y
  intro y hy
  rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · rw [LeviOntoS_xu_inv_fix u _ (he a), hfix (incl X.B.I (X.eR a)) (Or.inl (Or.inl ⟨a, rfl⟩)), he a]
  · rw [LeviOntoS_xu_inv_fix u _ (hf a), hfix (incl X.B.I (X.fR a)) (Or.inl (Or.inr ⟨a, rfl⟩)), hf a]
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [hfix (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) (Or.inr rfl), Matrix.mulVec_mulVec, hinv,
      Matrix.one_mulVec]

theorem LeviOntoS_K_inv {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) : κ⁻¹ ∈ X.B.I.Kset := by
  exact Subgroup.inv_mem (Formalism.UG.stabGL X.B.I.Lf) hκ

variable {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem leviOntoS_of (hK : KappaOnto TR u) : LeviOntoS TR cs := by
  intro q s
  obtain ⟨κ, hκK, hfix, hlev⟩ := hK s
  have e1 : colDS (cs.h (cs.base q.1))
      (cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩) = κ := by
    simp only [colDS, Subgroup.coe_mul, Subgroup.coe_mk]
    group
  have e2 : colDS (cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩)
      (cs.h (cs.base q.1)) = κ⁻¹ := by
    simp only [colDS, Subgroup.coe_mul, Subgroup.coe_mk]
    group
  refine ⟨cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩, ?_, ?_, ?_⟩
  · rw [e1]
    exact hκK
  · rw [e2]
    exact LeviOntoS_K_inv hκK
  · rw [e1]
    exact hlev

theorem leviOntoS_of_steps (hS : SIdem X) (hFS : FrameOfS X u) (hE : LeviElt TR u) (hL : MatLift TR) : LeviOntoS TR cs :=
  leviOntoS_of (TR := TR) (u := u) (cs := cs) (kappaOnto_of (TR := TR) (u := u) (hFS hS) hE hL)

end LeviOntoSPf

end Formalism.L2.SG.Pf.NormSteps
end
end

