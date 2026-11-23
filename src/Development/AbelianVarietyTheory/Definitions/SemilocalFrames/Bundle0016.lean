module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinkUnique
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG NumberField IsDedekindDomain Matrix Formalism.L2.SG.HidaSetting Formalism.L2.SG.ColDict
open Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct

namespace GlobalTheory.St.G.LinkCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)

theorem embA_rat (hι : GlobalTheory.St.IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E) :
    embA X wt ιA (fun j => inclE (F := D.host.F) (Ad D.host.F) (x j)) =
      incl X.B.I (X.crd (∑ j, x j • qFr wt j)) := by
  have h1 : ∀ a : D.host.E, ιA.symm (inclE (F := D.host.F) (Ad D.host.F) a) =
      inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm a) := by
    intro a
    rw [RingEquiv.symm_apply_eq, hι.1, RingEquiv.apply_symm_apply]
  funext i
  simp [embA, qA, incl, HidaSetting.crd, crdOf, h1, Finset.sum_apply]

end GlobalTheory.St.G.LinkCheck

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampQ {Cl Nu : Type} (Q : Prop → Prop) (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ :=
  haveI := L.fP
  ∑ A ∈ L.Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then L.aN p (d p) else L.aZ p (d p))

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def setQ (Q : Prop → Prop) : Set (TauC Y u u') := {t | (Y.tO u u').G t ≠ 0 ∧ Q (¬ (Y.tO u u').gener t)}

def FamQ {Cl : Type} (Q : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) : Prop :=
  TS = setQ Y u u' Q ∧ GlobalTheory.Unfold.ClsRow TS cls ∧
    ∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t'

def HasPt (TS : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) : Prop :=
  ∃ t ∈ TS, (Y.tO u u').vec t ≠ 0 ∧ ptPN t = γ

def grpF {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :=
  ∑' t : TauC Y u u', (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν}).indicator (Y.tO u u').vec t

def a2F {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) : ℝ :=
  ‖grpF Y u u' TS cls c γ ν‖ ^ 2 / J2of Y u u' νq γ

def gCls (t : TauC Y u u') : Set (TauC Y u u') :=
  {t' | t' ∈ (Y.tO u u').genSet ∧ (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t ∧ (Y.tO u u').s0 t t' = 1 ∧
    (Y.tO u u').scal t t'}

end GlobalTheory.SnFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Obj
variable {D : D7} {X : HidaSetting D}

def DbL (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := ∏ l ∈ k2ends D j δ, ((Nloc (ddS D) D.R.rS l (δ l) : ℚ) : ℝ)

def AmpAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Cs C : ℝ) : Prop :=
  ∀ t ∈ relSet Y u, ‖(Y.tO u u).vec t‖ ≤
    Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))

def PairsAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2) ≤
      massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')
end Obj

def TypeP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH Cs C Ch Cp

def AmpP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH : ℝ, 0 ≤ CH ∧ ∀ Cs : ℝ, 0 ≤ Cs →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → AmpAt large₂ Y u CH Cs C

def PairsP : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Ch Cp : ℝ, 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → PairsAt large₂ Y u CH Ch Cp

def NFExC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ t ∈ relSet Y u,
    ∃ N, AdT t N ∧ N.j = jT t ∧ N.T = Tu D u

def LabC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : GTu Y u) N, AdT t N →
    N.j = jT t ∧ N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = fun l => star (labT t l)

def PerRowC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
      (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧
        labT p.2 = δ'') →
      ENNReal.ofReal (∑ p ∈ S, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) ≤
        ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
          (((GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x x').encard : ℕ∞) : ℝ≥0∞) *
            ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
              GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x')

def ProdC : Prop :=
  ∀ Cs : ℝ, 0 ≤ Cs → ∃ C₁ : ℕ, 1 ≤ C₁ ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1)
    (CH : ℝ), Std D large₂ → 0 ≤ CH → 40 * D.R.rS ^ 4 ≤ D.R.k → 5 * D.R.rS ≤ D.R.k → ∀ t ∈ relSet Y u, ∀ hj : jT t ≤ D.R.rS, 1 ≤ jT t →
    ∃ (De : D.what₂.Tau → ℝ) (P : ℝ), 0 < P ∧ k2Del D (jT t) (labT t) = P ^ 2 ∧
      (∀ τ, GlobalTheory.Amp.DeOK D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (De τ)) ∧
      ∏ τ, GlobalTheory.Amp.degBd D.R.k D.R.rS (jT t) (C₁ * D.R.k * D.R.rS) (H1C large₂ CH) (De τ)
          (GlobalTheory.Amp.Dj D.R.k D.R.rS hj (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ))
          (GlobalTheory.Amp.sgV D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (H1C large₂ CH)) ≤
        (16 * Real.pi * Real.exp 1 / D.R.k) ^ (jT t * (D.R.k - 1 - jT t) * D.R.f) * (P ^ (D.R.k - 1 - jT t))⁻¹ *
          (8 * D.R.rS * H1C large₂ CH) ^ (80 * D.R.rS ^ 4 * D.R.f) * k2S D (H1C large₂ CH) (jT t) (labT t) ^ (-(Cs * D.R.k))
end GlobalTheory.TypeAsm
end
end

