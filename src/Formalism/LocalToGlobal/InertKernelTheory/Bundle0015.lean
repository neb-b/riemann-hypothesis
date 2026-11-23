module

public import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsSharp
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSharpWeights

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

end Gen

def SharpWtIs : Prop :=
  ∀ (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ), j < D.R.m →
    ∀ (τ : D.what₂.Tau) (r : Fin (D.R.N j)),
      ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2

end Formalism.L2.KerInert.SecondKernelSharpWeights
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelDifference

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

def entQ (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i)
    (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) : (D.chTw u μ).cls (i + 1) → (D.chTw u μ).Y (i + 1) → ℂ :=
  fun c' y' =>
    (((GL3Theta.rhoOf D (t.O u μ).mt i ((t.O u μ).dt i c) : ℂˣ) : ℂ) *
        ((GL3Theta.rhoOf' D (t.O u μ).mt i ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
      ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D (t.O u μ).dgen Q ((t.O u μ).frm (i + 1) y'))
          ((t.rd u μ).Th t.seam t.amb i c c'))

def KernelDifferenceRationalAtLevel {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (cK : Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, SharpQ t ex.tw u μ j x Q →
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      Rd j c' L' (entQ t u μ j (cls j La.1 La.2) (Q (cls j La.1 La.2))) =
        cK • Y.DelF j (cmp j x La.1 La.2) (Sr j La (c', L'))

section Frame

open MvPolynomial

def polDY (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) :
    MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ) :=
  aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
    C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
      X ((k.1, b, k.2.1) : GL3Theta.Idx D N N')) Q

def framePol (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    MvPolynomial (GL3Theta.FrV D N') ℂ :=
  ∑ α ∈ (polDY D s Q (N' := N')).support,
    AddMonoidAlgebra.coeff (polDY D s Q) α * C ((α.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G α)

end Frame

def ApplyFrame : Prop :=
  ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ),
    GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G = GL3Theta.evFr D (framePol D s Q G) y'

def EntQFrame : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ)
    (c : (D.chTw u μ).cls i) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (c' : (D.chTw u μ).cls (i + 1))
    (y' : (D.chTw u μ).Y (i + 1)),
    entQ t u μ i c Q c' y' =
      (((GL3Theta.rhoOf D (t.O u μ).mt i ((t.O u μ).dt i c) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt i ((t.O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
          frPoly (t.O u μ) (i + 1) (framePol D (t.O u μ).dgen Q ((t.rd u μ).Th t.seam t.amb i c c')) y')

def DelPolAt {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1))
    (ΦR : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →
      XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (cK : Y.Kc) : Prop :=
  ∀ La ∈ Y.Rep j, ∀ (x : ((ex.tw.fm u μ).lat j).V) Q, SharpQ t ex.tw u μ j x Q →
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      ΦR j c' L' ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (cls j La.1 La.2)) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (κ j c' L')) : ℂˣ) : ℂ)) •
          framePol D (t.O u μ).dgen (Q (cls j La.1 La.2))
            ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L'))) =
        cK • Y.DelF j (cmp j x La.1 La.2) (Sr j La (c', L'))

end Formalism.L2.KerInert.SecondKernelDifference
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.SecondKernelCoupledLastLift
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelCoupled

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)
variable (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)

def LatC (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ x, (X.Pj j).IsLatTup (lp x).2

def DegreeCompatibilityAtLevel (j : ℕ) : Prop :=
  ∀ x : (D.chTw u μ).cls j, padicValNat p (Nat.card ((D.chTw u μ).stab j x)) ≤ X.dG j

def TieSerC (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) :
    Prop :=
  ∀ (x : (D.chTw u μ).cls j) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
    Y.ThF j (lp x) (c', L') = ((Y.eS j (lp x) * (Y.eT j (c', L'))⁻¹)⁻¹ : X.G.Kf) • Sr j (lp x) (c', L')

def KernelDifferenceWithConstant {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) (cK : Y.Kc) :
    Prop :=
  ∀ (x : (D.chTw u μ).cls j) (y : ((ex.tw.fm u μ).lat j).V) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup),
    (X.Pj (j + 1)).IsLatTup L' →
      Rd j c' L' (entRec t ex.tw u μ j x y) = cK • Y.DelF j (cmp j y (lp x).1 (lp x).2) (Sr j (lp x) (c', L'))

def HeckeC (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ (v : X.Pl) (i : ℕ), ∀ F ∈ X.FQ j, ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∑ x : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹ •
        ∑ᶠ (L1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
          (_ : IsEdge p ((X.Pj j).n' (X.vJ j v)) i ⟨(lp x).2 (X.vJ j v), L1⟩),
          Y.ker j ((lp x).1, Function.update (lp x).2 (X.vJ j v) L1) La' (F (lp x).1 (lp x).2) =
      ∑ x : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹ •
        Y.ker j (lp x) La' (X.Tm v i j F (lp x).1 (lp x).2)

def TiesC {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  FormsSharpAt t u μ j ∧ TieReadAt (Y := Y) u μ cmp ι Rd j ∧ LatC u μ j lp ∧ DegreeCompatibilityAtLevel (X := X) u μ j ∧ TieSerC Y u μ Sr j lp ∧
    ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧ cK ≠ 0 ∧ KernelDifferenceWithConstant Y t u μ cmp ι Rd Sr j lp cK

def SecC (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) (lp : (D.chTw u μ).cls j → X.Lt j) : Prop :=
  ∀ x, lp x ∈ Y.Rep j ∧ cls j (lp x).1 (lp x).2 = x

end Gen

def SecondKernelCoupledLastLift : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp → HeckeC Y u μ (D.R.m - 1) lp →
      ExpansionDecomposition D _ Y (D.R.m - 1)

def Adm4NewInst : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    (∀ j, j + 1 < D.R.m → TiesAt t u μ KA.cls KA.cmp ι Rd Sr j) →
    (0 < D.R.m → TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp ∧ HeckeC Y u μ (D.R.m - 1) lp) →
      ArchimedeanSignatureMatching D _ Y

def HeckeCEntry : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om))
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → MinkowskiCounting D _ Y → SecC Y u μ KA.cls (D.R.m - 1) lp → TieStabAt (Y := Y) u μ KA.cls (D.R.m - 1) →
      HeckeC Y u μ (D.R.m - 1) lp

def TiesCOfAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)) (ι : ℂ →+* Y.Kc) (Rd : _) (Sr : _)
    (lp : (D.chTw u μ).cls (D.R.m - 1) → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (D.R.m - 1)),
    0 < D.R.m → SecC Y u μ KA.cls (D.R.m - 1) lp → TiesAt t u μ KA.cls KA.cmp ι Rd Sr (D.R.m - 1) →
      TiesC Y t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp

def SecCEx : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    0 < D.R.m → ∃ lp, SecC Y u μ KA.cls (D.R.m - 1) lp

end Formalism.L2.KerInert.SecondKernelCoupled
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.TieSerPin
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

def srOf {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    MvPowerSeries (X.ZA j) Y.Kc :=
  ((Y.eS j La * (Y.eT j La')⁻¹ : X.G.Kf)) • Y.ThF j La La'

def TieSerOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ), TieSerAt (Y := Y) (srOf Y) j

end Formalism.L2.KerInert.SecondKernelSeries
end
end

