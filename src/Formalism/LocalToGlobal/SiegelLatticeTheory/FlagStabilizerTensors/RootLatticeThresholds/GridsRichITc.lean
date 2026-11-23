module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierGrids

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def gridT {D : D7} (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (l : ℕ) (j : Fin (nfE D)) : ℕ → Finset ℝ :=
  Formalism.L2.SG.Pf.CarrierSz.gridCh ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)) l
    (4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1)) (2 * D.R.rS)

def grid1T {D : D7} (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (l : ℕ) (j : Fin (nfE D)) : Finset ℝ :=
  Formalism.L2.SG.Pf.CarrierSz.grid1Of ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place (plE D j)) l (4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1))

theorem b_ge_one (c : Formalism.FourierDecayAlt.Sz.Cfg) (h : c.Ok) : ∀ j, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact h.hb1
    · have h1 := ih hn (by omega)
      have h2 := h.hgap n hn (by omega)
      linarith

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem gridsRich_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hlen : 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ≤
      (D.s.Del : ℝ) / 2 - 5 / 2) :
    Formalism.FourierDecayAlt.KB.GridsRich (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) fc c i0' Θ TP A₀)) :=
  Formalism.L2.SG.Pf.CarrierSz.gridsRich_ch _ hlen (fun v => by show gridT e l v = _; unfold gridT; rfl)
    (fun v => by show grid1T e l v = _; unfold grid1T; rfl)

theorem gridsOK_ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hlen : 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ≤
      (D.s.Del : ℝ) / 2 - 5 / 2)
    (hOk : ∀ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w).Ok) (hl2 : l + 2 ≤ D.R.k) :
    Formalism.FourierDecayAlt.C.GridsOK (sOf (ITc X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) fc c i0' Θ TP A₀)) := by
  have hDel : (0 : ℝ) < (D.s.Del : ℝ) := by exact_mod_cast D.s.Del_pos
  refine Formalism.L2.SG.Pf.CarrierSz.gridsOK_ch _ hlen (fun v => by show gridT e l v = _; unfold gridT; rfl)
    (fun v => by show grid1T e l v = _; unfold grid1T; rfl)
    (Formalism.L2.SG.Pf.CarrierSz.pNe_of _ hDel (fun x => (hOk x).hv0) (fun x j h1 h2 => b_ge_one _ (hOk x) j h1 h2) hl2)

end Formalism.L2.SG.Pf.CarrierT
