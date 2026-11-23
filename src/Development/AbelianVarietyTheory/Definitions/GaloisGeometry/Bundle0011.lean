module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TrDual
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual beMean)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog lgN)

namespace GlobalTheory.KerStd

def BeData (l d : ℕ) [Fact l.Prime] [NeZero d] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l) : Prop :=
  UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧ F1 F be0 ∧ F2 l σ be0 ∧ OwOK d σ om oms ∧ TrDual d σ om oms ∧
    IsPrimitiveRoot ζ (l ^ d - 1)

def beOf (l d : ℕ) [Fact l.Prime] [NeZero d] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l) : MvPowerSeries (ZMod d) ℂ_[l] :=
  MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean (d := d) l σ be0 om oms ζ)

def BeStd (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l),
    BeData l d σ F be0 om oms ζ ∧ be = beOf l d σ be0 om oms ζ

def BeFam (D : D7) (ep : ∀ w : D.what₂.places.Pl, ℂ_[D.what₂.places.resChar w])
    (be : ∀ w : D.what₂.places.Pl, OrbitPlaces.Pl D →
      MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ w : D.what₂.places.Pl,
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
    ‖ep w‖ = 1 ∧ ∀ r, BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) (be w r)

def linEv (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p) (r : OrbitPlaces.Pl D) (a : Fin N0) (b : Fin N1) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ s : ZMod (nP D p), if s.val % 2 = 0 then
    MvPowerSeries.C ((σ^[s.val] c : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p r s, a, b) else 0

def linOd (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p) (r : OrbitPlaces.Pl D) (a : Fin N0) (b : Fin N1) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ s : ZMod (nP D p), if s.val % 2 = 0 then 0 else
    MvPowerSeries.C ((σ^[s.val] c : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p r s, a, b)

def hypZ (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1,
    (MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)

def alLoc (Lc : product_zeroth_first_parts.Loc) (s : ZMod Lc.d) : ℕ := if s ∈ Lc.TT then (Lc.nu s).rowLen 0 - (Lc.nu s).rowLen 1 else 0

def gainA (Lc : product_zeroth_first_parts.Loc) : ℝ :=
  (∑ s ∈ Lc.TT, ∑' e : ℕ,
    if Odd e ∧ ¬ (e < Lc.d ∧ s + (e : ZMod Lc.d) ∈ Lc.TT) then
      max ((alLoc Lc s : ℝ) / (Lc.l : ℝ) ^ e - (Lc.cap (s + (e : ZMod Lc.d)) : ℝ)) 0 else 0) -
  ((∑ s : ZMod Lc.d, ((Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) + (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s))) +
    ∑ s ∈ Lc.TT, ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2)

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
section
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

def reY {D : D7} (Y : LatInst D)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv) : LatInst D where
  vOf := Y.vOf
  Fl := Y.Fl
  Lv := fun u w hg => (LC (D.what₂.muAt w) u w hg).1
  Ch := fun u w hg => (LC (D.what₂.muAt w) u w hg).2
  Vram := Y.Vram

def reW {D : D7} (Y : LatInst D) (LC : _) : WeilJacquetShalikaLaw.TwLoc D (reY Y LC) := ⟨LC, fun _ _ _ => rfl⟩


open Classical in
def SysTw (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (K : G.Consts) (Dx : DivX D) {Y : G.LatInst D} (W : WeilJacquetShalikaLaw.TwLoc D Y)
    (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  ErrDefs D L Xe lev K ce → ∀ μ, DV.Used D μ → ∀ (hT : GatTies D), G.LatTied hT X (W.Yt μ) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp μ →
    ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
      (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) ((W.Yt μ).Fl u w hg)
        ((W.Yt μ).Lv u w hg) ((W.Yt μ).Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
      FormalGroupSystem.admitted D _ Y5 ∧
      ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
        (∀ v, v ∉ (G.reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg) → ∀ j < D.R.m,
          Y5.LowAt j v (Fn v (j + 1))) ∧
        WeilJacquetShalikaLaw.lowS L Xe K ce sp u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m,
          ∑ v ∈ Finset.univ \ (G.reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg), Fn v j) -
            ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

def RowTwU {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1

def CmpLite (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} (Ch : Chain Lv) : Prop :=
  ∃ cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[c.embW u w hg] Lv.Fm j,
    (∀ x : ((D.fm u).lat 0).V, cmp 0 (Tw.e0 u μ x) = c.cmp u w hg x) ∧
    (∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
      (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x)) ∧
    (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) ∧
    ∀ (y : ((Tw.fm u μ).lat D.R.m).V) (s : ℝ),
      vGeLat (D.gat u w hg) (Lv.Int D.R.m) (cmp D.R.m y) s → WeilJacquetShalikaLaw.VGe D w ((Tw.fm u μ).lat D.R.m).L y s

def ModelsOK (D : D7) (Y : LatInst D) (c : LatCmp D) (Dx : DivX D) (Tw : TwForms D) : Prop :=
  (∀ u, Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _)) ∧
  ∃ LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv,
    ∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      D.what₂.places.resChar w ∉ Dx.Qp μ →
      CmpLite D c Tw u μ w hg (LC μ u w hg).2 ∧ SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2

end GlobalTheory.TwU

end
end

