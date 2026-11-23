module

public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.WLeWjOne
public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.ExistsPowOrbRep
public import Formalism.SharpRestriction.GrowthBounds.DefsInst
public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.Bundle0001

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LatticeCompatibleAt {D : D7} {L : SizeData₂ D} (X : Inst D L) {p : ℕ} (G : GAtP p)
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau) (vOf : HH D → Fin G.P.nV) (Fl : Fills G) : Prop :=
  Fl.mm = D.R.m ∧ Fl.t = D.R.t ∧
  (Fl.c : ℝ) ≤ cG L ∧
  G.P.r = (if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1) ∧
  Set.InjOn vOf (reps X p) ∧
  (∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (t : HH D),
    ((D.eTau (pos ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau2 t →
      s ∉ Fl.TT v ∧ ∀ j ∈ SizeData₂.lifts D, (Fl.w v j s : ℝ) = fillG X (bL L) j (true, t)) ∧
  ∀ t0 ∈ reps X p,
    G.P.n' (vOf t0) = addOrderOf (hP D p) ∧
    ∀ s : Fin (G.P.n' (vOf t0)),
      ((D.eTau (pos ⟨vOf t0, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 (t0 + s.val • hP D p) ∧
      (s ∈ Fl.TT (vOf t0) ↔ t0 + s.val • hP D p ∈ D.host.TT) ∧
      (s ∈ Fl.TT (vOf t0) →
        Fl.a (vOf t0) s = aL L (t0 + s.val • hP D p) ∧
        Fl.b (vOf t0) s = bL L (t0 + s.val • hP D p)) ∧
      ∀ j ∈ SizeData₂.lifts D,
        (Fl.w (vOf t0) j s : ℝ) = fillG X (bL L) j (false, t0 + s.val • hP D p)

theorem latTied_iff {D : D7} {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) :
    LatTied hT X Y ↔ ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      LatticeCompatibleAt X (D.gat u w hg) (hT.gat_pos u w hg) (Y.vOf u w hg) (Y.Fl u w hg) := Iff.rfl

def rRec {D : D7} (L : SizeData₂ D) (p : ℕ) : ℕ := if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1

theorem tau_top_places_iff (D : D7) (t : HH D) : D.R.tau1 t ∈ D.host.topPlaces ↔ t ∈ D.host.TT := by
  rw [← Formalism.MainNotions.Inhab.plGG_false, Formalism.MainNotions.Inhab.plGG_top_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem tau_coe_val (φ : Formalism.HC.Frame) (t : φ.A) : ((tau1P φ t : φ.Psi) : φ.GG) = φ.tau1 t := rfl

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

end Formalism.L2.G
