module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def keyInOf {R : Type} [CommRing R] (t : SAB H (Sp R)) (th : t.PP.L.Sec) (g : ℕ) (hg : 1 ≤ g)
    (v : Fin g → (epsR R ⟶ t.G)) (hv : IsLieBasis v) (hab : IsAbelianScheme t.G)
    (hd : SmoothOfRelativeDimension g t.G.hom) (hs : Out.Sym t.G t.PP.L) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) (hth : ∀ s : Sp R, ∃ x : t.G.left, t.G.hom x = s ∧ x ∈ Out.nonzeroLocus th) : KeyIn R where
  P := { A := t.G, isAb := hab, g := g, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB,
         rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := hs, ample := ha, ktriv := hk }
  g_pos := hg
  rig := t.PP.rig
  rig_gen := t.PP.rigGen
  th := th
  th_ne := hth
  v := v
  basis := hv

end GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel
