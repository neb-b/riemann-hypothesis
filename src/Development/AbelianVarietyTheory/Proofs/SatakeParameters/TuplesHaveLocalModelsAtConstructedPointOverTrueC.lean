module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_bpt : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  intro h1 h2 K β hβ
  have key : ∀ O : Obj β.X.toD7, ofObj O = β.c.O → ModelsAt β.X.toD7 O := by
    refine positionOf_ind (P := HasPart) (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ModelsAt X.toD7 O) ?_ hβ
    intro K B f T w Z c hc O hO
    obtain ⟨b⟩ := hc
    have b' : Part w Z (ofObj O) := hO ▸ b
    exact _root_.GlobalTheory.Svd.modelsAt_of_part h1 h2 B f T w Z O b'
  have hm := key (β.Y.obj β.p) (by rw [ofObj_obj]; exact β.hY)
  exact _root_.GlobalTheory.Svd.modelsAt_tr β.X.toD7 (β.Y.obj β.p) (nPrime β.p.L) β.p.ht hm

end GlobalTheory.Svd
