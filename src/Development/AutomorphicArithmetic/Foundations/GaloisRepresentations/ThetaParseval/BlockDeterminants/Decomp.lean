module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006
public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.TracePiReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TP

open GlobalTheory.ThK.Dbl.Euler (cut cut_mul cut_form cut_sub cut_eq cut_one mm cont_mat prj)

section Cut

variable {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k]

end Cut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}

private def pr (e : AF F) (he : e * e = e) : UA σ X.J →* UA σ X.J :=
  MonoidHom.mk' (fun g => ⟨⟨cut e (mat g), cut e (mat g⁻¹),
    by rw [cut_mul he, ← mm, mul_inv_cancel]; exact cut_one, by rw [cut_mul he, ← mm, inv_mul_cancel]; exact cut_one⟩,
    cut_form he _ g.2⟩) fun g h => Subtype.ext (Units.ext (cut_mul he _ _).symm)

private theorem eps_sq : realAd F 1 * realAd F 1 = realAd F 1 :=
  Prod.ext (by
    change (realAd F 1).1 * (realAd F 1).1 = (realAd F 1).1
    rw [PositivityTheory.ThKG.Loc.Bump.eps_fst, one_mul]) (by
    change (realAd F 1).2 * (realAd F 1).2 = (realAd F 1).2
    rw [PositivityTheory.ThKG.Loc.Bump.eps_snd, zero_mul])

end UpperTheory.TP
