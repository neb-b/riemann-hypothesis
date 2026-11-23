module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramAugT
section
noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def bordM {a : ℕ} (G : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (z : Fin a) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E) :=
  Fin.snoc (α := fun _ => Fin (a + 1) → Fv F v ⊗[F] E)
    (fun i => Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (G i) (if i = z then 1 else 0))
    (Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (fun j => if j = z then 1 else 0) 0)

theorem hAddR (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + y') = hR (Fv F v) σ J x y + hR (Fv F v) σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hSmulR (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hAddL (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hSmulL (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem gram_augT {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) (z : Fin a)
    (h1 : ∀ i, hR (Fv F v) σ J (X i) w = if i = z then 1 else 0)
    (h2 : ∀ i, hR (Fv F v) σ J w (X i) = if i = z then 1 else 0) (h3 : hR (Fv F v) σ J w w = 0) :
    gramR (Fv F v) σ J (augT v X w) = bordM v (gramR (Fv F v) σ J X) z := by
  funext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [gramR, augT, bordM, h3]
    | cast j => simp [gramR, augT, bordM, h2]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [gramR, augT, bordM, h1]
    | cast j => simp [gramR, augT, bordM]

end PI.OmVf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfIsoWX
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_isoW (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_iso X u' ψ hStd hLat hGram (fun v hv => isoExt_of _ _ _ _ _ _ _ (hIso v hv)) hLI hRed hFI hFS

end PI.OmVd
end
end

