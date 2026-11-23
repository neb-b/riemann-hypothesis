module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def scl (v : PlX X) : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v :=
  Fin.append (alp v D.R.rS) (fun b : Fin D.R.rS => (alp v D.R.rS b.castSucc)⁻¹)

def yTup (v : PlX X) : TupV (E := X.B.I.E) v X.B.I.n (D.R.rS + 1 + D.R.rS) :=
  fun i => sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i

def localGramMatrixFrame (v : PlX X) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v))

abbrev abelian₂ : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def OmVStd : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → StdHyp X.B.I.cm.sig X.B.I.J ψ

def OmVLat : Prop :=
  ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = abelian₂ X

def OmVSD : Prop := ∀ v : PlX X, IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X)

def OmVPrim : Prop := ∀ v : PlX X, IsPrim v (abelian₂ X) (yTup X u' v)

def OmVGram : Prop := ∀ v : PlX X, gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) = localGramMatrixFrame X u' v

def OmVDet : Prop :=
  ∀ v : PlX X, ¬ (((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) →
    ∃ w ∈ OEv (E := X.B.I.E) v, (localGramMatrixFrame X u' v).det ∈ OEv (E := X.B.I.E) v ∧ (localGramMatrixFrame X u' v).det * w = 1

def OmVScale : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} =
      omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v}

def OmVBadT : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X) → UnramAt (E := X.B.I.E) v → IsPrim v (abelian₂ X) (yTup X u' v) →
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      ENNReal.ofReal (absV v (dV v) ^ ((X.B.I.n : ℝ) * (D.R.rS + 1 + D.R.rS : ℕ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (X.B.I.n - (D.R.rS + 1 + D.R.rS)) X.B.I.n,
          (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

def OmVLocU : Prop :=
  ∀ (v : PlX X) (a : ℕ) (Y : TupV (E := X.B.I.E) v X.B.I.n a),
    Formalism.L2.SG.Pf.NcLoc.OmLocU X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

end Formalism.L2.SG.Pf.NcVal.OmVSt
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTSt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def VolTO (ι : Type) : Set (ι → Fv F v ⊗[F] E) := {x | ∀ i, x i ∈ OEv (E := E) v}

def VolTOne (ι : Type) [Fintype ι] : Prop := sdE (E := E) ψ v ι (VolTO (E := E) v ι) = 1

def VolTAff (g : ℕ) (ι : Type) [Fintype ι] : Prop :=
  ∀ (b : ι → Fv F v ⊗[F] E) (S : Set (ι → Fv F v ⊗[F] E)),
    sdE (E := E) ψ v ι {w | (fun i => (w i - b i) * sc (E := E) v (g : Fv F v)⁻¹) ∈ S} =
      ((g : ℝ≥0∞) ^ (2 * Fintype.card ι))⁻¹ * sdE (E := E) ψ v ι S

def VolTLocPres (r : ℕ) : Prop :=
  ∀ S : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E),
    sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) {z | (fun p => locZ (E := E) v z p.1 p.2) ∈ S} =
      sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) S

def VolTW (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {Y | ∀ i j, Y (i, j) ∈ OEv (E := E) v ∧
    (Y (i, j) + sigR (Fv F v) σ (Y (j, i)) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}

def VolTHermInt (r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) : Prop :=
  (∀ i j, c j i = sigR (Fv F v) σ (c i j)) ∧ ∀ i j, c i j ∈ OEv (E := E) v

def VolTHermCnt (g r : ℕ) : Prop :=
  ∀ c, VolTHermInt σ v r c →
    sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (VolTW σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹

def VolTUSet (g r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  {p | (∀ q, p.1 q ∈ OEv (E := E) v) ∧ ∀ q, (p.2 q - p.1 q) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}

def VolTUOEq (g r : ℕ) : Prop := deepCongruenceVolume (E := E) v g r = VolTUSet (E := E) v g r

def VolTProdU (g r : ℕ) : Prop :=
  ((sdE (E := E) ψ v (UIdx r)).prod (sdE (E := E) ψ v (UIdx r))) (VolTUSet (E := E) v g r) =
    sdE (E := E) ψ v (UIdx r) (VolTO (E := E) v (UIdx r)) * ((g : ℝ≥0∞) ^ (2 * Fintype.card (UIdx r)))⁻¹

end Gen

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolTZZAt (v : PlX X) : Prop :=
  ZZX X u u' ψ v = (gAt X v : ℝ) ^ (-((3 * (D.R.rS + 1) ^ 2 : ℕ) : ℤ))

def VolumeDeepCongruenceSubgroup (v : PlX X) : Prop :=
  localVolumeUnit X ψ v = (gAt X v : ℝ) ^ (-((D.R.rS * (D.R.rS + 1) : ℕ) : ℤ))

def VolTTFCong (v : PlX X) : Prop :=
  VolTHermInt X.B.I.cm.sig v D.R.rS
    (fun i j => (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹)

end OfX

end Formalism.L2.SG.Pf.NcVal
end
end

