module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scalar

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def IsEmbHom (ι : A.V →ₗ[D.host.E] B.V) (s : GA D A →* GA D B) : Prop :=
  ∀ h, EmbRel B A ι (s h) h

end Scalar

section Vec

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  {Vt : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
  {S : D.what₂.Tau → SPar}




end Vec

end Formalism.IndefR.Mi

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def frame0 (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then (D.sp.Y 0).frame.repr (D.sp.hypE ⟨i, h⟩)
  else if i = D.R.rS then (D.sp.Y 0).frame.repr D.sp.zm
  else if h' : 2 * D.R.rS - i < D.R.rS then
    (D.sp.Y 0).frame.repr ((-(D.sp.T : D.host.E)) • D.sp.hypF ⟨2 * D.R.rS - i, h'⟩)
  else 0


open Classical in
def NormalFrame0 (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (S Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    (∀ i < D.R.m - 1, ∀ col : Fin (D.sp.Y 0).rank, col.val = D.R.N 0 + i →
      ColAt 0 βY0.val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) * frame0 i r) ∧
    (∀ col : Fin (D.sp.Y 0).rank, col.val < D.R.N 0 → XSpanAt 0 βY0.val ei col)

def VertexAt (j : ℕ) (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (βW : GL (Fin (D.sp.W j).rank) (EAf D))
    (e : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W j).rank)
    (ι : GL (Fin (D.sp.W j).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) : Prop :=
  (∀ k, (e k).val = k.val) ∧
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ι.val *
            (((D.sp.Y 0).gram.reindex e e).map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F))) *
            ι.val =
    (D.sp.W j).gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) ∧
  ∀ PP ∈ Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    IsIntM (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) ∧
      redM PP (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) = 1

end Formalism.IndefR.Mi

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NotRootUnity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
  NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnifIdele (P : HeightOneSpectrum (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧
    (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)

def IsUnramAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ e f : AE D, IsPrimeIdem P e f ∧ ∀ x : (AE D)ˣ, (x : AE D) = e * (x : AE D) + (1 - e) →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1


open Classical in
def chiAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : ℂ :=
  if h : IsUnramAt χ P ∧ ∃ x, IsUnifIdele P x then ((χ h.2.choose : Circle) : ℂ) else 0

def normP (P : HeightOneSpectrum (𝓞 D.host.E)) : ℕ := Ideal.absNorm P.asIdeal

def lfac (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) (s : ℂ) : ℂ :=
  (1 - chiAt χ P * (normP P : ℂ) ^ (-s))⁻¹

end Formalism.IndefR.Mi

end
end

