module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

namespace DefFam

variable {T T' J : Type} (F : DefFam K G Pl0 T J)

def comap (f : T' → T) (μ0' : T') : DefFam K G Pl0 T' J where
  v0 := F.v0
  μ0 := μ0'
  X := F.X
  R t := F.R (f t)
  L j t := F.L j (f t)
  tr := F.tr

end DefFam

namespace DefFam3

variable {I0 Ty T T' J : Type} (F3 : DefFam3 K G Pl0 I0 Ty T J)

def comap (f : T' → T) (μ0' : T') : DefFam3 K G Pl0 I0 Ty T' J where
  F := F3.F.comap f μ0'
  RI t := F3.RI (f t)
  LI j t := F3.LI j (f t)
  trI := F3.trI

end DefFam3

namespace FamIn

variable {T T' : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

def comap (f : T' → T) (μ0' : T') : FamIn K G Pl0 T' m where
  v0 := A.v0
  μ0 := μ0'
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j τ := A.muVal j (f τ)
  etaVal := A.etaVal
  ok τ := A.ok (f τ)
  MtildeCSD τ := A.MtildeCSD (f τ)
  leftGroupActionRight τ := A.leftGroupActionRight (f τ)
  heckeR τ := A.heckeR (f τ)
  MtCSD j τ := A.MtCSD j (f τ)
  leftGroupActionLift j τ := A.leftGroupActionLift j (f τ)
  heckeL j τ := A.heckeL j (f τ)

end FamIn

namespace FamIn3

variable {I0 Ty T T' : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

def comap (f : T' → T) (μ0' : T') : FamIn3 K G Pl0 I0 Ty T' m where
  A := A3.A.comap f μ0'
  okI τ := A3.okI (f τ)
  heckeRI τ := A3.heckeRI (f τ)
  heckeLI j τ := A3.heckeLI j (f τ)
  trI := A3.trI

end FamIn3

end Gen

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

def TupF.incl {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : TupF TU → TupF TC :=
  fun τ => ⟨τ.1, τ.2.imp id fun hm => h hm⟩

variable (v0 : InfinitePlace X.K) {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC)
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)








variable (Zs : DefSub (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).amb3)

end Inst

end Formalism.L2.DIV
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Col
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef

section Face

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem linkDIV_L2R_face [_root_.NumberField.IsTotallyComplex K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (Pk : IndefPkgR A fc cf C CH) (wf0 : (fc Pk.Zs).Df0.WF) (wf1 : (fc Pk.Zs).Df1.WF)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (u : (fc Pk.Zs).Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin ((fc Pk.Zs).Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsR Pk.core R u Nu sg) : DivClausesR Pk.core R u Nu sg :=
  divClausesR_of wf0 wf1 Pk.core R u Nu sg I

end Face

section Fam3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

end Fam3

section Col3

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)

end Col3

end Formalism.L2.DIV
end
end

