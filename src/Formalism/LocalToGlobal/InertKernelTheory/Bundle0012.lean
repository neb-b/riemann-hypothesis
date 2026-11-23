module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0011
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.AdmRed

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsRepComb
section
noncomputable section

namespace Formalism.L2.KerInert.RepComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

abbrev hK (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a b : ℕ) : Sesq (TaylorLogMetric.VC D a b) :=
  HV (ι := D.what₂.Tau) (a := a) (b := b) (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹

abbrev alK (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a b : ℕ) : TaylorLogMetric.VC D a b → ℂ :=
  alV (ι := D.what₂.Tau) (a := a) (b := b) D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹


variable (cc δ) in
abbrev lamK {a b : ℕ} (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  LamC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N'


variable (cc δ) in
abbrev halfA {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  AC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl


variable (cc δ) in
abbrev halfB {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : AddSubgroup (TaylorLogMetric.VC D a b) :=
  BC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl


variable (cc δ) in
abbrev ptsX {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Finset (TaylorLogMetric.VC D a b) :=
  repsOf (lamK cc δ N N') (halfA cc δ SS cl N N')


variable (cc δ) in
abbrev ptsA {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Finset (TaylorLogMetric.VC D a b) :=
  repsOf (halfB cc δ SS cl N N') (lamK cc δ N N' ⊓ halfA cc δ SS cl N N')


variable (cc δ) in
abbrev ptsB {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Finset (TaylorLogMetric.VC D a b) :=
  repsOf (lamK cc δ N N') (halfB cc δ SS cl N N')


variable (cc δ) in
def kerCoef {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ)
    (x y : TaylorLogMetric.VC D a b) : ℂ :=
  alK D cc δ a b x *
    (hatS (hK D cc δ a b) 1 (ptsA cc δ SS cl N N')
      (fun s => onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ Ξ (s - x)) y * alK D cc δ a b y) *
    Complex.exp ((Real.pi : ℂ) * (hK D cc δ a b y x - hK D cc δ a b x y) / 2)


variable (cc δ) in
def CoefInt {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ)
    {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ x ∈ ptsX cc δ SS cl N N', ∀ y ∈ ptsB cc δ SS cl N N',
    kerCoef cc δ SS cl N N' Ξ x y ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.IsIntP (TaylorLogMetric.lamC lam (kerCoef cc δ SS cl N N' Ξ x y))



variable (cc δ) in
def FinIdx {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Prop :=
  relIdx (lamK cc δ N N') (halfA cc δ SS cl N N') ≠ 0 ∧
    relIdx (halfB cc δ SS cl N N') (lamK cc δ N N' ⊓ halfA cc δ SS cl N N') ≠ 0 ∧
    relIdx (lamK cc δ N N') (halfB cc δ SS cl N N') ≠ 0


variable (cc δ) in
def LamIn {a b : ℕ} (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : Prop :=
  lamK cc δ N N' ≤ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N'

def CombKerT : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]),
    TaylorLogMetric.admitted D a b N N' → N'.FG → Submodule.span D.host.E (N : Set (Formalism.L2.Col.Sp D.host.E a)) = ⊤ →
    (Formalism.L2.PairingIndexBounds.F.aaOf D cc).FG →
    LaFacts (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' →
    0 < cl → SNum S cl → (∀ x, IntOff S (Ξ x)) → p ∉ S → LamIn cc δ N N' → TransAlg D B.tor (B.eNat χ) →
      TaylorLogMetric.IsComb D B.tor (B.eNat χ) lam N N' (Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ))

end Formalism.L2.KerInert.RepComb
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
section
noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def CurveDict : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (l : ℕ) [Fact l.Prime]
    (g : Formalism.MainNotions.GL3Theta.G1 l) (hLT : Formalism.L2.G.Pend.LTIso g),
    Formalism.MainNotions.GL3Theta.At D cc δ g → 5 ≤ l → Formalism.MainNotions.GL3Theta.InertK D l → Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C →
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension l, (g2 : ℂ_[l]) = Formalism.L2.Th1.A.g₂ g.W ∧ (g3 : ℂ_[l]) = Formalism.L2.Th1.A.g₃ g.W ∧
      (ε : ℂ_[l]) = (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ ∧
      PowerSeries.rescale ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) =
        PowerSeries.C ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * Formalism.L2.Th1.B.sgW g.W (s2 : ℂ_[l]) ∧
      ‖((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹‖ = 1 ∧
      CurveAt l (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 ∧
      ∀ D' : Formalism.BasicNotions.D7, DictInt D' g.lam g.abelian₂
        (((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε

end Formalism.L2.KerInert.Rep
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
section
noncomputable section

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf invF zOfX tw mAt rank_eq)
open Formalism.MainNotions.FormalGroupSystem (Sys)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

def kapInv (j : ℕ) (y : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : X.ZA j :=
  ⟨(pos.symm y.1).1, ((pos.symm y.1).2, Fin.cast (rank_eq X j) y.2.2, Fin.cast (rank_eq X (j + 1)) y.2.1)⟩

def linFrame {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')
    (S : (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  ∑ y, MvPowerSeries.C (S k y) * invF ℂ_[p] φ (kapInv X pos j y)


open Classical in
def subGen (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (x y : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  if x.1 = y.1 then
    (if IsOddPos (pos.symm x.1).2 then
      (M j La (pos.symm x.1).1).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) x.2.2 y.2.2 *
        ((M (j + 1) La' (pos.symm x.1).1)⁻¹).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) y.2.1 x.2.1
    else
      (M (j + 1) La' (pos.symm x.1).1).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) x.2.1 y.2.1 *
        ((M j La (pos.symm x.1).1)⁻¹).map (tw X ℂ_[p] (pos.symm x.1).1 (pos.symm x.1).2) y.2.2 x.2.2)
  else 0

def stdLin (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  if IsOddPos (pos.symm k.1).2 then
    ∑ a' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t j), ∑ b' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C (mAt X ℂ_[p] j (pos.symm k.1).1 (pos.symm k.1).2 (M j L0 (pos.symm k.1).1 * (φ.g (pos.symm k.1).1 : Matrix _ _ _))
          (Fin.cast (rank_eq X j) k.2.2) a' *
        mAt X ℂ_[p] (j + 1) (pos.symm k.1).1 (pos.symm k.1).2
          ((((φ.g' (pos.symm k.1).1)⁻¹ : GL _ _) : Matrix _ _ _) * (M (j + 1) La' (pos.symm k.1).1)⁻¹)
          b' (Fin.cast (rank_eq X (j + 1)) k.2.1)) *
      zOfX X ℂ_[p] j ⟨(pos.symm k.1).1, ((pos.symm k.1).2, a', b')⟩
  else
    ∑ a' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t j), ∑ b' : Fin (Formalism.MainNotions.FormalGroupSystem.NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C (mAt X ℂ_[p] (j + 1) (pos.symm k.1).1 (pos.symm k.1).2
          (M (j + 1) La' (pos.symm k.1).1 * (φ.g' (pos.symm k.1).1 : Matrix _ _ _)) (Fin.cast (rank_eq X (j + 1)) k.2.1) b' *
        mAt X ℂ_[p] j (pos.symm k.1).1 (pos.symm k.1).2
          ((((φ.g (pos.symm k.1).1)⁻¹ : GL _ _) : Matrix _ _ _) * (M j L0 (pos.symm k.1).1)⁻¹)
          a' (Fin.cast (rank_eq X j) k.2.2)) *
      zOfX X ℂ_[p] j ⟨(pos.symm k.1).1, ((pos.symm k.1).2, a', b')⟩

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos' : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Coord

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def lamB (k : D.what₂.Tau × Fin N' × Fin N) (i : Fin r) : ℂ_[p] := lamC lam (embT D k.1 (b i k.2.1 k.2.2))

def lamBc (k : D.what₂.Tau × Fin N' × Fin N) (i : Fin r) : ℂ_[p] :=
  lamC lam (embT D k.1 (D.host.conj (b i k.2.1 k.2.2)))


open Classical in
def LamONB : Prop :=
  ∀ k k' : D.what₂.Tau × Fin N' × Fin N, ∑ i, lamB D lam b k i * lamBc D lam b k' i = if k = k' then 1 else 0

end Coord

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
  {T : Type} [Fintype T] (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

def frVec (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La') (y : X.EA j ⊕ X.EA j)
    (k : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : ℂ_[p] :=
  MvPowerSeries.coeff (Finsupp.single y 1) (stdLin X E pos M φ k)

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos' : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))


open Classical in
def ColTie (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b →
        ∀ i i', ∑ k, lamBc D lam b k i * lamB D lam b k i' = if i = i' then 1 else 0

end Formalism.L2.KerInert.RepFrame

namespace Formalism.L2.KerInert.RepFrame

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def TraceTau (D : D7) : Prop :=
  ∀ y : D.host.E, ∑ τ : D.what₂.Tau, embT D τ y = D.host.φ₀ ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E)

end Formalism.L2.KerInert.RepFrame
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.SclY
section
noncomputable section

namespace Formalism.L2.KerInert.Rep

def sclY {σ R : Type} [CommRing R] (c : R) (G : MvPowerSeries σ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k : σ => MvPowerSeries.C c * MvPowerSeries.X k) G

end Formalism.L2.KerInert.Rep
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementLoc
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

namespace Formalism.L2.KerInert

def LowZC {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) (j : ℕ) (v : X.Pl) : Prop :=
  letI := wittFractionAlgebraCp p
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p], IntR (OcC p) (inParamK p ℂ_[p] U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      GeZ (AddMonoidAlgebra.coeff (applyD (X.PIv j I v)
        (X.ThZA ℂ_[p] j (MvPowerSeries.map (algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 p) ℂ_[p])
          (expS p (-(∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
            sub2 p be (MvPowerSeries.X (Sum.inl (⟨v, e⟩ : X.EA j))) (MvPowerSeries.X (Sum.inr (⟨v, e⟩ : X.EA j)))))) * U))) n)

def FirstKernelLocalOfGeneral : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    RepresentativeCondition X E hfin be pos F → LocalRepresentativeCondition X E hfin be pos F

def Adm3OfK1LowerBound : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    (∀ j < X.mm, ∀ v, LowZC X be j v) → RepresentativeCondition X E hfin be pos F → Adm3Rep X E hfin pos F

end Formalism.L2.KerInert
end
end

