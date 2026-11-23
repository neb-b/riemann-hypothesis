module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Mathlib
public import Formalism.PeriodIntegrals.GTDefs

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.AdIndexEq
section
noncomputable section

namespace PI.AdIndexEq

open Formalism.MainNotions.S

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def IndexEq : Prop :=
  ∀ (I : AutInst) (x : I.Gf),
    ((Ksub I).map (MulAut.conj x).toMonoidHom).relIndex (Ksub I) =
      ((Ksub I).map (MulAut.conj x⁻¹).toMonoidHom).relIndex (Ksub I)

end PI.AdIndexEq

end
end

-- bundled from Formalism.PeriodIntegrals.AdUnimod
section
open MeasureTheory

noncomputable section

namespace PI

def AdUnimod : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf), μf.IsHaarMeasure → μf.IsMulRightInvariant

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.AdelClassFin
section
noncomputable section

namespace PI.AdelClassFin

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

def GFf (I : Formalism.MainNotions.S.AutInst) : Set I.Gf :=
  {x | ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    I.fmat x = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))}

def AdelClassFin : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) →
    ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ u ∈ U, x = γ * s * u

end PI.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.GTLower
section
noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def GTLower : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.LatSizeCont
section
noncomputable section

namespace PI.LatSizeCont

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace Size

variable (I : Formalism.MainNotions.S.AutInst)

def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}

end Size

end PI.LatSizeCont
end
end

-- bundled from Formalism.PeriodIntegrals.NMeasInv
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix

namespace PI.NMeasInv

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

def FrameRel (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) ∧
  Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0

end Inst

def FinCpt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ K : Set I.Ginf, IsCompact K → μ K < ⊤

def RightInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ n ∈ Ninf I e z, μ.map (fun x => x * n) = μ

def InvInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      μ.map (fun x => x⁻¹) = μ

def ConjInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ h ∈ Hset I (Set.range e ∪ Set.range f ∪ {z}), μ.map (fun x => h * x * h⁻¹) = μ

def Target : Prop := FinCpt ∧ RightInv ∧ InvInv ∧ ConjInv

end PI.NMeasInv
end
end

-- bundled from Formalism.PeriodIntegrals.ScMuExists
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix

namespace PI.ScMuExists

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

abbrev muInf : Measure I.Ginf := Measure.pi fun v => Formalism.REAL.muG (I.ε v)

def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def IsQuotMeasS (μS ν : Measure I.Ginf) : Prop :=
  ∀ f : I.Ginf → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂(muInf I) = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

end Inst

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0 →
    ∃ muN muH nuQ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) muN ∧
      IsHaarOnSet I (Hset I (Set.range e ∪ Set.range f ∪ {z})) muH ∧
      IsQuotMeasS I ((muN.prod muH).map (fun p => p.1 * p.2)) nuQ

end PI.ScMuExists
end
end

-- bundled from Formalism.PeriodIntegrals.ScPsiExists
section
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScPsiExists

def psiEinf (I : Formalism.MainNotions.S.AutInst) (x : I.E) : ℂ :=
  ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x)))

def Target : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, ∃ psiEf : I.E ⊗[I.F] Af I.F → ℂ,
    (∀ x y, psiEf (x + y) = psiEf x * psiEf y) ∧
    (∀ x ∈ IntAf I.F I.E, psiEf x = 1) ∧
    ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Af I.F) x) * psiEinf I x = 1

end PI.ScPsiExists
end
end

-- bundled from Formalism.PeriodIntegrals.ScRefExists
section
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open Matrix

namespace PI.ScRefExists

section Fin

variable (I : Formalism.MainNotions.S.AutInst)

abbrev VA : Type := Fin I.n → I.E ⊗[I.F] Af I.F

def incl (x : Fin I.n → I.E) : VA I := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def hA (x y : VA I) : I.E ⊗[I.F] Af I.F :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) x y

abbrev sigA : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

def mL (m : ℕ) : Submodule (IntAf I.F I.E) (VA I) :=
  Submodule.span (IntAf I.F I.E) {y | ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x}

def InMod (m : ℕ) (S : Set (VA I)) (x : VA I) : Prop :=
  x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I m

def ZMod' (m : ℕ) (c : I.E ⊗[I.F] Af I.F) : Prop :=
  ∃ t ∈ IntAf I.F I.E, c = (m : I.E ⊗[I.F] Af I.F) * t

def InAt (g m : ℕ) (x : VA I) : Prop :=
  ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • x ∈ mL I m

end Fin

structure RefData (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) where
  e0 : Fin r → VA I
  f0 : Fin r → VA I
  z0 : VA I
  bw : Fin k → VA I
  bwd : Fin k → VA I
  ew : I.E ⊗[I.F] Af I.F
  vectorsInLattice : (∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf
  basisApprox : ∀ a, InAt I g g (e0 a - incl I (e a)) ∧ InAt I g g (f0 a - incl I (f a))
  gramIntegral : ∀ a b, ZMod' I g (hA I (e0 a) (e0 b)) ∧ ZMod' I g (hA I (f0 a) (f0 b)) ∧
    ZMod' I g (hA I (e0 a) (f0 b) - if a = b then 1 else 0)
  formsAtZero : ZMod' I g (hA I z0 z0 + 1) ∧
    ∀ a, ZMod' I g (hA I (e0 a) z0) ∧ ZMod' I g (hA I (f0 a) z0)
  weightVectorsIntegral : ∀ i, ZMod' I g (hA I z0 (bw i)) ∧ ZMod' I g (hA I z0 (bwd i)) ∧
    ∀ a, ZMod' I g (hA I (e0 a) (bw i)) ∧ ZMod' I g (hA I (f0 a) (bw i)) ∧
      ZMod' I g (hA I (e0 a) (bwd i)) ∧ ZMod' I g (hA I (f0 a) (bwd i))
  ew_idem : ew * ew = ew
  ew_orth : ew * sigA I ew = 0
  ew_int : ew ∈ IntAf I.F I.E
  ew_full : ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g
  bw_w : ∀ i, bw i = ew • bw i
  bwd_w : ∀ i, bwd i = sigA I ew • bwd i
  bw_dual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)
  latticeSpan : ∀ y ∈ I.Lf,
    InMod I g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E), 1 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    Nonempty (RefData I g r k e f)

end PI.ScRefExists
end
end

