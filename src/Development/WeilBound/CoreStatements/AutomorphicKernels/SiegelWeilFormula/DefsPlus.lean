module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}


variable (σ Y) in
def nA (b : GL (Fin n ⊕ Fin n) E) : AddSubgroup (Matrix (Fin n) (Fin n) (AE F E)) :=
  AddSubgroup.closure {β | ∃ x : G2 σ Y, inFrame b x = Matrix.fromBlocks 1 β 0 1}


variable (σ Y) in
def nF (b : GL (Fin n ⊕ Fin n) E) : AddSubgroup (nA σ Y b) :=
  AddSubgroup.closure {β | ∃ T : Matrix (Fin n) (Fin n) E, β.1 = (_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) T}

def IsNMap (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y) : Prop :=
  ∀ β, inFrame b (nb β) = Matrix.fromBlocks 1 β.1 0 1

def CoefData (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y) (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) : Prop :=
  IsNMap b nb ∧ lam.IsAddHaarMeasure ∧ IsAddFundamentalDomain (nF σ Y b) 𝓖 lam ∧ lam 𝓖 = 1

def fc (ψ : AddChar (AF F) ℂ) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y) (lam : Measure (nA σ Y b))
    (𝓖 : Set (nA σ Y b)) (f : G2 σ Y → ℂ) (T : nF σ Y b) (x : G2 σ Y) : ℂ :=
  ∫ β in 𝓖, f (nb β * x) * ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam

def IsND {b : GL (Fin n ⊕ Fin n) E} (T : nF σ Y b) : Prop := T.1.1.det ≠ 0

structure Std (B : Base F E) {m : ℕ} (A : Spc F E m) (Y : Spc F E n) (r s r' s' : ℕ) (χ : Chr F E) (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ)
    (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)) (Φ : (κ → AF F) → ℂ) : Prop where
  good : B.IsGood σ
  hm : 1 ≤ m
  hn : 1 ≤ n
  hnm : n < m
  aniso : min r s = 0
  sign : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s'
  hecke : IsHecke F E χ
  res : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m
  dbl : IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l
  frame : IsFrame2 σ Y b
  stdK : IsStdK (σ := σ) (Y := Y) B b K
  hgt : IsHgt K a
  haar : μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ A.J) D μ
  sch : Φ ∈ schA F κ
  fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ))

def s0 (m n : ℕ) : ℂ := ((m : ℂ) - n) / 2

def sec {κ : Type} (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (a : G2 σ Y → ℝ)
    (m : ℕ) (Φ : (κ → AF F) → ℂ) : ℂ → G2 σ Y → ℂ :=
  flat a (fun x => l (om x Φ)) (s0 m n)

def thetaMean {m : ℕ} {A : Spc F E m} {κ : Type} (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ))
    (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)) (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J))
    (Φ : (κ → AF F) → ℂ) (x : G2 σ Y) : ℂ :=
  ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ

def SWStdLt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s' χ (κ : Type) [Fintype κ] dd om S l b K a μ D Φ,
    Std (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ →
      EisValueAt (sec om l a m Φ) (s0 m n) (thetaMean om S μ D Φ)

end PositivityTheory.SiegelWeilFormula

end
