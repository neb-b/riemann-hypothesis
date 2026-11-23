module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalCharacter
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

@[expose] public section

noncomputable section

open NumberField Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E
open scoped ComplexConjugate

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fixK (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) : Submodule ℂ (Sm E n) :=
  π.V ⊓
    { carrier := {φ | ∀ k ∈ K, finRep E n k φ = φ}
      add_mem' := fun {a b} ha hb k hk => by rw [map_add (f := _), ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun c a ha k hk => by rw [map_smul, ha k hk] }

def IsHeckeAct [MeasurableSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E))) (K : Subgroup (GL (Fin n) (Af E)))
    (Y : Submodule ℂ (Sm E n)) (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ Y) : Prop :=
  ∀ h, IsHeckeF K h → ∀ y : Y, (((ρ h y : Y) : Sm E n) : GA E n → ℂ) = heckeOp μf h ((y : Sm E n) : GA E n → ℂ)

def ThetaFixedGlobalWeights : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg →
    GlobalTheory.ContraPair.DualIsConj π → ∀ lamE : (E →+* ℂ) → Formalism.BasicNotions.DomWeight n,
    (∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))) →
    ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
    (∀ k ∈ K, thetaF E n k ∈ K) → (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ K, finRep E n k ψ = ψ) →
    ∀ [MeasurableSpace (PositivityTheory.RgTw.G n)] [BorelSpace (PositivityTheory.RgTw.G n)] (μC : Measure (PositivityTheory.RgTw.G n))
      [μC.IsHaarMeasure] [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (μ : Measure (H E n 0)) [μ.IsHaarMeasure],
    ∃ (Y : Submodule ℂ (Sm E n)) (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ Y) (A : Module.End ℂ Y) (c : ℂ),
      Y ≤ π.V ∧ FiniteDimensional ℂ Y ∧ Y ≠ ⊥ ∧ (∀ y ∈ Y, ∀ k ∈ K, finRep E n k y = y) ∧
      IsHeckeAct μf K Y ρ ∧
      (∀ W : Submodule ℂ Y, (∀ h, IsHeckeF K h → ∀ y ∈ W, ρ h y ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      A * A = 1 ∧ (∀ h, IsHeckeF K h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) ∧ c ≠ 0 ∧
      ∀ (k : ∀ w : InfinitePlace E, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lamE w.embedding).w).V →L[ℂ]
          (PositivityTheory.RgBcC.lefE n (lamE w.embedding).w).V))
        (val : InfinitePlace E → PositivityTheory.RgBcC.Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w : InfinitePlace E, PositivityTheory.RgBcC.IsMult μC (PositivityTheory.RgBcC.lefE n (lamE w.embedding).w) (k w) (val w) (T w)) →
        ∀ h, IsHeckeF K h →
          IsTwTr μ π (phiProd (fun w => (lamE w.embedding).w) k h)
            (c * (∏ w : InfinitePlace E, val w (PositivityTheory.RgBcC.infOf (lamE w.embedding).w)) * LinearMap.trace ℂ Y (ρ h * A))

end PositivityTheory.Rg.BcB.Desc

end
