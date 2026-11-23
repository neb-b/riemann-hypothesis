module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF PositivityTheory.Rg.BcB.F.borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities.GelfandReading

def InfMatch : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (χ χ' : InfinitePlace E → Inf a),
  (∀ v s m, 1 ≤ m → 0 < a → GlobalTheory.Dec.gelfVal (χ v s) m = GlobalTheory.Dec.gelfVal (χ' v s) m) → mOf χ = mOf χ'

def InfMatchOf : Prop := gamma_zeta_nabla_cancel.GelfInj → InfMatch

def DerVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (μa : Measure (PositivityTheory.RgTw.G a)) (μb : Measure (PositivityTheory.RgTw.G b))
  (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) (κ : Type) [Fintype κ] (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)) (r r' : ℝ) (v : InfinitePlace E)
  (s : Bool) (k : ℕ) (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
  (A.pt (fun v' => if v' = v then [(s, k)] else []) (fun _ => []) ψ r).val χa χb =
      GlobalTheory.Dec.gelfVal (χa v s) k * (A.pt (fun _ => []) (fun _ => []) ψ' r').val χa χb ∧
    (A.pt (fun _ => []) (fun v' => if v' = v then [(s, k)] else []) ψ r).val χa χb =
      GlobalTheory.Dec.gelfVal (χb v s) k * (A.pt (fun _ => []) (fun _ => []) ψ' r').val χa χb

end UpperTheory.BaseChangeIdentities.GelfandReading

end
