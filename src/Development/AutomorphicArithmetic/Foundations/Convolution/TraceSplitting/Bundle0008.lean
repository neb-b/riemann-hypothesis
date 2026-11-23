module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
section
theorem UpperTheory.ConvolutionTheory.T.liftAll :
    UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll := by
  intro h F E _ _ _ _ _ _ _ _ σ hσ hp n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn π
    induction π using Quotient.inductionOn with
    | _ π =>
      rcases h F E σ hσ hp n hn (fun m h1 h2 => ih m h2 h1) π with ⟨ι, hι, m, Q, hm, hc, hw⟩ | ⟨P, hP, -⟩
      · exact ⟨ι, hι, m, Q, hm, Fintype.card_pos_iff.1 (by omega), hw⟩
      · refine ⟨Unit, inferInstance, fun _ => n, fun _ => GlobalTheory.CuspRep.CG.mk P, fun _ => hn, ⟨()⟩, ?_⟩
        rw [UpperTheory.ConvolutionTheory.R.sumSat_unit]
        exact hP.1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStrong
section
theorem UpperTheory.ConvolutionTheory.T.splitStrong :
    UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong := by
  intro hD F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hc hw v w i hi hcomp τ τ' hτ hτ'
  obtain ⟨-, -, -, -, -, hpl⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨hs, u, rfl, hiu⟩ := hpl v w i hi hcomp
  obtain ⟨π', hl, hloc⟩ := hD F E σ hσ hp n hn P hc v u hs
  obtain ⟨η, hη, hiso⟩ := (UpperTheory.ConvolutionTheory.R.fibre_holds F E hp n hn (.cx π') (.cx P) hl.1).2 (.cx π) hw
  have he : π'.twist η = π := (UpperTheory.ConvolutionTheory.Dp.isoEq F n (π'.twist η) π).1 hiso
  subst he
  have hτ₀ : (UpperTheory.CBC.Cusp.cx π').locComp v τ := by
    rcases hη with rfl | hη
    · simpa [GlobalTheory.CuspRep.CuspSub.twist_one] using hτ
    · exact (UpperTheory.ConvolutionTheory.T.normCharSplit F E σ hσ hp n hn η hη v hs π' τ).1 hτ
  obtain ⟨e, he⟩ := hloc τ τ' hτ₀ hτ'
  have hm : i.toRingHom = GroundTheory.Global.SemiLocal.completionMap v u.1 := RingHom.ext hiu
  refine ⟨e, fun g x => ?_⟩
  rw [hm]
  exact he g x
end

