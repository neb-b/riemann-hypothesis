module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.LevelX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JPT

@[expose] public section

open UpperTheory.V UpperTheory.V.Th UpperTheory.V.Hi UpperTheory.V.Hi.CaseU

theorem UpperTheory.V.Th.hidaX :
    Af.HypothesesH → HidaX := by
  intro P l _ L Ω _ _ _ _ _ _ s V hS c n hn r B Λ ι
  obtain ⟨R⟩ := hdEx P l L Ω s n hn V (QData.empty V hS) c r ι Λ
  let K : (hset (QData.empty V hS) R.τ₀).Lev := ⟨fun q => Empty.elim q, fun q => Empty.elim q⟩
  obtain ⟨J, hJ⟩ := jEx P l L Ω s n hn V _ c r ι B Λ R K
  exact ⟨J, jPT P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, Th.AnnihilatorQuotientFinite.levelX P l L Ω s n hn V _ c r ι B Λ R K hS J hJ⟩
