module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellP
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.UnipotentAdelicQuotients.Bundle0002

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

theorem exists_norm_lt_one' : ∃ ϖ : Fv F v, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  exact NormedField.exists_norm_lt_one _

variable {v}

theorem continuous_psiV' {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) : Continuous (psiV F ψ v) :=
  ((_root_.GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v).1

theorem psiV_add' (ψ : AddChar (AF F) ℂ) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y := by
  have h : pairA F 0 (singleV F v (x + y)) = pairA F 0 (singleV F v x) + pairA F 0 (singleV F v y) := by
    simp only [pairA, singleV, RestrictedProduct.single_add]
    exact Prod.ext (add_zero _).symm rfl
  simp only [psiV]; rw [h, AddChar.map_add_eq_mul]

theorem psiV_zero' (ψ : AddChar (AF F) ℂ) : psiV F ψ v 0 = 1 := by
  have h : pairA F 0 (singleV F v 0) = 0 := by
    simp only [pairA, singleV, RestrictedProduct.single_zero]; rfl
  simp only [psiV]; rw [h, AddChar.map_zero_eq_one]

theorem norm_psiV' {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : Fv F v) : ‖psiV F ψ v x‖ = 1 :=
  hψ.2.1 _

theorem exists_psiV_ne_one' {σ : E →ₐ[F] E} (_hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ y, psiV F ψ v y ≠ 1 :=
  ((_root_.GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v).2

end PositivityTheory.SiegelWeilFormula.SwLocFin
