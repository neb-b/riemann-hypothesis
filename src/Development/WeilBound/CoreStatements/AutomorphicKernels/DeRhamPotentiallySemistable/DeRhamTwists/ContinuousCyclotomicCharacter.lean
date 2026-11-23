module

public import Development.WeilBound.CoreStatements.HeckeCharacterDeRham.DeRhamHeckeResults.PotentiallySemistableDeRham.SemistableDeRhamStatement.Second

@[expose] public section

noncomputable section

namespace DeRhamTwist.Twist

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime]

def chi0 (l : ℕ) [Fact l.Prime] : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (PadicAlgCl l) l).comp
    (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l))

theorem continuous_cyclotomic_character : Continuous (chi0 l) :=
  cyclotomicCharacter.continuous l ℚ_[l] (PadicAlgCl l)

theorem cycloChar_toBot (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    cycloChar ⊥ (toBot g) = chi0 l g := rfl

theorem tQ_eq : tQ l = algebraMap (BdRp l) (BdR l) (tBdR l) := by
  show algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
  exact congrArg (algebraMap (BdRp l) (BdR l))
    (ACris.iota_periodT (untilt_epsilon (p := l)))

theorem tQ_ne : tQ l ≠ 0 := by
  rw [tQ_eq]
  exact algebraMap_tBdR_ne_zero

end DeRhamTwist.Twist
