module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.VVRank (pullS isPullSec_pullS)
open GlobalTheory.TwistBaseChange (eq_pullS_of_isPullSec)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaRuleCompare

section Descent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem sec_ext {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

omit [GrpObj A] in
theorem chart_ge {T T' : Over S} (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j ≤ (LPow A L a T').U j := by
  intro y hy
  have h1 : ((h ▷ A).left ≫ (snd T A).left).base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  rw [← Over.comp_left, whiskerRight_snd] at h1
  exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1

theorem gs_pullS {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((pullS A a h s).f j) = gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    pullS A a h' (pullS A a h s) = pullS A a (h' ≫ h) s :=
  sec_ext fun j => fn_ext fun y hy => by
    refine (gs_pullS h' _ _ y j hy).trans ((gs_pullS h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

end Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

section Auxiliary

variable (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

end Auxiliary

section Translates

variable (Xo : Moduli Dw l)

variable {Xo}

end Translates

section Values

variable {Xo : Moduli Dw l} {c : Coeff l}

end Values

end GlobalTheory.ThetaRuleCompare
