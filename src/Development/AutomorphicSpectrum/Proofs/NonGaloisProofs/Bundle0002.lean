module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasis

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCoboundary
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

theorem GlobalTheory.CompanionTheory.LocDual.cup_flip_cob {G W W' R : Type} [Group G] [TopologicalSpace G] [AddCommGroup W]
    [AddCommGroup W'] [CommRing R] (χ : G → R) (a : G → W →+ W) (a' : G → W' →+ W') (P : W →+ W' →+ R)
    (hP : ∀ g x y, P (a g x) (a' g y) = χ g * P x y) (y : G → W) (x : G → W')
    (hy : IsLocallyConstant y ∧ ∀ g h, y (g * h) = y g + a g (y h))
    (hx : IsLocallyConstant x ∧ ∀ g h, x (g * h) = x g + a' g (x h)) (z z' : G × G → R)
    (hz : (z = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z' = (fun p => P (a p.1 (y p.2)) (x p.1))) ∨
      (z' = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z = (fun p => P (a p.1 (y p.2)) (x p.1))))
    (h : ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z (g, h)) :
    ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z' (g, h) := by
  obtain ⟨f, hf, hfd⟩ := h
  have hlc : IsLocallyConstant fun g => P (y g) (x g) :=
    IsLocallyConstant.comp₂ hy.1 hx.1 fun u v => P u v
  have hid : ∀ g h, χ g * P (y h) (x h) - P (y (g * h)) (x (g * h)) + P (y g) (x g) =
      -P (y g) (a' g (x h)) - P (a g (y h)) (x g) := by
    intro g h
    rw [hy.2, hx.2, ← hP]
    simp only [map_add (f := _), AddMonoidHom.add_apply]
    abel
  refine ⟨fun g => -P (y g) (x g) - f g, (hlc.neg).sub hf, fun g h => ?_⟩
  have h1 := hid g h
  have h2 := hfd g h
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only at h2 ⊢ <;> linear_combination -h1 - h2
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodO_adic_complete_compact_basis : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ ϖ : O, Irreducible ϖ → IsAdicComplete (Ideal.span {ϖ}) O ∧ Finite (O ⧸ Ideal.span {ϖ}) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∃ e : ℕ, (l : O) ∈ Ideal.span {ϖ} ∧ ϖ ^ e ∈ Ideal.span {(l : O)}) ∧ (nhds (0 : LL)).HasBasis (fun _ : ℕ => True) (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ) ∧ ∀ u : ℤ_[l], algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ Set.range (algebraMap O LL) := by
  first | exact @GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure | exact GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure | (intros; apply GlobalTheory.CompanionTheory.GoodCoeff.goodO_structure <;> assumption)
end

