module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
public import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrincipalizationOfPrincipalisation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupport
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.VanishingIdealSmoothAgreesOff
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0011

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

open GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide GlobalTheory.CompanionTheory.Hypotheses₂.Resolution

theorem exists_centre_off {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k) (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁)
    (V : X₁.Opens) (h₀ : Smooth g) (h₁ : IsIntegral X₁) (h₂ : Smooth (Z.subschemeι ≫ g)) (h₃ : FinalTheorems.Blowup π Z)
    (h₄ : IsIso (π ∣_ V)) :
    ∃ Z' : X₁.IdealSheafData, Smooth (Z'.subschemeι ≫ g) ∧ (Z'.support : Set X₁) ⊆ (V : Set X₁)ᶜ ∧
      FinalTheorems.Blowup π Z' := by
  obtain ⟨hB, hA⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt g Z h₀ h₁ h₂
  let A : Closeds X₁ := ⟨_, hA⟩
  let O₁ : X₁.Opens := ⟨_, hB.isOpen_compl⟩
  let O₂ : X₁.Opens := ⟨_, hA.isOpen_compl⟩
  have hO₁ : (O₁ : Set X₁) = ((Z.support : Set X₁) \ A)ᶜ := by
    ext x
    change ¬ (x ∈ Z.support ∧ CartAt Z x) ↔ ¬ (x ∈ Z.support ∧ ¬ (x ∈ Z.support ∧ ¬ CartAt Z x))
    tauto
  obtain ⟨c₁, c₂⟩ := _root_.GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq g Z A O₁ h₂ (fun x hx => hx.1) hO₁
  have hV : FinalTheorems.EffCartier (Z.comap V.ι) := GlobalTheory.effCartier_comap_of_isIso_restrict π Z V h₄ h₃.1
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal A).support : Set X₁) = A :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal A
  refine ⟨_, c₁, ?_, _root_.GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open π Z _ O₁ O₂ h₃ ?_ c₂ ?_ ?_⟩
  · rw [hsupp]
    intro x hx hxV
    exact hx.2 ((_root_.GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff Z V).1 hV x hxV)
  · refine top_le_iff.1 fun x _ => ?_
    by_cases hx : x ∈ Z.support ∧ CartAt Z x
    · exact Or.inr fun h => h.2 hx.2
    · exact Or.inl hx
  · intro x hx hx'
    rw [← SetLike.mem_coe, hsupp] at hx'
    exact hx hx'
  · refine (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff Z O₂).2 fun x hx => ?_
    by_contra hc
    exact hx ⟨by_contra fun h => hc (GlobalTheory.T.cartier_at_of_not_mem_support Z x h), hc⟩

theorem isIntegral_of_seq {k : Type} [Field k] {X X' : Scheme.{0}} {g : X ⟶ Sp k} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') (hX : IsIntegral X) :
    Nonempty X' → Smooth (s ≫ g) → IsIntegral X' := by
  induction h with
  | id => exact fun _ _ => hX
  | @step X₁ X₂ s E₁ Z π h₁ h₂ h₃ h₄ h₅ ih =>
    intro hn hsm
    have : Nonempty X₁ := ⟨π hn.some⟩
    exact _root_.GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup (s ≫ g) Z π (ih this h₂) h₅ (by simpa using hsm) hn

theorem seq_of_iso {k : Type} [Field k] {X X' : Scheme.{0}} {g : X ⟶ Sp k} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') (hX : IsIntegral X) (hg : IsProjOver g) :
    Nonempty X' → ∀ V : X.Opens, IsIso (s ∣_ V) → IsSmoothBlowupSeq g (V : Set X)ᶜ s := by
  induction h with
  | id => exact fun _ _ _ => .id
  | @step X₁ X₂ s E₁ Z π h₁ h₂ h₃ h₄ h₅ ih =>
    intro hn V hV
    have : Nonempty X₁ := ⟨π hn.some⟩
    have hi : IsIntegral X₁ := isIntegral_of_seq h₁ hX this h₂
    have hp : IsProjOver (s ≫ g) :=
      (Resolution.IsBlowupSeq.of_smooth h₁.isSmoothBlowupSeq).isProjOver hg
    have hP : IsProper (s ≫ g) := isProper_of_isProjOver hp
    have hs : IsSeparated s := IsSeparated.of_comp s g
    obtain ⟨a, b⟩ := _root_.GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup s π Z V hi hs h₅ hn hV
    obtain ⟨Z', c₁, c₂, c₃⟩ := exists_centre_off (s ≫ g) Z π (s ⁻¹ᵁ V) h₂ hi h₃ h₅ b
    exact .step Z' π (ih this V a) c₁ c₂ c₃

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂


end GlobalTheory.CompanionTheory.Hypotheses₂
