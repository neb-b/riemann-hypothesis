module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

noncomputable section

namespace PositivityTheory.RgEis

def Twist : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (Γ K S P P' : Subgroup G) (c c₀ : G → ℂ) (η η' β ξ : G → ℝ) (N : ℝ), IsCompact (K : Set G) → IsCh Γ ⊤ c₀ →
    IsPar Γ K S c → IsPar Γ K P c → IsPar Γ K P' c →
    ((AllRep K fun ρ => HasWall Γ K P P' c η η' β ρ) → AllRep K fun ρ => HasWall Γ K P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasFirst Γ K S P P' c η η' β ρ) → AllRep K fun ρ => HasFirst Γ K S P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasLast Γ K S P P' c η η' β ξ N ρ) → AllRep K fun ρ => HasLast Γ K S P P' (c * c₀) η η' β ξ N ρ)

def Scale : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β l : G → ℝ) (s : ℝ), 0 < s →
  IsHt Γ K ⊤ l → HasWall Γ K P P' c η η' β ρ →
  HasWall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ

end PositivityTheory.RgEis
