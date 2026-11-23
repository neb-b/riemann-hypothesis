module

public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.GmapLocEqOfFrame

@[expose] public section

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_isom_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (p : Ideal (𝓞 K)) (hp : p.IsMaximal)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p I) = Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hpos := isTotPosDef_of_ortho hK hs hI
  have hd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hne φ
    rw [hx, map_zero] at this
    simp at this
  obtain ⟨e, -, hspan, rfl, he⟩ := hI
  have hS : WA.IsHermSemilocal (WA.locRing p) :=
    { star_mem := fun _ ha => WA.star_mem_locRing hp.isPrime ha
      frac := WA.frac_locRing p
      unram := WA.unram_locRing hK hp
      principal := WA.principal_locRing hK hp
      unit_or := fun a ha κ hκ μ hna hμ => WA.unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ }
  obtain ⟨g, hg, hge⟩ := WA.exists_isom_frame hS hs hd
    (WA.isSelfDualMod_loc hL hp.isPrime hu) e he
  exact ⟨g, hg, WA.gmap_loc_eq_of_frame hp.isPrime hu hspan he hg hge⟩

end ReciprocityTheory.ChartRestriction.L3
