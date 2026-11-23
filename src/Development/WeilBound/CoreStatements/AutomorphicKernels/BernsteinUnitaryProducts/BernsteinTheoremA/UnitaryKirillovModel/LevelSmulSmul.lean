module

public import Mathlib
public import GroundTheory.AutomorphicForms.ContragredientTranspose.Character
public import GroundTheory.AutomorphicForms.Bundle0004

@[expose] public section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

section Level

variable {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

theorem level_smul_smul (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    (c • h) • w = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((c • (h : HeckeAlgebra μ) : HeckeAlgebra μ) : G → ℂ) (w : V) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  rw [HeckeAlgebra.coe_smul]
  exact heckeAct_smul_left c (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo w.2))

theorem level_smul_comm (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    h • (c • w) = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (c • (w : V)) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  exact heckeAct_smul_right (h : HeckeAlgebra μ).mem c (smooth_of_mem_fixedVectors hKo w.2))

theorem level_schur (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (φ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) :
    ∃ c : ℂ, ∀ w, φ w = c • w := by
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let φℂ : Module.End ℂ (fixedVectors ρ K) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c w => by
        have e : c • w = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) • w := by
          rw [level_smul_smul, one_smul]
        rw [RingHom.id_apply, e, φ.map_smul, level_smul_smul, one_smul] }
  have hnt : Nontrivial (fixedVectors ρ K) := Submodule.nontrivial_iff_ne_bot.2 hK
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φℂ
  obtain ⟨w₀, hw₀⟩ := hc.exists_hasEigenvector
  let ψ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) :=
    { toFun := fun w => φ w - c • w
      map_add' := fun a b => by rw [map_add (f := _), smul_add]; abel
      map_smul' := fun h w => by rw [RingHom.id_apply, φ.map_smul, smul_sub, level_smul_comm] }
  have hw₀ker : w₀ ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    show φ w₀ - c • w₀ = 0
    rw [sub_eq_zero]
    exact Module.End.mem_eigenspace_iff.1 hw₀.1
  have hker : LinearMap.ker ψ ≠ ⊥ := fun hb => hw₀.2 (by rw [hb] at hw₀ker; exact (Submodule.mem_bot _).1 hw₀ker)
  have htop := (eq_bot_or_eq_top (LinearMap.ker ψ)).resolve_left hker
  refine ⟨c, fun w => ?_⟩
  have hw : w ∈ LinearMap.ker ψ := by rw [htop]; exact Submodule.mem_top
  exact sub_eq_zero.1 hw

theorem level_density (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (A : Module.End ℂ (fixedVectors ρ K)) :
    ∃ r : HeckeAlgebraLevel μ K hKc hKo, levelLin hKc hKo ρ r = A := by
  classical
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let fE : Module.End (Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) (fixedVectors ρ K) :=
    { toFun := A
      map_add' := A.map_add
      map_smul' := fun φ w => by
        rw [Module.End.smul_def, RingHom.id_apply, Module.End.smul_def]
        obtain ⟨c, hc⟩ := level_schur hKc hKo hρ hK φ
        rw [hc, hc, A.map_smul] }
  let b := Module.finBasis ℂ (fixedVectors ρ K)
  obtain ⟨r, hr⟩ := jacobson_density fE (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  have := hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this.symm

end Level

end Faith

end PositivityTheory.PfBern.Unit
