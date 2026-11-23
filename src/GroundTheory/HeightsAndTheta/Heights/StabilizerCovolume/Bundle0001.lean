module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CardZBasisEqMulFinrank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights.LowerBoundFree
  Module Matrix
open scoped Matrix ComplexConjugate Kronecker

section Tower

variable {Em : Type} [Field Em] [NumberField Em]

def towerZBasis {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) :
    Basis (Fin ρ × (Em →+* ℂ)) ℤ (Submodule.span (𝓞 Em) (Set.range v)) :=
  ((RingOfIntegers.basis Em).smulTower' (Basis.span hv)).reindex
    (Equiv.prodCongr (Equiv.refl _) (equivReindex Em).symm)

theorem towerZBasis_apply {M : Type} [AddCommGroup M] [Module (𝓞 Em) M] {ρ : ℕ} {v : Fin ρ → M}
    (hv : LinearIndependent (𝓞 Em) v) (p : Fin ρ × (Em →+* ℂ)) :
    (towerZBasis hv p : M) = RingOfIntegers.basis Em (equivReindex Em p.2) • v p.1 := by
  simp [towerZBasis, Basis.smulTower'_apply, Basis.span_apply]


end Tower

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)



end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.TorusIndex
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

section Torus

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def baseChangeLat (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 Em) (Fin N → Em)) :
    Submodule (𝓞 K) ((Em →+* K) → Fin N → K) :=
  Submodule.span (𝓞 K) ((fun v σ a => σ (v a)) '' (I : Set (Fin N → Em)))


open Classical in
def eigenLat (I : Submodule (𝓞 Em) (Fin N → Em)) (s : Em →+* K) : Submodule (𝓞 K) (Fin N → K) :=
  (baseChangeLat K I).comap (LinearMap.single (𝓞 K) (fun _ : Em →+* K => Fin N → K) s)

def familyLat (s : Em →+* K) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) (Set.range fun a i => s (v a i))

def genIndex {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M) : ℝ :=
  (Q.relIndex P : ℝ) / (P.relIndex Q : ℝ)

def familyIndex (I : Submodule (𝓞 Em) (Fin N → Em)) {ρ : ℕ} (v : Fin ρ → Fin N → Em) : ℕ :=
  (Submodule.span (𝓞 Em) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup

end Torus

def TorusIndex.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)) (ρ : ℕ) (v : Fin ρ → Fin N → Em), IsNzFamily I ρ v →
    ∀ s : Em →+* K,
      genIndex (eigenLat I s).toAddSubgroup (familyLat s v).toAddSubgroup =
        ((familyIndex I v : ℝ) / |(discr Em : ℝ)| ^ ρ) ^ ((Module.finrank ℚ K : ℝ) / Module.finrank ℚ Em)

namespace Gauss

open Gauss

theorem split (ι σ : Em →+* ℂ) : ∃ t : Em →+* Em, ι.comp t = σ := by
  have hcc : (ι.comp (cc : Em →+* Em)) ζ = -ι ζ := by
    rw [RingHom.comp_apply]
    change ι (cc ζ) = -ι ζ
    rw [cc_ζ, map_neg]
  rcases emb_ζ σ with h | h <;> rcases emb_ζ ι with h0 | h0
  · exact ⟨RingHom.id _, ringHom_ext (by rw [RingHom.comp_id, h, h0])⟩
  · exact ⟨_, ringHom_ext (by rw [hcc, h, h0, neg_neg])⟩
  · exact ⟨_, ringHom_ext (by rw [hcc, h, h0])⟩
  · exact ⟨RingHom.id _, ringHom_ext (by rw [RingHom.comp_id, h, h0])⟩

def isoVec : Fin 2 → Em := fun _ => 1

def isoLine : Submodule (𝓞 Em) (Fin 2 → Em) := Submodule.span (𝓞 Em) {isoVec}

def isoFam : Fin 1 → Fin 2 → Em := fun _ => isoVec

theorem span_isoFam : Submodule.span (𝓞 Em) (Set.range isoFam) = isoLine := by
  show Submodule.span (𝓞 Em) (Set.range fun _ : Fin 1 => isoVec) = isoLine
  rw [Set.range_const]
  rfl

theorem isoFam_nz : IsNzFamily isoLine 1 isoFam := by
  refine ⟨le_rfl, fun _ => Submodule.subset_span rfl, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 ?_
    intro h
    have := congrFun h 0
    simp [isoFam, isoVec] at this
  · rw [span_isoFam, AddSubgroup.relIndex_self]
    exact one_ne_zero

end Gauss

end GroundTheory.Heights₂.Heights.NineStatements
end
end

