module

public import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.SumUliftFinsetFinTwoExpand
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle0002

@[expose] public section

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

variable (D : D7)

instance totCx : IsTotallyComplex D.host.E :=
  (D.host.isCMField_hostE).to_isTotallyComplex

theorem conjugate_emb (g : D.R.GG) :
    ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  ext z
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  rw [show ((D.host.conj : D.host.E →+* D.host.E) z) = D.host.conj z from rfl, Formalism.MainNotions.WeightFamilies.emb_conj]
  rfl

theorem mk_tauEmb_injective : Function.Injective fun τ : D.what₂.Tau => InfinitePlace.mk (DV.tauEmb D τ) := by
  intro τ τ' h
  simp only at h
  rcases mk_eq_iff.1 h with h1 | h1
  · have h2 := (factEmb D.R D.host).1.1 h1
    exact D.eTau.injective (Subtype.ext h2)
  · exfalso
    unfold DV.tauEmb at h1
    rw [conjugate_emb] at h1
    have h2 := (factEmb D.R D.host).1.1 h1
    have hm := (D.eTau τ).2
    rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem] at hm
    exact hm (h2 ▸ (D.eTau τ').2)

theorem card_places : Fintype.card (InfinitePlace D.host.E) = Fintype.card D.what₂.Tau := by
  have h1 := DualLatticeEmbeddings.nPl_mul_two (K := D.host.E)
  rw [D.host.finrank_cmField] at h1
  have h2 : D.R.f = 2 * D.R.ord := rfl
  rw [D.what₂.card_Tau, h2]
  omega

def ePl : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨mk_tauEmb_injective D, (card_places D).symm⟩)

theorem finrank_E_eq : finrank ℚ D.host.E = 2 * D.R.f := by
  have h2 : D.R.f = 2 * D.R.ord := rfl
  rw [D.host.finrank_cmField, h2]
  ring

@[instance_reducible] def starE : StarRing D.host.E := starRingOfComm

attribute [local instance] starE

variable {D}

end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}

end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}

end Formalism.L2.Geo.Rec.StarEmbeddingNorm
