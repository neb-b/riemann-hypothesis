module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsAdm
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_admissible (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (μ : Fin n → ℝ) :
    FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) := by
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hE := hD.glRep
  obtain ⟨k, hk⟩ := khw_mem_layer hE hU hV hc hgap μ
  have hLf : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hV.1 k
  have hLK := kStable_of_isKStableSub hσ hD (layer ε E V k) hLf (layer_kStable hE hV.2.1 k)
  have hMf : FiniteDimensional ℂ ((layer ε E V k).map D.subtype) := Module.Finite.map _ _
  have hle : (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) ≤
      (layer ε E V k).map D.subtype := by
    refine sSup_le fun S hSmem => ?_
    obtain ⟨hS, hST⟩ := hSmem
    obtain ⟨hSf, hSK, hirr, -, -⟩ := id hST
    have hSM := data_kfin_le hgap hσ hD hV hc hVK S hS hSf (fun g hg x hx => hSK g hg x hx)
    have hSD : S ≤ D := hSM.trans (Submodule.map_subtype_le _ _)
    obtain ⟨w, hwS, hw0, hwμ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
    have hwg : w ∈ genSub E V := by
      obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
      have : y = w := Subtype.ext hyw
      exact this ▸ hy
    have hwL := hk w hwg hwμ
    have hS'K : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ (layer ε E V k).map D.subtype) := by
      intro g hg v hv
      refine ⟨hSK g hg v hv.1, ?_⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
      obtain ⟨z, hz, hzeq⟩ := hLK g hg y hy
      exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
    rcases hirr _ inf_le_left hS'K with h0 | hEq
    · exfalso
      have hmem : (w : H) ∈ S ⊓ (layer ε E V k).map D.subtype :=
        ⟨hwS, Submodule.mem_map_of_mem hwL⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hw0 (Subtype.ext hmem)
    · rw [← hEq]
      exact inf_le_right
  exact Submodule.finiteDimensional_of_le hle

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsLowK
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_lowK_eq (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) S) : S = V.map D.subtype := by
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  have hSf : FiniteDimensional ℂ S := hST.1
  have hSK : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S := hST.2.1
  have hSgen : S ≤ (genSub E V).map D.subtype :=
    ReciprocityTheory.ChartRestriction.DS.G2.data_kfin_le ⟨hmono, h, hh, hbig⟩ hσ hD hV hc hVK S hS hSf hSK
  have hSD : S ≤ D := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hSgen hx
    exact y.2
  obtain ⟨w, hwS, hw0, hwK⟩ := ReciprocityTheory.ChartRestriction.DS.exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
  have hwG : w ∈ genSub E V := by
    obtain ⟨y, hy, hyw⟩ := hSgen hwS
    have : y = w := Subtype.ext hyw
    exact this ▸ hy
  obtain ⟨w₀, hw₀V, -, m, ws, hwsum, hws⟩ :=
    ReciprocityTheory.ChartRestriction.DS.G2.k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hwG hwK
  have hz : ∀ j, ws j = 0 := by
    intro j
    by_contra hne
    obtain ⟨-, hpos, hle⟩ := (hws j).2 hne
    have : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hwV : w ∈ V := by
    rw [hwsum, Finset.sum_eq_zero (fun j _ => hz j), add_zero]
    exact hw₀V
  have hVT := ReciprocityTheory.ChartRestriction.DS.G2.data_isKTypeOf ⟨hmono, h, hh, hbig⟩ hσ hD hV hc hVK
  have hwVm : (w : H) ∈ V.map D.subtype := ⟨w, hwV, rfl⟩
  have hwne : (w : H) ≠ 0 := fun h0 => hw0 (Submodule.coe_eq_zero.1 h0)
  have hinf : S ⊓ V.map D.subtype = S := by
    rcases hST.2.2.1 (S ⊓ V.map D.subtype) inf_le_left
      (fun g hg v hv => ⟨hST.2.1 g hg v hv.1, hVT.2.1 g hg v hv.2⟩) with h0 | h1
    · exfalso
      apply hwne
      have hm : (w : H) ∈ S ⊓ V.map D.subtype := ⟨hwS, hwVm⟩
      rw [h0] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · exact h1
  have hSV : S ≤ V.map D.subtype := by
    rw [← hinf]
    exact inf_le_right
  rcases hVT.2.2.1 S hSV hST.2.1 with h0 | h1
  · exfalso
    apply hwne
    rw [h0] at hwS
    exact (Submodule.mem_bot ℂ).1 hwS
  · exact h1

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

