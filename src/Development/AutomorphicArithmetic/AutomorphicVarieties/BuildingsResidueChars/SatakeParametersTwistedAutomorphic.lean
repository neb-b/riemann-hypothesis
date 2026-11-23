module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.EulerdShift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0001

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem cnt_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) (h : ∀ ζ ∈ chars s, ¬ IsUnram (ζ * χ)) : cnt s χ = 0 := by
  unfold cnt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro y hy ⟨ζ, hζ, rfl, hu⟩
  exact h ζ ⟨hζ, hy⟩ hu

private theorem pol_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL (k := k))) (χ : kˣ →* ℂˣ) (h : cnt s χ = 0) : pol s χ = 1 := by
  obtain ⟨h0, hd, -⟩ := (polFacts k).2.2.2 s χ
  have e := eq_C_of_natDegree_eq_zero (hd.trans h)
  rw [e, eval_C] at h0
  rw [e, h0, C_1]
