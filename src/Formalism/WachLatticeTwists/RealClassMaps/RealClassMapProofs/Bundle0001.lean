module

public import Formalism.WachLatticeTwists.RealClassMaps.Bundle0001
public import Formalism.WachLatticeTwists.RealClassMaps.Statement
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Imports
public import Formalism.WachLatticeTwists.CupProductVanishing.Imports

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.ClsRowVOfMem
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG toH1Cocycles traceH1 transportCocycles)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem kRowRange (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (M : Type) [AddCommGroup M] [Module O M] (ρM : Representation O G M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m))
    (hopen : IsOpen (D.T : Set VT)) : LinearMap.range (kRow D ρM u hu) = lcH1 ρM := by
  have hdisc : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hopen
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      refine ⟨transportCocycles (MulEquiv.refl G) u ρM D.ρA hu ⟨c.1, c.2.2⟩, ?_, rfl⟩
      have h1 : IsLocallyConstant c.1 := (IsLocallyConstant.iff_continuous _).2 c.2.1
      exact h1.comp u.symm
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : IsLocallyConstant (c : G → M) := hc
    have h3 : (fun g : G => u ((c : G → M) g)) ∈ Z1 D.ρA := by
      refine ⟨(hc'.comp u).continuous, fun a b => ?_⟩
      beta_reduce
      rw [c.2, map_add (f := _), hu]
    refine ⟨Submodule.Quotient.mk ⟨_, h3⟩, ?_⟩
    refine congrArg (Submodule.mkQ _) (Subtype.ext (funext fun g => ?_))
    change u.symm (u ((c : G → M) g)) = _
    rw [LinearEquiv.symm_apply_apply]

theorem resLC (O G M : Type) [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (Dw : Subgroup G) :
    lcH1 ρ ≤ (lcH1 (resRep ρ Dw)).comap (resH1 ρ Dw) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : IsLocallyConstant (c : G → M) := hc
  refine ⟨restrictCocycles1 ρ Dw c, ?_, rfl⟩
  exact hc'.comp_continuous continuous_subtype_val

section
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

theorem clsRow_of_mem (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T')
    (f : Γ → T₂) (h : (fun g => v (f g)) ∈ Z1 D.ρTl') : clsRow D v f = Submodule.Quotient.mk ⟨_, h⟩ :=
  dif_pos h

end

end Formalism.RepresentationBoundsCohomology.FIN
end
end

-- bundled from Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.RowChiReal
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

set_option maxHeartbeats 1000000 in
theorem rowRhoReal : StatRowRhoReal := by
  intro p _ O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ek Ω _ _ _ _ _ Aw hp A T' _ _ _ _ _ _ _
    M _ _ _ _ r χ E ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ D u hu v familyMassRatio iS1 familyMassSecondLine iS2 HfV HfV' Fs Im hO hF hA hcyc hε hD hπ
    hv hγ hBK hFs hRow hk
  obtain ⟨K, hK, i, h1, -, -⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp
  have hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype := by
    ext g; simp [hε g]
  have hcD : IsCyc p K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) := h1 O D.ε (hεD ▸ hcyc)
  obtain ⟨inv, invF, hc⟩ := ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso hK hO hF i hcD
  have hD' : RealLatG i (withInv D inv.toLinearMap invF.toLinearMap) :=
    ⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩
  let j1 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := familyMassRatio
  have j2 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := iS1
  let j3 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := familyMassSecondLine
  have j4 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := iS2
  have hBK' : ∀ a, a ∈ HfV ↔ ∀ b ∈ HfV',
      fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap)) a b = 0 := by
    intro a
    rw [hBK a]
    refine forall₂_congr fun b _ => ?_
    show _ ↔ invF (cupFG D a b) = 0
    rw [LinearEquiv.map_eq_zero_iff]
  obtain ⟨_, hbk⟩ := bkInRow p K O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek)
    (withInv D inv.toLinearMap invF.toLinearMap) i u hu HfV HfV' hK hO hF hD' inv.injective invF.injective hc hBK'
  obtain ⟨C₁, c1, c2, c3, c3', c6, c7⟩ := hRow
  let pairD := fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap))
  refine ⟨prK (withInv D inv.toLinearMap invF.toLinearMap) _ hk, pairD, ?_, ?_⟩
  · rw [hFs]; exact hbk
  · refine ⟨C₁, fun z => Continuous fun q : _ × _ => z q.1 q.2, fun f => Continuous f, fun f => Continuous f,
      fun f => Continuous f, c1, c2, c3, ?_, ?_, c6, c7⟩
    · exact clause4GK p K O A T' _ r χ E (Aw.decompositionSubgroup Ek) ε hK hO i (hεD ▸ hcD) hA
    · exact clause5Row O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) ε T₁ T₂ ρ₁ ρ₂ π γ
        (withInv D inv.toLinearMap invF.toLinearMap) u hu v hε hD.contT hπ hv hγ hk C₁ c3'


end Formalism.RepresentationBoundsCohomology.FIN
end
end

