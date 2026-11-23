module

public import Mathlib
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd
public import Formalism.SharpRestriction.GrowthBounds.ColumnSystems
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
public import Formalism.SharpRestriction.GrowthBounds.ObjSeg
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSubgroup
section
theorem UpperTheory.Reformulated.B.ConjugateSubgroup.conj_sub :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    {Γ A : Subgroup G},
    IsClosed (↑A : Set G) →
      PositivityTheory.ThKEnd.Two.Lat (Γ.subgroupOf A) →
        ∀ {f c : G → ℂ},
          PositivityTheory.ThKEnd.Two.IsAv (Γ.subgroupOf A) Subtype.val f c →
            ∀ {γ : G},
              γ ∈ Γ →
                (∀ u ∈ A, γ⁻¹ * u * γ ∈ A) →
                  (∀ u ∈ A, γ * u * γ⁻¹ ∈ A) →
                    (∀ (x : G), f (γ * x) = f x) →
                      ∀ (x : G),
                        c (γ * x) =
                          c
                            x := by
  intro G _ _ _ _ _ _ _ _ Γ A hA L f c h γ hγ h1 h2 hf x
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology A := Topology.IsInducing.subtypeVal.secondCountableTopology
  let e : A ≃ₜ* A :=
    { toFun := fun u => ⟨γ⁻¹ * u * γ, h1 u u.2⟩
      invFun := fun u => ⟨γ * u * γ⁻¹, h2 u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk (by fun_prop) _
      continuous_invFun := Continuous.subtype_mk (by fun_prop) _ }
  refine PositivityTheory.ThKEnd.Two.IsAv.conj (ι := A.subtype) L h e (fun u => ?_) (fun u => ?_) hf x
  · exact (Γ.mul_mem_cancel_right hγ).trans (Γ.mul_mem_cancel_left (inv_mem hγ))
  · exact show (u : G) * γ = γ * (γ⁻¹ * u * γ) by group
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SymmetricFamilySpan
section
private theorem UpperTheory.Reformulated.B.SymmetricFamilySpan.prod_span_mem {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [Fintype ι] {V : ι → Type*} [∀ j, AddCommMonoid (V j)] [∀ j, Module R (V j)] (L : ∀ j, V j →ₗ[R] A)
    (G : ∀ j, Set (V j)) (M : Submodule R A) (h : ∀ s : ∀ j, V j, (∀ j, s j ∈ G j) → ∏ j, L j (s j) ∈ M)
    (s : ∀ j, V j) (hs : ∀ j, s j ∈ Submodule.span R (G j)) : ∏ j, L j (s j) ∈ M := by
  have h1 : ∏ j, L j (s j) ∈ ∏ j, Submodule.span R (L j '' G j) :=
    Finset.prod_hom_rel (r := fun (a : A) (N : Submodule R A) => a ∈ N) (Submodule.one_le.1 le_rfl)
      (fun j a N ha => Submodule.mul_mem_mul (Submodule.apply_mem_span_image_of_mem_span _ (hs j)) ha)
  rw [Submodule.prod_span] at h1
  refine Submodule.span_le.2 (fun x hx => ?_) h1
  obtain ⟨f, hf, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
  choose t ht e using hf
  simpa only [e, SetLike.mem_coe] using h t ht

theorem UpperTheory.Reformulated.B.SymmetricFamilySpan.symFam_span :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] {C0 CE1 CE2 : ℝ}
    {X : Formalism.MainNotions.ColumnSystems.Loc} (β : Formalism.MainNotions.ColumnSystems.Pf.GlobalTheory X)
    (G :
      (j : Fin (Formalism.MainNotions.G.numSeg X.TT)) →
        Set
          (MvPolynomial (Formalism.MainNotions.G.BVar ((2 : ℕ) * Formalism.MainNotions.G.segS X.TT j + (1 : ℕ)) X.m (X.seg C0 CE1 CE2 j).t)
            (Formalism.MainNotions.G.KK O)))
    (M : Submodule O (MvPolynomial ((↥X.TT × Bool) × Fin (X.m + (1 : ℕ))) (Formalism.MainNotions.G.KK O))),
    (∀ (s : Formalism.MainNotions.ColumnSystems.Pf.Syms O C0 CE1 CE2 X),
        (∀ (j : Fin (Formalism.MainNotions.G.numSeg X.TT)), s j ∈ G j) → Formalism.MainNotions.ColumnSystems.Pf.symFam (Formalism.MainNotions.G.KK O) X.p C0 CE1 CE2 X β s ∈ M) →
      ∀ (s : Formalism.MainNotions.ColumnSystems.Pf.Syms O C0 CE1 CE2 X),
        (∀ (j : Fin (Formalism.MainNotions.G.numSeg X.TT)), s j ∈ Submodule.span O (G j)) →
          Formalism.MainNotions.ColumnSystems.Pf.symFam (Formalism.MainNotions.G.KK O) X.p C0 CE1 CE2 X β s ∈
            M := by
  intro O _ _ C0 CE1 CE2 X β G M h s hs
  open Formalism.MainNotions.ColumnSystems.Pf Formalism.MainNotions.G in exact UpperTheory.Reformulated.B.SymmetricFamilySpan.prod_span_mem (fun j =>
                                            (LinearMap.mulLeft O (digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j))).comp
                                            ((MvPolynomial.aeval (R := KK O) (fun v => MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^
                                              symLev X.p C0 CE1 CE2 X j v)).toLinearMap.restrictScalars O)) G M h s hs
end

