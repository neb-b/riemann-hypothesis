module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0307
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PartFacts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.partFacts_pf :
    UpperTheory.Gal.Gen.PartFacts := by
  intro E _ _ _ a W C P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨I, F, h1, h2, rfl⟩ := GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms E a W C 1 f (fun c v g => by simpa using hf c.1 c.2 v g)
    refine Submodule.sum_mem _ fun π hπ => ?_
    have hfix : F π ∈ fixedBy W C := fun k hk v g => by simpa using h2 π hπ ⟨k, hk⟩ v g
    by_cases hP : P π.V
    · exact Submodule.mem_sup_left
        (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))
    · exact Submodule.mem_sup_right
        (Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩))
  · exact iSup₂_le fun π _ => inf_le_right
  · intro K hK
    refine iSup₂_mono fun π _ => inf_le_inf_left _ ?_
    intro f hf k hk v g
    exact hf k (hK hk) v g
  · intro x hx f hf
    have hle : part W C P ≤ (part W C P).comap (algRep W x) := by
      refine iSup₂_le fun π hP f hf => ?_
      refine Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨?_, ?_⟩)
      · exact AutSub.mem_finPart.2 fun v => π.isAut.stable x.1 _ (AutSub.mem_finPart.1 hf.1 v)
      · intro c hc v g
        change f.1 v (g * c * x.1) = f.1 v (g * x.1)
        have e : g * c * x.1 = g * x.1 * (x.1⁻¹ * c * x.1) := by group
        rw [e]
        exact hf.2 _ (hx c hc) v _
    exact hle hf
  · intro G hG
    obtain ⟨F, hF, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp
      (fun π : AutSub E a => ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C) G).1 hG
    refine ⟨F.support, F, fun π hπ => ?_, rfl⟩
    have h0 : F π ≠ 0 := Finsupp.mem_support_iff.1 hπ
    have hm : F π ∈ ⨆ (_ : P π.V), π.finPart W ⊓ fixedBy W C := hF π
    by_cases hP : P π.V
    · rw [iSup_pos hP] at hm
      exact ⟨hP, hm.1, hm.2, h0⟩
    · rw [iSup_neg hP] at hm
      exact absurd ((Submodule.mem_bot _).1 hm) h0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TwistPart
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.twistPart_pf :
    UpperTheory.Gal.Gen.TwistPart := by
  intro E _ _ _ a w₀ K W J A _ θ χ hC hK F hF
  let χ' : (lev K w₀ J) →* ℂˣ := χ.comp (θ.comp
    (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2))
  obtain ⟨I, G, h1, h2, rfl⟩ := GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms E a W (lev K w₀ J) χ' F fun c v g => hF c.1 c.2 v g
  refine Submodule.sum_mem _ fun π hπ => ?_
  by_cases h0 : G π = 0
  · rw [h0]
    exact zero_mem _
  have hlaw : ∀ c (hc : c ∈ lev K w₀ J) v g,
      (G π).1 v (g * c) = ((χ (θ ⟨cLoc w₀ c, hC c hc⟩) : ℂˣ) : ℂ) * (G π).1 v g :=
    fun c hc v g => h2 π hπ ⟨c, hc⟩ v g
  have hfix : G π ∈ fixedBy W K := fun k hk v g => by
    have hkC : k ∈ lev K w₀ J := (le_sup_left : K ≤ lev K w₀ J) hk
    have e : (⟨cLoc w₀ k, hC k hkC⟩ : J) = 1 := Subtype.ext (hK k hk)
    rw [hlaw k hkC v g, e]
    simp
  obtain ⟨v, hv⟩ : ∃ v, (G π).1 v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (Subtype.ext (LinearMap.ext hcon))
  have hP : GlobalTheory.CongW.HasTypeVec w₀ K J θ χ π.V :=
    ⟨(G π).1 v, AutSub.mem_finPart.1 (h1 π hπ) v, hv, fun x hx => funext fun g => hfix x hx v g,
      fun x hx h => funext fun g =>
        hlaw x ((le_sup_right : _ ≤ lev K w₀ J) ⟨hx, h⟩) v g⟩
  exact Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hP ⟨h1 π hπ, hfix⟩)
end

