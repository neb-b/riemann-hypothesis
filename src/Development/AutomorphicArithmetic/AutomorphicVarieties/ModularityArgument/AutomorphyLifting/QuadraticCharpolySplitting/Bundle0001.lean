module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.RcChars
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands
open GlobalTheory.PRep GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_of_chars {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : UpperTheory.Zero.LLC.LawsT a ha rc) (x : IrrGL (k := w.adicCompletion E)) {n : ℕ}
    (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hs : HasSupport x.rep (GlobalTheory.RoadU.chars ξ hξ)) (g : Weil h) :
    (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨hG, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  obtain ⟨𝔪, hm⟩ := GlobalTheory.langlandsExhaustionGL_holds (w.adicCompletion E) x
  have he : GlobalTheory.RoadU.chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hZ _ x _ _ hs
      (GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm)
  have hsum : (rc x).charPol g = ((msupp 𝔪).map fun y => (rc y).charPol g).prod := by
    rw [H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
      msupp, Multiset.map_bind, Multiset.prod_bind]
    have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
        (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
    rw [hl, Multiset.coe_toList]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => GlobalTheory.RoadU.CharSupport.charPol_seg H Δ g)
  rw [hsum, ← he, GlobalTheory.RoadU.chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => ?_)
  simp only [Function.comp_apply]
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

end UpperTheory.V.Z.Win
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.ThruLoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

section Res

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
  [IsScalarTower K L Ω] {A : ValuationSubring Ω}

theorem mem_ine_res_iff (t : G L Ω) :
    (AlgEquiv.restrictScalarsHom K t : G K Ω) ∈ Ine (F := K) A ↔ t ∈ Ine (F := L) A := Iff.rfl

def ineRes : Ine (F := L) A →* Ine (F := K) A :=
  ((AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω).comp (Ine (F := L) A).subtype).codRestrict _ fun t =>
    (mem_ine_res_iff (K := K) (t : G L Ω)).2 t.2

variable [IsAlgClosure K Ω] [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
  {hK : IsPlaceOver A v} {hL : IsPlaceOver A w}

theorem isSmooth_of_ine [FiniteDimensional K L] {aL : Weil hL →* (w.adicCompletion L)ˣ} (haL : IsLocalArtin hL aL)
    {ζ : (w.adicCompletion L)ˣ →* ℂˣ} (hζ : IsSmoothChar ζ) (θ : Weil hK →* ℂˣ)
    (hθ : ∀ t : Ine (F := L) A, θ (ineIncl hK (ineRes (K := K) t)) = ζ (aL (ineIncl hL t))) : IsSmooth θ := by
  have hV : IsOpen {t : Ine (F := L) A | ζ (aL (ineIncl hL t)) = 1} := haL.smooth hζ
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.1 hV
  have h1W : (1 : G L Ω) ∈ W := by
    have h1 : (1 : Ine (F := L) A) ∈ Subtype.val ⁻¹' W := by
      rw [hWV]
      simp
    exact h1
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff L Ω W).1 (hW.mem_nhds h1W)
  haveI := hE
  have hN : IsOpen ((Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup : Subgroup (G K Ω)) :
      Set (G K Ω)) := GlobalTheory.KLift.isOpen_map_restrictScalars _ E.fixingSubgroup_isOpen
  refine IsSmooth.of_open (hN.preimage continuous_subtype_val) ?_ ?_
  · show ((1 : Ine (F := K) A) : G K Ω) ∈ Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup
    exact Subgroup.one_mem _
  · intro σ hσ
    have hσ' : (σ : G K Ω) ∈ Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup := hσ
    obtain ⟨n, hn, hnσ⟩ := Subgroup.mem_map.1 hσ'
    have hnI : n ∈ Ine (F := L) A := (mem_ine_res_iff (K := K) n).1 (by rw [hnσ]; exact σ.2)
    have hres : ineRes (K := K) (⟨n, hnI⟩ : Ine (F := L) A) = σ := Subtype.ext hnσ
    have ht : (⟨n, hnI⟩ : Ine (F := L) A) ∈ {t : Ine (F := L) A | ζ (aL (ineIncl hL t)) = 1} := by
      rw [← hWV]
      exact hEW hn
    rw [← hres, hθ]
    exact ht

theorem exists_char_of_ine [FiniteDimensional K L] [w.asIdeal.LiesOver v.asIdeal]
    {aK : Weil hK →* (v.adicCompletion K)ˣ} (haK : IsLocalArtin hK aK)
    {aL : Weil hL →* (w.adicCompletion L)ˣ} (haL : IsLocalArtin hL aL)
    {ζ : (w.adicCompletion L)ˣ →* ℂˣ} (hζ : IsSmoothChar ζ) (θ : Weil hK →* ℂˣ)
    (hθ : ∀ t : Ine (F := L) A, θ (ineIncl hK (ineRes (K := K) t)) = ζ (aL (ineIncl hL t))) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ ∀ x : (w.adicCompletion L)ˣ,
      ord (w.adicCompletion L) x = 0 → ζ x = χ (GlobalTheory.BCChar.normU v w x) := by
  obtain ⟨χ, hχ, hθχ⟩ := haK.factor θ (isSmooth_of_ine haL hζ θ hθ)
  refine ⟨χ, hχ, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := haL.surj x
  have hdeg : deg g = 0 := by
    have h := haL.ord_eq g
    rw [hx] at h
    omega
  have hI : (g : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.1 hdeg
  have hg : ineIncl hL (⟨g, hI⟩ : Ine (F := L) A) = g := Subtype.ext rfl
  have key := GlobalTheory.T.localArtin_comp_norm_compat K L Ω A v w hK hL aK aL haK haL
    (ineIncl hK (ineRes (K := K) (⟨g, hI⟩ : Ine (F := L) A))) (ineIncl hL ⟨g, hI⟩) (fun _ => rfl)
  rw [← hg, ← hθ, hθχ, MonoidHom.comp_apply, key]

end Res

end UpperTheory.V.Z.Win
end
end

