module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X : Var F} {σ : F →+* ℂ}

theorem exists_ratVal_hom (y : CxPts X.str σ) :
    ∃ ψ : ((ratOf X).O (under y)).toSubring →+* ℂ, ∀ x : ((ratOf X).O (under y)).toSubring, ratVal (x : X.Fn) y = ψ x := by
  have h (x : ((ratOf X).O (under y)).toSubring) : ratVal (x : X.Fn) y = (ratOf X).val y.1 x := by
    obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 x.2).exists_fnOf
    rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
    refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
    rintro _ ⟨w, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]
  exact ⟨GlobalTheory.ZH.RatModel.valHom (M := ratOf X) y.1 _
    (GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf X) y.1 (IsLocalRing.closedPoint ℂ)), fun x => (h x).trans rfl⟩

theorem cInfAt_ratVal {κ : Type} [Fintype κ] {f : κ → X.Fn} {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a))
    {G : (κ → ℂ) → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) : CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hy g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hy)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, Set.univ, hW, isOpen_univ, trivial, hG.contDiffOn, ?_⟩
  filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
  congr 1
  funext a
  rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]

end GlobalTheory.GoodMetric
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.Published


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.Published.generic_of_isIso_restrict {X X' : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] (π : X' ⟶ X) (U : X.Opens)
    (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)] :
    π (genericPoint X') = genericPoint X ∧ π.residueDegree (genericPoint X') = 1 := by
  have hrange : (U : Set X) ⊆ Set.range π := by
    intro y hy
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso ((π ∣_ U).base)).2 ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    have := congrArg Subtype.val hx
    simpa [morphismRestrict_base_coe] using this
  have hgen : π (genericPoint X') = genericPoint X := by
    have h1 := (genericPoint_spec X').image π.continuous
    have hdense : closure (Set.range π) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (U.isOpen.dense hU).closure_eq]
      exact closure_mono hrange
    rw [Set.image_univ, hdense] at h1
    exact h1.eq (genericPoint_spec X)
  refine ⟨hgen, ?_⟩
  have hmem : genericPoint X' ∈ π ⁻¹ᵁ U := by
    show π (genericPoint X') ∈ U
    rw [hgen]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  obtain ⟨x, hx⟩ : genericPoint X' ∈ Set.range (π ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]; exact hmem
  have h1 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ∣_ U) U.ι x
  have h2 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ⁻¹ᵁ U).ι π x
  rw [morphismRestrict_ι, h2, _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ⁻¹ᵁ U).ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion U.ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ∣_ U), hx] at h1
  simpa using h1


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.Published.arBirational_of_arProj (H : _root_.GlobalTheory.Published.ArProj) :
    _root_.GlobalTheory.Published.ArBirational := by
  intro k _ X X' _ _ p p' D hp hp' _ _ π hπ U hU hiso L a hL
  obtain ⟨hgen, hdeg⟩ := _root_.GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have := (H k X X' p p' D hp hp' π hπ hgen (by rw [hdeg]; exact one_ne_zero)).1 L a hL
  simpa [hdeg] using this

end GlobalTheory.Published
end
end

