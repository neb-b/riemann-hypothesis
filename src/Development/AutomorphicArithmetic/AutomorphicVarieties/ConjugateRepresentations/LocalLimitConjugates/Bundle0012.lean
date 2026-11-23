module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HarmFin
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : W →ₗ[ℂ] W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp

private noncomputable def coords {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} (e : Fin n → Herm E a) : Co Ξ q →ₗ[ℂ] ((Fin q → Fin n) × Fin Ξ.d → Sm E a) where
  toFun ω p := cmp p.2 (ω fun j => e (p.1 j))
  map_add' α β := funext fun p => map_add (Bor.cmp p.2) _ _
  map_smul' c α := funext fun p => map_smul (Bor.cmp p.2) c _

private theorem coords_inj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) : Function.Injective (coords Ξ q e) := by
  intro α β h
  have hs : Submodule.span ℝ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 fun X _ => ?_
    rw [he X]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply AlternatingMap.coe_multilinearMap_injective
  refine MultilinearMap.ext_of_span_eq_top (g := fun _ => e) (fun _ => hs) fun I => ?_
  change α (fun j => e (I j)) = β (fun j => e (I j))
  rw [← sum_cmp (α _), ← sum_cmp (β _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun h (I, i)
  exact congrArg (· ⊗ₜ[ℂ] _) this

theorem UpperTheory.V.Cj.H.harmFin :
    UpperTheory.V.Cj.H.HarmFin := by
  intro E _ _ _ a Ξ r m q U hU
  obtain ⟨n, e, he⟩ := frameEx E a
  obtain ⟨W, _, _, _, ρ, hρ, hk⟩ := kType E a Ξ q
  have hF := formsFiniteGL E a U hU W ρ hρ fun t u => ((m t).map (u + ·)).prod
  set F := Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms U ρ fun t u => ((m t).map (u + ·)).prod) with hFd
  have hle : ∀ ω ∈ Submodule.span ℂ {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω}, ∀ p, coords Ξ q e ω p ∈ F := by
    intro ω hω p
    induction hω using Submodule.span_induction with
    | zero => rw [map_zero]; exact F.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact F.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact F.smul_mem c hx
    | mem ω hω =>
      obtain ⟨h, hu⟩ := hω
      obtain ⟨U', -, -, hl⟩ := h.lev
      refine Submodule.subset_span ⟨(h.aut _ _).1, fun k hk' => ?_, fun g => ?_, (h.aut _ _).2⟩
      · have h1 := congrArg (fun η : Co Ξ q => cmp p.2 (η fun j => e (p.1 j))) (hu k hk')
        exact (cmp_rT _ _ _).symm.trans h1
      · obtain ⟨T, w, hT, hw⟩ := hk ω hl.equiv (fun j => e (p.1 j)) p.2
        have := GlobalTheory.Published.AutFinGL.type_of_map ρ T hT w g
        rw [hw] at this
        exact this
  refine FiniteDimensional.of_injective (V₂ := (Fin q → Fin n) × Fin Ξ.d → F)
    (LinearMap.pi fun p => ((LinearMap.proj p ∘ₗ coords Ξ q e) ∘ₗ Submodule.subtype _).codRestrict F fun ω => hle ω.1 ω.2 p)
    fun α β h => Subtype.ext (coords_inj Ξ q he (funext fun p => ?_))
  exact congrArg Subtype.val (congrFun h p)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpComm
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opComm :
    UpperTheory.V.Cj.H.OpComm := by
  intro E _ _ _ a ha μ _ _ T hT T' hL
  obtain ⟨c1, c2, c3, -⟩ := clFacts E a μ
  have gf := gardFacts E a ha μ
  refine ⟨fun φ h => (hL φ h).1, fun X φ hφ => ?_, fun g φ hφ => ?_⟩
  · induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨ψ, F, hψ, hφ⟩ := h
      have h1 := liftCv E a ha μ T hT T' hL ψ φ F hψ hφ
      have h2 := cvLie E a μ ψ _ hψ _ h1 X
      have h3 := cvLie E a μ ψ φ hψ F hφ X
      have h4 := liftCv E a ha μ T hT T' hL _ _ F (((testOps E a ψ).2 hψ).1 X) h3
      exact Subtype.ext (h2.trans h4.symm)
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul s x _ hx => simp only [map_smul, hx]
  · have m1 : rt E a g (T' φ) ∈ gard μ := (gf _ (hL φ hφ).1).2.2.2.2 g
    have m0 : rt E a g φ ∈ gard μ := (gf _ hφ).2.2.2.2 g
    have m2 : T' (rt E a g φ) ∈ gard μ := (hL _ m0).1
    have m3 : (1 : ℂ) • rt E a g (T' φ) + (-1 : ℂ) • T' (rt E a g φ) ∈ gard μ :=
      add_mem (Submodule.smul_mem _ _ m1) (Submodule.smul_mem _ _ m2)
    have e := (c1 _ _ 1 (-1) (gf _ m1).2.1 (gf _ m2).2.1).2
    rw [c3 _ g (gf _ (hL φ hφ).1).2.1, (hL φ hφ).2, (hL _ m0).2, c3 _ g (gf _ hφ).2.1, hT,
      ← add_smul, add_neg_cancel, zero_smul] at e
    have z := c2 _ (gf _ m3).1 (gf _ m3).2.1 e
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at z
    exact z
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opLim :
    UpperTheory.V.Cj.H.OpLim := by
  intro E _ _ _ a ha μ _ _ T P hT hP hlim T' P' hT' hP' φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, hF⟩ := h
    intro C hC
    have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
    obtain ⟨-, hlin, -, hb⟩ := cvAlg (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1
    obtain ⟨B, hB⟩ := hb C hC
    have h1 : ∀ k, (T' k φ).1 = cv ψ.1 (T k F) := fun k =>
      liftCv E a ha μ (T k) (hT k) (T' k) (hT' k) ψ φ F hψ hF
    have h2 : (P' φ).1 = cv ψ.1 (P F) := liftCv E a ha μ P hP P' hP' ψ φ F hψ hF
    have h3 : Tendsto (fun k => B * ‖P F - T k F‖) atTop (𝓝 0) := by
      have h4 : Tendsto (fun k => P F - T k F) atTop (𝓝 (P F - P F)) := tendsto_const_nhds.sub (hlim F)
      have h5 := h4.norm.const_mul B
      simpa using h5
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [h3.eventually (gt_mem_nhds hε)] with k hk x hx
    rw [h1, h2, dist_eq_norm]
    have h6 := congrFun (hlin (P F) (T k F) 1 (-1)) x
    have h7 : (1 : ℂ) • P F + (-1 : ℂ) • T k F = P F - T k F := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [h7] at h6
    have h8 : cv ψ.1 (P F) x - cv ψ.1 (T k F) x = cv ψ.1 (P F - T k F) x := by
      rw [h6]; simp [sub_eq_add_neg]
    rw [h8]
    exact (hB _ x hx).trans_lt hk
  | zero =>
    intro C _
    simp only [map_zero]
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun k x _ => by simpa using hε
  | add φ ψ _ _ h1 h2 =>
    intro C hC
    simp only [map_add (f := _)]
    exact (h1 C hC).add (h2 C hC)
  | smul c φ _ h =>
    intro C hC
    simp only [map_smul]
    exact (uniformContinuous_const_smul c).comp_tendstoUniformlyOn (h C hC)
end

