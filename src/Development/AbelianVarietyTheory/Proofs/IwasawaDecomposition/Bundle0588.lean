module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrame
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

namespace GlobalTheory.ShFam.StalkSpread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_isMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (X.X.presheaf.germ W z hz).hom fz := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ X j z φz fz W₀ hz₀ hstr
  obtain ⟨U₀, hU₀, φ₀, f₀, hy₀, hs₀, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (j z)
  let gm₀ : Γ(gen Z, U₀) →+* X.X.presheaf.stalk z :=
    (X.X.presheaf.germ (j ⁻¹ᵁ U₀) z hy₀).hom.comp (j.app U₀).hom
  have hgm : ∀ (U : X.X.Opens) (hy : z ∈ U) (h : U ≤ j ⁻¹ᵁ U₀),
      (X.X.presheaf.germ U z hy).hom.comp (j.appLE U₀ U h).hom = gm₀ := fun U hy h =>
    RingHom.ext fun a => X.X.presheaf.germ_res_apply (homOfLE h) z hy _
  have hρ : ∀ (U : X.X.Opens) (hU : IsAffineOpen U) (h : U ≤ j ⁻¹ᵁ U₀),
      spMap (j.appLE U₀ U h).hom ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) =
        (show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j := fun U hU h =>
    IsAffineOpen.SpecMap_appLE_fromSpec j hU₀ hU h
  have hx₀ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) = stalkPt X z ≫ j := by
    obtain ⟨U, hU, hy, h⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := j ⁻¹ᵁ U₀) (x := z) hy₀
    rw [← hgm U hy h, ← spMap_comp_spMap, Category.assoc, hρ U hU h, ← Category.assoc, Spread.spMap_germ]
    rfl
  have hs₀' : (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genStr Z = spMap φ₀ := hs₀
  have hφ₀ : gm₀.comp φ₀ = φz := by
    have h1 : spMap (gm₀.comp φ₀) = spMap φz := by
      rw [← spMap_comp_spMap, ← hs₀', ← Category.assoc, hx₀, Category.assoc, hstr]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hx₁ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by rw [← Category.assoc, hx₀, Category.assoc]
  obtain ⟨g, hg⟩ := Spread.exists_bc f₀ gm₀ hφ₀ hx₁
  choose A B hAB hA using Spread.exists_coord g fz
  obtain ⟨U, hU, hy, s, hle, hs⟩ := Spread.exists_affine_germs z (W := W₀ ⊓ j ⁻¹ᵁ U₀) ⟨hz₀, hy₀⟩
    (fun p : Bool × (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) =>
      (cond p.1 (A p.2.1) (B p.2.1)) p.2.2.1 p.2.2.2)
  have h₀ : U ≤ j ⁻¹ᵁ U₀ := fun w hw => (hle hw).2
  let gm : Γ(X.X, U) →+* X.X.presheaf.stalk z := (X.X.presheaf.germ U z hy).hom
  let ρ : Γ(gen Z, U₀) →+* Γ(X.X, U) := (j.appLE U₀ U h₀).hom
  let A' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (true, ⟨τ, i, k⟩)
  let B' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (false, ⟨τ, i, k⟩)
  have hA' : ∀ τ i k, gm (A' τ i k) = A τ i k := fun τ i k => hs (true, ⟨τ, i, k⟩)
  have hB' : ∀ τ i k, gm (B' τ i k) = B τ i k := fun τ i k => hs (false, ⟨τ, i, k⟩)
  have hAB' : ∀ τ, B' τ * A' τ = 1 := fun τ => Matrix.ext fun i k => germ_injective_of_isIntegral X.X z hy (by
    show gm _ = gm _
    have := congrFun (congrFun (hAB τ) i) k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, hA', hB', Matrix.one_apply] at this ⊢
    rw [this]
    split_ifs <;> simp)
  have hx₂ : spMap ρ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z := by rw [← Category.assoc, hρ U hU h₀]
  have hx₃ : spMap gm ≫ ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, Spread.spMap_germ]
    rfl
  obtain ⟨g', hg'⟩ := Spread.exists_bc f₀ ρ rfl hx₂
  obtain ⟨fr, hfr⟩ := Spread.exists_change g' A' B' hAB'
  refine ⟨U, hU, ρ.comp φ₀, fr, hy, fun w hw => (hle hw).1, ?_, fun τ i => ?_⟩
  · rw [← hρ U hU h₀, Category.assoc, hs₀']
    exact spMap_comp_spMap φ₀ ρ
  · have hv : fz.vec τ i = res gm hx₃ (fr.vec τ i) := by
      rw [hfr, res_sum, hA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hA', hg, hg', res_res ρ hx₂ gm hx₃ (hgm U hy h₀) hx₁]
    exact congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) hv

end GlobalTheory.ShFam.StalkSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointLiftValuationRing
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCptLift

theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] [Algebra V L] [IsFractionRing V L] (yV : Sp V ⟶ gen Z) (pL : Sp L ⟶ C.Y.X), pL ≫ C.π = spMap (algebraMap V L) ≫ yV → ∃ q : Sp V ⟶ C.Y.X, q ≫ C.π = yV ∧ spMap (algebraMap V L) ≫ q = pL := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ _ L _ _ _ yV pL h
  have : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsSeparated (genStr Z ≫ spMap e.toRingHom) := inferInstance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  have hv : ValuativeCriterion.Existence C.π := by
    have h' : UniversallyClosed C.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h'
    exact h'.1
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨V, L, pL, yV, ⟨h⟩⟩).exists_lift
  exact ⟨q, q2, q1⟩

end GlobalTheory.FlagCptLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCptBase

theorem exists_geomPt (S : Scheme.{0}) (s : S) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (q : Sp K ⟶ S), s ∈ Set.range q := by
  let K := AlgebraicClosure (S.residueField s)
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  refine ⟨K, inferInstance, inferInstance, spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s, t, ?_⟩
  have h : S.fromSpecResidueField s (spMap (algebraMap (S.residueField s) K) t) ∈
      Set.range (S.fromSpecResidueField s) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at h
  rw [Scheme.Hom.comp_apply]
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

theorem isClosed_range_π (C : FlagCpt Z e) : IsClosed (Set.range C.π) := by
  have hZ : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have : IsSeparated (genStr Z ≫ spMap e.toRingHom) := inferInstance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  exact C.π.isClosedMap.isClosed_range

end GlobalTheory.FlagCptBase

namespace GlobalTheory.FlagCptBase

open CategoryTheory.Limits

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}

theorem exists_mem_range (Φ : FlagTor Z e U) (w : gen Z) : ∃ i, w ∈ Set.range (Φ.C i).π := by
  obtain ⟨K, _, _, q, t, hq⟩ := exists_geomPt _ w
  let χ : c.F →+* K := (Spec.preimage (q ≫ genStr Z)).hom
  have hχ : q ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ q hχ
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ q hχ g
  refine ⟨i, p t, ?_⟩
  rw [← hq, ← Scheme.Hom.comp_apply]
  exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp

theorem eq_of_apply_eq (Φ : FlagTor Z e U)
    (hA : ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z),
      x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x →
      (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g')
    (hB : ∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X),
      p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g)
    {i i' : U.Comp} (y : (Φ.C i).Y.X) (y' : (Φ.C i').Y.X) (h : (Φ.C i).π y = (Φ.C i').π y') : i = i' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Φ.C i).π) (g := (Φ.C i').π) y y' h
  obtain ⟨K, _, _, q, -⟩ := exists_geomPt _ z
  let p := q ≫ pullback.fst (Φ.C i).π (Φ.C i').π
  let p' := q ≫ pullback.snd (Φ.C i).π (Φ.C i').π
  let w := p ≫ (Φ.C i).π
  have hw' : p' ≫ (Φ.C i').π = w := by
    simp only [p, p', w, Category.assoc, pullback.condition]
  let χ : c.F →+* K := (Spec.preimage (w ≫ genStr Z)).hom
  have hχ : w ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  have hB' : ∀ (i : U.Comp) (p : Sp K ⟶ (Φ.C i).Y.X) (x : Sp K ⟶ gen Z), p ≫ (Φ.C i).π = x →
      x ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (x ≫ genι Z), (Φ.C i).Carries p g := by
    intro i p x hx hxχ
    subst hx
    rw [Category.assoc] at hxχ ⊢
    exact hB i K χ p hxχ
  obtain ⟨g, hg⟩ := hB' i p w rfl hχ
  obtain ⟨g', hg'⟩ := hB' i' p' w hw' hχ
  obtain ⟨p'', hp'', hc''⟩ := hA i K χ w hχ g g' p rfl hg
  obtain ⟨_, -, huniq⟩ := Φ.lifts K χ w hχ g'
  have h1 := huniq ⟨i, p''⟩ ⟨hp'', hc''⟩
  have h2 := huniq ⟨i', p'⟩ ⟨hw', hg'⟩
  exact congrArg Sigma.fst (h1.trans h2.symm)

end GlobalTheory.FlagCptBase

theorem GlobalTheory.FlagCptBase.exists_pt_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → (∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g') → (∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∃ p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj _ f hf hA hB K _ _ χ x hx
  let W : U.Comp → Set X.X := fun i => j ⁻¹' Set.range (Φ.C i).π
  have hcl : ∀ i, IsClosed (W i) := fun i => (GlobalTheory.FlagCptBase.isClosed_range_π (Φ.C i)).preimage j.continuous
  have hdis : ∀ i i' z, z ∈ W i → z ∈ W i' → i = i' := by
    rintro i i' z ⟨y, hy⟩ ⟨y', hy'⟩
    exact GlobalTheory.FlagCptBase.eq_of_apply_eq Φ hA hB y y' (hy.trans hy'.symm)
  have hcov : ∀ z, ∃ i, z ∈ W i := fun z => GlobalTheory.FlagCptBase.exists_mem_range Φ (j z)
  have hWk : W k = Set.univ := by
    have hc : (W k)ᶜ = ⋃ i ∈ ({k}ᶜ : Set U.Comp), W i := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := hcov z
        exact ⟨i, fun h => hz (h ▸ hi), hi⟩
      · rintro ⟨i, hik, hi⟩ hz
        exact hik (hdis i k z hi hz)
    have hopen : IsOpen (W k) := by
      rw [← isClosed_compl_iff, hc]
      exact Set.Finite.isClosed_biUnion (Set.toFinite _) (fun i _ => hcl i)
    obtain ⟨y⟩ : Nonempty (Φ.C k).Y.X := inferInstance
    have hne : (W k).Nonempty := ⟨f y, y, by rw [← hf, Scheme.Hom.comp_apply]⟩
    exact IsClopen.eq_univ ⟨hcl k, hopen⟩ hne
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx'
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ (x ≫ j) hx' g
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  have hi : i = k := by
    have h1 : x t ∈ W i := ⟨p t, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp⟩
    have h2 : x t ∈ W k := hWk ▸ Set.mem_univ _
    exact hdis _ _ _ h1 h2
  subst hi
  refine ⟨p, ?_⟩
  rw [← cancel_mono j, Category.assoc, hf]
  exact hp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullFlagFamilyLieCompatibleGraded
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlagTie

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

def Lower (g : Mat m K) : Prop := ∀ τ (i k : Fin (m τ)), i < k → g τ i k = 0

theorem lower_iff_blockTriangular (g : Mat m K) (τ : ι) :
    (∀ i k : Fin (m τ), i < k → g τ i k = 0) ↔ (g τ).BlockTriangular OrderDual.toDual :=
  ⟨fun h _ _ hik => h _ _ hik, fun h _ _ hik => h hik⟩

theorem Lower.mul {g h : Mat m K} (hg : Lower g) (hh : Lower h) : Lower (g * h) := fun τ =>
  (lower_iff_blockTriangular (g * h) τ).2
    (((lower_iff_blockTriangular g τ).1 (hg τ)).mul ((lower_iff_blockTriangular h τ).1 (hh τ)))

theorem Lower.inv {g : Mat m K} (hg : Lower g) : Lower g⁻¹ := fun τ => by
  by_cases hd : (g τ).det = 0
  · intro i k _
    show (g τ)⁻¹ i k = 0
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hd])]
    rfl
  · have := (g τ).invertibleOfIsUnitDet (Ne.isUnit hd)
    exact (lower_iff_blockTriangular g⁻¹ τ).2
      (Matrix.blockTriangular_inv_of_blockTriangular ((lower_iff_blockTriangular g τ).1 (hg τ)))

theorem Lower.det_eq {g : Mat m K} (hg : Lower g) (τ : ι) : (g τ).det = ∏ i, g τ i i :=
  Matrix.det_of_lowerTriangular _ ((lower_iff_blockTriangular g τ).1 (hg τ))

theorem lower_one : Lower (1 : Mat m K) := fun _ _ _ hik => Matrix.one_apply_ne hik.ne

theorem par_full_iff {O : Subring K} {g : Mat m K} : Par m O g ↔ Par 0 O g ∧ Lower g := by
  constructor
  · intro h
    exact ⟨h.mono (fun _ => Nat.zero_le _) le_rfl, fun τ i k hik => (h τ).2.2.2 i k i.2 hik⟩
  · rintro ⟨h, hl⟩ τ
    exact ⟨(h τ).1, (h τ).2.1, (h τ).2.2.1, fun i k _ hik => hl τ i k hik⟩

theorem lower_mul_iff {B L : Mat m K} (hl : Lower L) (hL : ∀ τ, (L τ).det ≠ 0) : Lower (B * L) ↔ Lower B := by
  refine ⟨fun h => ?_, fun h => h.mul hl⟩
  have := h.mul hl.inv
  rwa [mul_assoc, Mat.mul_inv hL, mul_one] at this

end Tri

section Nhds

variable {F : Type} [Field F] {ι : Type} [Finite ι] {m : ι → ℕ}

theorem mem_O_generic (Y : Var F) (x : Y.Fn) : x ∈ ((ratOf Y).O (genericPoint Y.X)).toSubring :=
  (mem_O_ratOf (Y := Y) (y := genericPoint Y.X) (g := x)).2 ⟨x, by
    show (Y.X.presheaf.stalkSpecializes _).hom x = x
    rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl⟩

theorem eventually_mem_O {Y : Var F} {z : Y.X} {g : Y.Fn} (h : g ∈ ((ratOf Y).O z).toSubring) :
    ∀ᶠ z' in nhds z, g ∈ ((ratOf Y).O z').toSubring := by
  obtain ⟨U, hz, a, rfl⟩ := (mem_O_ratOf.1 h).exists_fnOf
  exact Filter.eventually_of_mem (U.isOpen.mem_nhds hz) fun z' hz' => mem_O_ratOf.2 (regAt_fnOf hz' _ a)

theorem eventually_par {Y : Var F} {z : Y.X} {g : Mat m Y.Fn} (h : Par 0 ((ratOf Y).O z).toSubring g) :
    ∀ᶠ z' in nhds z, Par 0 ((ratOf Y).O z').toSubring g := by
  have h1 : ∀ᶠ z' in nhds z, ∀ τ i j, g τ i j ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_mem_O ((h τ).1 i j)
  have h2 : ∀ᶠ z' in nhds z, ∀ τ, (g τ).det⁻¹ ∈ ((ratOf Y).O z').toSubring :=
    Filter.eventually_all.2 fun τ => eventually_mem_O (h τ).2.2.1
  filter_upwards [h1, h2] with z' h1 h2 τ
  exact ⟨h1 τ, (h τ).2.1, h2 τ, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩

end Nhds

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

abbrev base (C : FlagCpt Z e) : Fr (ratOf C.Y) Dw.mult 0 := TieBase.fam e C.Y C.π C.π_str C.f0

theorem exists_lower (C : FlagCpt Z e) (y : C.Y.X) :
    ∃ (L : Mat Dw.mult C.Y.Fn) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      L⁻¹ ∈ (base C).S y ∧ (∀ τ, (L τ).det ≠ 0) ∧ Lower L ∧ (∀ τ i, L τ i i = t τ i) ∧
        ∀ τ i, (C.gr τ i).IsEqn y (t τ i) := by
  obtain ⟨φ, f, t, htri, hgr⟩ := C.gr_spec y
  obtain ⟨L, hc, hd, hl⟩ := (EigFrame.tri_iff f _ C.f0 t).1 htri
  have hL : ∀ τ, (L τ).det ≠ 0 := fun τ => by
    rw [Lower.det_eq hl τ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [hd]; exact (t τ i).ne_zero
  refine ⟨L, t, ?_, hL, hl, hd, hgr⟩
  show (∀ τ, (L⁻¹ τ).det ≠ 0) ∧ _
  refine ⟨fun τ => (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hL) τ)).ne_zero, φ, f, ?_⟩
  rw [Mat.inv_inv hL]
  exact hc

theorem one_mem_base (C : FlagCpt Z e) : (1 : Mat Dw.mult C.Y.Fn) ∈ (base C).S (genericPoint C.Y.X) := by
  obtain ⟨A, hA⟩ := (base C).nonempty (genericPoint C.Y.X)
  refine (Fr.mem_iff hA).2 fun τ => ?_
  refine ⟨fun _ _ => mem_O_generic _ _, ?_, mem_O_generic _ _, fun i j hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [one_mul]
  exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul (Fr.det_ne hA)) τ)).ne_zero

def flagFam (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn) (hA₁ : ∀ τ, (A₁ τ).det ≠ 0) : Fr (ratOf C.Y) Dw.mult Dw.mult where
  S y := {A' | A' * A₁⁻¹ ∈ (base C).S y ∧ Lower (A' * A₁⁻¹)}
  loc z := by
    obtain ⟨L, -, hLS, hL, hl, -, -⟩ := exists_lower C z
    obtain ⟨U₀, T, hz, -, hU₀⟩ := (base C).loc z
    have hev : ∀ᶠ z' in nhds z, L⁻¹ ∈ (base C).S z' :=
      (Filter.eventually_and.2 ⟨Filter.eventually_of_mem (U₀.isOpen.mem_nhds hz) fun _ h => h,
        eventually_par ((hU₀ z hz L⁻¹).1 hLS)⟩).mono fun z' h => (hU₀ z' h.1 L⁻¹).2 h.2
    obtain ⟨W, hW, hWo, hzW⟩ := eventually_nhds_iff.1 hev
    refine ⟨⟨W, hWo⟩, L⁻¹ * A₁, hzW, fun τ => ?_, fun z' hz' A' => ?_⟩
    · rw [Pi.mul_apply, Matrix.det_mul]
      exact mul_ne_zero (Fr.det_ne hLS τ) (hA₁ τ)
    · have hz'' : L⁻¹ ∈ (base C).S z' := hW z' hz'
      show (A' * A₁⁻¹ ∈ (base C).S z' ∧ Lower (A' * A₁⁻¹)) ↔ _
      rw [Fr.mem_iff hz'', Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, par_full_iff, lower_mul_iff hl hL]

theorem exists_tied_isGraded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type)
    [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (A₁ : Mat Dw.mult C.Y.Fn), (∀ τ, (A₁ τ).det ≠ 0) →
    ∃ E' : Fr (ratOf C.Y) Dw.mult Dw.mult, Tied e C.Y C.π C.f0 E' A₁ ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C A₁ hA₁
  have hA : A₁ ∈ (flagFam C A₁ hA₁).S (genericPoint C.Y.X) := by
    show A₁ * A₁⁻¹ ∈ (base C).S _ ∧ Lower (A₁ * A₁⁻¹)
    rw [Mat.mul_inv hA₁]
    exact ⟨one_mem_base C, lower_one⟩
  refine ⟨flagFam C A₁ hA₁, ⟨hA, fun y A h => ?_⟩, ⟨A₁, hA, fun y x => ?_⟩⟩
  · obtain ⟨-, φ, f, hf⟩ := h.1
    rw [Mat.mul_inv_rev, Mat.inv_inv hA₁] at hf
    exact ⟨φ, f, hf⟩
  · obtain ⟨L, t, hLS, hL, hl, hd, hgr⟩ := exists_lower C y
    refine ⟨L⁻¹ * A₁, ?_, t x.1 x.2, ?_, hgr x.1 x.2⟩
    · show L⁻¹ * A₁ * A₁⁻¹ ∈ (base C).S y ∧ Lower (L⁻¹ * A₁ * A₁⁻¹)
      rw [mul_assoc, Mat.mul_inv hA₁, mul_one]
      exact ⟨hLS, hl.inv⟩
    · rw [Mat.mul_inv_rev, Mat.inv_inv hL, ← mul_assoc, Mat.mul_inv hA₁, one_mul]
      exact hd _ _

end Main

end GlobalTheory.ShFam.FlagTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), EntC q.x.ker → ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t ∧ GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O t ∧ GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z t := by
  intro 𝒮 K q hE
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
  simp only [ofObj, extraObj] at ker_eq
  cases ker_eq
  obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
    ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
      nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
    kT.unf kT.ok kT.served
  obtain ⟨t, s, r, p, o, e⟩ := GlobalTheory.Core.DefKer.stdRd_keep w.I w.ok w.l Z t1 ((StdModel.stdKer_iff w.I w.l Z t1).2 s1)
  have ha : t.Adapted := by
    unfold Formalism.L2.Ker.KerEntTied.Adapted at a1 ⊢
    rw [o, e]
    exact a1
  have hc : GlobalTheory.Pdv.IsEntC t := by
    unfold GlobalTheory.Pdv.IsEntC
    rw [o, e, o1, e1]
    exact hE
  exact ⟨t, ⟨s, o.trans o1, heq_of_eq (e.trans e1), ha, p⟩, ⟨w.ok, w.pins, pin.isTw, pin.jets, rfl, s, hc, ha, p⟩, r⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecTensorToPullbackSectionsCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specTensor_to_pullback_sections_compat : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens) (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), letI := (ρ.appLE U W hW).hom.toAlgebra; letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra; ∃ (κ : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ pullback ξ ρ) (hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens)), (∀ c : Γ(Y', W), (Scheme.ΓSpecIso _).hom.hom (((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom c) = c ⊗ₜ[Γ(X, U)] (1 : R)) ∧ ∀ r : R, (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] r := by
  first | exact @GlobalTheory.specTensor_to_pullback | exact GlobalTheory.specTensor_to_pullback | (intros; apply GlobalTheory.specTensor_to_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem toReal_mem_psdCone_of_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X), β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := H.bar) (X := X) := by
  intro E _ _ _ H X _ _ _ _ β hβ hp
  have h := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 (fun _ => β) (fun _ => 1)
    (fun _ => hβ) (fun _ y => hp y) (fun _ => zero_le_one)
  simpa using h

end GlobalTheory.PolFan
end

