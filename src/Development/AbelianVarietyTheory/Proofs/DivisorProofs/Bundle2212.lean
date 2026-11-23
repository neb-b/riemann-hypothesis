module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictFiniteAffineCoverInfClosedPull2Bijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCohCover

theorem adj_pull2_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C') (adj : G ⊣ H) :
    Function.Bijective (CoefMap.restrict F G).pull2 := by
  have hl : ∀ c, (GlobalTheory.AdjHyp.counitCoef F adj).pull2 ((CoefMap.restrict F G).pull2 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyTwo_comp]
    exact (CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (CoefMap.pullCohomologyTwo_id c)
  have hr : ∀ c, (CoefMap.restrict F G).pull2 ((GlobalTheory.AdjHyp.counitCoef F adj).pull2 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyTwo_comp]
    refine ((CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((GlobalTheory.AdjHyp.counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (CoefMap.pullCohomologyTwo_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

theorem restrict_cover_pull2_bijective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {J : Type}
    (U : J → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op).pull2 := by
  set G := (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  have hv2 := _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.pull2_restrict_injective_of_comma _ _ hs hg hv, _root_.GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma _ _ hs hg hv hv2⟩

theorem restrict_pull2_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull2 := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (CoefMap.restrict (OAff s) incl).pull2 :=
    restrict_cover_pull2_bijective s (fun i => (U i).1) hcov
  have b2 := adj_pull2_bijective (incl ⋙ OAff s) gc.monotone_u.functor.op gc.monotone_l.functor.op
    gc.adjunction.op
  have e : ∀ c, (CoefMap.restrict (OAff s) hU.functor.op).pull2 c =
      (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op).pull2
        ((CoefMap.restrict (OAff s) incl).pull2 c) := fun c =>
    (CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (CoefMap.pullCohomologyTwo_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.AbCohCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull1Bijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BasisO

theorem restrict_bijective_one : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (C' : Type)
    [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X),
    (∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U) →
    (∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
      ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) →
    Function.Bijective (CoefMap.restrict (OAff s) G).pull1 := by
  intro R _ X s C' _ _ G h1 h2
  have H := hasLoc_OAff s
  have hcov := BasisExt.hcov_of_basis s G h1
  have hdir := BasisExt.hdir_of_basis s G h2
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

end GlobalTheory.Obs.BasisO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull2Bijective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem restrict_pull2_bijective_of_basis (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X)
    (h1 : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U)
    (h2 : ∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 →
      x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
        x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) :
    Function.Bijective (CoefMap.restrict (OAff s) G).pull2 := by
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let B : Set Γ(X, T.unop.1) :=
      {f | ∃ t : C', X.basicOpen f ≤ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ T.unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t, hxt, htT⟩ := h1 x T.unop.1 hx
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := (G.obj t).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨t, hf, htT⟩⟩, hxf⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, T.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S u hu
      obtain ⟨t, hft, htT⟩ := hFB (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op f) at hu
      have hSf : S.unop.1 ≤ X.basicOpen f := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      refine ⟨t, (homOfLE (show (G.obj t).unop ≤ T.unop from htT)).op,
        (homOfLE (show S.unop ≤ (G.obj t).unop from hSf.trans hft)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : C') (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS : IsAffineOpen S.unop.1 := S.unop.2
    have hS₁ : S.unop.1 ≤ (G.obj t₁).unop.1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G.obj t₂).unop.1 := leOfHom a₂.unop
    let B : Set Γ(X, S.unop.1) :=
      {g | ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ X.basicOpen g ≤ (G.obj t₃).unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hS.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t₃, e₁, e₂, hxt, -⟩ := h2 t₁ t₂ x S.unop.1 hx (hS₁ hx) (hS₂ hx)
      obtain ⟨g, hg, hxg⟩ := hS.exists_basicOpen_le (V := (G.obj t₃).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ⟨t₃, e₁, e₂, hg⟩⟩, hxg⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, S.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S' u hu
      obtain ⟨t₃, e₁, e₂, hgt⟩ := hFB (F.equivFin.symm i).2
      set g : Γ(X, S.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
      have hS'g : S'.unop.1 ≤ X.basicOpen g := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      exact ⟨t₃, e₁, e₂, ⟨(homOfLE (show S'.unop ≤ (G.obj t₃).unop from hS'g.trans hgt)).op⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  have hv2 := _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.pull2_restrict_injective_of_comma _ _ hs hg hv, _root_.GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma _ _ hs hg hv hv2⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictUpwardClosedSubcategoryPull1Bijective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem restrict_upwardClosed_subcategory_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : ObjectProperty C), (∀ S S', (S ⟶ S') → P S → P S') →
    (∀ T, Desc.Sep F fun S (_ : T ⟶ S) ↦ P S) → (∀ T, Desc.Glue F fun S (_ : T ⟶ S) ↦ P S) →
    (∀ T, Desc.Van1 F fun S (_ : T ⟶ S) ↦ P S) → Function.Bijective (CoefMap.restrict F P.ι).pull1 := by
  intro R _ C _ F P hP sep glue van
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g₀, hg⟩ := hc
    let g : ∀ S, P S → F.obj S := fun S hS ↦ g₀ ⟨S, hS⟩
    have hg' : ∀ (S S' : C) (hS : P S) (hS' : P S') (ψ : S ⟶ S'),
        g S' hS' - mp F ψ (g S hS) = f.1 S S' ψ := fun S S' hS hS' ψ ↦
      congrFun (congrFun (congrFun hg ⟨S, hS⟩) ⟨S', hS'⟩) (ObjectProperty.homMk ψ)
    have h1 : ∀ T : C, ∃ x : F.obj T, ∀ S (u : T ⟶ S) (hS : P S),
        mp F u x = g S hS - f.1 T S u := by
      intro T
      obtain ⟨x, hx⟩ := glue T (fun S u ↦ if hS : P S then g S hS - f.1 T S u else 0)
        fun S S' u ψ hS ↦ by
          have hS' := hP _ _ ψ hS
          simp only [dif_pos hS, dif_pos hS', map_sub]
          have k1 := Z1.comp f u ψ
          have k2 := hg' S S' hS hS' ψ
          linear_combination k2 - k1
      exact ⟨x, fun S u hS ↦ by rw [hx S u hS, dif_pos hS]⟩
    choose x hx using h1
    refine H1.mk_eq_zero.2 ⟨x, ?_⟩
    funext T T' φ
    rw [amitsur_d0_apply]
    refine (sub_eq_zero.1 (sep T' _ fun S u hS ↦ ?_)).symm
    have k1 := Z1.comp f φ u
    have k2 := hx T' S u hS
    have k3 := hx T S (φ ≫ u) hS
    rw [mp_comp] at k3
    simp only [map_sub]
    linear_combination k3 - k2 - k1
  · intro c
    obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
    let z : ∀ S S', (S ⟶ S') → F.obj S' := fun S S' ψ ↦
      if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0
    have hz : ∀ S S' S'' (ψ : S ⟶ S') (χ : S' ⟶ S''), P S →
        z S S'' (ψ ≫ χ) = mp F χ (z S S' ψ) + z S' S'' χ := by
      intro S S' S'' ψ χ hp
      have hp' := hP _ _ ψ hp
      simp only [z, dif_pos hp, dif_pos hp']
      exact y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hp'⟩) (T'' := ⟨S'', hP _ _ χ hp'⟩)
        (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ)
    have hzy : ∀ (S S' : P.FullSubcategory) (ψ : S ⟶ S'), z S.obj S'.obj ψ.hom = y.1 S S' ψ := by
      intro S S' ψ
      simp only [z, dif_pos S.property]
      rfl
    have h1 : ∀ T : C, ∃ b : ∀ S, (T ⟶ S) → F.obj S, (∀ S S' u ψ, P S →
        b S' (u ≫ ψ) - mp F ψ (b S u) = z S S' ψ) ∧ (P T → ∀ S u, b S u = z T S u) := by
      intro T
      by_cases hp : P T
      · exact ⟨fun S u ↦ z T S u, fun S S' u ψ _ ↦ by
          have := hz _ _ _ u ψ hp
          linear_combination this, fun _ _ _ ↦ rfl⟩
      · obtain ⟨b, hb⟩ := van T (fun S S' _ ψ ↦ z S S' ψ) fun S S' S'' u ψ χ h ↦ hz _ _ _ ψ χ h
        exact ⟨b, hb, fun h ↦ absurd h hp⟩
    choose b hb hb' using h1
    have h2 : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ S (u : T' ⟶ S), P S →
        mp F u x = b T S (φ ≫ u) - b T' S u := by
      intro T T' φ
      refine glue T' _ fun S S' u ψ hp ↦ ?_
      have k1 := hb T _ _ (φ ≫ u) ψ hp
      have k2 := hb T' _ _ u ψ hp
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k1 - k2
    choose f hf using h2
    refine ⟨H1.mk F ⟨f, fun T T' T'' φ ψ ↦ sub_eq_zero.1 (sep T'' _ fun S u hp ↦ ?_)⟩, ?_⟩
    · have k1 := hf _ _ (φ ≫ ψ) S u hp
      have k2 := hf _ _ φ S (ψ ≫ u) hp
      have k3 := hf _ _ ψ S u hp
      simp only [map_sub, map_add (f := _), mp_comp, Category.assoc] at k1 k2 ⊢
      linear_combination k1 - k2 - k3
    · rw [CoefMap.pullCohomologyOne_class]
      congr 1
      refine Subtype.ext ?_
      funext S S' ψ
      have k1 := hf _ _ ψ.hom _ (𝟙 _) S'.property
      rw [hb' _ S.property, hb' _ S'.property, mp_id, Category.comp_id] at k1
      have k2 := hz _ _ _ (𝟙 S'.obj) (𝟙 S'.obj) S'.property
      rw [Category.id_comp, mp_id] at k2
      rw [← hzy]
      change f _ _ ψ.hom = _
      linear_combination k1 + k2

end GlobalTheory.CatCoh.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCoeffSpanSetSectionsFlatBaseChangeNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem height_comap_eq_one_of_flat_of_mem {R R₁ : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing R₁] [IsNoetherianRing R₁] (ρ : R →+* R₁) (hρ : ρ.Flat) {f : R} (hf : f ≠ 0)
    (q : Ideal R₁) [q.IsPrime] (hq : q.height = 1) (hfq : ρ f ∈ q) : (q.comap ρ).height = 1 := by
  letI := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  haveI : Algebra.HasGoingDown R R₁ := Algebra.HasGoingDown.of_flat
  haveI : (q.comap ρ).IsPrime := Ideal.comap_isPrime ρ q
  haveI : q.LiesOver (q.comap ρ) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.comap ρ) q
  have hle : (q.comap ρ).height ≤ 1 := by rw [← hq, h]; exact le_self_add
  refine le_antisymm hle ?_
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  intro hb
  have : f ∈ q.comap ρ := hfq
  rw [hb, Ideal.mem_bot] at this
  exact hf this

end GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem spanBy_mono {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {T T' : Set F₁}
    (h : T ⊆ T') : spanBy c T ⊆ spanBy c T' := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact ⟨n, r, t, fun i => h (ht i), rfl⟩

theorem spanBy_sections_eq_of_flat : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (V₀ : Set F), (0 : F) ∈ V₀ → (∀ a ∈ V₀, ∀ b ∈ V₀, a + b ∈ V₀) → (∀ r, ∀ a ∈ V₀, c₀ r * a ∈ V₀) → (∀ a ∈ V₀, (c₀ f)⁻¹ * a ∈ V₀) → ∀ (W : Ideal R → Set F) (W₁ : Ideal R₁ → Set F₁), (∀ p : Ideal R, p.IsPrime → f ∈ p → ∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W p) → (∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → (∀ a ∈ W p, ∀ b ∈ W p, a + b ∈ W p) ∧ (∀ r, ∀ a ∈ W p, c₀ r * a ∈ W p) ∧ (∀ s, s ∉ p → ∀ a ∈ W p, (c₀ s)⁻¹ * a ∈ W p)) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → GaussAt c₁ q θ (W (q.comap ρ)) (W₁ q)) → spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p}) = spanBy c₁ (θ '' V₀) ∩ {v | ∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → v ∈ W₁ q} := by
  intro R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin V₀ hV0 hVadd hVsmul _ W W₁
    htor hWcl hgauss
  have hW0 : ∀ p : Ideal R, p.IsPrime → f ∈ p → (0 : F) ∈ W p := fun p hp hfp => by
    obtain ⟨m, hm⟩ := htor p hp hfp 0
    simpa using hm
  set P := {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal} with hPdef
  have hP : P.Finite := GlobalTheory.finite_height_eq_one_mem hf

  have key : ∀ S : Finset (PrimeSpectrum R), (∀ p ∈ S, p ∈ P) →
      spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal}) =
        spanBy c₁ (θ '' V₀) ∩ {x | ∀ p ∈ S, x ∈ spanBy c₁ (θ '' W p.asIdeal)} := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => intro _; ext x; simp
    | insert a S ha ih =>
      intro hS
      have haP := hS a (Finset.mem_insert_self a S)
      obtain ⟨hadd, hsmul, -⟩ := hWcl a.asIdeal a.2 haP.1 haP.2
      have hSP : ∀ p ∈ S, p ∈ P := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have e : {u | u ∈ V₀ ∧ ∀ p ∈ insert a S, u ∈ W p.asIdeal} =
          {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} ∩ W a.asIdeal := by
        ext u; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
          forall_eq_or_imp]; tauto
      rw [e, _root_.GlobalTheory.Desc.spanBy_image_inter R R₁ F F₁ ρ c₀ c₁ θ hρ hc₀ hcomm hlin {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} (W a.asIdeal)
        ⟨hV0, fun p hp => hW0 p.asIdeal p.2 (hSP p hp).2⟩
        (fun a' ha' b hb => ⟨hVadd a' ha'.1 b hb.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).1 a' (ha'.2 p hp) b (hb.2 p hp)⟩)
        (fun r a' ha' => ⟨hVsmul r a' ha'.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).2.1 r a' (ha'.2 p hp)⟩)
        (hW0 a.asIdeal a.2 haP.2) hadd hsmul, ih hSP]
      ext x; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
        forall_eq_or_imp]; tauto
  have hS := key hP.toFinset (fun p hp => hP.mem_toFinset.mp hp)
  have e1 : {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p} =
      {u | u ∈ V₀ ∧ ∀ p ∈ hP.toFinset, u ∈ W p.asIdeal} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
    exact and_congr_right fun _ => ⟨fun h p hp => h p.asIdeal p.2 hp.1 hp.2,
      fun h p hp h1 hfp => h ⟨p, hp⟩ ⟨h1, hfp⟩⟩
  rw [e1, hS]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
  refine and_congr_right fun hx => ?_
  have hxr : x ∈ spanBy c₁ (Set.range θ) := spanBy_mono c₁ (Set.image_subset_range θ V₀) hx
  have hd : ∃ d : R₁, d ≠ 0 ∧ c₁ d * x ∈ spanBy c₁ (Set.range θ) := ⟨1, one_ne_zero, by simpa⟩
  constructor
  · intro h q hq hq1 hfq
    have h1 := height_comap_eq_one_of_flat_of_mem ρ hρ hf q hq1 hfq
    refine ((hgauss q hq hq1 hfq) x hd).mpr ⟨1, (Ideal.ne_top_iff_one q).mp hq.ne_top, ?_⟩
    simpa using h ⟨q.comap ρ, Ideal.comap_isPrime ρ q⟩ ⟨h1, hfq⟩
  · intro h p hp
    obtain ⟨hadd, hsmul, hinv⟩ := hWcl p.asIdeal p.2 hp.1 hp.2
    refine _root_.GlobalTheory.Desc.LocalDescent.mem_spanBy_of_forall_height_one R R₁ F F₁ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin p.asIdeal p.2 hp.1 hp.2
      (W p.asIdeal) (htor p.asIdeal p.2 hp.2) hadd hsmul hinv x hxr fun q hq hq1 hfq hqp => ?_
    have := ((hgauss q hq hq1 hfq) x hd).mp (h q hq hq1 hfq)
    rwa [hqp] at this

end GlobalTheory.Desc
end

