module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverO

def counitCoef {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) {G : C' ⥤ C} {H : C ⥤ C'} (adj : G ⊣ H) :
    CoefMap (RingHom.id R) (G ⋙ F) F where
  G := H
  α V := (mp F (adj.counit.app V)).toRingHom
  naturality {V V'} φ b := by
    change mp F (adj.counit.app V') (mp F (G.map (H.map φ)) b) = mp F φ (mp F (adj.counit.app V) b)
    rw [← mp_comp, ← mp_comp]
    have e := adj.counit.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at e
    rw [e]
  smul V r b := by
    change mp F (adj.counit.app V) (r • b) = r • mp F (adj.counit.app V) b
    exact map_smul _ r b

theorem restrict_pull1_bijective_of_adj {R : Type} [CommRing R] {C C' : Type} [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C') (adj : G ⊣ H) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  have hl : ∀ c, (counitCoef F adj).pull1 ((CoefMap.restrict F G).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (CoefMap.pullCohomologyOne_id c)
  have hr : ∀ c, (CoefMap.restrict F G).pull1 ((counitCoef F adj).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    refine ((CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (CoefMap.pullCohomologyOne_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

theorem restrict_cover_affine_pull1_bijective (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (J : Type) (U : J → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op).pull1 := by
  let G : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ ⥤ AffOp X := (Monotone.functor
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
  have hdir : ∀ (t₁ t₂ : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (S : AffOp X), (G.obj t₁ ⟶ S) →
      (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
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
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull1 := by
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
  have b1 : Function.Bijective (CoefMap.restrict (OAff s) incl).pull1 :=
    restrict_cover_affine_pull1_bijective R X s J (fun i => (U i).1) hcov
  have b2 := restrict_pull1_bijective_of_adj (incl ⋙ OAff s) gc.monotone_u.functor.op
    gc.monotone_l.functor.op gc.adjunction.op
  have e : ∀ c, (CoefMap.restrict (OAff s) hU.functor.op).pull1 c =
      (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op).pull1
        ((CoefMap.restrict (OAff s) incl).pull1 c) := fun c =>
    (CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (CoefMap.pullCohomologyOne_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomSplitBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SplitCx

variable {R : Type} [CommRing R]

theorem exists_quasiInv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (d : M →ₗ[R] N) (hQ : Module.Projective R (N ⧸ LinearMap.range d)) :
    ∃ b : N →ₗ[R] M, ∀ x, d (b (d x)) = d x := by
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y : N, y - t ((LinearMap.range d).mkQ y) ∈ LinearMap.range d := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun ht ((LinearMap.range d).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let r : N →ₗ[R] LinearMap.range d :=
    LinearMap.codRestrict _ (LinearMap.id - t ∘ₗ (LinearMap.range d).mkQ) hmem
  have hr : ∀ y : LinearMap.range d, r y = y := by
    intro y
    apply Subtype.ext
    simp only [r, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 y.2, map_zero, sub_zero]
  haveI : Module.Projective R (LinearMap.range d) :=
    Module.Projective.of_split (LinearMap.range d).subtype r (LinearMap.ext hr)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict d)
  refine ⟨s ∘ₗ r, fun x => ?_⟩
  have h1 := LinearMap.congr_fun hs (r (d x))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
  have h2 := congrArg Subtype.val h1
  have h3 : (r (d x) : N) = d x := congrArg Subtype.val (hr ⟨d x, LinearMap.mem_range_self d x⟩)
  exact h2.trans h3

theorem exists_decomp {M0 M1 M2 : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [Module.Projective R M1] [Module.Projective R M2]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (h : ∀ x, d1 (d0 x) = 0)
    (hQ1 : Module.Projective R (M1 ⧸ LinearMap.range d0))
    (hQ2 : Module.Projective R (M2 ⧸ LinearMap.range d1)) :
    ∃ (e : M1 →ₗ[R] M1) (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1),
      e ∘ₗ e = e ∧ e ∘ₗ d0 = 0 ∧ d1 ∘ₗ e = 0 ∧ LinearMap.id = e + d0 ∘ₗ a + b ∘ₗ d1 := by
  obtain ⟨b, hb⟩ := exists_quasiInv d1 hQ2
  obtain ⟨b', hb'⟩ := exists_quasiInv d0 hQ1
  set a : M1 →ₗ[R] M0 := b' ∘ₗ (LinearMap.id - b ∘ₗ d1) with ha
  set e : M1 →ₗ[R] M1 := LinearMap.id - d0 ∘ₗ a - b ∘ₗ d1 with he0
  have he : ∀ y, e y = y - d0 (b' (y - b (d1 y))) - b (d1 y) := fun y => by
    simp [e, a]
  have k1 : ∀ x, d1 (e x) = 0 := fun x => by
    rw [he]; simp only [map_sub, h, hb]; abel
  have k2 : ∀ x, d0 (b' (e x)) = 0 := fun x => by
    rw [he]; simp only [map_sub, hb']; abel
  refine ⟨e, a, b, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply]
    simp only [he (e x), k1, map_zero, sub_zero, k2]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    simp only [he, h, map_zero, sub_zero, hb', sub_self]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, k1]
  · ext x
    simp only [e, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

theorem bc {M0 M1 M2 P : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [AddCommGroup P] [Module R P]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (π : M1 →ₗ[R] P) (σ : P →ₗ[R] M1)
    (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1)
    (hπσ : π ∘ₗ σ = LinearMap.id) (hπd : π ∘ₗ d0 = 0) (hdσ : d1 ∘ₗ σ = 0)
    (hid : LinearMap.id = σ ∘ₗ π + d0 ∘ₗ a + b ∘ₗ d1) (S : Type) [CommRing S] [Algebra R S] :
    Function.Surjective (fun z : LinearMap.ker (d1.baseChange S) => π.baseChange S z.1) ∧
      ∀ z : LinearMap.ker (d1.baseChange S),
        π.baseChange S z.1 = 0 ↔ z.1 ∈ LinearMap.range (d0.baseChange S) := by
  have e1 : ∀ y, π.baseChange S (σ.baseChange S y) = y := fun y => by
    have := congrArg (LinearMap.baseChange S) hπσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at this
    exact LinearMap.congr_fun this y
  have e2 : ∀ y, π.baseChange S (d0.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hπd
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e3 : ∀ y, d1.baseChange S (σ.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hdσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e4 : ∀ y, y = σ.baseChange S (π.baseChange S y) + d0.baseChange S (a.baseChange S y)
      + b.baseChange S (d1.baseChange S y) := fun y => by
    have := congrArg (LinearMap.baseChange S) hid
    rw [LinearMap.baseChange_id, LinearMap.baseChange_add, LinearMap.baseChange_add,
      LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.baseChange_comp] at this
    exact LinearMap.congr_fun this y
  refine ⟨fun y => ⟨⟨σ.baseChange S y, e3 y⟩, e1 y⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · refine ⟨a.baseChange S z.1, ?_⟩
    have h0 : d1.baseChange S z.1 = 0 := z.2
    have := e4 z.1
    rw [hz, h0, map_zero, map_zero, zero_add, add_zero] at this
    exact this.symm
  · rintro ⟨w, hw⟩
    rw [← hw]; exact e2 w

end GlobalTheory.AbCoh.SplitCx

namespace GlobalTheory.AbCoh

theorem cohom_split_baseChange : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z := by
  intro R _ K hK hQ i h1 h2 R' _ _
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  try simp only [Nat.add_sub_cancel, Nat.add_one_sub_one]
  haveI : Module.Projective R (K.X (j + 1)) := (hK _).2
  haveI : Module.Projective R (K.X (j + 1 + 1)) := (hK _).2
  haveI : Module.Finite R (K.X (j + 1)) := (hK _).1
  have hdd : ∀ x, (K.d (j + 1) (j + 1 + 1)).hom ((K.d j (j + 1)).hom x) = 0 := fun x => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]; rfl
  obtain ⟨e, a, b, hee, hed, hde, hid⟩ := SplitCx.exists_decomp (K.d j (j + 1)).hom
    (K.d (j + 1) (j + 1 + 1)).hom hdd (hQ j (by omega)) (hQ (j + 1) (by omega))
  let π : K.X (j + 1) →ₗ[R] LinearMap.range e := e.rangeRestrict
  let σ : LinearMap.range e →ₗ[R] K.X (j + 1) := (LinearMap.range e).subtype
  have hπσ : π ∘ₗ σ = LinearMap.id := by
    ext ⟨y, w, rfl⟩
    change e (e w) = e w
    rw [← LinearMap.comp_apply, hee]
  have hπd : π ∘ₗ (K.d j (j + 1)).hom = 0 := by
    ext x
    change e ((K.d j (j + 1)).hom x) = 0
    rw [← LinearMap.comp_apply, hed]; rfl
  have hdσ : (K.d (j + 1) (j + 1 + 1)).hom ∘ₗ σ = 0 := by
    ext ⟨y, w, rfl⟩
    change (K.d (j + 1) (j + 1 + 1)).hom (e w) = 0
    rw [← LinearMap.comp_apply, hde]; rfl
  have hid' : LinearMap.id = σ ∘ₗ π + (K.d j (j + 1)).hom ∘ₗ a + b ∘ₗ (K.d (j + 1) (j + 1 + 1)).hom := by
    rw [hid]; rfl
  haveI : Module.Projective R (LinearMap.range e) := Module.Projective.of_split σ π hπσ
  obtain ⟨sR, kR⟩ := SplitCx.bc _ _ π σ a b hπσ hπd hdσ hid' R
  obtain ⟨sR', kR'⟩ := SplitCx.bc _ _ π σ a b hπσ hπd hdσ hid' R'
  refine ⟨LinearMap.range e, inferInstance, inferInstance, inferInstance, inferInstance,
    (TensorProduct.lid R _).toLinearMap ∘ₗ (π.baseChange R ∘ₗ (LinearMap.ker _).subtype),
    π.baseChange R' ∘ₗ (LinearMap.ker _).subtype, ?_, sR', ?_, kR', ?_⟩
  · exact (TensorProduct.lid R _).surjective.comp sR
  · intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype,
      LinearEquiv.map_eq_zero_iff]
    exact kR z
  · intro z z' hz
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
    rw [hz]
    clear hz
    induction (z.1 : R ⊗[R] K.X (j + 1)) using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [ext, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, Algebra.ofId_apply,
        LinearMap.baseChange_tmul, TensorProduct.lid_tmul]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, _root_.mul_one]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationPairingWellDefined
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_vf_of_frame {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (l : Glob1 F →ₗ[R] R) :
    ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T,
      (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧
      ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  obtain ⟨m, ⟨fr⟩⟩ := hF
  refine ⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (fr.w i)) • fr.δ i T, fun T T' φ ω ↦ ?_, fun w T ↦ ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [LinearMap.sum_apply, LinearMap.smul_apply, fr.nat, smul_eq_mul, map_sum,
      map_mul, AlgHom.commutes]
  · have hc : ∀ i, ∃ c : R, ∀ T, fr.δ i T (w.1 T) = algebraMap R (F.obj T) c := fun i ↦ by
      obtain ⟨c, hc, -⟩ := h0 (fun T ↦ fr.δ i T (w.1 T)) (by
        funext T T' φ
        simp only [amitsur_d0_apply, Pi.zero_apply]
        rw [w.2 φ, fr.nat, sub_self])
      exact ⟨c, hc⟩
    choose c hc using hc
    have hw : w = ∑ i, c i • fr.w i := by
      refine Subtype.ext (funext fun T ↦ ?_)
      rw [fr.sum T (w.1 T)]
      simp only [hc, algebraMap_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    conv_rhs => rw [hw]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smul, hc, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem derivClass_eq : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x y' w' → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = ∑ k, l (w' k) • y' k := by
  intro R _ C _ F hF h0 x n n' y w y' w' hd hd' l
  obtain ⟨δ, hnat, hδ⟩ := exists_vf_of_frame F hF h0 l
  obtain ⟨f, g, ω, rfl, hg, hf⟩ := hd
  obtain ⟨f', g', ω', hx, hg', hf'⟩ := hd'
  obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 hx
  obtain rfl : y = fun k ↦ H1.mk F (g k) := funext fun k ↦ (hg k).symm
  obtain rfl : y' = fun k ↦ H1.mk F (g' k) := funext fun k ↦ (hg' k).symm
  have e1 : ∑ k, l (w k) • H1.mk F (g k) = H1.mk F (∑ k, l (w k) • g k) := by simp [map_sum, map_smul]
  have e2 : ∑ k, l (w' k) • H1.mk F (g' k) = H1.mk F (∑ k, l (w' k) • g' k) := by simp [map_sum, map_smul]
  rw [e1, e2, H1.mk_eq_mk]
  refine ⟨fun T ↦ δ T (ω' T - ω T - D R _ (b T)), ?_⟩
  funext T T' φ
  have hbφ : d0 F b T T' φ = f'.1 T T' φ - f.1 T T' φ := congrFun (congrFun (congrFun hb T) T') φ
  have key : D R _ (f'.1 T T' φ) - D R _ (f.1 T T' φ) = D R _ (b T') - p1 F φ (D R _ (b T)) := by
    rw [← map_sub, ← hbφ, amitsur_d0_apply, map_sub, p1_D]
  rw [hf φ, hf' φ] at key
  have e := congrArg (δ T') key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_add (f := _), map_sum, LinearMap.map_smul, hnat, hδ, smul_eq_mul] at e
  simp only [amitsur_d0_apply, map_sub, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.sub_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  simp only [mul_comm (algebraMap R _ _)] at e ⊢
  linear_combination e

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSubEqDetCharSmulOfMemInv
section
open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

variable {ι : Type} [Fintype ι]

def genColSub (d a : ℕ) : Pol ι d a →ₐ[ℂ] MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval fun y => ∑ j' : Fin a, C (X (y.1, j', y.2.2)) * X (y.1, y.2.1, j')

omit [Fintype ι] in
theorem map_eval_genColSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genColSub d a P) = colSub g P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [genColSub, colSub, algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp =>
    simp only [map_mul, hp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [genColSub, colSub, map_sum]

def genDetChar (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_genDetChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genDetChar a n) = detChar n g := by
  rw [genDetChar, map_prod, detChar]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem colSub_eq_detChar_smul_of_mem_inv {a d : ℕ} (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) : colSub g P = detChar n g • P := by
  set D : MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
    genColSub d a P - C (genDetChar a n) * map C P with hDdef
  have hD : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ,
      map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) D = colSub g P - detChar n g • P := by
    intro g
    rw [hDdef, map_sub, map_mul, map_C, map_eval_genColSub, eval_genDetChar, map_map, smul_eq_C_mul]
    congr 2
    have : (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2).comp (C : ℂ →+* MvPolynomial (ι × Fin a × Fin a) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, map_id]
  have hD0 : D = 0 := by
    refine MvPolynomial.ext _ _ fun m => ?_
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := a) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [← coeff_map, hD u]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin a) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hP (fun τ => ⟨u τ, hu' τ⟩)
    simp only at this
    simp only [this, sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have := hD g
  rw [hD0, _root_.map_zero] at this
  exact (sub_eq_zero.mp this.symm)

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDetermStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V1 V2 : Submodule K R) [FiniteDimensional K V2] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V1) → (∀ h : H, ∀ x ∈ V1, act h x ∈ V1) → (∀ h : H, ∀ x ∈ V1, x * act h u ∈ V2) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V2 := by
  first | exact @GlobalTheory.BadCount.embReg_of_groupDet | exact GlobalTheory.BadCount.embReg_of_groupDet | (intros; apply GlobalTheory.BadCount.embReg_of_groupDet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeIsRootOfSimpleRootPointedEtaleNbhdStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (h : Polynomial i.A) (a₀ : i.A), h.Monic → i.pt (h.eval a₀) = 0 → i.pt (h.derivative.eval a₀) ≠ 0 → ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B), (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧ c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  first | exact @GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root | exact GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root | (intros; apply GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root <;> assumption)
end

