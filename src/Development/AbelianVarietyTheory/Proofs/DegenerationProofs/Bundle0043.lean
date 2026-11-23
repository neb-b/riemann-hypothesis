module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.SplitPull

theorem free_of_isField {R M : Type} [CommRing R] (hR : IsField R) [AddCommGroup M] [Module R M] :
    Module.Free R M := by
  letI := hR.toField
  exact Module.Free.of_divisionRing R M

theorem exists_basis_pushout {R R' : CommRingCat.{0}} (hR : IsField R) (b : R ⟶ R') :
    ∃ (J : Type) (e : J → R'), ∀ (A A' : CommRingCat.{0}) (a : R ⟶ A) (p : A ⟶ A') (q : R' ⟶ A'),
      IsPushout a b p q →
      (∀ u : A', ∃ (s : Finset J) (x : J → A), u = ∑ l ∈ s, p.hom (x l) * q.hom (e l)) ∧
      ∀ (s : Finset J) (x : J → A), ∑ l ∈ s, p.hom (x l) * q.hom (e l) = 0 → ∀ l ∈ s, x l = 0 := by
  letI := b.hom.toAlgebra
  haveI : Module.Free R R' := free_of_isField hR
  let e := Module.Free.chooseBasis R R'
  refine ⟨_, e, fun A A' a p q h => ?_⟩
  letI := a.hom.toAlgebra
  letI := p.hom.toAlgebra
  letI := q.hom.toAlgebra
  letI := (p.hom.comp a.hom).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout R A R' A' := CommRingCat.isPushout_iff_isPushout.mp h
  let B := hp.out.basis e
  have hB : ∀ l, B l = q.hom (e l) := fun l => hp.out.basis_apply e l
  refine ⟨fun u => ⟨(B.repr u).support, B.repr u, ?_⟩, fun s x hx => ?_⟩
  · conv_lhs => rw [← B.linearCombination_repr u]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl
  · refine linearIndependent_iff'.1 B.linearIndependent s x ?_
    rw [← hx]
    exact Finset.sum_congr rfl fun l _ => by rw [hB, Algebra.smul_def]; rfl

theorem exists_basis_sections {K K' : Type} [Field K] [Field K'] (f : Sp K' ⟶ Sp K) :
    ∃ (J : Type) (e : J → Γ(Sp K', ⊤)), ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (iX : X ⟶ Sp K) (iY : Y ⟶ Sp K'),
      IsPullback g iY iX f →
      (∀ U : X.Opens, IsAffineOpen U → ∀ u : Γ(Y, g ⁻¹ᵁ U), ∃ (s : Finset J) (x : J → Γ(X, U)),
        u = ∑ l ∈ s, (g.app U).hom (x l) * (iY.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom (e l)) ∧
      ∀ (s : Finset J) (x : J → Γ(X, ⊤)), ∑ l ∈ s, g.appTop.hom (x l) * iY.appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0 := by
  have hR : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨J, e, he⟩ := exists_basis_pushout hR (f.appLE ⊤ ⊤ le_top)
  refine ⟨J, e, fun X Y g iX iY h => ?_⟩
  have po : ∀ U : X.Opens, IsAffineOpen U → _ := fun U hU => he _ _ _ _ _
    ((isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) hU))
  refine ⟨fun U hU u => ?_, fun s x hx l hl => ?_⟩
  · have := (po U hU).1 u
    rwa [Scheme.Hom.appLE_eq_app] at this
  · refine X.IsSheaf.section_ext fun y _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine ⟨U, le_top, hy, ?_⟩
    rw [map_zero]
    refine (po U hU).2 s (fun l => resG X le_top (x l)) ?_ l hl
    have := congrArg (resG Y (le_top : g ⁻¹ᵁ U ≤ ⊤)) hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    congr 1
    exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Y, g ⁻¹ᵁ U) => q.hom (x l)) (g.map_appLE le_rfl (homOfLE le_top).op)

open GlobalTheory.UU

theorem appLE_app {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    (r.appLE (φ ⁻¹ᵁ V) ⊤ k).hom ((φ.app V).hom u) = (s.appLE V ⊤ k').hom u := by
  subst hs
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem appTop_appLE {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : s = r ≫ φ) (V : C.Opens)
    (k : ⊤ ≤ φ ⁻¹ᵁ V) (k' : ⊤ ≤ s ⁻¹ᵁ V) (u : Γ(C, V)) :
    r.appTop.hom ((φ.appLE V ⊤ k).hom u) = (s.appLE V ⊤ k').hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ V ⊤ ⊤ k le_top
  rw [← this]
  erw [r.appLE_eq_app]
  rfl

theorem appLE_appLE_top {A B C : Scheme.{0}} (r : A ⟶ B) (φ : B ⟶ C) (s : A ⟶ C) (hs : r ≫ φ = s) (V : B.Opens)
    (k : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(C, ⊤)) :
    (r.appLE V ⊤ k).hom ((φ.appLE ⊤ V le_top).hom u) = s.appTop.hom u := by
  subst hs
  have := Scheme.Hom.appLE_comp_appLE r φ ⊤ V ⊤ le_top k
  erw [(r ≫ φ).appLE_eq_app] at this
  exact congrArg (fun q => q.hom u) this

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G]
  [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G}
  {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i)
include hF hi

theorem stable_pull {V : G.left.Opens} (hV : Stable i V) : Stable i' (F ⁻¹ᵁ V) := by
  obtain ⟨τ, hτ, hχ, hc⟩ := hi
  intro Z t g h
  have ht : (pushPt hτ t ≫ i).left = (t ≫ i').left ≫ F := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← hc, ← Category.assoc]; rfl
  have := hV _ (pushPt hτ t) (pushPt hF.1.w g) h
  rwa [hF.2 Z (t ≫ i') g _ (pushPt hF.1.w g) ht rfl] at this

theorem hasWt_pull {V : G.left.Opens} {u : Γ(G.left, V)} {χ : X} (hu : HasWt i V u χ) :
    HasWt i' (F ⁻¹ᵁ V) ((F.app V).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hc⟩ := hi
  intro Z t g h h'
  have ht : (pushPt hτ t ≫ i).left = (t ≫ i').left ≫ F := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← hc, ← Category.assoc]; rfl
  have e := hF.2 Z (t ≫ i') g _ (pushPt hF.1.w g) ht rfl
  rw [appLE_app _ F _ e V h' (by rw [e]; exact h'), appLE_app _ F (pushPt hF.1.w g).left rfl V h h, ← hχ]
  refine (hu _ (pushPt hτ t) (pushPt hF.1.w g) _ _).trans (congrArg (· * _) ?_)
  show (t.left ≫ τ).appTop.hom _ = _
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem hasWt_coeff {J : Type} (e : J → Γ(S', ⊤))
    (he : ∀ (Y : Over S) (s : Finset J) (x : J → Γ(Y.left, ⊤)),
      ∑ l ∈ s, (pullback.fst Y.hom f).appTop.hom (x l) * (pullback.snd Y.hom f).appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0)
    {V : G.left.Opens} (s : Finset J) (x : J → Γ(G.left, V))
    (hu : HasWt i' (F ⁻¹ᵁ V) (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) 0) :
    ∀ l ∈ s, HasWt i V (x l) 0 := by
  intro l hl Y t g h h'
  rw [torusCompat_iff] at hi
  let Y' : Over S' := Over.mk (pullback.snd Y.hom f)
  let p : Y'.left ⟶ Y.left := pullback.fst Y.hom f
  have hp : p ≫ Y.hom = Y'.hom ≫ f := pullback.condition
  let p' : Over.mk (Y'.hom ≫ f) ⟶ Y := Over.homMk p hp
  have hT := SplitTorus.isPullback_bcMap f X
  have wt : (p ≫ t.left) ≫ (splitTorus S X).hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  have wg : (p ≫ g.left) ≫ G.hom = Y'.hom ≫ f := by rw [Category.assoc, Over.w, hp]
  let t' : Y' ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ wt) (hT.lift_snd _ _ wt)
  let g' : Y' ⟶ G' := Over.homMk (hF.1.lift _ _ wg) (hF.1.lift_snd _ _ wg)
  have ht' : t'.left ≫ SplitTorus.bcMap f X = p ≫ t.left := hT.lift_fst _ _ wt
  have hg' : p ≫ g.left = g'.left ≫ F := (hF.1.lift_fst _ _ wg).symm
  have hm : p ≫ ((t ≫ i) * g).left = ((t' ≫ i') * g').left ≫ F := by
    rw [← hF.2 Y' (t' ≫ i') g' (p' ≫ t ≫ i) (p' ≫ g) ?_ hg', ← MonObj.comp_mul]
    · rfl
    · change p ≫ t.left ≫ i.left = (t'.left ≫ i'.left) ≫ F
      rw [Category.assoc, ← hi, ← Category.assoc t'.left, ht', Category.assoc]
  have key : ∀ (r : Y ⟶ G) (r' : Y' ⟶ G') (_ : p ≫ r.left = r'.left ≫ F) (k : ⊤ ≤ r.left ⁻¹ᵁ V),
      ∃ k' : ⊤ ≤ r'.left ⁻¹ᵁ F ⁻¹ᵁ V, (r'.left.appLE _ ⊤ k').hom
        (∑ l ∈ s, (F.app V).hom (x l) * (G'.hom.appLE ⊤ (F ⁻¹ᵁ V) le_top).hom (e l)) =
        ∑ l ∈ s, p.appTop.hom ((r.left.appLE V ⊤ k).hom (x l)) * Y'.hom.appTop.hom (e l) := by
    intro r r' hr k
    have k₁ : ⊤ ≤ (p ≫ r.left) ⁻¹ᵁ V := p.preimage_mono k
    have k₂ : ⊤ ≤ (r'.left ≫ F) ⁻¹ᵁ V := hr ▸ k₁
    refine ⟨k₂, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, appLE_app _ F _ hr V k₂ k₁, appTop_appLE p r.left _ rfl V k k₁]
    exact congrArg (_ * ·) (appLE_appLE_top _ _ _ (Over.w r') _ _ _)
  obtain ⟨k₁, e₁⟩ := key _ _ hm h'
  obtain ⟨k₂, e₂⟩ := key _ _ hg' h
  have h0 := hu Y' t' g' k₂ k₁
  rw [e₁, e₂, charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h0
  rw [charUnit_zero_val, map_one, _root_.one_mul, ← sub_eq_zero]
  refine he Y s (fun l => (((t ≫ i) * g).left.appLE V ⊤ h').hom (x l) - (g.left.appLE V ⊤ h).hom (x l)) ?_ l hl
  rw [← h0]
  exact Finset.sum_congr rfl fun l _ => by rw [map_sub, sub_mul]; rfl

end

theorem pull_pull_and_split_pull : (∀ (X Y Y' : Scheme.{0}) (C : Charts X) (φ : Y ⟶ X) (ψ : Y' ⟶ Y) [IsAffineHom φ] [IsAffineHom ψ], (C.pull φ).pull ψ = C.pull (ψ ≫ φ)) ∧ ∀ (K K' : Type) [Field K] [Field K'] (H : Over (Sp K)) [GrpObj H] (H' : Over (Sp K')) [GrpObj H'] (f : Sp K' ⟶ Sp K) (φ : H'.left ⟶ H.left) [IsAffineHom φ], IsGrpPullback H' H f φ → ∀ (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl), C.Split c → Charts.Split (C.pull φ) c := by
  refine ⟨fun X Y Y' C φ ψ _ _ => rfl, ?_⟩
  rintro K K' _ _ H _ H' _ f φ _ hφ C d c ⟨hc, i, hT⟩
  obtain ⟨i', hi, -⟩ := existsUnique_torusCompat hφ.1 i
  have := hT.hom
  refine ⟨MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hc, i', hi.isMonHom hφ,
    fun a => stable_pull hφ hi (hT.stable a), fun a j hj => hasWt_pull hφ hi (hT.inv a j hj),
    fun a j k hj => hasWt_pull hφ hi (hT.wt a j k hj), fun k x => ?_, fun a u hu => ?_⟩
  · obtain ⟨a, j, hj, hx⟩ := hT.bpf k (φ x)
    refine ⟨a, j, hj, ?_⟩
    change x ∈ H'.left.basicOpen ((φ.app (C.W a)).hom (C.r a j))
    rw [← Scheme.preimage_basicOpen]
    exact hx
  · obtain ⟨J, e, he⟩ := exists_basis_sections f
    obtain ⟨s, x, rfl⟩ := (he _ _ φ _ _ hφ.1).1 (C.W a) (C.aff a) u
    have hx := hasWt_coeff hφ hi e (fun Y => (he _ _ _ _ _ (IsPullback.of_hasPullback Y.hom f)).2) s x hu
    refine Subring.sum_mem _ fun l hl => Subring.mul_mem _ ?_ (Subring.subset_closure (Or.inl ⟨e l, rfl⟩))
    have h1 := hT.gen a (x l) (hx l hl)
    refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ h1)
    rintro v (⟨w, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨f.appTop.hom w, ?_⟩)
      have e₁ := Scheme.Hom.appLE_comp_appLE φ H.hom ⊤ (C.W a) (φ ⁻¹ᵁ C.W a) le_top le_rfl
      have e₂ := Scheme.Hom.appLE_comp_appLE H'.hom f ⊤ ⊤ (φ ⁻¹ᵁ C.W a) le_top le_top
      simp only [hφ.1.w] at e₁
      rw [φ.appLE_eq_app] at e₁
      erw [f.appLE_eq_app] at e₂
      exact congrArg (fun q => q.hom w) (e₂.trans e₁.symm)
    · exact Subring.subset_closure (Or.inr ⟨j, hj, rfl⟩)

end GlobalTheory.ZJ.SplitPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusWeightTestGenericPointRationalPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

def wtDefect {P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens) (u : Γ(G, V))
    (e : Γ(T, ⊤)) : Γ(P, a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V) :=
  (a.appLE V _ inf_le_left).hom u - (c.appLE ⊤ _ le_top).hom e * (b.appLE V _ inf_le_right).hom u

theorem appLE_wtDefect {Z P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens)
    (u : Γ(G, V)) (e : Γ(T, ⊤)) (p : Z ⟶ P) {a' b' : Z ⟶ G} {c' : Z ⟶ T} (ha : p ≫ a = a')
    (hb : p ≫ b = b') (hc : p ≫ c = c') (h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V))
    (h₁ : ⊤ ≤ a' ⁻¹ᵁ V) (h₂ : ⊤ ≤ b' ⁻¹ᵁ V) :
    (p.appLE _ ⊤ h).hom (wtDefect a b c V u e) =
      (a'.appLE V ⊤ h₁).hom u - c'.appTop.hom e * (b'.appLE V ⊤ h₂).hom u := by
  subst ha hb hc
  have e₁ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p a V _ ⊤ inf_le_left h)
  have e₂ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p b V _ ⊤ inf_le_right h)
  have e₃ := congrArg (fun q => CommRingCat.Hom.hom q e)
    ((Scheme.Hom.appLE_comp_appLE p c ⊤ _ ⊤ le_top h).trans (Scheme.Hom.appLE_eq_app (p ≫ c)))
  rw [wtDefect, map_sub, map_mul]
  exact congrArg₂ (· - ·) e₁ (congrArg₂ (· * ·) e₃ e₂)

theorem eq_zero_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {P : Over (Sp k)}
    [Smooth P.hom] {W : P.left.Opens} (d : Γ(P.left, W))
    (h : ∀ (z : 𝟙_ (Over (Sp k)) ⟶ P) (x : (𝟙_ (Over (Sp k))).left),
      z.left x ∉ P.left.basicOpen d) : d = 0 := by
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced (S := Spec (.of k)) P.hom
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec (.of k)) P.hom
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  have hne' : ((P.left.basicOpen d : P.left.Opens) : Set P.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h' => hne (TopologicalSpace.Opens.ext h')
  obtain ⟨x, hxd, hx⟩ := nonempty_inter_closedPoints hne' (P.left.basicOpen d).isOpen.isLocallyClosed
  refine h (Over.homMk (pointOfClosedPoint (K := k) P.hom x hx)
    (pointOfClosedPoint_comp (K := k) P.hom x hx)) (IsLocalRing.closedPoint k) ?_
  have e := pointOfClosedPoint_apply (K := k) P.hom x hx (IsLocalRing.closedPoint k)
  exact e.symm ▸ hxd

theorem wt_of_genericPoint :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  intro k _ _ G _ hG X _ _ _ i F _ s g hg V u χ H
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp k)).1 X
  have : Smooth (splitTorus (Sp k) X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _
  have : Smooth (splitTorus (Sp k) X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp k) X).hom G.hom ≫
      (splitTorus (Sp k) X).hom))
  have hact : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left = ((t ≫ i) * y).left := by
    intro Z t y
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hsnd : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (snd (splitTorus (Sp k) X) G).left = y.left := by
    intro Z t y
    rw [← Over.comp_left, lift_snd]
  have hfst : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (fst (splitTorus (Sp k) X) G).left = t.left := by
    intro Z t y
    rw [← Over.comp_left, lift_fst]
  have hd : wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val = 0 := by
    refine eq_zero_of_rationalPoints _ fun z x hx => ?_
    set d := wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val with hdd
    let t := z ≫ fst _ _
    let m : G ⟶ splitTorus (Sp k) X ⊗ G := lift (toUnit G ≫ t) (𝟙 G)
    have hz : (z ≫ snd _ _) ≫ m = z := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, t, Category.assoc, lift_fst]
        rw [← Category.assoc (snd _ _), ← Category.assoc z, toUnit_unique (z ≫ _) (𝟙 _),
          Category.id_comp]
      · simp [m]
    have hgm : g ≫ m = lift (toUnit (Over.mk s) ≫ t) g := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, Category.assoc, lift_fst]
        rw [← Category.assoc, toUnit_unique (g ≫ _) (toUnit _)]
      · simp [m]
    have h0 := hg (m.left ⁻¹ᵁ (splitTorus (Sp k) X ⊗ G).left.basicOpen d)
      ⟨(z ≫ snd _ _).left x, by
        have : m.left ((z ≫ snd _ _).left x) = z.left x := congrArg (fun q => q.left x) hz
        show m.left ((z ≫ snd _ _).left x) ∈ (splitTorus (Sp k) X ⊗ G).left.basicOpen d
        rw [this]; exact hx⟩
    have h1 : ⊤ ≤ (lift (toUnit (Over.mk s) ≫ t) g).left ⁻¹ᵁ
        (splitTorus (Sp k) X ⊗ G).left.basicOpen d := by
      rw [← hgm]; exact h0
    have h2 := h1.trans ((lift (toUnit (Over.mk s) ≫ t) g).left.preimage_mono
      ((splitTorus (Sp k) X ⊗ G).left.basicOpen_le d))
    have h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V := by
      rw [← hact]; exact fun y hy => (h2 hy).1
    have h₂ : ⊤ ≤ g.left ⁻¹ᵁ V := by
      rw [← hsnd (toUnit (Over.mk s) ≫ t)]; exact fun y hy => (h2 hy).2
    have hu := isUnit_ev (R := F) _ _ h2 d h1
    have hv := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact _ _) (hsnd _ _) (hfst _ _) h2 h₁ h₂)
    have hH := (H t h₁ h₂).trans (congrArg (· * ev (R := F) g.left V h₂ u)
      (ev_top (R := F) (toUnit (Over.mk s) ≫ t).left le_top (charUnit (Sp k) X χ).val))
    refine hu.ne_zero (hv.trans ?_)
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hH.trans (map_mul _ _ _).symm))
  intro Z t y h₁ h₂
  have h : ⊤ ≤ (lift t y).left ⁻¹ᵁ (((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left ⁻¹ᵁ V ⊓
      (snd (splitTorus (Sp k) X) G).left ⁻¹ᵁ V) := by
    rw [← hact] at h₁
    rw [← hsnd t] at h₂
    exact fun w hw => ⟨h₁ hw, h₂ hw⟩
  have hv := appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact t y) (hsnd t y) (hfst t y)
    h h₁ h₂
  rw [hd, map_zero] at hv
  exact sub_eq_zero.1 hv.symm

end GlobalTheory.SS.WtRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependence
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem vt_mul_io_shift (g : N.Gt) (w χ : N.X) :
    ((N.ψ w * g.s w : Oˣ) : O) * N.vt (g * N.io w) χ = N.vt g (χ + w) := by
  have e : N.c χ * (g * N.io w).b = N.c (χ + w) * g.b := by
    rw [Gt.mul_b, io_b, N.c_add, mul_assoc, mul_comm g.b]
  rw [vt, vt, e, ← mul_assoc, ← Units.val_mul]
  congr 2
  have a := congrArg Additive.ofMul (g.mult χ w)
  rw [Gt.mul_s, io_s, io_b, N.ψ_add, N.τ_symm w χ, N.cub.s12 (N.c χ) g.b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) -a

theorem vt_mul_tor_shift (g : N.Gt) (t : Multiplicative N.X →* Oˣ) (χ : N.X) :
    N.vt (g * N.tor t) χ = (t (Multiplicative.ofAdd χ) : Oˣ) * N.vt g χ := by
  rw [vt, vt, mul_comm g, N.tor_mul_s_apply, Gt.mul_b, tor_b, one_mul, mul_left_comm (N.ψ χ), Units.val_mul, mul_assoc]

theorem tk_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.tk p (N.qTriv k z) = p.1.2.s z ^ k :=
  ((_root_.GlobalTheory.PsiQuadratic.main O N k z).2.2 p.1.2).1

theorem tk_qTriv_left {k : ℕ} (p : N.QT k) (z : N.X) : N.tk (N.qTriv k z) p = p.1.2.s z ^ k := by
  rw [← Gt.pow_s, N.mem_QT.1 p.2, io_s, N.τ_symm]
  rfl

theorem wQ_qTriv_odd {k : ℕ} (hk : Odd k) (z : N.X) : N.wQ (N.qTriv k z) = N.ψ z ^ k := by
  symm
  rw [(_root_.GlobalTheory.Ex.SymLift.normalising_factor O N k hk (N.qTriv k z) (N.qTriv k z)).1, tk_qTriv_right]
  obtain ⟨h₁, h₂, -⟩ := _root_.GlobalTheory.PsiQuadratic.main O N k z
  constructor
  · change _ * dbl N.θ N.σ (N.c z) ^ k = N.τ z z ^ k
    rw [h₁, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  · change _ = N.ψ (k • z) * mulq N.θ N.σ k (N.c z)
    rw [h₂, ← pow_mul, sq]

theorem wQ_mul_qTriv_odd {k : ℕ} (hk : Odd k) (p : N.QT k) (z : N.X) :
    N.wQ (p * N.qTriv k z) = N.wQ p * N.ψ z ^ k * p.1.2.s z ^ k := by
  have h := (_root_.GlobalTheory.Ex.SymLift.normalising_factor O N k hk p (N.qTriv k z)).2.1
  rw [wp, tk_qTriv_right, tk_qTriv_left, div_self', one_pow, one_mul, N.wQ_qTriv_odd hk] at h
  exact h.symm

theorem txT_mul_qTriv {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (z χ : N.X) :
    N.txT m (p * N.qTriv (m ^ 2) z) χ = N.txT m p (χ + m • z) := by
  have e : (p * N.qTriv (m ^ 2) z).1.2 = p.1.2 * N.io z := rfl
  rw [txT, txT, N.wQ_mul_qTriv_odd hm.pow, e, mul_pow, ← N.io_nsmul, ← N.vt_mul_io_shift, ← mul_assoc,
    ← Units.val_mul]
  congr 2
  have h₁ := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB m 0 p.1.2.b (N.c z)).2.1
  obtain ⟨-, h₂, h₃⟩ := _root_.GlobalTheory.PsiQuadratic.main O N m z
  have h₄ := congrArg (· ^ m) (h₃ p.1.2).1
  have h₅ := Gt.pow_s p.1.2 m (m • z)
  rw [N.c_nsmul] at h₅
  simp only [mul_pow, ← pow_mul, ← sq] at h₄
  rw [Gt.mul_b, io_b, h₁, ← h₂, ← h₄, ← h₅]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem txT_mul_tor {m : ℕ} (hm : Odd m) (p p' : N.QT (m ^ 2)) (χ : N.X) (t : Multiplicative N.X →* Oˣ)
    (h : p'.1.1 = p.1.1) (h' : p'.1.2 = p.1.2 * N.tor t) :
    N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) *
      N.txT m p χ := by
  have ht : t ^ (m ^ 2) = 1 := by
    apply N.tor_injective
    have a := N.mem_QT.1 p'.2
    rw [h, h', mul_pow, N.mem_QT.1 p.2, mul_eq_left] at a
    rw [N.tor_pow, a, N.tor_one]
  obtain ⟨j, hj⟩ : Odd (m ^ 2) := hm.pow
  have hd : (m ^ 2 - 1) / 2 = j := by omega
  have hy : t p.1.1 ^ j * t p.1.1 ^ j * t p.1.1 = 1 := by
    rw [← pow_add, ← pow_succ, ← two_mul, ← hj, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
  have hb : p'.1.2.b = p.1.2.b := by rw [h', Gt.mul_b, tor_b, mul_one]
  have hs : p'.1.2.s p.1.1.toAdd = t p.1.1 * p.1.2.s p.1.1.toAdd := by
    rw [h', mul_comm p.1.2, N.tor_mul_s_apply]
    rfl
  rw [txT, txT, wQ, wQ, NumB.wS, NumB.wS, hb, h, hs, h', mul_pow, ← N.tor_pow, vt_mul_tor_shift, hd,
    ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [ofAdd_add, ofAdd_toAdd, ofAdd_nsmul, map_mul, map_pow, MonoidHom.pow_apply]
  have a := congrArg Additive.ofMul hy
  apply Additive.ofMul.injective
  simp only [div_pow, mul_pow, ofMul_mul, ofMul_div, ofMul_one] at a ⊢
  linear_combination (norm := abel) -a

end GlobalTheory.Ex.NumD

namespace GlobalTheory.Ex

theorem txT_shift : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  intro O _ N m hm p p' χ
  refine ⟨fun z h h' => ?_, fun t h h' => N.txT_mul_tor hm p p' χ t h h'⟩
  have e : p' = p * N.qTriv (m ^ 2) z := Subtype.ext (Prod.ext h h')
  rw [e, N.txT_mul_qTriv hm]

end GlobalTheory.Ex
end

