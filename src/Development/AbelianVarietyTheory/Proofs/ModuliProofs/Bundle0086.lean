module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.FiniteClasses

open GlobalTheory.Points

theorem preconnectedSpace_pts (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : PreconnectedSpace (Pts (spMap (algebraMap ℂ A))) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) A 1 one_ne_zero
  have he := isEmbedding_ptsOverEquivAlgHom (C := ℂ) A (id_eq_spMap_algebraMap ℂ)
  refine ⟨he.isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨(ptsOverEquivAlgHom A (id_eq_spMap_algebraMap ℂ)).symm φ, trivial, by simp⟩

theorem finite_range_affine (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] {I : Type*}
    (c : Pts (spMap (algebraMap ℂ A)) → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcomp : ∀ P : Ideal A, spMap (Ideal.Quotient.mk P) ≫ spMap (algebraMap ℂ A) =
      spMap (algebraMap ℂ (A ⧸ P)) := fun P => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfin : (⋃ P ∈ minimalPrimes A,
      Set.range (c ∘ PtsOver.map (spMap (Ideal.Quotient.mk P)) (hcomp P) (𝟙 _))).Finite := by
    refine (minimalPrimes.finite_of_isNoetherianRing A).biUnion fun P hP => ?_
    have : P.IsPrime := hP.1.1
    have := preconnectedSpace_pts (A ⧸ P)
    exact Set.Subsingleton.finite (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hc.comp_continuous (PtsOver.continuous_map _ _ _)).apply_eq_of_preconnectedSpace a b)
  refine hfin.subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, rfl⟩ := (ptsEquivAlgHom A).symm.surjective x
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := RingHom.ker φ.toRingHom) bot_le
  refine Set.mem_biUnion (x := P) hP ⟨(ptsEquivAlgHom (A ⧸ P)).symm
    (Ideal.Quotient.liftₐ P φ fun a ha => hle ha), congrArg c (Subtype.ext ?_)⟩
  simp only [PtsOver.map_val, ptsOverEquivAlgHom_symm_val]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem finite_range {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [QuasiCompact p] {I : Type*}
    (c : Pts p → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let 𝒰 := Y.affineOpenCover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (X := Y)
    (fun i => ((𝒰.f i).opensRange : Set Y)) (fun i => (𝒰.f i).opensRange.isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨𝒰.idx y, 𝒰.covers y⟩)
  have key : ∀ {R : CommRingCat.{0}} (j : Spec R ⟶ Y) [IsOpenImmersion j],
      (Set.range (c ∘ PtsOver.map j rfl (𝟙 _))).Finite := by
    intro R j _
    have hl : IsLocallyConstant (c ∘ PtsOver.map j rfl (𝟙 _)) :=
      hc.comp_continuous (PtsOver.continuous_map _ _ _)
    have hft : LocallyOfFiniteType (j ≫ p) := inferInstance
    generalize c ∘ PtsOver.map j rfl (𝟙 _) = c' at hl
    generalize j ≫ p = q at c' hl hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact finite_range_affine R c' hl
  refine (t.finite_toSet.biUnion fun i _ => key (𝒰.f i)).subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (x.1 (IsLocalRing.closedPoint ℂ))))
  have hx' : x ∈ Set.range (PtsOver.map (𝒰.f i) rfl (𝟙 _)) := by
    rw [PtsOver.range_map, range_comp_of_isOpenImmersion]
    exact (le_preimage_iff x.1 _).2 hx
  obtain ⟨z, rfl⟩ := hx'
  exact Set.mem_biUnion hi ⟨z, rfl⟩

theorem isLocallyConstant_of_hol {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) (d : ℕ)
    (hp : SmoothOfRelativeDimension d p) {I : Type*} (c : Pts p → I)
    (H : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → Pts p), IsOpen B → IsHolTo B (fun b => (y b).1) →
      ∀ b₀ ∈ B, ∀ᶠ b in 𝓝 b₀, c (y b) = c (y b₀)) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let h := overHomeomorph (C := ℂ) (Over.mk p)
  obtain ⟨W, σ, U, t, hW, h0, hσ, -, hhol, hco, hop, -⟩ := HolChart.exists_holomorphic_chart valAt'_rules
    existsUnique_point_of_ringHom exists_holomorphic_section_of_etale (Over.mk p) d hp (h.symm x)
  have hop' : IsOpen (σ '' W) := by
    refine TopologicalSpace.le_def.1 (le_generateFrom ?_) _ hop
    rintro _ ⟨V, f, O, hO, rfl⟩
    exact (isOpen_basicSet (C := ℂ) V f hO).preimage (isEmbedding_left (Over.mk p)).continuous
  have hx : h (σ 0) = x := by rw [hσ, Homeomorph.apply_symm_apply]
  have hev := H W (fun b => h (σ b)) hW hhol 0 h0
  have hxU : ⊤ ≤ x.1 ⁻¹ᵁ U := by rw [← hx]; exact (hco 0 h0).1
  have hT : Tendsto (fun (z : Pts p) (i : Fin d) => valR z.1 U (t i)) (𝓝 x) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    have h1 := ((continuousAt_valR (t i) hxU).comp continuous_subtype_val.continuousAt).tendsto
    have h2 : valR x.1 U (t i) = (0 : Fin d → ℂ) i := by rw [← hx]; exact (hco 0 h0).2 i
    rw [← h2]
    exact h1
  have hN : h '' (σ '' W) ∈ 𝓝 x := (h.isOpenMap _ hop').mem_nhds ⟨_, ⟨0, h0, rfl⟩, hx⟩
  filter_upwards [hN, hT.eventually hev] with z hz hz'
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have : (fun i => valR (h (σ w)).1 U (t i)) = w := funext (hco w hw).2
  rw [this, hx] at hz'
  exact hz'

theorem finite_image_of_locally_constant_on_holomorphic_families :
    (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B) → ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (I : Type 1) (cls : (Sp ℂ ⟶ X) → I), SmoothOfRelativeDimension d s → QuasiCompact s → (∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B, ∀ᶠ b in nhds b₀, cls (y b) = cls (y b₀)) → (cls '' {x | x ≫ s = spMap σ}).Finite := by
  intro _ k _ σ X s d I cls hs hq H
  let p := pullback.snd s (spMap σ)
  let q := pullback.fst s (spMap σ)
  have hp : SmoothOfRelativeDimension d p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback s (spMap σ)) hs
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hover : ∀ z : Pts p, (z.1 ≫ q) ≫ s = spMap σ := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, Category.id_comp]
  have hl : IsLocallyConstant fun z : Pts p => cls (z.1 ≫ q) := by
    refine isLocallyConstant_of_hol p d hp _ fun B y hB hy => ?_
    refine H B (fun b => (y b).1 ≫ q) hB (fun b _ => hover _) fun U f => ?_
    simp only [valAt'_eq_valR, valR_comp]
    exact hy (q ⁻¹ᵁ U) ((q.app U).hom f)
  refine (finite_range p _ hl).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx), pullback.lift_snd _ _ _⟩, ?_⟩
  exact congrArg cls (pullback.lift_fst _ _ _)

end GlobalTheory.FiniteClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerCommutesWithEndomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS.Endo

private theorem valAt'_comp_lemma {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) :
    valAt' (x ≫ φ) U a = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom a) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dite_eq_right h, dite_eq_right h']

theorem ptDer_push {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : X ⟶ Y) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) :
    PtDer (y ≫ f) (fun W a => δ (f ⁻¹ᵁ W) ((f.app W).hom a)) := by
  constructor
  · intro W hW a b
    rw [(f.app W).hom.map_add]
    exact h.add (f ⁻¹ᵁ W) hW _ _
  · intro W hW a b
    rw [map_mul, valAt'_comp_lemma y f W a, valAt'_comp_lemma y f W b]
    exact h.mul (f ⁻¹ᵁ W) hW _ _
  · intro W W' hle hW a
    have hle' : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W := fun x hx => hle hx
    have nat : (f.app W').hom (resG Y hle a) = resG X hle' ((f.app W).hom a) :=
      congrArg (fun φ : Γ(Y, W) ⟶ Γ(X, f ⁻¹ᵁ W') => φ.hom a) (f.naturality (homOfLE hle).op)
    rw [nat]
    exact h.res (f ⁻¹ᵁ W) (f ⁻¹ᵁ W') hle' hW _

theorem ptDer_sub {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W a => δ W a - δ' W a) := by
  constructor
  · intro W hW a b
    rw [h.add W hW, h'.add W hW]
    ring
  · intro W hW a b
    rw [h.mul W hW, h'.mul W hW]
    ring
  · intro W W' hle hW a
    rw [h.res W W' hle hW, h'.res W W' hle hW]

theorem app_top_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : X ⟶ X) (hf : f ≫ p = p) (r : R) :
    (f.app ⊤).hom (constFn p ⊤ r) = resG X (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤) (constFn p ⊤ r) := by
  have aux : ∀ q : X ⟶ Sp R, q = p → ∀ e e', q.appLE ⊤ (f ⁻¹ᵁ ⊤) e = p.appLE ⊤ (f ⁻¹ᵁ ⊤) e' := by
    rintro q rfl e e'
    rfl
  have key : ∀ e, p.appLE ⊤ ⊤ e ≫ f.app ⊤ =
      p.appLE ⊤ ⊤ e ≫ X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)).op := by
    intro e
    rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE f, Scheme.Hom.appLE_comp_appLE]
    exact aux _ hf _ _
  unfold constFn
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(X, f ⁻¹ᵁ ⊤) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (key _)

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

theorem fn_differentiableAt (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z : Fin g → ℂ) (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W a) z := by
  have hU := u.hol (m ⁻¹ᵁ W) ((m.app W).hom a)
  have hz' : z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W)} := hz
  have heq : fn u m W a = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom a) := by
    funext w
    exact valAt'_comp_lemma (u.ex w).left m W a
  rw [heq]
  exact hU.2.differentiableAt (hU.1.mem_nhds hz')

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z l : Fin g → ℂ) (hl : l ∈ u.Λ) :
    fderiv ℂ (fn u m W a) (z + l) = fderiv ℂ (fn u m W a) z := by
  have hper : (fun w => fn u m W a (w + l)) = fn u m W a := by
    funext w
    unfold fn
    rw [ex_add_lattice u w l hl]
  rw [← fderiv_comp_add_right, hper]

theorem comm_of_endo : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  intro P₀ u Hm χ hU R instR x₀ X p m hp hpb D Θ s hKS f f₀ F hfp hf₀ hF
  have hFdiff : Differentiable ℂ F := by
    have := (LinearMap.toContinuousLinearMap F).differentiable
    rwa [LinearMap.coe_toContinuousLinearMap'] at this

  have hpt : ∀ z, (u.ex z).left ≫ m ≫ f = (u.ex (F z)).left ≫ m := by
    intro z
    rw [hF z, Over.comp_left, Category.assoc, hf₀]

  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hone : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P₀.A) ≫ f₀ = 1 := by
    have h0 := hF 0
    rw [map_zero, hex0] at h0
    exact h0.symm
  have hFl : ∀ l ∈ u.Λ, F l ∈ u.Λ := by
    intro l hl
    rw [← u.ker, hF, (u.ker l).2 hl, hone]
  have hexF : ∀ z, ∀ l ∈ u.Λ, u.ex (F (z + l)) = u.ex (F z) := by
    intro z l hl
    rw [map_add (f := _)]
    exact ex_add_lattice u _ _ (hFl l hl)
  have hdom : ∀ W z, z ∈ dom u m (f ⁻¹ᵁ W) ↔ F z ∈ dom u m W := by
    intro W z
    show ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ W) ↔ ⊤ ≤ ((u.ex (F z)).left ≫ m) ⁻¹ᵁ W
    rw [← hpt z]
    rfl
  have hfn : ∀ W a z, fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) z = fn u m W a (F z) := by
    intro W a z
    show valAt' ((u.ex z).left ≫ m) (f ⁻¹ᵁ W) ((f.app W).hom a) = valAt' ((u.ex (F z)).left ≫ m) W a
    rw [← hpt z, ← Category.assoc, valAt'_comp_lemma ((u.ex z).left ≫ m) f W a]
  have hfd : ∀ W a z, F z ∈ dom u m W → fderiv ℂ (fn u m (f ⁻¹ᵁ W) ((f.app W).hom a)) z =
      (fderiv ℂ (fn u m W a) (F z)).comp (LinearMap.toContinuousLinearMap F) := by
    intro W a z hz
    have e : fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) = fn u m W a ∘ (LinearMap.toContinuousLinearMap F) := by
      funext w
      exact hfn W a w
    rw [e]
    exact ((fn_differentiableAt u m W a (F z) hz).hasFDerivAt.comp z
      (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv

  let d : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ :=
    fun z W a => s (F z) W a - s z (f ⁻¹ᵁ W) ((f.app W).hom a)
  have hd : ∀ z, PtDer ((u.ex (F z)).left ≫ m) (d z) ∧ ∀ r, d z ⊤ (constFn p ⊤ r) = 0 := by
    intro z
    refine ⟨?_, ?_⟩
    · have h1 := ptDer_push _ f (s z) (hKS.der z)
      rw [Category.assoc, hpt z] at h1
      exact ptDer_sub _ _ _ (hKS.der (F z)) h1
    · intro r
      have htop : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ ⊤) := fun x _ => trivial
      show s (F z) ⊤ (constFn p ⊤ r) - s z (f ⁻¹ᵁ ⊤) ((f.app ⊤).hom (constFn p ⊤ r)) = 0
      rw [app_top_constFn p f hfp r, (hKS.der z).res ⊤ (f ⁻¹ᵁ ⊤) le_top htop, hKS.base, hKS.base, sub_self]
  have hdhol : ∀ W a, DifferentiableOn ℂ (fun z => d z W a) {z ∈ Set.univ | F z ∈ dom u m W} := by
    intro W a
    have h1 : DifferentiableOn ℂ (fun z => s (F z) W a) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol W a).comp hFdiff.differentiableOn (fun z hz => hz.2)
    have h2 : DifferentiableOn ℂ (fun z => s z (f ⁻¹ᵁ W) ((f.app W).hom a)) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol (f ⁻¹ᵁ W) ((f.app W).hom a)).mono (fun z hz => (hdom W z).2 hz.2)
    exact h1.sub h2
  obtain ⟨w, hwd, hw⟩ := _root_.GlobalTheory.KS.VertField.exists_differentiableOn_vertical P₀ u Hm χ hU R x₀ X p m hp hpb P₀.g Set.univ F d isOpen_univ hFdiff
    (fun z _ => hd z) hdhol

  have hper : ∀ z, ∀ l ∈ u.Λ,
      w (z + l) = w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))) := by
    intro z l hl
    have hFl' := hFl l hl
    have hpt' : PtDer ((u.ex (F z)).left ≫ m) (d (z + l)) ∧ ∀ r, d (z + l) ⊤ (constFn p ⊤ r) = 0 := by
      rw [← hexF z l hl]
      exact hd (z + l)
    obtain ⟨w0, -, huniq⟩ := _root_.GlobalTheory.KS.VertFamily.existsUnique_vector P₀ u Hm χ hU R x₀ X p m hp hpb (F z) (d (z + l)) hpt'.1 hpt'.2
    refine (huniq _ ?_).trans (huniq _ ?_).symm
    · intro W a hz
      have hz' : F (z + l) ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (F (z + l))).left ≫ m) ⁻¹ᵁ W
        rw [hexF z l hl]
        exact hz
      rw [hw (z + l) (Set.mem_univ _) W a hz', map_add (f := _), fderiv_fn_add_lattice u m W a (F z) (F l) hFl']
    · intro W a hz
      have hzf : z ∈ dom u m (f ⁻¹ᵁ W) := (hdom W z).2 hz
      have e1 := hKS.per ⟨F l, hFl'⟩ W a (F z) hz
      have e2 := hKS.per ⟨l, hl⟩ (f ⁻¹ᵁ W) ((f.app W).hom a) z hzf
      have hd0 := hw z (Set.mem_univ _) W a hz
      show s (F (z + l)) W a - s (z + l) (f ⁻¹ᵁ W) ((f.app W).hom a) = _
      rw [map_add (f := _), e1, e2, hfd W a z hz]
      show _ = fderiv ℂ (fn u m W a) (F z) (w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))))
      rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', map_add (f := _), map_sub, ← hd0]
      ring

  have hc_add : ∀ v v' : Fin P₀.g → ℂ,
      Θ.mulVec (star (F (v + v'))) - F (Θ.mulVec (star (v + v'))) =
        (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) + (Θ.mulVec (star (F v')) - F (Θ.mulVec (star v'))) := by
    intro v v'
    rw [map_add (f := _), star_add, star_add, Matrix.mulVec_add, Matrix.mulVec_add, map_add (f := _)]
    abel
  have hc_smul : ∀ (a : ℂ) (v : Fin P₀.g → ℂ),
      Θ.mulVec (star (F (a • v))) - F (Θ.mulVec (star (a • v))) =
        star a • (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) := by
    intro a v
    rw [map_smul, star_smul, star_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, smul_sub]
  let cA : (Fin P₀.g → ℂ) →+ (Fin P₀.g → ℂ) :=
    AddMonoidHom.mk' (fun v => Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) hc_add
  have hexp : ∀ v : Fin P₀.g → ℂ, Θ.mulVec (star (F v)) - F (Θ.mulVec (star v)) =
      ∑ j, star (v j) • cA (fun k => if j = k then 1 else 0) := by
    intro v
    have h1 : cA v = ∑ j, cA (v j • fun k => if j = k then 1 else 0) := by
      conv_lhs => rw [pi_eq_sum_univ v]
      exact map_sum cA _ _
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact hc_smul (v j) _

  have hwdiff : Differentiable ℂ w := differentiableOn_univ.1 hwd
  have hzero : ∀ i j, cA (fun k => if j = k then 1 else 0) i = 0 := by
    intro i j
    have hperi : ∀ (l : u.Λ) (z : Fin P₀.g → ℂ), w (z + l) i =
        w z i + (fun j => cA (fun k => if j = k then 1 else 0) i) ⬝ᵥ star (l : Fin P₀.g → ℂ) := by
      intro l z
      rw [hper z l l.2, Pi.add_apply, hexp (l : Fin P₀.g → ℂ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hI := _root_.GlobalTheory.entire_antilinear_periods_const P₀.g u.Λ u.discrete u.full (fun z => w z i) _ (differentiable_pi.1 hwdiff i) hperi
    exact congrFun hI.1 j
  intro z
  have hz := hexp z
  have hz0 : Θ.mulVec (star (F z)) - F (Θ.mulVec (star z)) = 0 := by
    rw [hz]
    funext i
    simp [hzero]
  exact (sub_eq_zero.1 hz0).symm

end GlobalTheory.KS.Endo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescends
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LinDescent


open ThetaSplit in
theorem lbPow_descends : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) := by
  intro hlaw k _ _ P n C B _ ψ hn hnk htor hW hψ hfin het hsurj hker
  have := P.isAb.comm
  letI : CommGroup C := { (inferInstance : Group C) with mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }
  have hfinT : Finite {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} := by
    have h := (hlaw.mulN (Sp k) P n hn).2.2.2.2 k (𝟙 _) hnk
    exact Nat.finite_of_card_ne_zero (h.trans_ne (pow_ne_zero _ hn.ne'))
  have : Finite C := Finite.of_injective
    (fun c : C => (⟨c.1, htor c.1 c.2⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1}))
    fun a b h => Subtype.ext (congrArg (fun q => q.1) h)
  obtain ⟨u, hu, hc⟩ := ThetaSplit.exists_cocycle hlaw.globalFns P.isAb P.isLB (ThetaSplit.units_divisible k) n C.subtype
    (fun c c' => hW c.1 c.2 c'.1 c'.2)
  refine exists_descent_of_isReduced (Sp k) P.A B ψ C C.subtype (lbPow P.L n) (DVR.linComb_isLB P.L P.isLB _ _) hψ hfin het hsurj
    (fun k' _ _ t => ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c h => ?_⟩) u hu hc
  · obtain ⟨c, h₁, h₂⟩ := ThetaSplit.exists_rational_ker ψ t x hx
    exact ⟨⟨c, (hker c).1 h₁⟩, h₂⟩
  · rintro ⟨c, rfl⟩
    rw [Category.assoc, (hker (C.subtype c)).2 c.2, MonObj.comp_one]
  · have : Epi t := ThetaSplit.epi_of_fields t
    refine Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 ?_))
    have e : toUnit (Over.mk t) ≫ c.1 = toUnit (Over.mk t) ≫ (1 : 𝟙_ (Over (Sp k)) ⟶ P.A) :=
      h.trans (MonObj.comp_one _).symm
    exact congrArg (fun q => q.left) e

end GlobalTheory.LinDescent
end
end

