module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImAdjointOfSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ConjBound

open GlobalTheory.EigenNorm

variable {g : ℕ}

theorem im_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (t u : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im) (z w : Fin g → ℂ) :
    (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im := by
  have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hr : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v := fun r v => by
    funext i; simp
  induction hz, hw using Submodule.span_induction₂ with
  | mem_mem z w hz hw => exact h z hz w hw
  | zero_left w _ => simp [hermForm]
  | zero_right z _ => simp [hermForm]
  | add_left z z' w _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | add_right z w w' _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
  | smul_left r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1]
  | smul_right r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul,
      Complex.im_ofReal_mul, h1]

theorem hermForm_eq_sum (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z w = ∑ i, ∑ j, z i * Hm i j * starRingEnd ℂ (w j) := by
  simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, _root_.mul_assoc]

theorem entry_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ)
    (h : ∀ z w, (hermForm Hm (t * z) w).im = (hermForm Hm z (star t * w)).im) (i j : Fin g) :
    t i * Hm i j = Hm i j * t j := by
  have key : ∀ s : ℂ, (s * (t i * Hm i j)).im = (s * (Hm i j * t j)).im := fun s => by
    have := h (Pi.single i s) (Pi.single j 1)
    rw [hermForm_eq_sum, hermForm_eq_sum] at this
    simp only [Pi.mul_apply, Pi.single_apply, Pi.star_apply, mul_ite, mul_zero, _root_.mul_one, ite_mul, zero_mul,
      apply_ite (starRingEnd ℂ), map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RCLike.star_def, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have h1 := key 1
  have h2 := key Complex.I
  rw [_root_.one_mul, _root_.one_mul] at h1
  rw [Complex.I_mul_im, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

theorem re_lt_of_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ) (κ : ℝ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hc : ∀ i j, t i * Hm i j = Hm i j * t j) (ht : ∀ i, ‖t i‖ ^ 2 < κ) (y : Fin g → ℂ) (hy : y ≠ 0) :
    (hermForm Hm (t * y) (t * y)).re < κ * (hermForm Hm y y).re := by
  let s : Fin g → ℂ := fun i => (Real.sqrt (κ - ‖t i‖ ^ 2) : ℝ)
  have hs0 : ∀ i, s i ≠ 0 := fun i => by
    have : 0 < Real.sqrt (κ - ‖t i‖ ^ 2) := Real.sqrt_pos.2 (sub_pos.2 (ht i))
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hsy : s * y ≠ 0 := fun h0 => hy (by
    funext i
    have := congrFun h0 i
    simpa [hs0 i] using this)
  have hss : ∀ i, s i * starRingEnd ℂ (s i) + t i * starRingEnd ℂ (t i) = κ := fun i => by
    rw [Complex.mul_conj', Complex.mul_conj']
    have : ‖s i‖ ^ 2 = κ - ‖t i‖ ^ 2 := by
      simp only [s, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (sub_pos.2 (ht i)).le
    rw [← Complex.ofReal_pow, this]
    push_cast; ring
  have hsum : hermForm Hm (s * y) (s * y) + hermForm Hm (t * y) (t * y) = κ * hermForm Hm y y := by
    simp only [hermForm_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : Hm i j = 0
    · simp [h0]
    · have hij : t i = t j := by
        have := hc i j
        rw [mul_comm] at this
        exact mul_left_cancel₀ h0 this
      have hsij : s i = s j := by simp only [s, hij]
      simp only [Pi.mul_apply, map_mul, hij, hsij, ← hss j]
      ring
  have h1 := hpos _ hsy
  have h2 := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.re_ofReal_mul] at h2
  linarith

theorem exists_action_lt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Q : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 E) (κ : ℕ), (∀ (c : 𝓞 E) x i, Q (c • x) i = ty i (c : E) * Q x i) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D.EF x y) → (∀ τ : E →+* ℂ, ‖τ (a : E)‖ ^ 2 < κ) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (a • x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro E _ _ _ H D g ty Q Hm a κ hlin ⟨_, _, hspan, _, hpos, him⟩ hκ
  let t : Fin g → ℂ := fun i => ty i (a : E)
  have h1 : ∀ x, t * Q x = Q (a • x) := fun x => funext fun i => (hlin a x i).symm
  have h2 : ∀ x, star t * Q x = Q (H.bar a • x) := fun x => funext fun i => by
    rw [hlin, H.bar_eq, IsCMField.complexEmbedding_complexConj]; rfl
  refine ⟨LinearMap.mulLeft ℂ t, h1, fun y hy => ?_⟩
  refine re_lt_of_comm Hm t κ hpos (entry_comm Hm t (im_adjoint_of_span Hm t (star t) _ hspan ?_))
    (fun i => hκ (ty i)) y hy
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
  rw [h1, h2, him, him, D.adj]

end GlobalTheory.ConjBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.isDominant_pullback_fst_of_isOpenMap {X U Y : Scheme.{0}} (j : U ⟶ X) [IsDominant j]
    (p : Y ⟶ X) (hp : IsOpenMap p) : IsDominant (pullback.fst p j) := by
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_fst]
  exact j.denseRange.preimage hp


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.eq_of_specializes_of_mem_genericPoints {T : Type*} [TopologicalSpace T] [T0Space T]
    {x y : T} (hx : x ∈ genericPoints T) (h : y ⤳ x) : y = x := by
  have h1 : closure ({y} : Set T) ⊆ closure {x} :=
    hx.2 isIrreducible_singleton.closure h.closure_subset
  exact (h.antisymm (specializes_iff_closure_subset.2 h1)).eq


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.genericPoints_subset_range_of_isDominant {X U : Scheme.{0}} (j : U ⟶ X) [IsDominant j]
    [QuasiCompact j] : genericPoints X ⊆ Set.range j := by
  intro ξ hξ
  obtain ⟨V, hV, hξV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show ξ ∈ (⊤ : X.Opens) from trivial)
  replace hV : IsAffineOpen V := hV
  have hc : IsCompact (j ⁻¹' (V : Set X)) :=
    QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact
  obtain ⟨s, hs, hW⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hc, V.isOpen.preimage j.continuous⟩
  have hcl : ξ ∈ closure (j '' (j ⁻¹' (V : Set X))) := by
    rw [Set.image_preimage_eq_inter_range]
    exact j.denseRange.open_subset_closure_inter V.isOpen hξV
  rw [hW, Set.image_iUnion₂, hs.closure_biUnion, Set.mem_iUnion₂] at hcl
  obtain ⟨W, hWs, hξW⟩ := hcl
  have hWV : (W : Set U) ⊆ j ⁻¹' (V : Set X) := by
    rw [hW]
    exact Set.subset_biUnion_of_mem (u := fun i : U.affineOpens => ((i : U.Opens) : Set U)) hWs
  have hWa : IsAffineOpen (W : U.Opens) := W.2
  set g := hWa.fromSpec ≫ j with hg
  have hrg : Set.range g = j '' (W : Set U) := by
    rw [hg, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hWa.range_fromSpec]
  have hsub : Set.range g ⊆ Set.range hV.fromSpec := by
    rw [hrg, hV.range_fromSpec]
    rintro _ ⟨x, hx, rfl⟩
    exact hWV hx
  set k := IsOpenImmersion.lift hV.fromSpec g hsub with hk
  have hkg : k ≫ hV.fromSpec = g := IsOpenImmersion.lift_fac _ _ _
  set φ := Spec.preimage k
  have hφ : Spec.map φ = k := Spec.map_preimage k
  obtain ⟨p, hp⟩ : ξ ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hξV
  have hinj : Function.Injective hV.fromSpec := hV.fromSpec.isOpenEmbedding.injective
  have hpcl₀ : p ∈ closure (Set.range (Spec.map φ)) := by
    rw [hV.fromSpec.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.mem_preimage, hp]
    convert hξW using 2
    rw [← hrg, ← hkg, ← hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hpcl₁ : (p : PrimeSpectrum Γ(X, V)) ∈ closure (Set.range (PrimeSpectrum.comap φ.hom)) :=
    hpcl₀
  rw [PrimeSpectrum.closure_range_comap] at hpcl₁
  have hpcl : RingHom.ker φ.hom ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hpcl₁
  have hmin : p.asIdeal ∈ (Ideal.comap φ.hom ⊥).minimalPrimes := by
    rw [← RingHom.ker_eq_comap_bot]
    refine ⟨⟨p.2, hpcl⟩, fun q hq hqp => ?_⟩
    have hspec : (⟨q, hq.1⟩ : PrimeSpectrum _) ⤳ p :=
      (PrimeSpectrum.le_iff_specializes _ _).1 hqp
    have heq := _root_.GlobalTheory.eq_of_specializes_of_mem_genericPoints (hp ▸ hξ)
      (hspec.map hV.fromSpec.continuous)
    have heq' := hinj heq
    rw [← heq']
  obtain ⟨q, hq, -, hqp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes φ.hom _ hmin
  refine ⟨hWa.fromSpec ⟨q, hq⟩, ?_⟩
  rw [← hp]
  change g ⟨q, hq⟩ = _
  have hgq : g ⟨q, hq⟩ = hV.fromSpec (Spec.map φ ⟨q, hq⟩) := by rw [← hkg, ← hφ]; rfl
  rw [hgq]
  congr 1
  exact PrimeSpectrum.ext hqp


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks {X U : Scheme.{0}} (j : U ⟶ X) [Flat j]
    [SurjectiveOnStalks j] (u : U) : IsIso (j.stalkMap u) := by
  have hs := j.stalkMap_surjective u
  letI := (j.stalkMap u).hom.toAlgebra
  haveI : Module.Flat _ _ := Flat.stalkMap j u
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (j u)) (U.presheaf.stalk u)) :=
    inferInstanceAs (IsLocalHom (j.stalkMap u).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (j u)) (B := U.presheaf.stalk u)
  have hi : Function.Injective (j.stalkMap u).hom :=
    FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j u)) (U.presheaf.stalk u)
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hi, hs⟩


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.densePart_basic : ∀ (X U : Scheme.{0}) (j : U ⟶ X), IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → genericPoints X ⊆ Set.range j ∧ (∀ u : U, IsIso (j.stalkMap u)) ∧ (IsReduced X → IsSchemeTheoreticallyDominant j) ∧ ∀ (Y : Scheme.{0}) (p : Y ⟶ X), UniversallyOpen p → IsDominant (pullback.fst p j) := by
  intro X U j _ _ _ _
  refine ⟨_root_.GlobalTheory.genericPoints_subset_range_of_isDominant j,
    fun u => _root_.GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks j u,
    fun _ => (isSchemeTheoreticallyDominant_iff_isDominant j).2 inferInstance,
    fun Y p _ => _root_.GlobalTheory.isDominant_pullback_fst_of_isOpenMap j p p.isOpenMap⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenPosDefOfContinuous
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isOpen_posDef_of_continuous {X n : Type} [TopologicalSpace X] [Fintype n]
    (M : X → Matrix n n ℝ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : n → ℝ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (n → ℝ) => dotProduct (star p.2) ((M p.1).mulVec p.2)) :=
    (continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd)
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1,
      0 < dotProduct (star v) ((M x).mulVec v) := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 ⊢
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  exact (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)

theorem card_sym2_fin (h : ℕ) : Fintype.card (Sym2 (Fin h)) = h * (h + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

theorem exists_siegel_coordinates :
    ∀ h : ℕ, ∃ (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ), IsOpen B ∧ Convex ℝ B ∧ (∀ i j, Differentiable ℂ (fun b => τ b i j)) ∧ (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) ∧ ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm → (t.map Complex.im).PosDef → ∃! b, b ∈ B ∧ τ b = t := by
  intro h
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (card_sym2_fin h)
  let τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ :=
    fun b => Matrix.of fun i j => b (e s(i, j))
  have hτ : ∀ b i j, τ b i j = b (e s(i, j)) := fun _ _ _ => rfl
  have hsymm : ∀ b, (τ b).IsSymm := by
    intro b
    ext i j
    rw [Matrix.transpose_apply, hτ, hτ, Sym2.eq_swap]
  refine ⟨{b | ((τ b).map Complex.im).PosDef}, τ, ?_, ?_, ?_, ?_, ?_⟩
  · apply isOpen_posDef_of_continuous (fun b => (τ b).map Complex.im)
    · refine continuous_matrix fun i j => ?_
      exact Complex.continuous_im.comp (continuous_apply (e s(i, j)))
    · intro b
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.map_apply, hτ]
      rw [Sym2.eq_swap]
  · intro x hx y hy a b ha hb hab
    have key : (τ (a • x + b • y)).map Complex.im
        = a • (τ x).map Complex.im + b • (τ y).map Complex.im := by
      ext i j
      simp [hτ]
    change ((τ (a • x + b • y)).map Complex.im).PosDef
    rw [key]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by simpa using hab
      subst this
      simpa using hy
    · exact (Matrix.PosDef.smul hx ha').add_posSemidef
        (Matrix.PosSemidef.smul (Matrix.PosDef.posSemidef hy) hb)
  · intro i j
    exact differentiable_apply (𝕜 := ℂ) (e s(i, j))
  · intro b hb
    exact ⟨hsymm b, hb⟩
  · intro t ht hp
    let f : Sym2 (Fin h) → ℂ := Sym2.lift ⟨fun i j => t i j, fun i j => (ht.apply i j).symm⟩
    have hf : τ (fun k => f (e.symm k)) = t := by
      ext i j
      change f (e.symm (e s(i, j))) = t i j
      rw [Equiv.symm_apply_apply]
      rfl
    refine ⟨fun k => f (e.symm k), ⟨?_, hf⟩, ?_⟩
    · change ((τ (fun k => f (e.symm k))).map Complex.im).PosDef
      rw [hf]; exact hp
    · rintro b ⟨-, hb⟩
      funext k
      obtain ⟨z, rfl⟩ := e.surjective k
      induction z using Sym2.ind with
      | _ i j =>
        rw [Equiv.symm_apply_apply]
        exact congrFun (congrFun hb i) j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KerConeMemMinimalPrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace HomogMinPrime

open MvPolynomial

theorem eval_scale {o σ A : Type} [CommRing o] [CommRing A] (f : o →+* A) (g : σ → A) (c : A)
    {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    eval₂Hom f (fun a => g a * c) F = c ^ e * eval₂Hom f g F := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [F.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = e := by
    by_contra h
    exact (mem_support_iff.mp hd) (hF.coeff_eq_zero h)
  rw [eval₂Hom_monomial, eval₂Hom_monomial, ← hdeg]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply]
  ring

theorem eval_cone {o σ K : Type} [CommRing o] [Field K] (β : o →+* K) (u : σ → K)
    {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X) F
      = Polynomial.monomial e (eval₂Hom β u F) := by
  rw [eval_scale _ (fun a => Polynomial.C (u a)) Polynomial.X hF,
    ← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
  congr 1
  exact (map_eval₂Hom β u (Polynomial.C : K →+* Polynomial K) F).symm

theorem mem_ker_cone {o σ K : Type} [CommRing o] [Field K] (β : o →+* K) (u : σ → K)
    (F : MvPolynomial σ o) :
    F ∈ RingHom.ker (eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X)) ↔
      ∀ e, eval₂Hom β u (homogeneousComponent e F) = 0 := by
  rw [RingHom.mem_ker]
  have h : eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X) F =
      ∑ e ∈ Finset.range (F.totalDegree + 1),
        Polynomial.monomial e (eval₂Hom β u (homogeneousComponent e F)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← sum_homogeneousComponent F, map_sum]
    exact Finset.sum_congr rfl fun e _ => eval_cone β u (homogeneousComponent_isHomogeneous e F)
  rw [h]
  constructor
  · intro h0 e
    by_cases he : e ∈ Finset.range (F.totalDegree + 1)
    · have := congrArg (fun p : Polynomial K => p.coeff e) h0
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Polynomial.coeff_zero,
        Finset.sum_ite_eq', he, ite_true] at this
      exact this
    · rw [homogeneousComponent_eq_zero, map_zero]
      rw [Finset.mem_range] at he
      omega
  · intro h0
    exact Finset.sum_eq_zero fun e _ => by rw [h0, map_zero]

end HomogMinPrime


open HomogMinPrime in
theorem ker_cone_mem_minimalPrimes : ∀ (o σ K : Type) [CommRing o] [Field K] (I : Ideal (MvPolynomial σ o)) (β : o →+* K) (u : σ → K) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → u i = 1 → RingHom.ker (MvPolynomial.eval₂Hom β u) ∈ (I ⊔ Ideal.span {MvPolynomial.X i - 1}).minimalPrimes → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) ∈ I.minimalPrimes := by
  intro o σ K _ _ I β u i hI hu hmin
  have hIφ : I ≤ RingHom.ker (MvPolynomial.eval₂Hom β u) := le_sup_left.trans hmin.1.2
  refine ⟨⟨RingHom.ker_isPrime _, fun F hF => (mem_ker_cone β u F).2 fun e => hIφ (hI F hF e)⟩, ?_⟩
  rintro Q ⟨hQ, hIQ⟩ hQψ
  have hQφ : ∀ F ∈ Q, MvPolynomial.eval₂Hom β u F = 0 := by
    intro F hF
    have := (mem_ker_cone β u F).1 (hQψ hF)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
    exact Finset.sum_eq_zero fun e _ => this e
  let L := FractionRing (MvPolynomial σ o ⧸ Q)
  let π : MvPolynomial σ o →+* L := (algebraMap (MvPolynomial σ o ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ F, π F = 0 ↔ F ∈ Q := by
    intro F
    simp only [π, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hx : π (MvPolynomial.X i) ≠ 0 := by
    intro h
    have := hQφ _ ((hπ _).1 h)
    rw [MvPolynomial.eval₂Hom_X', hu] at this
    exact one_ne_zero this
  let χ : MvPolynomial σ o →+* L := MvPolynomial.eval₂Hom (π.comp MvPolynomial.C)
    (fun a => π (MvPolynomial.X a) * (π (MvPolynomial.X i))⁻¹)
  have hπe : MvPolynomial.eval₂Hom (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) = π := by
    apply MvPolynomial.ringHom_ext <;> simp
  have hχ : ∀ (F : MvPolynomial σ o) e, χ (MvPolynomial.homogeneousComponent e F) =
      (π (MvPolynomial.X i))⁻¹ ^ e * π (MvPolynomial.homogeneousComponent e F) := by
    intro F e
    have := eval_scale (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a))
      (π (MvPolynomial.X i))⁻¹ (MvPolynomial.homogeneousComponent_isHomogeneous e F)
    rw [hπe] at this
    exact this
  have h1 : I ⊔ Ideal.span {MvPolynomial.X i - 1} ≤ RingHom.ker χ := by
    refine sup_le (fun F hF => ?_) ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [hχ, (hπ _).2 (hIQ (hI F hF e)), mul_zero]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]
      simp only [χ, MvPolynomial.eval₂Hom_X']
      rw [mul_inv_cancel₀ hx, sub_self]
  have h2 : RingHom.ker χ ≤ RingHom.ker (MvPolynomial.eval₂Hom β u) := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    have hG : (∑ e ∈ Finset.range (F.totalDegree + 1),
        MvPolynomial.X i ^ (F.totalDegree - e) * MvPolynomial.homogeneousComponent e F) ∈ Q := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hπ, map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← MvPolynomial.sum_homogeneousComponent F, map_sum] at hF
      have := congrArg (fun y => π (MvPolynomial.X i) ^ F.totalDegree * y) hF
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun e he => ?_
      have he' : e ≤ F.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
      rw [hχ, map_mul, map_pow, pow_sub₀ _ hx he', inv_pow, _root_.mul_assoc]
    have := hQφ _ hG
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPolynomial.sum_homogeneousComponent F, map_sum, ← this]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, map_pow, MvPolynomial.eval₂Hom_X', hu, one_pow, _root_.one_mul]
  have h3 := hmin.2 ⟨RingHom.ker_isPrime χ, h1⟩ h2
  intro F hF
  rw [mem_ker_cone] at hF
  rw [← MvPolynomial.sum_homogeneousComponent F]
  refine Q.sum_mem fun e _ => ?_
  have h4 : χ (MvPolynomial.homogeneousComponent e F) = 0 := h3 (hF e)
  rw [hχ] at h4
  exact (hπ _).1 ((mul_eq_zero.1 h4).resolve_left (pow_ne_zero _ (inv_ne_zero hx)))

end GlobalTheory
end

