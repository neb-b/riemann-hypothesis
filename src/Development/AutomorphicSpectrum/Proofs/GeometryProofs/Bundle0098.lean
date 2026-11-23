module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLift
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.LieTangent

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem centre_field_base {K K' : Type} [Field K] [Field K'] {X : Scheme.{0}} (φ : K →+* K')
    (z : Sp K ⟶ X) : centre (Spec.map (CommRingCat.ofHom φ) ≫ z) = centre z := by
  have : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K') = IsLocalRing.closedPoint K :=
    Subsingleton.elim _ _
  change (Spec.map (CommRingCat.ofHom φ) ≫ z) _ = z _
  rw [Scheme.Hom.comp_apply, this]

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_generise (M : LieModel G ξ E) (p : Cpt ξ) {y : X} (hy : genPt ξ ⤳ y) (c : y ⤳ p.1) {e : E}
    {v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G} (h : M.Extends p e v) :
    M.Extends ⟨y, hy⟩ e (epsBase (R := X.presheaf.stalk p.1) (R' := X.presheaf.stalk y)
      (X.presheaf.stalkSpecializes c).hom (Scheme.SpecMap_stalkSpecializes_fromSpecStalk c) ≫ v) := by
  rw [LieModel.extends_iff] at *
  refine ⟨isTanAt_base _ _ h.1, ?_⟩
  rw [h.2, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, ← dualMap_comp]
  congr 3
  exact RingHom.ext fun s => (genMap_specializes p hy c s).symm

theorem valAt_lie_base {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    (M : LieModel G ξ E) {z : Sp R ⟶ X} {z' : Sp R' ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ z = z')
    (hg : genPt ξ ⤳ centre z') {e : E} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z' e (epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨hg, _, extends_generise M ⟨centre z, h1⟩ hg (centre_specializes φ z) hv, ?_⟩
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, spec_comp, ← dualMap_comp, ← dualMap_comp]
  congr 3
  exact congrArg (fun g => g.hom) (stalk_base φ z).symm

end

theorem pull_lie_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc] (MB : LieModel G z Bc) (x : Bc) (e : Li)
    (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
    M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
    ∃ v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G, M.ValAt _ e v' ∧
      (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left) := by
  intro X Ω _ ξ G _ Li _ _ M L _ _ z σ Bc _ _ MB x e v hv hl
  have hz : Spec.map (CommRingCat.ofHom σ) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) =
      spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc, spec_comp]
  have hg : genPt ξ ⤳ centre (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) := by
    obtain ⟨h1, -⟩ := hv
    rw [← hz, centre_field_base]
    exact h1
  refine ⟨epsBase σ hz ≫ v, valAt_lie_base σ M hz hg hv, ?_⟩
  unfold LieModel.Lifts at *
  change (Spec.map _ ≫ v.left) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rw [Category.comp_id] at hl
  rw [hl, ← Category.assoc, spec_comp, ← dualMap_comp]

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRatioProductFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum

variable {L : Type} [Field L] [NumberField L]

theorem finsum_log_add_sum_log {x : L} (hx : x ≠ 0) :
    ∑ᶠ v : FinitePlace L, Real.log (v x) + ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = 0 := by
  have hmul : (Function.mulSupport fun v : FinitePlace L => v x).Finite :=
    FinitePlace.hasFiniteMulSupport hx
  have h1 : ∑ᶠ v : FinitePlace L, Real.log (v x) = Real.log (∏ᶠ v : FinitePlace L, v x) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun v _ => (FinitePlace.pos_iff.2 hx).ne')]
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hv
    simp [h1]
  have h2 : ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    classical
    rw [← Real.log_prod fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx), ← norm_prod]
    have h3 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
    have h4 : ∏ σ : L →+* ℂ, σ x = ∏ σ : L →ₐ[ℚ] ℂ, σ x :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ fun σ => (DFunLike.congr rfl rfl)
    rw [h4, ← h3, eq_ratCast, Complex.norm_ratCast]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hx]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem support_log_finite {x : L} (hx : x ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (v x)).Finite := by
  refine (show (Function.mulSupport fun v : FinitePlace L => v x).Finite from
    FinitePlace.hasFiniteMulSupport hx).subset fun v hv h => hv ?_
  simp [show v x = 1 from h]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def badPlaces (w : (Σ k, J k) → L) : Set (FinitePlace L) :=
  ⋃ p : Σ k, J k, {v | w p ≠ 0 ∧ v (w p) ≠ 1}

theorem badPlaces_finite (w : (Σ k, J k) → L) : (badPlaces w).Finite := by
  refine Set.finite_iUnion fun p => ?_
  by_cases hp : w p = 0
  · exact Set.finite_empty.subset fun v hv => hv.1 hp
  · refine (show (Function.mulSupport fun v : FinitePlace L => v (w p)).Finite from
      FinitePlace.hasFiniteMulSupport hp).subset fun v hv => hv.2

theorem eq_one_of_notMem {w : (Σ k, J k) → L} {v : FinitePlace L} (hv : v ∉ badPlaces w)
    {p : Σ k, J k} (hp : w p ≠ 0) : v (w p) = 1 := by
  by_contra h
  exact hv (Set.mem_iUnion.2 ⟨p, hp, h⟩)

theorem le_iSup_place (w : (Σ k, J k) → L) (v : FinitePlace L) (k : K) (c : J k) :
    v (w ⟨k, c⟩) ≤ ⨆ i, v (w ⟨k, i⟩) :=
  le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove c

theorem iSup_place_pos {w : (Σ k, J k) → L} (v : FinitePlace L) {k : K} (h : ∃ c, w ⟨k, c⟩ ≠ 0) :
    0 < ⨆ i, v (w ⟨k, i⟩) := by
  obtain ⟨c, hc⟩ := h
  exact (FinitePlace.pos_iff.2 hc).trans_le (le_iSup_place w v k c)

theorem iSup_place_eq_one {w : (Σ k, J k) → L} {v : FinitePlace L} (hv : v ∉ badPlaces w) {k : K}
    (h : ∃ c, w ⟨k, c⟩ ≠ 0) : ⨆ i, v (w ⟨k, i⟩) = 1 := by
  obtain ⟨c, hc⟩ := h
  haveI : Nonempty (J k) := ⟨c⟩
  refine le_antisymm (ciSup_le fun i => ?_) ?_
  · by_cases hi : w ⟨k, i⟩ = 0
    · rw [hi, map_zero]; exact zero_le_one
    · exact (eq_one_of_notMem hv hi).le
  · rw [← eq_one_of_notMem hv hc]
    exact le_iSup_place w v k c

theorem log_locRatio (a : K → ℤ) {w : (Σ k, J k) → L} (c₀ : (k : K) → J k)
    (h : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) (h₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) (v : FinitePlace L) :
    Real.log (locRatio a w c₀ v) =
      (∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) -
        ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩)) := by
  unfold locRatio
  rw [Real.log_prod fun k _ => zpow_ne_zero _
    (div_ne_zero (iSup_place_pos v (h k)).ne' (FinitePlace.pos_iff.2 (h₀ k)).ne'),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.log_zpow, Real.log_div (iSup_place_pos v (h k)).ne' (FinitePlace.pos_iff.2 (h₀ k)).ne',
    mul_sub]

theorem ratio_sum (L : Type) [Field L] [NumberField L] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (a : K → ℤ) (w : (Σ k, J k) → L) (c₀ : (k : K) → J k) (u : L) :
    (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → u ≠ 0 →
    (∀ v, 0 < locRatio a w c₀ v) ∧ (Function.mulSupport (locRatio a w c₀)).Finite ∧
    ∑ᶠ v : FinitePlace L, (Real.log (locRatio a w c₀ v) - Real.log (v u)) =
      (∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        ∑ σ : L →+* ℂ, (Real.log ‖σ u‖ + ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖) := by
  intro h h₀ hu
  refine ⟨fun v => ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun k _ => zpow_pos
      (div_pos (iSup_place_pos v (h k)) (FinitePlace.pos_iff.2 (h₀ k))) _
  · refine (badPlaces_finite w).subset fun v hv => ?_
    by_contra hb
    apply hv
    unfold locRatio
    refine Finset.prod_eq_one fun k _ => ?_
    rw [iSup_place_eq_one hb (h k), eq_one_of_notMem hb (h₀ k)]
    simp
  · have hS : (Function.support fun v : FinitePlace L =>
        ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))).Finite := by
      refine (badPlaces_finite w).subset fun v hv => ?_
      by_contra hb
      apply hv
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [iSup_place_eq_one hb (h k), Real.log_one, mul_zero]
    have hT1 : ∀ k, (Function.support fun v : FinitePlace L =>
        (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))).Finite := fun k =>
      (support_log_finite (h₀ k)).subset fun v hv hz => hv (by simp [show Real.log (v (w ⟨k, c₀ k⟩)) = 0 from hz])
    have hT : (Function.support fun v : FinitePlace L =>
        ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))).Finite := by
      refine (Set.finite_iUnion hT1).subset fun v hv => ?_
      by_contra hb
      apply hv
      refine Finset.sum_eq_zero fun k _ => ?_
      by_contra hk
      exact hb (Set.mem_iUnion.2 ⟨k, hk⟩)
    have hTsum : ∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩)) =
        -∑ k, (a k : ℝ) * ∑ σ : L →+* ℂ, Real.log ‖σ (w ⟨k, c₀ k⟩)‖ := by
      rw [finsum_sum_comm _ _ fun k _ => hT1 k, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_finsum,
        eq_neg_of_add_eq_zero_left (finsum_log_add_sum_log (h₀ k)), mul_neg]
    have hu' := eq_neg_of_add_eq_zero_left (finsum_log_add_sum_log hu)
    simp_rw [log_locRatio a c₀ h h₀]
    have hST := (hS.union hT).subset (Function.support_sub
      (fun v : FinitePlace L => ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)))
      (fun v : FinitePlace L => ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))))
    have hcomm : ∑ σ : L →+* ℂ, ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖ =
        ∑ k, (a k : ℝ) * ∑ σ : L →+* ℂ, Real.log ‖σ (w ⟨k, c₀ k⟩)‖ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    rw [finsum_sub_distrib hST (support_log_finite hu), finsum_sub_distrib hS hT, hTsum, hu',
      Finset.sum_add_distrib, hcomm]
    ring

end GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {σ : Type} [Fintype σ]

theorem aeval_scale {R : Type} [CommRing R] {F : MvPolynomial σ ℤ} {n : ℕ} (hF : F.IsHomogeneous n) (c : R)
    (x : σ → R) : MvPolynomial.aeval (fun j => c * x j) F = c ^ n * MvPolynomial.aeval x F := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ j, m j = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem aeval_map_hom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : σ → A) (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun j => f (t j)) F = f (MvPolynomial.aeval t F) :=
  by simpa using (MvPolynomial.comp_aeval_apply (f := t) f.toIntAlgHom F).symm

variable {Ω : Type} [Field Ω]

def IsFormQuot (x : σ → Ω) (i : σ) (b : Ω) : Prop :=
  ∃ (N n : ℕ) (G : MvPolynomial σ ℤ), N ≠ 0 ∧ G.IsHomogeneous n ∧
    MvPolynomial.aeval x G = (N : Ω) * x i ^ n * b

theorem isFormQuot_of_mem [CharZero Ω] {x : σ → Ω} {i : σ} (hi : x i ≠ 0) {b : Ω}
    (hb : b ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i)) : IsFormQuot x i b := by
  induction hb using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    refine ⟨1, 1, MvPolynomial.X j, one_ne_zero, MvPolynomial.isHomogeneous_X _ _, ?_⟩
    simp only [MvPolynomial.aeval_X, Nat.cast_one, one_mul, pow_one]
    field_simp
  | algebraMap r =>
    refine ⟨r.den, 0, MvPolynomial.C r.num, r.den_nz, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    simp only [MvPolynomial.aeval_C, pow_zero, mul_one, eq_ratCast, eq_intCast, Rat.cast_def, map_intCast]
    field_simp
  | add a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', MvPolynomial.C (N' : ℤ) * MvPolynomial.X i ^ n' * G +
      MvPolynomial.C (N : ℤ) * MvPolynomial.X i ^ n * G', mul_ne_zero hN hN', ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n')).mul hG using 1
        omega
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n)).mul hG' using 1
        omega
    · simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, he', eq_intCast,
        Int.cast_natCast, Nat.cast_mul, map_natCast]
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', G * G', mul_ne_zero hN hN', hG.mul hG', ?_⟩
    simp only [map_mul, he, he', Nat.cast_mul]
    ring

theorem common_denominator {κ : Type} [Fintype κ] {x : σ → Ω} {i : σ} {b : κ → Ω}
    (h : ∀ j, IsFormQuot x i (b j)) :
    ∃ (N n : ℕ) (F : κ → MvPolynomial σ ℤ), N ≠ 0 ∧ (∀ j, (F j).IsHomogeneous n) ∧
      ∀ j, MvPolynomial.aeval x (F j) = (N : Ω) * x i ^ n * b j := by
  classical
  choose N n G hN hG he using h
  refine ⟨∏ j, N j, ∑ j, n j, fun j => MvPolynomial.C ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : ℤ) *
    MvPolynomial.X i ^ (∑ l, n l - n j) * G j, Finset.prod_ne_zero_iff.2 fun j _ => hN j, fun j => ?_, fun j => ?_⟩
  all_goals have hle : n j ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  · convert ((MvPolynomial.isHomogeneous_C _ _).mul
      ((MvPolynomial.isHomogeneous_X _ i).pow (∑ l, n l - n j))).mul (hG j) using 1
    omega
  · have hp : x i ^ (∑ l, n l) = x i ^ (∑ l, n l - n j) * x i ^ n j := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hq : ((∏ l, N l : ℕ) : Ω) = (N j : Ω) * ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : Ω) := by
      rw [← Nat.cast_mul, Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j)]
    simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, eq_intCast, Int.cast_natCast,
      map_natCast]
    rw [hp, hq]
    ring

theorem aeval_ne_zero_of_unit {L S : Type} [Field L] [CharZero L] [CommRing S] (g : S →+* Ω)
    (hg : Function.Injective g) (φ : S →+* L) {x : σ → Ω} {w : σ → L} {i : σ} (hx : x i ≠ 0) (hw : w i ≠ 0)
    (t : σ → S) (ht : ∀ j, g (t j) = x j / x i) (ht' : ∀ j, φ (t j) * w i = w j)
    {F : MvPolynomial σ ℤ} {n N : ℕ} (hN : N ≠ 0) (hF : F.IsHomogeneous n) {e : S} (he : IsUnit e)
    (hFe : MvPolynomial.aeval x F = (N : Ω) * x i ^ n * g e) : MvPolynomial.aeval w F ≠ 0 := by
  have h1 : x = fun j => x i * g (t j) := funext fun j => by rw [ht, mul_div_cancel₀ _ hx]
  have h2 : MvPolynomial.aeval x F = x i ^ n * g (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h1]
    rw [aeval_scale hF, aeval_map_hom]
  have h3 : MvPolynomial.aeval t F = (N : S) * e := by
    apply hg
    apply mul_left_cancel₀ (pow_ne_zero n hx)
    rw [← h2, hFe, map_mul, map_natCast]
    ring
  have h4 : w = fun j => w i * φ (t j) := funext fun j => by rw [← ht', mul_comm]
  have h5 : MvPolynomial.aeval w F = w i ^ n * φ (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h4]
    rw [aeval_scale hF, aeval_map_hom]
  rw [h5, h3, map_mul, map_natCast]
  exact mul_ne_zero (pow_ne_zero _ hw) (mul_ne_zero (Nat.cast_ne_zero.2 hN) (he.map φ).ne_zero)

end Forms

section Germs

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_unit_germ {p : Cpt ξ} (hinj : Function.Injective (genMap ξ p)) {s : Ω} (h : unitAt ξ p s) :
    ∃ e : X.presheaf.stalk p.1, IsUnit e ∧ genMap ξ p e = s := by
  obtain ⟨h0, ⟨e, rfl⟩, ⟨e', he'⟩⟩ := h
  refine ⟨e, IsUnit.of_mul_eq_one e' (hinj ?_), rfl⟩
  rw [map_mul, he', mul_inv_cancel₀ h0, map_one]

theorem unitAt_natCast [CharZero Ω] {L : Type} [Field L] [CharZero L] {zz : Spec (CommRingCat.of L) ⟶ X}
    (h : genPt ξ ⤳ centre zz) {r : ℕ} (hr : r ≠ 0) : unitAt ξ ⟨centre zz, h⟩ (r : Ω) := by
  have hu : IsUnit ((r : X.presheaf.stalk (centre zz))) := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo zz).hom).map_nonunit _ (IsUnit.mk0 _
      ((map_natCast (Scheme.stalkClosedPointTo zz).hom r).trans_ne ((Nat.cast_ne_zero (R := L)).2 hr)))
  obtain ⟨u, hu⟩ := hu
  have hv : genMap ξ ⟨centre zz, h⟩ (u : X.presheaf.stalk (centre zz)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine ⟨Nat.cast_ne_zero.2 hr, ⟨_, hv⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre zz))ˣ) : _), ?_⟩⟩
  rw [← hv]
  exact map_units_inv _ u

end Germs

theorem ratios_quotients_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∀ (i : J k₀) (k : K) (c : J k), z ⟨k₀, i⟩ ≠ 0 → z ⟨k, c⟩ ≠ 0 → ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ), (∀ j, (F j).IsHomogeneous n) ∧ (∀ j, MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F c) * y ⟨k, j⟩) ∧ MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F c) ≠ 0 := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE L _ _ z hz i k c hzi hzc
  classical
  obtain ⟨hblk, hvan⟩ := hz
  obtain ⟨zz, ⟨hsp, hco⟩, -⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.tie_points X Ω ξ K J y hT L).1 z
    (fun k' => (hblk k').imp fun _ h => IsUnit.mk0 _ h) hvan
  let p : Cpt ξ := ⟨centre zz, hsp⟩
  have hinj : Function.Injective (genMap ξ p) := hT.gen.inj p
  have hfib : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := fun r hr hn => hn (unitAt_natCast hsp hr.ne_zero)
  obtain ⟨hyi, hrat⟩ := hco.2 k₀ i (IsUnit.mk0 _ hzi)
  obtain ⟨hyc, hrat'⟩ := hco.2 k c (IsUnit.mk0 _ hzc)
  have hgerm : ∀ i' : J k₀, ∃ t : X.presheaf.stalk (centre zz),
      genMap ξ p t = y ⟨k₀, i'⟩ / y ⟨k₀, i⟩ ∧ (Scheme.stalkClosedPointTo zz).hom t * z ⟨k₀, i⟩ = z ⟨k₀, i'⟩ := by
    intro i'
    obtain ⟨r, ⟨_, t, h1, h2⟩, h3⟩ := hrat i'
    exact ⟨t, h1, by rw [h2, h3]⟩
  choose t ht ht' using hgerm
  have hchart : InChart ξ (fun i' : J k₀ => y ⟨k₀, i'⟩) i p := ⟨hyi, fun i' => ⟨t i', ht i'⟩⟩
  have hreg : ∀ j, y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ p := by
    intro j
    obtain ⟨r, ⟨_, u, h1, _⟩, _⟩ := hrat' j
    exact ⟨u, h1⟩
  choose s hsB hsU hsa using fun j => ((hE p hfib).2 i hchart).1 _ (hreg j)
  have hSU : unitAt ξ p (∏ j, s j) := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => (hsU j).1, Subring.prod_mem _ fun j _ => (hsU j).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact Subring.prod_mem _ fun j _ => (hsU j).2.2
  have hSa : ∀ j, (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩) ∈
      Algebra.adjoin ℚ (Set.range fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩) := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j), mul_right_comm]
    exact Subalgebra.mul_mem _ (hsa j) (Subalgebra.prod_mem _ fun l _ => hsB l)
  obtain ⟨N, n, F, hN, hF, he⟩ := common_denominator (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i)
    (b := fun j => (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩)) fun j =>
      isFormQuot_of_mem (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i) hyi (hSa j)
  obtain ⟨e, heu, hee⟩ := exists_unit_germ hinj hSU
  refine ⟨n, F, hF, fun j => ?_, ?_⟩
  · rw [he j, he c, div_self hyc]
    field_simp
  · refine aeval_ne_zero_of_unit (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (w := fun i' : J k₀ => z ⟨k₀, i'⟩) (i := i)
      (genMap ξ p) hinj (Scheme.stalkClosedPointTo zz).hom hyi hzi t ht ht' hN (hF c) heu ?_
    rw [he c, div_self hyc, _root_.mul_one, hee]

end GlobalTheory.CompanionTheory.Ar.BlockRatio
end
end

