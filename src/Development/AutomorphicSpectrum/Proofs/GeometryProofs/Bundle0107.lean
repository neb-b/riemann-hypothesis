module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0098
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0026
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TwoTorsionPointsSpreadOpen

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SameOrbitOfProportionalCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrbitBlock

theorem aeval_smul_of_homog {σ A : Type} [Fintype σ] [CommRing A] [Algebra ℤ A] {n : ℕ}
    {F : MvPolynomial σ ℤ} (hF : F.IsHomogeneous n) (t : A) (b : σ → A) :
    MvPolynomial.aeval (fun i => t * b i) F = t ^ n * MvPolynomial.aeval b F := by
  classical
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem mConeMap_rename_block {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ : K)
    {F : MvPolynomial (J k₀) ℤ} (hF : F.IsHomogeneous n) :
    mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.X k₀ ^ n *
        MvPolynomial.C (MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F) := by
  have h1 : mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.aeval (fun i : J k₀ => (MvPolynomial.X k₀ : MvPolynomial K Ω) *
        MvPolynomial.C (y ⟨k₀, i⟩)) F := by
    rw [mConeMap, MvPolynomial.aeval_rename]
    congr 2
    funext i
    simp [mul_comm]
  rw [h1, aeval_smul_of_homog hF]
  congr 1
  exact (MvPolynomial.comp_aeval_apply (fun i : J k₀ => y ⟨k₀, i⟩)
    (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) F).symm

theorem relation_at {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ k : K) (c j : J k)
    {Fj Fc : MvPolynomial (J k₀) ℤ} (hj : Fj.IsHomogeneous n) (hc : Fc.IsHomogeneous n)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fj * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fc * y ⟨k, j⟩)
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fj * w ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fc * w ⟨k, j⟩ := by
  set G : MRing J := MvPolynomial.rename (Sigma.mk k₀) Fj * MvPolynomial.X ⟨k, c⟩ -
    MvPolynomial.rename (Sigma.mk k₀) Fc * MvPolynomial.X ⟨k, j⟩ with hG
  have hmem : G ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, hG, map_sub, map_mul, map_mul,
      mConeMap_rename_block y k₀ hj, mConeMap_rename_block y k₀ hc]
    have hx : ∀ p : Σ k, J k, mConeMap y (MvPolynomial.X p) =
        MvPolynomial.C (y p) * MvPolynomial.X p.1 := fun p => by
      simp [mConeMap]
    rw [hx, hx]
    have h' := congrArg (MvPolynomial.C : Ω →+* MvPolynomial K Ω) h
    simp only [map_mul] at h'
    linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * h'
  have hv := hw.2 G hmem
  have hv' : MvPolynomial.aeval w G = 0 := by
    rw [← hv, MvPolynomial.eval_map]
    rfl
  rw [hG, map_sub, map_mul, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X] at hv'
  exact sub_eq_zero.1 hv'

theorem sameOrbit_of_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ w ∈ mcPts (mCoordIdeal y), ∀ w' ∈ mcPts (mCoordIdeal y), ∀ u : ℂ, (∀ i : J k₀, w ⟨k₀, i⟩ = u * w' ⟨k₀, i⟩) → SameOrbit w w' := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE w hw w' hw' u hu
  have hpts : w ∈ Small.ptsOver ℂ (mCoordIdeal y) := by
    refine ⟨hw.1, fun f hf => ?_⟩
    rw [← hw.2 f hf, MvPolynomial.eval_map]
    rfl
  obtain ⟨i, hi⟩ := hw.1 k₀
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hi (by rw [hu i, zero_mul])
  have key : ∀ k, ∃ s : ℂ, s ≠ 0 ∧ ∀ j, w ⟨k, j⟩ = s * w' ⟨k, j⟩ := by
    intro k
    obtain ⟨c, hc⟩ := hw.1 k
    obtain ⟨n, F, hF, hrel, hne⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms X Ω ξ K J y k₀ hT hE ℂ w hpts i k c hi hc
    have hscale : ∀ t, MvPolynomial.aeval (fun i' : J k₀ => w ⟨k₀, i'⟩) (F t) =
        u ^ n * MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F t) := by
      intro t
      rw [← aeval_smul_of_homog (hF t)]
      congr 2
      funext i'
      exact hu i'
    have hne' : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) ≠ 0 := by
      intro h0
      exact hne (by rw [hscale, h0, mul_zero])
    have r := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw
    have r' := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw'
    have hc' : w' ⟨k, c⟩ ≠ 0 := by
      intro h0
      obtain ⟨j, hj⟩ := hw'.1 k
      have := r' j
      rw [h0, mul_zero] at this
      exact (mul_ne_zero hne' hj) this.symm
    refine ⟨w ⟨k, c⟩ / w' ⟨k, c⟩, div_ne_zero hc hc', fun j => ?_⟩
    have e1 := r j
    have e2 := r' j
    rw [hscale, hscale] at e1
    have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e3 : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * w ⟨k, c⟩ =
        MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) * w ⟨k, j⟩ :=
      mul_left_cancel₀ hun (by linear_combination e1)
    apply mul_left_cancel₀ hne'
    have e4 : w ⟨k, c⟩ / w' ⟨k, c⟩ * w' ⟨k, c⟩ = w ⟨k, c⟩ := div_mul_cancel₀ _ hc'
    linear_combination (-1 : ℂ) * e3 + (w ⟨k, c⟩ / w' ⟨k, c⟩) * e2 -
      MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * e4
  choose s hs0 hs using key
  exact ⟨s, hs0, funext fun p => by
    obtain ⟨k, j⟩ := p
    exact hs k j⟩

end GlobalTheory.CompanionTheory.Ar.OrbitBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

private theorem smoothOfRelativeDimension_restrict_of_le {A S : Scheme.{0}} (f : A ⟶ S) {n : ℕ} {V W : A.Opens} (h : V ≤ W)
    (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) : SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have := smoothOfRelativeDimension_comp 0 n (A.homOfLE h) (W.ι ≫ f)
  rw [zero_add, ← Category.assoc, Scheme.homOfLE_ι] at this
  exact this

private theorem relDim_eq_of_mem_of_mem {A S : Scheme.{0}} (f : A ⟶ S) {n m : ℕ} {V W : A.Opens}
    (hV : SmoothOfRelativeDimension n (V.ι ≫ f)) (hW : SmoothOfRelativeDimension m (W.ι ≫ f))
    {x : A} (hxV : x ∈ V) (hxW : x ∈ W) : n = m :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ (smoothOfRelativeDimension_restrict_of_le f inf_le_left hV) (smoothOfRelativeDimension_restrict_of_le f inf_le_right hW)
    ⟨x, hxV, hxW⟩

theorem reldim_eq_of_two_pullbacks {P A S : Scheme.{0}} {f : A ⟶ S} {b : A ⟶ S} {p : P ⟶ A} {a₁ a₂ : P ⟶ A}
    (h₁ : IsPullback a₁ p f b) (h₂ : IsPullback a₂ p f b) {n₁ n₂ : ℕ} {W₁ W₂ : A.Opens}
    (d₁ : SmoothOfRelativeDimension n₁ (W₁.ι ≫ f)) (d₂ : SmoothOfRelativeDimension n₂ (W₂.ι ≫ f))
    (z : P) (hz₁ : a₁ z ∈ W₁) (hz₂ : a₂ z ∈ W₂) : n₁ = n₂ := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₁
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₂
  have e₁ : SmoothOfRelativeDimension n₁ ((a₁ ⁻¹ᵁ W₁).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₁)
      ((isPullback_morphismRestrict a₁ W₁).paste_vert h₁) d₁
  have e₂ : SmoothOfRelativeDimension n₂ ((a₂ ⁻¹ᵁ W₂).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₂)
      ((isPullback_morphismRestrict a₂ W₂).paste_vert h₂) d₂
  exact relDim_eq_of_mem_of_mem p e₁ e₂ hz₁ hz₂

theorem isPullback_fst_snd {X : Scheme.{0}} (G : Over X) :
    IsPullback (fst G G) (snd G G) (toUnit G) (toUnit G) := by
  exact IsPullback.of_is_product (tensorProductIsBinaryProduct G G) isTerminalTensorUnit

theorem isPullback_mul_snd {X : Scheme.{0}} (G : Over X) [GrpObj G] :
    IsPullback (fst G G * snd G G) (snd G G) (toUnit G) (toUnit G) := by
  refine IsPullback.of_is_product (c := BinaryFan.mk (fst G G * snd G G) (snd G G)) ?_ isTerminalTensorUnit
  refine BinaryFan.IsLimit.mk _ (fun u v => lift (u * v⁻¹) v) ?_ ?_ ?_
  · intro T u v
    simp [comp_mul]
  · intro T u v
    simp
  · intro T u v m h₁ h₂
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h₁ h₂
    have h₃ : m ≫ fst G G * v = u := by
      rw [← h₂]
      exact (comp_mul m (fst G G) (snd G G)).symm.trans h₁
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simpa using eq_mul_inv_of_mul_eq h₃
    · simpa using h₂

theorem toUnit_left {X : Scheme.{0}} (G : Over X) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

theorem reldim_eq_unit {X : Scheme.{0}} (G : Over X) [GrpObj G] {n m : ℕ} {W V : G.left.Opens}
    (dW : SmoothOfRelativeDimension n (W.ι ≫ G.hom)) (dV : SmoothOfRelativeDimension m (V.ι ≫ G.hom))
    (g : G.left) (hg : g ∈ W) (hV : eSec G (G.hom g) ∈ V) : n = m := by
  have h₁ := (isPullback_fst_snd G).map (Over.forget X)
  have h₂ := (isPullback_mul_snd G).map (Over.forget X)
  simp only [Over.forget_map, toUnit_left] at h₁ h₂
  have p₁ : (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    simp
  have p₂ : (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = (η[G]).left (G.hom g) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mul, lift_fst, lift_snd, mul_inv_cancel,
      Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply, toUnit_left]
  refine reldim_eq_of_two_pullbacks h₁ h₂ dW dV ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ?_ ?_
  · show (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ W
    rw [p₁]
    exact hg
  · show (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ V
    rw [p₂]
    unfold eSec at hV
    exact hV

private theorem smoothOfRelativeDimension_of_local {A S : Scheme.{0}} (f : A ⟶ S) (n : ℕ)
    (h : ∀ x : A, ∃ W : A.Opens, x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  rw [smoothOfRelativeDimension_iff]
  intro x
  obtain ⟨W, hxW, hW⟩ := h x
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := (smoothOfRelativeDimension_iff n (W.ι ≫ f)).1 hW ⟨x, hxW⟩
  have e₁ : W.ι ''ᵁ V ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact e hv
  have e₂ : V ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ V) := fun v hv => ⟨v, hv, rfl⟩
  have hcomp := Scheme.Hom.appLE_comp_appLE W.ι f U (W.ι ''ᵁ V) V e₁ e₂
  have hiso : W.ι.appLE (W.ι ''ᵁ V) V e₂ = (W.ι.appIso V).hom := (Scheme.Hom.appIso_hom' W.ι V).symm
  have key : f.appLE U (W.ι ''ᵁ V) e₁ = (W.ι ≫ f).appLE U V e ≫ (W.ι.appIso V).inv := by
    rw [← hcomp, hiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨U, hU, W.ι ''ᵁ V, hV.image_of_isOpenImmersion W.ι, ⟨⟨x, hxW⟩, hxV, rfl⟩, e₁, ?_⟩
  rw [key, CommRingCat.hom_comp]
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (W.ι.appIso V).inv.hom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (W.ι.appIso V).symm.commRingCatIsoToRingEquiv
  have h1 := h0.comp hstd
  rwa [zero_add] at h1

theorem smoothGrp_relDim : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [Smooth G.hom],
    (∀ q : X, genPt ξ ⤳ q) → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X Ω _ ξ G _ _ hgen
  obtain ⟨n₀, W₀, hW₀, d₀⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (genPt ξ))
  refine ⟨n₀, smoothOfRelativeDimension_of_local G.hom n₀ fun g => ?_⟩
  obtain ⟨n, W, hgW, dW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom g
  obtain ⟨m, V, hV, dV⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (G.hom g))
  have h₁ : n = m := reldim_eq_unit G dW dV g hgW hV
  have hsp : eSec G (genPt ξ) ⤳ eSec G (G.hom g) := (hgen (G.hom g)).map (eSec G).base.hom.continuous
  have h₂ : m = n₀ := relDim_eq_of_mem_of_mem G.hom dV d₀ (hsp.mem_open V.isOpen hV) hW₀
  rw [h₁, h₂] at dW
  exact ⟨W, hgW, dW⟩

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructure
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.TorusAct

theorem isMonHom_of_comp_mono {C : Type*} [Category C] [CartesianMonoidalCategory C] {T G : C}
    [MonObj T] [MonObj G] (i : T ⟶ G) [IsMonHom i] [Mono i] (f : G ⟶ G) [IsMonHom f] (u : T ⟶ T)
    (h : u ≫ i = i ≫ f) : IsMonHom u := by
  constructor
  · rw [← cancel_mono i, Category.assoc, h, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono i).1
    simp only [Category.assoc, h, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

theorem diagMap_eq_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X) :
    GlobalTheory.Diag.diagMap S u = GlobalTheory.SplitTorus.torusMap S u :=
  (GlobalTheory.SplitTorus.eq_torusMap_iff _ _).2 (GlobalTheory.Diag.diagMap_chi S u)

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G]

theorem mono_i (τ : TorusExtension G) : letI := τ.addCommGroup; letI := τ.grpB; Mono τ.i := by
  letI := τ.addCommGroup
  letI := τ.grpB
  exact ⟨fun g h e => τ.isKernel.hom_ext e (toUnit_unique _ _)⟩

theorem exists_restrict (τ : TorusExtension G) (f : G ⟶ G) [IsMonHom f] :
    letI := τ.addCommGroup; letI := τ.grpB; ∀ (b : τ.B ⟶ τ.B), IsMonHom b → f ≫ τ.q = τ.q ≫ b →
      ∃ φ : τ.X →+ τ.X, GlobalTheory.SplitTorus.torusMap (Sp K) φ ≫ τ.i = τ.i ≫ f := by
  letI := τ.addCommGroup
  letI := τ.grpB
  intro b hb hq
  haveI := mono_i τ
  haveI := τ.i_hom
  have w : (τ.i ≫ f) ≫ τ.q = toUnit _ ≫ η := by
    rw [Category.assoc, hq, ← Category.assoc, τ.isKernel.w, Category.assoc, IsMonHom.one_hom]
  let u := τ.isKernel.lift (τ.i ≫ f) (toUnit _) w
  have hu : u ≫ τ.i = τ.i ≫ f := τ.isKernel.lift_fst _ _ _
  haveI : IsMonHom u := isMonHom_of_comp_mono τ.i f u hu
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨φ, hφ ▸ hu⟩

theorem exists_module_diagAct : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G)
    (O : Type) [CommRing O] (act : OAct O G), letI := τ.addCommGroup; letI := τ.grpB;
    (∀ a, ∃ b : τ.B ⟶ τ.B, IsMonHom b ∧ act.act a ≫ τ.q = τ.q ≫ b) →
      ∃ m : Module O τ.X, letI := m;
        ∀ a, (GlobalTheory.Diag.diagAct (Sp K) O τ.X).act a ≫ τ.i = τ.i ≫ act.act a := by
  intro K _ G _ τ O _ act
  letI := τ.addCommGroup
  letI := τ.grpB
  intro hb
  haveI := mono_i τ
  haveI := τ.i_hom
  have ex : ∀ a, ∃ φ : τ.X →+ τ.X, GlobalTheory.SplitTorus.torusMap (Sp K) φ ≫ τ.i = τ.i ≫ act.act a := fun a => by
    obtain ⟨b, h1, h2⟩ := hb a
    haveI := act.hom a
    exact exists_restrict τ _ b h1 h2
  choose φ hφ using ex
  have inj : ∀ {α β : τ.X →+ τ.X}, GlobalTheory.SplitTorus.torusMap (Sp K) α ≫ τ.i =
      GlobalTheory.SplitTorus.torusMap (Sp K) β ≫ τ.i → α = β := fun h =>
    GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 h)
  have h1 : φ 1 = AddMonoidHom.id τ.X := inj (by
    rw [hφ, act.one, GlobalTheory.SplitTorus.torusMap_id, Category.comp_id, Category.id_comp])
  have hm : ∀ a b, φ (a * b) = (φ a).comp (φ b) := fun a b => inj (by
    rw [hφ, act.mul, GlobalTheory.SplitTorus.torusMap_comp, Category.assoc, hφ,
      ← Category.assoc _ τ.i, hφ, Category.assoc])
  have ha : ∀ a b, φ (a + b) = φ a + φ b := fun a b => inj (by
    rw [hφ, act.add, GlobalTheory.SplitTorus.torusMap_add, MonObj.mul_comp, hφ, hφ, MonObj.comp_mul])
  let ρ : O →+* AddMonoid.End τ.X := RingHom.mk' ⟨⟨φ, h1⟩, hm⟩ ha
  letI m : Module O τ.X := Module.compHom τ.X ρ
  refine ⟨m, fun a => ?_⟩
  have e : DistribSMul.toAddMonoidHom τ.X a = φ a := rfl
  rw [GlobalTheory.Diag.diagAct_act, e, diagMap_eq_torusMap, hφ]

end GlobalTheory.CompanionTheory.TorusAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExact
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieExact

theorem ker_fst_isNilpotent {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra R (DualNumber A)] (π : DualNumber A →ₐ[R] A)
    (h : ∀ b, π b = TrivSqZeroExt.fst b) : IsNilpotent (RingHom.ker (π : DualNumber A →+* A)) := by
  refine ⟨2, ?_⟩
  rw [pow_two]
  refine le_bot_iff.mp (Ideal.mul_le.mpr fun a ha b hb => ?_)
  have ha' : TrivSqZeroExt.fst a = 0 := by rw [← h]; exact ha
  have hb' : TrivSqZeroExt.fst b = 0 := by rw [← h]; exact hb
  have : a * b = 0 := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha', hb']
  simp [this]

theorem exists_lift_dual {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (A : Type) [Field A]
    (s : Spec (CommRingCat.of (DualNumber A)) ⟶ S) (x₀ : Spec (CommRingCat.of A) ⟶ X)
    (h : x₀ ≫ f = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ s) :
    ∃ x : Spec (CommRingCat.of (DualNumber A)) ⟶ X,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber A) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom
  have hloc : IsLocalHom π.hom := ⟨fun b hb => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hb⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) (O := ⊤) trivial
  refine GlobalTheory.exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (GlobalTheory.range_subset_opens_of_isLocalRing s ?_) (GlobalTheory.range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) =
        s (Spec.map π (IsLocalRing.closedPoint (CommRingCat.of A))) :=
      congr($h (IsLocalRing.closedPoint (CommRingCat.of A)))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R B _ _ _ _ _ _ π' hπ' φ
    have hsurj : Function.Surjective π' := fun a => ⟨TrivSqZeroExt.inl a, by rw [hπ']; rfl⟩
    have hnil := ker_fst_isNilpotent π' (fun b => by rw [hπ']; rfl)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ π' hsurj hnil,
      Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩

variable {S : Scheme.{0}}

theorem one_comp_hom {M N T : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : T ⟶ M) ≫ f = 1 := by
  simp [Hom.one_def, IsMonHom.one_hom]

noncomputable def zeroSec {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) : Over.mk x ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) (by
    simp only [Over.mk_left, Over.mk_hom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; rfl
    rw [this]; simp)

theorem isTanAt_iff {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ zeroSec x ≫ v = 1 :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t : Over.mk x ⟶ G => t.left) h⟩

end GlobalTheory.CompanionTheory.Ar.LieExact


open GlobalTheory.CompanionTheory.Ar.LieExact in
theorem GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G), letI := τ.addCommGroup; letI := τ.grpB; ∀ (A : Type) [Field A] (c : K →+* A), (∀ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v → (v ≫ τ.q = 1 ↔ ∃ w : epsAt (spMap c) ⟶ splitTorus (Sp K) τ.X, IsTanAt _ _ w ∧ w ≫ τ.i = v)) ∧ ∀ w : epsAt (spMap c) ⟶ τ.B, IsTanAt τ.B _ w → ∃ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v ∧ v ≫ τ.q = w := by
  intro K _ G _ τ
  letI := τ.addCommGroup
  letI := τ.grpB
  intro A _ c
  have hq : IsMonHom τ.q := τ.q_hom
  have hi : IsMonHom τ.i := τ.i_hom
  refine ⟨fun v hv => ⟨fun h => ?_, ?_⟩, fun w hw => ?_⟩
  · have sq : v ≫ τ.q = toUnit _ ≫ η := h.trans Hom.one_def
    refine ⟨τ.isKernel.lift v (toUnit _) sq, ?_, τ.isKernel.lift_fst _ _ _⟩
    rw [isTanAt_iff]
    refine τ.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.assoc, τ.isKernel.lift_fst, one_comp_hom, (isTanAt_iff _ _ _).mp hv]
  · rintro ⟨w, -, rfl⟩
    rw [Category.assoc, τ.isKernel.w, ← Category.assoc, toUnit_unique (w ≫ toUnit _) (toUnit _),
      Hom.one_def]
  · obtain ⟨hs, -⟩ := GlobalTheory.torusExtension_smooth_geometricallyConnected G τ
    obtain ⟨x, hx1, hx2⟩ := exists_lift_dual τ.q.left A w.left
      (1 : Over.mk (spMap c) ⟶ G).left (by
        have h1 : ((1 : Over.mk (spMap c) ⟶ G) ≫ τ.q).left = (1 : Over.mk (spMap c) ⟶ τ.B).left := by
          rw [one_comp_hom]
        rw [Over.comp_left] at h1
        exact h1.trans hw.symm)
    refine ⟨Over.homMk x ?_, hx1, Over.OverMorphism.ext hx2⟩
    rw [← Over.w τ.q, ← Category.assoc, hx2, Over.w w]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelTrivialOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.KerSpread

theorem injective_on_points_of_generic : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.torus_kernel_trivial_spreads_open

end GlobalTheory.CompanionTheory.Ar.KerSpread
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwoTorsionSpreadOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem pts_spread : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  exact @PositivityTheory.Xgn.two_torsion_points_spread_open

end GlobalTheory.CompanionTheory.Ar
end

