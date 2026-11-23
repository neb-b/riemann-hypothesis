module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieModelTransportIsomorphism
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsIntegralPointWithCoordinates
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt


open scoped ComplexOrder in
theorem gramDet_ne_zero_of_linearIndependent :
    ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (f : Fin n → B.carrier), LinearIndependent (𝓞 L) f → B.gramDet σ f ≠ 0 := by
  intro L _ _ B σ n f hf
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec B.metric σ (f i)) =
      Matrix.of fun i j ↦ (B.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f j) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hf)).det_pos
  rw [hG] at hp
  exact hp.ne'

end GlobalTheory.CompanionTheory.Ar.RootHt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicInverseChartValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ImmersionBiholo


open Topology in
theorem ker_fderiv_comp_biholo : ∀ (e : ℕ) (X₁ X₂ V : Type) [TopologicalSpace X₁] [TopologicalSpace X₂] [NormedAddCommGroup V] [NormedSpace ℂ V] (A₁ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₁) (A₂ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₂) (π : X₁ → X₂) (inv : X₂ → X₁), ReciprocityTheory.AnForm.M.HoloMap A₁ A₂ π → ReciprocityTheory.AnForm.M.HoloMap A₂ A₁ inv → Function.Bijective π → (∀ x, inv (π x) = x) → ∀ (Φ : X₁ → V) (x : X₂) (j₁ : Fin A₁.n) (j₂ : Fin A₂.n), inv x ∈ (A₁.chart j₁).source → x ∈ (A₂.chart j₂).source → DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x)) → (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x))).ker = ⊥ → (fderiv ℂ (fun v => Φ (inv ((A₂.chart j₂).symm v))) (A₂.chart j₂ x)).ker = ⊥ := by
  intro e X₁ X₂ V _ _ _ _ A₁ A₂ π inv hπ hinv hbij hleft Φ x j₁ j₂ hx₁ hx₂ hdiff hker
  have hright : ∀ y, π (inv y) = y := fun y => by
    obtain ⟨w, rfl⟩ := hbij.2 y
    rw [hleft]
  have hy : A₂.chart j₂ x ∈ (A₂.chart j₂).target := (A₂.chart j₂).map_source hx₂
  have hsy : (A₂.chart j₂).symm (A₂.chart j₂ x) = x := (A₂.chart j₂).left_inv hx₂
  have hz : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target := (A₁.chart j₁).map_source hx₁
  have hsz : (A₁.chart j₁).symm (A₁.chart j₁ (inv x)) = inv x := (A₁.chart j₁).left_inv hx₁
  have hτ : DifferentiableAt ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) := by
    have hmem : A₂.chart j₂ x ∈ (A₂.chart j₂).target ∩
        ⇑(A₂.chart j₂).symm ⁻¹' (inv ⁻¹' (A₁.chart j₁).source) := by
      refine ⟨hy, ?_⟩
      show inv ((A₂.chart j₂).symm (A₂.chart j₂ x)) ∈ (A₁.chart j₁).source
      rw [hsy]
      exact hx₁
    exact (hinv.2 j₂ j₁ _ hmem).differentiableAt
  have hσ : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) (A₁.chart j₁ (inv x)) := by
    have hmem : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target ∩
        ⇑(A₁.chart j₁).symm ⁻¹' (π ⁻¹' (A₂.chart j₂).source) := by
      refine ⟨hz, ?_⟩
      show π ((A₁.chart j₁).symm (A₁.chart j₁ (inv x))) ∈ (A₂.chart j₂).source
      rw [hsz, hright]
      exact hx₂
    exact (hπ.2 j₁ j₂ _ hmem).differentiableAt
  have hev : ∀ᶠ v in 𝓝 (A₂.chart j₂ x),
      v ∈ (A₂.chart j₂).target ∧ inv ((A₂.chart j₂).symm v) ∈ (A₁.chart j₁).source := by
    refine Filter.Eventually.and ((A₂.chart j₂).open_target.mem_nhds hy) ?_
    have hc : ContinuousAt (inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) :=
      hinv.1.continuousAt.comp ((A₂.chart j₂).continuousAt_symm hy)
    have hs : (A₁.chart j₁).source ∈ 𝓝 ((inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
      rw [Function.comp_apply, hsy]
      exact (A₁.chart j₁).open_source.mem_nhds hx₁
    exact hc.preimage_mem_nhds hs
  have hτz : (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) = A₁.chart j₁ (inv x) := by
    simp only [Function.comp_apply, hsy]
  have hσ' : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hσ
  have hid : (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm)
      =ᶠ[𝓝 (A₂.chart j₂ x)] id := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply, id_eq]
    rw [(A₁.chart j₁).left_inv hv.2, hright, (A₂.chart j₂).right_inv hv.1]
  have hcomp : (fderiv ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).comp
      (fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))
      = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    rw [← fderiv_comp _ hσ' hτ, hid.fderiv_eq, fderiv_id]
  have hτinj : ∀ w, fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w = 0 → w = 0 := by
    intro w hw
    have h := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hw, map_zero] at h
    exact h.symm
  have hdiff' : DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hdiff
  have hker' : (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker = ⊥ := by
    rw [hτz]
    exact hker
  have hfeq : (fun v => Φ (inv ((A₂.chart j₂).symm v))) =ᶠ[𝓝 (A₂.chart j₂ x)]
      (fun v => Φ ((A₁.chart j₁).symm v)) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply]
    rw [(A₁.chart j₁).left_inv hv.2]
  rw [hfeq.fderiv_eq, fderiv_comp _ hdiff' hτ, eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  apply hτinj
  have h1 : fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w ∈
      (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
        ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker := hw
  rw [hker'] at h1
  exact h1

end GlobalTheory.CompanionTheory.Ar.ImmersionBiholo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem embedding_const_preconnected {F : Type} [Field F] [NumberField F] {m : ℕ} {B : Set (Fin m → ℂ)} (hpre : IsPreconnected B)
    (κ : (Fin m → ℂ) → (F →+* ℂ))
    (hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) B) {b b' : Fin m → ℂ} (hb : b ∈ B) (hb' : b' ∈ B) :
    κ b = κ b' := by
  have key : ∀ x : 𝓞 F, κ b (x : F) = κ b' (x : F) := by
    intro x
    have hT : IsDiscrete (Set.range fun s : F →+* ℂ => s (x : F)) :=
      (Set.finite_range _).isDiscrete
    have hmaps : Set.MapsTo (fun c => κ c (x : F)) B (Set.range fun s : F →+* ℂ => s (x : F)) :=
      fun c _ => ⟨κ c, rfl⟩
    exact hpre.constant_of_mapsTo hT (hd x).continuousOn hmaps hb hb'
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
  ext x
  exact key x

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyMultilinear
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    IsSmoothHerm (HermLine.ofWeight u hu) :=
  ContDiffOn.exp hs.neg

theorem smooth_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

theorem homog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [← C_1, C_apply] at hm
  have := Finset.mem_singleton.mp (support_monomial_subset hm)
  simp [this]

theorem inter_ofWeight {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    I W (n + 1) (Fin.snoc L (HermLine.ofWeight u hu)) = -ptsIntegral W (pot L) u := by
  have h1 : (1 : MRing ι) ∉ W := (Ideal.ne_top_iff_one W).mp hW.2.1.1.ne_top
  rw [hI.2.2 W n L _ 1 (fun _ => 0) hW hL (smooth_ofWeight u hu hs) (fun k => by simp [HermLine.ofWeight])
    homog_one h1]
  have hd : divSupp W (1 : MRing ι) = ∅ := by
    ext V
    simp [divSupp, Ideal.minimalPrimes_top]
  have hl : logNorm (HermLine.ofWeight u hu) (1 : MRing ι) = u := by
    funext z
    simp [logNorm, HermLine.ofWeight]
  unfold recR arInt
  rw [hd, hl]
  simp only [finsum_mem_empty, zero_sub]
  rfl

noncomputable def tens : (N : ℕ) → (Fin N → HermLine ι) → HermLine ι
  | 0, _ => HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)
  | N + 1, x => (tens N (fun i => x i.castSucc)).tensor (x (Fin.last N))

theorem tens_a : ∀ (N : ℕ) (x : Fin N → HermLine ι), (tens N x).a = ∑ i, (x i).a
  | 0, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x => by
    rw [Fin.sum_univ_castSucc, ← tens_a N (fun i => x i.castSucc)]
    rfl

theorem tens_h : ∀ (N : ℕ) (x : Fin N → HermLine ι) z, (tens N x).h z = ∏ i, (x i).h z
  | 0, _, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x, z => by
    rw [Fin.prod_univ_castSucc, ← tens_h N (fun i => x i.castSucc)]
    rfl

theorem tens_smooth : ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) → IsSmoothHerm (tens N x)
  | 0, _, _ => smooth_ofWeight _ _ contDiffOn_const
  | N + 1, x, hx => smooth_tensor (tens_smooth N _ fun _ => hx _) (hx _)

theorem ptsIntegral_zero (W : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral W φ (fun _ => 0) = 0 := by
  unfold ptsIntegral
  split_ifs with h
  · have : ∀ y w, sheetDensity W h.choose φ (fun _ => 0) y w = 0 := fun y w => by
      unfold sheetDensity
      split_ifs <;> simp
    simp [ptsIntegralAt, this]
  · rfl

theorem inter_tens {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) →
      I W (n + 1) (Fin.snoc L (tens N x)) = ∑ i, I W (n + 1) (Fin.snoc L (x i))
  | 0, _, _ => by
    rw [tens, inter_ofWeight hI hW hL _ _ contDiffOn_const, ptsIntegral_zero]
    simp
  | N + 1, x, hx => by
    rw [tens, hI.2.1 W n L _ _ hW hL (tens_smooth N _ fun _ => hx _) (hx _),
      inter_tens hI hW hL N _ (fun _ => hx _), Fin.sum_univ_castSucc]

end GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

theorem GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq : PtsIntegrableStatement → MetricLocalStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d N : ℕ) (x : Fin N → HermLine ι) (v : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → (∀ i, IsSmoothHerm (x i)) → (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → v (fun p => c p.1 * z p) = v z) → SmoothFn v → ∑ i, (x i).a = A.a → (∀ z ∈ mcPts W, ∏ i, (x i).h z = A.h z * Real.exp (-v z)) → ∑ i, I W (n + 1) (Fin.snoc L (x i)) = S.ht * ptsIntegral W (pot L) (fun _ => 1) - ptsIntegral W (pot L) v := by
  intro hP hM K _ ι _ Ω _ F _ _ y φ I W n L A S d N x v hI hV hO hyW hW hL hA hx hv hs ha hh
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hsn : ∀ B : HermLine ι, IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc L B : Fin (n + 1) → HermLine ι) j) := fun B hB j => by
    induction j using Fin.lastCases with
    | last => simpa using hB
    | cast j => simpa using hL j
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hloc : I W (n + 1) (Fin.snoc L (tens N x)) =
      I W (n + 1) (Fin.snoc L (A.tensor (HermLine.ofWeight v hv))) := by
    refine hM K ι I hI W (n + 1) _ _ hW (hsn _ (tens_smooth N x hx))
      (hsn _ (smooth_tensor hA (smooth_ofWeight v hv hs))) (fun j => ?_) (fun j z hz => ?_)
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_a, ha]
        simp [HermLine.tensor, HermLine.ofWeight]
      | cast j => simp only [Fin.snoc_castSucc]
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_h, hh z hz]
        rfl
      | cast j => simp only [Fin.snoc_castSucc]
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  rw [← inter_tens hI hW hL N x hx, hloc, hI.2.1 W n L _ _ hW hL hA (smooth_ofWeight v hv hs),
    inter_ofWeight hI hW hL v hv hs,
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq hP K ι Ω F y φ I W n L A S d hI hV hO hyW hW hL hA, sub_eq_add_neg]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricTorusPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos

theorem core_gram_posDef {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).PosDef := by
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp

theorem cochar_indep {Xc : Type} [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] {r : ℕ}
    (β : Fin r → (Xc →+ ℤ)) (hβ : LinearIndependent ℤ β) :
    LinearIndependent ℂ (fun a => (Int.castAddHom ℂ).comp (β a)) := by
  let b := Module.Free.chooseBasis ℤ Xc
  let ev : (Xc →+ ℤ) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ Xc → ℤ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have : f.toIntLinearMap = 0 := b.ext fun i => congrFun hf i
    ext x
    exact LinearMap.congr_fun this x
  have h1 : LinearIndependent ℤ (ev ∘ β) := hβ.map' ev hev
  have h2 : LinearIndependent ℂ (fun a => algebraMap ℤ ℂ ∘ (ev ∘ β) a) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  let evC : (Xc →+ ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ Xc → ℂ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp evC h2

theorem exists_diff {S : Scheme.{0}} {T G : Over S} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    {R : Type} [CommRing R] {x : Sp R ⟶ S} {E F : Type} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (M : LieModel T x E) (N : LieModel G x F) : ∃ A : E →ₗ[R] F, ∀ e, N.pt (A e) = M.pt e ≫ u := by
  have ht : ∀ e, IsTanAt G x (M.pt e ≫ u) := by
    intro e
    have h1 := (LieEx.isTanAt_iff x T _).1 (M.tan e)
    refine (LieEx.isTanAt_iff x G _).2 ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (h1 =≫ u).trans ?_
    exact MonObj.one_comp u
  choose A hA using fun e => N.onto _ (ht e)
  refine ⟨{ toFun := A, map_add' := fun e e' => N.inj ?_, map_smul' := fun c e => N.inj ?_ }, hA⟩
  · rw [N.add, hA, hA, hA, M.add, MonObj.mul_comp]
  · apply Over.OverMorphism.ext
    rw [N.smul, hA, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc]

theorem gramAt_posDef_of_diff_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  intro X Ω _ K J y ξ G _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β zc Mz _ hker v hv
  obtain ⟨V, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ (zc ≫ ρ)
  obtain ⟨A, hA⟩ := exists_diff u Mz (LiePull.modelPull hΦ zc MR)
  have hA' : ∀ δ, (MR.pt (A δ)).left = (Mz.pt δ ≫ u).left ≫ Φ := by
    intro δ
    rw [← hA, ← LiePull.pts_left hΦ (LiePull.eps_assoc zc)]
    exact congrArg (fun k => k.left) ((LiePull.tanPts hΦ zc).apply_symm_apply (MR.pt (A δ))).symm
  have hk : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro δ hδ
    apply hker
    rw [← hA, hδ]
    have := (LiePull.modelPull hΦ zc MR).add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hli := (cochar_indep β β.linearIndependent).map' A hk
  obtain ⟨core, hcore⟩ := h.herm (zc ≫ ρ) V MR
  have key := core_gram_posDef core _ hli
  have hv' : ∀ a, v a = MR.pt (A ((Int.castAddHom ℂ).comp (β a))) := fun a =>
    Over.OverMorphism.ext ((hv a).trans (hA' _).symm)
  have hm : RootHt.gramAt h (zc ≫ ρ) v = Matrix.of fun a b =>
      core.inner ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) a) ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) b) := by
    ext a c
    simp only [RootHt.gramAt, Matrix.of_apply, hcore, hv', Function.comp_apply]
  rw [hm]
  exact key

end GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Bridge

theorem comb_eig_frame : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ :=
  @PositivityTheory.Xgf.lie_model_eigenvectors_action

end GlobalTheory.CompanionTheory.Ar.Fl.Bridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsoTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IsoMove

theorem lieModel_isoMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ :=
  @PositivityTheory.UnitarySelfGeneration.lie_model_transport_isomorphism

end GlobalTheory.CompanionTheory.Ar.IsoMove
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabLie

theorem lieModel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (V : Type) [AddCommGroup V] [Module R V] (M : LieModel t'.G x V), ∃ Mf : LieModel t.G (x ≫ f) V, ∀ e, (Mf.pt e).left = (M.pt e).left ≫ m.φ := by
  intro E _ _ _ H S S' t' t f m R _ x V _ _ M
  obtain ⟨Mf, h⟩ := (LiePull.lieModel_pullback S S' t.G t'.G f m.φ m.cart R x V).2 M
  exact ⟨Mf, fun e => (h e).symm⟩

end GlobalTheory.CompanionTheory.Ar.SabLie
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_section_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem algebraicPoint_extends_to_integers : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ Small.ptsOver L (mCoordIdeal y), ∃ z : Sp (𝓞 L) ⟶ X, CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w :=
  @CoverDenseAlt.exists_integral_point_with_coordinates

end GlobalTheory.CompanionTheory.Ar
end

