module

public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0014
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FormHeightGen
public import Development.WeilBound.CoreStatements.NefModelVolumes.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanEqMahler
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import ReciprocityTheory.SemistableReduction.Bundle0018
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.MemMinimalPrimesOfMemSupport
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DifferentiableOnSheet
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FormHeightOneEq
section
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Matrix GlobalTheory.ChowHt GroundTheory.Heights₂.Heights

namespace ChowFormHeightComparison₂.CF.D

theorem gaussAbs_eq {K : Type} [Field K] [NumberField K] {ι : Type} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (f : MvPolynomial ι K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.equivHeightOneSpectrum.symm v) f = gaussNorm v f := by
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs gaussNorm
  congr 2
  funext s
  apply NNReal.eq
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply]
  show ((‖(FinitePlace.embedding v) (AddMonoidAlgebra.coeff f s)‖).toNNReal : ℝ) = HeightOneSpectrum.adicAbv K v (AddMonoidAlgebra.coeff f s)
  rw [FinitePlace.norm_embedding]
  exact Real.coe_toNNReal _ (AbsoluteValue.nonneg _ _)

theorem mean_eq_mahler {m k : ℕ} (hm : 1 ≤ m) (h : HermNorm m) {f : MvPolynomial (Fin k × Fin m) ℂ} (hf : f ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst h.mat⁻¹ f) = mahler h k f := by
  have hB : (h.mat * h.mat⁻¹)ᴴ * (h.mat * h.mat⁻¹) = 1 := by
    rw [Matrix.mul_nonsing_inv _ h.isUnit_det]
    simp
  rw [← GlobalTheory.CompanionTheory.Ar.HS.SphereMean.sphere_mean_eq_mahler m k h h.mat⁻¹ f hm hf hB]
  have hP : ∀ n, ReciprocityTheory.MultiplicativeHeights.sphereProb n = GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP n := by
    intro n
    unfold ReciprocityTheory.MultiplicativeHeights.sphereProb GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP
    rw [ProbabilityTheory.cond, MeasureTheory.Measure.restrict_univ]
  have hE : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere k m,
      eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (linSubst h.mat⁻¹ f) =
        eval (fun p : Fin k × Fin m => (h.mat⁻¹ *ᵥ fun a => (↑(z p.1) : EuclideanSpace ℂ (Fin m)).ofLp a) p.2) f := by
    intro z
    unfold linSubst
    rw [MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    erw [MvPolynomial.aeval_bind₁]
    refine congrArg (fun g => MvPolynomial.aeval g f) ?_
    funext p
    simp [ReciprocityTheory.MultiplicativeHeights.blockPoint, ReciprocityTheory.MultiplicativeHeights.spherePoint, Matrix.mulVec, dotProduct, mul_comm]
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  simp only [hP, hE]

theorem formHeight_one_eq {K : Type} [Field K] [NumberField K] {m k : ℕ} (hm : 1 ≤ m) (H : ArchData K m) (δ : ℕ)
    {f : MvPolynomial (Fin k × Fin m) K} (hf : f ≠ 0) :
    formHeight δ (1 : Matrix (Fin m) (Fin m) K) (fun σ => (H.normAt σ).mat⁻¹) f = chowHt H k δ f := by
  unfold formHeight chowHt
  rw [GlobalTheory.HeightUnique.linSubst_one, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  have e (σ : K →+* ℂ) : ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst (H.normAt σ).mat⁻¹ (MvPolynomial.map σ f)) =
      mahler (H.normAt σ) k (MvPolynomial.map σ f) :=
    mean_eq_mahler hm _ fun h0 => hf (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  simp only [gaussAbs_eq, e]
  ring

end ChowFormHeightComparison₂.CF.D

private theorem coneMap_comp_coordSubst {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N N' : ℕ}
    (M : Matrix (Fin N) (Fin N') K) (y : Fin N → Ω) :
    (GlobalTheory.CompHt.coneMap K y).comp (GlobalTheory.CompHt.coordSubst M) =
      GlobalTheory.CompHt.coneMap K (fun k => ∑ j, algebraMap K Ω (M j k) * y j) := by
  apply MvPolynomial.algHom_ext
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, GlobalTheory.CompHt.coordSubst, GlobalTheory.CompHt.coneMap, MvPolynomial.aeval_X, map_sum,
    map_mul, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem aeval_linSubst {K L : Type} [Field K] [CommRing L] [Algebra K L] {B N n : ℕ}
    (M : Matrix (Fin N) (Fin n) K) (f : MvPolynomial (Fin B × Fin N) K) (u : Fin B × Fin n → L) :
    MvPolynomial.aeval u (linSubst M f) =
      MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, algebraMap K L (M p.2 k) * u (p.1, k)) f := by
  unfold linSubst
  rw [MvPolynomial.aeval_eq_bind₁]
  erw [MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g f) ?_
  funext p
  simp [MvPolynomial.aeval_X, MvPolynomial.aeval_C]

private theorem isChowForm_of_isChowFormInt {k : Type} [Field k] {N : ℕ} {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (hf : IsChowFormInt I e dl f) :
    GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  refine ⟨hf.ne_zero, fun p => ⟨fun hp => hf.dvd_of_forall_aeval_eq_zero
    (fun u hu => hp u ((hf.zero_iff u).1 hu)), ?_⟩⟩
  rintro ⟨q, rfl⟩ u hu
  rw [map_mul, (hf.zero_iff u).2 hu, zero_mul]

private theorem sum_algebraMap_mul_sum_eq_matrix_mul {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b c : ℕ}
    (M : Matrix (Fin a) (Fin b) K) (P : Matrix (Fin b) (Fin c) K) (z : Fin a → L) (k : Fin c) :
    ∑ j : Fin b, algebraMap K L (P j k) * ∑ i : Fin a, algebraMap K L (M i j) * z i =
      ∑ i, algebraMap K L ((M * P) i k) * z i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem sum_sum_algebraMap_mul_comm {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b : ℕ}
    (g : Matrix (Fin a) (Fin b) K) (v : Fin b → L) (z : Fin a → L) :
    ∑ j, (∑ k, algebraMap K L (g j k) * v k) * z j = ∑ k, v k * ∑ j, algebraMap K L (g j k) * z j := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

private theorem exists_right_inverse_of_span_col_eq_top {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) : ∃ P : Matrix (Fin m) (Fin N) K, g * P = 1 := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective g.mulVecLin
    (by rw [Matrix.range_mulVecLin, hg])
  refine ⟨LinearMap.toMatrix' r, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hr
  have h2 : LinearMap.toMatrix' g.mulVecLin = g := LinearMap.toMatrix'_toLin' g
  rw [LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id] at h1
  exact h1

private theorem isMultiHomog_of_isMultiHomogeneous_const {K : Type} [Field K] {B n δ : ℕ} (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f) : GroundTheory.Heights₂.Heights.IsMultiHomog δ f := by
  intro s hs
  funext b
  have hb : ∑ j : Fin n, s (b, j) = δ := hf s (MvPolynomial.mem_support_iff.2 hs) b
  rw [← hb, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [GroundTheory.Heights₂.Heights.groupWeight, Pi.single_apply]


open ChowFormHeightComparison₂.CF.D in
theorem ChowFormHeightComparison₂.CF.stForm : ChowFormHeightComparison₂.CF.StForm := by
  intro K Ω _ _ _ _ d N m δ g A hspan hA y Φ hΦ H hH
  obtain ⟨P, hgP⟩ := exists_right_inverse_of_span_col_eq_top g hspan
  have hne : Φ ≠ 0 := hΦ.ne_zero
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      exfalso
      have hirr := hΦ.irred
      have hC := MvPolynomial.eq_C_of_isEmpty Φ
      have hc : AddMonoidAlgebra.coeff Φ 0 ≠ 0 := fun h => hne (by rw [hC, h, map_zero])
      rw [hC] at hirr
      exact hirr.not_isUnit ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C)
    · exact h0
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exfalso
      have := congrFun (congrFun hgP ⟨0, hN⟩) ⟨0, hN⟩
      simp [Matrix.mul_apply] at this
    · exact h0
  refine ⟨isChowForm_of_isChowFormInt (dl := δ) ?_, isMultiHomog_of_isMultiHomogeneous_const _ (GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog), ?_⟩
  · refine ⟨GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog, PositivityTheory.UnitarySelfGeneration.UnitProductCombination.irreducible_linSubst hgP hΦ.irred, ?_⟩
    intro u
    rw [aeval_linSubst, hΦ.zero_iff]
    constructor
    · rintro ⟨z, hz0, hzI, hzu⟩
      refine ⟨fun k => ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j, ?_, ?_, ?_⟩
      · intro hx
        apply hz0
        have hx' : ∀ k, ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j = 0 := fun k => congrFun hx k
        funext i
        have h2 := sum_algebraMap_mul_sum_eq_matrix_mul g P z i
        simp only [hx', mul_zero, Finset.sum_const_zero, hgP, Matrix.one_apply] at h2
        simpa using h2.symm
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hzI
        show GlobalTheory.CompHt.coneMap K y (GlobalTheory.CompHt.coordSubst g h) = 0
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst]
        exact hh
      · intro i
        exact (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) z).symm.trans (hzu i)
    · rintro ⟨x, hx0, hxI, hxu⟩
      have hxz : ∀ k, x k = ∑ j, algebraMap K (AlgebraicClosure K) (g j k) *
          ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' := by
        intro k
        have hl : (MvPolynomial.X k - GlobalTheory.CompHt.coordSubst (P * g) (MvPolynomial.X k)) ∈
            GlobalTheory.CompHt.coneIdeal K (fun k => ∑ j, algebraMap K Ω (g j k) * y j) := by
          show GlobalTheory.CompHt.coneMap K _ _ = 0
          have e : (fun k => ∑ j, algebraMap K Ω ((P * g) j k) * ∑ i, algebraMap K Ω (g i j) * y i) =
              fun k => ∑ i, algebraMap K Ω (g i k) * y i := by
            funext k
            rw [sum_algebraMap_mul_sum_eq_matrix_mul, ← Matrix.mul_assoc, hgP, Matrix.one_mul]
          rw [map_sub, ← AlgHom.comp_apply, coneMap_comp_coordSubst, e, sub_self]
        have h3 := hxI _ hl
        rw [map_sub, GlobalTheory.CompHt.aeval_coordSubst, MvPolynomial.aeval_X, MvPolynomial.aeval_X, sub_eq_zero] at h3
        rw [h3]
        exact (sum_algebraMap_mul_sum_eq_matrix_mul P g x k).symm
      refine ⟨fun j => ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k', ?_, ?_, ?_⟩
      · intro hz
        apply hx0
        have hz' : ∀ j, ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' = 0 := fun j => congrFun hz j
        funext k
        rw [hxz k]
        simp [hz']
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hxI
        show GlobalTheory.CompHt.coneMap K _ (GlobalTheory.CompHt.coordSubst P h) = 0
        have e : (fun k => ∑ j, algebraMap K Ω (P j k) * ∑ i, algebraMap K Ω (g i j) * y i) = y := by
          funext k
          rw [sum_algebraMap_mul_sum_eq_matrix_mul, hgP]
          simp [Matrix.one_apply]
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst, e]
        exact hh
      · intro i
        refine (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) _).trans ?_
        simp only [← hxz]
        exact hxu i
  · rw [← PositivityTheory.UnitarySelfGeneration.UnitProductCombination.formHeight_gen hN g hspan A hA (fun σ => (H.normAt σ).mat⁻¹) ?_ hne hΦ.homog,
      formHeight_one_eq hm H δ (GlobalTheory.HeightUnique.linSubst_ne_zero hgP hne)]
    intro σ x
    have h1 := hH σ x
    unfold GroundTheory.Heights₂.Heights.HermNorm.dualNorm at h1
    rw [← h1, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Matrix.mulVec, dotProduct, ← Matrix.transpose_nonsing_inv]
end
end

-- bundled from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralOfLintegral
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GroundTheory.Heights₂.Heights (HermNorm coneBall fsLog coneIntegral coordBall_mass IsProjPrime)
open scoped ENNReal

namespace ChowFormHeightComparison₂.CF.C

theorem integral_of_lintegral {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {b : ℝ≥0∞} (hb : b ≠ 0) (hb' : b ≠ ⊤) {f : X → ℝ} {g : Y → ℝ} (hg : Measurable g) (hf : Integrable f μ)
    (h : ∀ G : ℝ → ℝ≥0∞, Measurable G → ∫⁻ x, G (f x) ∂μ = b * ∫⁻ y, G (g y) ∂ν) :
    Integrable g ν ∧ ∫ y, g y ∂ν = (∫ x, f x ∂μ) / b.toReal := by
  have hG1 : Measurable fun t : ℝ => ‖t‖ₑ := measurable_enorm
  have hgi : Integrable g ν := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    have hfin : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := hf.2
    rw [h _ hG1] at hfin
    exact ENNReal.lt_top_of_mul_ne_top_right hfin.ne hb
  refine ⟨hgi, ?_⟩
  have hp := h _ ENNReal.measurable_ofReal
  have hn := h (fun t => ENNReal.ofReal (-t)) (ENNReal.measurable_ofReal.comp measurable_neg)
  have hb0 : b.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hb, hb'⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi, hp, hn,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub]
  field_simp

theorem map_notMem {K : Type} [Field K] [NumberField K] {m : ℕ} {P : Ideal (MvPolynomial (Fin m) (𝓞 K))}
    (hP : P.IsPrime) (hI : P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) ≠ ⊤) {q : MvPolynomial (Fin m) (𝓞 K)}
    (hq : q ∉ P) : MvPolynomial.map (algebraMap (𝓞 K) K) q ∉ P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) (𝓞 K)) (MvPolynomial (Fin m) K) :=
    MvPolynomial.algebraMvPolynomial
  haveI hloc := MvPolynomial.isLocalization (σ := Fin m) (nonZeroDivisors (𝓞 K)) K
  have hdisj : Disjoint (((nonZeroDivisors (𝓞 K)).map (C (σ := Fin m)) : Submonoid (MvPolynomial (Fin m) (𝓞 K))) :
      Set (MvPolynomial (Fin m) (𝓞 K))) (P : Set (MvPolynomial (Fin m) (𝓞 K))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haP
    apply hI
    have hmem : MvPolynomial.map (algebraMap (𝓞 K) K) (C a) ∈ P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) :=
      Ideal.mem_map_of_mem _ haP
    rw [map_C] at hmem
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero ha
    exact Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit ha0).map C)
  intro hmem
  apply hq
  have hc := IsLocalization.under_map_of_isPrime_disjoint (M := (nonZeroDivisors (𝓞 K)).map (C (σ := Fin m)))
    (S := MvPolynomial (Fin m) K) hP hdisj
  rw [← hc, Ideal.mem_comap]
  exact hmem

theorem volume_univ_zero : (volume : Measure (V 0)) univ = 1 := by
  rw [← (stdOrthonormalBasis ℝ (V 0)).volume_parallelepiped]
  congr 1
  refine (Set.eq_univ_of_forall fun x => ?_).symm
  have hx : x = 0 := by
    ext i
    exact i.elim0
  rw [hx]
  exact (mem_parallelepiped_iff _ _).2 ⟨0, Set.left_mem_Icc.2 zero_le_one, by simp⟩

theorem integral_zero {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {p : Z ⟶ Sp R} {σ : R →+* ℂ}
    [SecondCountableTopology (CxPts p σ)] [CompactSpace (CxPts p σ)] {φ : Weight p σ B} (hφ : φ.IsCInf)
    (hc : ∀ y : CxPts p σ, ∃ c : AlgChart p σ 0, y ∈ c.e.source) (G : CxPts p σ → ℝ) :
    ∑ᶠ y, G y = ∫ y, G y ∂φ.chernPart 0 1 := by
  classical
  have hV : ∀ a b : V 0, a = b := fun a b => by
    ext i
    exact i.elim0
  have hsrc : ∀ (c : AlgChart p σ 0) (y : CxPts p σ), y ∈ c.e.source → c.e.source = {y} := by
    intro c y hy
    ext z
    constructor
    · intro hz
      exact c.e.injOn hz hy (hV _ _)
    · rintro rfl
      exact hy
  haveI : DiscreteTopology (CxPts p σ) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro y
    obtain ⟨c, hcy⟩ := hc y
    rw [← hsrc c y hcy]
    exact c.e.open_source
  haveI : Finite (CxPts p σ) := finite_of_compact_of_discrete
  letI := Fintype.ofFinite (CxPts p σ)
  have hμ : φ.chernPart 0 1 = Measure.count := by
    rw [Measure.ext_iff_singleton]
    intro y
    obtain ⟨c, hcy⟩ := hc y
    have himg : (c.e '' {y}) = Set.univ := Set.eq_univ_of_forall fun v => ⟨y, rfl, hV _ _⟩
    rw [Measure.count_singleton,
      Weight.chernPart_apply hφ 1 c (measurableSet_singleton y) (Set.singleton_subset_iff.2 hcy), himg]
    simp [GlobalTheory.AlgChart.chernDens_zero, volume_univ_zero]
  rw [hμ, finsum_eq_sum_of_fintype, integral_fintype Integrable.of_finite]
  simp [Measure.real, Measure.count_singleton]

end ChowFormHeightComparison₂.CF.C

namespace ChowFormHeightComparison₂.CF

open C

theorem stArch (h1 : StPts) (h2 : StCharts) : StArch := by
  unfold StArch
  intro K _ _ Z _ p B m s e hE hAV hChow hproj σ φ h hφ hFS u hu
  obtain ⟨f, hf⟩ := hChow
  haveI : CompactSpace (CxPts p (σ.comp (algebraMap (𝓞 K) K))) := hAV.compactSpace _
  haveI : SecondCountableTopology (CxPts p (σ.comp (algebraMap (𝓞 K) K))) :=
    GlobalTheory.CxPts.secondCountableTopology_of_isProjOver _ hAV.isProjOver
  obtain ⟨hem, hint, hcyc, hnull⟩ := C.cone_side hproj hf σ h hu
  obtain ⟨n, q, hqh, hqP, hqc⟩ := h2 K Z p B m s e hE hAV
  have hPprime : (ptIdeal p s (genericPoint Z)).IsPrime :=
    ((h1 (𝓞 K) Z p B m s hE).1 (genericPoint Z)).isPrime
  have hq' : MvPolynomial.map (algebraMap (𝓞 K) K) q ∉ genIdeal p s :=
    C.map_notMem hPprime hproj.isPrime.ne_top hqP
  have hJzero : ∀ x : Fin m → ℂ,
      (∀ r ∈ Ideal.map (MvPolynomial.map σ) (genIdeal p s), MvPolynomial.eval x r = 0) ↔
        ∀ r ∈ ptIdeal p s (genericPoint Z), eval₂ (σ.comp (algebraMap (𝓞 K) K)) x r = 0 := by
    intro x
    constructor
    · intro hx r hr
      have hx' := hx _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
      rw [MvPolynomial.map_map, MvPolynomial.eval_map] at hx'
      exact hx'
    · intro hx r hr
      have hle : Ideal.map (MvPolynomial.map σ) (genIdeal p s) ≤ RingHom.ker (MvPolynomial.eval x) := by
        rw [Ideal.map_le_iff_le_comap, genIdeal, Ideal.map_le_iff_le_comap]
        intro r' hr'
        rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.map_map, MvPolynomial.eval_map]
        exact hx r' hr'
      exact hle hr
  have hμ0 : μH[↑(2 * (e + 1))] ({0} ∪ coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)) ∩
      {y : EuclideanSpace ℂ (Fin m) | eval₂ (σ.comp (algebraMap (𝓞 K) K)) (h.pointOf y) q = 0}) = 0 := by
    refine measure_union_null (C.hausdorffMeasure_zero e) ?_
    refine measure_mono_null ?_ (hnull _ hq')
    rintro y ⟨hy1, hy2⟩
    refine ⟨hy1, ?_⟩
    simp only [Set.mem_setOf_eq] at hy2 ⊢
    rw [MvPolynomial.map_map, MvPolynomial.eval_map]
    exact hy2
  have hℓs : ∀ t : ℂ, t ≠ 0 → ∀ x : EuclideanSpace ℂ (Fin m),
      fsLog h (fun k => σ (u k)) (h.pointOf (t • x)) = fsLog h (fun k => σ (u k)) (h.pointOf x) := by
    intro t ht x
    rw [HermNorm.pointOf_smul']
    have hsum : ∑ j : Fin m, σ (u j) * (t • h.pointOf x) j = t * ∑ j : Fin m, σ (u j) * h.pointOf x j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [fsLog]
    rw [hsum, HermNorm.dualNorm_smul, norm_mul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 ht)]
  have hpc : Continuous fun y : EuclideanSpace ℂ (Fin m) => h.pointOf y := by
    unfold HermNorm.pointOf
    fun_prop
  have hℓm : Measurable fun y : EuclideanSpace ℂ (Fin m) => fsLog h (fun k => σ (u k)) (h.pointOf y) := by
    simp only [GroundTheory.Heights₂.Heights.ConeFsLog.fsLog_pointOf]
    have hc : Continuous fun y : EuclideanSpace ℂ (Fin m) => ∑ j : Fin m, σ (u j) * h.pointOf y j :=
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hpc)
    exact Real.measurable_log.comp (hc.norm.measurable.div measurable_norm)
  have hgm : Measurable fun y : CxPts p (σ.comp (algebraMap (𝓞 K) K)) =>
      fsLog h (fun k => σ (u k)) (coords p (σ.comp (algebraMap (𝓞 K) K)) hE.isLB s y) := by
    have := C.measurable_coords (h := h) (s := s) (p := p) (σ := σ.comp (algebraMap (𝓞 K) K)) hE.isLB hℓm hℓs
    simpa only [C.pointOf_euc] using this
  have hkey : ∀ G : ℝ → ℝ≥0∞, Measurable G →
      ∫⁻ y in coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)),
          G (fsLog h (fun k => σ (u k)) (h.pointOf y)) ∂μH[↑(2 * (e + 1))] =
        μH[↑(2 * (e + 1))] {y : EuclideanSpace ℂ (Fin m) | ‖y‖ < 1 ∧ ∀ j : Fin m, e + 1 ≤ ↑j → y.ofLp j = 0} *
          ∫⁻ y, G (fsLog h (fun k => σ (u k)) (coords p (σ.comp (algebraMap (𝓞 K) K)) hE.isLB s y))
            ∂φ.chernPart e 1 := by
    intro G hG
    have hc := C.lintegral_cone hE hφ hFS hJzero hqh (hqc _) hμ0
      (F := fun y => G (fsLog h (fun k => σ (u k)) (h.pointOf y))) (hG.comp hℓm) (fun t ht x => by
        simp only [hℓs t ht])
    rw [hc]
    simp only [C.pointOf_euc]
  obtain ⟨-, hgint⟩ := C.integral_of_lintegral (coordBall_mass hem).1.ne' (coordBall_mass hem).2.ne hgm hint hkey
  constructor
  · unfold Weight.chernInt
    rw [C.chernPart_neg hE hφ hFS, Measure.restrict_zero, integral_zero_measure, sub_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero, hgint, hcyc]
    · rfl
    · intro y hy
      simp only [Set.mem_setOf_eq, not_not] at hy
      rw [fsLog, hy, norm_zero, zero_div, Real.log_zero]
  · intro he0
    subst he0
    have hch : ∀ y : CxPts p (σ.comp (algebraMap (𝓞 K) K)), ∃ c : AlgChart p (σ.comp (algebraMap (𝓞 K) K)) 0,
        y ∈ c.e.source := by
      intro y
      refine hqc _ y ?_
      exact C.eval₂_loc_ne_zero (GlobalTheory.TwistTop.under_eq_genericPoint hAV y) (GlobalTheory.CxPts.mem_pick hE.isLB y) hqh hqP
    rw [C.integral_zero hφ hch, hgint, hcyc]
    rfl

end ChowFormHeightComparison₂.CF
end
end

