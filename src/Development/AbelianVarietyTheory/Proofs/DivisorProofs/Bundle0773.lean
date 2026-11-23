module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitNormVectorIsotropicHermitian
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_local_unitNorm_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  intro F E _ _ _ _ _ σ hcm K _ _ M J hM hJ hiso x y hx hy
  have hinj : Function.Injective (inclR (F := F) K : E →+* K ⊗[F] E) := Algebra.TensorProduct.includeRight_injective (algebraMap F K).injective
  have hne : ∀ z : Fin M → E, hE σ J z z ≠ 0 → ((fun i => inclR K (z i)) : Fin M → K ⊗[F] E) ≠ 0 := by
    intro z hz h0
    apply hz
    have hz0 : z = 0 := funext fun i => hinj (by simpa using congrFun h0 i)
    subst hz0
    simp [hE, Formalism.UG.hform]
  rcases _root_.GlobalTheory.NormDichotomy.unit_or_norm F E σ hcm K with hfld | hspl
  · exact _root_.GlobalTheory.PlaneNorm.FieldCase.exists_unitNorm_pair F E σ hcm K M J hJ hfld hiso _ _ (hne x hx) (hne y hy)
  · obtain ⟨w, hxw, hwy⟩ := GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne F E σ hcm M J hM hJ x y hx hy
    have hs : ∀ e : E, sigR K σ (inclR K e) = inclR K (σ e) := fun e => rfl
    have hRE : ∀ a b : Fin M → E, hR K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (hE σ J a b) := by
      intro a b
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, hs, JR, Matrix.map_apply, RingHom.coe_coe]
    have hG : ∀ a b : Fin M → E, gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)) =
        inclR K (gram2E σ J a b) := by
      intro a b
      simp only [gram2R, gram2E, hRE, map_sub, map_mul]
    have hsym : ∀ a b : Fin M → E, σ (hE σ J a b) = hE σ J b a := by
      intro a b
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, GlobalTheory.HermLineZeros.conj_invol hcm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hJ.1]
      ring
    have hfix : ∀ a b : Fin M → E, σ (gram2E σ J a b) = gram2E σ J a b := by
      intro a b
      simp only [gram2E, map_sub, map_mul, hsym]
      ring
    have key : ∀ a b : Fin M → E, gram2E σ J a b ≠ 0 →
        IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i)))) := by
      intro a b hab
      obtain ⟨g, hg⟩ := GlobalTheory.HermLineZeros.exists_of_fixed hcm _ (hfix a b)
      have hg0 : g ≠ 0 := by rintro rfl; exact hab (by rw [← hg, map_zero])
      have hk : algebraMap F K (-g) ≠ 0 := by
        rw [map_neg, neg_ne_zero, ne_eq, map_eq_zero_iff _ (algebraMap F K).injective]; exact hg0
      obtain ⟨t, ht⟩ := hspl _ hk
      have hval : -(gram2R K σ J (fun i => inclR K (a i)) (fun i => inclR K (b i))) =
          algebraMap K (K ⊗[F] E) (algebraMap F K (-g)) := by
        rw [hG, ← hg, map_neg, map_neg]
        congr 1
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes g
      have hu : IsUnit (t * sigR K σ t) := by
        rw [ht]; exact (IsUnit.mk0 _ hk).map _
      exact ⟨t, isUnit_of_mul_isUnit_left hu, by rw [ht, hval]⟩
    exact ⟨fun i => inclR K (w i), key x w hxw, key w y hwy⟩

end GlobalTheory.PlaneNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem exists_rapid_superposition_characters :
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  intro Z _ _ _ Φ hΦ hc
  obtain ⟨m, A, φ, hφ, hint, hinv⟩ := GlobalTheory.fourier_inversion_real_linear_forms (hc.toSchwartzMap hΦ)
  let B : EuclideanSpace ℝ (Fin m) →L[ℝ] (Z →L[ℝ] ℝ) := (2 * Real.pi)⁻¹ • A
  have hB : ∀ w z, 2 * Real.pi * B w z = A w z := by
    intro w z
    have : (2 * Real.pi) ≠ 0 := by positivity
    simp only [B, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨EuclideanSpace ℝ (Fin m), inferInstance, volume, inferInstance, φ, fun w => B w,
    hφ.measurable, fun z => ?_, fun N => ?_, fun z => ?_⟩
  · exact (by fun_prop : Continuous fun x => B x z).measurable
  · refine ((hint N).const_mul ((1 + ‖B‖) ^ N)).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (by fun_prop : Continuous fun x => ‖φ x‖ * (1 + ‖B x‖) ^ N).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc, ← mul_pow, mul_comm]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ N) (norm_nonneg _)
      have h1 := B.le_opNorm w
      nlinarith [norm_nonneg B, norm_nonneg w]
  · have h := hinv z
    have h0 : (hc.toSchwartzMap hΦ) z = Φ z := rfl
    rw [h0] at h
    rw [h]
    congr 1
    ext w
    rw [Real.fourierChar_apply, hB]

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularSectionOfRegularDifferences
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_section_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ →
    (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ U : A.left.affineOpens, ∃ k : (Fin g → ℂ) → ℂ,
    ∀ i, IsReg u.ex (U.1 ⊓ W i) (k - h i) := by
  intro A _ g L u hA K W h hcov hreg U
  obtain ⟨-, -, -, -, hinf, -, -, -, hres, he, -, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  have hres' : ∀ (V V' : A.left.Opens) (hle : V' ≤ V) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V',
      val u.ex V' ((A.left.presheaf.map (homOfLE hle).op).hom b) z = val u.ex V b z :=
    fun V V' hle b z hz ↦ hres V V' hle b z hz
  have vsub : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b - c) z = val u.ex V b z - val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_sub e (show Sec (str A) V from b) c
  have vadd : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b + c) z = val u.ex V b z + val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_add e (show Sec (str A) V from b) c
  have vneg : ∀ (V : A.left.Opens) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (-b) z = - val u.ex V b z := by
    intro V b z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he']
    exact map_neg e (show Sec (str A) V from b)
  choose b hb using hreg
  have hle : ∀ i j, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ≤ W i ⊓ W j :=
    fun i j ↦ inf_le_inf inf_le_right inf_le_right
  let f : ∀ i j, Γ(A.left, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := fun i j ↦
    (A.left.presheaf.map (homOfLE (hle i j)).op).hom (b i j)
  have hf : ∀ i j, ∀ z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)), val u.ex _ (f i j) z = h i z - h j z := by
    intro i j z hz
    rw [hres' _ _ (hle i j) (b i j) z hz]
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := (hinf _ _).symm ▸ (by
      rw [hinf, hinf, hinf] at hz
      exact ⟨hz.1.2, hz.2.2⟩)
    rw [← hb i j z hz']
    rfl
  have hcoc : ∀ i j k, (A.left.presheaf.map (homOfLE (inf_le_left : (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j))).op).hom (f i j) +
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k))).op).hom (f j k) =
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W i) ⊓ (U.1 ⊓ W k))).op).hom (f i k) := by
    intro i j k
    rw [← sub_eq_zero]
    refine _root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA _ _ fun z hz ↦ ?_
    have hz3 := hz
    rw [hinf, hinf, hinf, hinf, hinf] at hz3
    rw [vsub _ _ _ z hz, vadd _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz,
      hf i j z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.1.2.1, hz3.1.2.2⟩),
      hf j k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.2.1, hz3.1.2.2⟩, hz3.2.1, hz3.2.2⟩),
      hf i k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.2.1, hz3.2.2⟩)]
    ring
  have hcov' : U.1 ≤ ⨆ i, U.1 ⊓ W i := by
    rw [← inf_iSup_eq, hcov, inf_top_eq]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CechPer.cech_one_cocycle_split A.left U.1 U.2 K (fun i ↦ U.1 ⊓ W i) (fun i ↦ inf_le_left) hcov' f hcoc
  have key : ∀ i j z, z ∈ pre u.ex (U.1 ⊓ W i) → z ∈ pre u.ex (U.1 ⊓ W j) →
      h i z - val u.ex _ (a i) z = h j z - val u.ex _ (a j) z := by
    intro i j z hi hj
    have hz : z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := by rw [hinf]; exact ⟨hi, hj⟩
    have h1 := hf i j z hz
    rw [ha i j, vsub _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz] at h1
    linear_combination -h1
  classical
  refine ⟨fun z ↦ if hz : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) then
      h hz.choose z - val u.ex _ (a hz.choose) z else 0, fun i ↦ ⟨-(a i), fun z hz ↦ ?_⟩⟩
  have hex : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) := ⟨i, hz⟩
  simp only [Pi.sub_apply, dif_pos hex]
  rw [key _ i z hex.choose_spec hz, vneg _ _ z hz]
  ring

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCompactPartitionOnCompact
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff Manifold

namespace GlobalTheory

theorem exists_smooth_compact_partition_on_compact :
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (K : Set Z),
    IsCompact K → ∀ (ι : Type) [Fintype ι] (U : ι → Set Z), (∀ i, IsOpen (U i)) →
    K ⊆ ⋃ i, U i → ∃ φ : ι → Z → ℂ, (∀ i, ContDiff ℝ ∞ (φ i) ∧ HasCompactSupport (φ i) ∧
      tsupport (φ i) ⊆ U i) ∧ ∀ z ∈ K, ∑ i, φ i z = 1 := by
  intro Z _ _ _ K hK ι _ U hU hKU
  classical
  haveI : ProperSpace Z := FiniteDimensional.proper ℝ Z
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Z)
  have hcov : K ⊆ ⋃ i, U i ∩ Metric.ball (0 : Z) R := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKU hz)
    exact Set.mem_iUnion.2 ⟨i, hi, hR hz⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ Z)
    hK.isClosed (fun i => U i ∩ Metric.ball (0 : Z) R)
    (fun i => (hU i).inter Metric.isOpen_ball) hcov
  have hρs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i) := fun i =>
    contMDiff_iff_contDiff.1 (ρ i).contMDiff
  refine ⟨fun i z => ((ρ i z : ℝ) : ℂ), fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hρs i)
  · have h1 : tsupport (fun z => ((ρ i z : ℝ) : ℂ)) ⊆ tsupport (ρ i) :=
      tsupport_comp_subset Complex.ofReal_zero _
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Z) R) (isClosed_tsupport _) ?_
    exact h1.trans ((hρ i).trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
  · exact (tsupport_comp_subset Complex.ofReal_zero _).trans ((hρ i).trans Set.inter_subset_left)
  · intro z hz
    have h2 := ρ.sum_eq_one hz
    rw [finsum_eq_sum_of_fintype] at h2
    simp only
    rw [← Complex.ofReal_sum, h2, Complex.ofReal_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZeroSectionValueInPowerFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeroSection_value_in_powerFrame : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))), L.IsLB → eA.IsGen → ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  first | (exact @GlobalTheory.HomFixUnivVals.vals) | (exact GlobalTheory.HomFixUnivVals.vals) | (intros; apply GlobalTheory.HomFixUnivVals.vals  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIpAtNonneg
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)
open scoped ComplexOrder

namespace GlobalTheory.ColumnFamilyMetric

open GlobalTheory.PeriodClassSum GlobalTheory.TestLat.Compare

theorem chF_gramV (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg)
    (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (b : (chF W sel mu I u j).β) :
    ((chF W sel mu I u j).mem b).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u j) := by
  ext i k
  have e : gramKd X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  show pairK (W.lamTrue u j) (gramKd X.emb 1) (bVV _ _ i) (bVV _ _ k) = _
  rw [e]
  exact pairK_one_basis (W.lamTrue u j) i k

theorem famIpAt_nonneg : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok) (v : InfinitePlace X.K) (φ : (chF W sel mu I u j).Forms), 0 ≤ (famIpAt (chF W sel mu I u j) h v φ φ).re := by
  intro X Pr R W sel Sg mu I u j h v φ
  refine (Complex.nonneg_iff.1 ?_).1
  unfold famIpAt
  refine Finset.sum_nonneg fun b _ => ?_
  have hG : ((((chF W sel mu I u j).mem b).gramV).map v.embedding).PosSemidef := by
    rw [chF_gramV]
    exact (gramB_posDef (W.lamTrue u j) v.embedding).posSemidef
  letI := (h b).fintypeCl
  exact (ipAt_eq _ (h b) v _ _).symm ▸ wForm_nonneg _ hG _

end GlobalTheory.ColumnFamilyMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitarySheafContinuousBaseChangeLevelwiseQcqsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitarySheaf_continuous_baseChange_levelwiseQcqs : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S), QcqsOver p → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((bc p).mapCone c)) := by
  first
  | exact @GlobalTheory.EtC.contCone_bc_qcqsOver
  | exact GlobalTheory.EtC.contCone_bc_qcqsOver
  | (intros; apply GlobalTheory.EtC.contCone_bc_qcqsOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFieldCharacterLabelsCompatNormPowInv
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.LabelNorm

variable {p : ℕ} [Fact p.Prime]

theorem sub_pos' {d : ℕ} (hd : 0 < d) : 0 < p ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)

theorem theta_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left h]
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hfin : IsOfFinOrder (L.gen d) := isOfFinOrder_iff_pow_eq_one.2 ⟨_, sub_pos' hd, hp.pow_eq_one⟩
  have hm : n ≡ h.choose [MOD p ^ d - 1] := by
    rw [← L.gen_order d hd]; exact hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  have h1 : L.teich x ^ (p ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod h.choose h1, pow_eq_pow_mod n h1, hm]

theorem exists_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    ∃ n : ℕ, z = L.gen d ^ n := by
  haveI : NeZero (p ^ d - 1) := ⟨(sub_pos' hd).ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact ⟨n, hn.symm⟩

theorem tor_pow {d : ℕ} (u : Tor p d) : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]

theorem base_pow (c : (ZMod p)ˣ) : algebraMap (ZMod p) (Fbar p) c ^ (p ^ 1 - 1) = 1 :=
  tor_pow (toTorOne p c)

theorem labels_norm_pow (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ)
    (x : Fbar p) (n : ℕ) (hθ : LabelsChar L θ x) : LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n) := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos h hN
  have hx : (x ^ n) ^ (p ^ N - 1) = 1 := by
    obtain ⟨k, hk⟩ := Nat.pow_sub_one_dvd_pow_sub_one p h
    rw [hk, ← pow_mul, mul_comm n, pow_mul, pow_mul, hθ.1, one_pow, one_pow]
  refine ⟨hx, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow L hN (tor_pow u)
  have hn : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) = L.gen d ^ k := by
    have e : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) =
        ((u : (Fbar p)ˣ) : Fbar p) ^ ((p ^ N - 1) / (p ^ d - 1)) := Units.val_pow_eq_pow_val _ _
    obtain ⟨e', rfl⟩ := h
    rw [e, hk, ← pow_mul, mul_comm k, pow_mul, L.gen_norm d e' hd (Nat.pos_of_mul_pos_left hN)]
  rw [hk, theta_gen_pow L hN hx, MonoidHom.pow_apply, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, hθ.2, hn,
    theta_gen_pow L hd hθ.1, map_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem labels_base (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) :
    LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have h1 : LabelsChar L (χ.comp ((MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).symm :
      Tor p 1 →* (ZMod p)ˣ)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
    refine ⟨base_pow a, fun u => ?_⟩
    obtain ⟨v, rfl⟩ := (MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).surjective u
    rw [MonoidHom.comp_apply, MonoidHom.coe_coe, MulEquiv.symm_apply_apply, ← h v]
    rfl
  have h2 := labels_norm_pow L hN 1 (one_dvd N) _ _ 1 h1
  rw [pow_one, pow_one] at h2
  exact h2

theorem labels_inv (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) : LabelsTame L χ⁻¹ a⁻¹ := by
  intro u
  obtain ⟨k, hk⟩ := exists_pow L one_pos (base_pow u)
  have h1 := h u
  rw [hk, theta_gen_pow L one_pos (base_pow a)] at h1
  rw [hk, theta_gen_pow L one_pos (base_pow a⁻¹), MonoidHom.inv_apply, Units.val_inv_eq_inv_val (χ u), ← h1,
    ← inv_pow]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (N : ℕ), 0 < N → (∀ (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ) (x : Fbar p) (n : ℕ), LabelsChar L θ x → LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n)) ∧ ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a → LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) ∧ LabelsTame L χ⁻¹ a⁻¹ :=
  fun _ _ L _ hN => ⟨labels_norm_pow L hN, fun χ a h => ⟨labels_base L hN χ a h, labels_inv L χ a h⟩⟩

end GlobalTheory.LabelNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  first | (exact @GlobalTheory.HomFixUniv.isGen_of_matRel) | (exact GlobalTheory.HomFixUniv.isGen_of_matRel) | (intros; apply GlobalTheory.HomFixUniv.isGen_of_matRel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_generatingCombinationMatrixLocus : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  first | (exact @GlobalTheory.HomFixOpen.main) | (exact GlobalTheory.HomFixOpen.main) | (intros; apply GlobalTheory.HomFixOpen.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubschemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearNormalisation_closed_subscheme : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.HomFixUniv.normal_closed) | (exact GlobalTheory.HomFixUniv.normal_closed) | (intros; apply GlobalTheory.HomFixUniv.normal_closed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormClassSumMatrixLeCauchySchwarzStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ), 0 ≤ t → 0 ≤ h → 0 ≤ h' → (∀ b, PosAt ((Q.F i).mem b) v) → (∀ b, PosAt ((Q.F (i + 1)).mem b) v) → (∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) → (∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h') → (∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) → ∀ φ : (Q.F i).Forms, (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤ (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  first | exact @GlobalTheory.ColNorms.SumBound.step_le | exact GlobalTheory.ColNorms.SumBound.step_le | (intros; apply GlobalTheory.ColNorms.SumBound.step_le <;> assumption)
end

