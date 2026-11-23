module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0011
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0010

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatRat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  filter_upwards [h.compl_mem_cofinite] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [h2]
  exact not_lt.mp hv

def latR {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

def Good {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) : Prop :=
  ∀ k l, algebraMap F (Fv F v) (b.repr (b k * e) l) ∈ v.adicCompletionIntegers F

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (y : Fv F v ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (y * inclR (Fv F v) e) l =
      ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k *
        algebraMap F (Fv F v) (b.repr (b k * e) l) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  simp [inclR, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

theorem mul_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {e : E}
    (he : Good b v e) {y : Fv F v ⊗[F] E} (hy : y ∈ latR b v) : y * inclR (Fv F v) e ∈ latR b v := by
  intro l
  rw [repr_mul]
  exact sum_mem fun k _ => mul_mem (hy k) (he k l)

theorem sum_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ι : Type}
    (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ c ∈ s, f c ∈ latR b v) : ∑ c ∈ s, f c ∈ latR b v := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun c hc => h c hc k

theorem eventually_good {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Good b v e :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_integral _

theorem eventually_good_matrix {d m : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin m) (Fin m) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Good b v (g i j) :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_good b _

omit [NumberField F] in
theorem rmul_rmul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : rmul R (rmul R X A) B = rmul R X (A * B) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [NumberField F] in
theorem rmul_one (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

theorem rmul_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : Matrix (Fin n) (Fin n) E} (hg : ∀ i j, Good b v (g i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v := by
  intro a i
  exact sum_mem_latR _ _ (fun c _ => mul_mem_latR (hg c a) (fun k => hX c i k))

theorem actTup_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : GL (Fin M) E} (hg : ∀ i j, Good b v ((g : Matrix (Fin M) (Fin M) E) i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v := by
  intro a i
  have h : actTup (Fv F v) (bc (inclR (Fv F v)) g) X a i =
      ∑ j, X a j * inclR (Fv F v) ((g : Matrix (Fin M) (Fin M) E) i j) := by
    simp only [actTup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h]
  exact sum_mem_latR _ _ (fun j _ => mul_mem_latR (hg i j) (fun k => hX a j k))

omit [NumberField F] in
theorem actTup_inv {M n : ℕ} (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (bc (inclR R) g⁻¹) (actTup R (bc (inclR R) g) X) = X := by
  funext a
  simp only [actTup, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem one_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F) :
    (1 : Fv F v ⊗[F] E) ∈ latR b v := by
  intro k
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k

theorem consTup_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro hX a i k
    simpa [consTup] using hX a.succ i.succ k
  · intro hX a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consTup] using one_mem_latR h k
      · simp [consTup]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup]
      · simpa [consTup] using hX a i

theorem latV_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b n M
  refine ⟨fun g hg => ?_, fun g => ?_, ?_⟩
  · filter_upwards [eventually_good_matrix b g, eventually_good_matrix b g⁻¹] with v h1 h2 X
    refine ⟨fun hX => ?_, rmul_mem h1⟩
    have hmul : g.map (inclR (F := F) (E := E) (Fv F v)) * g⁻¹.map (inclR (F := F) (E := E) (Fv F v)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg),
        Matrix.map_one _ (map_zero _) (map_one _)]
    have := rmul_mem h2 hX
    rwa [rmul_rmul, hmul, rmul_one] at this
  · filter_upwards [eventually_good_matrix b (g : Matrix (Fin M) (Fin M) E),
      eventually_good_matrix b ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)] with v h1 h2 X
    refine ⟨fun hX => ?_, actTup_mem h1⟩
    have := actTup_mem (g := g⁻¹) h2 hX
    rwa [actTup_inv] at this
  · have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
        algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun k => eventually_integral (b.repr (1 : E) k)
    filter_upwards [h0] with v h X
    exact consTup_mem_iff h X

end GlobalTheory.CompanionTheory.SW.LatRat
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LebesgueSelfdualForDotCharacter
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RealFourier

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fourierChar_smul (t : ℝ) (c : ℂ) :
    (Real.fourierChar t : Circle) • c = c * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

theorem inversion_neg (ι : Type) [Fintype ι] (Φ : (ι → ℝ) → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ)
    (hi : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume)
    (z : ι → ℝ) :
    ∫ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (y ⬝ᵥ z) : ℝ) : ℝ)) = Φ (-z) := by
  have mp := PiLp.volume_preserving_toLp ι
  have emb : MeasurableEmbedding (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  have hin : ∀ x y : ι → ℝ, inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y)
      = x ⬝ᵥ y := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  set Ψ : EuclideanSpace ℝ ι → ℂ := fun u => Φ u.ofLp with hΨ
  have hΨc : Continuous Ψ := hc.comp (PiLp.continuous_ofLp 2 _)
  have hΨi : Integrable Ψ volume :=
    (mp.integrable_comp_emb emb).1 (hc.integrable_of_hasCompactSupport hs)
  have hF : ∀ y : ι → ℝ, FourierTransform.fourier Ψ (WithLp.toLp 2 y) = ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
    intro y
    rw [Real.fourier_eq, ← mp.integral_comp emb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hin, fourierChar_smul, hΨ]
    simp
  have hFi : Integrable (FourierTransform.fourier Ψ) volume := by
    refine (mp.integrable_comp_emb emb).1 ?_
    refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
    exact (hF y).symm
  have hinv := congrFun (hΨc.fourierInv_fourier_eq hΨi hFi) (WithLp.toLp 2 (-z))
  rw [Real.fourierInv_eq, ← mp.integral_comp emb] at hinv
  have hval : Ψ (WithLp.toLp 2 (-z)) = Φ (-z) := rfl
  rw [← hval, ← hinv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hin, fourierChar_smul, hF]
  simp

end GlobalTheory.CompanionTheory.SW.RealFourier

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem selfDual_real_coord : ∀ (ι : Type) [Fintype ι] (ε : ℝ), ε = 1 ∨ ε = -1 →
    SelfDual (volume : Measure (ι → ℝ))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * (ε * (x ⬝ᵥ y) : ℝ))) := by
  intro ι _ ε hε
  refine ⟨inferInstance, fun Φ hc hs hi z => ?_⟩
  rcases hε with rfl | rfl
  ·
    have hG : ∀ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) =
        ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
          Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
      intro y
      rw [← integral_neg_eq_self (fun x : ι → ℝ =>
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hc' : Continuous fun u : ι → ℝ => Φ (-u) := hc.comp continuous_neg
    have hs' : HasCompactSupport fun u : ι → ℝ => Φ (-u) :=
      hs.comp_homeomorph (Homeomorph.neg (ι → ℝ))
    have hi' : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
        Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume :=
      hi.congr (Filter.Eventually.of_forall hG)
    have key := RealFourier.inversion_neg ι (fun u => Φ (-u)) hc' hs' hi' (-z)
    simp only [neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hG y]
    simp
  · exact RealFourier.inversion_neg ι Φ hc hs hi z

end GlobalTheory.CompanionTheory.SW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulVecEqSmul
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ModDet

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem map_mul_unit (lam : Measure K) [lam.IsAddHaarMeasure] (u : Kˣ) :
    lam.map (fun y => (u : K) * y) = (distribHaarChar K u)⁻¹ • lam := by
  have hm : Measurable (fun y : K => (u : K) * y) :=
    (continuous_const.mul continuous_id).measurable
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← map_inv,
    distribHaarChar_mul lam u⁻¹ s]
  congr 1
  ext y
  simp [Set.mem_inv_smul_set_iff, Units.smul_def]

theorem pi_smul_const {ι : Type} [Fintype ι] (lam : Measure K) [SigmaFinite lam] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • lam) = (∏ i, c i) • Measure.pi (fun _ : ι => lam) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    ENNReal.ofNNReal_finsetProd]

theorem pi_map_diag {ι : Type} [Fintype ι] (lam : Measure K) [lam.IsAddHaarMeasure] (D : ι → Kˣ) :
    (Measure.pi fun _ : ι => lam).map (fun x i => (D i : K) * x i) =
      (∏ i, (distribHaarChar K (D i))⁻¹) • Measure.pi fun _ : ι => lam := by
  have hm : ∀ i, Measurable (fun y : K => (D i : K) * y) := fun i =>
    (continuous_const.mul continuous_id).measurable
  have hs : ∀ i, SigmaFinite (lam.map (fun y : K => (D i : K) * y)) := fun i => by
    rw [map_mul_unit]; infer_instance
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [map_mul_unit]
  exact pi_smul_const lam _

theorem smul_cancel (lam : Measure K) [lam.IsAddHaarMeasure] {a b : ℝ≥0}
    (h : a • lam = b • lam) : a = b := by
  obtain ⟨C, hC, hn⟩ := exists_compact_mem_nhds (0 : K)
  have h0 : lam C ≠ 0 := (Measure.measure_pos_of_mem_nhds lam hn).ne'
  have h1 : lam C ≠ ∞ := hC.measure_lt_top.ne
  have e := congrArg (fun m : Measure K => m C) h
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem map_transvections {ι : Type} [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (L : List (Matrix.TransvectionStruct ι K)) :
    μ.map (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) = μ := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
      (continuous_const.matrix_mulVec continuous_id).measurable
    have e : (fun x : ι → K => ((t :: L).map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) =
        (fun x => t.toMatrix *ᵥ x) ∘
          (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
      funext x
      simp [Matrix.mulVec_mulVec]
    rw [e, ← Measure.map_map (hm _) (hm _), ih]
    exact _root_.GlobalTheory.CompanionTheory.SW.transvection_map_addHaar K ι μ t

theorem det_transvections {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι K)) :
    ((L.map Matrix.TransvectionStruct.toMatrix).prod).det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [Matrix.det_mul, ih, Matrix.TransvectionStruct.det]

theorem map_mulVec_eq_smul : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (lam : Measure K) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι K), IsUnit A.det → ∀ c : ℝ≥0,
      lam.map (fun y => A.det * y) = c • lam → μ.map (fun x => A *ᵥ x) = c • μ := by
  intro K _ _ _ _ _ _ _ _ _ _ ι _ _ μ _ lam _ A hA c hc
  obtain ⟨L, L', D, hAeq⟩ := _root_.GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec K ι A
  have hdet : A.det = ∏ i, D i := by
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, det_transvections, det_transvections,
      Matrix.det_diagonal, one_mul, mul_one]
  have hu : ∀ i, IsUnit (D i) := fun i => by
    have h := hA
    rw [hdet, ← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)] at h
    exact isUnit_of_mul_isUnit_left h
  obtain ⟨Du, hDu⟩ : ∃ Du : ι → Kˣ, ∀ i, (Du i : K) = D i :=
    ⟨fun i => (hu i).unit, fun i => (hu i).unit_spec⟩
  have hcc : (∏ i, (distribHaarChar K (Du i))⁻¹) = c := by
    refine smul_cancel lam ?_
    rw [← hc, hdet]
    have e : (∏ i, D i) = ((∏ i, Du i : Kˣ) : K) := by
      simp [Units.coe_prod, hDu]
    rw [e, map_mul_unit, map_prod, Finset.prod_inv_distrib]
  have hμ := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : ι => lam)
  have hmd : Measurable (fun (x : ι → K) i => (Du i : K) * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have hdiag : μ.map (fun (x : ι → K) i => (Du i : K) * x i) = c • μ := by
    rw [hμ, Measure.map_smul, pi_map_diag, hcc, smul_comm]
    exact hmd.aemeasurable
  have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have e : (fun x : ι → K => A *ᵥ x) =
      (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) ∘
        (fun (x : ι → K) i => (Du i : K) * x i) ∘
          (fun x => (L'.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
    funext x
    have hd : ∀ y : ι → K, (fun i => (Du i : K) * y i) = Matrix.diagonal D *ᵥ y := fun y => by
      funext i
      simp [Matrix.mulVec_diagonal, hDu]
    simp only [Function.comp_apply, hd, Matrix.mulVec_mulVec]
    rw [hAeq, Matrix.mul_assoc]
  rw [e, ← Measure.map_map (hm _) (hmd.comp (hm _)), ← Measure.map_map hmd (hm _),
    map_transvections μ L', hdiag, Measure.map_smul, map_transvections μ L]
  exact (hm _).aemeasurable

end GlobalTheory.CompanionTheory.SW.ModDet
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankZeroGramFiberMeasure
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramEmpty

theorem fibre_eq_dirac_of_unique {V X : Type} [MeasurableSpace V] [MeasurableSpace X] [Subsingleton V]
    [Subsingleton X] (μ : Measure V) (ν : Measure X) (m : X → Measure V) (x₀ : V)
    (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1)
    (h : ∀ φ : V → ℝ≥0∞, Measurable φ → ∫⁻ v, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(m b) ∂ν) (S : X) :
    m S = Measure.dirac x₀ := by
  have h1 := h (fun _ => 1) measurable_const
  have hc : (fun b => ∫⁻ _, (1 : ℝ≥0∞) ∂(m b)) = fun _ => m S Set.univ := by
    funext b
    rw [Subsingleton.elim b S]
    simp
  rw [hc] at h1
  simp only [lintegral_const, one_mul, hμ, hν, mul_one] at h1
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [Subsingleton.eq_univ_of_nonempty hs, ← h1]
    simp

end GlobalTheory.CompanionTheory.SW.GramEmpty

open GlobalTheory.CompanionTheory.SW.GramEmpty in
theorem GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ d b lam _ m hm S
  obtain ⟨-, h2, -⟩ := hm
  haveI : Subsingleton (HermR R σ 0) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : IsEmpty {p : Fin 0 × Fin 0 // p.1 < p.2} := ⟨fun p => p.1.1.elim0⟩
  have hU : {X : Fin 0 → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = Set.univ := by
    ext X
    simp
  have hμ : coordW R b lam 0 M Set.univ = 1 := by
    unfold coordW
    rw [Measure.pi_of_empty]
    simp
  have hν : coordHerm R σ b lam 0 Set.univ = 1 := by
    unfold coordHerm
    rw [Measure.comap_apply _ (Function.injective_of_subsingleton _)
      (fun s _ => Subsingleton.measurableSet) _ MeasurableSet.univ]
    have : (Set.univ : Set ((Fin 0 → R) × ({p : Fin 0 × Fin 0 // p.1 < p.2} → R ⊗[F] E))) =
        Set.univ ×ˢ Set.univ := by simp
    rw [Set.image_univ_of_surjective, this, Measure.prod_prod, Measure.pi_of_empty, Measure.pi_of_empty]
    · simp
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  refine fibre_eq_dirac_of_unique _ _ m _ hμ hν (fun φ hφ => ?_) S
  have := h2 φ hφ
  rw [hU, Measure.restrict_univ] at this
  exact this
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquiv
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem selfDual_map_of_comp {V V' : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ)
    (h : SelfDual μ (fun x y => χ (e x) (e y))) : SelfDual (μ.map e) χ := by
  obtain ⟨hH, hF⟩ := h
  let eM : V ≃ᵐ V' := e.toHomeomorph.toMeasurableEquiv
  have hcoe : (eM : V → V') = e := rfl
  have hint : ∀ g : V' → ℂ, ∫ y, g y ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => by
    rw [← hcoe]; exact integral_map_equiv eM g
  refine ⟨e.isAddHaarMeasure_map μ, fun Φ hc hs hi z => ?_⟩
  have hinner : ∀ y : V, ∫ x, Φ x * χ x (e y) ∂(μ.map e)
      = ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ := fun y => hint _
  have hi' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ) μ := by
    have h1 : Integrable ((fun y => ∫ x, Φ x * χ x y ∂(μ.map e)) ∘ eM) μ :=
      (eM.measurableEmbedding.integrable_map_iff).1 (by rw [hcoe]; exact hi)
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hinner y
  have hcs : HasCompactSupport (Φ ∘ e) :=
    hs.comp_homeomorph e.toHomeomorph
  have key := hF (Φ ∘ e) (hc.comp e.continuous) hcs hi' (e.symm z)
  rw [hint]
  simp only [hinner]
  simpa using key

theorem selfDual_transport (V V' : Type) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ) :
    SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  refine ⟨selfDual_map_of_comp e μ χ, fun h => ?_⟩
  have h2 := selfDual_map_of_comp e.symm (μ.map e) (fun x y => χ (e x) (e y)) (by simpa using h)
  have hm : (μ.map e).map e.symm = μ := by
    have m1 : Measurable (e.symm : V' → V) := e.symm.continuous.measurable
    have m2 : Measurable (e : V → V') := e.continuous.measurable
    rw [Measure.map_map m1 m2]
    have : (e.symm : V' → V) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  rwa [hm] at h2

end GlobalTheory.CompanionTheory.SW
end

