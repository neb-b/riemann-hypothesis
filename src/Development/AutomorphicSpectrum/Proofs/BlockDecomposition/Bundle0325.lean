module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0197
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0219
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProduct
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightWordL2LaplacianBound
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobSecK

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_congr (w : List (Ix n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) :
    Set.EqOn (Rw w f) (Rw w h) (GLs n) := by
  induction w with
  | nil => exact e
  | cons p w ih => exact RCalc.Rd_congr (bs p) ih

theorem Rw_smooth (w : List (Ix n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact RCalc.Rd_contDiffOn (bs p) ih

theorem Rw_append (w w' : List (Ix n)) (f : Mat n → V) : Rw w' (Rw w f) = Rw (w' ++ w) f := by
  induction w' with
  | nil => rfl
  | cons p w' ih =>
    show Rd (bs p) (Rw w' (Rw w f)) = Rd (bs p) (Rw (w' ++ w) f)
    rw [ih]

end Words

section HWords

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HWords

section Skew

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Skew

section Bracket

def cf (M : Mat n) (p : Ix n) : ℝ := if p.1 then (M p.2.1 p.2.2).re else (M p.2.1 p.2.2).im

theorem sum_cf (M : Mat n) : ∑ p : Ix n, cf M p • bs p = M := by
  rw [OmDec.sum_Ix]
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ext i j
  simp only [cf, bs, if_true, Bool.false_eq_true, if_false, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · simp only [h, and_self, if_true]
    obtain ⟨rfl, rfl⟩ := h
    simp [Complex.real_smul, Complex.re_add_im]
  · simp [h]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sum_cf (M : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd M f g = ∑ p : Ix n, ((cf M p : ℝ) : ℂ) • Rd (bs p) f g := by
  conv_lhs => rw [← sum_cf M]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Rd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, map_smul]
  exact (Complex.coe_smul _ _).symm

end Bracket

section HBracket

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HBracket

section Sections

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Sections

section Powers

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Powers

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Main

end GlobalTheory.CompanionTheory.SobSecK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeScalingHermitianMeasure
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

theorem map_eq_sqrt_smul {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0)
    (h : ν.map (e ∘ e) = c • ν) : ν.map e = NNReal.sqrt c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul b he.aemeasurable, hb, smul_smul]
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbc : b * b = c := by
    have h3 : ((b * b : ℝ≥0) • ν) K = (c • ν) K := by rw [← h2, h]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  rw [hb, ← hbc, NNReal.sqrt_mul_self]

theorem scalH_scalH {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (a b : R) (S : HermR R σ n) :
    scalH R σ a (scalH R σ b S) = scalH R σ (a * b) S := by
  apply Subtype.ext
  simp only [scalH_coe, smul_smul, map_mul]

theorem scalH_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : scalH R σ 1 S = S := by
  apply Subtype.ext
  simp only [scalH_coe, map_one, one_smul]

def scalEquiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (n : ℕ) (l : F) (hl : l ≠ 0) : HermR R σ n ≃ₜ+ HermR R σ n :=
  have hc : ∀ a : R, Continuous (scalH R σ (n := n) a) := fun a => by
    obtain ⟨iTR, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
    haveI := iTR
    exact Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  have hm : algebraMap F R l * algebraMap F R l⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hl, map_one]
  { toFun := scalH R σ (algebraMap F R l)
    invFun := scalH R σ (algebraMap F R l⁻¹)
    left_inv := fun S => by rw [scalH_scalH, mul_comm, hm, scalH_one]
    right_inv := fun S => by rw [scalH_scalH, hm, scalH_one]
    map_add' := fun S T => by
      apply Subtype.ext
      simp [scalH_coe]
    continuous_toFun := hc _
    continuous_invFun := hc _ }

def oneByOne {F E : Type} [Field F] [Field E] [Algebra F E] (l : F) : Matrix (Fin 1) (Fin 1) E :=
  Matrix.of fun _ _ => algebraMap F E l

theorem action_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (l : F) (S : HermR R σ 1) :
    ((scalH R σ (algebraMap F R l) (scalH R σ (algebraMap F R l) S) : HermR R σ 1) :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R) := by
  have h1 : inclR R (algebraMap F E l) = algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
  have h2 : sigR R σ (algebraMap R (R ⊗[F] E) (algebraMap F R l)) =
      algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  ext i j
  simp only [scalH_coe, cT, oneByOne, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul, h1, h2]
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  subst hi hj
  ring

theorem local_scal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (l : F) (hl : l ≠ 0) (c : ℝ≥0)
    (ν : Measure (HermR R σ 1)) (hν : ν.IsAddHaarMeasure)
    (h : ∀ τ : HermR R σ 1 → HermR R σ 1, (∀ S, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) → ν.map τ = c • ν) :
    ν.map (scalH R σ (algebraMap F R l)) = NNReal.sqrt c • ν := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := iTR
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact map_eq_sqrt_smul (scalEquiv σ hcm R 1 l hl) ν c (h _ (action_eq R σ l))

theorem scal_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  intro F E _ _ _ _ _ σ hcm l hl
  have hdet : (oneByOne l : Matrix (Fin 1) (Fin 1) E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact (map_ne_zero (algebraMap F E)).2 hl
  obtain ⟨ci, c, hu, hi, hv⟩ := _root_.GlobalTheory.CompanionTheory.SW.pf_herm F E σ hcm 1 (oneByOne l) hdet
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  refine ⟨NNReal.sqrt ci, fun v => NNReal.sqrt (c v), (PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ci ci c c hu hu).2.2.2.2.2.1, ?_, ?_⟩
  · intro ν hν
    exact local_scal σ hcm (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1) l hl ci ν hν (hi ν hν)
  · intro v ν hν
    exact local_scal σ hcm (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) l hl (c v) ν hν (hv v ν hν)

end GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFirstCohomologyKernelsExist
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

open TowerAx

section

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}
  (H : TowerAx ρ res p mm)
  (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)

theorem resTot_self
    (h1 : ∀ e t S (h : S ⊆ S) a, res e t S S h a = a) (S : Finset ι) (h : S ⊆ S) (a : H.Tot hc S) :
    H.resTot hc S S h a = a := by
  induction a using (H.ops hc S).induction with
  | h0 => exact map_zero _
  | hof e t a =>
    rw [resTot_of]
    exact congrArg _ (Subtype.ext (h1 _ _ _ _ _))
  | hadd a b ha hb => rw [map_add (f := _), ha, hb]

theorem resTot_resTot
    (h2 : ∀ e t S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res e t S' S'' h' (res e t S S' h a) = res e t S S'' (h.trans h') a)
    (S S' S'' : Finset ι) (h : S ⊆ S') (h' : S' ⊆ S'') (a : H.Tot hc S) :
    H.resTot hc S' S'' h' (H.resTot hc S S' h a) = H.resTot hc S S'' (h.trans h') a := by
  induction a using (H.ops hc S).induction with
  | h0 => simp only [map_zero]
  | hof e t a =>
    rw [resTot_of, resTot_of, resTot_of]
    exact congrArg _ (Subtype.ext (h2 _ _ _ _ _ _ _ _))
  | hadd a b ha hb => simp only [map_add (f := _), ha, hb]

theorem X_smul_bijective_tot
    (h9 : ∀ i e t S, i ∈ S → Function.Bijective (mm i e t S)) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    Function.Bijective fun m : H.Tot hc S =>
      (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) • m := by
  have hS : S.Nonempty := ⟨i, hi⟩
  refine (H.ops hc S).X_smul_bijective i fun e t => ⟨fun a b h => ?_, fun b => ?_⟩
  · exact Subtype.ext ((h9 i (e + 1) t S hi).1 (congrArg Subtype.val h))
  · obtain ⟨a, ha⟩ := (h9 i (e + 1) t S hi).2 (b : T (e + 1) (t + 1) S)
    refine ⟨⟨a, (mem_Ks hS).2 ((h9 i e t S hi).1 ?_)⟩, Subtype.ext ha⟩
    rw [← H.p_mm i e t S a hS, ha, (mem_Ks hS).1 b.2, map_zero]

end

theorem exists_uniform_h1_kernels : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (one : ∀ e (i : ι), T e 0 {i}) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S), (∀ e t S (h : S ⊆ S) a, res e t S S h a = a) → (∀ e t S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res e t S' S'' h' (res e t S S' h a) = res e t S S'' (h.trans h') a) → (∀ e t S S' (h : S ⊆ S') a, S.Nonempty → p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a)) → (∀ j e t S a, S.Nonempty → p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a)) → (∀ j e t S S' (h : S ⊆ S') a, S.Nonempty → res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S'))) → (∀ e t S, S.Nonempty → Function.Surjective (p e t S)) → (∀ e t S, S.Nonempty → LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤) → (∀ e t S, S.Nonempty → Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥) → (∀ i e t S, i ∈ S → Function.Bijective (mm i e t S)) → (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ e (c : ∀ i j : ι, T (e + 1) t {i, j}), (∀ i j, p e t {i, j} (c i j) = 0) → (∀ i j k, res (e + 1) t {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res (e + 1) t {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res (e + 1) t {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, T (e + 1) t {i}, (∀ i, p e t {i} (b i) = 0) ∧ ∀ i j, c i j = res (e + 1) t {i} {i, j} (sub_pair_left i j) (b i) - res (e + 1) t {j} {i, j} (sub_pair_right i j) (b j) := by
  intro ι _ _ R _ _ g ρ T _ _ res p mm one hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have H : TowerAx ρ res p mm := ⟨h3, h4, h5, h6, h7, h8⟩
  obtain ⟨t₀, ht⟩ := _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.serre_cech_pairs ι (MvPolynomial (Fin g) R) (H.Tot hc)
    (fun S => (H.ops hc S).grading) (H.resTot hc) (fun S S' h => H.isGradedMap_resTot hc h)
    (resTot_self H hc h1) (resTot_resTot H hc h2)
    (fun i S hi => X_smul_bijective_tot H hc h9 i S hi)
    (GlobalTheory.T.commuting_operators_uniform_kernel ι R g ρ T res p mm hc H h10) (GlobalTheory.T.commuting_operators_uniform_cokernel ι R g ρ T res p mm hc H h11)
    (GlobalTheory.T.commuting_operators_kernel_lift ι R g ρ T res p mm hc H one h12 h13)
  refine ⟨t₀, fun t htt e c hp hcoc => ?_⟩
  have hne (i j : ι) : ({i, j} : Finset ι).Nonempty := ⟨i, Finset.mem_insert_self _ _⟩
  let c' : ∀ i j : ι, H.Tot hc {i, j} := fun i j =>
    (H.ops hc {i, j}).of e t ⟨c i j, (mem_Ks (hne i j)).2 (hp i j)⟩
  obtain ⟨b', -, hcob⟩ := ht t htt c' (fun i j => (H.ops hc {i, j}).of_mem_grading e t _) (by
    intro i j k
    simp only [c', resTot_of, ← map_add (f := _)]
    exact congrArg _ (Subtype.ext (hcoc i j k)))
  refine ⟨fun i => ((H.ops hc {i}).comp e t (b' i) : T (e + 1) t {i}), fun i =>
    (mem_Ks (Finset.singleton_nonempty i)).1 ((H.ops hc {i}).comp e t (b' i)).2, fun i j => ?_⟩
  have h := congrArg (fun m => (((H.ops hc {i, j}).comp e t m : Ks p e t {i, j}) : T (e + 1) t {i, j}))
    (hcob i j)
  simpa [c', comp_resTot] using h

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatCoverGlue


set_option maxHeartbeats 1000000 in
theorem glue {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k)
    (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c))
    (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory),
      stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj)
    (hloc : ∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective
      (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j)) (j : ℕ) :
    Function.Bijective
      (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  have hGU : ∀ (α : U.ι) (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory), InU (U.U α) T.obj →
      InU (U.U α) (m.G.obj ⟨T.obj, T.property.1⟩).obj := fun α T hT => by
    obtain ⟨-, V, rfl, hV⟩ := hG {U.U α} ⟨T.obj, T.property.1, U.U α, rfl, hT⟩
    exact hV
  refine cover_bij ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
      (IdF.span _ c) (fun _ => le_rfl))
    (fun α T => InU (U.U α) T.obj) (fun α T => InU (U.U α) T.obj) (fun α T T' φ hT => Site.inU_hom φ.hom hT)
    (fun α T T' φ hT => Site.inU_hom φ.hom hT) (fun T => ?_) (fun T => ?_) (fun α T hT => hGU α T hT)
    (fun S hS j => ?_) j
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  have h₁ : ∀ (r : ℕ) T, stF q ρ r {⨅ α ∈ S, U.U α} T →
      ∃ hp : stF q ρ r (Set.range U.U) T,
        capS (fun α (T : (stF q ρ r (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun r T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have a₀ := nestAdj (h₁ n) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  have a₁ := nestAdj (h₁ (n + 1)) (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  let rL : CH.Mor ((capS (fun α (T : (stF q ρ n (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      CH.modF (sV q ρ n (Set.range U.U)).A) (CH.modF (sV q ρ n {⨅ α ∈ S, U.U α}).A) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ n))
  let rO : CH.Mor ((capS (fun α (T : (stF q ρ (n + 1) (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      sq (IdF.top (sV q ρ (n + 1) (Set.range U.U)).A) (IdF.span (sV q ρ (n + 1) (Set.range U.U)).A c))
      (sq (IdF.top (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A) (IdF.span (sV q ρ (n + 1) {⨅ α ∈ S, U.U α}).A c)) (RingHom.id _) :=
    CH.Mor.restrict _ (nestF (h₁ (n + 1)))
  have bL : Function.Bijective (rL.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₀ j
  have bO : Function.Bijective (rO.pull j) := CrystallineSemistableComparison.P.adj _ _ _ a₁ j
  refine (Function.Bijective.of_comp_iff' bO _).1 ?_
  have e : ∀ x, rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x) =
      ((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl)).pull j (rL.pull j x) := by
    intro x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) _ rO j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id _) rL _ j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id _) _ _ (𝟙 _) (fun T y => ?_) j x
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  have e2 := funext e
  refine (show Function.Bijective (fun x => rO.pull j ((morU ((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o
        (IdF.span _ c) (fun _ => le_rfl))
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hGU α T (hT α hα)).pull j x)) from ?_)
  rw [e2]
  exact (hloc S hS j).comp bL

end GlobalTheory.CompanionTheory.FlatCoverGlue
end
end

