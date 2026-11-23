module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasure
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

section Gen

variable {H : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem exists_scale (ν : Measure H) [ν.IsAddHaarMeasure] (e : H ≃ₜ+ H) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ν.map e = c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  exact ⟨Measure.addHaarScalarFactor (ν.map e) ν,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem map_eq_of_sq_conj (ν : Measure H) [ν.IsAddHaarMeasure] (A B D : H ≃ₜ+ H)
    (h1 : ∀ x, B x = A (A x)) (h2 : ∀ x, B (D x) = D (A x)) : ν.map A = ν := by
  obtain ⟨c, hc0, hc⟩ := exists_scale ν A
  obtain ⟨d, hd0, hd⟩ := exists_scale ν D
  obtain ⟨b, -, hb⟩ := exists_scale ν B
  have mA : Measurable A := A.continuous.measurable
  have mB : Measurable B := B.continuous.measurable
  have mD : Measurable D := D.continuous.measurable
  have e1 : b • ν = (c * c) • ν := by
    rw [← hb]
    have : (B : H → H) = A ∘ A := funext h1
    rw [this, ← Measure.map_map mA mA, hc, Measure.map_smul c mA.aemeasurable, hc, smul_smul]
  have e2 : (d * b) • ν = (c * d) • ν := by
    have h3 : (B : H → H) ∘ D = D ∘ A := funext h2
    have l : (ν.map D).map B = (d * b) • ν := by
      rw [hd, Measure.map_smul d mB.aemeasurable, hb, smul_smul]
    have r : (ν.map A).map D = (c * d) • ν := by
      rw [hc, Measure.map_smul c mD.aemeasurable, hd, smul_smul]
    rw [← l, ← r, Measure.map_map mB mD, Measure.map_map mD mA, h3]
  obtain ⟨Kc, hK, hKn⟩ := exists_compact_mem_nhds (0 : H)
  have hpos : ν Kc ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have htop : ν Kc ≠ ⊤ := hK.measure_lt_top.ne
  have cancel : ∀ u v : ℝ≥0, u • ν = v • ν → u = v := by
    intro u v h
    have := congrArg (fun m : Measure H => m Kc) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    exact_mod_cast (ENNReal.mul_left_inj hpos htop).1 this
  have hb' := cancel _ _ e1
  have hcd := cancel _ _ e2
  have hc1 : c = 1 := by
    rw [hb'] at hcd
    have : (c * d) * c = (c * d) * 1 := by
      calc (c * d) * c = d * (c * c) := by ring
        _ = c * d := hcd
        _ = (c * d) * 1 := (mul_one _).symm
    exact mul_left_cancel₀ (mul_ne_zero hc0 hd0) this
  rw [hc, hc1, one_smul]

end Gen

section Mat

open HeckeCharacterZeroLocus.SiegelWeilU (cT)

variable {K : Type} [CommRing K] (s : K →+* K) {n : ℕ}

theorem cT_one : cT s (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.cT
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem conj_conj (g h S : Matrix (Fin n) (Fin n) K) :
    cT s h * (cT s g * S * g) * h = cT s (g * h) * S * (g * h) := by
  rw [HeckeCharacterZeroLocus.SiegelWeilU.cT_mul]
  simp only [Matrix.mul_assoc]

theorem shearM_zero (a : Fin n) : shearM a (0 : Fin n → K) = 1 := by
  ext i j
  simp [shearM]

theorem shearM_mul (a : Fin n) (x y : Fin n → K) (hy : y a = 0) :
    shearM a x * shearM a y = shearM a (x + y) := by
  have hN : (Matrix.of (fun b c => if c = a then x b else 0) *
      Matrix.of (fun b c => if c = a then y b else 0) : Matrix (Fin n) (Fin n) K) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = a
    · subst hk
      by_cases hj : j = k <;> simp [hj, hy]
    · simp [hk]
  rw [shearM, shearM, shearM, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hN, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, add_zero]
  ext i j
  by_cases hj : j = a
  · simp [hj]
    ring
  · simp [hj]

def diagAt (a : Fin n) (t : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun i => if i = a then t else 1

theorem diagAt_mul (a : Fin n) (t u : K) (h : t * u = 1) : diagAt a t * diagAt a u = 1 := by
  rw [diagAt, diagAt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = a <;> simp [hi, h]

theorem diagAt_shearM (a : Fin n) (x : Fin n → K) (hx : x a = 0) :
    diagAt a 2 * shearM a (x + x) = shearM a x * diagAt a 2 := by
  ext i j
  rw [diagAt, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [shearM, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  by_cases hj : j = a
  · subst hj
    by_cases hi : i = j
    · subst hi
      simp [hx]
    · simp [Matrix.one_apply, hi] <;> ring
  · by_cases hij : i = j
    · subst hij
      simp [hj]
    · rw [Matrix.one_apply_ne hij]
      simp [hj]

variable [TopologicalSpace K] [IsTopologicalRing K]

def conjEq (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cT s g * S * g ∈ H)
    (g g' : Matrix (Fin n) (Fin n) K) (h1 : g * g' = 1) (h2 : g' * g = 1) : H ≃ₜ+ H where
  toFun S := ⟨cT s g * S * g, hH _ S.2 g⟩
  invFun S := ⟨cT s g' * S * g', hH _ S.2 g'⟩
  left_inv S := Subtype.ext (by
    change cT s g' * (cT s g * (S : Matrix (Fin n) (Fin n) K) * g) * g' = S
    rw [conj_conj, h1, cT_one, Matrix.one_mul, Matrix.mul_one])
  right_inv S := Subtype.ext (by
    change cT s g * (cT s g' * (S : Matrix (Fin n) (Fin n) K) * g') * g = S
    rw [conj_conj, h2, cT_one, Matrix.one_mul, Matrix.mul_one])
  map_add' S T := Subtype.ext (by
    change cT s g * ((S : Matrix (Fin n) (Fin n) K) + T) * g = cT s g * S * g + cT s g * T * g
    rw [Matrix.mul_add, Matrix.add_mul])
  continuous_toFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

theorem conjEq_val (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cT s g * S * g ∈ H)
    (g g' : Matrix (Fin n) (Fin n) K) (h1 : g * g' = 1) (h2 : g' * g = 1) (S : H) :
    (conjEq s H hH g g' h1 h2 S : Matrix (Fin n) (Fin n) K) = cT s g * S * g := rfl

theorem map_shear (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cT s g * S * g ∈ H)
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsAddHaarMeasure] (h2 : IsUnit (2 : K)) (a : Fin n) (x : Fin n → K) (hx : x a = 0)
    (τ : H → H) (hτ : ∀ S, (τ S : Matrix (Fin n) (Fin n) K) = cT s (shearM a x) * S * shearM a x) :
    ν.map τ = ν := by
  have inv : ∀ y : Fin n → K, y a = 0 → shearM a y * shearM a (-y) = 1 ∧ shearM a (-y) * shearM a y = 1 := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [shearM_mul a _ _ (by simp [hy]), add_neg_cancel, shearM_zero]
    · rw [shearM_mul a _ _ hy, neg_add_cancel, shearM_zero]
  have hxx : (x + x) a = 0 := by simp [hx]
  obtain ⟨i1, i2⟩ := inv x hx
  obtain ⟨j1, j2⟩ := inv (x + x) hxx
  have d1 : diagAt a (2 : K) * diagAt a ((h2.unit⁻¹ : Kˣ) : K) = 1 :=
    diagAt_mul a _ _ (h2.mul_val_inv)
  have d2 : diagAt a ((h2.unit⁻¹ : Kˣ) : K) * diagAt a (2 : K) = 1 :=
    diagAt_mul a _ _ (h2.val_inv_mul)
  have hτe : τ = conjEq s H hH _ _ i1 i2 := funext fun S => Subtype.ext (hτ S)
  rw [hτe]
  refine map_eq_of_sq_conj ν _ (conjEq s H hH _ _ j1 j2) (conjEq s H hH _ _ d1 d2) ?_ ?_
  · intro S
    apply Subtype.ext
    rw [conjEq_val, conjEq_val, conjEq_val, conj_conj, shearM_mul a _ _ hx]
  · intro S
    apply Subtype.ext
    rw [conjEq_val, conjEq_val, conjEq_val, conjEq_val, conj_conj, conj_conj, diagAt_shearM a x hx]

end Mat

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

theorem coordHerm_map_shear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) * S * GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  intro F E _ _ _ _ _ σ hσ n d b lam hlam a s hs τ _ hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, -, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hH n
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  have hinv : ∀ x : Ainf F ⊗[F] E, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ x) = x :=
    GlobalTheory.CompanionTheory.SW.GramAlg.sigR_invol (Ainf F) (GlobalTheory.CompanionTheory.SW.GramAlg.sigma_invol hσ)
  have hmem : ∀ S ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, ∀ g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n := by
    intro S hS g
    have hS' : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) S = S := by
      ext i j
      exact hS i j
    have key : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ)
        (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g)
        = HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g := by
      rw [HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, GlobalTheory.CompanionTheory.SW.GramAlg.cT_cT _ hinv, hS', Matrix.mul_assoc]
    intro i j
    exact congrFun (congrFun key i) j
  have h2 : IsUnit (2 : Ainf F ⊗[F] E) := by
    have : IsUnit (algebraMap F (Ainf F ⊗[F] E) 2) := (IsUnit.mk0 (2 : F) two_ne_zero).map _
    rwa [map_ofNat] at this
  exact map_shear (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) hmem
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n) h2 a s hs τ hτ

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7} {n t : ℕ} {B W : HSp D}

def c1 (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : Mx D a W.rank :=
  U.submatrix id fun j => finCongr hn (Fin.castAdd t j)

def c2 (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : Mx D a t :=
  U.submatrix id fun j => finCongr hn (Fin.natAdd W.rank j)

def ww (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) : Mx D W.rank W.rank :=
  mm (mt W h⁻¹) (rat x₀)

def ac (V : HSp D) {a b : ℕ} (g : GA D V) (z : Mx D V.rank a × Mx D V.rank b) : Mx D V.rank a × Mx D V.rank b :=
  (mm (mt V g) z.1, mm (mt V g) z.2)

abbrev Par (D : D7) (n t : ℕ) (W : HSp D) : Type := GA D W × Mx D t n × Mx D W.rank t

def zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (p : Par D n t W) :
    Mx D B.rank W.rank × Mx D B.rank t :=
  (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1),
    mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1))

def Q0 {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) : Measure (Par D n t W) :=
  I.m.prod (I.μ₁.prod μ)

def rho {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Measure (Mx D B.rank W.rank × Mx D B.rank t) :=
  (Q0 I μ).map (zp d hn x₀)

def nuT {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Measure (Mx D B.rank W.rank × Mx D B.rank t) :=
  (I.νK.prod (Q0 I μ)).map fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting
variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem top_mx (a b : ℕ) : IsTopologicalAddGroup (Mx D a b) ∧ LocallyCompactSpace (Mx D a b) ∧ SecondCountableTopology (Mx D a b) ∧
    T2Space (Mx D a b) ∧ BorelSpace (Mx D a b) := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  exact ⟨i1, i2, i3, i4, ⟨rfl⟩⟩

theorem continuous_first_column_block (hn : W.rank + t = n) {a : ℕ} : Continuous (c1 (D := D) (W := W) hn (a := a)) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_second_column_block (hn : W.rank + t = n) {a : ℕ} : Continuous (c2 (D := D) (W := W) hn (a := a)) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_ww (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Continuous (ww W x₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  exact ((continuous_mt W).comp continuous_inv).matrix_mul continuous_const

theorem continuous_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous (zp d hn x₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hT := (top_mx (D := D) B.rank W.rank).1
  have hT2 := (top_mx (D := D) B.rank t).1
  have h1 : Continuous fun p : Par D n t W => mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1) :=
    (continuous_const.matrix_mul ((continuous_first_column_block hn).comp (continuous_fst.comp continuous_snd))).add
      (continuous_const.matrix_mul ((continuous_ww x₀).comp continuous_fst))
  exact h1.prodMk ((h1.matrix_mul (continuous_snd.comp continuous_snd)).add
    (continuous_const.matrix_mul ((continuous_second_column_block hn).comp (continuous_fst.comp continuous_snd))))

theorem continuous_ac (V : HSp D) {a b : ℕ} :
    Continuous fun u : GA D V × (Mx D V.rank a × Mx D V.rank b) => ac V u.1 u.2 := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (((continuous_mt V).comp continuous_fst).matrix_mul (continuous_fst.comp continuous_snd)).prodMk
    (((continuous_mt V).comp continuous_fst).matrix_mul (continuous_snd.comp continuous_snd))

theorem top_pair (a b c : ℕ) : BorelSpace (Mx D a b × Mx D a c) ∧ SecondCountableTopology (Mx D a b × Mx D a c) := by
  obtain ⟨-, -, h3, -, h5⟩ := top_mx (D := D) a b
  obtain ⟨-, -, h3', -, h5'⟩ := top_mx (D := D) a c
  exact ⟨inferInstance, inferInstance⟩

theorem top_par (n t : ℕ) (W : HSp D) : BorelSpace (Par D n t W) ∧ SecondCountableTopology (Par D n t W) := by
  obtain ⟨-, -, h3, -, h5⟩ := top_mx (D := D) t n
  obtain ⟨-, -, h3', -, h5'⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, -, g4, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance⟩

theorem measurable_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Measurable (zp d hn x₀) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  exact (continuous_zp d hn x₀).measurable

theorem sigmaFinite_parameter_product_measure {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure) :
    SigmaFinite (Q0 I μ) := by
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  unfold Q0
  infer_instance

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting
variable {D : D7} {n t : ℕ} {B W : HSp D}

def XU (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) (U : Mx D t n) :
    Mx D B.rank n :=
  mm d.jX U + mm d.j0 (jn hn (ww W x₀ h) 0)

theorem measurable_pi {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Measurable fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  have hc : Continuous fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2) :=
    (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  exact hc.measurable

end GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

def Dom : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (a b c : ℕ) (ι : Fin c → Fin b), Function.Injective ι →
  ∀ Φ ∈ schwartzA θ a b, ∃ M ∈ schwartzA θ a c, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
    ∀ x : Mx D a b, ‖Φ x‖ ≤ (M (x.submatrix id ι)).re

def OrbFin : Prop := ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (m : Measure (GA D W)), m.IsHaarMeasure →
  ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ N ∈ schwartzA θ W.rank W.rank,
    ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂m < ⊤

def ZpEq : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (b₀ : HermE D W.rank),
  b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ p : Par D n t W,
    ip B (zp d hn x₀ p).1 (zp d hn x₀ p).1 = rat b₀.1 ∧ yv B b₀ (zp d hn x₀ p) = p.2.2 ∧ qv B b₀ (zp d hn x₀ p) = 0

def AcEq : Prop := ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) (g : GA D V) (z : Mx D V.rank r × Mx D V.rank t),
  ip V (ac V g z).1 (ac V g z).1 = ip V z.1 z.1 ∧ yv V b₀ (ac V g z) = yv V b₀ z ∧ qv V b₀ (ac V g z) = qv V b₀ z

def JnPi : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) x₀ (g : GA D B) (p : Par D n t W),
  jn hn (ac B g (zp d hn x₀ p)).1 (ac B g (zp d hn x₀ p)).2 =
    mm (mt B g) (mm (XU d hn x₀ p.1 p.2.1) (bl hn 1 p.2.2 0 1))

def JnBl : Prop := ∀ (D : D7) (n t a : ℕ) (r : ℕ) (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (y : Mx D r t),
  mm (jn hn w v) (bl hn 1 y 0 1) = jn hn w (mm w y + v)

def Ext0 : Prop := ∀ (D : D7) (n t : ℕ) (W : HSp D) (hn : W.rank + t = n) x₀ (h : GA D W),
  mm (mt W h⁻¹) (rat (ext0 hn x₀)) = jn hn (ww W x₀ h) 0

def Shift : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
  (Φ : Mx D B.rank n → ℂ) (y : Mx D W.rank t) (a : Mx D W.rank n),
    ikp I (fun X => Φ (mm X (bl hn 1 y 0 1))) a = ikp I Φ (mm a (bl hn 1 y 0 1))

def IkLint : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (I : IkD d n) θ, IsInfFam θ →
  ∀ M ∈ schwartzA θ B.rank n, (∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) → ∀ a : Mx D W.rank n,
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 a))‖ₑ ∂I.νK ∂I.μ₁ = ‖ikp I M a‖ₑ

def Fub4 : Prop := ∀ (α β γ δ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite e],
  (∀ f : α × β × γ × δ → ℂ, Integrable f (a.prod (b.prod (c.prod e))) →
    ∫ p, f p ∂(a.prod (b.prod (c.prod e))) = ∫ y, ∫ h, ∫ u, ∫ k, f (k, h, u, y) ∂a ∂c ∂b ∂e) ∧
  (∀ f : α × β × γ × δ → ℝ≥0∞, Measurable f →
    ∫⁻ p, f p ∂(a.prod (b.prod (c.prod e))) = ∫⁻ y, ∫⁻ h, ∫⁻ u, ∫⁻ k, f (k, h, u, y) ∂a ∂c ∂b ∂e)

def Law : Prop := ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
  (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (q : GlobalTheory.RegSW.stab d),
    (rho hn I μ x₀).map (ac B (q : GA D B)) = ((GlobalTheory.RegSW.absDet d q)⁻¹ ^ (W.rank + t) : ℝ≥0) • rho hn I μ x₀

def core {D : D7} {n t : ℕ} {B W : HSp D} {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (Φ : Mx D B.rank n → ℂ) (η : Mx D W.rank t → ℂ) (p : I.l.K × Par D n t W) : ℂ :=
  Φ (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1))) * conj (η p.2.2.2)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitIndex

theorem rStab_index_ne_zero_of_compact : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := by
  intro G _ _ _ θ K K' d f hθ hKc ho hf y
  set W : Subgroup G := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set G) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf K : Subgroup K) : Set K) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf K).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf K ≤ rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k)) := by
    intro k' hk' k
    have hk'W : (k' : G) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : G)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : G) ∈ K' := hk'W.2
    have e : (y * ((k * k' : K) : G))⁻¹ * d * θ (y * ((k * k' : K) : G)) =
        (k' : G)⁻¹ * (((y * (k : G))⁻¹ * d * θ (y * (k : G))) * θ (k' : G)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf _ hl _).1, (hf _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

end GlobalTheory.CompanionTheory.SplitIndex
end
end

