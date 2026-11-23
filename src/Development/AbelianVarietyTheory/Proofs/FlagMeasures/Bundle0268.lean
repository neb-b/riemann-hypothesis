module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNilpotentAlgebraIsotropicFlagUnipotentRadi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLevi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
section
noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := rank_base_space D.R
  simp only [Ranks.N, zero_mul, add_zero] at this
  omega

variable {D : D7} (X : HidaSetting D)

def ci : Fin (2 * D.R.rS + D.R.k + 1) ≃ Fin X.B.I.n := finCongr (X.n_eq.trans (rank_eq D)).symm

def crdH (y : (VS D).V) : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E := fun i => X.bas.repr y (ci X i)

def vecOf : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).toLinearMap

def Jc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E :=
  fun i j => (VS D).hT (X.bas (ci X i)) (X.bas (ci X j))

def Lc : Submodule (𝓞 D.host.E) (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :=
  (VS D).L0.comap ((vecOf X).restrictScalars (𝓞 D.host.E))

def Pc (u : D.what₂.Word) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i b => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.eX a) i) b

def fc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin D.R.rS) D.host.E :=
  Matrix.of fun i a => crdH X (X.fY a) i

def Tc (u : D.what₂.Word) : D.host.F := (((D.mem u).A.T : ℕ) : D.host.F)

def tauOf (D : D7) (w : InfinitePlace D.host.E) : D.what₂.Tau :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose

def Direct (D : D7) (w : InfinitePlace D.host.E) : Prop := w.embedding = embS D (tauOf D w)

def A0 {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  (C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix id (ci X)

def Ac {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  if Direct D w then A0 X C w else (A0 X C w).map star

def sc (D : D7) (a : Fin D.R.rS) : ℝ := (2 * D.host.v) ^ (D.R.rS - (a : ℕ))

def trX {θ : ℝ} (C : Choice X θ) (x : X.B.I.Ginf) : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun τ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)))

def cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then M else fun i j => star (M i j)

def Gm (D : D7) (y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun w => cjw D w (y (tauOf D w))

end GlobalTheory.CovDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolic
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem gaugeSubEx_mem_maxK_iff {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    g ∈ maxK ε ↔ g ∈ Formalism.REAL.KG ε := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  constructor
  · intro h
    have h1 : (uMat g)ᴴ * uMat g = 1 := h
    have h2 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h1
    refine ⟨Matrix.mem_unitaryGroup_iff'.mpr h1, ?_⟩
    show uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g
    calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hg]
      _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.one_mul]
  · intro h
    exact Matrix.mem_unitaryGroup_iff'.mp h.1

theorem gaugeSubEx_haarK (n : ℕ) (ε : Fin n → Bool) :
    ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧
      ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  have hK : maxK ε = (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    Set.ext fun g => gaugeSubEx_mem_maxK_iff ε g
  have hc : IsCompact (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hm : MeasurableSet (maxK ε) := hK ▸ hc.isClosed.measurableSet
  have hv : Measurable (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have := Formalism.REAL.compact_haar_probability n ε
  refine ⟨(Formalism.REAL.muK ε).map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hm.compl]
    have : (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) ⁻¹' (maxK ε)ᶜ = ∅ := by
      ext k
      simp [hK]
    rw [this, measure_empty]
  · rw [Measure.map_apply hv MeasurableSet.univ, Set.preimage_univ, measure_univ]
  · intro k hk
    have hk' : k ∈ Formalism.REAL.KG ε := (gaugeSubEx_mem_maxK_iff ε k).mp hk
    have h := map_mul_left_eq_self (Formalism.REAL.muK ε) ⟨k, hk'⟩
    rw [Measure.map_map (measurable_const_mul k) hv]
    conv_rhs => rw [← h]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl

theorem gaugeSubEx : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagN ε W) (dimN n j) μ) ∧ (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μ) ∧ ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧ ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  intro n ε a j W _ hW
  refine ⟨?_, ?_, gaugeSubEx_haarK n ε⟩
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := _root_.GlobalTheory.RadicalAlg.exists_algebra_flagN n ε a j W hW
    rw [h4]
    exact _root_.GlobalTheory.GaugeSubExists.exists_isGaugeSub n ε A _ E h1 h2 h3
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := _root_.GlobalTheory.LeviAlgebra.exists_levi_algebra n ε a j W hW
    rw [h4]
    exact _root_.GlobalTheory.GaugeSubExists.exists_isGaugeSub n ε A _ E h1 h2 h3

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProductChartTangentEquivBallVolume
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TubeLie

open GlobalTheory.OmegaFrobenius (realify unrealify_realify)

theorem norm_sq_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

theorem skew_top {k : ℕ} (X : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) (i j : Fin k) :
    conj (unrealify (X : EuclideanSpace ℝ _) j i) + unrealify (X : EuclideanSpace ℝ _) i j = 0 := by
  have h := (_root_.GlobalTheory.TubeLie.mem_lieE_UH_of_sq k 1 (X : EuclideanSpace ℝ _) (by simp)).1 X.2
  have h' := congrFun (congrFun h i) j
  simpa [Matrix.conjTranspose_apply, Complex.star_def] using h'

theorem lie_entry {k : ℕ} (η : ℝ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    (Mᴴ * Hd k η + Hd k η * M) i j =
      conj (M j i) * (if j = Fin.last k then (η : ℂ) else 1) + (if i = Fin.last k then (η : ℂ) else 1) * M i j := by
  simp [Hd, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

private theorem Hd_mul_self_eq_one {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Hd k η * Hd k η = 1 := by
  unfold Hd
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> rcases hη with rfl | rfl <;> norm_num

theorem tang_mem {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    realify (k + 1) (tang η v) ∈ lieE (UH (Hd k η)) := by
  rw [_root_.GlobalTheory.TubeLie.mem_lieE_UH_of_sq _ _ _ (Hd_mul_self_eq_one hη), GlobalTheory.OmegaFrobenius.unrealify_realify]
  have hs := skew_top v.1
  ext i j
  rw [lie_entry, Matrix.zero_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, hs] <;> ring

theorem unrealify_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem unrealify_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = c • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem tang_add {k : ℕ} (η : ℝ) (v w : Par k) : tang η (v + w) = tang η v + tang η w := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, unrealify_add, add_div] <;> ring

theorem tang_smul {k : ℕ} (η c : ℝ) (v : Par k) : tang η (c • v) = c • tang η v := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [tang, blk, hv, unrealify_smul, Complex.real_smul] <;> ring

def tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Par k →ₗ[ℝ] lieE (UH (Hd k η)) where
  toFun v := ⟨realify (k + 1) (tang η v), tang_mem hη v⟩
  map_add' v w := by ext1; simp [tang_add]
  map_smul' c v := by ext1; simp [tang_smul]

theorem unrealify_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    unrealify (tangL hη v : EuclideanSpace ℝ _) = tang η v := by
  exact GlobalTheory.OmegaFrobenius.unrealify_realify (tang η v)

theorem norm_sq_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) (v : Par k) :
    ‖tangL hη v‖ ^ 2 = ‖v.1‖ ^ 2 + (‖v.2.1‖ ^ 2 + ‖v.2.2‖ ^ 2) := by
  have hη1 : ‖(η : ℂ)‖ = 1 := by rcases hη with rfl | rfl <;> simp
  have e1 : ‖tangL hη v‖ ^ 2 = ∑ i, ∑ j, ‖tang η v i j‖ ^ 2 := by
    have h := norm_sq_unrealify (tangL hη v).1
    rw [unrealify_tangL] at h
    rw [← h, Submodule.coe_norm]
  have e2 : ‖v.1‖ ^ 2 = ∑ i, ∑ j, ‖unrealify v.1.1 i j‖ ^ 2 := by
    rw [← norm_sq_unrealify, Submodule.coe_norm]
  have e3 : ‖v.2.2‖ ^ 2 = ∑ j, ‖v.2.2 j‖ ^ 2 := EuclideanSpace.norm_sq_eq _
  rw [e1, e2, e3]
  simp only [Fin.sum_univ_castSucc, tang, blk, Fin.lastCases_castSucc, Fin.lastCases_last, hv]
  have hc : ∀ z : ℂ, ‖z / (√2 : ℝ)‖ ^ 2 = ‖z‖ ^ 2 / 2 := by
    intro z
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  have hb : ∀ z : ℂ, ‖-(η : ℂ) * (starRingEnd ℂ) (z / (√2 : ℝ))‖ ^ 2 = ‖z‖ ^ 2 / 2 := by
    intro z
    rw [norm_mul, norm_neg, hη1, one_mul, Complex.norm_conj, hc]
  have hd : ‖((v.2.1 : ℝ) : ℂ) * Complex.I‖ ^ 2 = ‖v.2.1‖ ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  simp only [hb, hc, hd, Finset.sum_add_distrib]
  linarith [Finset.sum_div Finset.univ (fun x => ‖v.2.2.ofLp x‖ ^ 2) (2 : ℝ)]

theorem tangL_surjective {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) : Function.Surjective (tangL (k := k) hη) := by
  intro y
  set M := unrealify (y : EuclideanSpace ℝ (Fin (k + 1) × Fin (k + 1) × Bool)) with hMdef
  have hM := (_root_.GlobalTheory.TubeLie.mem_lieE_UH_of_sq _ _ _ (Hd_mul_self_eq_one hη)).1 y.2
  have e : ∀ i j, (starRingEnd ℂ) (M j i) * (if j = Fin.last k then (η : ℂ) else 1) +
      (if i = Fin.last k then (η : ℂ) else 1) * M i j = 0 := by
    intro i j
    have h := congrFun (congrFun hM i) j
    rwa [lie_entry, Matrix.zero_apply] at h
  let A : Matrix (Fin k) (Fin k) ℂ := fun i j => M i.castSucc j.castSucc
  have hA : GlobalTheory.OmegaFrobenius.realify k A ∈ lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) := by
    rw [_root_.GlobalTheory.TubeLie.mem_lieE_UH_of_sq _ _ _ (by simp), GlobalTheory.OmegaFrobenius.unrealify_realify]
    ext i j
    have h := e i.castSucc j.castSucc
    simp [Fin.castSucc_ne_last] at h
    simp only [Matrix.mul_one, Matrix.one_mul]
    exact h
  have hll : (M (Fin.last k) (Fin.last k)).re = 0 := by
    have h := congrArg Complex.re (e (Fin.last k) (Fin.last k))
    rcases hη with rfl | rfl <;> simp at h <;> linarith
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  refine ⟨(⟨GlobalTheory.OmegaFrobenius.realify k A, hA⟩, (M (Fin.last k) (Fin.last k)).im,
    WithLp.toLp 2 (fun j => ((√2 : ℝ) : ℂ) * M (Fin.last k) j.castSucc)), ?_⟩
  apply Subtype.ext
  rw [← (GlobalTheory.OmegaFrobenius.realify (k + 1)).apply_symm_apply (y : EuclideanSpace ℝ _)]
  show GlobalTheory.OmegaFrobenius.realify (k + 1) (tang η _) = GlobalTheory.OmegaFrobenius.realify (k + 1) M
  congr 1
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · apply Complex.ext <;> simp [tang, blk, hll]
  · simp [tang, blk, hv, h2]
  · have h := e i.castSucc (Fin.last k)
    simp [Fin.castSucc_ne_last] at h
    simp [tang, blk, hv, h2]
    linear_combination -h
  · have hu : unrealify (GlobalTheory.OmegaFrobenius.realify k A) = A := GlobalTheory.OmegaFrobenius.unrealify_realify A
    simp only [tang, blk, Fin.lastCases_castSucc]
    exact congrFun (congrFun hu i) j

def tangIsom {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) :
    WithLp 2 (lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) × WithLp 2 (ℝ × EuclideanSpace ℂ (Fin k))) →ₗᵢ[ℝ]
      lieE (UH (Hd k η)) where
  toFun p := tangL hη (p.fst, p.snd.fst, p.snd.snd)
  map_add' p q := by rw [← map_add (f := _)]; rfl
  map_smul' c p := by rw [← map_smul]; rfl
  norm_map' p := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    exact norm_sq_tangL hη _

theorem measurePreserving_of_isom {A B C D : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [FiniteDimensional ℝ C] [MeasurableSpace C] [BorelSpace C] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
    (J : WithLp 2 (A × WithLp 2 (B × C)) →ₗᵢ[ℝ] D) (hs : Function.Surjective J) :
    MeasurePreserving (fun v : A × B × C => J (WithLp.toLp 2 (v.1, WithLp.toLp 2 v.2)))
      (volume.prod (volume.prod volume)) volume := by
  have h1 : MeasurePreserving (Prod.map (id : A → A) (WithLp.toLp 2 : B × C → WithLp 2 (B × C)))
      (volume.prod (volume.prod volume)) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (WithLp.volume_preserving_toLp B C)
  have h2 := WithLp.volume_preserving_toLp A (WithLp 2 (B × C))
  have h3 := (LinearIsometryEquiv.ofSurjective J hs).measurePreserving
  exact h3.comp (h2.comp h1)

theorem measurePreserving_tangL {k : ℕ} {η : ℝ} (hη : η = 1 ∨ η = -1) :
    MeasurePreserving (tangL (k := k) hη) (volume.prod (volume.prod volume)) volume := by
  have hsurj : Function.Surjective (tangIsom (k := k) hη) := by
    intro y
    obtain ⟨v, rfl⟩ := tangL_surjective hη y
    exact ⟨WithLp.toLp 2 (v.1, WithLp.toLp 2 (v.2.1, v.2.2)), rfl⟩
  exact measurePreserving_of_isom (tangIsom hη) hsurj

theorem exists_tang_equiv : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∃ L : Par k ≃L[ℝ] lieE (UH (Hd k η)), (∀ v : Par k, unrealify ((L v : lieE (UH (Hd k η))) : EuclideanSpace ℝ _) = tang η v) ∧ ∀ ρ : ℝ, 0 < ρ → volume (L '' Metric.ball (0 : Par k) ρ) = volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ))) ρ) * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))) := by
  intro k η hk hη
  have hinj : Function.Injective (tangL (k := k) hη) := by
    refine (injective_iff_map_eq_zero (tangL hη)).2 fun v hv => ?_
    have h := norm_sq_tangL hη v
    rw [hv, norm_zero] at h
    have a := sq_nonneg ‖v.1‖
    have b := sq_nonneg ‖v.2.1‖
    have c := sq_nonneg ‖v.2.2‖
    have h1 : ‖v.1‖ ^ 2 = 0 := by nlinarith
    have h2 : ‖v.2.1‖ ^ 2 = 0 := by nlinarith
    have h3 : ‖v.2.2‖ ^ 2 = 0 := by nlinarith
    simp only [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)
  let Lₗ := LinearEquiv.ofBijective (tangL hη) ⟨hinj, tangL_surjective hη⟩
  let L : Par k ≃L[ℝ] lieE (UH (Hd k η)) := Lₗ.toContinuousLinearEquiv
  refine ⟨L, fun v => unrealify_tangL hη v, fun ρ hρ => ?_⟩
  let e := L.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving e (volume.prod (volume.prod volume)) volume :=
    ⟨(measurePreserving_tangL hη).measurable, (measurePreserving_tangL hη).map_eq⟩
  have hpre := hmp.measure_preimage_equiv (e '' Metric.ball (0 : Par k) ρ)
  rw [MeasurableEquiv.preimage_image] at hpre
  change volume (e '' Metric.ball (0 : Par k) ρ) = _
  rw [← hpre]
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hz : (0 : Par k) = (0, 0, 0) := rfl
  rw [hz, ← ball_prod_same, ← ball_prod_same, Measure.prod_prod, Measure.prod_prod, Real.volume_ball,
    InnerProductSpace.volume_ball (0 : EuclideanSpace ℂ (Fin k))]
  have hf : Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  have hG : Real.Gamma (((2 * k : ℕ) : ℝ) / 2 + 1) = (k.factorial : ℝ) := by
    rw [show ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have hπ : √Real.pi ^ (2 * k) = Real.pi ^ k := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hf, hG, hπ]
  congr 1
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ (2 * k)),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ρ)]
  congr 1
  ring

end GlobalTheory.TubeLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitary
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem exists_haar_sigmaFinite :
    ∀ (I : AutInst), ∃ μf : Measure I.Gf, μf.IsHaarMeasure ∧ SigmaFinite μf := by
  intro I
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨Measure.haar, inferInstance, inferInstance⟩

end GlobalTheory.CongTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWord
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFrame

theorem ddIdeal_ne_bot (D : D7) :
    (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) : Ideal (𝓞 D.host.E)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem one_mem_ddS_zpow_neg (D : D7) (m : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [zpow_neg, zpow_natCast, ddS, ← FractionalIdeal.coeIdeal_pow]
  refine FractionalIdeal.one_mem_inv_coe_ideal ?_
  rw [← Ideal.zero_eq_bot]
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact ddIdeal_ne_bot D)

theorem frame_mem_rowLat (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a ∈ Λ := by
  obtain ⟨-, ⟨-, -, hz, -⟩, hX⟩ := hΛ
  have hXS : XS D F0 ≤ Λ := by
    rw [← hX]; exact inf_le_left
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z (Fin.last _) ∈ Λ
    rw [Fin.snoc_last]; exact hz.1
  | cast i =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z i.castSucc ∈ Λ
    rw [Fin.snoc_castSucc]
    apply hXS
    apply Submodule.subset_span
    refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
    have : -((D.R.rS : ℤ) - ((i : ℕ) : ℤ)) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub i.isLt.le]
    rw [this]
    exact one_mem_ddS_zpow_neg D _

theorem frame_mem_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → ∀ a, frame (lf D (X.Fu u)) a ∈ Λ :=
  fun D X Y u Λ hΛ a => frame_mem_rowLat D (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ) a

end GlobalTheory.RowFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometry
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIsom

theorem frameOK_mapLF : ∀ (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    ∀ (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂ →
    ∀ (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T), FrameOK D Λ₁ F → FrameOK D Λ₂ (mapLF γ F) := by
  intro D γ hγ Λ₁ Λ₂ hΛ T F hF
  subst hΛ
  have e : mapLF γ F = PI.RepsIndep.Tr.mapL γ hγ F := by
    unfold mapLF
    rw [dite_eq_left hγ]
    rfl
  rw [e]
  exact PI.RepsIndep.Tr.FrameOK_map hγ hF

end GlobalTheory.FrameIsom
end

