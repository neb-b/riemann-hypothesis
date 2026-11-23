module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import ReciprocityTheory.ThetaQuasiPeriods.NormInvSmulMemSphere

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

def ChartDiffEnergy.Statement : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → (∀ i, (T i).PosDef) →
    Integrable (ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i))
      (fun y => hermChartPot A y - hermChartPot B y) (fun y => hermChartPot A y - hermChartPot B y))

def ChartIbpCutoff.Statement : Prop :=
  ∀ (n : ℕ) (A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ i, (T i).PosDef) →
    Tendsto (fun k : ℕ => ∫ y : Fin (n + 1) → ℂ, chartCutoff k y *
        ((hermChartPot A y - hermChartPot B y) *
            maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
              fun i => hermChartPot (T i)) y -
          (hermChartPot C y - hermChartPot D y) *
            maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
              fun i => hermChartPot (T i)) y))
      atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

abbrev PlIdx (j m : ℕ) : Type := {I : Finset (Fin (j + m)) // I.card = j}

def plAnchor (j m : ℕ) : PlIdx j m :=
  ⟨Finset.univ.map (Fin.castAddEmb m), by simp⟩

abbrev plBlocks (f j m : ℕ) : Fin f → Type := fun _ => PlIdx j m

abbrev GrassField (f j m : ℕ) : Type := FractionRing (MvPolynomial (Fin f × Fin j × Fin m) ℚ)

def grassPolyCoord (f j m : ℕ) : (Σ _ : Fin f, PlIdx j m) → MvPolynomial (Fin f × Fin j × Fin m) ℚ :=
  fun p => (colsOf (onePipe (fun a b => (X (p.1, a, b) : MvPolynomial (Fin f × Fin j × Fin m) ℚ)))
    p.2).det

def grassCoord (f j m : ℕ) : (Σ _ : Fin f, PlIdx j m) → GrassField f j m :=
  fun p => algebraMap _ _ (grassPolyCoord f j m p)

def grassIdeal (f j m : ℕ) : Ideal (MRing (plBlocks f j m)) :=
  mCoordIdeal (grassCoord f j m)

def fsMulti {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => 1)

def IsRootMatrix {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) : Prop :=
  ∀ τ a b, ∃ k : ℕ, 0 < k ∧ ζ τ a b ^ k = 1

def rootCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) : (Σ _ : Fin f, PlIdx j m) → ℂ :=
  fun p => (colsOf (onePipe (ζ p.1)) p.2).det

def rootPointIdeal {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    Ideal (MRing (plBlocks f j m)) :=
  mCoordIdeal (rootCoord ζ)

def rootFamily (f j m : ℕ) : Set (Ideal (MRing (plBlocks f j m))) :=
  {W | ∃ ζ : Fin f → Matrix (Fin j) (Fin m) ℂ, IsRootMatrix ζ ∧ W = rootPointIdeal ζ}

def grassConst (f j m : ℕ) : ℝ := ((f * j : ℕ) : ℝ) / 2 * Real.log (1 + m)

def rootAnchorSection (f j m : ℕ) : MRing (plBlocks f j m) :=
  ∏ τ : Fin f, X ⟨τ, plAnchor j m⟩

def coneRatios {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) : Set Ω :=
  Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩

def GrassHeightBound.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (f j m : ℕ), 1 ≤ f → ∀ II : IntersectionSystem, IsIntersectionSystem II →
    II (Fin f) (plBlocks f j m) (grassIdeal f j m) (f * j * m + 1) (fun _ => fsMulti (plBlocks f j m)) ≤
      ((f * j * m + 1 : ℕ) : ℝ) * grassConst f j m *
        geomDeg (grassIdeal f j m) (fsMulti (plBlocks f j m)) (f * j * m)

def CoordConeArithVar.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : ℕ) (t : Fin d → Ω),
    Nonempty K → (∀ k, y ⟨k, c k⟩ ≠ 0) → AlgebraicIndependent ℚ t →
    (∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios y c)) →
    (∀ r ∈ coneRatios y c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r) →
    IsArithVar (mCoordIdeal y) (d + 1)

def GrassArithVar.Statement : Prop :=
  ∀ (f j m : ℕ), 1 ≤ f → IsArithVar (grassIdeal f j m) (f * j * m + 1)

def RootArithVar.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → IsRootMatrix ζ →
    IsArithVar (rootPointIdeal ζ) 1

def FsLineSmooth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsSmoothHerm (fsMulti ι)

def FsLineLevi.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z w : (Σ k, ι k) → ℂ),
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 ≤ leviForm (fun z => Real.log ((fsMulti ι).h z)) z w

def FsLineSemipositive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsSemipositiveRel ⊥ P (fsMulti ι)

def NefOfNonneg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ),
    (∀ k, 0 ≤ a k) → NefOnFibres P a

def FsConjInvariant.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsConjInvariantH (fsMulti ι)

def MultiHomogMemCoord.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ),
    IsMultiHomog g a → (g ∈ mCoordIdeal y ↔ aeval y g = 0)

def GrassLeRoot.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), grassIdeal f j m ≤ rootPointIdeal ζ

def RootDense.Statement : Prop :=
  ∀ (f j m : ℕ), IsZariskiDense (grassIdeal f j m) (rootFamily f j m)

def RootAnchorNonzero.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ), ∀ τ, z ⟨τ, plAnchor j m⟩ ≠ 0

def RootPointConj.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ), ∀ τ, ∃ ζ' : Matrix (Fin j) (Fin m) ℂ,
      (∀ a b, ∃ k : ℕ, 0 < k ∧ ζ' a b ^ k = 1) ∧
        ∀ I : PlIdx j m, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * (colsOf (onePipe ζ') I).det

def RootLogNormBound.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ),
      -grassConst f j m ≤ logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z

def RootDivSuppEmpty.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    divSupp (rootPointIdeal ζ) (rootAnchorSection f j m) = ∅

abbrev McClasses {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (W : Ideal (MRing ι)) : Type _ :=
  Quot fun z z' : mcPts W => ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
    (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p

def RootPointsFinite.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    Finite (McClasses (rootPointIdeal ζ))

def RootHeight.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → IsRootMatrix ζ →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (rootPointIdeal ζ) 1 ![fsMulti (plBlocks f j m)] ≤
        grassConst f j m * degC (rootPointIdeal ζ)

def lineExampleCoord : (Σ _ : Unit, Fin 2) → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun p => if p.2 = 0 then 1 else algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)

def lineExampleT : Fin 1 → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun _ => algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ThetaGauss
section
set_option maxSynthPendingDepth 1

open Matrix MeasureTheory Real
open scoped MatrixOrder

namespace GroundTheory.Heights₂.Heights
namespace KTheta

noncomputable section

variable {g : ℕ}

theorem qf_star_mul_self (B : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    qf (star B * B) v = ∑ i, (B *ᵥ v) i ^ 2 := by
  unfold qf
  rw [← Matrix.mulVec_mulVec, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    Matrix.dotProduct_mulVec, vecMul_transpose]
  simp [dotProduct, sq]

theorem integral_exp_sum_sq (c : ℝ) :
    ∫ x : Fin g → ℝ, exp (-c * ∑ i, x i ^ 2) = (√(π / c)) ^ g := by
  have h : (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) = fun x => ∏ i, exp (-c * x i ^ 2) := by
    funext x; rw [Finset.mul_sum, Real.exp_sum]
  rw [h, integral_fintype_prod_volume_eq_prod (f := fun _ (t : ℝ) => exp (-c * t ^ 2))]
  simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem integral_comp_mulVec (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (f : (Fin g → ℝ) → ℝ) (hf : Continuous f) :
    ∫ v, f (B *ᵥ v) = |B.det|⁻¹ * ∫ x, f x := by
  have hdet : LinearMap.det (Matrix.toLin' B) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin g → ℝ))) hdet
  have hm : Measurable (Matrix.toLin' B) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toLin' B)).measurable
  have h1 : ∫ v, f (B *ᵥ v) = ∫ x, f x ∂(Measure.map (Matrix.toLin' B) volume) := by
    rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
    rfl
  rw [h1, hmap, integral_smul_measure, LinearMap.det_toLin']
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul]

theorem integral_exp_qf (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) :
    ∫ v, exp (-c * qf Y v) = (√(π / c)) ^ g * (√Y.det)⁻¹ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hdetY : Y.det = B.det ^ 2 := by
    rw [hB, det_mul, star_eq_conjTranspose, det_conjTranspose]; simp [sq]
  have hBdet : B.det ≠ 0 := by
    intro h; have := hY.det_pos; rw [hdetY, h] at this; simp at this
  calc ∫ v, exp (-c * qf Y v) = ∫ v, (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) (B *ᵥ v) := by
        congr 1; funext v; rw [hB, qf_star_mul_self]
    _ = |B.det|⁻¹ * ∫ x : Fin g → ℝ, exp (-c * ∑ i, x i ^ 2) :=
        integral_comp_mulVec B hBdet (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) (by fun_prop)
    _ = (√(π / c)) ^ g * (√Y.det)⁻¹ := by
        rw [integral_exp_sum_sq c, hdetY, Real.sqrt_sq_eq_abs]; ring

theorem integral_exp_two_pi_qf (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    ∫ v, exp (-(2 * π) * qf Y v) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) := by
  rw [integral_exp_qf Y hY (2 * π)]
  have hd := hY.det_pos
  have h2 : π / (2 * π) = (2 : ℝ)⁻¹ := by field_simp
  rw [h2, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
    Real.sqrt_inv, mul_inv, inv_pow]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]

theorem summable_exp_qf (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) (hc : 0 < c)
    (v : Fin g → ℝ) : Summable fun k : Fin g → ℤ => exp (-c * qf Y (intVec k + v)) := by
  set τ : Matrix (Fin g) (Fin g) ℂ := Complex.I • Y.map (fun y => (((c / π) * y : ℝ) : ℂ)) with hτ
  have him : τ.map Complex.im = (c / π) • Y := by
    ext i j; simp [hτ]
  have hYt : Yᵀ = Y := by
    have := hY.isHermitian; rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this; exact this
  have hdom : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin g) := by
    show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
    rw [him, transpose_smul, hYt, ← two_smul ℝ, smul_smul]
    exact hY.smul (by positivity)
  have hs := ReciprocityTheory.PTheta.thetaSummable_holds (Fin g) v 0 0 τ hdom
  refine hs.congr fun k => ?_
  unfold ReciprocityTheory.PTheta.thetaTerm
  rw [ReciprocityTheory.PTheta.sphereQuadraticPositivity.norm_eC, ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_arg, him]
  have hw : (fun i => (k i : ℝ) + v i) = intVec k + v := by funext i; simp [intVec]
  rw [hw]
  congr 1
  simp only [qf, smul_mulVec, dotProduct_smul, Pi.zero_apply, Complex.zero_im, smul_eq_mul]
  simp [dotProduct]
  field_simp

theorem intVec_mem_span (k : Fin g → ℤ) :
    intVec k ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g))) := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro i
  exact ⟨k i, by simp [intVec]⟩

theorem exists_int_of_mem_span {x : Fin g → ℝ}
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))) (i : Fin g) :
    ∃ n : ℤ, x i = n := by
  rw [Module.Basis.mem_span_iff_repr_mem] at hx
  obtain ⟨n, hn⟩ := hx i
  exact ⟨n, by simpa using hn.symm⟩

def latticeEquiv :
    (Fin g → ℤ) ≃ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup where
  toFun k := ⟨intVec k, intVec_mem_span k⟩
  invFun γ := fun i => ⌊(γ : Fin g → ℝ) i⌋
  left_inv k := by funext i; simp [intVec]
  right_inv γ := by
    apply Subtype.ext; funext i
    obtain ⟨n, hn⟩ := exists_int_of_mem_span γ.2 i
    simp [intVec, hn]

theorem integral_cube_tsum (F : (Fin g → ℝ) → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFc : Continuous F)
    (hs : ∀ u, Summable fun k : Fin g → ℤ => F (intVec k + u)) :
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ∑' k : Fin g → ℤ, F (intVec k + u) = ∫ x, F x := by
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup :=
    (latticeEquiv (g := g)).symm.injective.countable
  have hD := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin g)) (volume : Measure (Fin g → ℝ))
  have hDI : ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin g)) =ᵐ[volume]
      Set.Icc (0 : Fin g → ℝ) 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, ← Set.pi_univ_Icc]
    exact Measure.ae_eq_set_pi (fun i _ => Ico_ae_eq_Icc)
  have hP : ∀ u, ∑' k, F (intVec k + u) = (∑' k, ENNReal.ofReal (F (intVec k + u))).toReal := by
    intro u
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 _) (hs u),
      ENNReal.toReal_ofReal (tsum_nonneg fun k => hF0 _)]
  have hPm : Measurable fun u => ∑' k : Fin g → ℤ, F (intVec k + u) := by
    simp_rw [hP]
    exact (Measurable.tsum fun k => ENNReal.measurable_ofReal.comp
      (hFc.measurable.comp (measurable_const_add _))).ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => tsum_nonneg fun k => hF0 _)
      hPm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFc.aestronglyMeasurable]
  congr 1
  rw [hD.lintegral_eq_tsum'' (fun x => ENNReal.ofReal (F x)), ← setLIntegral_congr hDI,
    ← lintegral_tsum (μ := volume.restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin g))))
      (f := fun (γ : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup)
        (x : Fin g → ℝ) => ENNReal.ofReal (F (γ +ᵥ x)))
      (fun γ => (ENNReal.measurable_ofReal.comp
        (hFc.measurable.comp (measurable_const_vadd γ))).aemeasurable)]
  refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) (fun u _ => ?_)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 _) (hs u)]
  rw [← (latticeEquiv (g := g)).tsum_eq]
  rfl

end

end KTheta

end GroundTheory.Heights₂.Heights
end

