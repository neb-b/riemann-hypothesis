module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import GroundTheory.GlobalFields.TateThesis.LatticePoisson
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDualMin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussDualMin

theorem inner_toLp_eq_dotProduct {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

theorem qf_inv_transpose_mulVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (m : Fin g → ℝ) : qf (Bᵀ * B)⁻¹ (Bᵀ *ᵥ m) = m ⬝ᵥ m := by
  have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
  have hBu : IsUnit B.det := hB.isUnit
  have h1 : (Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ m) = B⁻¹ *ᵥ m := by
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBt,
      Matrix.mul_one]
  unfold qf
  rw [h1, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hBu,
    one_mulVec]

end PGaussDualMin


open PGaussDualMin in
theorem GaussDualMin.proof : GaussDualMin.Statement := by
  intro g B hB μ hμ hμ0
  classical
  obtain ⟨m, rfl⟩ : ∃ m : Fin g → ℝ, μ = WithLp.toLp 2 m := ⟨WithLp.ofLp μ, (WithLp.toLp_ofLp _ μ).symm⟩
  have hdual := GroundTheory.Global.mem_dualLattice.1 hμ
  have hex : ∀ i : Fin g, ∃ k : ℤ, inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g))
      (WithLp.toLp 2 (B *ᵥ Pi.single i 1)) = k :=
    fun i => hdual _ (Submodule.subset_span ⟨i, rfl⟩)
  choose l hl using hex
  have hlm : intVec l = Bᵀ *ᵥ m := by
    funext i
    change ((l i : ℤ) : ℝ) = _
    rw [← hl i, inner_toLp_eq_dotProduct, dotProduct_mulVec, dotProduct_single_one,
      mulVec_transpose]
  refine ⟨l, ?_, ?_⟩
  · intro hl0
    apply hμ0
    have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
    have h0 : Bᵀ *ᵥ m = 0 := by
      rw [← hlm, hl0]; funext i; simp [intVec]
    have hm0 : m = 0 := by
      calc m = (Bᵀ)⁻¹ *ᵥ (Bᵀ *ᵥ m) := by
            rw [mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
        _ = 0 := by rw [h0, mulVec_zero]
    rw [hm0]; rfl
  · rw [hlm, qf_inv_transpose_mulVec B hB, ← real_inner_self_eq_norm_sq,
      inner_toLp_eq_dotProduct]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCoords
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussLatticeCoords

theorem toLp_mulVec_intVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (k : Fin g → ℤ) :
    WithLp.toLp 2 (B *ᵥ intVec k) = ∑ i, k i • WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  have h : intVec k = ∑ i, (k i : ℝ) • (Pi.single i 1 : Fin g → ℝ) := by
    ext j
    simp [intVec, Finset.sum_apply, Pi.single_apply]
  rw [h, Matrix.mulVec_sum, WithLp.toLp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, Int.cast_smul_eq_zsmul]

end PGaussLatticeCoords


open PGaussLatticeCoords in
theorem GaussLatticeCoords.proof : GaussLatticeCoords.Statement := by
  intro g B hB
  refine ⟨fun k => ?_, fun x hx => ?_, fun k k' hkk' => ?_⟩
  · rw [toLp_mulVec_intVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    exact ⟨c, by rw [toLp_mulVec_intVec, hc]⟩
  · have hk : B *ᵥ intVec k = B *ᵥ intVec k' := hkk'
    have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
    have hv : intVec k = intVec k' := by
      have := congrArg (fun v => B⁻¹ *ᵥ v) hk
      simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec] using this
    funext i
    exact Int.cast_injective (congrFun hv i)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCovolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory Module

noncomputable section

namespace PGaussLatticeCovolume

def cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) : Fin g → EuclideanSpace ℝ (Fin g) :=
  fun i => WithLp.toLp 2 (B *ᵥ Pi.single i 1)

theorem cols_linearIndependent {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    LinearIndependent ℝ (cols B) := by
  have h := Matrix.linearIndependent_cols_of_det_ne_zero hB
  have e : cols B = (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm ∘ B.col := by
    funext i
    simp [cols]
  rw [e]
  exact h.map' _ (LinearEquiv.ker _)

def colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  basisOfLinearIndependentOfCardEqFinrank' (cols B) (cols_linearIndependent hB) (by simp)

theorem coe_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ⇑(colBasis hB) = cols B := by
  simp [colBasis]

theorem span_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Submodule.span ℤ (Set.range (colBasis hB)) = gaussLattice B := by
  rw [coe_colBasis]
  rfl

def intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℤ (gaussLattice B) :=
  ((colBasis hB).restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (span_colBasis hB))

theorem coe_intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ((↑) : gaussLattice B → EuclideanSpace ℝ (Fin g)) ∘ intBasis hB = cols B := by
  funext i
  simp [intBasis, Basis.restrictScalars_apply, coe_colBasis]

theorem det_cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    (EuclideanSpace.basisFun (Fin g) ℝ).toBasis.det (cols B) = B.det := by
  rw [Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, cols]

theorem volume_fundamentalDomain_basisFun (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin g) ℝ).toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume),
    OrthonormalBasis.coe_toBasis, measureReal_def,
    (EuclideanSpace.basisFun (Fin g) ℝ).volume_parallelepiped, ENNReal.toReal_one]

end PGaussLatticeCovolume


open PGaussLatticeCovolume in
theorem GaussLatticeCovolume.proof (hL : GaussLatticeIsLattice.Statement) :
    GaussLatticeCovolume.Statement := by
  intro g B hB
  have : DiscreteTopology (gaussLattice B) := (hL g B hB).1
  have : IsZLattice ℝ (gaussLattice B) := (hL g B hB).2
  rw [ZLattice.covolume_eq_det_mul_measureReal (gaussLattice B) volume (intBasis hB)
      (EuclideanSpace.basisFun (Fin g) ℝ).toBasis,
    coe_intBasis, det_cols, volume_fundamentalDomain_basisFun, mul_one]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeIsLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PGaussLatticeIsLattice

def colBasis {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    Module.Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  (Pi.basisFun ℝ (Fin g)).map
    ((B.toLinearEquiv' (B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hB))).trans
      (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm)

theorem colBasis_apply {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) (i : Fin g) :
    colBasis B hB i = WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  rw [colBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

theorem gaussLattice_eq_span {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    gaussLattice B = Submodule.span ℤ (Set.range (colBasis B hB)) := by
  unfold gaussLattice
  congr 2
  funext i
  exact (colBasis_apply B hB i).symm

end PGaussLatticeIsLattice


open PGaussLatticeIsLattice in
theorem GaussLatticeIsLattice.proof : GaussLatticeIsLattice.Statement := by
  intro g B hB
  have h := gaussLattice_eq_span B hB
  refine ⟨?_, fun {_} => ⟨?_⟩⟩
  · rw [h]; infer_instance
  · rw [h]; exact ZSpan.span_top (colBasis B hB)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPacking
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric

namespace PGaussPacking

theorem pairwiseDisjoint_balls {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ : ℝ}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) :
    (s : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint (fun x => ball x (δ / 2)) := by
  intro x hx y hy hxy
  apply ball_disjoint_ball
  rw [dist_eq_norm]
  linarith [hsep x hx y hy hxy]

theorem biUnion_balls_subset {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ r : ℝ}
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) :
    (⋃ x ∈ s, ball x (δ / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2) := by
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨x, hx, hz⟩ := hz
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rw [sub_zero]
  calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    _ < δ / 2 + r := by linarith [hs x hx]
    _ = r + δ / 2 := by ring

end PGaussPacking


open PGaussPacking in
theorem GaussPacking.proof : GaussPacking.Statement := by
  intro n s δ r hδ hr hsep hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : s.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => Subsingleton.elim a b)
    have h1' : (s.card : ℝ) ≤ 1 := by exact_mod_cast h1
    simpa using h1'
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hδ2 : 0 < δ / 2 := by positivity
  have hR : 0 ≤ r + δ / 2 := by positivity
  have hmeas : ∑ x ∈ s, (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x (δ / 2)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2)) := by
    rw [← measure_biUnion_finset (pairwiseDisjoint_balls s hsep) (fun x _ => measurableSet_ball)]
    exact measure_mono (biUnion_balls_subset s hs)
  simp only [Measure.addHaar_ball _ _ hδ2.le, Measure.addHaar_ball _ _ hR,
    finrank_euclideanSpace_fin, Finset.sum_const, nsmul_eq_mul] at hmeas
  have hc0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ 0 :=
    (measure_ball_pos _ _ one_pos).ne'
  have hct : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [← mul_assoc] at hmeas
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hmeas
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hp : 0 < (δ / 2) ^ n := pow_pos hδ2 n
  have key : (1 + 2 * r / δ) ^ n = (r + δ / 2) ^ n / (δ / 2) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [key, le_div_iff₀ hp]
  exact h2

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace PGaussPoissonBound

theorem norm_toLp_sq {g : ℕ} (v : Fin g → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, sq]

end PGaussPoissonBound


open PGaussPoissonBound in
theorem GaussPoissonBound.proof (hL : GaussLatticeIsLattice.Statement)
    (hV : GaussLatticeCovolume.Statement) (hK : GaussLatticeCoords.Statement)
    (hF : GaussFourierSelf.Statement) : GaussPoissonBound.Statement := by
  intro g B hB a
  obtain ⟨hdisc, hlat⟩ := hL g B hB
  have : DiscreteTopology (gaussLattice B) := hdisc
  have : IsZLattice ℝ (gaussLattice B) := hlat
  obtain ⟨hmem, hsurj, hinj⟩ := hK g B hB
  let E := EuclideanSpace ℝ (Fin g)
  let L := gaussLattice B
  let φ : (Fin g → ℤ) ≃ L := Equiv.ofBijective
    (fun k => ⟨WithLp.toLp 2 (B *ᵥ intVec k), hmem k⟩)
    ⟨fun k k' h => hinj (by
        have := congrArg (fun x : L => WithLp.ofLp (x : E)) h
        simpa using this),
      fun x => by
        obtain ⟨k, hk⟩ := hsurj x x.2
        exact ⟨k, Subtype.ext hk.symm⟩⟩
  let G := GroundTheory.Global.gaussianSchwartz E
  let a' : E := WithLp.toLp 2 (B *ᵥ a)
  let f : (Fin g → ℤ) → ℝ := fun k =>
    Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))
  have hG : ∀ k, G ((φ k : E) + a') = ((f k : ℝ) : ℂ) := fun k => by
    have h1 : ((φ k : E) + a') = WithLp.toLp 2 (B *ᵥ (intVec k + a)) := by
      rw [Matrix.mulVec_add]; rfl
    rw [h1, GroundTheory.Global.gaussianSchwartz_apply, norm_toLp_sq]
  have hnG : ∀ k, ‖G ((φ k : E) + a')‖ = f k := fun k => by
    rw [hG, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hGfun : (G : E → ℂ) = fun x => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
    funext fun x => GroundTheory.Global.gaussianSchwartz_apply x
  have hFG : ∀ μ : E, 𝓕 (G : E → ℂ) μ = ((Real.exp (-π * ‖μ‖ ^ 2) : ℝ) : ℂ) := fun μ => by
    rw [hGfun]; exact hF g μ
  have hnD : ∀ μ : GroundTheory.Global.dualLattice L,
      ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ = Real.exp (-π * ‖(μ : E)‖ ^ 2) := fun μ => by
    rw [norm_mul, Circle.norm_coe, mul_one, hFG, Complex.norm_of_nonneg (Real.exp_pos _).le]

  have hsumf : Summable f := by
    have h := (φ.summable_iff (f := fun ℓ : L => ‖G (ℓ + a')‖)).2
      (GroundTheory.Global.lattice_summable_norm L G a')
    exact h.congr fun k => hnG k

  have hsumD := GroundTheory.Global.dualLattice_summable_norm L G a'
  have hsumE : Summable fun μ : GroundTheory.Global.dualLattice L => Real.exp (-π * ‖(μ : E)‖ ^ 2) :=
    hsumD.congr hnD
  refine ⟨hsumf, hsumE, ?_⟩

  have hP := GroundTheory.Global.lattice_poisson_summation L G a'
  have hlhs : ∑' ℓ : L, G (ℓ + a') = ((∑' k, f k : ℝ) : ℂ) := by
    rw [← φ.tsum_eq (fun ℓ : L => G (ℓ + a')), Complex.ofReal_tsum]
    exact tsum_congr fun k => hG k
  rw [hlhs] at hP
  have hcov : ZLattice.covolume L = |B.det| := hV g B hB
  have hcpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  calc ∑' k, f k = ‖((∑' k, f k : ℝ) : ℂ)‖ :=
        (Complex.norm_of_nonneg (tsum_nonneg fun k => (Real.exp_pos _).le)).symm
    _ = (ZLattice.covolume L)⁻¹ *
          ‖∑' μ : GroundTheory.Global.dualLattice L, 𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ := by
        rw [hP, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    _ ≤ (ZLattice.covolume L)⁻¹ *
          ∑' μ : GroundTheory.Global.dualLattice L, ‖𝓕 (G : E → ℂ) μ * 𝐞 ⟪(μ : E), a'⟫‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumD) (inv_pos.2 hcpos).le
    _ = |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := by
        rw [hcov]; exact congrArg _ (tsum_congr hnD)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonDual
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace PGaussPoissonDual

theorem qf_smul {g : ℕ} (c : ℝ) (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    qf (c • Y) w = c * qf Y w := by
  rw [qf, qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot_mulVec_self {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    (B *ᵥ w) ⬝ᵥ (B *ᵥ w) = qf (Bᵀ * B) w := by
  rw [qf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w Bᵀ, Matrix.vecMul_transpose]

end PGaussPoissonDual


open PGaussPoissonDual in
theorem GaussPoissonDual.proof (hS : GaussSqrt.Statement) (hP : GaussPoissonBound.Statement)
    (hM : GaussDualMin.Statement) (hD : GaussDetFactor.Statement) :
    GaussPoissonDual.Statement := by
  intro g Y ρ hY hρ hmin u
  have hY2 : ((1 / 2 : ℝ) • Y).PosDef := hY.smul (by norm_num)
  obtain ⟨B, hB⟩ := hS g _ hY2
  have hdetB : B.det ≠ 0 := by
    intro h0
    have h1 : (Bᵀ * B).det = 0 := by rw [det_mul, det_transpose, h0, mul_zero]
    rw [hB] at h1
    exact hY2.det_pos.ne' h1
  have hterm : ∀ k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) =
      Real.exp (-π * ((B *ᵥ (intVec k + u)) ⬝ᵥ (B *ᵥ (intVec k + u)))) := by
    intro k
    rw [dot_mulVec_self, hB, qf_smul]
    ring_nf
  obtain ⟨hsum, -, hle⟩ := hP g B hdetB u
  refine ⟨(summable_congr hterm).2 hsum, GroundTheory.Global.dualLattice (gaussLattice B), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨l, hl0, hl⟩ := hM g B hdetB v hv hv0
    have hYdet : IsUnit Y.det := isUnit_iff_ne_zero.2 hY.det_pos.ne'
    have hinv : (Bᵀ * B)⁻¹ = (2 : ℝ) • Y⁻¹ := by
      rw [hB]
      apply Matrix.inv_eq_left_inv
      rw [smul_mul_smul_comm, Y.nonsing_inv_mul hYdet]
      norm_num
    rw [hinv, qf_smul] at hl
    have h2 := hmin l hl0
    have hq : 0 ≤ qf Y⁻¹ (intVec l) := le_trans (sq_nonneg ρ) h2
    have h3 : ρ ^ 2 ≤ ‖v‖ ^ 2 := by linarith
    nlinarith [norm_nonneg v]
  · rw [tsum_congr hterm, ← hD g Y B hY hB]
    exact hle

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCaseCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

end GroundTheory.Heights₂.Heights
end

