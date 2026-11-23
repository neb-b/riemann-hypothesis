module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTenso
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem compAt_mem_intV_of_intAt : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  intro D v a ha
  have h : finPart D a ∈ intAE D := ha.2
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D a) ∈ intV D v
  generalize finPart D a = b at h ⊢
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    exact ⟨_, hα v, x, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
  | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy

end GlobalTheory.FixedUnitNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RealPairBound

theorem trace_conjT_mul_single {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℂ) (i : Fin r) (j : Fin s) (a : ℂ) :
    (Xᴴ * Matrix.single i j a).trace = star (X i j) * a := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem gramAt_det_ne (D : D7) (T : HSp D) (τ : D.what₂.Tau) : (gramAt D T τ).det ≠ 0 := by
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne T)

theorem pair_single (D : D7) (T : HSp D) {ρ : ℕ} (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin ρ) ℂ)
    (i : Fin T.rank) (j : Fin ρ) (a : ℂ) :
    tauE D τ D.host.xi0 * (Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j a)).trace
      = tauE D τ D.host.xi0 * (star (X i j) * a) := by
  have hu : IsUnit (gramAt D T τ).det := isUnit_iff_ne_zero.2 (gramAt_det_ne D T τ)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (gramAt D T τ), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    trace_conjT_mul_single]

theorem realSize_le_pairing : ∀ (D : D7) (θ : InfFam D) (T : HSp D) (ρ : ℕ), ∃ (k : ℕ) (τs : Fin k → D.what₂.Tau)
    (zs : Fin k → Matrix (Fin T.rank) (Fin ρ) ℂ) (C : ℝ), ∀ x : Mx D T.rank ρ,
      realSize θ x ≤ C * ∑ i, |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
  intro D θ T ρ
  classical
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let α : D.what₂.Tau → Bool → ℂ := fun τ b => if b then (c τ)⁻¹ * Complex.I else (c τ)⁻¹
  let z : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → Matrix (Fin T.rank) (Fin ρ) ℂ :=
    fun p => (gramAt D T p.1)⁻¹ * Matrix.single p.2.1 p.2.2.1 (α p.1 p.2.2.2)
  let e := (Fintype.equivFin (D.what₂.Tau × Fin T.rank × Fin ρ × Bool)).symm
  refine ⟨_, fun n => (e n).1, fun n => z (e n), 1, fun x => ?_⟩
  rw [one_mul]
  let v : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → ℝ := fun p =>
    |2 * (tauE D p.1 D.host.xi0 * ((compAt θ p.1 x)ᴴ * gramAt D T p.1 * z p).trace).re|
  change realSize θ x ≤ ∑ n, v (e n)
  rw [Equiv.sum_comp e v, Fintype.sum_prod_type, realSize]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Fintype.sum_bool]
  have hv : ∀ b, v (τ, i, j, b) = |2 * (c τ * (star (compAt θ τ x i j) * α τ b)).re| := fun b => by
    simp only [v, z]
    rw [pair_single]
  rw [hv, hv]
  have h1 : c τ * (star (compAt θ τ x i j) * α τ true) = star (compAt θ τ x i j) * Complex.I := by
    simp only [α, if_true]
    field_simp [hc τ]
  have h0 : c τ * (star (compAt θ τ x i j) * α τ false) = star (compAt θ τ x i j) := by
    simp only [α, Bool.false_eq_true, if_false]
    field_simp [hc τ]
  rw [h1, h0]
  have hn := Complex.norm_le_abs_re_add_abs_im (compAt θ τ x i j)
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    abs_mul, mul_zero, mul_one, zero_sub, abs_neg, abs_two]
  linarith [abs_nonneg (compAt θ τ x i j).re, abs_nonneg (compAt θ τ x i j).im]

end GlobalTheory.RealPairBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf.MajMeas

variable {D : D7}

theorem norm_compAt_le_realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m)
    (j : Fin n) : ‖compAt θ τ x i j‖ ≤ realSize θ x := by
  unfold realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ', ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖ :=
        Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem continuous_realSize {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} :
    Continuous (realSize θ : Mx D m n → ℝ) := by
  unfold realSize
  refine continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_norm.comp ((GlobalTheory.FockCompare.continuous_comp hθ τ).comp (continuous_id.matrix_elem i j))

theorem finPart_eq_zero_iff {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (a : AE D) : finPart D a = 0 ↔ a = σ (fun τ => θ τ (infPart D a)) := by
  constructor
  · intro ha
    refine sub_eq_zero.1 (h.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, h.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, h.comp, sub_self]
  · intro ha
    rw [ha]
    exact h.fin _

theorem isClosed_finZero {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (m n : ℕ) : IsClosed {z : Mx D m n | z.map (finPart D) = 0} := by
  haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have e : {z : Mx D m n | z.map (finPart D) = 0} =
      ⋂ i, ⋂ j, {z : Mx D m n | z i j = σ (fun τ => θ τ (infPart D (z i j)))} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hz i j
      have hz' := congrFun (congrFun hz i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at hz'
      exact (finPart_eq_zero_iff h _).1 hz'
    · intro hz
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply]
      exact (finPart_eq_zero_iff h _).2 (hz i j)
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (continuous_id.matrix_elem i j) ?_
  exact h.cont.comp (continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp h.inf τ).comp (continuous_id.matrix_elem i j))

theorem setOf_inBox {m n : ℕ} (K : Set (Mx D m n)) :
    {x | InBox K x} = K + {z : Mx D m n | z.map (finPart D) = 0} := by
  ext x
  constructor
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, hk, x - k, hx, add_sub_cancel k x⟩
  · rintro ⟨k, hk, z, hz, rfl⟩
    exact ⟨k, hk, by rwa [add_sub_cancel_left]⟩

theorem isClosed_inBox {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) : IsClosed {x | InBox K x} := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  rw [setOf_inBox]
  exact (isClosed_finZero h m n).add_left_of_isCompact hK

theorem isCompact_box {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) (R : ℝ) :
    IsCompact {x | InBox K x ∧ realSize θ x ≤ R} := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  let B : Set (D.what₂.Tau → Fin m → Fin n → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let g : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) → Mx D m n := fun p =>
    p.1 + Matrix.of fun i j => σ (fun τ => p.2 τ i j - θ τ (infPart D (p.1 i j)))
  have hg : Continuous g := by
    refine continuous_fst.add (continuous_matrix fun i j => h.cont.comp (continuous_pi fun τ => ?_))
    have c1 : Continuous fun p : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) => p.2 τ i j := by fun_prop
    have c2 : Continuous fun p : Mx D m n × (D.what₂.Tau → Fin m → Fin n → ℂ) => θ τ (infPart D (p.1 i j)) :=
      (GlobalTheory.FockCompare.continuous_comp h.inf τ).comp (continuous_fst.matrix_elem i j)
    exact c1.sub c2
  refine ((hK.prod hB).image hg).of_isClosed_subset
    ((isClosed_inBox h K hK).inter (isClosed_le (continuous_realSize h.inf) continuous_const)) ?_
  rintro x ⟨⟨k, hk, hx⟩, hR⟩
  refine ⟨(k, fun τ i j => θ τ (infPart D (x i j))), ⟨hk, fun τ _ i _ j _ => ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_compAt_le_realSize θ x τ i j).trans hR
  · ext i j
    have h0 := congrFun (congrFun hx i) j
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply] at h0
    have e := (finPart_eq_zero_iff h _).1 h0
    simp only [(infPart D).map_sub, (θ _).map_sub] at e
    show k i j + σ (fun τ => θ τ (infPart D (x i j)) - θ τ (infPart D (k i j))) = x i j
    rw [← e, add_sub_cancel]

theorem measurable_maj {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) (N : ℕ) : Measurable (maj θ K N) := by
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  unfold maj
  exact Measurable.ite (isClosed_inBox h K hK).measurableSet
    ((continuous_const.add (continuous_realSize h.inf)).pow N).measurable.inv measurable_const

theorem exists_leftInv {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E)
    (hx : LinearIndependent D.host.E x.transpose) : ∃ y : Matrix (Fin n) (Fin m) D.host.E, y * x = 1 := by
  have hinj : Function.Injective x.mulVecLin := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective x.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  rwa [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {m n k : ℕ} (A : Mx D m n) (B : Mx D n k) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem realSize_mul_le (θ : InfFam D) {m n k : ℕ} (Y : Mx D m n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : Mx D n k, realSize θ (Y * a) ≤ c * realSize θ a := by
  refine ⟨∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖, by positivity, fun a => ?_⟩
  calc realSize θ (Y * a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

theorem maj_rat_le (θ : InfFam D) (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E)
    (hx : LinearIndependent D.host.E x.transpose) (K : Set (Mx D m k)) (hK : IsCompact K) :
    ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k,
      maj θ K N ((rat x : Mx D m n) * u) ≤ C * maj θ K' N u := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  obtain ⟨y, hy⟩ := exists_leftInv x hx
  have hyx : (rat y : Mx D n m) * rat x = 1 := by
    unfold rat
    rw [← Matrix.map_mul, hy, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨c, hc0, hc⟩ := realSize_mul_le θ (k := k) (rat y : Mx D n m)
  refine ⟨(fun a => (rat y : Mx D n m) * a) '' K, hK.image (continuous_const.matrix_mul continuous_id),
    fun N => ⟨(1 + c) ^ N, fun u => ?_⟩⟩
  by_cases hb : InBox K ((rat x : Mx D m n) * u)
  · obtain ⟨k0, hk0, hkx⟩ := hb
    have hb' : InBox ((fun a => (rat y : Mx D n m) * a) '' K) u := by
      refine ⟨rat y * k0, ⟨k0, hk0, rfl⟩, ?_⟩
      have e : u - rat y * k0 = rat y * (rat x * u - k0) := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
      rw [e, Matrix.map_mul, hkx, Matrix.mul_zero]
    simp only [maj, if_pos (show InBox K ((rat x : Mx D m n) * u) from ⟨k0, hk0, hkx⟩), if_pos hb']
    have hs := hc ((rat x : Mx D m n) * u)
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul] at hs
    have h0 := realSize_nonneg θ ((rat x : Mx D m n) * u)
    have h0' := realSize_nonneg θ u
    have hle : 1 + realSize θ u ≤ (1 + c) * (1 + realSize θ ((rat x : Mx D m n) * u)) := by nlinarith
    have hA : 0 < (1 + realSize θ ((rat x : Mx D m n) * u)) ^ N := by positivity
    have hB : 0 < (1 + realSize θ u) ^ N := by positivity
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle N
  · have e : maj θ K N ((rat x : Mx D m n) * u) = 0 := by simp only [maj, if_neg hb]
    rw [e]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N u)

end GlobalTheory.Unf.MajMeas


open GlobalTheory.Unf.MajMeas in
theorem GlobalTheory.Unf.maj_measurable_rat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → IsClosed {x | InBox K x} ∧ Continuous (realSize θ : Mx D m n → ℝ) ∧ (∀ N, Measurable (maj θ K N)) ∧ ∀ R : ℝ, IsCompact {x | InBox K x ∧ realSize θ x ≤ R}) ∧ ∀ (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E), LinearIndependent D.host.E x.transpose → ∀ K : Set (Mx D m k), IsCompact K → ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k, maj θ K N ((rat x : Mx D m n) ⬝ u) ≤ C * maj θ K' N u := by
  intro D θ hθ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact ⟨fun m n K hK => ⟨isClosed_inBox hσ K hK, continuous_realSize hθ, fun N => measurable_maj hσ K hK N,
    fun R => isCompact_box hσ K hK R⟩, fun m n k x hx K hK => maj_rat_le θ m n k x hx K hK⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLink
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_comp_one {D : D7} {S T : HSp D} (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (1, h) (om (g, 1) f) = om (g, h) f := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  ext <;> simp

theorem rTrans_liftS {D : D7} {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T))
    (G : GA D T → ℂ) (f : WO S T → ℂ) (g : GA D S) :
    rTrans g (liftS om ν 𝓕 G f) = liftS om ν 𝓕 G (om (g, 1) f) := by
  funext x
  simp only [rTrans, liftS_apply]
  congr 1
  funext h
  have e : ((x, h) : GA D S × GA D T) * (g, 1) = (x * g, h) := by simp
  rw [← e, map_mul, Module.End.mul_apply]

theorem doubleStep_of_laws : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  intro D hBF hFB hLink hHand hFlat ψ σ B J B' s₁ s₂ l vL Φ₁ Φ₂ φ G g hΦ₁ hΦ₂ hφ hG hG'
  have hfl := _root_.GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hFlat ψ
  have hΞ₁ : ∀ h₁, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) := fun h₁ =>
    hfl.1 _ B J s₁ _ (s₁.weil.om_pres _ _ hΦ₁)
  have hΞ₂ : ∀ h₁ h₂, IsThetaFunO ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := fun h₁ h₂ =>
    hfl.2 _ J B' s₂ _ (s₂.weil.om_pres _ _ hΦ₂)
  have hL := fun h₁ => hLink ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ _ hφ (hΞ₁ h₁)
  refine ⟨fun h₁ h₂ => hHand ψ σ J B' s₂ vL _ _ (hL h₁).1 (hΞ₂ h₁ h₂), ?_⟩
  refine ⟨fun h₁ => J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)), ?_, ?_⟩
  · have := hBF ψ (σ + 1) B J s₁ φ (s₂.lift G Φ₂) (s₁.om (g, 1) Φ₁) hφ hG' (s₁.weil.om_pres _ _ hΦ₁)
    simp only [om_comp_one] at this
    convert this using 2
    exact rTrans_liftS _ _ _ _ _ _
  · intro h₁
    have := hFB ψ σ J B' s₂ vL _ G (s₂.om (h₁, 1) Φ₂) (hL h₁).1 hG (s₂.weil.om_pres _ _ hΦ₂)
    simp only [om_comp_one] at this
    convert this using 1
    · rfl
    · show J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)) = _
      rw [(hL h₁).2]
      congr 1
      exact rTrans_liftS _ _ _ _ _ _

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.BesSemi

variable {D : D7}

theorem continuous_embA {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Continuous (embA d o) := by
  have h : (embA d o : GA D A → GA D S) = fun h => d.emb0 (o.emb (h, 1)) := funext fun h => embA_apply d o h
  rw [h]
  exact d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))

theorem besselCompression_unipotent_mul_embedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 * (mt S (n * d.emb0 k) * d.j0) = mt S₀ k := by
  have hflag := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e
    (GlobalTheory.MixPer.Decomp.linInd d) n).1 hn
  have hcols : ∀ j : Fin S₀.rank, ∃ a : Fin ρ → AE D,
      mt S n *ᵥ (fun i => d.j0 i j) = (fun i => d.j0 i j) + d.jX *ᵥ a := by
    intro j
    apply hflag.2
    change d.pY *ᵥ (fun i => d.j0 i j) = 0
    funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (congrFun d.pY_j0 i) j
  choose a ha using hcols
  have h0 : mt S n * d.j0 = d.j0 + d.jX * Matrix.of (fun i j => a j i) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (ha j) i
  have hproj : d.p0 * (mt S n * d.j0) = 1 := by
    rw [h0, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic,
    ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, hproj, Matrix.one_mul]

theorem unique {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n n' : GA D S}
    (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) {h h' : GA D A} (e : n * embA d o h = n' * embA d o h') :
    n = n' ∧ h = h' := by
  have e0 := congrArg (fun g => d.p0 * (mt S g * d.j0)) e
  rw [embA_apply, embA_apply, besselCompression_unipotent_mul_embedding d hn,
    besselCompression_unipotent_mul_embedding d hn'] at e0
  have hh : h = h' := congrArg Prod.fst (o.emb_injective (mt_injective S₀ e0))
  subst h'
  exact ⟨mul_right_cancel e, rfl⟩

theorem rat_iff {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n : GA D S}
    (hn : n ∈ flagN d) (h : GA D A) : n * embA d o h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ A := by
  constructor
  · intro hg
    have hk : o.emb (h, 1) ∈ GQ S₀ := by
      rw [mem_GQ_iff]
      rw [embA_apply] at hg
      rw [← besselCompression_unipotent_mul_embedding d hn]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S _).1 hg) (rat_mem _))
    have hA : h ∈ GQ A := by
      rw [mem_GQ_iff]
      have e : o.pA * (mt S₀ (o.emb (h, 1)) * o.jA) = mt A h := by
        rw [o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]
      rw [← e]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S₀ _).1 hk) (rat_mem _))
    have he : embA d o h ∈ GQ S := by rw [embA_apply]; exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hk
    refine ⟨?_, hA⟩
    have : n = n * embA d o h * (embA d o h)⁻¹ := (mul_inv_cancel_right n _).symm
    rw [this]
    exact mul_mem hg (inv_mem he)
  · rintro ⟨hn', hA⟩
    refine mul_mem hn' ?_
    rw [embA_apply]
    exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (o.emb_mem_GQ hA (one_mem _))

end GlobalTheory.Unf.BesSemi

namespace GlobalTheory.Unf

theorem besSemi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  intro D σ B
  refine ⟨BesSemi.continuous_embA B.d B.o, GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d),
    fun n hn h => ?_, fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e,
    fun n hn h => BesSemi.rat_iff B.d B.o hn h⟩
  rw [embA_apply]
  let g := B.d.emb0 (B.o.emb (h, 1))
  have hg : mt B.V g * B.d.e.map (incA D) = B.d.e.map (incA D) :=
    B.d.wittDecomp_anisotropicEmbedding_inclX _
  have hg' := GlobalTheory.BesselChar.inv_fix_cols (mt_inv_mul B.V g) hg
  have hflag := GlobalTheory.BesselChar.mem_NFlag_iff B.V B.d.e
    (GlobalTheory.MixPer.Decomp.linInd B.d)
  change g * n * g⁻¹ ∈ flagN B.d
  apply (hflag _).2
  rw [mt_mul, mt_mul]
  exact ((hflag n).1 hn).conj hg hg' (mt_mul_inv B.V g)
    (GlobalTheory.BesselChar.perp_fixed B.d.e g⁻¹ hg')

end GlobalTheory.Unf
end

