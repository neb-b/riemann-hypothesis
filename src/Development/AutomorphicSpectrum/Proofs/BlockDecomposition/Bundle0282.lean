module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleVecMulUnipMatrix
section
noncomputable section

open NumberField Filter Topology Matrix
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
  GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.SiegelEscape

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_eq_of_mem_lat {γ : AdelicGLn.AdelicGL K n} (hγ : γ ∈ lat K n) :
    ∃ (γ₀ : GL (Fin n) K) (u : IdeleGroup K),
      γ = AdelicGLn.diagonal K n γ₀ * scalarUnits K n u := by
  set s : IdeleGroup K := posIdele (Real.exp 1) (Real.exp_pos _) with hs
  have hz : (tor K fun _ : Fin n => (1 : ℝ)) = scalarUnits K n s := rfl
  have hN : (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hz, ← map_zpow, ← scalarUnits_mul_comm, mul_inv_cancel_right, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have h := Subgroup.mul_normal (AdelicGLn.diagonal K n).range
    (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ)))
  have hγ' : γ ∈ (↑((AdelicGLn.diagonal K n).range ⊔
      Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))) : Set (AdelicGLn.AdelicGL K n)) := hγ
  rw [h] at hγ'
  obtain ⟨a, ⟨γ₀, rfl⟩, b, hb, rfl⟩ := Set.mem_mul.1 hγ'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact ⟨γ₀, s ^ k, by rw [hz, map_zpow]⟩

theorem detModule_scalarUnits (u : IdeleGroup K) :
    (detModule K n (scalarUnits K n u) : ℝ) = (ideleModule K u : ℝ) ^ n := by
  rw [detModule, MonoidHom.comp_apply, scalarUnits_apply, det_diagUnits, map_prod,
    coe_finset_prod_pos]
  simp

theorem detModule_unipGL {r : ℕ} (X : UPos n r → 𝔸[K]) : detModule K n (unipGL X) = 1 :=
  mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL X)

theorem detModule_diagonal (γ₀ : GL (Fin n) K) : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)

theorem detModule_aR {r : ℕ} (hr : r ≤ n) (t : ℝ) :
    (detModule K n (aR K n r t) : ℝ) = Real.exp (r * t) ^ Module.finrank ℚ K := by
  have h := ideleModule_det_diagUnits_posIdele (K := K) (n := n)
    (fun i : Fin n => Real.exp (if (i : ℕ) < r then t else 0)) (fun _ => Real.exp_pos _)
  have h2 : ∏ i : Fin n, Real.exp (if (i : ℕ) < r then t else 0) = Real.exp (r * t) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 2
    simp [Fin.card_filter_val_lt, hr]
  rw [h2] at h
  exact h

theorem ratVec_single (l : Fin n) : ratVec (Pi.single l (1 : K)) = Pi.single l (1 : 𝔸[K]) := by
  ext1 i
  by_cases h : i = l
  · subst h; simp [ratVec]
  · simp [ratVec, h]

theorem single_vecMul_unipMatrix {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (X : UPos n r → 𝔸[K]) :
    Pi.single l (1 : 𝔸[K]) ᵥ* unipMatrix X = Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  ext1 j
  rw [Matrix.single_one_vecMul]
  simp [unipMatrix, blockEntry_apply, h, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem single_vecMul_aR {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (t : ℝ) :
    Pi.single l (1 : 𝔸[K]) ᵥ* ((aR K n r t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  have h1 : ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ = 1 → posIdele (K := K) ρ hρ = 1 := by
    rintro _ _ rfl
    exact map_one (posIdeleHom K)
  rw [aR, tor, coe_diagUnits]
  ext1 j
  rw [Matrix.vecMul_diagonal]
  by_cases hj : j = l
  · subst hj
    rw [h1 _ _ (by simp [h])]
    simp
  · simp [Pi.single_apply, hj]

theorem height_eq {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (γ₀ : GL (Fin n) K) (u : IdeleGroup K)
    (X : UPos n r → 𝔸[K]) (t : ℝ) (q : AdelicGLn.AdelicGL K n) :
    Reduction.height (AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q))
        (Pi.single l (1 : K) ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (ideleModule K u : ℝ) *
        adelicNorm (Pi.single l (1 : 𝔸[K]) ᵥ* (q : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  rw [mul_assoc, height_diagonal_mul, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.vecMul_one, Reduction.height, ratVec_single, Units.val_mul, Units.val_mul,
    Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    coe_unipGL, scalarUnits_apply, coe_diagUnits]
  have h0 : Pi.single l (1 : 𝔸[K]) ᵥ* Matrix.diagonal (fun _ : Fin n => ((u : IdeleGroup K) : 𝔸[K])) =
      ((u : IdeleGroup K) : 𝔸[K]) • Pi.single l (1 : 𝔸[K]) := by
    ext1 j
    rw [Matrix.vecMul_diagonal]
    simp [mul_comm]
  rw [h0, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, single_vecMul_unipMatrix hl,
    single_vecMul_aR hl]
  have hne : (Pi.single l (1 : K) : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h l
    simp at this
  have hfc := hasFiniteContent_height q hne
  rw [ratVec_single] at hfc
  exact adelicNorm_smul hfc u

theorem escape : Escape := by
  intro K _ _ n r hr hrn D Q T hD hQ hT
  have hn : 0 < n := by omega
  set l : Fin n := ⟨n - 1, by omega⟩ with hldef
  have hl : r ≤ (l : ℕ) := by simp only [hldef]; omega
  set e : Fin n → K := Pi.single l 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h l
    simp [he] at this
  obtain ⟨ε, hε, hheight⟩ := exists_pos_le_height hT
  obtain ⟨P, hP, hvec⟩ := exists_adelicNorm_vecMul_le_mul hQ
  set A : ℝ := adelicNorm (ratVec e) with hA
  have hA1 : 1 ≤ A := one_le_adelicNorm_ratVec he0
  have hcont : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨_, B, -, -, hB⟩ := exists_pos_bounds hT hcont fun g _ => (detModule K n g).2
  obtain ⟨b, _, hb, -, hb'⟩ := exists_pos_bounds hQ hcont fun g _ => (detModule K n g).2
  set c : ℝ := ε / (P * A) with hc
  have hPA : 0 < P * A := mul_pos hP (by linarith)
  have hcpos : 0 < c := div_pos hε hPA
  set d := Module.finrank ℚ K with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have htend : Tendsto (fun t : ℝ => Real.exp (r * t) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd0).comp
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr0))
  filter_upwards [htend.eventually_gt_atTop (B / (c ^ n * b))] with t ht γ hγ X _ q hq hmem
  obtain ⟨γ₀, u, rfl⟩ := exists_eq_of_mem_lat hγ
  set E : ℝ := (ideleModule K u : ℝ) with hE
  have hEpos : 0 < E := (ideleModule K u).2
  set τ := AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q) with hτ
  have hx0 : (e ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≠ 0 := by
    intro h
    apply he0
    have h2 := congrArg (· ᵥ* ((γ₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using h2
  have h1 : ε ≤ E * (P * A) := by
    have h2 := hheight τ hmem _ hx0
    rw [hτ, height_eq hl] at h2
    have h3 := hvec q hq (ratVec e) (hasFiniteContent_ratVec he0)
    rw [he, ratVec_single] at h3
    rw [hA, he, ratVec_single]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hEpos.le)
  have hcE : c ≤ E := (div_le_iff₀ hPA).2 h1
  have hdet : (detModule K n τ : ℝ) = E ^ n * (Real.exp (r * t) ^ d * (detModule K n q : ℝ)) := by
    rw [hτ, map_mul, map_mul, map_mul, map_mul, detModule_diagonal, detModule_unipGL, one_mul,
      one_mul, Positive.val_mul, Positive.val_mul, detModule_scalarUnits, detModule_aR hrn.le]
  have hle := (hB τ hmem).2
  rw [hdet] at hle
  have hbq := (hb' q hq).1
  have hexp : 0 < Real.exp (r * t) ^ d := pow_pos (Real.exp_pos _) _
  have hcn : 0 < c ^ n := pow_pos hcpos _
  have h4 : c ^ n * (Real.exp (r * t) ^ d * b) ≤ B := by
    refine le_trans ?_ hle
    exact mul_le_mul (pow_le_pow_left₀ hcpos.le hcE n)
      (mul_le_mul_of_nonneg_left hbq hexp.le) (mul_pos hexp hb).le (pow_pos hEpos _).le
  rw [div_lt_iff₀ (mul_pos hcn hb)] at ht
  nlinarith [ht, h4]

end GlobalTheory.CompanionTheory.SiegelEscape

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusWeightDecomposition
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RgDsTor

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW PositivityTheory.RgDs.K

variable {n : ℕ}

theorem diagI_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  unfold inK inG Jm
  refine ⟨?_, ?_⟩
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext a
    simp [star_mul]
    split_ifs <;> ring
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem tor_eq_exp (θ : Fin n → ℝ) :
    tor θ = NormedSpace.exp (((1 : ℝ) : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  rw [Complex.ofReal_one, one_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [Complex.exp_eq_exp_ℂ]

private theorem pow_apply_eq_pow_smul_of_apply_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) (k : ℕ) : (A ^ k) w = c ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']

theorem exp_apply_of_eigen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) :
    NormedSpace.exp A w = Complex.exp c • w := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V w)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const w
  rw [← Complex.exp_eq_exp_ℂ] at h2
  have h3 : HasSum (fun k : ℕ => (ContinuousLinearMap.apply ℂ V w) (((k.factorial : ℂ))⁻¹ • A ^ k))
      (Complex.exp c • w) := by
    convert h2 using 1
    funext k
    rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      pow_apply_eq_pow_smul_of_apply_eq_smul A c w h k, smul_smul, smul_eq_mul]
  have e := h1.unique h3
  rwa [ContinuousLinearMap.apply_apply] at e

private theorem diagonal_mul_I_eq_sum_single (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      ∑ a, ((θ a : ℂ) * Complex.I) • Matrix.single a a (1 : ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

theorem dtau_diag_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (θ : Fin n → ℝ) :
    T.dτ (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) T.w =
      (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • T.w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [diagonal_mul_I_eq_sum_single, map_sum, ContinuousLinearMap.sum_apply]
  simp_rw [map_smul, ContinuousLinearMap.smul_apply, T.13, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem torW : TorW := by
  intro n ε Λ T θ k hk
  have hX := diagI_inK ε θ
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ 1, hk, tor_eq_exp])
  rw [← h1, KType.op_curve T hX γ hγ 1]
  apply exp_apply_of_eigen
  rw [ContinuousLinearMap.smul_apply, dtau_diag_w, smul_smul, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.RgDsTor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
section
noncomputable section

open NumberField MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def UBnd {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) : Prop :=
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ t₀ : ℝ,
    ∀ Q : Set (AdelicGLn.AdelicGL K n), IsCompact Q → ∃ C : ℝ, ∀ i, ∀ b ∈ ω, ∀ x : Fin n → ℝ, (∀ r, -t₀ ≤ sr x r) →
      ∀ q ∈ Q, ‖f i (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r)

structure UFam {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) : Prop where
  cont : ∀ i, Continuous (f i)
  left : ∀ i, IsLeftInvariant (f i)
  level : ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ i (g : AdelicGLn.AdelicGL K n) (u : U),
      f i (g * finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = f i g

abbrev mat (y : archGroup K n) : ArchMatrix K n := ((y : (ArchMatrix K n)ˣ) : ArchMatrix K n)

structure Ker [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ) : Prop where
  cont : Continuous β
  cpt : HasCompactSupport β
  nonneg : ∀ y, 0 ≤ β y
  mass : ∫ y, β y ∂ν = 1
  lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ y y', |β y - β y'| ≤ L * ‖mat y - mat y'‖

def sm [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ y, (β y : ℂ) * f (x * infEmb K n y) ∂ν

theorem continuous_mat : Continuous (mat : archGroup K n → ArchMatrix K n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isCompact_ball {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
  have hemb : IsEmbedding (fun y : archGroup K n => mat y) :=
    Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)
  have hsub : Metric.closedBall (1 : ArchMatrix K n) ρ ⊆ Set.range (fun y : archGroup K n => mat y) := by
    intro a ha
    have h1 : ‖1 - a‖ < 1 := by
      rw [norm_sub_rev]
      exact lt_of_le_of_lt (by simpa [dist_eq_norm] using ha) hρ
    refine ⟨⟨Units.oneSub (1 - a) h1, Subgroup.mem_top _⟩, ?_⟩
    simp [mat]
  have := (hemb.isInducing.isCompact_preimage_iff hsub).2 (isCompact_closedBall (1 : ArchMatrix K n) ρ)
  convert this using 1
  ext y
  simp [dist_eq_norm]

theorem tent_lip {A : Type*} [SeminormedAddCommGroup A] {ρ : ℝ} (hρ0 : 0 < ρ) (a b e : A) :
    |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ ρ⁻¹ * ‖a - b‖ := by
  have h1 : |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ |(1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ)| := by
    simp only [max_comm (0 : ℝ)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : (1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ) = ρ⁻¹ * (‖b - e‖ - ‖a - e‖) := by
    field_simp
    ring
  rw [h2, abs_mul, abs_of_pos (inv_pos.2 hρ0)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ0.le))
  have h3 := abs_norm_sub_norm_le (b - e) (a - e)
  rw [sub_sub_sub_cancel_right] at h3
  rw [norm_sub_rev a b]
  exact h3

theorem exists_ker [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {U : Set (archGroup K n)} (hU : U ∈ 𝓝 1) :
    ∃ β, Ker ν β ∧ tsupport β ⊆ U := by
  have hc : ContinuousAt (fun y : archGroup K n => mat y) 1 := continuous_mat.continuousAt

  have hb : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} ⊆ U := by
    have hemb : IsInducing (fun y : archGroup K n => mat y) :=
      (Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)).isInducing
    rw [hemb.nhds_eq_comap, mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    have h1 : mat (1 : archGroup K n) = 1 := rfl
    rw [h1] at ht
    obtain ⟨e, he, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ht
    refine ⟨min e (1 / 2), by positivity, by
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun y hy => hsub ?_⟩
    apply hball
    simp only [Metric.mem_closedBall, dist_eq_norm]
    exact le_trans hy (min_le_left _ _)
  obtain ⟨ρ, hρ0, hρ1, hρU⟩ := hb
  set β₀ : archGroup K n → ℝ := fun y => max 0 (1 - ‖mat y - 1‖ / ρ) with hβ₀
  have hβc : Continuous β₀ :=
    continuous_const.max (continuous_const.sub ((continuous_mat.sub continuous_const).norm.div_const _))
  have hsupp : Function.support β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
    intro y hy
    by_contra h
    apply hy
    have h' : ρ < ‖mat y - 1‖ := not_le.1 h
    have : 1 < ‖mat y - 1‖ / ρ := (one_lt_div hρ0).2 h'
    exact max_eq_left (by linarith)
  have hclosed : IsClosed {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} :=
    isClosed_le (continuous_mat.sub continuous_const).norm continuous_const
  have hts : tsupport β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := closure_minimal hsupp hclosed
  have hcs : HasCompactSupport β₀ := (isCompact_ball hρ1).of_isClosed_subset (isClosed_tsupport _) hts
  have hnn : ∀ y, 0 ≤ β₀ y := fun y => le_max_left _ _
  have hpos : 0 < ∫ y, β₀ y ∂ν := by
    refine hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn (x := 1) ?_
    have : β₀ 1 = 1 := by simp [hβ₀, mat]
    rw [this]; exact one_ne_zero
  set c := ∫ y, β₀ y ∂ν with hcdef
  have hcpos : 0 ≤ c⁻¹ := inv_nonneg.2 hpos.le
  have hk : Ker ν (fun y => c⁻¹ * β₀ y) := by
    refine { cont := continuous_const.mul hβc
             cpt := hcs.mul_left
             nonneg := fun y => mul_nonneg hcpos (hnn y)
             mass := ?_
             lip := ⟨c⁻¹ * ρ⁻¹, mul_nonneg hcpos (inv_nonneg.2 hρ0.le), fun y y' => ?_⟩ }
    · rw [integral_const_mul, ← hcdef, inv_mul_cancel₀ hpos.ne']
    · rw [← mul_sub, abs_mul, abs_of_nonneg hcpos, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hcpos
      exact tent_lip hρ0 _ _ _
  exact ⟨_, hk, (tsupport_mul_subset_right (f := fun _ => c⁻¹) (g := β₀)).trans (hts.trans hρU)⟩

end GlobalTheory.CompanionTheory.Conc

end
end

