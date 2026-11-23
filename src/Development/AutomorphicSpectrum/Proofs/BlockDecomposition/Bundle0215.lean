module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0199
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem latK_mulVec {M : Matrix (Fin n) (Fin n) L} (h1 : ∀ i j, Valued.v (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → Valued.v (M i j) < 1) (k : ℕ) {x : Fin n → L} (hx : x ∈ latK L n k) :
    M.mulVec x ∈ latK L n k := by
  have hx1 : ∀ j, Valued.v (x j) ≤ 1 := fun j => by
    have := hx j
    split_ifs at this with h
    · exact this
    · exact this.le
  intro i
  show if i.val < k then Valued.v ((M.mulVec x) i) ≤ 1 else Valued.v ((M.mulVec x) i) < 1
  have e : (M.mulVec x) i = ∑ j, M i j * x j := rfl
  rw [e]
  split_ifs with hik
  · refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' (hx1 j)).trans (h1 i j)
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    by_cases hjk : j.val < k
    · have hji : j < i := by
        rw [Fin.lt_def]; omega
      exact (mul_le_of_le_one_right' (hx1 j)).trans_lt (h2 i j hji)
    · have := hx j
      rw [if_neg hjk] at this
      exact (mul_le_of_le_one_left' (h1 i j)).trans_lt this

theorem mem_iwU_iff (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) :
    g ∈ IwU σ n ↔ (∀ i j, Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
      ∀ i j, j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1 := by
  constructor
  · intro hg
    have hg' : (g : GL (Fin n) L) ∈ IwGL L n := hg
    refine ⟨fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries hg' i j, fun i j hji => ?_⟩
    have h := (Subgroup.mem_iInf.1 hg') ⟨i.val, by omega⟩
    have hs : (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n i.val = latK L n i.val := h
    have he : (Pi.single j (1 : L) : Fin n → L) ∈ latK L n i.val := by
      intro k
      by_cases hk : k = j
      · subst hk
        have : k.val < i.val := hji
        simp [this]
      · have : (Pi.single j (1 : L) : Fin n → L) k = 0 := Pi.single_eq_of_ne hk _
        rw [this]
        split_ifs <;> simp
    have hm := Set.smul_mem_smul_set (a := Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) he
    rw [hs] at hm
    have hi := hm i
    rw [if_neg (lt_irrefl _)] at hi
    have e : ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • (Pi.single j (1 : L) : Fin n → L)) i =
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := by
      show (Matrix.mulVec ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (Pi.single j (1 : L) : Fin n → L)) i = _
      simp
    rwa [e] at hi
  · rintro ⟨h1, h2⟩
    have hinv := (GlobalTheory.LGrp.mem_GU_iff σ n (g : GL (Fin n) L)).1 g.2
    have h1' : ∀ i j, Valued.v (((g : GL (Fin n) L)⁻¹).val i j) ≤ 1 := fun i j => by
      rw [hinv, hσv]; exact h1 _ _
    have h2' : ∀ i j, j < i → Valued.v (((g : GL (Fin n) L)⁻¹).val i j) < 1 := fun i j hji => by
      rw [hinv, hσv]; exact h2 _ _ (Fin.rev_lt_rev.2 hji)
    show (g : GL (Fin n) L) ∈ IwGL L n
    refine Subgroup.mem_iInf.2 fun k => ?_
    show (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n k = latK L n k
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact latK_mulVec h1 h2 k hy
    · refine ⟨((g : GL (Fin n) L)⁻¹).val.mulVec x, latK_mulVec h1' h2' k hx, ?_⟩
      show ((g : GL (Fin n) L)).val.mulVec (((g : GL (Fin n) L)⁻¹).val.mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem iwU_diag (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} (hg : g ∈ IwU σ n) (i : Fin n) :
    Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
  classical
  obtain ⟨h1, h2⟩ := (mem_iwU_iff hσv g).1 hg
  obtain ⟨k1, k2⟩ := (mem_iwU_iff hσv g⁻¹).1 (inv_mem hg)
  have hprod : (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i i = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; simp
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hprod
  have hrest : Valued.v (∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    rw [map_mul]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hji
    · exact (mul_le_of_le_one_right' (k1 j i)).trans_lt (h2 i j hji)
    · exact (mul_le_of_le_one_left' (h1 i j)).trans_lt (k2 j i hji)
  have hmain : Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
    have e : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
        (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
        1 - ∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
          (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i := by
      rw [← hprod]; ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by simpa using hrest), map_one]
  rw [map_mul] at hmain
  refine le_antisymm (h1 i i) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmain.symm
    _ ≤ _ := mul_le_of_le_one_right' (k1 i i)

end GlobalTheory.CompanionTheory.SatPow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationDifferentiable
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.MolDiff

variable {n : ℕ}

def rmul (w : Mat n) : CLof (Mat n) (Mat n) :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ w)

theorem rmul_apply (w z : Mat n) : rmul w z = z * w := rfl

def rmulLin : Mat n →ₗ[ℝ] CLof (Mat n) (Mat n) where
  toFun := rmul
  map_add' a b := by
    ext1 z
    simp [rmul_apply, mul_add]
  map_smul' c a := by
    ext1 z
    simp [rmul_apply]

theorem continuous_rmul : Continuous (rmul : Mat n → CLof (Mat n) (Mat n)) :=
  LinearMap.continuous_of_finiteDimensional rmulLin

theorem exists_unit_of_mem {g : Mat n} (h : g ∈ GLs n) : ∃ y : G n, y.val = g := by
  have : IsUnit g := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

theorem isCompact_lift {K : Set (Mat n)} (hK : IsCompact K) (hs : K ⊆ GLs n) :
    IsCompact (Units.val ⁻¹' K : Set (G n)) := by
  refine ((GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff ?_).2 hK
  intro g hg
  obtain ⟨y, hy⟩ := exists_unit_of_mem (hs hg)
  exact ⟨y, hy⟩

theorem exists_compact_support {K B : Set (Mat n)} (hK : IsCompact K) (hKs : K ⊆ GLs n)
    (hB : IsCompact B) (hBs : B ⊆ GLs n) :
    ∃ S : Set (G n), IsCompact S ∧ ∀ z ∈ B, ∀ u : G n, z * (u⁻¹ : G n).val ∈ K → u ∈ S := by
  refine ⟨(fun p : G n × G n => p.1⁻¹ * p.2) ''
    ((Units.val ⁻¹' K : Set (G n)) ×ˢ (Units.val ⁻¹' B : Set (G n))), ?_, ?_⟩
  · exact ((isCompact_lift hK hKs).prod (isCompact_lift hB hBs)).image
      ((continuous_fst.inv).mul continuous_snd)
  · intro z hz u hu
    obtain ⟨y, rfl⟩ := exists_unit_of_mem (hBs hz)
    refine ⟨(y * u⁻¹, y), ⟨?_, hz⟩, ?_⟩
    · simpa using hu
    · simp

end GlobalTheory.CompanionTheory.PresSobA.MolDiff


open GlobalTheory.CompanionTheory.PresSobA.MolDiff in
theorem GlobalTheory.CompanionTheory.PresSobA.mol_differentiableAt :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ, ∀ z ∈ GLs n, DifferentiableAt ℝ (Mol μ φ (⇑x)) z := by
  intro n _ _ μ _ V _ _ _ _ φ hφ x z hz
  obtain ⟨hsm, hcs, hsub⟩ := hφ
  have hc1 : Continuous φ := hsm.continuous
  have hdφ : Differentiable ℝ φ := hsm.differentiable (by simp)
  have hcf : Continuous (fderiv ℝ φ) := hsm.continuous_fderiv (by simp)
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  obtain ⟨B, hBn, hBs, hBc⟩ := local_compact_nhds (isOpen_GLs.mem_nhds hz)
  obtain ⟨S, hSc, hS⟩ := MolDiff.exists_compact_support hcs hsub hBc hBs
  have hinv : Continuous (fun u : G n => (u⁻¹ : G n).val) :=
    Units.continuous_val.comp continuous_inv
  have hmul : Continuous (fun p : Mat n × G n => p.1 * (p.2⁻¹ : G n).val) :=
    continuous_fst.matrix_mul (hinv.comp continuous_snd)
  let g : Mat n → G n → CLof (Mat n) ℝ := fun z u =>
    (fderiv ℝ φ (z * (u⁻¹ : G n).val)).comp (MolDiff.rmul (u⁻¹ : G n).val)
  have hg : Continuous (fun p : Mat n × G n => g p.1 p.2) :=
    (hcf.comp hmul).clm_comp (MolDiff.continuous_rmul.comp (hinv.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hBc.prod hSc).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨C0, hC0⟩ := hc1.bounded_above_of_compact_support hcs
  have hxS : IntegrableOn (⇑x) S μ := by
    haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hSc.measure_lt_top⟩
    exact ((Lp.memLp x).restrict S).integrable (by norm_num)
  let bound : G n → ℝ := S.indicator fun u => max C C0 * ‖x u‖
  have hbi : Integrable bound μ := IntegrableOn.integrable_indicator (hxS.norm.const_mul _) hSc.measurableSet
  have hout : ∀ z' ∈ B, ∀ u : G n, u ∉ S → z' * (u⁻¹ : G n).val ∉ tsupport φ :=
    fun z' hz' u hu h => hu (hS z' hz' u h)
  let F : Mat n → G n → V := fun z u => φ (z * (u⁻¹ : G n).val) • x u
  let F' : Mat n → G n → CLof (Mat n) V := fun z u => (g z u).smulRight (x u)
  have hFm : ∀ z', AEStronglyMeasurable (F z') μ := fun z' =>
    ((hc1.comp (continuous_const.matrix_mul hinv)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable x)
  have hF'm : AEStronglyMeasurable (F' z) μ := by
    have hgz : Continuous (g z) := hg.comp (Continuous.prodMk_right z)
    let L : CLof (Mat n) ℝ →L[ℝ] V →L[ℝ] CLof (Mat n) V :=
      LinearMap.mkContinuous₂ (ContinuousLinearMap.smulRightLₗ ℝ (Mat n) V) 1
        (by
          intro c v
          change ‖c.smulRight v‖ ≤ 1 * ‖c‖ * ‖v‖
          simp [ContinuousLinearMap.norm_smulRight_apply])
    exact L.aestronglyMeasurable_comp₂
      hgz.aestronglyMeasurable (Lp.aestronglyMeasurable x)
  have hFb : ∀ u, ‖F z u‖ ≤ bound u := by
    intro u
    by_cases hu : u ∈ S
    · simp only [bound, Set.indicator_of_mem hu, F, norm_smul]
      exact mul_le_mul_of_nonneg_right ((hC0 _).trans (le_max_right _ _)) (norm_nonneg _)
    · simp only [bound, Set.indicator_of_notMem hu, F]
      rw [image_eq_zero_of_notMem_tsupport (hout z (mem_of_mem_nhds hBn) u hu)]
      simp
  have hF'b : ∀ᵐ u ∂μ, ∀ z' ∈ B, ‖F' z' u‖ ≤ bound u := by
    refine ae_of_all _ fun u z' hz' => ?_
    by_cases hu : u ∈ S
    · simp only [bound, Set.indicator_of_mem hu, F', ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right ((hC (z', u) ⟨hz', hu⟩).trans (le_max_left _ _))
        (norm_nonneg _)
    · have h0 : g z' u = 0 := by
        show (fderiv ℝ φ (z' * (u⁻¹ : G n).val)).comp _ = 0
        rw [fderiv_of_notMem_tsupport ℝ (hout z' hz' u hu)]
        exact ContinuousLinearMap.zero_comp _
      simp only [bound, Set.indicator_of_notMem hu, F', h0]
      simp
  have hd : ∀ᵐ u ∂μ, ∀ z' ∈ B, HasFDerivAt (F · u) (F' z' u) z' := by
    refine ae_of_all _ fun u z' _ => ?_
    have h1 : HasFDerivAt (fun w : Mat n => w * (u⁻¹ : G n).val) (MolDiff.rmul (u⁻¹ : G n).val) z' :=
      (MolDiff.rmul (u⁻¹ : G n).val).hasFDerivAt
    exact ((hdφ _).hasFDerivAt.comp z' h1).smul_const (x u)
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hBn
    (Eventually.of_forall hFm) (hbi.mono' (hFm z) (ae_of_all _ hFb)) hF'm hF'b hbi hd).differentiableAt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiResolventIdentity
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toC0_eq_of_coe (p : C₀(ℝ, ℂ)) (f : ℝ → ℂ) (h : ∀ y, p y = f y) : toC0 f = p := by
  have hf : f = ⇑p := funext fun y => (h y).symm
  subst hf
  have hc : Continuous (⇑p) ∧ Tendsto (⇑p) (cocompact ℝ) (𝓝 0) := ⟨p.continuous, p.zero_at_infty'⟩
  unfold toC0
  rw [dite_eq_left hc]
  ext y
  rfl

theorem exists_resolvent_C0 : ∃ r : C₀(ℝ, ℂ), ∀ y, r y = (((1 + y ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hpos : ∀ y : ℝ, (1 + y ^ 2) ≠ 0 := fun y => by positivity
  have hcont : Continuous (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact (by fun_prop : Continuous fun y : ℝ => 1 + y ^ 2).inv₀ hpos
  have hat : Tendsto (fun y : ℝ => 1 + y ^ 2) (cocompact ℝ) atTop := by
    have h1 : Tendsto (fun y : ℝ => ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun y : ℝ => 1 + ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      tendsto_atTop_add_const_left _ 1 h1
    simpa using h2
  have htend : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := by
    have h3 : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) (cocompact ℝ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hat
    have h4 : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h3
    rwa [Complex.ofReal_zero] at h4
  exact ⟨⟨⟨_, hcont⟩, htend⟩, fun y => rfl⟩

theorem phiRes_holds : PhiRes := by
  intro n _ _ μ _ E _ Ω T F c hS g T₀ hb N _
  obtain ⟨-, -, -, -, -, -, -, -, -, hPW, -⟩ := hS
  have h0 := (hPW c g T₀ hb).1 0
  simp only [pow_zero, one_mul] at h0
  obtain ⟨r, hr⟩ := exists_resolvent_C0
  have hT : F.Φ r = T := F.res r hr
  let q : C₀(ℝ, ℂ) := ⟨⟨hg c g, h0.1⟩, h0.2⟩
  have hq : ∀ y, q y = hg c g y := fun y => rfl
  have key : ∀ M : ℕ, ∃ p : C₀(ℝ, ℂ),
      (∀ y, p y = ((((1 + y ^ 2) ^ M)⁻¹ : ℝ) : ℂ) * hg c g y) ∧ F.Φ p = F.Φ q * T ^ M := by
    intro M
    induction M with
    | zero => exact ⟨q, fun y => by simp [hq], by simp⟩
    | succ M ih =>
      obtain ⟨p, hp, hΦ⟩ := ih
      refine ⟨p * r, fun y => ?_, ?_⟩
      · have : (p * r) y = p y * r y := rfl
        rw [this, hp, hr, pow_succ (1 + y ^ 2) M, mul_inv]
        push_cast
        ring
      · rw [F.map_mul, hΦ, hT, pow_succ, mul_assoc]
  obtain ⟨p, hp, hΦ⟩ := key N
  rw [toC0_eq_of_coe p _ hp, toC0_eq_of_coe q _ hq, hΦ]

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorization
section
noncomputable section

open Filter Topology
open scoped ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

def phaseRoot (z : ℂ) : ℂ := z / ((Real.sqrt ‖z‖ : ℝ) : ℂ)

theorem norm_phaseRoot (z : ℂ) : ‖phaseRoot z‖ = Real.sqrt ‖z‖ := by
  unfold phaseRoot
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.div_sqrt

theorem continuous_phaseRoot : Continuous phaseRoot := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : phaseRoot 0 = 0 := by simp [phaseRoot]
    unfold ContinuousAt
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_phaseRoot]
    have : Continuous fun w : ℂ => Real.sqrt ‖w‖ := by fun_prop
    simpa using this.tendsto 0
  · have hne : ((Real.sqrt ‖z‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)
      exact_mod_cast this.ne'
    have hc : Continuous fun w : ℂ => ((Real.sqrt ‖w‖ : ℝ) : ℂ) := by fun_prop
    exact continuousAt_id.div hc.continuousAt hne

theorem tendsto_pow_mul_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ}
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) (m : ℕ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ m * k y) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨h', hh'⟩ := hr (2 * m)
  have h0 : Tendsto (fun y => ‖h' y‖) (cocompact ℝ) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (h'.zero_at_infty')
  have h1 : Tendsto (fun y => Real.sqrt ‖h' y‖) (cocompact ℝ) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h1.congr fun y => ?_
  rw [hh', norm_mul, norm_mul, hn, norm_pow, norm_pow, Complex.norm_real, pow_mul',
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem exists_rapid_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ} (hc : Continuous k)
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) : ∃ k' : C₀(ℝ, ℂ), (∀ y, k' y = k y) ∧ Rapid k' := by
  have key : ∀ m : ℕ, ∃ g : C₀(ℝ, ℂ), ∀ y, g y = (y : ℂ) ^ m * k y := fun m =>
    ⟨⟨⟨fun y => (y : ℂ) ^ m * k y, by fun_prop⟩, tendsto_pow_mul_of_norm_sqrt hr hn m⟩,
      fun _ => rfl⟩
  obtain ⟨k', hk'⟩ := key 0
  have hk : ∀ y, k' y = k y := fun y => by simp [hk']
  refine ⟨k', hk, fun m => ?_⟩
  obtain ⟨g, hg⟩ := key m
  exact ⟨g, fun y => by rw [hg, hk]⟩

theorem factorRapid : FactorRapid := by
  intro h hr
  obtain ⟨h₁, e₁, r₁⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => phaseRoot (h y))
    (continuous_phaseRoot.comp h.continuous) (fun y => norm_phaseRoot _)
  obtain ⟨h₂, e₂, r₂⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => ((Real.sqrt ‖h y‖ : ℝ) : ℂ))
    (by have := h.continuous; fun_prop)
    (fun y => by rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)])
  have hs : star h₂ = h₂ := by
    ext y
    rw [ZeroAtInftyContinuousMap.star_apply, e₂]
    simp
  refine ⟨h₁, h₂, r₁, r₂, by rwa [hs], ?_⟩
  ext y
  rw [ZeroAtInftyContinuousMap.mul_apply, e₁, e₂]
  by_cases hy : h y = 0
  · simp [hy, phaseRoot]
  · have hne : ((Real.sqrt ‖h y‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖h y‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hy)
      exact_mod_cast this.ne'
    simp only [phaseRoot]
    field_simp

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdSkewEqConst
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem rd_skew_eq_const {n : ℕ} (E : KMod n) (Y : Mat n) (hY : Yᴴ = -Y) :
    ∃ B : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g) := by
  obtain ⟨c, hc, c0, cadd, cd⟩ := _root_.GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve.exists_unitary_curve Y hY
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← cadd, add_neg_cancel, c0])
  let Φ : ℝ → (E.V →L[ℂ] E.V) := fun t => E.ρ (c (-t))
  have hΦc : Continuous Φ := E.cont.comp (hc.comp continuous_neg)
  have hΦ0 : Φ 0 = 1 := by simp only [Φ, neg_zero, c0, map_one]
  have hΦa : ∀ s t, Φ (s + t) = Φ s * Φ t := fun s t => by
    simp only [Φ, neg_add, cadd, map_mul]
  obtain ⟨B, hB⟩ := GlobalTheory.T.continuous_one_param_differentiable Φ hΦc hΦ0 hΦa
  refine ⟨B, fun f hf g hg => ?_⟩
  have hk : ∀ t, f (g * (c t).1) = Φ t (f g) := fun t => by
    rw [hf.2 g hg (c t), hinv]
  have h1 : HasDerivAt (fun t => Φ t (f g)) (B (f g)) 0 :=
    ((ContinuousLinearMap.apply ℂ E.V (f g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hB
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)
  have h2 : HasDerivAt (fun t => g * (c t).1) (g * Y) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 cd
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp)
  have h3 : HasFDerivAt f (fderiv ℝ f g) (g * (c 0).1) := by
    simpa [c0] using hd.hasFDerivAt
  have h4 : HasDerivAt (fun t => f (g * (c t).1)) (fderiv ℝ f g (g * Y)) 0 :=
    h3.comp_hasDerivAt 0 h2
  have h5 : (fun t => f (g * (c t).1)) = fun t => Φ t (f g) := funext hk
  rw [h5] at h4
  exact h4.unique h1

end GlobalTheory.CompanionTheory.WaveSpd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelWordOrderSwap
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.KerSwap

theorem isKer_swap : WaveSpeed → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E (w ++ w') g K → IsKer μ E (w' ++ w) g K := by
  intro hW hR n _ _ μ _ E w w' g T K hg hK
  refine ⟨hK.1, hK.2.1, hK.2.2.1, fun u hu x hx => ?_⟩
  rw [hK.2.2.2 u hu x hx]
  have hs : ContDiffOn ℝ ∞ (fun x' => ∫ t : ℝ, (g t : ℂ) • u t x') (GLs n) := by
    have h1 := ((GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg hW n E u g T hu hg).2.1 0).1
    simpa only [zero_add] using h1
  exact GlobalTheory.CompanionTheory.WaveMult.Swap.zOp_swap hR n w w' _ hs x hx

end GlobalTheory.CompanionTheory.WaveMult.KerSwap
end
end

