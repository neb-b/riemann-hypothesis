module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartRightInverse
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerShearHaar.MeasurePreservingOfCard

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.AeProductMemUnipotentAndNilradical
section
noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def PiCont : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)), inWb k r z → 0 < Tz k r z →
    IsHCTypeW k r z u π → ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z)

theorem ellA_cont (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  unfold ellA
  split_ifs with h
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ j).mul continuous_const

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (ellA_cont z a)))))

theorem inv_contOn : ContinuousOn (fun h : Mat k r => h⁻¹) (Gr k r) := by
  unfold Gr
  have key : ∀ h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), h⁻¹ = (h.det)⁻¹ • h.adjugate := fun h _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContinuousOn.congr ?_ key
  exact ((continuous_id.matrix_det.continuousOn).inv₀
    (fun h hh => (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh).ne_zero)).smul continuous_id.matrix_adjugate.continuousOn

theorem ae_product_mem_unipotent_and_nilradical {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : μW {x | Matrix.of x ∉ UWset k r z} = 0) (hN : μN {x | Matrix.of x ∉ Nset k r} = 0)
    (hUWG : UWset k r z ⊆ Gr k r) (hNG : Nset k r ⊆ Gr k r) :
    ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) ∧
      (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r) := by
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} = {x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p
      simp
    rw [e, Measure.prod_prod, hW, zero_mul]
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.2 ∈ Nset k r} = Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r} := by
      ext p
      simp
    rw [e, Measure.prod_prod, hN, mul_zero]
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨⟨hp1, hp2⟩, hp1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (hUWG hp1) (hNG hp2)⟩

section Meas

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem bInt_aesm (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hσ : IsURepOn (Gr k r) σ)
    {μW μN : Measure (Mt k r)}
    (hUWc : IsClosed (UWset k r z)) (hUWG : UWset k r z ⊆ Gr k r)
    (hUWinv : ∀ h ∈ UWset k r z, h⁻¹ ∈ UWset k r z)
    (hπc : ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z))
    (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r)
    (w' : H) (ξ : Vp) (v : H) : AEStronglyMeasurable (bInt z c σ π w' ξ v) (μW.prod μN) := by
  set T : Set (Mt k r × Mt k r) :=
    {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r} with hTdef
  have hfst : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r) := continuous_fst
  have hsnd : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r) := continuous_snd
  have hmul : Continuous fun p : Mt k r × Mt k r => Matrix.of p.1 * Matrix.of p.2 :=
    hfst.matrix_mul hsnd
  have hTc : IsClosed T := (hUWc.preimage hfst).inter (gr_isClosed.preimage hmul)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1 * Matrix.of p.2) v) T :=
    (hσ.2.2 v).comp hmul.continuousOn (fun p hp => hp.2)
  have hi : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1)⁻¹) T :=
    inv_contOn.comp hfst.continuousOn (fun p hp => hUWG hp.1)
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹ ξ) T :=
    (hπc ξ).comp hi (fun p hp => hUWinv _ hp.1)
  have h3 : Continuous fun p : Mt k r × Mt k r => star (psiGen k r z c (Matrix.of p.2)) :=
    continuous_star.comp ((psiGen_cont z c).comp hsnd)
  have hcont : ContinuousOn (bInt z c σ π w' ξ v) T :=
    ((continuousOn_const.inner h1).mul h3.continuousOn).smul h2
  have := hcont.aestronglyMeasurable (μ := μW.prod μN) hTc.measurableSet
  have hae' : ∀ᵐ p ∂(μW.prod μN), p ∈ T := hae
  rwa [Measure.restrict_eq_self_of_ae_mem hae'] at this

end Meas

theorem aInt_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : AInt := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g hg
  obtain ⟨C, _, hCb⟩ := aBound_of hSG hD hRG hS hPi hNI hU k r z c u v b H σ Vp π w μG μS ν μW μN
    hH hR hC x₀ hx₀ ξ
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, _, _⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have := hμW.1
  have := hμN.1
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  refine ⟨bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG (fun h hh => (hUW h hh h hh).2.1)
    (hPC k r z u Vp π hz hT hHC) (hae.mono fun p hp => hp.2) _ _ _, ?_⟩
  exact (hCb g hg).trans_lt ENNReal.ofReal_lt_top

theorem aCont_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : ACont := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g₀ hg₀
  have : FirstCountableTopology (Mat k r) :=
    inferInstanceAs (FirstCountableTopology (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨Cφ, hCφ0, hCφ⟩ := ptDecay_of hSG hD hRG k r z c u v b H σ Vp π w μG μS ν μW μN hH hR hC x₀ hx₀
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, hWfin, hNc⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have hPU := (hPi k r z u Vp π hz hT hHC).2
  obtain ⟨Kw, hKw⟩ := (hU k r z hz hT).exists_bound_of_continuousOn
    (opn_continuous (k := k) (r := r)).continuousOn
  have hKw0 : 0 ≤ max Kw 0 := le_max_right _ _
  have hinvb : ∀ h ∈ UWset k r z, opn h⁻¹ ≤ max Kw 0 := fun h hh =>
    le_max_of_le_left ((Real.le_norm_self _).trans (hKw _ (hUW h hh h hh).2.1))
  have := hμW.1
  have := hμN.1
  have hN := nilradical_half_sum_nonneg (k := k) (r := r)
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  have hH2 : 0 ≤ opn (Hpk k r) * opn (Hpk k r) := mul_nonneg (opn_nonneg _) (opn_nonneg _)
  set K0 := Cφ * (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r * ‖ξ‖
    with hK0d
  have hK0 : 0 ≤ K0 := mul_nonneg (mul_nonneg hCφ0 (Real.rpow_nonneg (mul_nonneg hKw0
    (mul_nonneg hH2 (by linarith [opn_nonneg g₀]))) _)) (norm_nonneg _)
  have hmeas : Measurable fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r) :=
    (show Continuous fun m : Mt k r => opn (Matrix.of m) from opn_continuous).measurable.pow_const _
  have hgi : Integrable (fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r)) μN := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun m =>
      Real.rpow_nonneg (opn_nonneg _) _)]
    exact hNI k r μN hμN hNc
  have hbi : Integrable (fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
      (μW.prod μN) := by
    have := (integrable_const (1 : ℝ) (μ := μW)).mul_prod hgi
    simpa using this.const_mul K0
  show ContinuousWithinAt (fun g => ∫ p, bInt z c σ π (σ x₀ w) ξ (σ g w) p ∂(μW.prod μN))
    (Gr k r) g₀
  apply continuousWithinAt_of_dominated
    (bound := fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
  · exact Filter.Eventually.of_forall fun g => bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG
      (fun h hh => (hUW h hh h hh).2.1) (hPC k r z u Vp π hz hT hHC)
      (hae.mono fun p hp => hp.2) _ _ _
  · have hev1 : ∀ᶠ g in 𝓝[Gr k r] g₀, g ∈ Gr k r := self_mem_nhdsWithin
    have hev2 : ∀ᶠ g in 𝓝[Gr k r] g₀, opn g < opn g₀ + 1 :=
      eventually_nhdsWithin_of_eventually_nhds
        ((opn_continuous (k := k) (r := r)).continuousAt.eventually (gt_mem_nhds (lt_add_one _)))
    filter_upwards [hev1, hev2] with g hg hlt
    filter_upwards [hae] with p hp
    refine (bInt_bound z c hσ (π := π) hCφ hKw0 ξ p (hUWG hp.1.1) (hinvb _ hp.1.1)
      (hPU _ (hUW _ hp.1.1 _ hp.1.1).2.1 ξ) (hNG hp.1.2) hg).trans ?_
    have hle : (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N1H k r ≤
        (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r :=
      Real.rpow_le_rpow (mul_nonneg hKw0 (mul_nonneg hH2 (opn_nonneg _)))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlt.le hH2) hKw0) hN
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle hCφ0) (norm_nonneg _)) (Real.rpow_nonneg (opn_nonneg _) _)
  · exact hbi
  · refine Filter.Eventually.of_forall fun p => ?_
    have h1 : ContinuousWithinAt (fun g => σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)) (Gr k r) g₀ :=
      (σ _).continuous.continuousAt.comp_continuousWithinAt (hσ.2.2 w g₀ hg₀)
    exact ((continuousWithinAt_const.inner h1).mul continuousWithinAt_const).smul
      continuousWithinAt_const

end WlocSk.PtD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NShear
section
open Matrix Formalism.QuantumDeterminants MeasureTheory

noncomputable section

namespace WlocSk.NB

variable {k r : ℕ}

def rk : CI k r → ℕ
  | Sum.inl p => r - p.1.1.val
  | Sum.inr (Sum.inl q) => r - q.1.val
  | Sum.inr (Sum.inr _) => r + 1

def dlt (m₀ : Mx k r) (x : CI k r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (cF x)ᴴ * ((bF m₀)ᴴ * (bB m₀ * cE x + bC m₀ * cF x))

def shG (m₀ : Mx k r) (x : CI k r → ℂ) : CI k r → ℂ
  | Sum.inl p => ∑ c, if p.1.1 < c then bA m₀ p.1.1 c * cA x c p.1.2 else 0
  | Sum.inr (Sum.inl q) => (∑ c, if q.1 < c then bA m₀ q.1 c * cB x c q.2 else 0) + bB m₀ q.1 q.2
  | Sum.inr (Sum.inr p) => (dlt m₀ x p.1.1 p.1.2 - star (dlt m₀ x p.1.2 p.1.1)) / 2

def shH (m₀ : Mx k r) (x : CI k r → ℂ) : Fin r → ℝ := fun a => (dlt m₀ x a a).im

theorem split_low {A : Matrix (Fin r) (Fin r) ℂ} (hA : LowId A) (v : Fin r → ℂ) (a : Fin r) :
    ∑ c, A a c * v c = v a + ∑ c, if a < c then A a c * v c else 0 := by
  have : ∀ c, A a c * v c = (if a = c then v c else 0) + (if a < c then A a c * v c else 0) := by
    intro c
    rcases lt_trichotomy a c with h | rfl | h
    · rw [if_neg (ne_of_lt h), if_pos h, zero_add]
    · rw [if_pos rfl, if_neg (lt_irrefl a), add_zero, hA a a le_rfl, if_pos rfl, one_mul]
    · rw [if_neg (ne_of_gt h), if_neg (not_lt.2 h.le), add_zero, hA a c h.le, if_neg (ne_of_gt h),
        zero_mul]
  rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

theorem lowId_bA {g : Mx k r} (hc : ColB g) : LowId (bA g) := fun a b h => hc.aa a b h

theorem mof_mul {m₀ g : Mx k r} (h0 : m₀ ∈ Nset k r) (hg : g ∈ Nset k r) :
    mof (m₀ * g) = mof g + (bF g)ᴴ * ((bF m₀)ᴴ * (bB m₀ * bE g + bC m₀ * bF g)) := by
  have hc0 := colB_of_mem h0
  have hF0 := rel_F hc0 h0.1
  rw [mof, mof, bF_mul hc0, bC_mul, conjTranspose_mul]
  rw [add_assoc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  have : (bF g)ᴴ * (bF m₀)ᴴ * (bA m₀ * bC g) = (bF g)ᴴ * bC g := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bF m₀)ᴴ, hF0, Matrix.one_mul]
  rw [this]
  simp only [Matrix.mul_assoc, Matrix.mul_add]

theorem lmul_coord {m₀ : Mx k r} (h0 : m₀ ∈ Nset k r) (x : CI k r → ℂ) (s : Fin r → ℝ) :
    psiC (m₀ * phi0 x s) = x + shG m₀ x ∧ psiR (m₀ * phi0 x s) = s + shH m₀ x := by
  have hg := test_vector_mem_schwartz_bruhat x s
  have hcg := colB_of_mem hg
  have hc0 := colB_of_mem h0
  have hps := nilpotent_chart_right_inverse x s
  have hM : mof (m₀ * phi0 x s) = mof (phi0 x s) + dlt m₀ x := by
    rw [mof_mul h0 hg, dlt, phi0, bF_mk, bE_mk]
  constructor
  · funext i
    rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
    · show bA (m₀ * phi0 x s) a b = _
      rw [bA_mul hcg, Matrix.mul_apply, phi0, bA_mk, split_low (lowId_bA hc0)]
      simp only [Pi.add_apply, shG, cA, dif_pos h]
    · show bB (m₀ * phi0 x s) a j = _
      rw [bB_mul hcg, Matrix.add_apply, Matrix.mul_apply, phi0, bB_mk, split_low (lowId_bA hc0)]
      simp only [Pi.add_apply, shG, cB]
      ring
    · show kof (m₀ * phi0 x s) a b = _
      have e1 : kof (phi0 x s) a b = x (Sum.inr (Sum.inr ⟨(a, b), h⟩)) :=
        congrFun hps.1 (Sum.inr (Sum.inr ⟨(a, b), h⟩))
      simp only [kof, hM, Matrix.add_apply, Pi.add_apply, shG, star_add] at e1 ⊢
      rw [← e1]
      ring
  · funext a
    have e1 : (mof (phi0 x s) a a).im = s a := congrFun hps.2 a
    show (mof (m₀ * phi0 x s) a a).im = _
    rw [hM, Matrix.add_apply, Complex.add_im, e1]
    rfl

theorem shG_dep (m₀ : Mx k r) (i : CI k r) (x y : CI k r → ℂ)
    (hxy : ∀ j, rk j < rk i → x j = y j) : shG m₀ x i = shG m₀ y i := by
  have hAB : (∀ j, rk j ≤ r → x j = y j) → cA x = cA y ∧ cB x = cB y := by
    intro h
    refine ⟨?_, ?_⟩
    · ext a b; unfold cA; split_ifs with h1
      · exact h _ (by simp only [rk]; omega)
      · rfl
      · rfl
    · ext a j; exact h _ (by simp only [rk]; omega)
  rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · simp only [shG]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · congr 1
      unfold cA
      split_ifs with hcb
      · exact hxy _ (by simp only [rk]; have := c.isLt; have : a.val < c.val := hac; omega)
      · rfl
      · rfl
    · rfl
  · simp only [shG]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · congr 1
      exact hxy _ (by simp only [rk]; have := c.isLt; have : a.val < c.val := hac; omega)
    · rfl
  · obtain ⟨hA, hB⟩ := hAB fun j hj => hxy j (by show rk j < r + 1; omega)
    simp only [shG, dlt, cF, cE, hA, hB]

theorem continuous_dlt (m₀ : Mx k r) : Continuous (dlt m₀) :=
  continuous_cF.matrix_conjTranspose.matrix_mul (continuous_const.matrix_mul
    ((continuous_const.matrix_mul continuous_cE).add (continuous_const.matrix_mul continuous_cF)))

theorem continuous_shG (m₀ : Mx k r) (i : CI k r) : Continuous fun x => shG m₀ x i := by
  rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · simp only [shG]
    refine continuous_finsetSum _ fun c _ => ?_
    split_ifs
    · exact continuous_const.mul (continuous_cA.matrix_elem _ _)
    · exact continuous_const
  · simp only [shG]
    refine (continuous_finsetSum _ fun c _ => ?_).add continuous_const
    split_ifs
    · exact continuous_const.mul (continuous_cB.matrix_elem _ _)
    · exact continuous_const
  · simp only [shG]
    exact (((continuous_dlt m₀).matrix_elem _ _).sub ((continuous_dlt m₀).matrix_elem _ _).star).div_const _

theorem continuous_shH (m₀ : Mx k r) : Continuous (shH m₀) :=
  continuous_pi fun a => Complex.continuous_im.comp ((continuous_dlt m₀).matrix_elem a a)

theorem shear_mp {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (rkf : ι → ℕ) (G : (ι → ℂ) → ι → ℂ)
    (H : (ι → ℂ) → Fin d → ℝ) (hG : ∀ i, Measurable fun x => G x i)
    (hdep : ∀ i (x y : ι → ℂ), (∀ j, rkf j < rkf i → x j = y j) → G x i = G y i)
    (hH : Measurable H) :
    MeasurePreserving (fun t : (ι → ℂ) × (Fin d → ℝ) => (t.1 + G t.1, t.2 + H t.1)) volume volume := by
  have h1 : MeasurePreserving (fun x : ι → ℂ => fun i => x i + G x i) volume volume :=
    PI.LowSplitHaarW.triShear ι rkf (fun i x => G x i) hG hdep
  have h2 := h1.skew_product (μc := (volume : Measure (Fin d → ℝ))) (μd := volume)
    (g := fun x s => s + H x) (measurable_snd.add (hH.comp measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (H x))
  exact h2

end WlocSk.NB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartNormBound
section
open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace WlocSk.NB

variable {k r : ℕ}

theorem opn_nonneg' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.L2.SG.WuDecay.opn M :=
  norm_nonneg _

theorem entry_le_opn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖M i j‖ ≤ Formalism.L2.SG.WuDecay.opn M := by
  unfold Formalism.L2.SG.WuDecay.opn
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M).le_opNorm
    (EuclideanSpace.single j (1 : ℂ))
  rw [PiLp.norm_single, norm_one, mul_one] at h1
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h1)
  rw [Matrix.ofLp_toEuclideanCLM, PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply]

theorem one_le_opn {g : Mx k r} (hg : g ∈ Nset k r) : 1 ≤ Formalism.L2.SG.WuDecay.opn g := by
  have h := entry_le_opn g (wI k r 0) (wI k r 0)
  rw [(colB_of_mem hg).ww 0 0, if_pos rfl, norm_one] at h
  exact h

theorem mof_le (g : Mx k r) (a b : Fin r) :
    ‖mof g a b‖ ≤ r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  rw [mof, Matrix.mul_apply]
  calc ‖∑ c, (bF g)ᴴ a c * bC g c b‖ ≤ ∑ c, ‖(bF g)ᴴ a c * bC g c b‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin r, Formalism.L2.SG.WuDecay.opn g ^ 2 := Finset.sum_le_sum fun c _ => by
        rw [norm_mul, conjTranspose_apply, norm_star, sq]
        exact mul_le_mul (entry_le_opn g (esI k r c) (esI k r a)) (entry_le_opn g (eI k r c) (esI k r b))
          (norm_nonneg _) (opn_nonneg' _)
    _ = r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by simp

theorem kof_le (g : Mx k r) (a b : Fin r) :
    ‖kof g a b‖ ≤ r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [kof, norm_div, h2]
  have := norm_sub_le (mof g a b) (star (mof g b a))
  rw [norm_star] at this
  have h1 := mof_le g a b
  have h3 := mof_le g b a
  linarith

theorem psiC_le {g : Mx k r} (hg : g ∈ Nset k r) (i : CI k r) :
    ‖psiC g i‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  set o := Formalism.L2.SG.WuDecay.opn g with ho
  have h1 : 1 ≤ o := one_le_opn hg
  have hoo : o ≤ o ^ 2 := by nlinarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ho2 : 0 ≤ o ^ 2 := sq_nonneg o
  rcases i with p | q | p
  · have := entry_le_opn g (eI k r p.1.1) (eI k r p.1.2)
    show ‖g _ _‖ ≤ _
    nlinarith
  · have := entry_le_opn g (eI k r q.1) (wI k r q.2)
    show ‖g _ _‖ ≤ _
    nlinarith
  · have := kof_le g p.1.1 p.1.2
    show ‖kof g _ _‖ ≤ _
    nlinarith

theorem psiR_le (g : Mx k r) (a : Fin r) :
    ‖psiR g a‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  have h := mof_le g a a
  have h' : ‖psiR g a‖ ≤ ‖mof g a a‖ := by
    rw [psiR, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
  have ho2 : 0 ≤ Formalism.L2.SG.WuDecay.opn g ^ 2 := sq_nonneg _
  nlinarith

theorem growth (g : Mx k r) (hg : g ∈ Nset k r) :
    1 + ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn (Matrix.of g) ^ 2 := by
  show 1 + ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn g ^ 2
  have h1 : 1 ≤ Formalism.L2.SG.WuDecay.opn g := one_le_opn hg
  have hB : 0 ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by positivity
  have hC : ‖psiC g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 :=
    (pi_norm_le_iff_of_nonneg hB).2 fun i => psiC_le hg i
  have hR : ‖psiR g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 :=
    (pi_norm_le_iff_of_nonneg hB).2 fun a => psiR_le g a
  have hP : ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
    rw [Prod.norm_def]; exact max_le hC hR
  nlinarith

theorem nilpotent_chart_norm_bound (x : CI k r → ℂ) (s : Fin r → ℝ) :
    1 + ‖(x, s)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn (Matrix.of (phi0 x s)) ^ 2 := by
  have h := growth (phi0 x s) (test_vector_mem_schwartz_bruhat x s)
  rw [(nilpotent_chart_right_inverse x s).1, (nilpotent_chart_right_inverse x s).2] at h
  exact h

end WlocSk.NB

end
end

