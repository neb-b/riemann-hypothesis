module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.EIntBound
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def EInt (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r') : ℝ≥0∞ :=
  ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))

theorem eInt_bound (hGL : GNLower) (hHA : HeisAct) (hHC : HeisClosed) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      EInt k r' A c g ≤ ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  exact ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.eInt_bound' hGL hHA hCL hCM k r' A hA

theorem cInt_fin (n : ℕ) (σ : ℝ) (h1 : 1 < σ) (h2 : σ < 2 * (n : ℝ) + 1) :
    (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
      ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹)) < ∞ := by
  have hF0 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioc 0 1) := by
    refine Integrable.mono'
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 * (n : ℝ) - σ)
        (by linarith)).1 ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := hy.1
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) hA) hy0.le
        _ = y ^ (2 * (n : ℝ) - σ) := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one]
  have hF1 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -σ) (by linarith) zero_lt_one) ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := zero_lt_one.trans hy
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y ^ (-((2 * n + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_left _ _) hA) hy0.le
        _ = y ^ (-σ) := by
          rw [← mul_assoc, mul_comm y, ← Real.rpow_add_one hy0.ne', ← Real.rpow_add hy0]
          congr 1
          push_cast
          ring
  have hY : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hF0.union hF1
  have hI : Integrable (fun c : ℂ => ‖c‖ ^ (2 * (n : ℝ) - σ) *
      min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) volume := by
    first
      | exact (integrable_fun_norm_addHaar volume
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
      | exact (integrable_fun_norm_addHaar (μ := volume)
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
  calc (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
        ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹))
      = ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ) *
          min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) :=
        lintegral_congr fun c => (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm
    _ < ∞ := hI.lintegral_lt_top

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExistsKmat
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

theorem exists_K (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κL : EE k r ≃ₗᵢ[ℂ] EE k r, (∀ a, κL (c a) = u a) ∧ ∀ x, κL (HE k r x) = HE k r (κL x) := by
  have hF : ∀ w : Fin (r + 1) → EE k r, Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      Orthonormal ℂ (Sum.elim w (fun a => HE k r (w a))) := by
    intro w hw hwi
    rw [orthonormal_iff_ite] at hw ⊢
    rintro (a | a) (b | b)
    · simp [hw]
    · simp [hwi]
    · simp [HE_adj, hwi]
    · simp [HE_adj, HE_HE, hw]
  have hcard : Module.finrank ℂ (EE k r) = Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) := by
    simp; omega
  have hres : ∀ w : Fin (r + 1) ⊕ Fin (r + 1) → EE k r, Orthonormal ℂ w →
      Orthonormal ℂ ((Set.range (Sum.inl : _ → (Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1))).restrict
        (Sum.elim w 0)) := by
    intro w hw
    rw [orthonormal_iff_ite] at hw ⊢
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    change inner ℂ (w p) (w q) = _
    rw [hw p q]
    by_cases hpq : p = q
    · subst hpq; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpq, if_neg]; intro h; exact hpq (Sum.inl_injective (congrArg Subtype.val h))
  obtain ⟨bP, hbP⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF c hc hci))
  obtain ⟨bQ, hbQ⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF u hu hui))
  have hP : ∀ p, bP (Sum.inl p) = Sum.elim c (fun a => HE k r (c a)) p := fun p => hbP _ ⟨p, rfl⟩
  have hQ : ∀ p, bQ (Sum.inl p) = Sum.elim u (fun a => HE k r (u a)) p := fun p => hbQ _ ⟨p, rfl⟩
  set κL := bP.repr.trans bQ.repr.symm with hκL
  have hκb : ∀ i, κL (bP i) = bQ i := fun i => by simp [hκL]
  have hc1 : ∀ a, κL (c a) = u a := fun a => by
    have := hκb (Sum.inl (Sum.inl a)); rwa [hP, hQ] at this
  have hc2 : ∀ a, κL (HE k r (c a)) = HE k r (u a) := fun a => by
    have := hκb (Sum.inl (Sum.inr a)); rwa [hP, hQ] at this
  have hfix : ∀ (b : OrthonormalBasis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) ℂ (EE k r))
      (w : Fin (r + 1) → EE k r), Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      (∀ p, b (Sum.inl p) = Sum.elim w (fun a => HE k r (w a)) p) →
      ∀ j, HE k r (b (Sum.inr j)) = b (Sum.inr j) := by
    intro b w hw hwi hb j
    refine fix_of_perp w hw hwi _ (fun a => ?_) (fun a => ?_)
    · have := hb (Sum.inl a); simp only [Sum.elim_inl] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
    · have := hb (Sum.inr a); simp only [Sum.elim_inr] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
  refine ⟨κL, hc1, fun x => ?_⟩
  have key : (κL.toLinearEquiv.toLinearMap).comp (HE k r) = (HE k r).comp κL.toLinearEquiv.toLinearMap := by
    refine bP.toBasis.ext fun i => ?_
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rcases i with (a | a) | j
    · rw [hP, Sum.elim_inl, hc2, hc1]
    · rw [hP, Sum.elim_inr, HE_HE, hc1, hc2, HE_HE]
    · rw [hfix bP c hc hci hP j, hκb, hfix bQ u hu hui hQ j]
  simpa using LinearMap.congr_fun key x

theorem exists_Kmat (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κ ∈ Kset k r, ∀ a, (WithLp.toLp 2 (κ *ᵥ (c a).ofLp) : EE k r) = u a := by
  obtain ⟨κL, hκc, hκH⟩ := exists_K hk c u hc hu hci hui
  set κ : Mat k r := Matrix.toEuclideanLin.symm κL.toLinearEquiv.toLinearMap with hκdef
  have hκ : ∀ v, (WithLp.toLp 2 (κ *ᵥ v) : EE k r) = κL (WithLp.toLp 2 v) := by
    intro v
    have h1 : Matrix.toEuclideanLin κ = κL.toLinearEquiv.toLinearMap := LinearEquiv.apply_symm_apply _ _
    have := LinearMap.congr_fun h1 (WithLp.toLp 2 v)
    rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp] at this
    exact this
  have hunit : κᴴ * κ = 1 := by
    ext i j
    have h2 : inner ℂ (WithLp.toLp 2 (κ *ᵥ Pi.single i 1) : EE k r) (WithLp.toLp 2 (κ *ᵥ Pi.single j 1)) =
        inner ℂ (WithLp.toLp 2 (Pi.single i 1) : EE k r) (WithLp.toLp 2 (Pi.single j 1)) := by
      rw [hκ, hκ, LinearIsometryEquiv.inner_map_map]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct] at h2
    simp only [Matrix.mul_apply, conjTranspose_apply, one_apply]
    convert h2 using 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      simp [mulVec_single, mul_comm]
    · simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  have hv : ∀ v, κ *ᵥ (Hpk k r *ᵥ v) = Hpk k r *ᵥ (κ *ᵥ v) := by
    intro v
    have := hκH (WithLp.toLp 2 v)
    rw [HE_apply, WithLp.ofLp_toLp, ← hκ, ← hκ, HE_apply, WithLp.ofLp_toLp] at this
    simpa using congrArg WithLp.ofLp this
  have hcomm : κ * Hpk k r = Hpk k r * κ := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  refine ⟨κ, ⟨?_, hunit⟩, fun a => ?_⟩
  · show κᴴ * Hpk k r * κ = Hpk k r
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  · rw [hκ, WithLp.toLp_ofLp, hκc]

theorem inner_bvec (i : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (bvec i) : EE k r) (WithLp.toLp 2 v) = v i := by
  first
    | (simp [bvec, PiLp.inner_apply, Pi.single_apply])
    | (show inner ℂ (EuclideanSpace.single i (1 : ℂ)) (WithLp.toLp 2 v : EE k r) = v i
       rw [EuclideanSpace.inner_single_left]; simp)

theorem phiV_apply (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV k r b i = if b.val < r then (if i.val = 2 * r + k - b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0)) := by
  unfold phiV
  by_cases hb : (b : ℕ) < r
  · rw [dite_eq_left hb, if_pos hb]
    show (Pi.single (esI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = _
    rw [Pi.single_apply]
    by_cases hi : (i : ℕ) = 2 * r + k - b.val
    · rw [if_pos hi, if_pos (show i = esI k r ⟨b.val, hb⟩ from Fin.ext hi)]
    · rw [if_neg hi, if_neg (show ¬ i = esI k r ⟨b.val, hb⟩ from fun h => hi (congrArg Fin.val h))]
  · rw [dite_eq_right hb, if_neg hb]
    simp [epsV, bvec, Pi.single_apply, Fin.ext_iff]
    have e1 : ((wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by first | rfl | simp [wI]
    have e2 : ((wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by first | rfl | simp [wI]
    rw [e1, e2]

theorem toLp_phiV (a : Fin (r + 1)) : (WithLp.toLp 2 (phiV k r a) : EE k r) =
    if a.val < r then WithLp.toLp 2 (bvec ⟨2 * r + k - a.val, by omega⟩) else
      ((Real.sqrt 2)⁻¹ : ℂ) • (WithLp.toLp 2 (bvec ⟨r, by omega⟩) + WithLp.toLp 2 (bvec ⟨r + k, by omega⟩)) := by
  ext i
  by_cases ha : a.val < r
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff]
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff, mul_add, mul_ite]

theorem hcc : star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    first
      | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
      | simp
  rw [hs, ← mul_inv, h2]; norm_num

theorem qe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV k r a) : EE k r)) := by
  have key : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := hcc
  rw [orthonormal_iff_ite]
  intro a b
  have hA := a.isLt
  have hB := b.isLt
  rw [toLp_phiV]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, phiV_apply]
    split_ifs <;> first
      | rfl
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, phiV_apply, phiV_apply]
    split_ifs <;> first
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | (exfalso; exact ‹¬a = b› (Fin.ext (by omega)))
      | (exfalso; simp_all; done)
      | (exfalso; simp_all <;> omega)
      | (simp; done)
      | (simp only [add_zero, zero_add, mul_one]; linear_combination (2 : ℂ) * key)

end ReciprocityTheory.ChartRestriction.DS.Xi.GS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GaNonneg
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem H_es (k r : ℕ) (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  have ha := a.isLt
  funext i
  have hi := i.isLt
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem row_fix {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : h (eI k r a) j = if j = eI k r a then 1 else 0 := by
  obtain ⟨hU, hfix, -⟩ := hm
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have h1 : hᴴ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
    have := congrArg (fun M => M *ᵥ bvec (esI k r a)) hU'
    simp only [← Matrix.mulVec_mulVec, (hfix a).2, H_es] at this
    exact this
  have h2 := congrFun h1 j
  simp only [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  have h3 := congrArg star h2
  rw [star_star] at h3
  rw [h3]
  split_ifs <;> simp

theorem row_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (v : Fin (2 * r + k + 1) → ℂ) : (h *ᵥ v) (eI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, row_fix hm a, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem inv_fix {k r : ℕ} {h : Mat k r} (hu : IsUnit h.det) {v : Fin (2 * r + k + 1) → ℂ} (hv : h *ᵥ v = v) :
    h⁻¹ *ᵥ v = v := by
  calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem conj_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (n : Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : h⁻¹ *ᵥ v = v) (a : Fin r) :
    ((h * n * h⁻¹) *ᵥ v) (eI k r a) = (n *ᵥ v) (eI k r a) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, row_apply hm a]

theorem lam_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z)
    (hu : IsUnit h.det) (n : Mat k r) : lam k r z (h * n * h⁻¹) = lam k r z n := by
  have hent : ∀ (g : Mat k r) (i j : Fin (2 * r + k + 1)), g i j = (g *ᵥ bvec j) i := by
    intro g i j
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hz : h⁻¹ *ᵥ z = z := inv_fix hu hm.2.2
  have hell : ell k r z (h * n * h⁻¹) = ell k r z n := by
    unfold ell
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with hlt
    · rw [hent (h * n * h⁻¹), hent n]
      exact conj_apply hm n _ (inv_fix hu (hm.2.1 _).1) a
    · exact conj_apply hm n z hz a
  simp only [lam, hell]

end ReciprocityTheory.ChartRestriction.DS.Xi.XI

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB

theorem ga_nonneg (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : 0 ≤ Ga k r l Y := by
  unfold Ga
  let M : Matrix (Fin (2 * r + k + 1)) (Fin (l.val + 1)) ℂ := fun i b => Y (Fin.castLE (by omega) b) i
  have key : 0 ≤ ((Mᴴ * M).det).re := by
    open scoped ComplexOrder in
    have h0 := Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self M).det_nonneg
    rw [Complex.zero_re] at h0
    exact h0.1
  convert key using 3
  ext a b
  first
    | rfl
    | (simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply, M]; rfl)

theorem rpow_bd (a b K s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 1 ≤ K) (hs : 0 ≤ s) (h1 : b ≤ K * a)
    (h2 : a ≤ K * b) : a ^ (-s) ≤ K ^ s * b ^ (-s) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have hb0 : b = 0 := le_antisymm (by simpa using h1) hb
    subst hb0
    have h3 : 1 ≤ K ^ s := Real.one_le_rpow hK hs
    have h4 : 0 ≤ (0:ℝ) ^ (-s) := Real.rpow_nonneg le_rfl _
    nlinarith
  · have hbpos : 0 < b := by
      by_contra hc
      push_neg at hc
      nlinarith
    rw [Real.rpow_neg ha, Real.rpow_neg hb]
    have hbs : b ^ s ≤ K ^ s * a ^ s := by
      rw [← Real.mul_rpow (by linarith) ha]
      exact Real.rpow_le_rpow hb h1 hs
    have hapos : 0 < a ^ s := Real.rpow_pos_of_pos hpos s
    have hbpos' : 0 < b ^ s := Real.rpow_pos_of_pos hbpos s
    rw [← div_eq_mul_inv, inv_eq_one_div]
    first
      | (rw [div_le_div_iff_of_pos hapos hbpos']; linarith)
      | (rw [div_le_div_iff₀ hapos hbpos']; linarith)

theorem gN_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ gN g := Real.sqrt_nonneg _

theorem ga_two {k r : ℕ} (A : Mat k r) (K : ℝ) (hA : gN A ≤ K) (l : Fin (r + 1))
    (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (K ^ (l.val + 1)) ^ 2 * Ga k r l Y := by
  refine (ga_mul_le k r A l Y).trans (mul_le_mul_of_nonneg_right ?_ (ga_nonneg k r l Y))
  rw [← pow_mul, ← pow_mul, mul_comm]
  exact pow_le_pow_left₀ (gN_nonneg A) hA _

theorem xi_bd {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (h : Mat k r) (hu : IsUnit h.det) (K : ℝ)
    (hK : 1 ≤ K) (h1 : gN h ≤ K) (h2 : gN h⁻¹ ≤ K) (m : Mat k r) :
    xiR k r s (h * m) ≤ (∏ l, (K ^ (l.val + 1)) ^ s l) * xiR k r s m := by
  unfold xiR
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro l _
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  · intro l _
    have hK0 : 0 ≤ K ^ (l.val + 1) := pow_nonneg (by linarith) _
    have hK' : 1 ≤ K ^ (l.val + 1) := one_le_pow₀ hK
    have e1 : Ga k r l (fun a => (h * m) *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => m *ᵥ phiV k r a) := by
      have := ga_two h K h1 l (fun a => m *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec] at this
      exact this
    have e2 : Ga k r l (fun a => m *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => (h * m) *ᵥ phiV k r a) := by
      have := ga_two h⁻¹ K h2 l (fun a => (h * m) *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec, ← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul] at this
      exact this
    have d1 : Del k r l (h * m) ≤ K ^ (l.val + 1) * Del k r l m := by
      have := Real.sqrt_le_sqrt e1
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    have d2 : Del k r l m ≤ K ^ (l.val + 1) * Del k r l (h * m) := by
      have := Real.sqrt_le_sqrt e2
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    exact rpow_bd _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hK' (hs l) d2 d1

theorem cont_gN {k r : ℕ} : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  refine Continuous.sqrt ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)

theorem cont_ga {k r : ℕ} (l : Fin (r + 1)) :
    Continuous fun x : Mt k r => Ga k r l (fun a => Matrix.of x *ᵥ phiV k r a) := by
  unfold Ga
  refine Complex.continuous_re.comp ?_
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.of_apply]
  have hx : Continuous fun x : Mt k r => Matrix.of x := continuous_id
  first
    | exact ((hx.matrix_mulVec continuous_const).star).dotProduct (hx.matrix_mulVec continuous_const)
    | (simp only [dotProduct]; exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (hx.matrix_mulVec continuous_const).star).mul ((continuous_apply i).comp (hx.matrix_mulVec continuous_const)))
    | (simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]; fun_prop)

theorem meas_xi (k r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable fun x : Mt k r => xiN k r s (Matrix.of x) := by
  unfold xiN xiR
  refine Measurable.real_toNNReal ?_
  refine Finset.measurable_prod _ fun l _ => ?_
  refine Measurable.pow_const ?_ _
  exact ((cont_ga l).sqrt).measurable

end ReciprocityTheory.ChartRestriction.DS.Xi.XI
end
end

