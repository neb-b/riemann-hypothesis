module

public import Mathlib
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementU
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgMulLeft
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmLeftN

open Matrix in
variable {k r : ℕ} in
private lemma flagMat_mulVec_eq_sum_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]

open Matrix in
variable {k r : ℕ} in
private lemma rW_mulVec_adjugate_zhat_single_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_fvec]
  simp [mulVec_single_one, conjTranspose_apply]

open Matrix in
variable {k r : ℕ} in
private lemma conjTranspose_hpk : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose

open Matrix in
variable {k r : ℕ} in
private lemma gram_eq_upper_bounds (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_hpk,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma mul_adjugate_conjTranspose_eq_of_det_eq_one {m n : ℕ} (X : Matrix (Fin n) (Fin m) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ) (hU : U.det = 1) :
    (X * U) * ((X * U)ᴴ * Y).adjugateᴴ = X * (Xᴴ * Y).adjugateᴴ := by
  rw [conjTranspose_mul, Matrix.mul_assoc Uᴴ, adjugate_mul_distrib, conjTranspose_mul,
    adjugate_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc X U,
    ← Matrix.mul_assoc U, mul_adjugate, hU, one_smul, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
private lemma det_eq_one_of_upUni {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) : U.det = 1 := by
  rw [det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]


open Matrix in
theorem _root_.GlobalTheory.WigSh.OmLeftN.omg_mul_left (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g n : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hn : n ∈ _root_.Formalism.QuantumDeterminants.Nset k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' (n * g) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  obtain ⟨U, hU, hnF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z hz n hn
  have hnU : nᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * n = _root_.Formalism.QuantumDeterminants.Hpk k r := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff n).1 hn).1
  have hQ : _root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      _root_.Formalism.QuantumDeterminants.Hpk k r * (n * g)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z * U := by
    have key : nᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * (n * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)) =
        _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z := by
      simp only [← Matrix.mul_assoc, hnU]
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← hnF, key]
  rw [rW_mulVec_adjugate_zhat_single_last, rW_mulVec_adjugate_zhat_single_last, gram_eq_upper_bounds, gram_eq_upper_bounds, mulVec_mulVec, mulVec_mulVec, hQ,
    mul_adjugate_conjTranspose_eq_of_det_eq_one _ _ _ (det_eq_one_of_upUni hU)]

theorem omg_left_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g m : Mx k r), inWb k r z → inWb k r z' → g ∈ UH (Hpk k r) → m ∈ Formalism.QuantumDeterminants.Nset k r → GlobalTheory.WigSh.omg k r z z' (m⁻¹ * g) = GlobalTheory.WigSh.omg k r z z' g :=
  fun k r z z' g m hz _ _ hm => omg_mul_left k r z z' g m⁻¹ hz ((unipotent_subgroup_holds k r).2.2 m hm)

end GlobalTheory.WigSh.OmLeftN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
section
open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem lintegral_density {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (Ph : Ω → ℝ)
    (hPh : AEMeasurable Ph ν) (h0 : ∀ x, 0 ≤ Ph x) (f : Ω → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(ν.withDensity fun x => ENNReal.ofReal (Ph x))
      = ∫⁻ x, ENNReal.ofReal (f x * Ph x) ∂ν := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ hPh.ennreal_ofReal
    hf.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (f x), ENNReal.ofReal_mul (h0 x)]

theorem exists_pos_version {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → ℝ)
    (hf : AEMeasurable f ν) (hpos : ∀ᵐ x ∂ν, 0 < f x) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, 0 < g x) ∧ f =ᵐ[ν] g := by
  classical
  refine ⟨fun x => if 0 < hf.mk f x then hf.mk f x else 1, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_lt measurable_const hf.measurable_mk)
      hf.measurable_mk measurable_const
  · intro x
    by_cases h : 0 < hf.mk f x <;> simp [h]
  · filter_upwards [hf.ae_eq_mk, hpos] with x hx hp
    rw [← hx, if_pos hp]

theorem product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : ℕ) (len : Fin (r + 1) → Ω → ℝ)
      (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) →
      AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a, len a x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ (r + 1)) := by
  intro Ω _ ν r len Ph A Rr hm hpos hPh h0 hmass hA hR h1 h2
  choose l hlm hlp hle using fun a => exists_pos_version ν (len a) (hm a) (hpos a)
  have hall : ∀ᵐ x ∂ν, ∀ a, len a x = l a x := ae_all_iff.2 hle
  set μ : Measure Ω := ν.withDensity fun x => ENNReal.ofReal (Ph x) with hμ
  haveI : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]⟩
  have hR0 : 0 ≤ Rr := zero_le_one.trans hR
  have hsq : ∀ q : ℕ, Real.sqrt A ^ (2 * q) = A ^ q := fun q => by
    rw [pow_mul, Real.sq_sqrt hA]
  have hup := Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds Ω μ r (r + 1) l (Real.sqrt A) Rr hlm hlp
    (Real.sqrt_nonneg A) hR0
    (fun q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0 _ ((hlm 0).pow_const _), hsq]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h1 q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx])
    (fun c q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0
        (fun ω => (l c.succ ω / l c.castSucc ω) ^ (2 * q)) (((hlm _).div (hlm _)).pow_const _)]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h2 c q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx, hx])
  have hprod := Formalism.HermitianLatticeCounting.P.corollary_product_estimate_holds Ω μ r 1 (r + 1) l (Real.sqrt A * Rr ^ r) hlm hlp
    (by positivity) le_rfl
    (fun a _ => by
      rw [mul_one]
      refine (hup a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul Rr r]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR ?_) (by positivity)
      rw [mul_comm r]
      exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 a.isLt))
  have hfilt : univ.filter (fun a : Fin (r + 1) => a.val < r + 1) = univ :=
    filter_true_of_mem fun a _ => a.isLt
  rw [hfilt, hμ, lintegral_density ν Ph hPh h0 _
    ((Finset.measurable_prod _ fun a _ => hlm a).pow_const _)] at hprod
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hprod.trans_eq ?_)
  · filter_upwards [hall] with x hx
    simp only [hx, mul_one, Finset.prod_pow]
  · congr 1
    rw [mul_one, mul_pow, hsq, mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    ring

end GlobalTheory.MomentHolder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwine
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_ofFn_prod_apply_of_intertwine {M Wp : Type} [AddCommGroup M] [Module ℂ M]
    (l : M → Wp) :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ M) (g : Fin t → Wp → Wp),
      (∀ k v, l (f k v) = g k (l v)) → ∀ v,
      l ((List.ofFn f).prod v) = List.foldr (fun T h => T h) (l v) (List.ofFn g) := by
  intro t
  induction t with
  | zero => intro f g _ v; simp
  | succ t ih =>
    intro f g h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons, Module.End.mul_apply, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun k v => h k.succ v) v]

theorem qminor_block_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  intro M Wp _ _ _ _ n m E l w Pop hw h u v
  unfold Formalism.REAL.qminor Formalism.FourierDecayAlt.Q.qmF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := map_ofFn_prod_apply_of_intertwine (l : M → Wp) m
    (fun k => Formalism.REAL.Tm E (u - ((k : ℕ) : ℂ)) (w (σ k)) (w k))
    (fun k y => (if id (σ k) = id k then (u - ((k : ℕ) : ℂ)) • y else 0) + Pop (id (σ k)) (id k) y)
    (fun k x => by
      unfold Formalism.REAL.Tm
      by_cases hk : σ k = k
      · simp [hk, h, sub_smul, Nat.cast_smul_eq_nsmul]
      · have : w (σ k) ≠ w k := fun e => hk (hw e)
        simp [hk, this, h]) v
  rw [← key, Module.End.mul_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorColumnExpansionUnderLinearMap
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapStepCol

theorem exists_perm_of_range_eq {n t : ℕ} (a a₂ : Fin t → Fin n) (ha : Function.Injective a)
    (h : Set.range a = Set.range a₂) : ∃ τ : Equiv.Perm (Fin t), a = a₂ ∘ τ := by
  have h1 : ∀ i, ∃ j, a₂ j = a i := fun i => by
    have : a i ∈ Set.range a₂ := h ▸ Set.mem_range_self i
    exact this
  choose f hf using h1
  have hinj : Function.Injective f := fun i j hij => ha (by rw [← hf i, ← hf j, hij])
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  funext i
  simp [hf]

theorem norm_sign {t : ℕ} (τ : Equiv.Perm (Fin t)) :
    ‖(((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem cap_step_col : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → b0 ∉ Set.range a → (∀ j v, l (E (a j) b0 v) = (if a j = a0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
  intro M Wp _ _ _ _ n t E l a b a' b' a0 b0 p hE ha hb ha' hb' hra ha0 hrb hb0 hba hl
  obtain ⟨σ, hσ⟩ := exists_perm_of_range_eq a (Fin.cons a0 a' : Fin (t + 1) → Fin n) ha
    (by rw [hra, Fin.range_cons])
  obtain ⟨τ, hτ⟩ := exists_perm_of_range_eq b (Fin.cons b0 b' : Fin (t + 1) → Fin n) hb
    (by rw [hrb, Fin.range_cons])
  refine ⟨(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ), ?_, ?_⟩
  · rw [norm_mul, norm_sign, norm_sign, one_mul]
  intro u v
  have hT : ∀ (j : Fin (t + 1)) (w : M),
      l (Formalism.REAL.Tm E u ((Fin.cons a0 a' : Fin (t + 1) → Fin n) j) b0 w) =
        (if j = 0 then p else 0) • l w := by
    intro j w
    have hmem : (Fin.cons a0 a' : Fin (t + 1) → Fin n) j ∈ Set.range a := by
      rw [hra, ← Fin.range_cons]; exact Set.mem_range_self j
    obtain ⟨i, hi⟩ := hmem
    have hne : a i ≠ b0 := fun h => hba ⟨i, h⟩
    have hiff : a i = a0 ↔ j = 0 := by
      rw [hi]
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp only [Fin.cons_succ, Fin.succ_ne_zero, iff_false]
        exact fun h => ha0 ⟨k, h⟩
    rw [← hi, Formalism.REAL.Tm, if_neg hne, zero_add, hl]
    simp only [hiff]
  have key : l (Formalism.REAL.qminor E (Fin.cons a0 a' : Fin (t + 1) → Fin n)
      (Fin.cons b0 b' : Fin (t + 1) → Fin n) u v) = p • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [PI.QmColExpWork.expFirst, LinearMap.sum_apply, map_sum, Finset.sum_eq_single 0]
    · have e1 : (Fin.cons a0 a' : Fin (t + 1) → Fin n) ∘ (0 : Fin (t + 1)).succAbove = a' := by
        funext k; simp
      have e2 : (Fin.cons b0 b' : Fin (t + 1) → Fin n) ∘ Fin.succ = b' := by
        funext k; simp
      rw [e1, e2]
      simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Module.End.mul_apply]
      have := hT 0 (Formalism.REAL.qminor E a' b' (u - 1) v)
      simpa using this
    · intro j _ hj
      rw [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, Module.End.mul_apply,
        Fin.cons_zero, hT, if_neg hj, zero_smul, smul_zero]
    · simp
  rw [hσ, hτ, Formalism.REAL.quantumMinorRowSkew_holds, Formalism.REAL.quantumMinorColSkew_holds _ _ _ E hE,
    Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Module.End.intCast_apply, map_zsmul, map_zsmul, key, mul_smul, mul_smul,
    Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

end GlobalTheory.CapStepCol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorEqUnitSmulOfRangeEq
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_perm_of_range_eq {t : ℕ} {β : Type} (a a₂ : Fin t → β)
    (ha : Function.Injective a) (ha₂ : Function.Injective a₂) (h : Set.range a = Set.range a₂) :
    ∃ τ : Equiv.Perm (Fin t), a = a₂ ∘ τ := by
  refine ⟨(Equiv.ofInjective a ha).trans ((Set.equivOfEq h).trans (Equiv.ofInjective a₂ ha₂).symm), ?_⟩
  funext i
  simp [Equiv.apply_ofInjective_symm]

theorem qminor_eq_smul_of_range_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a a₂ b b₂ : Fin t → Fin n), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective a₂ → Function.Injective b → Function.Injective b₂ → Set.range a = Set.range a₂ → Set.range b = Set.range b₂ → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u, Formalism.REAL.qminor E a b u = e • Formalism.REAL.qminor E a₂ b₂ u := by
  intro A _ _ n t E a a₂ b b₂ hE ha ha₂ hb hb₂ hra hrb
  obtain ⟨σ, rfl⟩ := exists_perm_of_range_eq a a₂ ha ha₂ hra
  obtain ⟨τ, rfl⟩ := exists_perm_of_range_eq b b₂ hb hb₂ hrb
  refine ⟨(((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : ℂ), ?_, fun u => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h' | h' <;> simp [h, h']
  · rw [Formalism.REAL.quantumMinorRowSkew_holds A n t E a₂ (b₂ ∘ τ) σ u, Formalism.REAL.quantumMinorColSkew_holds A n t E hE a₂ b₂ τ u,
      Int.cast_smul_eq_zsmul, zsmul_eq_mul, ← mul_assoc, Int.cast_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SectionEqZeroOfForallGeometricPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlatPoints

theorem isPullback_whiskerRight_left {S : Scheme.{0}} {T H : Over S} (q : T ⟶ H) (Y : Over S) :
    IsPullback (pullback.fst T.hom Y.hom) (q ▷ Y).left q.left (pullback.fst H.hom Y.hom) := by
  refine (IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst T.hom Y.hom)
    (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q)
    (IsPullback.of_hasPullback H.hom Y.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback T.hom Y.hom).flip

theorem section_eq_zero_of_cover {X : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}}
    (u : ∀ i, Z i ⟶ X) [∀ i, IsOpenImmersion (u i)] (hu : ∀ x : X, ∃ i z, u i z = x)
    (W : X.Opens) (f : Γ(X, W)) (h : ∀ i, ((u i).app W).hom f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W f 0 fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := hu x
  have hinj : Function.Injective ((u i).stalkMap z).hom :=
    (asIso ((u i).stalkMap z)).commRingCatIsoToRingEquiv.injective
  change (X.presheaf.germ W _ hx).hom f = (X.presheaf.germ W _ hx).hom 0
  apply hinj
  rw [Scheme.Hom.germ_stalkMap_apply, h i]
  simp

theorem eq_zero_of_forall_point (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)] (a : A)
    (ha : ∀ φ : A →ₐ[O] F, φ a = 0) : a = 0 := by
  have := tensor_eq_zero_of_forall_geometric_point O F hinj A O (a ⊗ₜ 1) (fun φ => by simp [ha φ])
  simpa using congrArg (TensorProduct.rid O A) this

theorem finite_algHom (O F : Type) [CommRing O] [Field F] [Algebra O F] (A : Type) [CommRing A]
    [Algebra O A] [Module.Finite O A] : Finite (A →ₐ[O] F) := by
  have : Finite (TensorProduct O F A →ₐ[F] F) := inferInstance
  exact Finite.of_equiv _ (Algebra.TensorProduct.liftEquivRight O F A F).symm

theorem affine_case (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)]
    (H Y : Over (Spec (CommRingCat.of O))) (e : specO O A ≅ H) [Flat Y.hom]
    (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W))
    (h : ∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) : f = 0 := by
  have := finite_algHom O F A
  let Φ : A →ₐ[O] ((A →ₐ[O] F) → F) := Pi.algHom O (fun _ => F) (fun φ => φ)
  have hΦ : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact eq_zero_of_forall_point O F hinj A a fun φ => congrFun ha φ
  let q : specO O ((A →ₐ[O] F) → F) ⟶ H := ptMap Φ ≫ e.hom
  have h1 : IsSchemeTheoreticallyDominant (ptMap Φ).left :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hΦ
  have h2 : QuasiCompact (ptMap Φ).left :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom Φ.toRingHom)))
  have h0 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h3 : IsSchemeTheoreticallyDominant q.left := by
    change IsSchemeTheoreticallyDominant ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have h4 : QuasiCompact q.left := by
    change QuasiCompact ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have hp := isPullback_whiskerRight_left q Y
  have h5 : IsSchemeTheoreticallyDominant (q ▷ Y).left := .of_isPullback hp
  have h6 : QuasiCompact (q ▷ Y).left := MorphismProperty.of_isPullback hp h4
  apply (q ▷ Y).left.app_injective W
  rw [map_zero]
  let u : (A →ₐ[O] F) → (specO O F ⟶ specO O ((A →ₐ[O] F) → F)) :=
    fun φ => ptMap (Pi.evalAlgHom O (fun _ => F) φ)
  have hu : ∀ φ, IsOpenImmersion (u φ).left := fun φ =>
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : A →ₐ[O] F => CommRingCat.of F) φ))))
  have hu' : ∀ φ, IsOpenImmersion (u φ ▷ Y).left := fun φ =>
    MorphismProperty.of_isPullback (isPullback_whiskerRight_left (u φ) Y) (hu φ)
  refine section_eq_zero_of_cover (fun φ => (u φ ▷ Y).left) (fun x => ?_) _ _ (fun φ => ?_)
  · obtain ⟨φ, p, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := fun _ : A →ₐ[O] F => F) (pullback.fst (specO O ((A →ₐ[O] F) → F)).hom Y.hom x)
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_whiskerRight_left (u φ) Y) p x hp
    exact ⟨φ, z, hz⟩
  · have := h (u φ ≫ q)
    rw [MonoidalCategory.comp_whiskerRight] at this
    exact this

end GlobalTheory.FlatPoints

namespace GlobalTheory

theorem section_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (H Y : Over (Spec (CommRingCat.of O))), IsFinite H.hom → Flat H.hom → IsReduced (specO O F ⊗ H).left → Flat Y.hom → ∀ (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W)), (∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) → f = 0 := by
  intro O F _ _ _ _ hinj H Y hfin hflat hred hY W f h
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  letI : Algebra O Γ(H.left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ(H.left, ⊤) ≅ H := Over.isoMk H.left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have h2 : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ(H.left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have : Module.Flat O Γ(H.left, ⊤) := (Flat.SpecMap_iff (f := ψ)).mp h2
  have h0 : IsIso (specO O F ◁ e.hom).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.hom)))
  have h3 : IsReduced (specO O F ⊗ specO O Γ(H.left, ⊤)).left :=
    isReduced_of_isOpenImmersion (specO O F ◁ e.hom).left
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ(H.left, ⊤)))) :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ(H.left, ⊤)).inv _ h3
  have : _root_.IsReduced (TensorProduct O F Γ(H.left, ⊤)) := (affine_isReduced_iff _).mp h4
  exact FlatPoints.affine_case O F hinj Γ(H.left, ⊤) H Y e W f h

end GlobalTheory
end

