module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp Filter Topology
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LenCont

theorem eucl_eq {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucl, Complex.normSq_eq_norm_sq]

theorem eucl_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    eucl (A *ᵥ v) ≤ opn A * eucl v := by
  rw [eucl_eq, eucl_eq, opn, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem opn_continuous {n : ℕ} : Continuous (opn (n := n)) := by
  unfold opn
  refine continuous_norm.comp ?_
  exact LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)

theorem opn_one {n : ℕ} : opn (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  rw [opn, map_one, norm_one]

def len {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))}

theorem len_le {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g h : Matrix (Fin n) (Fin n) ℂ)
    (hh : IsUnit h.det) : len Y f g ≤ opn (g⁻¹ * h) * len Y f h := by
  have hb : BddBelow {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))} :=
    ⟨0, by rintro t ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  have hne : {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}.Nonempty := ⟨_, 0, Y.zero_mem, rfl⟩
  have key : ∀ t ∈ {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}, len Y f g ≤ opn (g⁻¹ * h) * t := by
    rintro t ⟨y, hy, rfl⟩
    refine (csInf_le hb ⟨y, hy, rfl⟩).trans ?_
    have := eucl_mulVec_le (g⁻¹ * h) (h⁻¹ *ᵥ (f - y))
    rwa [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one] at this
  have h0 : 0 ≤ opn (g⁻¹ * h) := norm_nonneg _
  rcases h0.eq_or_lt with h0 | h0
  · obtain ⟨t, ht⟩ := hne
    have := key t ht
    rw [← h0] at this ⊢
    simpa using this
  · rw [mul_comm, ← div_le_iff₀ h0]
    refine le_csInf hne fun t ht => ?_
    rw [div_le_iff₀ h0, mul_comm]
    exact key t ht

theorem len_continuousOn {n : ℕ} (Y : Submodule ℂ (Fin (n + 1) → ℂ)) (f : Fin (n + 1) → ℂ) :
    ContinuousOn (len Y f) {g | IsUnit g.det} := by
  intro x₀ hx₀
  have hx₀' : IsUnit x₀.det := hx₀
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → _) x₀ := by
    refine continuousAt_matrix_inv x₀ ?_
    obtain ⟨u, hu⟩ := hx₀'
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have h1 : Tendsto (fun x => opn (x⁻¹ * x₀)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x⁻¹ * x₀)) x₀ :=
      opn_continuous.continuousAt.comp (hinv.mul continuousAt_const)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have h2 : Tendsto (fun x => opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x₀⁻¹ * x)) x₀ :=
      opn_continuous.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have hU : Tendsto (fun x => opn (x⁻¹ * x₀) * len Y f x₀) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    simpa using h1.mul_const (len Y f x₀)
  have hL : Tendsto (fun x => len Y f x₀ / opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    have := (tendsto_const_nhds (x := len Y f x₀)).div h2 one_ne_zero
    rw [div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.mono_left nhdsWithin_le_nhds)
    (hU.mono_left nhdsWithin_le_nhds) ?_ (Eventually.of_forall fun x => len_le Y f x x₀ hx₀')
  filter_upwards [self_mem_nhdsWithin, (h2.eventually (lt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds]
    with x hx hpos
  rw [div_le_iff₀ hpos, mul_comm]
  exact len_le Y f x₀ x hx

theorem fold_continuousOn {X ι : Type*} [TopologicalSpace X] [DecidableEq ι] (S : Set X) (F : ι → X → ℝ)
    (hF : ∀ a, ContinuousOn (F a) S) (s : Finset ι) :
    ContinuousOn (fun x => s.fold max 1 fun a => F a x) S := by
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact continuous_max.comp_continuousOn ((hF a).prodMk ih)

theorem lA_Sg_continuousOn : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)),
    (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  intro k r z
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have h : ∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r) := fun a =>
    (len_continuousOn _ (fvec k r z a)).mono fun g hg => ((uHGroup _ _ hH).2.2 g hg).1
  exact ⟨h, fold_continuousOn (GG k r) (fun a x => lA k r z x a) h Finset.univ⟩

end GlobalTheory.Amp.LenCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousUpperOff
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.USplit

def coords {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : UT r → ℂ := fun p => A p.1.1 p.1.2

theorem upper_of_lt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : a < b) : upper x a b = x ⟨(a, b), h⟩ := by
  unfold upper
  rw [dif_pos h]

theorem upper_diag {r : ℕ} (x : UT r → ℂ) (a : Fin r) : upper x a a = 1 := by
  unfold upper
  rw [dif_neg (lt_irrefl a), if_pos rfl]

theorem upper_of_gt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : b < a) : upper x a b = 0 := by
  unfold upper
  rw [dif_neg (lt_asymm h), if_neg (ne_of_gt h)]

theorem mul_apply_lt {r : ℕ} (x y : UT r → ℂ) {a b : Fin r} (h : a < b) :
    (upper x * upper y) a b = x ⟨(a, b), h⟩ + y ⟨(a, b), h⟩ +
      ∑ c, if a < c ∧ c < b then upper x a c * upper y c b else 0 := by
  rw [Matrix.mul_apply]
  have key : ∀ c, upper x a c * upper y c b =
      ((if c = a then y ⟨(a, b), h⟩ else 0) + (if c = b then x ⟨(a, b), h⟩ else 0)) +
        (if a < c ∧ c < b then upper x a c * upper y c b else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hac
    · have hcb : c ≠ b := ne_of_lt (hca.trans h)
      rw [upper_of_gt x hca, zero_mul, if_neg (ne_of_lt hca), if_neg hcb,
        if_neg (fun k => lt_asymm hca k.1)]
      simp
    · subst hca
      rw [upper_diag, one_mul, upper_of_lt y h, if_pos rfl, if_neg (ne_of_lt h),
        if_neg (fun k => lt_irrefl _ k.1)]
      simp
    · rcases lt_trichotomy c b with hcb | hcb | hbc
      · rw [if_neg (ne_of_gt hac), if_neg (ne_of_lt hcb), if_pos ⟨hac, hcb⟩]
        simp
      · subst hcb
        rw [upper_diag, mul_one, upper_of_lt x h, if_neg (ne_of_gt h), if_pos rfl,
          if_neg (fun k => lt_irrefl _ k.2)]
        simp
      · rw [upper_of_gt y hbc, mul_zero, if_neg (ne_of_gt hac), if_neg (ne_of_gt hbc),
          if_neg (fun k => lt_asymm hbc k.2)]
        simp
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a, Finset.sum_ite_eq' Finset.univ b]
  simp only [Finset.mem_univ, if_true]
  ring

theorem upper_coords_mul {r : ℕ} (x y : UT r → ℂ) : upper (coords (upper x * upper y)) = upper x * upper y := by
  ext a b
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [upper_of_lt _ hab]
    rfl
  · subst hab
    rw [upper_diag, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [upper_diag, upper_diag, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [upper_of_gt x hlt, zero_mul]
      · rw [upper_of_gt y hgt, mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [upper_of_gt _ hba, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rcases lt_or_ge c a with hca | hac
    · rw [upper_of_gt x hca, zero_mul]
    · rw [upper_of_gt y (lt_of_lt_of_le hba hac), mul_zero]

theorem continuous_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : a < b
  · simp only [upper, dif_pos h]
    exact continuous_apply _
  · simp only [upper, dif_neg h]
    exact continuous_const

theorem continuous_upperIn {r : ℕ} (β : Fin r → ℕ) : Continuous (upperIn β) := by
  have hg : Continuous fun (x : UTin β → ℂ) (p : UT r) =>
      if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 = β p.1.2
    · simp only [dif_pos h]
      exact continuous_apply _
    · simp only [dif_neg h]
      exact continuous_const
  exact (continuous_upper r).comp hg

theorem continuous_upperOff {r : ℕ} (β : Fin r → ℕ) : Continuous (upperOff β) := by
  have hg : Continuous fun (x : UToff β → ℂ) (p : UT r) =>
      if h : β p.1.1 ≠ β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 ≠ β p.1.2
    · simp only [dif_pos h]
      exact continuous_apply _
    · simp only [dif_neg h]
      exact continuous_const
  exact (continuous_upper r).comp hg

def prodMap {r : ℕ} (β : Fin r → ℕ) (u : UT r → ℂ) : UT r → ℂ :=
  coords (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1))

theorem continuous_prodMap {r : ℕ} (β : Fin r → ℕ) : Continuous (prodMap β) := by
  have h1 : Continuous fun u : UT r → ℂ => upperIn β (fun p => u p.1) :=
    (continuous_upperIn β).comp (continuous_pi fun p => continuous_apply _)
  have h2 : Continuous fun u : UT r → ℂ => upperOff β (fun p => u p.1) :=
    (continuous_upperOff β).comp (continuous_pi fun p => continuous_apply _)
  exact continuous_pi fun p => (h1.matrix_mul h2).matrix_elem p.1.1 p.1.2

private theorem shearCond_prodMap {r : ℕ} (β : Fin r → ℕ) :
    Formalism.FourierDecayAlt.P.ShearMeasurability.ShearCond (fun p : UT r => p.1.2.val - p.1.1.val) (prodMap β) := by
  intro q x y hxy
  obtain ⟨⟨a, b⟩, h⟩ := q
  have e : ∀ u : UT r → ℂ, prodMap β u ⟨(a, b), h⟩ - u ⟨(a, b), h⟩ = ∑ c, if a < c ∧ c < b then
      upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) a c *
      upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) c b else 0 := by
    intro u
    have hin : upperIn β (fun p => u p.1) = upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) := by
      unfold upperIn
      congr 1
    have hoff : upperOff β (fun p => u p.1) =
        upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) := by
      unfold upperOff
      congr 1
    show (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1)) a b - _ = _
    rw [hin, hoff, mul_apply_lt _ _ h]
    by_cases hb : β a = β b
    · have hb' : ¬ β a ≠ β b := not_not.mpr hb
      simp only [if_pos hb, if_neg hb', add_zero, add_sub_cancel_left]
    · simp only [if_neg hb, if_pos hb, zero_add, add_sub_cancel_left]
  rw [e x, e y]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 : c.val - a.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    have h2 : b.val - c.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    rw [upper_of_lt _ hc.1, upper_of_lt _ hc.2, upper_of_lt _ hc.1, upper_of_lt _ hc.2,
      hxy ⟨(a, c), hc.1⟩ h1, hxy ⟨(c, b), hc.2⟩ h2]
  · rfl

theorem prodMap_mp {r : ℕ} (β : Fin r → ℕ) : MeasurePreserving (prodMap β) volume volume := Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp _ (prodMap β) (continuous_prodMap β).measurable (shearCond_prodMap β)

theorem lebesgue_split : ∀ (r : ℕ) (β : Fin r → ℕ), Monotone β → (∀ (x : UTin β → ℂ) (y : UToff β → ℂ), ∃ u : UT r → ℂ, upper u = upperIn β x * upperOff β y) ∧ ∀ f : (Fin r → Fin r → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u)) = ∫⁻ y : UToff β → ℂ, ∫⁻ x : UTin β → ℂ, f (Matrix.of.symm (upperIn β x * upperOff β y)) := by
  intro r β _
  refine ⟨fun x y => ⟨coords (upperIn β x * upperOff β y), ?_⟩, fun f hf => ?_⟩
  · unfold upperIn upperOff
    exact upper_coords_mul _ _
  · have hc : Continuous fun u : UT r → ℂ => (Matrix.of.symm (upper u) : Fin r → Fin r → ℂ) :=
      continuous_upper r
    have hu : Measurable fun u : UT r → ℂ => f (Matrix.of.symm (upper u)) := hf.comp hc.measurable
    have hM : Continuous fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        (Matrix.of.symm (upperIn β z.1 * upperOff β z.2) : Fin r → Fin r → ℂ) :=
      ((continuous_upperIn β).comp continuous_fst).matrix_mul ((continuous_upperOff β).comp continuous_snd)
    have hG : Measurable fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) := hf.comp hM.measurable
    have hsplit := MeasureTheory.volume_preserving_piEquivPiSubtypeProd (fun _ : UT r => ℂ)
      (fun p : UT r => β p.1.1 = β p.1.2)
    have key : ∀ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) =
        f (Matrix.of.symm (upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1))) := by
      intro v
      have hp : upper (prodMap β v) = upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1) := by
        unfold prodMap upperIn upperOff
        exact upper_coords_mul _ _
      rw [hp]
    calc ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u))
        = ∫⁻ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) :=
          ((prodMap_mp β).lintegral_comp hu).symm
      _ = ∫⁻ v : UT r → ℂ, (fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
            f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)))
            (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : UT r => ℂ)
              (fun p : UT r => β p.1.1 = β p.1.2) v) := lintegral_congr fun v => key v
      _ = ∫⁻ z : (UTin β → ℂ) × (UToff β → ℂ), f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) :=
          hsplit.lintegral_comp hG
      _ = _ := lintegral_prod_symm _ hG.aemeasurable

end GlobalTheory.Amp.USplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiusHomSubquotientSublattice
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.SubquotCover

theorem sum_normSq_eq_trace {a b : Type} [Fintype a] [Fintype b] (M : Matrix a b ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Mᴴ * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_normSq_mul {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq b] [DecidableEq c]
    (P : Matrix a b ℂ) (M : Matrix b c ℂ) (Q : Matrix c d ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) :
    ∑ i, ∑ j, ‖(P * M * Q) i j‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace, conjTranspose_mul, conjTranspose_mul]
  have hmid : Qᴴ * (Mᴴ * Pᴴ) * (P * M * Q) = Qᴴ * (Mᴴ * M * Q) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, hP, Matrix.one_mul]
  rw [hmid, Matrix.trace_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem vecAt_mulVec {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (w : InfinitePlace K) (M : Matrix (Fin a) (Fin b) K) (y : Fin b → K) :
    vecAt (Pi.basisFun K (Fin a)) w (M *ᵥ y)
      = M.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin b)) w y := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vecAt, Pi.basisFun_repr, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    map_mul]

theorem mulVec_fcoord {K : Type} [Field K] [NumberField K] [StarRing K] {a : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (w : InfinitePlace K) (hX : IsUnit (X w).det) (y : Fin a → K) :
    X w *ᵥ fcoord (Pi.basisFun K (Fin a)) X w y = vecAt (Pi.basisFun K (Fin a)) w y := by
  rw [fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]

theorem subquot_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S R : Submodule (𝓞 K) (Fin n → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N S) → largestSize (Pi.basisFun K (Fin n)) X R ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ S, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = 0) → (∀ w, ∀ y ∈ A, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))) → ∃ φ : Matrix (Fin n) (Fin n) K, (∀ y ∈ S, φ *ᵥ y = 0) ∧ (∀ y ∈ A, φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ A, D w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = (T w - (X w)⁻¹ * φ.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ Real.sqrt (∑ w, Formalism.REAL.hs (D w)) ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt (nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi / (2 * lo) := by
  intro K _ _ _ _ n X A S R lo hi hX hA hSat hR hlo hhi hsize hlarge T hTS hTR
  obtain ⟨m, q, X', Q, hm, hX', hQ, hqf, -, hQS, hqS, hspan, hN⟩ :=
    GlobalTheory.T.quotient_lattice_realized_isometrically K n X A S hX hA hSat
  obtain ⟨r, e, X'', P, B, hr, hX'', hP, hPe, hB, hBspan, heB, hRB, hlB⟩ :=
    _root_.GlobalTheory.exists_isometric_realisation_of_sublattice K n X R hX hR
  obtain ⟨φ', hφ'B, hbound⟩ := GlobalTheory.T.lattice_pair_volume_bounds K m r X' X''
    (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) B lo hi hX' hX'' (hA.map _) hB hspan
    hBspan hlo hhi
    (fun N' hN' hN'0 => by
      obtain ⟨N, hSN, hNA, heq⟩ := hN N' hN' hN'0
      rw [← heq]
      exact hsize N hSN hNA)
    (by rw [hlB]; exact hlarge) (fun w => (P w)ᴴ * T w * (Q w)ᴴ)
  refine ⟨e * φ' * q, ?_, ?_,
    fun w => P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w,
    ?_, ?_⟩
  · intro y hy
    rw [← Matrix.mulVec_mulVec, hqS y hy, Matrix.mulVec_zero]
  · intro y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    apply heB
    apply hφ'B
    exact Submodule.mem_map.mpr ⟨y, hy, by simp [Matrix.toLin'_apply]⟩
  · intro w y hy
    set u := fcoord (Pi.basisFun K (Fin n)) X w y with hu
    have hQu : Q w *ᵥ u = fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) := (hqf w y hy).symm
    have hXu : X w *ᵥ u = vecAt (Pi.basisFun K (Fin n)) w y := mulVec_fcoord X w (hX w) y
    have hX'u : X' w *ᵥ (Q w *ᵥ u) = q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y := by
      rw [hQu, mulVec_fcoord X' w (hX' w), vecAt_mulVec]

    have hTQ : T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u)) = T w *ᵥ u := by
      have hmem : u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈
          Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) :=
        hQS w u (Submodule.subset_span ⟨y, hy, rfl⟩)
      have hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))
          ≤ LinearMap.ker (Matrix.mulVecLin (T w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        exact hTS w z hz
      have h0 := hker hmem
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero] at h0
      exact h0.symm

    have hPP : ∀ v ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K))),
        P w *ᵥ ((P w)ᴴ *ᵥ v) = v := by
      intro v hv
      have hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))
          ≤ LinearMap.range (Matrix.mulVecLin (P w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨z, -, rfl⟩ := hRB x hx
        refine ⟨(X'' w)⁻¹ *ᵥ vecAt (Pi.basisFun K (Fin r)) w z, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hPe w, ← Matrix.mulVec_mulVec,
          ← vecAt_mulVec]
        rfl
      obtain ⟨z, rfl⟩ := hle hv
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec _ (P w)ᴴ, hP w, Matrix.one_mulVec]
    calc (P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w) *ᵥ u
        = P w *ᵥ ((P w)ᴴ *ᵥ (T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u))))
          - (P w * (X'' w)⁻¹) *ᵥ (φ'.map w.embedding *ᵥ (X' w *ᵥ (Q w *ᵥ u))) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc]
      _ = T w *ᵥ u - ((X w)⁻¹ * e.map w.embedding) *ᵥ (φ'.map w.embedding *ᵥ
            (q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y)) := by
          rw [hTQ, hPP _ (hTR w y hy), hX'u, hPe w]
      _ = (T w - (X w)⁻¹ * (e * φ' * q).map w.embedding * X w) *ᵥ u := by
          rw [Matrix.sub_mulVec, ← hXu, Matrix.map_mul, Matrix.map_mul]
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have hm' : (m : ℝ) = (rkK A : ℝ) - rkK S := by rw [← hm]; push_cast; ring
    have hr' : (r : ℝ) = rkK R := by rw [hr]
    rw [← hm', ← hr']
    refine Eq.trans_le ?_ hbound
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Formalism.REAL.hs]
    exact sum_normSq_mul (P w) _ (Q w) (hP w) (hQ w)

end GlobalTheory.SubquotCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryOfFiniteSupportStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_of_finite_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)), (∀ v, h v ∈ UPts σ J (v.adicCompletion F)) → {v | h v ≠ 1}.Finite → ∃ x ∈ UPts σ J (Ad F), ∀ v, bc (prV (E := E) v) x = h v := by
  first | exact @GlobalTheory.St.G.exists_adelic_of_finite_support | exact GlobalTheory.St.G.exists_adelic_of_finite_support | (intros; apply GlobalTheory.St.G.exists_adelic_of_finite_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplOfSaturated
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem exists_compl_of_saturated {R V : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublatticeComplement.main
  | exact _root_.GlobalTheory.SaturatedSublatticeComplement.main
  | (apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublatticeComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublatticeComplement.main ..)

theorem saturatedFlag_splits : ∀ (E : Type) [Field E] [NumberField E] (n a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 E) (Fin n → E)), S 0 = ⊥ → Monotone S → (S (Fin.last a)).FG → (∀ i, ∀ y ∈ S (Fin.last a), y ∈ Submodule.span E (S i : Set (Fin n → E)) → y ∈ S i) → ∃ A : Fin a → Submodule (𝓞 E) (Fin n → E), ∀ i, A i ⊓ S i.castSucc = ⊥ ∧ A i ⊔ S i.castSucc = S i.succ := by
  intro E _ _ n a S _ hmono hfg hsat
  have key : ∀ i : Fin a, ∃ A : Submodule (𝓞 E) (Fin n → E),
      A ⊓ S i.castSucc = ⊥ ∧ A ⊔ S i.castSucc = S i.succ := by
    intro i
    have hle : S i.succ ≤ S (Fin.last a) := hmono (Fin.le_last _)
    refine exists_compl_of_saturated _ _ (hmono (Fin.castSucc_lt_succ).le)
      (Submodule.FG.of_le hfg hle) ?_
    intro r y hr hy hry
    apply hsat _ y (hle hy)
    have hr' : (algebraMap (𝓞 E) E r) ≠ 0 := by
      simpa using hr
    have : y = (algebraMap (𝓞 E) E r)⁻¹ • (r • y) := by
      rw [← algebraMap_smul E r y, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hry)
  choose A hA using key
  exact ⟨A, hA⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoeffIdealOfLatticeFgAndMemIffStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (F : Formalism.MainNotions.S.FlagG S r T) (Λ : Submodule (𝓞 E) S.V) (a : Fin r), Λ.FG → (GlobalTheory.RowLatXS.Ia Λ F a).FG ∧ ∀ t : E, t ∈ GlobalTheory.RowLatXS.Ia Λ F a ↔ ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
  first | exact @GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | exact GlobalTheory.RowLatXS.Ia_fg_and_mem_iff | (intros; apply GlobalTheory.RowLatXS.Ia_fg_and_mem_iff <;> assumption)
end

