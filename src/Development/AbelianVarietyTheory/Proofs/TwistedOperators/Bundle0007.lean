module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FromColsMulVecEqZero
section
namespace GlobalTheory.TwistDual

open Matrix

variable {E : Type} [Field E] [StarRing E] [CharZero E]

theorem fromCols_mulVec_eq_zero {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0)
    (u : Fin r ⊕ Fin m → E) (hu : Matrix.fromCols C B *ᵥ u = 0) : u = 0 := by
  have hBC : Bᴴ * G * C = 0 := by
    have := congrArg conjTranspose hCB
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hsplit : C *ᵥ (u ∘ Sum.inl) + B *ᵥ (u ∘ Sum.inr) = 0 := by
    rw [← hu]; funext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type]
  have hb : u ∘ Sum.inr = 0 := by
    have h2 := congrArg (fun w => (Bᴴ * G) *ᵥ w) hsplit
    simp only [mulVec_add, mulVec_mulVec, hBC, zero_mulVec, zero_add, mulVec_zero] at h2
    exact Matrix.eq_zero_of_mulVec_eq_zero hBB h2
  have ha : u ∘ Sum.inl = 0 := by
    rw [hb, mulVec_zero, add_zero] at hsplit
    have hC' := Fintype.linearIndependent_iff.1 hC
    funext k
    refine hC' _ ?_ k
    rw [← hsplit]; funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  funext x
  rcases x with k | k
  · exact congrFun ha k
  · exact congrFun hb k

theorem mulVec_surjective {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    Function.Surjective ((Matrix.fromCols C B)ᴴ * G).mulVecLin := by
  set M := (Matrix.fromCols C B)ᴴ * G
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [Matrix.mulVecLin_apply, mulVec_transpose] at hw
    have h1 := congrArg star hw
    rw [star_vecMul, star_zero, conjTranspose_mul, hG, conjTranspose_conjTranspose, ← mulVec_mulVec] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hGd h1
    have h3 := fromCols_mulVec_eq_zero hG hC hBB hCB _ h2
    simpa using congrArg star h3
  have hr : Mᵀ.rank = Fintype.card (Fin r ⊕ Fin m) := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  rw [Matrix.rank_transpose] at hr
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← hr]
  rfl

theorem exists_dual {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hCC : Cᴴ * G * C = 0) (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    ∃ C' : Matrix (Fin n) (Fin r) E, Cᴴ * G * C' = 1 ∧ C'ᴴ * G * C' = 0 ∧ C'ᴴ * G * B = 0 := by
  have hs := mulVec_surjective hG hGd hC hBB hCB
  choose v hv using fun k : Fin r => hs (Pi.single (Sum.inl k) (1 : E))
  set C₁ : Matrix (Fin n) (Fin r) E := Matrix.of fun i k => v k i
  have key : ∀ a k, ∑ i, ((Matrix.fromCols C B)ᴴ * G) a i * C₁ i k = (Pi.single (Sum.inl k) (1 : E) : Fin r ⊕ Fin m → E) a := by
    intro a k
    rw [← hv k]
    simp only [C₁, Matrix.mulVecLin_apply, mulVec, dotProduct, Matrix.of_apply]
  have hC1 : Cᴴ * (G * C₁) = 1 := by
    ext j k
    have := key (Sum.inl j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inl] at this ⊢
    rw [this, Pi.single_apply, Matrix.one_apply]
    simp [eq_comm]
  have hB1 : Bᴴ * (G * C₁) = 0 := by
    ext j k
    have := key (Sum.inr j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inr] at this ⊢
    rw [this]
    simp
  have hGc : ∀ (p q : ℕ) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E),
      Yᴴ * (G * X) = (Xᴴ * (G * Y))ᴴ := by
    intro p q X Y
    simp [conjTranspose_mul, hG, Matrix.mul_assoc]
  have hCC' : Cᴴ * (G * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCC
  have hCB' : Cᴴ * (G * B) = 0 := by rw [← Matrix.mul_assoc]; exact hCB
  have h1C : C₁ᴴ * (G * C) = 1 := by rw [hGc, hC1, conjTranspose_one]
  have h1B : C₁ᴴ * (G * B) = 0 := by
    have := congrArg conjTranspose hB1
    rw [conjTranspose_zero, ← hGc] at this
    exact this
  set S := C₁ᴴ * (G * C₁) with hSdef
  have hS : Sᴴ = S := by rw [hSdef, ← hGc]
  set X : Matrix (Fin r) (Fin r) E := (2 : E)⁻¹ • S with hXdef
  have hX : Xᴴ = X := by
    rw [hXdef, conjTranspose_smul, hS, star_inv₀, star_ofNat]
  have hXX : X + X = S := by
    rw [hXdef, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero), one_smul]
  have a1 : ∀ Y : Matrix (Fin r) (Fin r) E, Cᴴ * (G * (C * Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, hCC', Matrix.zero_mul]
  have a2 : ∀ Y : Matrix (Fin r) (Fin r) E, C₁ᴴ * (G * (C * Y)) = Y := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, h1C, Matrix.one_mul]
  refine ⟨C₁ - C * X, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hC1, a1, sub_zero]
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      hC1, a1, a2, Matrix.mul_one, Matrix.mul_zero, sub_zero]
    rw [← hSdef, ← hXX]; abel
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.sub_mul, Matrix.mul_assoc, h1B, hCB',
      Matrix.mul_zero, sub_zero]

end GlobalTheory.TwistDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominated
section
open Filter Topology Metric Set

namespace GlobalTheory

theorem gradedSeries_regroup {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (x s : ℂ)
    (hs : HasSum (fun i => c i * x ^ deg i) s) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) s := by
  have h1 := hs.tsum_fiberwise deg
  have e : (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) =
      (fun k => ∑' i : deg ⁻¹' {k}, c i * x ^ deg i) := by
    funext k
    rw [← tsum_mul_right]
    apply tsum_congr
    rintro ⟨i, hi⟩
    simp only [mem_preimage, mem_singleton_iff] at hi
    simp [hi]
  rw [e]
  exact h1

theorem gradedSeries_continue {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (δ ρ : ℝ) (Q : ℂ → ℂ)
    (hδ : 0 < δ) (hQ : DifferentiableOn ℂ Q (ball 0 ρ))
    (h : ∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => c i * (x : ℂ) ^ deg i) (Q x))
    (X : ℂ) (hX : ‖X‖ < ρ) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * X ^ k) (Q X) := by
  set A : ℕ → ℂ := fun k => ∑' i : deg ⁻¹' {k}, c i with hAdef
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ A with hpdef
  have hx0 : 0 < δ / 2 := by positivity
  set x0 : NNReal := ⟨δ / 2, hx0.le⟩ with hx0def
  have hrad : (x0 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    have hs := (gradedSeries_regroup deg c _ _ (h (δ / 2) hx0 (by linarith))).summable
    have hs' := summable_norm_iff.mpr hs
    refine hs'.congr fun n => ?_
    simp only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0]
    rfl
  have hF := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hx0)) hrad)
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  have hs0 : 0 < min (δ / 2) ρ := lt_min hx0 hρ
  have hQan : AnalyticOnNhd ℂ Q (ball 0 ρ) := hQ.analyticOnNhd isOpen_ball
  have hmem : ∀ z : ℂ, ‖z‖ < δ / 2 → z ∈ Metric.eball (0 : ℂ) p.radius := by
    intro z hz
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    refine lt_of_lt_of_le ?_ hrad
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hz)
  have hFan : AnalyticOnNhd ℂ p.sum (ball 0 (min (δ / 2) ρ)) := fun z hz =>
    hF.analyticAt_of_mem (hmem z (lt_of_lt_of_le (by simpa using hz) (min_le_left _ _)))
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = Q z := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hx0] with x hx
    have h1 := gradedSeries_regroup deg c _ _ (h x hx.1 (by linarith [hx.2]))
    simp only [p, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact h1.tsum_eq
  have heq : EqOn p.sum Q (ball 0 (min (δ / 2) ρ)) :=
    hFan.eqOn_of_preconnected_of_frequently_eq
      (hQan.mono (ball_subset_ball (min_le_right _ _)))
      (convex_ball _ _).isPreconnected (mem_ball_self hs0) hfreq
  have hQp : HasFPowerSeriesAt Q p 0 :=
    hF.hasFPowerSeriesAt.congr (Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hs0) heq)
  have hR0 : 0 < (‖X‖ + ρ) / 2 := by positivity
  set R : NNReal := ⟨(‖X‖ + ρ) / 2, hR0.le⟩ with hRdef
  have hR : 0 < R := by rw [← NNReal.coe_pos]; exact hR0
  have hdR : DifferentiableOn ℂ Q (closedBall 0 R) :=
    hQ.mono (closedBall_subset_ball (by change (‖X‖ + ρ) / 2 < ρ; linarith))
  have hC := hdR.hasFPowerSeriesOnBall hR
  have hCp : cauchyPowerSeries Q 0 R = p := hC.hasFPowerSeriesAt.eq_formalMultilinearSeries hQp
  rw [hCp] at hC
  have hXm : X ∈ Metric.eball (0 : ℂ) R := by
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; change ‖X‖ < (‖X‖ + ρ) / 2; linarith)
  have := hC.hasSum hXm
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this
  exact this

theorem gradedSeries_continuation_dominated : ∀ {ι : Type} (deg : ι → ℕ),
    (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ),
    0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) →
    DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) →
    (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧
      HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) →
    ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧
      Summable (fun i => b i * ‖X‖ ^ deg i) := by
  intro ι deg hfin a b C δ ρ P P' hδ hb hab hP hP' h X hX
  have hA := gradedSeries_continue deg a δ ρ P hδ hP (fun x h1 h2 => (h x h1 h2).1) X hX
  have hB := gradedSeries_continue deg (fun i => (b i : ℂ)) δ ρ P' hδ hP'
    (fun x h1 h2 => (h x h1 h2).2) ((‖X‖ : ℝ) : ℂ) (by simpa using hX)
  have hBr : Summable (fun k => (∑' i : deg ⁻¹' {k}, b i) * ‖X‖ ^ k) := by
    rw [← Complex.summable_ofReal]
    refine hB.summable.congr fun k => ?_
    push_cast [Complex.ofReal_tsum]
    rfl
  have hsb : Summable (fun i => b i * ‖X‖ ^ deg i) := by
    rw [← (Equiv.sigmaFiberEquiv deg).summable_iff]
    rw [summable_sigma_of_nonneg (f := (fun i => b i * ‖X‖ ^ deg i) ∘ (Equiv.sigmaFiberEquiv deg))
      (fun _ => mul_nonneg (hb _) (pow_nonneg (norm_nonneg _) _))]
    refine ⟨fun k => ?_, ?_⟩
    · have : Finite {i // deg i = k} := (hfin k).to_subtype
      exact Summable.of_finite
    · refine hBr.congr fun k => ?_
      rw [← tsum_mul_right]
      exact tsum_congr fun y => by
        simp [Equiv.sigmaFiberEquiv, show deg y.1 = k from y.2]
  have hsa : Summable (fun i => a i * X ^ deg i) := by
    refine Summable.of_norm_bounded (hsb.mul_left C) fun i => ?_
    rw [norm_mul, norm_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hab i) (pow_nonneg (norm_nonneg _) _)
  refine ⟨?_, hsb⟩
  have h3 := hsa.hasSum
  have h4 := (gradedSeries_regroup deg a X _ h3).unique hA
  rw [h4] at h3
  exact h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsSmallerLevelRelIndexMul
section
namespace GlobalTheory

open QuotientGroup

theorem hasSum_comp_fst_card_mul_of_fintype {α β : Type} [Fintype β] (f : α → ℂ) (a : ℂ) (hf : HasSum f a) :
    HasSum (fun p : α × β => f p.1) ((Fintype.card β : ℂ) * a) := by
  classical
  have hdec : (fun p : α × β => f p.1) = fun p => ∑ b : β, (if p.2 = b then f p.1 else 0) := by
    funext p
    simp
  rw [hdec]
  have hterm : ∀ b ∈ (Finset.univ : Finset β),
      HasSum (fun p : α × β => if p.2 = b then f p.1 else 0) a := by
    intro b _
    have hinj : Function.Injective (fun x : α => (x, b)) := fun x y h => by
      simpa using congrArg Prod.fst h
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def] using hf
    · intro p hp
      by_cases h : p.2 = b
      · exact absurd ⟨p.1, by ext <;> simp [h]⟩ hp
      · simp [h]
  have := hasSum_sum hterm
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

theorem hasSum_cosets_smaller_level_relIndex_mul : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  intro G _ K J H Γ hKJ hJH hHΓ hidx Ψ z hvan hinv hsum
  classical

  set f : Γ ⧸ J.subgroupOf Γ → ℂ := fun x => Ψ (x.out : Γ) with hf
  have hfmk : ∀ g : Γ, f (mk g) = Ψ (g : G) := by
    intro g
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf Γ) g
    simp only [hf, hj, Subgroup.coe_mul]
    exact hinv _ g.2 _ (Subgroup.mem_subgroupOf.mp j.2)

  let ι : H ⧸ J.subgroupOf H → Γ ⧸ J.subgroupOf Γ := fun y => mk (Subgroup.inclusion hHΓ y.out)
  have hιmk : ∀ a : H, ι (mk a) = mk (Subgroup.inclusion hHΓ a) := by
    intro a
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) a
    show (mk (Subgroup.inclusion hHΓ (mk a : H ⧸ J.subgroupOf H).out) : Γ ⧸ J.subgroupOf Γ) = _
    rw [hj, QuotientGroup.eq]
    simp [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp j.2
  have hιinj : Function.Injective ι := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [hιmk, hιmk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hxy
  have h1 : HasSum f z := by
    rw [← hιinj.hasSum_iff]
    · convert hsum using 1
      funext y
      show f (mk (Subgroup.inclusion hHΓ y.out)) = _
      rw [hfmk]
      rfl
    · intro x hx
      show Ψ (x.out : G) = 0
      apply hvan _ x.out.2
      intro hH
      apply hx
      refine ⟨mk ⟨(x.out : G), hH⟩, ?_⟩
      rw [hιmk]
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rfl

  have hle : K.subgroupOf Γ ≤ J.subgroupOf Γ := fun x hx => by
    simpa [Subgroup.mem_subgroupOf] using hKJ (Subgroup.mem_subgroupOf.mp hx)
  let e := Subgroup.quotientEquivProdOfLE hle
  have hJΓ : J ≤ Γ := hJH.trans hHΓ
  have hrel : (K.subgroupOf Γ).relIndex (J.subgroupOf Γ) = K.relIndex J :=
    Subgroup.relIndex_subgroupOf hJΓ
  haveI : (((K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))).FiniteIndex := ⟨by
    rw [← Subgroup.relIndex, hrel]; exact hidx⟩
  haveI : Finite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))
  have hcard : (Fintype.card (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) : ℂ)
      = (K.relIndex J : ℂ) := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index, ← Subgroup.relIndex, hrel]
  have h2 := hasSum_comp_fst_card_mul_of_fintype (β := J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) f z h1
  rw [hcard, ← e.hasSum_iff] at h2
  convert h2 using 1
  funext y
  have he1 : (e y).1 = mk y.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  simp only [Function.comp_apply, he1, hfmk]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumOfDominatedOfEqNearZero
section
open Metric Filter Topology

namespace GlobalTheory

theorem hasSum_of_dominated_of_eq_near_zero {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ)
    (hbc : ∀ i, ‖b i‖ ≤ c i)
    (hc : ∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hnear : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) :
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) := by
  intro z hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hbound : ∀ i (w : ℂ), ‖b i * w ^ n i‖ ≤ c i * ‖w‖ ^ n i := by
    intro i w
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbc i) (pow_nonneg (norm_nonneg w) _)
  have hsum : ∀ w : ℂ, ‖w‖ < r → Summable (fun i => b i * w ^ n i) := by
    intro w hw
    exact Summable.of_norm_bounded (hc ‖w‖ (norm_nonneg w) hw) (fun i => hbound i w)
  let F : ℂ → ℂ := fun w => ∑' i, b i * w ^ n i
  have hFd : DifferentiableOn ℂ F (ball 0 r) := by
    intro w hw
    have hw' : ‖w‖ < r := by simpa using hw
    obtain ⟨s, hws, hsr⟩ := exists_between hw'
    have hs0 : 0 ≤ s := le_trans (norm_nonneg w) hws.le
    have hd : DifferentiableOn ℂ F (ball 0 s) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (u := fun i => c i * s ^ n i) (hc s hs0 hsr)
        (fun i => ?_) isOpen_ball (fun i v hv => ?_)
      · exact ((differentiable_const _).mul (differentiable_id.pow _)).differentiableOn
      · refine (hbound i v).trans ?_
        have hv' : ‖v‖ < s := by simpa using hv
        have hci : 0 ≤ c i := (norm_nonneg _).trans (hbc i)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv'.le _) hci
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hws))).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F (ball 0 r) := hFd.analyticOnNhd isOpen_ball
  have hRa : AnalyticOnNhd ℂ R (ball 0 r) := hR.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = R w := by
    apply Eventually.frequently
    have h1 : ∀ᶠ w in 𝓝 (0:ℂ), w ∈ ball (0:ℂ) ε := isOpen_ball.mem_nhds (mem_ball_self hε)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw hw0
    have hw0' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hwε : ‖w‖ < ε := by simpa using hw
    exact (hnear w hw0' hwε).tsum_eq
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hRa (convex_ball (0:ℂ) r).isPreconnected
    (mem_ball_self hr) hfreq
  have hzb : z ∈ ball (0:ℂ) r := by simpa using hz
  rw [← heq hzb]
  exact (hsum z hz).hasSum

theorem hasSum_of_dominated_of_eq_near_zero' : ∀ {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ) (R : ℂ → ℂ) (r ε : ℝ), (∀ i, ‖b i‖ ≤ c i) →
    (∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) → 0 < ε →
    DifferentiableOn ℂ R (Metric.ball 0 r) →
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) →
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) :=
  fun b c n R r ε h1 h2 h3 h4 h5 => hasSum_of_dominated_of_eq_near_zero b c n R r ε h1 h2 h3 h4 h5

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermiteReductionUnipotent
section
namespace GlobalTheory

theorem hermite_reduction_column {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R → R) (hb : ∀ i j, j < i → b i j = 0) (hr : ∀ i y, b i i ∣ y - r i y)
    (j : Fin n) (m : ℕ) :
    ∃ x : Fin n → R, x j = 1 ∧ (∀ l, j < l → x l = 0) ∧
      ∀ i : Fin n, i < j → (j : ℕ) ≤ i + m → ∃ y, b.mulVec x i = r i y := by
  induction m with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [hl.ne'], fun i hi hj => ?_⟩
    exact absurd (Fin.lt_def.1 hi) (by omega)
  | succ m ih =>
    obtain ⟨x, hx1, hx0, hx⟩ := ih
    by_cases h : ∃ k : Fin n, (j : ℕ) = k + m + 1
    · obtain ⟨k, hk⟩ := h
      obtain ⟨z, hz⟩ := hr k (b.mulVec x k)
      have hkj : k < j := Fin.lt_def.2 (by omega)
      have key : ∀ i, b.mulVec (x - Pi.single k z) i = b.mulVec x i - b i k * z := by
        intro i
        rw [Matrix.mulVec_sub, Pi.sub_apply]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      refine ⟨x - Pi.single k z, ?_, fun l hl => ?_, fun i hi hj => ?_⟩
      · simp [hx1, hkj.ne']
      · simp [hx0 l hl, (hkj.trans hl).ne']
      · rw [key]
        by_cases hik : i = k
        · subst hik
          exact ⟨b.mulVec x i, by rw [← hz]; ring⟩
        · have hne : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
          have hki : k < i := Fin.lt_def.2 (by omega)
          rw [hb i k hki, zero_mul, sub_zero]
          exact hx i hi (by omega)
    · refine ⟨x, hx1, hx0, fun i hi hj => hx i hi ?_⟩
      by_contra hc
      exact h ⟨i, by omega⟩

theorem hermite_reduction_unipotent :
    ∀ (R : Type) [CommRing R] (n : ℕ) (b : Matrix (Fin n) (Fin n) R) (r : Fin n → R → R),
      (∀ i j, j < i → b i j = 0) → (∀ i y, b i i ∣ y - r i y) →
      ∃ u : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        ∀ i j, i < j → ∃ y, (b * u) i j = r i y := by
  intro R _ n b r hb hr
  choose x hx1 hx0 hx using fun j : Fin n => hermite_reduction_column b r hb hr j n
  refine ⟨Matrix.of fun i j => x j i, fun i j h => hx0 j i h, fun i => hx1 i, fun i j h => ?_⟩
  obtain ⟨y, hy⟩ := hx j i h (by have := j.2; omega)
  exact ⟨y, by rw [← hy]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsAlt
section
namespace GlobalTheory.LemmaTwoFortyThirteen

theorem main {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ (0 : R) ∧ a • v ∈ M) :
    Submodule.span K (↑M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha, hav⟩ := h v
  have hK : algebraMap R K a ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne ha
  have hv : v = (algebraMap R K a)⁻¹ • (a • v) := by
    rw [← algebraMap_smul K a v, smul_smul, inv_mul_cancel₀ hK, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hav)

end GlobalTheory.LemmaTwoFortyThirteen
end

