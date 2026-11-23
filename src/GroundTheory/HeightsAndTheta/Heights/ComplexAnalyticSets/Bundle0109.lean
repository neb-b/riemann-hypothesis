module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Theta.SplitLinear.RankMinors
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceHasBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem PlaceHasBranch.proof (h₁ : PlaceBranchExists.Statement) (h₂ : PuncturedBranchInOneBranch.Statement)
    (h₃ : PuncturedBranchSameOrder.Statement) : PlaceHasBranch.Statement := by
  intro n I q m c hrad hdim hcov hdisj P
  obtain ⟨N, hN, hNc⟩ := hcov
  obtain ⟨ν, hν⟩ := h₁ n I q hrad hdim P
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]

  have hcont : ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) 0 := by
    have h0 : ContinuousAt ν.toFun (fun _ ↦ (0 : ℂ)) :=
      ν.differentiableOn.continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right, hnorm] using ν.radius_pos))
    exact h0.comp (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N := hcont.preimage_mem_nhds (by rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  have hin : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < min ε ν.radius → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image := by
    intro τ _ hτ
    refine hNc ⟨ν.mapsTo ?_, hεN ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact hτ.trans_le (min_le_right _ _)
    · rw [dist_zero_right]
      exact hτ.trans_le (min_le_left _ _)
  obtain ⟨b, ρ', hρ', hb⟩ := h₂ n I q m c ν (min ε ν.radius) hrad hdim (lt_min hε ν.radius_pos) hin hdisj
  exact ⟨b, fun f ↦ (hν f).trans (h₃ n I q (c b) ν ρ' hrad hdim hρ' hb f).symm⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaneSliceMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff Matrix

noncomputable section

theorem maDens_congr {D : ℕ} {F G : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 z] G k) : ReciprocityTheory.AnForm.maDens F z = ReciprocityTheory.AnForm.maDens G z := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) z = fderiv ℝ (fderiv ℝ (G k)) z :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) z) = fun k => ReciprocityTheory.AnForm.hessC (G k) z := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeBranchDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem PrimeBranchDimOne.proof : PrimeBranchDimOne.Statement := by
  intro n J q c hJ hloc

  have hq : q ∈ zeroSet J := by
    have := c.mapsTo (Metric.mem_ball_self c.radius_pos)
    rwa [c.map_zero] at this

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    have h1 := ringKrullDim_quotient_le J
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at hle hnn
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hnn (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact absurd (WithBot.coe_le_coe.mp h3) (by simp)
      | coe e => exact ⟨e, rfl⟩
  have hdim : ringKrullDim (localRingAt J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have he1 : e ≤ 1 := by
    have h2 : ((e : ℕ) : WithBot ℕ∞) ≤ 1 := hdim ▸ hloc
    exact_mod_cast h2
  rw [he]
  obtain h0 | h1 : e = 0 ∨ e = 1 := by omega
  swap
  · rw [h1]
  exfalso
  subst h0

  have hfield : IsField (MvPolynomial (Fin n) ℂ ⧸ J) := by
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).2 (by simpa using he)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield
  have hJM : J = RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    hmax.eq_of_le (RingHom.ker_ne_top _) (fun f hf => RingHom.mem_ker.mpr (hq f hf))

  have hZ : ∀ x ∈ zeroSet J, x = q := by
    intro x hx
    funext i
    have hmem : X i - C (q i) ∈ J := by
      rw [hJM, RingHom.mem_ker]
      simp
    have := hx _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.mp this

  set r := c.radius
  let v : Fin 1 → ℂ := fun _ => ((r / 2 : ℝ) : ℂ)
  have hv : v ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff c.radius_pos]
    intro i
    simp only [v, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos c.radius_pos)]
    exact half_lt_self c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := Metric.mem_ball_self c.radius_pos
  have heq : c.toFun v = c.toFun 0 := by
    rw [hZ _ (c.mapsTo hv), hZ _ (c.mapsTo h0)]
  have := congrFun (c.injOn hv h0 heq) 0
  simp only [v, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  exact (half_pos c.radius_pos).ne' this

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionUnramifiedGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjectionUnramifiedGeneric

theorem pderiv_inr_rename_inl {α β : Type} (b : β) (a : MvPolynomial α ℂ) :
    pderiv (Sum.inr b) (rename (Sum.inl : α → α ⊕ β) a) = 0 := by
  classical
  induction a using MvPolynomial.induction_on with
  | C c => simp
  | add p p' hp hp' => simp [hp, hp']
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]

theorem proof : ProjectionUnramifiedGeneric.Statement := by
  classical
  intro α β _ _ Q r q t hQ hint hqQ htQ hgen
  let L := FractionRing (MvPolynomial (α ⊕ β) ℂ ⧸ Q)
  let φ : MvPolynomial (α ⊕ β) ℂ →+* L := (algebraMap (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ Q := by
    intro p
    have hinj := IsFractionRing.injective (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L
    simp only [φ, RingHom.comp_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_zero (algebraMap (MvPolynomial (α ⊕ β) ℂ ⧸ Q) L)]
    exact hinj.eq_iff
  let ι : MvPolynomial α ℂ →+* MvPolynomial (α ⊕ β) ℂ := (rename Sum.inl : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial (α ⊕ β) ℂ).toRingHom

  let D : (β → L) → MvPolynomial (α ⊕ β) ℂ → L := fun c p => ∑ b, φ (pderiv (Sum.inr b) p) * c b
  have hDadd : ∀ c p p', D c (p + p') = D c p + D c p' := by
    intro c p p'
    simp only [D, map_add (f := _), add_mul, Finset.sum_add_distrib]
  have hDmul : ∀ c p p', D c (p * p') = φ p * D c p' + φ p' * D c p := by
    intro c p p'
    simp only [D]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pderiv_mul]
    simp only [map_add (f := _), map_mul]
    ring
  have hDsum : ∀ c (f : Fin r → MvPolynomial (α ⊕ β) ℂ), D c (∑ j, f j) = ∑ j, D c (f j) := by
    intro c f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [D, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hDX : ∀ c b, D c (X (Sum.inr b)) = c b := by
    intro c b
    simp [D, pderiv_X, Pi.single_apply]
  have hDι : ∀ c a, D c (ι a) = 0 := by
    intro c a
    simp [D, ι, pderiv_inr_rename_inl]
  have hDpoly : ∀ c b (G : Polynomial (MvPolynomial α ℂ)),
      D c (G.eval₂ ι (X (Sum.inr b))) =
        φ ((Polynomial.derivative G).eval₂ ι (X (Sum.inr b))) * c b := by
    intro c b G
    induction G using Polynomial.induction_on with
    | C a => simp [hDι]
    | add f g hf hg => simp only [Polynomial.eval₂_add, hDadd, hf, hg, Polynomial.derivative_add,
        map_add, add_mul]
    | monomial n a h =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial (MvPolynomial α ℂ)) =
          Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
      rw [e, Polynomial.eval₂_mul, hDmul, h, Polynomial.eval₂_X, hDX]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_one, Polynomial.eval₂_X, map_add, map_mul, mul_one]
      ring

  have hker : ∀ c : β → L, (∀ j, D c (q j) = 0) → c = 0 := by
    intro c hc
    have hDQ : ∀ p ∈ Q, D c p = 0 := by
      intro p hp
      obtain ⟨i, hi⟩ := hgen p hp
      obtain ⟨g, hg⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hi
      have h1 : D c (t ^ i * p) = 0 := by
        rw [← hg, hDsum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hDmul, hc j, (hφ _).2 (hqQ j)]
        ring
      rw [hDmul, (hφ p).2 hp, zero_mul, add_zero] at h1
      have ht : φ t ≠ 0 := fun h => htQ ((hφ t).1 h)
      rw [map_pow] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ ht)
    funext b
    obtain ⟨F, hFm, hF⟩ := hint b
    set y : L := φ (X (Sum.inr b))
    set Fb : Polynomial L := F.map (φ.comp ι)
    have hFb0 : Fb ≠ 0 := (hFm.map _).ne_zero
    have hev : ∀ G : Polynomial (MvPolynomial α ℂ),
        φ (G.eval₂ ι (X (Sum.inr b))) = (G.map (φ.comp ι)).eval y := by
      intro G
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]
    have hroot : Fb.IsRoot y := by
      show Fb.eval y = 0
      rw [← hev]
      exact (hφ _).2 hF
    set k := Polynomial.rootMultiplicity y Fb
    have hk : 0 < k := (Polynomial.rootMultiplicity_pos hFb0).2 hroot
    set G := Polynomial.derivative^[k - 1] F
    have hG : G.eval₂ ι (X (Sum.inr b)) ∈ Q := by
      rw [← hφ, hev, ← Polynomial.iterate_derivative_map]
      exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (Nat.sub_lt hk one_pos)
    have hG' : φ ((Polynomial.derivative G).eval₂ ι (X (Sum.inr b))) ≠ 0 := by
      have e : Polynomial.derivative G = Polynomial.derivative^[k] F := by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm, Function.iterate_succ_apply']
      rw [e, hev, ← Polynomial.iterate_derivative_map, Polynomial.eval_iterate_derivative_rootMultiplicity]
      have : CharZero L := charZero_of_injective_ringHom (φ.comp MvPolynomial.C).injective
      rw [nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
        (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero y hFb0)
    have h0 := hDQ _ hG
    rw [hDpoly] at h0
    exact (mul_eq_zero.1 h0).resolve_left hG'

  let M : Matrix (Fin r) β L := Matrix.of fun j b => φ (pderiv (Sum.inr b) (q j))
  have hMinj : Function.Injective M.mulVecLin := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    apply hker c
    intro j
    have := congrFun hc j
    simpa [M, Matrix.mulVec, dotProduct, D] using this
  have hrank : M.rank = Fintype.card β := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hMinj, Module.finrank_fintype_fun_eq_card]
  obtain ⟨I, J, hIJ⟩ := GroundTheory.Heights₂.Theta.SplitLinear.exists_minor_ne_zero M hrank.ge
  have hJinj : Function.Injective J := by
    intro x x' hxx'
    by_contra hne
    exact hIJ (Matrix.det_zero_of_column_eq hne fun p => by simp [M, hxx'])
  have hJbij : Function.Bijective J :=
    (Fintype.bijective_iff_injective_and_card J).2 ⟨hJinj, by simp⟩
  let e := Equiv.ofBijective J hJbij
  let μ : MvPolynomial (α ⊕ β) ℂ := (Matrix.of fun p p' => pderiv (Sum.inr (J p')) (q (I p))).det
  refine ⟨μ, ?_, ?_⟩
  · intro hμ
    apply hIJ
    rw [← (hφ μ).2 hμ, RingHom.map_det]
    congr 1
  · intro w _ hw v hvX hv
    have hdet : (Matrix.of fun p p' => eval w (pderiv (Sum.inr (J p')) (q (I p)))).det ≠ 0 := by
      rw [RingHom.map_det] at hw
      convert hw using 2
      ext p p'
      simp [RingHom.mapMatrix_apply]
    have hsub : Matrix.mulVec (Matrix.of fun p p' => eval w (pderiv (Sum.inr (J p')) (q (I p))))
        (fun p => v (Sum.inr (J p))) = 0 := by
      funext p
      have h1 := hv (I p)
      rw [Fintype.sum_sum_type] at h1
      simp only [hvX, mul_zero, Finset.sum_const_zero, zero_add] at h1
      rw [← Equiv.sum_comp e] at h1
      simpa [Matrix.mulVec, dotProduct, e] using h1
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hsub
    funext s
    cases s with
    | inl a => exact hvX a
    | inr b =>
      have h1 : v (Sum.inr (J (e.symm b))) = 0 := congrFun hz (e.symm b)
      have h2 : J (e.symm b) = b := e.apply_symm_apply b
      rwa [h2] at h1

end ProjectionUnramifiedGeneric

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRadialPrimitive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

theorem RadialPrimitive.primitive_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ τ in c..t, f τ) ∧ deriv (fun t => ∫ τ in c..t, f τ) = f := by
  have hd : deriv (fun t => ∫ τ in c..t, f τ) = f :=
    funext fun t => hf.continuous.deriv_integral f c t
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t => ?_, by rw [hd]; exact hf⟩, hd⟩
  exact (hf.continuous.integral_hasStrictDerivAt c t).hasDerivAt.differentiableAt

theorem RadialPrimitive.proof : RadialPrimitive.Statement := by
  intro e a t₀ T ha ht₀ hconst hzero hint
  set c : ℝ := ((e + 1 : ℕ) : ℝ) with hc
  set g : ℝ → ℝ := fun τ => a τ * (c * τ ^ (e + 1 - 1)) with hg
  set P : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, g τ with hP
  have hgs : ContDiff ℝ ∞ g := ha.mul (contDiff_const.mul (contDiff_id.pow _))
  obtain ⟨hPs, hPd⟩ := RadialPrimitive.primitive_contDiff g hgs 0
  have hrt : ∀ t, radialTransform (e + 1) a t = a t * t ^ (e + 1) - P t := fun t => rfl

  have hPc : ∀ t ∈ Set.Icc 0 t₀, P t = a 0 * t ^ (e + 1) := by
    intro t ht
    have h0 := radialTransform_eq_zero_of_const e a hconst ht
    rw [hrt, hconst t ht] at h0
    linarith
  set h : ℝ → ℝ := fun t => if t < t₀ then a 0 else P t / t ^ (e + 1) with hh
  have hlow : ∀ t, t < t₀ → h t = a 0 := fun t ht => if_pos ht
  have hpos : ∀ t, 0 < t → h t = P t / t ^ (e + 1) := by
    intro t ht
    by_cases h1 : t < t₀
    · rw [hlow t h1, hPc t ⟨ht.le, h1.le⟩, mul_div_assoc, div_self (pow_ne_zero _ ht.ne'), mul_one]
    · exact if_neg h1
  have hlowE : ∀ x, x < t₀ → h =ᶠ[nhds x] fun _ => a 0 := fun x hx =>
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds hx) fun t ht => hlow t ht
  have hposE : ∀ x, 0 < x → h =ᶠ[nhds x] fun t => P t / t ^ (e + 1) := fun x hx =>
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun t ht => hpos t ht
  have hs : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < t₀
    · exact contDiffAt_const.congr_of_eventuallyEq (hlowE x hx)
    · have hx0 : 0 < x := lt_of_lt_of_le ht₀ (not_lt.1 hx)
      exact (hPs.contDiffAt.div (contDiff_id.pow _).contDiffAt (pow_ne_zero _ hx0.ne')).congr_of_eventuallyEq
        (hposE x hx0)

  set R : ℝ := max T t₀ with hR
  have hPz : ∀ t, R ≤ t → P t = 0 := by
    intro t ht
    have hTt : T ≤ t := le_trans (le_max_left _ _) ht
    have hgc : Continuous g := hgs.continuous
    have htail : ∫ τ in T..t, g τ = 0 := by
      have hcg : ∫ τ in T..t, g τ = ∫ τ in T..t, (0 : ℝ) :=
        intervalIntegral.integral_congr fun τ hτ => by
          rw [Set.uIcc_of_le hTt] at hτ
          simp [hg, hzero τ hτ.1]
      rw [hcg]
      simp
    have := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := T) (c := t)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    simp only [hP]
    rw [← this, htail, add_zero]
    exact hint
  have hhz : ∀ t, R ≤ t → h t = 0 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₀ (le_trans (le_max_right _ _) ht)
    rw [hpos t ht0, hPz t ht, zero_div]
  obtain ⟨hQs, hQd⟩ := RadialPrimitive.primitive_contDiff h hs R
  refine ⟨fun t => ∫ τ in R..t, h τ, hQs, ⟨R, fun t ht => ?_⟩, ?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · have hcg : ∫ τ in R..t, h τ = ∫ τ in R..t, (0 : ℝ) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [Set.uIcc_of_le ht] at hτ
        exact hhz τ hτ.1
    show ∫ τ in R..t, h τ = 0
    rw [hcg]
    simp
  · rw [hQd]
    exact hlow 0 ht₀
  · rw [hQd, (hlowE 0 ht₀).deriv_eq]
    simp
  · rw [hQd, hpos t ht, hrt, div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')]
    ring
  · rw [hQd, (hposE t ht).deriv_eq, hrt]
    have hPt : HasDerivAt P (g t) t := (hgs.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hq : HasDerivAt (fun s => P s / s ^ (e + 1))
        ((g t * t ^ (e + 1) - P t * (((e + 1 : ℕ) : ℝ) * t ^ (e + 1 - 1))) / (t ^ (e + 1)) ^ 2) t :=
      hPt.div (hasDerivAt_pow (e + 1) t) (pow_ne_zero _ ht.ne')
    rw [hq.deriv]
    simp only [hg, hc, Nat.add_sub_cancel]
    have ht' : t ≠ 0 := ht.ne'
    push_cast
    field_simp
    ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrderBranchesMeet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable def VarBranch.restrictInto {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I k q) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Metric.ball (0 : Fin k → ℂ) ε, c.toFun t ∈ zeroSet J) : VarBranch J k q where
  radius := min ε c.radius
  radius_pos := lt_min hε c.radius_pos
  toFun := c.toFun
  differentiableOn := c.differentiableOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  injOn := c.injOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  map_zero := c.map_zero
  mapsTo := fun t ht ↦ h t (Metric.ball_subset_ball (min_le_left _ _) ht)

theorem VarBranch.eventually_mem_zeroSet {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I 1 q) (h : ∀ f ∈ J, branchOrder c f = ⊤) :
    ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J := by
  have key : ∀ f ∈ J, ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), eval (c.toFun t) f = 0 := by
    intro f hf
    have h0 := analyticOrderAt_eq_top.1 (h f hf)
    have ht : Tendsto (fun t : Fin 1 → ℂ ↦ t 0) (𝓝 0) (𝓝 0) := (continuous_apply 0).tendsto' _ _ rfl
    filter_upwards [ht.eventually h0] with t ht
    have : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    rwa [this] at ht
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J : J.FG)
  filter_upwards [(s.eventually_all).2 fun g hg ↦ key g (hs ▸ Submodule.subset_span hg)] with t ht f hf
  have hle : Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) ≤ RingHom.ker (eval (c.toFun t)) :=
    Ideal.span_le.2 fun g hg ↦ ht g hg
  have hf' : f ∈ Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) := by
    rw [Ideal.span, hs]
    exact hf
  exact hle hf'

end GroundTheory.Heights₂.Heights
end

