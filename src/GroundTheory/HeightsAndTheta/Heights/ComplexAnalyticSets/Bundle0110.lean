module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrdersLiftCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem eventually_const_mem_ball_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
  have hc : Continuous (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) := continuous_pi fun _ ↦ continuous_id
  exact hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (0 : Fin 1 → ℂ) hr)

theorem analyticAt_comp_const_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {φ : (Fin 1 → ℂ) → E} {r : ℝ} (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) :
    AnalyticAt ℂ (fun τ : ℂ ↦ φ (fun _ ↦ τ)) 0 := by
  have hc : Differentiable ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) :=
    differentiable_pi.2 fun _ ↦ differentiable_id
  exact DifferentiableOn.analyticAt (s := (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) ⁻¹' Metric.ball 0 r)
    (hφ.comp hc.differentiableOn fun _ h ↦ h) (eventually_const_mem_ball_one hr)

theorem analyticAt_eval_of_analyticAt_zero {n : ℕ} {F : ℂ → Fin n → ℂ} (hF : AnalyticAt ℂ F 0)
    (p : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun τ ↦ eval (F τ) p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (analyticAt_pi_iff.mp hF i)

theorem branchOrder_ne_top_of_not_mem (hB : BranchOffHypersurface.Statement) {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (γ : VarBranch J 1 q) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)) {b : MvPolynomial (Fin n) ℂ} (hb : b ∉ J) :
    branchOrder γ b ≠ ⊤ := by
  intro htop
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (analyticOrderAt_eq_top.1 htop)
  have hU : Metric.ball (0 : Fin 1 → ℂ) (min ε γ.radius) ⊆ Metric.ball 0 γ.radius :=
    Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨t, ht, hne⟩ := hB n 1 J b _ γ.toFun hJ hdim hb Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (lt_min hε γ.radius_pos)⟩ (γ.differentiableOn.mono hU) (γ.injOn.mono hU)
    fun t ht ↦ γ.mapsTo (hU ht)
  have ht0 : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
  apply hne
  rw [← ht0]
  apply hεb
  rw [Metric.mem_ball, dist_zero_right] at ht ⊢
  exact lt_of_le_of_lt (norm_le_pi_norm t 0) (lt_of_lt_of_le ht (min_le_left _ _))

theorem SameOrdersLiftCentre.proof (hB : BranchOffHypersurface.Statement) : SameOrdersLiftCentre.Statement := by
  intro n J q M γ γ' Γ Γ' hJ hdim hΓd hΓ hΓ'd hΓ' hord
  funext s
  rcases s with j | i
  · have e := congrFun (hΓ 0 (Metric.mem_ball_self γ.radius_pos)).2 j
    have e' := congrFun (hΓ' 0 (Metric.mem_ball_self γ'.radius_pos)).2 j
    simp only [firstCoords] at e e'
    rw [e, e', γ.map_zero, γ'.map_zero]
  obtain ⟨a, b, hb, hab⟩ := M.birational i

  have key : ∀ (c : VarBranch J 1 q) (L : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
      DifferentiableOn ℂ L (Metric.ball 0 c.radius) →
      (∀ τ ∈ Metric.ball 0 c.radius, L τ ∈ zeroSetIn M.ideal ∧ firstCoords (L τ) = c.toFun τ) → ∀ l : ℂ,
      branchOrder c (a - C l * b) =
        branchOrder c b + analyticOrderAt (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 := by
    intro c L hLd hL l
    have hLa : AnalyticAt ℂ (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
      ((analyticAt_pi_iff.mp (analyticAt_comp_const_one c.radius_pos hLd)) (Sum.inr i)).sub analyticAt_const
    have hBa := analyticAt_eval_of_analyticAt_zero (analyticAt_comp_const_one c.radius_pos c.differentiableOn) b
    rw [branchOrder, branchOrder, ← analyticOrderAt_mul hBa hLa]
    apply analyticOrderAt_congr
    filter_upwards [eventually_const_mem_ball_one c.radius_pos] with τ hτ
    have h := (hL _ hτ).1 _ hab
    simp only [eval_sub, eval_mul, eval_X, eval_rename] at h
    change eval (firstCoords (L fun _ ↦ τ)) b * _ - eval (firstCoords (L fun _ ↦ τ)) a = 0 at h
    rw [(hL _ hτ).2] at h
    simp only [eval_sub, eval_mul, eval_C, Pi.mul_apply]
    linear_combination -h
  set l := Γ 0 (Sum.inr i)
  have k1 := key γ Γ hΓd hΓ l
  have k2 := key γ' Γ' hΓ'd hΓ' l
  rw [← hord, ← hord] at k2
  have heq := WithTop.add_left_cancel (branchOrder_ne_top_of_not_mem hB γ hJ hdim hb) (k1.symm.trans k2)
  have hGa : AnalyticAt ℂ (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ.radius_pos hΓd)) (Sum.inr i)).sub analyticAt_const
  have hG'a : AnalyticAt ℂ (fun τ : ℂ ↦ Γ' (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ'.radius_pos hΓ'd)) (Sum.inr i)).sub analyticAt_const
  have hz : analyticOrderAt (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 ≠ 0 :=
    hGa.analyticOrderAt_ne_zero.2 (sub_self _)
  rw [heq] at hz
  exact (sub_eq_zero.1 (hG'a.analyticOrderAt_ne_zero.1 hz)).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetFormComparison

theorem hessC_congr {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    hessC f y = hessC g y := by
  unfold hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

theorem contDiff_logPot (N : ℕ) : ContDiff ℝ ∞ (HilbertSamuel.ProjFS.logPot (N := N)) := by
  have h : (HilbertSamuel.ProjFS.logPot (N := N)) = fun z => Real.log (1 + euclPot z) := rfl
  rw [h]
  exact (contDiff_const.add (contDiff_euclPot N)).log fun z => by
    have : 0 ≤ euclPot z := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith

theorem posSemidef_hessC_logPot_sub {N : ℕ} {z : Fin N → ℂ} (hz : ‖z‖ ≤ 1) :
    ((((1 + N : ℝ) ^ 2 : ℝ) : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1).PosSemidef := by
  set m : ℝ := (1 + N) ^ 2 with hm
  have h1 : ContDiffAt ℝ 2 (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w) z :=
    contDiffAt_const.mul (((contDiff_logPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have h2 : ContDiffAt ℝ 2 (fun w => (-1 : ℝ) * euclPot w) z :=
    contDiffAt_const.mul (((contDiff_euclPot N).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt)
  have e : (m : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z - 1 =
      hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z := by
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ z h1 h2, ReciprocityTheory.AnForm.M.hessC_const_mul',
      ReciprocityTheory.AnForm.M.hessC_const_mul', TubeFormComparison.hessC_euclPot]
    simp [sub_eq_add_neg]
  rw [e]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ z (h1.add h2) fun w => ?_
  have hq := ReciprocityTheory.AnForm.M.re_star_dot_hessC
    (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z (star w)
  have hq' : levi (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z w =
      (star (star w) ⬝ᵥ (hessC (fun w => m * HilbertSamuel.ProjFS.logPot (N := N) w + (-1 : ℝ) * euclPot w) z
        *ᵥ star w)).re := by rw [hq, star_star]
  rw [hq', ← e, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, HilbertSamuel.ProjFS.hessC_logPot_eq_chernCoeff 0, Matrix.smul_mulVec,
    dotProduct_smul, CP.chernCoeff_quadForm, CP.star_dotProduct_self]
  set a : ℝ := ∑ j, ‖(star w) j‖ ^ 2 with ha
  set q : ℝ := 1 + normSqSum z with hqdef
  have hS0 : 0 ≤ normSqSum z := normSqSum_nonneg z
  have hSN : normSqSum z ≤ N := by
    have : ∀ j, ‖z j‖ ^ 2 ≤ 1 := fun j =>
      pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm z j).trans hz)
    calc normSqSum z = ∑ j, ‖z j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin N, (1 : ℝ) := Finset.sum_le_sum fun j _ => this j
      _ = N := by simp
  have hCS := CP.norm_dotProduct_sq_le z (star w)
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq1 : 1 ≤ q := by linarith
  have hpi := Real.pi_pos
  have hval : ((m : ℂ) • (((2 * Real.pi : ℝ) : ℂ) • ((1 / (2 * Real.pi * q) *
      (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) : ℝ) : ℂ)) - (a : ℂ)).re =
      m * (a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2) / q - a := by
    simp only [smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
    field_simp
  rw [hval]
  rw [← ha] at hCS
  have hd : q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 ≤ (1 - q⁻¹) * a := by
    rw [inv_mul_le_iff₀ (by linarith)]
    have : q * ((1 - q⁻¹) * a) = normSqSum z * a := by
      rw [hqdef]
      field_simp
      ring
    rw [this]
    exact hCS
  have hqm : q ^ 2 ≤ m := by
    rw [hm]
    have : q ≤ 1 + N := by linarith
    exact pow_le_pow_left₀ (by linarith) this 2
  have hqa : a / q ≤ a - q⁻¹ * ‖z ⬝ᵥ star w‖ ^ 2 := by
    have : a / q = q⁻¹ * a := by ring
    nlinarith
  rw [sub_nonneg, le_div_iff₀ (by linarith)]
  have h4 : q ^ 2 * (a / q) = q * a := by
    field_simp
  nlinarith [h4, mul_le_mul_of_nonneg_left hqa (by positivity : (0 : ℝ) ≤ m),
    mul_le_mul_of_nonneg_right hqm (div_nonneg ha0 (by linarith : (0 : ℝ) ≤ q))]

end SheetFormComparison


end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCMUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

theorem sliceCMUnmixed_local (h : CMQuotientUnmixed.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsPrime] {d : ℕ} (J : Ideal R) (ℓ : Fin d → R) (hℓ : ∀ i, ℓ i ∈ m)
    (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (π : Localization.AtPrime m →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J.map (algebraMap R (Localization.AtPrime m)))
    (hB : ringKrullDim B = (d + 1 : ℕ))
    (hS : ringKrullDim (Localization.AtPrime m ⧸
      (J ⊔ Ideal.span (Set.range ℓ)).map (algebraMap R (Localization.AtPrime m))) = (1 : ℕ)) :
    ∀ P ∈ associatedPrimes R (R ⧸ (J ⊔ Ideal.span (Set.range ℓ))), P ≤ m →
      P ∈ (J ⊔ Ideal.span (Set.range ℓ)).minimalPrimes ∧ P ≠ m := by
  intro P hP hPm
  obtain ⟨I, hI⟩ : ∃ I, I = J ⊔ Ideal.span (Set.range ℓ) := ⟨_, rfl⟩
  rw [← hI] at hP hS ⊢
  have hJI : J ≤ I := hI ▸ le_sup_left
  let x : Fin d → B := fun i => π (algebraMap R (Localization.AtPrime m) (ℓ i))

  have hspan : Ideal.span (Set.range x) = (I.map (algebraMap R (Localization.AtPrime m))).map π := by
    rw [hI, Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker π).2 hker.ge, bot_sup_eq,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp]
    rfl
  have hker_le : ∀ Q : Ideal R, J ≤ Q → RingHom.ker π ≤ Q.map (algebraMap R (Localization.AtPrime m)) :=
    fun Q hQ => hker ▸ Ideal.map_mono hQ
  have hcomap : ∀ Q : Ideal R, J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π =
        Q.map (algebraMap R (Localization.AtPrime m)) := fun Q hQ => by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 (hker_le Q hQ)]

  have hdimx : ringKrullDim (B ⧸ Ideal.span (Set.range x)) = (1 : ℕ) := by
    let f : Localization.AtPrime m →+* B ⧸ Ideal.span (Set.range x) := (Ideal.Quotient.mk _).comp π
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
    have hkf : RingHom.ker f = I.map (algebraMap R (Localization.AtPrime m)) := by
      ext c
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap,
        hcomap I hJI]
    rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf),
      ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hkf), hS]
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => by
    have : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact map_nonunit π _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m (ℓ i)).2
      (hℓ i))
  have hsum : ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B := by
    rw [hdimx, hB, ← Nat.cast_add, Nat.add_comm]

  obtain ⟨hPp, y, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmemP : ∀ s, s ∈ P ↔ s * r ∈ I := fun s => by
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot,
      show s • Ideal.Quotient.mk I r = Ideal.Quotient.mk I (s * r) from rfl, Ideal.Quotient.eq_zero_iff_mem]
  have hIP : I ≤ P := fun s hs => (hmemP s).2 (I.mul_mem_right r hs)
  have hdisj : ∀ Q : Ideal R, Q ≤ m → Disjoint (m.primeCompl : Set R) Q :=
    fun Q hQ => Set.disjoint_left.2 fun u hu huQ => hu (hQ huQ)
  have hprime : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      ((Q.map (algebraMap R (Localization.AtPrime m))).map π).IsPrime := fun Q hQ hQm hJQ => by
    have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) Q hQ (hdisj Q hQm)
    exact Ideal.map_isPrime_of_surjective hπ (hker_le Q hJQ)
  have hback : ∀ Q : Ideal R, Q.IsPrime → Q ≤ m → J ≤ Q →
      (((Q.map (algebraMap R (Localization.AtPrime m))).map π).comap π).comap
        (algebraMap R (Localization.AtPrime m)) = Q := fun Q hQ hQm hJQ => by
    rw [hcomap Q hJQ]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hQ (hdisj Q hQm)
  obtain ⟨p, hp⟩ : ∃ p, p = (P.map (algebraMap R (Localization.AtPrime m))).map π := ⟨_, rfl⟩
  have hpP : p.IsPrime := hp ▸ hprime P hPp hPm (hJI.trans hIP)

  have hass : p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)) := by
    refine isAssociatedPrime_iff.2 ⟨hpP, Ideal.Quotient.mk _ (π (algebraMap R (Localization.AtPrime m) r)), ?_⟩
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
      show π a • Ideal.Quotient.mk (Ideal.span (Set.range x)) (π (algebraMap R (Localization.AtPrime m) r)) =
        Ideal.Quotient.mk _ (π (a * algebraMap R (Localization.AtPrime m) r)) by rw [map_mul]; rfl,
      Ideal.Quotient.eq_zero_iff_mem, hspan, ← Ideal.mem_comap, ← Ideal.mem_comap, hcomap I hJI, hp,
      hcomap P (hJI.trans hIP)]
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl a
    rw [← IsLocalization.mk'_one (M := m.primeCompl) (Localization.AtPrime m) r, ← IsLocalization.mk'_mul,
      mul_one, IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    simp_rw [hmemP, mul_assoc]
  obtain ⟨hmin, hdimp⟩ := h B d x hxm hsum p hass
  refine ⟨⟨⟨hPp, hIP⟩, fun Q ⟨hQp, hIQ⟩ hQP => ?_⟩, fun hPeq => ?_⟩
  · have hQm : Q ≤ m := hQP.trans hPm
    have hJQ : J ≤ Q := hJI.trans hIQ
    have h1 : Ideal.span (Set.range x) ≤ (Q.map (algebraMap R (Localization.AtPrime m))).map π := by
      rw [hspan]
      exact Ideal.map_mono (Ideal.map_mono hIQ)
    have h2 : (Q.map (algebraMap R (Localization.AtPrime m))).map π ≤ p :=
      hp ▸ Ideal.map_mono (Ideal.map_mono hQP)
    have h3 := hmin.2 ⟨hprime Q hQp hQm hJQ, h1⟩ h2
    rw [← hback P hPp hPm (hJI.trans hIP), ← hback Q hQp hQm hJQ, ← hp]
    exact Ideal.comap_mono (Ideal.comap_mono h3)
  · have hpmax : p.IsMaximal := by
      have := Ideal.map_eq_top_or_isMaximal_of_surjective π hπ
        (maximalIdeal.isMaximal (Localization.AtPrime m))
      rw [hPeq, Localization.AtPrime.map_eq_maximalIdeal] at hp
      rw [← hp] at this
      exact this.resolve_left hpP.ne_top
    let := Ideal.Quotient.field p
    have h0 : ringKrullDim (B ⧸ p) = 0 := ringKrullDim_eq_zero_of_field (B ⧸ p)
    rw [hdimp, hdimx] at h0
    exact absurd h0 (by simp)

theorem SliceCMUnmixed.proof (h : CMQuotientUnmixed.Statement) : SliceCMUnmixed.Statement := by
  intro n d J L q hCM hdimB hdimS P hP hPm
  have : IsCohenMacaulayLocalRing (localRingAt J q) := hCM
  have hℓ : ∀ i, linPoly L i - C ((L *ᵥ q) i) ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := by
    intro i
    rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self]
  have hsl : sliceIdeal J L q = J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i)) := rfl
  rw [hsl] at hP hdimS ⊢
  have h1 := sliceCMUnmixed_local h (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) J
    (fun i => linPoly L i - C ((L *ᵥ q) i)) hℓ (localRingAt J q)
  have h2 := h1 (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h3 := h2 hdimB hdimS
  exact h3 P hP hPm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets StokesOffDiscriminant
open scoped ContDiff Manifold

noncomputable section

theorem StokesOffDiscriminant.proof : StokesOffDiscriminant.Statement := by
  intro n d J A P _ _ _ _ hsheet F G φ hF hG hφ hFc ⟨U, hUo, hPU, hFU⟩
  set K := closure {x | x ∈ zeroSet J ∧ F x ≠ 0} with hKdef
  have hKZ : K ⊆ zeroSet J :=
    closure_minimal (by exact fun x hx => hx.1) (SheetSumMeasurable.isClosed_zeroSet J)
  have hKU : K ⊆ Uᶜ :=
    closure_minimal (fun x hx hxU => hx.2 (hFU x ⟨hxU, hx.1⟩)) hUo.isClosed_compl
  have hKc : IsCompact K := hFc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => hx.2)
  have hwin : ∀ x : K, ∃ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (V : Set (Fin (d + 1) → ℂ))
      (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ (x : Fin n → ℂ) ∈ W ∧ DifferentiableOn ℂ s V ∧
        (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
        ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := hsheet x (hKZ hx) fun h => hKU hx (hPU h)
    exact ⟨s, window_of_sheet hs⟩
  choose s V W hVo hWo hxW hsd hsec hWs using hwin
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover W hWo fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℂ) isClosed_closure
    (fun i : t => W i.1) (fun i => hWo i.1) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  set f : t → (Fin n → ℂ) → ℝ := fun i x => ρ i x * F x with hfdef
  have hsum : ∀ x ∈ zeroSet J, F x = ∑ i, f i x := by
    intro x hxZ
    by_cases hK : x ∈ K
    · have h1 := ρ.sum_eq_one hK
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hfdef, ← Finset.sum_mul, h1, one_mul]
    · have hF0 : F x = 0 := by_contra fun h => hK (subset_closure ⟨hxZ, h⟩)
      simp [hfdef, hF0]
  have hfs : ∀ i, SmoothNear (zeroSet J) (f i) := by
    obtain ⟨O, hO, hZO, hFO⟩ := hF
    exact fun i => ⟨O, hO, hZO, (hρs i).contDiffOn.mul hFO⟩
  have hfW : ∀ i, tsupport (f i) ⊆ W i.1 := fun i => tsupport_mul_subset_left.trans (hρ i)
  have hpiece := fun i : t => window_stokes (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G φ
    (hfs i) hG hφ hFc.mul_left (hfW i)
  have hL : ∀ y, chartDens J A F (vecCons G φ) y = ∑ i, chartDens J A (f i) (vecCons G φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => f i x * ReciprocityTheory.AnForm.maDens (fun k => vecCons G φ k ∘ s') y) (by
        intro x hx s' _
        rw [hsum x hx.1, Finset.sum_mul])
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_weight_window (hsec i.1) (hWs i.1) (f i) (hfW i) _ y)
  have hR : ∀ y, chartDens J A G (vecCons F φ) y = ∑ i, chartDens J A G (vecCons (f i) φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s') y) (by
        rintro x ⟨-, rfl⟩ s' hs'
        rw [maDens_sheet_finset_sum Finset.univ F f φ hs' hsum fun i _ => hfs i, Finset.mul_sum])
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_cons_window (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G (hfW i) φ y)
  unfold chartInt
  simp only [hL, hR]
  rw [integral_finsetSum _ fun i _ => (hpiece i).2.1, integral_finsetSum _ fun i _ => (hpiece i).2.2]
  exact Finset.sum_congr rfl fun i _ => (hpiece i).1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveRegularPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveRegularPoint.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
      w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
        ∃ (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)) (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ w ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
            IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ V = g '' O

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPointOfPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelPointOfPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ∀ P : MaximalSpectrum (curveNormalisation J q),
      ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
                (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) =
            Ring.ord (pointLocalRing M.ideal w)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserLocallyInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def UniformiserLocallyInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ U)

end

end GroundTheory.Heights₂.Heights
end

