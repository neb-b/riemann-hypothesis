module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAveragedMinorOperatorExpPosBoundAnalytic
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

private lemma posDef_inv_toMK_mul_mul_toMK {n : ℕ} {ε : Fin n → Bool} (k : KG ε)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : ((toMK k)⁻¹ * x * toMK k).PosDef := by
  have hK : toMK k ∈ Kset ε := (mem_KG ε _).1 k.2
  have hU : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hK.1
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  rw [hinv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro v₁ v₂ hv
  have := congrArg (fun v => (toMK k)ᴴ *ᵥ v) hv
  simpa [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU] using this

private lemma norm_inner_ps_exp_le_decHS_mul {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    {w : W} (hlam : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) {h : ℝ}
    (hgap : GapAtLeast ε lam h) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (u y : W) :
    ‖⟪y, ps ε lam τ w (NormedSpace.exp X) u⟫_ℂ‖ ≤
      decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖y‖ := by
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  have hint : ∀ v : W, Integrable (fun k : KG ε => ‖⟪v, τ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε) := by
    intro v
    by_contra hn
    have hs := GlobalTheory.PsiBound.schur_norm hτ v
    rw [integral_undef hn, mul_zero] at hs
    have hv : v = 0 := by
      have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.1 this
    subst hv
    simp at hn
  have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
  rw [GlobalTheory.PsiBound.ps_entry hτ lam hP u y]
  refine GlobalTheory.PsiBound.weighted_bound (muK ε) (Module.finrank ℂ W) _ _ _ _ _ _ hM (norm_nonneg u)
    (norm_nonneg y) (fun k => GlobalTheory.PsiBound.norm_Phi_le hlam hgap hX ((mem_KG ε _).1 k.2))
    (hint y) ?_ (GlobalTheory.PsiBound.schur_norm hτ y) ?_
  · simpa only [norm_inner_symm] using hint u
  · simpa only [norm_inner_symm] using GlobalTheory.PsiBound.schur_norm hτ u

theorem ps_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  intro n ε lam W _ _ τ w hlam hτ h hgap X hX
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  refine ⟨fun x => ?_, ?_, ?_⟩
  ·
    rw [GlobalTheory.PsiBound.ps_entry hτ lam hP x x]
    set F : KG ε → ℂ := fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) *
      (⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) with hFdef
    have hF : ∀ k, 0 ≤ F k := by
      intro k
      have hphi : 0 < Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) :=
        (phiPos n lam _ (posDef_inv_toMK_mul_mul_toMK k hP)).2.1
      have hsq : 0 ≤ ⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ := by
        rw [← inner_conj_symm x (τ (toMK k) w), mul_comm, Complex.mul_conj]
        exact Complex.zero_le_real.2 (Complex.normSq_nonneg _)
      exact mul_nonneg hphi.le hsq
    have hre : ∀ k, F k = ((F k).re : ℂ) := fun k =>
      Complex.ext rfl (by simpa using ((Complex.le_def.1 (hF k)).2).symm)
    have hI : ∫ k, F k ∂(muK ε) = ((∫ k, (F k).re ∂(muK ε) : ℝ) : ℂ) := by
      rw [integral_congr_ae (Eventually.of_forall hre)]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [hI]
    refine mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.2 (integral_nonneg fun k => ?_))
    exact (Complex.le_def.1 (hF k)).1
  ·
    have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun u => ?_
    set T := ps ε lam τ w (NormedSpace.exp X)
    rcases eq_or_ne (T u) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    have hb := norm_inner_ps_exp_le_decHS_mul hlam hτ hgap hX u (T u)
    rw [inner_self_eq_norm_sq_to_K] at hb
    simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hb
    have hpos : 0 < ‖T u‖ := norm_pos_iff.2 h0
    nlinarith
  ·
    obtain ⟨hopen, hpos, hdiff, -⟩ := psBasic n ε lam W τ w hlam hτ
    haveI : FiniteDimensional ℂ W := hτ.1
    haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
    let e : (Fin n → Fin n → ℂ) ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv
    have hg : AnalyticAt ℂ (fun z : Fin n → Fin n → ℂ => ps ε lam τ w (Matrix.of z))
        (e.symm (NormedSpace.exp X)) :=
      GlobalTheory.SCV.analyticAt_of_differentiableOn hdiff
        (hopen.mem_nhds (show Matrix.of _ ∈ U1 ε from hpos _ hP))
    have he : AnalyticAt ℂ (⇑e.symm) (NormedSpace.exp X) :=
      e.symm.toContinuousLinearMap.analyticAt _
    exact hg.comp he

end GlobalTheory.SphJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
section
noncomputable section

open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

namespace GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {q n : ℕ}

theorem v_det_mat (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) : Valued.v (mat g).det = 1 := by
  have h : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have h1 := congrArg (fun M => Valued.v (det M)) h
  have hJ : IsInt (antiJ L n) := fun i j => by
    unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  simp only [det_mul, map_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hσ,
    v_det_eq_one hJ hJ GlobalTheory.UnitarySwap.antiJ_mul_self, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, h1])

theorem secVal_pow {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ) (k : ℕ) :
    secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = varX q n (χ ϖ) s ^ k := by
  have h := P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val, varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem section_eq (hC : Completion) {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ}
    {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n χ s Φ) (g : GU σ n) {l : ℕ} (h : HasLen (mat g) l) :
    Φ (io1 σ n g) = varX q n (χ ϖ) s ^ l := by
  obtain ⟨U, V, C, hfr, hdet⟩ := h
  obtain ⟨k, hk, hk', hx⟩ := hC L ϖ σ q n hU g U V C hfr
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hK : (⟨k, hk⟩ : GD σ n) ∈ KD σ n := ⟨hk, hk'⟩
  have hp : ∀ x : Fin n → L, ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv ((mat g * C) *ᵥ x) ((mat g * C) *ᵥ x) := fun x => by
    change (blkMat finSumFinEquiv (mat g) 1 * k.1) *ᵥ _ = _
    rw [← mulVec_mulVec, hx, blkMat_mulVec, mulVec_mulVec, one_mulVec]
  have hP : io1 σ n g * ⟨k, hk⟩ ∈ PD σ n := mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
    rw [hp, pairVec_mem_diagSub])
  have hlev : leviMat finSumFinEquiv ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 = mat g * C := by
    refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
    have := congrFun ((mem_siegelOf.1 hP).mulVec_diag (Pi.single j 1)) (finSumFinEquiv (.inl i))
    rw [hp, pairVec_inl, pairVec_inl] at this
    exact this.symm
  have h1 := hΦ ⟨_, hP⟩ _ (inv_mem hK)
  rw [mul_inv_cancel_right] at h1
  have h2 : Valued.v ((aD σ n ⟨_, hP⟩ * (ϖ ^ l)⁻¹ : Lˣ) : L) = 1 := by
    have hϖ : Valued.v (ϖ : L) = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
    rw [Units.val_mul, val_aOf, hlev, det_mul, map_mul, map_mul, v_det_mat hU.2.1, hdet, one_mul,
      Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow, hϖ, ← WithZero.exp_nsmul,
      ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  rw [h1, ← inv_mul_cancel_right (aD σ n ⟨_, hP⟩) (ϖ ^ l), secVal_mul hq, secVal_unit q hχ _ h2, one_mul, secVal_pow hU]

theorem closedForm_eq {q : ℕ} (hq : q ≠ 0) (n m : ℕ) (ε s : ℂ) (α : Fin (n / 2) → ℂˣ) (hε : ε = (-1) ^ m) :
    closedForm q n (varX q n ε s) (varY q ε s) α = stdL q n α ε (s + 1 / 2) / dFac q n m s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have h1 : ε * ((q ^ 2 : ℕ) : ℂ) ^ (-(s + 1 / 2)) = varY q ε s := by
    rw [varY, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    congr 2
    push_cast
    ring
  have h2 : (dFac q n m s)⁻¹ = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * varX q n ε s) := by
    rw [dFac, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [etaL, inv_inv, varX, hε, show -(2 * s + n - j) = (j : ℂ) + -(2 * s + n) by ring, Complex.cpow_add _ _ hq0,
      Complex.cpow_natCast, neg_pow (q : ℂ), pow_add]
    ring
  rw [div_eq_mul_inv, h2, stdL, h1, closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm (varY q ε s)]
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

theorem unramDoublingInert : UnramDoublingInert := by
  intro L _ _ _ ϖ σ q n hU _ _ μ _ hμ χ hχ s Φ hΦ α w hw
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hF : FracExists := _root_.GlobalTheory.InertZeta.fracExists_of_smith _root_.GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued
  have hsec : (fun g => Φ (io1 σ n g) * w g) = fun g => varX q n (χ ϖ) s ^ len (mat g) * w g := funext fun g => by
    rw [section_eq _root_.GlobalTheory.FrameCompletion.completion hU hχ hΦ g (hF L ϖ n hU.2.2.2.1 _ (det_mat_ne_zero g))]
  have hint : ∀ Z, HasSum (fun x : GU σ n ⧸ KU σ n => varX q n (χ ϖ) s ^ len (mat x.out) * w x.out) Z →
      Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = Z := fun Z hZ => by
    rw [hsec]
    refine _root_.GlobalTheory.InertZeta.cosetIntegral_holds _ μ (KU σ n) (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1 hμ _ Z (fun g k hk => ?_) hZ
    have h1 := hw.1 1 ⟨k, hk⟩ g
    have h2 := len_mat_mul (one_mem _) hk g
    simp only [OneMemClass.coe_one, one_mul] at h1 h2
    rw [h1, h2]
  refine ⟨fun hD => ?_, fun hn => hint 1 (hasSum_small _root_.GlobalTheory.InertZeta.smallRank hU hn (fun g => varX q n (χ ϖ) s ^ len (mat g) * w g)
    fun k hk => ?_)⟩
  · obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ))
      fun i => (α i).ne_zero
    have h2 := hasSum_spherical hF (T.leviRadicalProductLength_of_lattice_steps _root_.GlobalTheory.InertZeta.addVec _root_.GlobalTheory.InertZeta.dual_inter_eq_sum _root_.GlobalTheory.InertZeta.RowSpan.spanEq_holds _root_.GlobalTheory.InertZeta.HeisCoord.Heisenberg₂)
      (_root_.GlobalTheory.InertZeta.count_of_heis _root_.GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ (_root_.GlobalTheory.InertZeta.latIndex_of_smith _root_.GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued) _root_.GlobalTheory.InertZeta.traceIndex) (_root_.GlobalTheory.InertZeta.smallCorner_of_heis_dual _root_.GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ _root_.GlobalTheory.InertZeta.dual_inter_eq_sum) _root_.GlobalTheory.InertZeta.genFun_holds (_root_.GlobalTheory.InertZeta.cosetSurj_of_leviExists _root_.GlobalTheory.InertZeta.leviExists)
      _root_.GlobalTheory.InertZeta.cosetInj _root_.GlobalTheory.InertZeta.leviExists (T.sphericalInductionTransitivity_of_leviExists _root_.GlobalTheory.InertZeta.leviExists) _root_.GlobalTheory.InertZeta.smallRank _root_.GlobalTheory.InertZeta.step hU (n / 2) n (by omega) (by omega)
      (fun i => (α i : ℂ)) (varX q n (χ ϖ) s) (varY q (χ ϖ) s) φ (fun i => (α i).ne_zero) (by
        rw [varX, varY, neg_add, neg_add, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, Complex.cpow_neg_one,
          Complex.cpow_neg _ (n : ℂ), Complex.cpow_natCast]
        field_simp) hD.1 hD.2 hφ h1
    have h3 := hint _ (_root_.GlobalTheory.InertZeta.dosetSwap _ (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) (fun g => varX q n (χ ϖ) s ^ len (mat g)) w φ _
      (fun a b g => by simp only [len_mat_mul a.2 b.2]) hw.1 (fun g => by
        rw [hw.2.2 _ (Final.DosetIndMem _ _ ℂ g), Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
          (fun i => (α i).ne_zero) _ (Final.DosetIndMem _ _ ℂ g) φ hφ, Pi.smul_apply, h1, smul_eq_mul, mul_one]) h2)
    exact ⟨h3.1, h3.2, fun m hm => h3.2.trans (closedForm_eq hq n m _ s α hm)⟩
  · have h1 := hw.1 1 ⟨k, hk⟩ 1
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [len_of_mem hk, h1, hw.2.1, pow_zero, mul_one]

end GlobalTheory.InertZeta

end
end

