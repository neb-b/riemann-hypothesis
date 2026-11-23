module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import GroundTheory.GlobalFields.TateThesis.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRangeMulQuotientBoundedLevel
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegLoc.Scaled

theorem sum_comp_surj {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card B : ℂ) * ∑ a, G (π a) = (Fintype.card A : ℂ) * ∑ b, G b :=
  _root_.UpperTheory.Reformulated.B.Rd1.sum_comp_surj π hπ G

variable {R : Type} [CommRing R]

theorem fixed_decomp {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    (k : ℕ) (d : R) (hd : σ d = d) :
    d ∈ lev ϖ k ∨ ∃ a₀ e c, k = e + a₀ ∧ σ c = c ∧ c ∉ lev ϖ 1 ∧ d = ϖ ^ a₀ * c := by
  induction k with
  | zero => left; simp [lev]
  | succ k ih =>
    rcases ih with h | ⟨a₀, e, c, hk, hc, hc1, hdc⟩
    · obtain ⟨c, rfl⟩ := mem_lev_iff.1 h
      have hc : σ c = c := by
        apply hR.reg.pow k
        simpa [map_mul, map_pow, hR.fix_ϖ] using hd
      by_cases h1 : c ∈ lev ϖ 1
      · left
        obtain ⟨t, rfl⟩ := mem_lev_iff.1 h1
        exact mem_lev_iff.2 ⟨t, by ring⟩
      · right
        exact ⟨k, 1, c, by omega, hc, h1, rfl⟩
    · right
      exact ⟨a₀, e + 1, c, by omega, hc, hc1, hdc⟩

theorem unit_notMem {ϖ x : R} (hϖ : ¬ IsUnit ϖ) (hx : IsUnit x) : x ∉ lev ϖ 1 := by
  intro h
  obtain ⟨t, rfl⟩ := mem_lev_iff.1 h
  exact hϖ (by simpa using isUnit_of_mul_isUnit_left hx)

theorem mul_mem_lev_iff {ϖ c : R} (hreg : IsSMulRegular R ϖ) (hc : IsUnit c) (e a₀ : ℕ) (y : R) :
    ϖ ^ a₀ * c * y ∈ lev ϖ (e + a₀) ↔ y ∈ lev ϖ e := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := mem_lev_iff.1 h
    have h1 : c * y = ϖ ^ e * t := by
      apply hreg.pow a₀
      simp only [smul_eq_mul]
      rw [← mul_assoc, ht, pow_add]
      ring
    obtain ⟨v, hv⟩ := hc.exists_left_inv
    refine mem_lev_iff.2 ⟨v * t, ?_⟩
    calc y = v * (c * y) := by rw [← mul_assoc, hv, one_mul]
      _ = ϖ ^ e * (v * t) := by rw [h1]; ring
  · intro h
    obtain ⟨t, rfl⟩ := mem_lev_iff.1 h
    exact mem_lev_iff.2 ⟨c * t, by rw [pow_add]; ring⟩

theorem card_range_mul {ϖ c : R} (hreg : IsSMulRegular R ϖ) (hc : IsUnit c) (e a₀ : ℕ) :
    Nat.card (Set.range fun w : R ⧸ lev ϖ (e + a₀) =>
      w * Ideal.Quotient.mk (lev ϖ (e + a₀)) (ϖ ^ a₀ * c)) = Nat.card (R ⧸ lev ϖ e) := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk (lev ϖ e)) := Ideal.Quotient.mk_surjective
  set s := Function.surjInv hsurj with hsdef
  have hs : ∀ x, Ideal.Quotient.mk (lev ϖ e) (s x) = x := Function.surjInv_eq hsurj
  let φ : R ⧸ lev ϖ e → R ⧸ lev ϖ (e + a₀) :=
    fun x => Ideal.Quotient.mk (lev ϖ (e + a₀)) (ϖ ^ a₀ * c * s x)
  have hinj : Function.Injective φ := by
    intro x x' hxx
    have h1 : ϖ ^ a₀ * c * s x - ϖ ^ a₀ * c * s x' ∈ lev ϖ (e + a₀) :=
      Ideal.Quotient.eq.1 hxx
    rw [← mul_sub] at h1
    have h2 := (mul_mem_lev_iff hreg hc e a₀ _).1 h1
    rw [← hs x, ← hs x']
    exact Ideal.Quotient.eq.2 h2
  have hrange : (Set.range fun w : R ⧸ lev ϖ (e + a₀) =>
      w * Ideal.Quotient.mk (lev ϖ (e + a₀)) (ϖ ^ a₀ * c)) = Set.range φ := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
      refine ⟨Ideal.Quotient.mk (lev ϖ e) y, ?_⟩
      have h1 : s (Ideal.Quotient.mk (lev ϖ e) y) - y ∈ lev ϖ e :=
        Ideal.Quotient.eq.1 (hs _)
      have h2 := (mul_mem_lev_iff hreg hc e a₀ _).2 h1
      rw [mul_sub] at h2
      have h3 := Ideal.Quotient.eq.2 h2
      simp only [φ]
      rw [h3, ← map_mul, mul_comm]
    · rintro ⟨x, rfl⟩
      refine ⟨Ideal.Quotient.mk _ (s x), ?_⟩
      simp only [φ]
      rw [← map_mul, mul_comm]
  rw [hrange]
  exact Nat.card_congr (Equiv.ofInjective φ hinj).symm

theorem gauss_image_level : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → (∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j) → ∀ (k : ℕ) (d : R), σ d = d → ∃ e : ℕ, e ≤ k ∧ Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = (q ^ 2) ^ e ∧ ∀ a : R, σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ k, ψ k (Ideal.Quotient.mk (lev ϖ k) (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) = (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by
  intro R _ σ ϖ q ε hR _ ψ hψ H k d hd
  have hq : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by have := hR.one_lt; omega
    exact_mod_cast this
  have hcard : ∀ j, Fintype.card (R ⧸ lev ϖ j) = q ^ (2 * j) := fun j => by
    rw [← Nat.card_eq_fintype_card]
    exact _root_.GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε hR j
  rcases fixed_decomp hR k d hd with h0 | ⟨a₀, e, c, rfl, hc, hc1, rfl⟩
  · have hz : Ideal.Quotient.mk (lev ϖ k) d = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h0
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · have : (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = {0} := by
        ext z
        simp [hz, eq_comm]
      rw [this]
      simp
    · intro a _ _
      have hz' : Ideal.Quotient.mk (lev ϖ k) (a * d) = 0 := by rw [map_mul, hz, mul_zero]
      simp only [hz', zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
        hcard, nsmul_eq_mul, mul_one, pow_zero]
      push_cast
      rfl
  · have hcu : IsUnit c := hR.fixLocal c hc hc1
    refine ⟨e, by omega, ?_, ?_⟩
    · rw [card_range_mul hR.reg hcu e a₀, _root_.GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε hR e, pow_mul]
    · intro a ha ha1
      have hau : IsUnit a := hR.fixLocal a ha ha1
      have hac : a * c ∉ lev ϖ 1 := unit_notMem hR.notUnit (hau.mul hcu)
      have hacf : σ (a * c) = a * c := by rw [map_mul, ha, hc]
      have hle : lev ϖ (e + a₀) ≤ lev ϖ e := by
        intro x hx
        obtain ⟨t, rfl⟩ := mem_lev_iff.1 hx
        exact mem_lev_iff.2 ⟨ϖ ^ a₀ * t, by rw [pow_add]; ring⟩
      let π : (R ⧸ lev ϖ (e + a₀)) →+ (R ⧸ lev ϖ e) :=
        (Ideal.Quotient.factor hle).toAddMonoidHom
      have hπ : Function.Surjective π := by
        intro x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨Ideal.Quotient.mk _ y, rfl⟩
      let G : R ⧸ lev ϖ e → ℂ := fun v =>
        ψ e (Ideal.Quotient.mk (lev ϖ e) (a * c) * (barσ σ ϖ hR.fix_ϖ e v * v))
      have hF : ∀ w : R ⧸ lev ϖ (e + a₀),
          ψ (e + a₀) (Ideal.Quotient.mk (lev ϖ (e + a₀)) (a * (ϖ ^ a₀ * c)) *
            (barσ σ ϖ hR.fix_ϖ (e + a₀) w * w)) = G (π w) := by
        intro w
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
        have h1 := psi_pow hψ e a₀ (a * c * (σ y * y))
        change ψ (e + a₀) (Ideal.Quotient.mk _ (a * (ϖ ^ a₀ * c)) *
            (Ideal.Quotient.mk _ (σ y) * Ideal.Quotient.mk _ y)) =
          ψ e (Ideal.Quotient.mk _ (a * c) *
            (Ideal.Quotient.mk _ (σ y) * Ideal.Quotient.mk _ y))
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← h1]
        congr 2
        ring
      rw [Finset.sum_congr rfl (fun w _ => hF w)]
      have h2 := sum_comp_surj π hπ G
      have h3 : ∑ v, G v = ((ε : ℂ) * q) ^ e := H e (a * c) hacf hac
      rw [h3, hcard, hcard] at h2
      push_cast at h2
      have hqe : (q : ℂ) ^ (2 * e) ≠ 0 := pow_ne_zero _ hq
      have h4 : ∑ w, G (π w) =
          (q : ℂ) ^ (2 * (e + a₀)) * ((ε : ℂ) * q) ^ e / (q : ℂ) ^ (2 * e) := by
        rw [← h2]
        field_simp
      rw [h4, mul_pow, div_pow]
      field_simp
      ring

end GlobalTheory.CompanionTheory.SiegLoc.Scaled

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCount
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem clm_apply_eq_sum {d : ℕ} (T : V d →L[ℂ] ℂ) (v : V d) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

theorem abs_det_restrictScalars_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    |((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det| =
      ‖M.det‖ ^ 2 := by
  have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (Matrix.toEuclideanLin M : V d →ₗ[ℂ] V d)) := by
    rw [← LinearMap.det_restrictScalars]
    rfl
  rw [h1, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

theorem area_formula_neg_comb (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ)
    (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞) (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (hAU : A ⊆ U) (hA : MeasurableSet A)
    (hh : Measurable h) :
    ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) =
      ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) *
        ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a =>
          fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  classical
  let F : V d → Matrix β (Fin d) ℂ := fun z =>
    Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)
  let M : V d → Matrix (Fin d) (Fin d) ℂ := fun z => -(Matrix.of C * F z)
  let g : V d → V d := fun z => WithLp.toLp 2 (fun k => -∑ j, C k j * f j z)
  let L : V d → V d →L[ℂ] V d := fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)
  let f' : V d → V d →L[ℝ] V d := fun z => (L z).restrictScalars ℝ
  have hderC : ∀ z ∈ A, HasFDerivWithinAt g (L z) A z := by
    intro z hz
    rw [hasFDerivWithinAt_euclidean]
    intro k
    have hj : ∀ j, HasFDerivAt (f j) (fderiv ℂ (f j) z) z := fun j =>
      ((hf j).differentiableAt (hU.mem_nhds (hAU hz))).hasFDerivAt
    have hs : HasFDerivAt (fun w => -∑ j, C k j * f j w)
        (-∑ j, C k j • fderiv ℂ (f j) z) z :=
      (HasFDerivAt.fun_sum fun j _ => (hj j).const_mul (C k j)).neg
    have he : PiLp.proj 2 (fun _ : Fin d => ℂ) k ∘L L z = -∑ j, C k j • fderiv ℂ (f j) z := by
      ext v
      have hv : ∀ j, fderiv ℂ (f j) z v = ∑ a, v a * F z j a := fun j => clm_apply_eq_sum _ v
      change ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)) v).ofLp k = _
      rw [Matrix.ofLp_toEuclideanCLM]
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, hv]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [he]
    exact hs.hasFDerivWithinAt
  have hder : ∀ z ∈ A, HasFDerivWithinAt g (f' z) A z := fun z hz =>
    (hderC z hz).restrictScalars ℝ
  have hdet : ∀ z, |(f' z).det| = ‖(Matrix.of C * F z).det‖ ^ 2 := by
    intro z
    have := abs_det_restrictScalars_toEuclideanCLM (M z)
    rw [show (M z).det = (-1) ^ Fintype.card (Fin d) * (Matrix.of C * F z).det from
      Matrix.det_neg _] at this
    simpa using this
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℂ))
      (volume : Measure (Fin d → ℂ)) (volume : Measure (V d)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin d))
  have hw := (GroundTheory.Heights₂.Heights.AreaMultiplicityWeight.proof (V d) volume A g f' hA hder).2
    (fun y => h y.ofLp) (hh.comp (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm.measurable)
  have hfib : ∀ c : Fin d → ℂ, {z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0} =
      {z ∈ A | g z = WithLp.toLp 2 c} := by
    intro c
    ext z
    simp only [Set.mem_setOf_eq, g]
    refine and_congr_right fun _ => ?_
    rw [(WithLp.toLp_injective 2).eq_iff, funext_iff]
    refine forall_congr' fun k => ?_
    rw [neg_eq_iff_add_eq_zero, add_comm]
  calc ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞)
      = ∫⁻ c : Fin d → ℂ, (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
          (MeasurableEquiv.toLp 2 (Fin d → ℂ) c) := by
        refine lintegral_congr fun c => ?_
        rw [hfib c, mul_comm]
        rfl
    _ = ∫⁻ y : V d, (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp :=
        hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
          (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
    _ = ∫⁻ z in A, h (g z).ofLp * ENNReal.ofReal |(f' z).det| := hw.symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [hdet z]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPow
section
namespace GlobalTheory.CompanionTheory.KlocOp

theorem cstar_char_eq_zpow : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) →
    ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) →
    (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) →
    ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  intro φ hmul hc hn h1
  have hmem : ∀ z : ℂˣ, φ (z : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere] using hn z z.ne_zero
  let f : ℂˣ → Circle := fun z => ⟨φ (z : ℂ), hmem z⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hc.comp_continuous Units.continuous_val fun z => z.ne_zero
  have hf1 : f 1 = 1 := by
    apply Circle.ext
    have := h1 1 one_pos
    simpa [f] using this
  have hfm : ∀ a b : ℂˣ, f (a * b) = f a * f b := fun a b => by
    apply Circle.ext
    rw [Circle.coe_mul]
    change φ ((a * b : ℂˣ) : ℂ) = φ (a : ℂ) * φ (b : ℂ)
    rw [Units.val_mul]
    exact hmul a b a.ne_zero b.ne_zero
  let χ : ℂˣ →ₜ* Circle :=
    { toFun := f, map_one' := hf1, map_mul' := hfm, continuous_toFun := hfc }
  obtain ⟨⟨m, τ⟩, hp, -⟩ := GroundTheory.Global.existsUnique_complexUnits_circle χ
  have hp' : ∀ z : ℂˣ, φ (z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := hp
  have hr : ∀ r : ℝ, 0 < r → (r : ℂ) ^ ((τ : ℂ) * Complex.I) = 1 := by
    intro r hr0
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have h := hp' (Units.mk0 (r : ℂ) hne)
    rw [Units.val_mk0, h1 r hr0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_self hne, one_zpow, one_mul] at h
    exact h.symm
  refine ⟨m, fun z hz => ?_⟩
  have h := hp' (Units.mk0 z hz)
  rw [Units.val_mk0, hr _ (norm_pos_iff.mpr hz), mul_one] at h
  exact h

end GlobalTheory.CompanionTheory.KlocOp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeights
section
open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem sec_inv {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {w : W} (hP : IsPar Γ K P c)
    (law : ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w) :
    ∀ γ ∈ Γ, γ ∈ P → ∀ x, sec K P c ρ (γ * x) w = sec K P c ρ x w := by
  intro γ hγ hγP x
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have h1 := law (γ * p) (P.mul_mem hγP hp) ⟨k, hk⟩
  have h2 := law p hp ⟨k, hk⟩
  simp only at h1 h2
  rw [← mul_assoc, h1, h2, hP.ch.mul γ hγP p hp, hP.ch.rat γ hγ hγP, one_mul]

theorem cross (hSec : SecLaw) (hHt : HtLip) (hSt : PiLocalization₂) (hWL : WallLaw) : Cross := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ Q P P' c η η' β ξ L R D Op H Ω hPQ hP'Q hP hP' hη hη' hβ hξ hW hΩ hx
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have parRes : ∀ (P : Subgroup G), IsPar Γ K P c → IsPar (Γ ⊓ Q) K P c := fun _ h =>
    ⟨h.closed, h.iwa, ⟨h.ch.mul, h.ch.norm, fun γ hγ hp => h.ch.rat γ hγ.1 hp, h.ch.cont⟩⟩
  have htRes : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → IsHt (Γ ⊓ Q) K P f := fun _ _ h =>
    ⟨h.left, h.right, fun γ hγ hp => h.rat γ hγ.1 hp, h.cont⟩
  obtain ⟨-, -, hbound⟩ := hWL G W K ρ hK hρ (Γ ⊓ Q) P P' c η η' β L R D Op H (parRes P hP) (parRes P' hP')
    (htRes P η hη) (htRes P' η' hη') (htRes P' β hβ) hW
  have hξinv : ∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x := by
    intro γ h1 h2 x
    rw [hξ.left γ h2, hξ.rat γ h1 h2, zero_add]
  have htinv : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro P f hf γ h1 h2 x
    rw [hf.left γ h2, hf.rat γ h1 h2, zero_add]
  have iwaQ : Iwa Q K := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hP.iwa g
    exact ⟨p, hPQ hp, k, hk, e⟩
  have mξ := hHt G Γ K Q ξ hK iwaQ hξ
  have mη := hHt G Γ K P η hK hP.iwa hη
  have mη' := hHt G Γ K P' η' hK hP'.iwa hη'
  have mβ := hHt G Γ K P' β hK hP'.iwa hβ
  let t : Cos (Γ ⊓ Q) Γ → ℂ × ℂ → G → (L →L[ℂ] W) := fun r l g =>
    Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)
  have hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g := by
    intro r g p v
    have h1 : Differentiable ℂ fun τ : ℂ => H (p + τ • v).1 (rep r * g) :=
      (hW.hol (rep r * g)).comp (by fun_prop)
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).2 * ξ (rep r * g)) := by fun_prop
    exact h2.smul h1
  have hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × G => t r y.1 y.2 := by
    intro r
    have h0 : Continuous fun y : (ℂ × ℂ) × G => rep r * y.2 := by fun_prop
    have h1 : Continuous fun y : (ℂ × ℂ) × G => H y.1.1 (rep r * y.2) :=
      hW.cont.comp (continuous_fst.fst.prodMk h0)
    have h2 : Continuous fun y : (ℂ × ℂ) × G => ξ (rep r * y.2) := hξ.cont.comp h0
    have h3 : Continuous fun y : (ℂ × ℂ) × G => Complex.exp (y.1.2 * ξ (rep r * y.2)) :=
      Complex.continuous_exp.comp ((continuous_fst.snd).mul (Complex.continuous_ofReal.comp h2))
    exact h3.smul h1
  have hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : Cos (Γ ⊓ Q) Γ → ℝ, Summable u ∧
      ∀ l ∈ tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r := by
    intro x hxΩ g
    obtain ⟨a, b, ε, hε, hRa, hbR, hbx, hxa, hconv⟩ := hx x hxΩ
    obtain ⟨M, hM⟩ := hbound a b hRa hbR
    have inv₁ : ∀ γ ∈ Γ, γ ∈ P → ∀ x, (fun x => a * η x) (γ * x) = (fun x => a * η x) x := by
      intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    have inv₂ : ∀ γ ∈ Γ, γ ∈ P' → ∀ x, (fun x => β x - b * η' x) (γ * x) = (fun x => β x - b * η' x) x := by
      intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    have m₁ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |a * η (g * u) - a * η g| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη C hC
      refine ⟨|a| * A, fun g u hu => ?_⟩
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg a)
    have m₂ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C,
        |(β (g * u) - b * η' (g * u)) - (β g - b * η' g)| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη' C hC
      obtain ⟨B, hB⟩ := mβ C hC
      refine ⟨B + |b| * A, fun g u hu => ?_⟩
      have e : (β (g * u) - b * η' (g * u)) - (β g - b * η' g) =
          (β (g * u) - β g) - b * (η' (g * u) - η' g) := by ring
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hB g u hu) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg b)
    have hl : |x.2 - ε - x.2| ≤ ε := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]
    have hr : |x.2 + ε - x.2| ≤ ε := by rw [add_sub_cancel_left, abs_of_pos hε]
    obtain ⟨U, hU, u, hu, hb⟩ := _root_.GlobalTheory.CompanionTheory.EisCross.dom G (L →L[ℂ] W) Γ (Γ ⊓ Q) P P' ξ (fun x => a * η x) (fun x => β x - b * η' x) H a b
      (x.2 - ε) (x.2 + ε) M mξ m₁ m₂ (hW.convR a hRa) (hW.convL b hbR) hM
      (_root_.GlobalTheory.CompanionTheory.RgEis.cross_stage_pos hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hl).1)
      (_root_.GlobalTheory.CompanionTheory.RgEis.cross_stage_pos hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hr).1)
      (_root_.GlobalTheory.CompanionTheory.RgEis.cross_stage_pos hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hl).2)
      (_root_.GlobalTheory.CompanionTheory.RgEis.cross_stage_pos hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hr).2) g
    refine ⟨Set.Icc b a ×ˢ Set.Icc (x.2 - ε) (x.2 + ε),
      prod_mem_nhds (Icc_mem_nhds hbx hxa) (Icc_mem_nhds (by linarith) (by linarith)), U, hU, u, hu, ?_⟩
    intro l hl g' hg' r
    obtain ⟨h1, h2⟩ := hl
    exact hb l h1.1 h1.2 h2.1 h2.2 g' hg' r
  obtain ⟨hTG, hsum⟩ := GlobalTheory.T.holomorphic_series_uniform_tube _ _ _ t Ω hhol hcont hdom
  have key : ∀ l ∈ tube Ω, ∀ g (w : L), outer Γ (Γ ⊓ Q) ξ H l g w =
      ∑' r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w := by
    intro l hl g w
    have hs : Summable fun r => t r l g := (hsum l hl g).of_norm
    exact (ContinuousLinearMap.apply ℂ W w).map_tsum hs
  obtain ⟨law, -, Ms, hMs⟩ := hSec G W K ρ hK hρ Γ P c hP
  obtain ⟨law', -, Ms', hMs'⟩ := hSec G W K ρ hK hρ Γ P' c hP'
  refine ⟨hTG, hsum, ?_, ?_⟩
  · intro l hl hRl hconv g w
    have hw : (w : W) ∈ secSp K P c ρ := hW.le w.2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        D l.1 • (Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P c ρ (fun x => l.1 * η x) (rep r * g) w) := by
      intro r
      rw [hW.eqR l.1 hRl, smul_comm]
    simp_rw [e]
    rw [tsum_const_smul'']
    congr 1
    refine _root_.GlobalTheory.CompanionTheory.RgEisCross.stage_eis hSt G W Γ K Q P c ρ ξ (fun x => l.1.re * η x + l.2.re * ξ x) (fun x => l.1 * η x) l.2 w
      (Ms * ‖(w : W)‖) hPQ hξinv ?_ (sec_inv hP (law w hw)) (fun x => hMs x w) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    · intro x
      simp
  · intro l hl hRl hconv g w
    have hw : ((Op l.1 w : secSp K P' c ρ) : W) ∈ secSp K P' c ρ := (Op l.1 w).2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P' c ρ (fun x => β x - l.1 * η' x) (rep r * g) (Op l.1 w) := by
      intro r
      rw [hW.eqL l.1 hRl]
    simp_rw [e]
    refine _root_.GlobalTheory.CompanionTheory.RgEisCross.stage_eis hSt G W Γ K Q P' c ρ ξ (fun x => β x - l.1.re * η' x + l.2.re * ξ x)
      (fun x => (β x : ℂ) - l.1 * η' x) l.2 _ (Ms' * ‖((Op l.1 w : secSp K P' c ρ) : W)‖) hP'Q hξinv ?_
      (sec_inv hP' (law' _ hw)) (fun x => hMs' x _) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    · intro x
      simp

end GlobalTheory.CompanionTheory.RgEisCross
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialFourierIntegralBoundStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_fourier_integral_bound : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ), 0 < ε → Continuous φ → (∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))) → Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧ ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le | exact GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.integrable_and_norm_integral_le <;> assumption)
end

