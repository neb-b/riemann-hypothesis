module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0139
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0081

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameBallCoordinate
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section Pure

variable {j j' : ℕ}

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply, fromBlocks_one]

theorem sgUInv_mul {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    (sgI j j' * uᴴ * sgI j j') * u = 1 := by
  have h : uᴴ * sgI j j' * u = sgI j j' := hu
  calc (sgI j j' * uᴴ * sgI j j') * u = sgI j j' * (uᴴ * sgI j j' * u) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, sgI_mul_self]

theorem mul_sgUInv {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    u * (sgI j j' * uᴴ * sgI j j') = 1 :=
  mul_eq_one_comm.1 (sgUInv_mul hu)

theorem sgUInv_mulVec (u : Matrix (Sg j j') (Sg j j') ℂ) (x : Fin j' → ℂ) :
    (sgI j j' * uᴴ * sgI j j') *ᵥ Sum.elim 0 x =
      Sum.elim (-(u.toBlocks₂₁ᴴ *ᵥ x)) (u.toBlocks₂₂ᴴ *ᵥ x) := by
  conv_lhs => rw [← fromBlocks_toBlocks u]
  simp only [sgI, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_mulVec]
  ext (i | i) <;> simp [Matrix.neg_mulVec, Matrix.mulVec_neg]

theorem mulVec_elim_zero (u : Matrix (Sg j j') (Sg j j') ℂ) (w : Fin j → ℂ) :
    u *ᵥ Sum.elim w 0 = Sum.elim (u.toBlocks₁₁ *ᵥ w) (u.toBlocks₂₁ *ᵥ w) := by
  conv_lhs => rw [← fromBlocks_toBlocks u]
  simp only [fromBlocks_mulVec]
  ext (i | i) <;> simp

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) :
    moebW u 0 = u.toBlocks₂₁ * (u.toBlocks₁₁)⁻¹ := by
  simp [moebW]

theorem star_conj_single (d : Matrix (Fin j') (Fin j') ℂ) (a b : Fin j') :
    star (dᴴ *ᵥ Pi.single a 1) ⬝ᵥ (dᴴ *ᵥ Pi.single b 1) = (d * dᴴ) a b := by
  simp [Matrix.mul_apply, dotProduct, Matrix.mulVec_single_one, Matrix.conjTranspose_apply]

end Pure

section Point

theorem point_graph_gram (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) (W : Matrix (Fin j') (Fin j) ℂ)
    (H1 : ∀ u : Matrix (Sg j j') (Sg j j') ℂ, IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef)
    (H2 : ∀ x y : Fin j' → ℂ, R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y))
    (hA : C.IsAdapted R A) (h0 : (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j')
    (hW : W = moebW (C.cinv (A₀ τ) τ * A τ) 0) :
    (∀ v : Fin j → ℂ, C.pPart R τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) ∧ R.gram (fun b : Fin j' => C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))) * (1 - W * Wᴴ) = ((2 * C.c : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) ∧ (1 - W * Wᴴ).PosDef := by
  obtain ⟨hc1, hc2, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts E Ψ j j' n g Λ F C τ (A₀ τ) h0
  generalize C.cinv (A₀ τ) τ = c at hc1 hc2 hW
  have hsgr : cᴴ * sgI j j' * c = C.sgr τ := by
    have : cᴴ * ((A₀ τ)ᴴ * C.sgr τ * A₀ τ) * c = (A₀ τ * c)ᴴ * C.sgr τ * (A₀ τ * c) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [h0, hc2] at this
    simpa using this
  have hu : IsSgU (c * A τ) := by
    have h : (c * A τ)ᴴ * sgI j j' * (c * A τ) = (A τ)ᴴ * (cᴴ * sgI j j' * c) * A τ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    show (c * A τ)ᴴ * sgI j j' * (c * A τ) = sgI j j'
    rw [h, hsgr, hA.unit τ]
  have hAu : A₀ τ * (c * A τ) = A τ := by
    rw [← Matrix.mul_assoc, hc2, Matrix.one_mul]
  generalize hue : c * A τ = u at hu hAu hW
  obtain ⟨ha, hd, hinv, hpos⟩ := H1 u hu
  rw [← hW] at hinv hpos
  refine ⟨fun v => ?_, ?_, hpos⟩
  · have hWv : Sum.elim v (W *ᵥ v) = u *ᵥ Sum.elim ((u.toBlocks₁₁)⁻¹ *ᵥ v) 0 := by
      rw [mulVec_elim_zero, hW, moebW_zero, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ ha, Matrix.one_mulVec]
    rw [hWv, Matrix.mulVec_mulVec, hAu]
    exact hA.ker τ _
  · have hp : ∀ x : Fin j' → ℂ, C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 x) =
        C.pPart R τ (A τ *ᵥ Sum.elim 0 (u.toBlocks₂₂ᴴ *ᵥ x)) := by
      intro x
      have hA₀ : A₀ τ = A τ * (sgI j j' * uᴴ * sgI j j') := by
        rw [← hAu, Matrix.mul_assoc, mul_sgUInv hu, Matrix.mul_one]
      have hs : (Sum.elim (-(u.toBlocks₂₁ᴴ *ᵥ x)) (u.toBlocks₂₂ᴴ *ᵥ x) : Sg j j' → ℂ) =
          Sum.elim (-(u.toBlocks₂₁ᴴ *ᵥ x)) 0 + Sum.elim (0 : Fin j → ℂ) (u.toBlocks₂₂ᴴ *ᵥ x) := by
        ext (i | i) <;> simp
      conv_lhs => rw [hA₀, ← Matrix.mulVec_mulVec, sgUInv_mulVec, hs, Matrix.mulVec_add]
      rw [pPart_add, hA.ker τ, zero_add]
    have hg : R.gram (fun b : Fin j' => C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))) =
        ((2 * C.c : ℝ) : ℂ) • (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) := by
      ext a b
      simp only [RiemLat.gram, Matrix.of_apply, hp, H2, star_conj_single, Matrix.smul_apply, smul_eq_mul]
    have hinv' : (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) * (1 - W * Wᴴ) = 1 := mul_eq_one_comm.1 hinv
    rw [hg, Matrix.smul_mul, hinv']

end Point

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameDeterminesLatticeStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_determines_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → R'.form = F.form → C.IsAdapted R A → C.IsAdapted R' A → R.EqvBy R' 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameHermitianProduct
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)


open Classical in
theorem perExt_I_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.perExt R (Pi.single τ (Complex.I • y)) = Complex.I • C.perExt R (Pi.single τ y) := by
  ext k
  have hk := congrFun h k
  simp only [LatEmb.pBar, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at hk ⊢
  linear_combination (-2 * Complex.I) * hk +
    ((C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I


open Classical in
theorem pPart_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.pPart R τ y = C.perExt R (Pi.single τ y) := by
  have h1 := perExt_I_of_pBar C R h
  ext k
  simp only [LatEmb.pPart, h1, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (-(1 / 2 : ℂ) * (C.perExt R (Pi.single τ y)) k) * Complex.I_mul_I


open Classical in
theorem Fm_single (τ : Ψ) (y x : Fin (j + j') → ℂ) :
    C.Fm (Pi.single τ y) (Pi.single τ x) =
      2 * (embOf (F.σ τ) C.xi * (star x ⬝ᵥ (C.gr τ *ᵥ y))).re := by
  unfold LatEmb.Fm
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem xi_block {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (x y : Fin j' → ℂ) :
    embOf (F.σ τ) C.xi * (star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.gr τ *ᵥ (A τ *ᵥ Sum.elim 0 y))) =
      -(Complex.I * (C.c : ℂ) * (star x ⬝ᵥ y)) := by
  have hs : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) = -(star x ⬝ᵥ y) := by
    have h1 : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) =
        star (Sum.elim 0 x : Sg j j' → ℂ) ⬝ᵥ (((A τ)ᴴ * C.sgr τ * A τ) *ᵥ Sum.elim 0 y) := by
      rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [Matrix.dotProduct_mulVec]
    rw [h1, hA.unit τ]
    simp only [sgI, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec]
  have hg : C.sgr τ = ((C.eps τ : ℝ) : ℂ) • C.gr τ := rfl
  rw [hg, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hs
  rw [C.xi_eq τ]
  push_cast
  linear_combination (Complex.I * (C.c : ℂ)) * hs

theorem gram_last_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), (∀ y y', (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y') → C.IsAdapted R A → ∀ (τ : Ψ) (x y : Fin j' → ℂ), R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y) := by
  classical
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R A hF hA τ x y
  have hx := pPart_of_pBar C R (hA.kerBar τ x)
  have hy := pPart_of_pBar C R (hA.kerBar τ y)
  have hiy := perExt_I_of_pBar C R (hA.kerBar τ y)
  have h1 := hF (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  have h2 := hF (Pi.single τ (Complex.I • (A τ *ᵥ Sum.elim 0 y))) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  rw [Fm_single, xi_block C R hA] at h1
  rw [Fm_single, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_left_comm, xi_block C R hA, hiy,
    smul_dotProduct, smul_eq_mul] at h2
  rw [RiemLat.ip, hx, hy]
  set H := C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) ⬝ᵥ
    R.Hm *ᵥ star (C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 x))) with hH
  set w := star x ⬝ᵥ y with hw
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZero
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex

theorem re_star_dotProduct_self {κ : Type} [Fintype κ] (w : κ → ℂ) :
    (star w ⬝ᵥ w).re = ‖WithLp.toLp 2 w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (star (w i) * w i).re = Complex.normSq (w i) := by
    simp [Complex.normSq_apply]
  rw [this, Complex.normSq_eq_norm_sq]

theorem re_form_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) (v : κ' → ℂ) :
    (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re = ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
  have h : star v ⬝ᵥ ((Zᴴ * Z) *ᵥ v) = star (Z *ᵥ v) ⬝ᵥ (Z *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, h, Complex.sub_re,
    re_star_dotProduct_self, re_star_dotProduct_self]

theorem posDef_iff {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) :
    (1 - Zᴴ * Z).PosDef ↔ ∀ v : κ' → ℂ, v ≠ 0 → ‖WithLp.toLp 2 (Z *ᵥ v)‖ < ‖WithLp.toLp 2 v‖ := by
  have hH : (1 - Zᴴ * Z).IsHermitian :=
    (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)
  constructor
  · intro h v hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hv)).1
    have h0 : (0 : ℝ) < ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
      rw [← re_form_eq]
      simpa using hpos
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (sub_pos.mp h0)
  · intro h
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hH, fun v hv => ?_⟩
    have hre : 0 < (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re := by
      rw [re_form_eq, sub_pos]
      exact pow_lt_pow_left₀ (h v hv) (norm_nonneg _) two_ne_zero
    have hstar : star (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)) = star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v) := by
      conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
    have him : (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem ballMat_combo {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (s t : Fin n → ℂ) (a b : ℝ) (τ : Ψ) :
    ballMat q (a • s + b • t) τ = a • ballMat q s τ + b • ballMat q t τ := by
  ext x y
  simp [ballMat]

theorem convex_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) [Fintype Ψ] :
    Convex ℝ (ballDom q) := by
  intro s hs t ht a b ha hb hab τ
  refine (posDef_iff _).mpr fun v hv => ?_
  have h1 := (posDef_iff _).mp (hs τ) v hv
  have h2 := (posDef_iff _).mp (ht τ) v hv
  have hc := convex_ball (0 : EuclideanSpace ℂ (Fin j)) ‖WithLp.toLp 2 v‖
    (x := WithLp.toLp 2 (ballMat q s τ *ᵥ v)) (y := WithLp.toLp 2 (ballMat q t τ *ᵥ v))
    (by simpa using h1) (by simpa using h2) ha hb hab
  have he : WithLp.toLp 2 (ballMat q (a • s + b • t) τ *ᵥ v) =
      a • WithLp.toLp 2 (ballMat q s τ *ᵥ v) + b • WithLp.toLp 2 (ballMat q t τ *ᵥ v) := by
    rw [ballMat_combo, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    rfl
  rw [he]
  simpa using hc

theorem zero_mem_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have h : ballMat q (0 : Fin n → ℂ) τ = 0 := by
    ext x y
    simp [ballMat]
  rw [h]
  simpa using (Matrix.PosDef.one : (1 : Matrix (Fin j') (Fin j') ℂ).PosDef)

theorem ballDom_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n),
    IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q :=
  fun _ _ _ _ _ q => ⟨BallInverse.isOpen_ballDom q, convex_ballDom q, zero_mem_ballDom q⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuousStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_zero_continuous : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, Continuous fun x => f x τ) → (∀ x τ, IsSgU (f x τ)) → Continuous fun x => moebBall q (f x) 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallPotentialFormula
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem ballPot_ballPt_eq : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ), ballPot q (ballPt q W) = -∑ τ, Real.log (1 - W τ * (W τ)ᴴ).det.re := by
  intro Ψ _ j j' n q W
  unfold ballPot
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hm : ballMat q (ballPt q W) τ = (W τ)ᵀ := by
    ext a b
    simp [ballMat, ballPt]
  have key : 1 - ((W τ)ᵀ)ᴴ * (W τ)ᵀ = (starRingEnd ℂ).mapMatrix (1 - W τ * (W τ)ᴴ) := by
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sub_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, map_sub, map_sum, map_mul]
    congr 1
    · by_cases h : a = b <;> simp [Matrix.one_apply, h]
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp
  rw [hm, key, ← RingHom.map_det, Complex.conj_re]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterionStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_embeddings_criterion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → ∀ i k : Ix Ψ j j', (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingInverseRootImaginaryStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_inverse_root_imaginary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (s : 𝓞 E →+* ℂ) (m : ℕ), m ≠ 0 → ∃ ε : ℝ, ε ^ 2 = 1 ∧ embOf s (((m : E) * (H.rt : E))⁻¹) = Complex.I * (((1 / ((m : ℝ) * Real.sqrt H.d)) * ε : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAdaptedFrameBis
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

section Lin

variable {a b : ℕ}

end Lin

section GS

end GS

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Emb

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)


theorem exists_adapted_at (hF : R.form = F.form) (hS : R.HasSig F.σ j j') (τ : Ψ) :
    ∃ A : Matrix (Fin (j + j')) (Sg j j') ℂ, Aᴴ * C.sgr τ * A = sgI j j' ∧
      (∀ v : Fin j → ℂ, C.pPart R τ (A *ᵥ Sum.elim v 0) = 0) ∧
      (∀ v : Fin j' → ℂ, C.pBar R τ (A *ᵥ Sum.elim 0 v) = 0) :=
  by apply _root_.UpperTheory.Reformulated.B.Gwb8.exists_adapted_at <;> assumption

end Lat

theorem exists_isAdapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F)
    (R : RiemLat E g Λ), R.form = F.form → R.HasSig F.σ j j' → ∃ A, C.IsAdapted R A := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R hF hS
  choose A h1 h2 h3 using exists_adapted_at C R hF hS
  exact ⟨A, ⟨h1, h2, h3⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted
end
end

