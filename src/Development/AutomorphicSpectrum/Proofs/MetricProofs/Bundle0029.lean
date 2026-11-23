module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SubframeDetLogGrowth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp [RiemLat.ip, star_add, Matrix.mulVec_add, dotProduct_add]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = star c * R.ip x y := by
  simp [RiemLat.ip, star_smul, Matrix.mulVec_smul, dotProduct_smul]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem real_smul_eq' (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x := by
  ext i
  simp

theorem ip_period_im (R : RiemLat E g Λ) (x y : Λ) : (R.ip (R.P x) (R.P y)).im = R.form y x :=
  R.im y x

theorem isometry_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hf : ∀ x y, R'.form (γ x) (γ y) = R.form x y) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (x y : Fin g → ℂ) : R'.ip (φ x) (φ y) = R.ip x y := by
  let D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z w => R'.ip (φ z) (φ w) - R.ip z w
  have hl : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [D, map_add (f := _), ip_add_left']
    ring
  have hr : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    simp only [D, map_add (f := _), ip_add_right']
    ring
  have hcl : ∀ (c : ℂ) z w, D (c • z) w = star c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_left']
    ring
  have hcr : ∀ (c : ℂ) z w, D z (c • w) = c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_right']
    ring
  have h0l : ∀ w, D 0 w = 0 := fun w => by
    simp [D, RiemLat.ip]
  have h0r : ∀ z, D z 0 = 0 := fun z => by
    simp [D, RiemLat.ip]
  have base : ∀ l l', (D (R.P l) (R.P l')).im = 0 := fun l l' => by
    simp only [D, Complex.sub_im]
    rw [← hP, ← hP, ip_period_im, ip_period_im, hf, sub_self]
  have s1 : ∀ l w, (D (R.P l) w).im = 0 := fun l w => by
    have hw : w ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨l', rfl⟩ := h
      exact base l l'
    | zero => simp [h0r]
    | add w w' _ _ h h' => simp [hr, h, h']
    | smul r w _ h =>
      rw [real_smul_eq', hcr]
      simp [h]
  have s2 : ∀ z w, (D z w).im = 0 := fun z w => by
    have hz : z ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨l, rfl⟩ := h
      exact s1 l w
    | zero => simp [h0l]
    | add z z' _ _ h h' => simp [hl, h, h']
    | smul r z _ h =>
      rw [real_smul_eq', hcl]
      simp [h]
  have s3 : (D x y).re = 0 := by
    have h := s2 x (Complex.I • y)
    rw [hcr] at h
    simpa using h
  have s4 : D x y = 0 := Complex.ext s3 (s2 x y)
  exact sub_eq_zero.mp s4

theorem commutes_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (a : 𝓞 E) (x : Fin g → ℂ) : φ (R.B a x) = R'.B a (φ x) := by
  have hx : x ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, rfl⟩ := h
    rw [← R.act, ← hP, ← hP, map_smul, R'.act]
  | zero => simp
  | add x x' _ _ h h' => simp [h, h']
  | smul r x _ h =>
    rw [real_smul_eq', map_smul, map_smul, h, map_smul, map_smul]

theorem isometry_and_commutes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) →
    (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  intro E _ _ _ g Λ _ _ R R' γ φ hf hP
  have hs := (_root_.LevelTowerAlt.riemann_lattice_eigen_projections E g Λ Unit R).2.1
  exact ⟨isometry_of_periods R R' hs γ φ hf hP, commutes_of_periods R R' hs γ φ hP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentComplexOfRealHermitian
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.RealFormIndep

theorem pairing_real_combination {g k : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (u : Fin k → Fin g → ℂ) (a b : Fin k → ℝ) :
    (∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j) =
      ∑ i, ∑ j, ((a i * b j : ℝ) : ℂ) * (u i ⬝ᵥ Hm *ᵥ star (u j)) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.real_smul,
    Complex.real_smul, Complex.ofReal_mul]
  ring

theorem linearIndependent_complex_of_real_form :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℝ u →
        (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → LinearIndependent ℂ u := by
  intro g k Hm hpos u hu hreal
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc
  have hR : ∀ a b : Fin k → ℝ, ((∑ i, a i • u i) ⬝ᵥ Hm *ᵥ star (∑ j, b j • u j)).im = 0 := by
    intro a b
    rw [pairing_real_combination]
    simp [Complex.im_sum, hreal]
  have hxy : (∑ i, (c i).re • u i) + Complex.I • (∑ i, (c i).im • u i) = 0 := by
    rw [← hc]
    ext t
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Complex.re_add_im (c i)]
    ring
  have hx : (∑ i, (c i).re • u i) = -(Complex.I • ∑ i, (c i).im • u i) := eq_neg_of_add_eq_zero_left hxy
  have hyy : ((∑ i, (c i).im • u i) ⬝ᵥ Hm *ᵥ star (∑ j, (c j).im • u j)).re = 0 := by
    have h := hR (fun i => (c i).re) (fun j => (c j).im)
    rw [hx, neg_dotProduct, smul_dotProduct, smul_eq_mul] at h
    simpa using h
  have hy0 : (∑ i, (c i).im • u i) = 0 := by
    by_contra hne
    have := hpos _ hne
    linarith
  have hx0 : (∑ i, (c i).re • u i) = 0 := by
    rw [hx, hy0, smul_zero, neg_zero]
  intro i
  have h1 := hu (fun i => (c i).re) hx0 i
  have h2 := hu (fun i => (c i).im) hy0 i
  exact Complex.ext (by simpa using h1) (by simpa using h2)

end GlobalTheory.CompanionTheory.Ar.RealFormIndep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentRealPeriodsBasis
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_basis_periods_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  intro E _ _ _ g Λ _ _ R n b
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (_root_.LevelTowerAlt.riemann_lattice_eigen_projections E g Λ Unit R).2.1
  have hmem : ∀ x : Λ, R.P x ∈ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ c hy
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hmem x
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin g → ℂ) := by
    have h1 : Module.finrank ℤ Λ = Fintype.card (Fin n) := by
      haveI := R.free
      haveI := R.fin
      exact Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [← h1, R.rank, h2]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodsSubframeDetBounds
section
open Matrix Metric GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open scoped ComplexOrder

theorem frame_rank_of_gram_det_ne_zero {g k : ℕ} (M : Matrix (Fin g) (Fin k) ℂ)
    (h : (Mᵀ * M.map star).det ≠ 0) : M.rank = k := by
  have hu : IsUnit (Mᵀ * M.map star) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_fin] at h1
  have h2 := Matrix.rank_mul_le_left Mᵀ (M.map star)
  rw [Matrix.rank_transpose] at h2
  have h3 := M.rank_le_width
  omega

theorem frame_compact_nhd {g k : ℕ} (M₀ : Matrix (Fin g) (Fin k) ℂ) (h : M₀.rank = k) :
    ∃ S : Set (Matrix (Fin g) (Fin k) ℂ), IsCompact S ∧ S ∈ nhds M₀ ∧ ∀ M ∈ S, M.rank = k := by
  have hP : (M₀.map star)ᴴ = M₀ᵀ := by
    ext i j
    simp
  have hpos : 0 < ((M₀ᵀ * M₀.map star).det).re := by
    have := GlobalTheory.re_det_pos_of_posDef (subframe_gram_posDef M₀ h)
    rw [hP] at this
    exact this
  have hU : IsOpen {M : Matrix (Fin g) (Fin k) ℂ | 0 < ((Mᵀ * M.map star).det).re} :=
    isOpen_lt continuous_const subframe_continuous_det
  haveI : LocallyCompactSpace (Matrix (Fin g) (Fin k) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin g → Fin k → ℂ))
  obtain ⟨S, hS, hSU, hSc⟩ := local_compact_nhds (hU.mem_nhds hpos)
  refine ⟨S, hSc, hS, fun M hM => frame_rank_of_gram_det_ne_zero M ?_⟩
  intro h0
  have := hSU hM
  rw [Set.mem_setOf_eq, h0] at this
  simp at this

theorem continuousAt_matrix_inv {X : Type*} [TopologicalSpace X] {g : ℕ}
    (A : X → Matrix (Fin g) (Fin g) ℂ) (x : X) (hA : ContinuousAt A x) (h : (A x).det ≠ 0) :
    ContinuousAt (fun y => (A y)⁻¹) x := by
  have hd : ContinuousAt (fun y => (A y).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hA
  have ha : ContinuousAt (fun y => (A y).adjugate) x :=
    (continuous_id.matrix_adjugate).continuousAt.comp hA
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hd.inv₀ h).smul ha

theorem chartRadius_le_log_sum {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (h1 : ∀ k, ‖z k‖ < 1)
    (h0 : ∀ i : Fin n, i.val < a → z i ≠ 0) :
    1 ≤ chartRadius h z ∧ chartRadius h z ≤ (Real.exp 1 + 2) *
      (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) := by
  have hsum : ∑ j : Fin a, |Real.log ‖z (Fin.castLE h j)‖| =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    refine Finset.sum_bij (fun j _ => Fin.castLE h j) ?_ ?_ ?_ ?_
    · intro j _
      simp
    · intro j _ j' _ e
      exact Fin.castLE_injective h e
    · intro i hi
      have hi' : i.val < a := by simpa using hi
      exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, by ext; simp⟩
    · intro j _
      rfl
  have hterm : ∀ j : Fin a, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ =
      2 * |Real.log ‖z (Fin.castLE h j)‖| := by
    intro j
    have hc : cuspCoord h z j = z (Fin.castLE h j) := rfl
    have hn : 0 ≤ ‖z (Fin.castLE h j)‖ := norm_nonneg _
    rw [hc, Real.log_inv, Real.log_pow, abs_of_nonpos (Real.log_nonpos hn (h1 _).le)]
    push_cast
    ring
  have hr : chartRadius h z = Real.exp 1 + 2 *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    rw [chartRadius, ← hsum, Finset.mul_sum]
    simp only [hterm]
  have hS : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [hr]
  constructor
  · linarith
  · nlinarith

theorem logPeriods_subframe_det_bounds : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ) (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin k) (Fin g) ℂ), ContinuousAt F 0 → (F 0).rank = k → ∃ (ρ K : ℝ) (N : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i : Fin n, i.val < a → z i ≠ 0) → ‖(F z * L.H z * (F z)ᴴ).det‖ ≤ K ∧ 1 ≤ K * (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) ^ N * ‖(F z * L.H z * (F z)ᴴ).det‖ := by
  intro n a g Λ _ L k F hF hrk
  obtain ⟨Q, A, hAd, hA0, hAH⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame n a g Λ L
  obtain ⟨ρ₁, c, C, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousAt A 0 := by
    have : ContinuousOn A (ball 0 1) :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
    exact this.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hAi := continuousAt_matrix_inv A 0 hAc hA0
  have hc2 : Continuous (fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hmul : ContinuousAt (fun z => F z * (A z)⁻¹) 0 :=
    ContinuousAt.comp (g := fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2)
      (f := fun z => (F z, (A z)⁻¹)) hc2.continuousAt (hF.prodMk hAi)
  have hG : ContinuousAt (fun z => (F z * (A z)⁻¹)ᵀ) 0 :=
    (continuous_id.matrix_transpose.continuousAt).comp hmul
  have hM0 : ((F 0 * (A 0)⁻¹)ᵀ).rank = k := by
    have hu : IsUnit ((A 0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hA0)
    rw [Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, hrk]
  obtain ⟨S, hS, hSn, hSr⟩ := frame_compact_nhd _ hM0
  obtain ⟨C', hC', hd⟩ := subframe_det_log_growth g k (Matrix (Fin g) (Fin k) ℂ) S hS id
    continuousOn_id hSr c C hc
  have hdet : ContinuousAt (fun z => (A z).det) 0 :=
    (continuous_id.matrix_det).continuousAt.comp hAc
  have hev : ∀ᶠ z in nhds (0 : Fin n → ℂ), (F z * (A z)⁻¹)ᵀ ∈ S ∧ (A z).det ≠ 0 :=
    (hG.eventually_mem hSn).and (hdet.eventually_ne hA0)
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have he : 0 < Real.exp 1 + 2 := by positivity
  refine ⟨min (min ρ₁ ρ₂) 1, C' * (Real.exp 1 + 2) ^ k, k, lt_min (lt_min hρ₁ hρ₂) one_pos,
    min_le_right _ _, fun z hz hz0 => ?_⟩
  have hzρ : ‖z‖ < min (min ρ₁ ρ₂) 1 := by simpa [dist_zero_right] using hz
  have hz1n : ‖z‖ < 1 := lt_of_lt_of_le hzρ (min_le_right _ _)
  have hz1 : ∀ k, ‖z k‖ < 1 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz1n
  have hzρ₁ : z ∈ closedBall (0 : Fin n → ℂ) ρ₁ := by
    have : ‖z‖ ≤ ρ₁ := hzρ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    simpa [dist_zero_right] using this
  have hzρ₂ : z ∈ ball (0 : Fin n → ℂ) ρ₂ := by
    have : ‖z‖ < ρ₂ := lt_of_lt_of_le hzρ ((min_le_left _ _).trans (min_le_right _ _))
    simpa [dist_zero_right] using this
  obtain ⟨hGS, hAz⟩ := hball z hzρ₂
  have hcusp : ∀ j : Fin a, cuspCoord L.a_le z j ≠ 0 := fun j => hz0 _ (by simp)
  have hzp : z ∈ puncturedChart L.a_le (ball (0 : Fin n → ℂ) 1) :=
    ⟨by simpa [dist_zero_right] using hz1n, hcusp⟩
  have hw := HodgeDerivative.logLift_mem L.a_le hzp
  have hexp := HodgeDerivative.expCover_logLift L.a_le hcusp
  have hAHz := hAH _ hw
  rw [hexp] at hAHz
  obtain ⟨hb1, hb2⟩ := hb _ hw (by rw [hexp]; exact hzρ₁)
  rw [hexp] at hb2
  obtain ⟨hr1, hr2⟩ := chartRadius_le_log_sum L.a_le z hz1 hz0
  have hx := hd _ hGS ((Q.τ (logLift a z)).map Complex.im) (chartRadius L.a_le z) hr1 hb1 hb2
  set Y := (Q.τ (logLift a z)).map Complex.im with hY
  set S' := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| with hS'
  have hAu : IsUnit (A z).det := isUnit_iff_ne_zero.2 hAz
  have hinv1 : (A z)⁻¹ * A z = 1 := Matrix.nonsing_inv_mul _ hAu
  have hinv2 : (A z)ᴴ * ((A z)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv1, Matrix.conjTranspose_one]
  have hkey : F z * L.H z * (F z)ᴴ = (F z * (A z)⁻¹) * (Y⁻¹).map Complex.ofReal * (F z * (A z)⁻¹)ᴴ := by
    rw [← hAHz, Matrix.conjTranspose_mul]
    have e : F z * (A z)⁻¹ * (A z * L.H z * (A z)ᴴ) * (((A z)⁻¹)ᴴ * (F z)ᴴ) =
        F z * ((A z)⁻¹ * A z) * L.H z * ((A z)ᴴ * ((A z)⁻¹)ᴴ) * (F z)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, hinv1, hinv2]
    simp
  have hd1 : ((F z * L.H z * (F z)ᴴ).det).re ≤ C' := by
    rw [hkey]
    exact hx.1
  have hd2 : 1 ≤ C' * chartRadius L.a_le z ^ k * ((F z * L.H z * (F z)ᴴ).det).re := by
    rw [hkey]
    exact hx.2
  have hpsd : (F z * L.H z * (F z)ᴴ).PosSemidef := by
    rw [hkey]
    have hYp : Y.PosDef := Q.im_posDef _ hw
    exact (subframe_map_posSemidef hYp.inv.posSemidef).mul_mul_conjTranspose_same _
  have hD := hpsd.det_nonneg
  obtain ⟨D, hDdef⟩ : ∃ D, D = (F z * L.H z * (F z)ᴴ).det := ⟨_, rfl⟩
  rw [← hDdef] at hd1 hd2 hD ⊢
  have hnorm : ‖D‖ = D.re := by
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hD
    have e : D = (D.re : ℂ) := by
      apply Complex.ext <;> simp [h2.symm]
    rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonneg h1]
  rw [hnorm]
  have hre : 0 ≤ D.re := (Complex.nonneg_iff.1 hD).1
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE1 : 1 ≤ (Real.exp 1 + 2) ^ k := one_le_pow₀ (by linarith [Real.exp_pos 1])
  constructor
  · calc D.re ≤ C' := hd1
      _ ≤ C' * (Real.exp 1 + 2) ^ k := le_mul_of_one_le_right hC'.le hE1
  · have hpow : chartRadius L.a_le z ^ k ≤ ((Real.exp 1 + 2) * (1 + S')) ^ k :=
      pow_le_pow_left₀ (by linarith) hr2 k
    calc (1 : ℝ) ≤ C' * chartRadius L.a_le z ^ k * D.re := hd2
      _ ≤ C' * ((Real.exp 1 + 2) * (1 + S')) ^ k * D.re := by gcongr
      _ = C' * (Real.exp 1 + 2) ^ k * (1 + S') ^ k * D.re := by rw [mul_pow]; ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemSpanOfRealCombinationPeriods
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem mem_span_part_of_period_real_comb :
    ∀ (g k n : ℕ) (Λ : Type) [AddCommGroup Λ] (P : Λ →+ (Fin g → ℂ))
      (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
      LinearIndependent ℝ (fun j => P (b j)) → Function.Injective f →
      ∀ (x : Λ) (c : Fin k → ℝ), P x = ∑ i, (c i : ℂ) • P (b (f i)) →
        x ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := by
  intro g k n Λ _ P b f hli hf x c hx
  classical

  have hPx : P x = ∑ j, ((b.repr x j : ℤ) : ℝ) • P (b j) := by
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

  let d : Fin n → ℝ := fun j => ∑ i, if f i = j then c i else 0
  have hPd : P x = ∑ j, d j • P (b j) := by
    rw [hx]
    simp only [d, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Complex.coe_smul]
  have hcoef : ∀ j, ((b.repr x j : ℤ) : ℝ) = d j := by
    have h0 : ∑ j, (((b.repr x j : ℤ) : ℝ) - d j) • P (b j) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hPx, ← hPd, sub_self]
    intro j
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 j)
  have hzero : ∀ j, j ∉ Set.range f → b.repr x j = 0 := by
    intro j hj
    have hd : d j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      exact fun h => hj ⟨i, h⟩
    have := hcoef j
    rw [hd] at this
    exact_mod_cast this
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hzero j hj, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.Ar.Cusp
end

