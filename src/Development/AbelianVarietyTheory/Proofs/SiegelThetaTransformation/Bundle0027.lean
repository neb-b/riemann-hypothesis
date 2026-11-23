module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
section
namespace GlobalTheory.Dict

section General
open Filter Topology

theorem const_of_norm_factor {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {U : Set V}
    (hU : IsOpen U) (hc : IsPreconnected U) {J : Type*} (R T : J → V → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hR : ∀ i, DifferentiableOn ℂ (R i) U) (hT : ∀ i, DifferentiableOn ℂ (T i) U)
    (h : ∀ x ∈ U, ∃ k : ℂ, ‖k‖ = ρ ∧ ∀ i, R i x = k * T i x) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ U, R i x = C * T i x := by
  by_cases hz : ∀ i, ∀ x ∈ U, T i x = 0
  ·
    refine ⟨(ρ : ℂ), Complex.ofReal_ne_zero.mpr hρ.ne', fun i x hx => ?_⟩
    obtain ⟨k, -, hk⟩ := h x hx
    rw [hk i, hz i x hx, mul_zero, mul_zero]
  simp only [not_forall, exists_prop] at hz
  obtain ⟨j, x0, hx0, hTj⟩ := hz

  have hev : ∀ᶠ y in 𝓝 x0, y ∈ U ∧ T j y ≠ 0 :=
    (hU.eventually_mem hx0).and (((hT j).continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne hTj)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hsub : Metric.ball x0 ε ⊆ U := fun y hy => (hball y hy).1

  have hqd : DifferentiableOn ℂ (fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) := fun y hy =>
    (((hR j).mono hsub) y hy).mul ((((hT j).mono hsub) y hy).inv (hball y hy).2)
  have hqk : ∀ y ∈ Metric.ball x0 ε, ∀ k : ℂ, (∀ i, R i y = k * T i y) → R j y * (T j y)⁻¹ = k := by
    intro y hy k hk
    rw [hk j, mul_inv_cancel_right₀ (hball y hy).2]
  have hqn : ∀ y ∈ Metric.ball x0 ε, ‖R j y * (T j y)⁻¹‖ = ρ := by
    intro y hy
    obtain ⟨k, hkn, hk⟩ := h y (hsub hy)
    rw [hqk y hy k hk, hkn]
  have hx0b : x0 ∈ Metric.ball x0 ε := Metric.mem_ball_self hε
  have hmax : IsMaxOn (norm ∘ fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) x0 :=
    isMaxOn_iff.mpr fun y hy => by
      simp only [Function.comp_apply]
      rw [hqn y hy, hqn x0 hx0b]

  have hqc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x0 ε).isPreconnected
    Metric.isOpen_ball hqd hx0b hmax
  set C : ℂ := R j x0 * (T j x0)⁻¹ with hCdef
  have hCn : ‖C‖ = ρ := hqn x0 hx0b
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hCn
    exact hρ.ne' hCn.symm
  have hloc : ∀ y ∈ Metric.ball x0 ε, ∀ i, R i y = C * T i y := by
    intro y hy i
    obtain ⟨k, -, hk⟩ := h y (hsub hy)
    have hqy : R j y * (T j y)⁻¹ = C := hqc hy
    rw [hk i, ← hqk y hy k hk, hqy]

  let S : Set V := {x | ∀ᶠ y in 𝓝 x, ∀ i, R i y = C * T i y}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hx0S : x0 ∈ S := Filter.eventually_of_mem (Metric.ball_mem_nhds x0 hε) hloc
  have hcl : closure S ∩ U ⊆ S := by
    rintro y ⟨hyS, hyU⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU y hyU
    have hδ4 : 0 < δ / 4 := by linarith
    obtain ⟨x1, hx1S, hdist⟩ := Metric.mem_closure_iff.mp hyS (δ / 4) hδ4
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y hδ4) fun z hz i => ?_

    have hφD : ∀ t ∈ Metric.ball (0 : ℂ) (3 / 2), x1 + t • (z - x1) ∈ Metric.ball y δ := by
      intro t ht
      have ht' : ‖t‖ < 3 / 2 := by simpa using ht
      have hx1' : ‖x1 - y‖ < δ / 4 := by rw [← dist_eq_norm, dist_comm]; exact hdist
      have hz' : ‖z - y‖ < δ / 4 := by rw [← dist_eq_norm]; exact hz
      have hw : ‖z - x1‖ ≤ ‖z - y‖ + ‖x1 - y‖ := by
        calc ‖z - x1‖ = ‖(z - y) - (x1 - y)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖x1 - y‖ := norm_sub_le _ _
      have htw : ‖t • (z - x1)‖ ≤ 3 / 2 * ‖z - x1‖ := by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖x1 + t • (z - x1) - y‖ = ‖(x1 - y) + t • (z - x1)‖ := by congr 1; abel
        _ ≤ ‖x1 - y‖ + ‖t • (z - x1)‖ := norm_add_le _ _
        _ < δ := by linarith
    have hφc : Continuous fun t : ℂ => x1 + t • (z - x1) := by fun_prop

    have hgd : DifferentiableOn ℂ (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1)))
        (Metric.ball (0 : ℂ) (3 / 2)) := by
      intro t ht
      have hmem : x1 + t • (z - x1) ∈ U := hδU (hφD t ht)
      have hlin : DifferentiableAt ℂ (fun t : ℂ => x1 + t • (z - x1)) t := by fun_prop
      have h1 : DifferentiableAt ℂ (R i) (x1 + t • (z - x1)) := (hR i).differentiableAt (hU.mem_nhds hmem)
      have h2 : DifferentiableAt ℂ (T i) (x1 + t • (z - x1)) := (hT i).differentiableAt (hU.mem_nhds hmem)
      exact ((h1.comp t hlin).sub ((h2.comp t hlin).const_mul C)).differentiableWithinAt

    have htend : Filter.Tendsto (fun t : ℂ => x1 + t • (z - x1)) (𝓝 0) (𝓝 x1) :=
      hφc.tendsto' 0 x1 (by simp)
    have hg0 : (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1))) =ᶠ[𝓝 0] 0 :=
      (htend.eventually hx1S).mono fun t ht => by
        simp only [Pi.zero_apply]
        rw [ht i, sub_self]

    have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (3 / 2) := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]; norm_num
    have hg1 := (hgd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (3 / 2)).isPreconnected (Metric.mem_ball_self (by norm_num)) hg0 h1mem
    have hz1 : x1 + (1 : ℂ) • (z - x1) = z := by rw [one_smul, add_sub_cancel]
    simp only [Pi.zero_apply, hz1] at hg1
    exact sub_eq_zero.mp hg1
  have hUS : U ⊆ S := hc.subset_of_closure_inter_subset hSo ⟨x0, hx0, hx0S⟩ hcl
  exact ⟨C, hC0, fun i x hx => (hUS hx).self_of_nhds i⟩

end General

end GlobalTheory.Dict

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem bchar_ne_zero_of_mem_bor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : Wt Ψ r)
    {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  unfold bchar
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_

  have htri : (mat b τ).BlockTriangular id := fun a c hca => (hb τ).2 a c hca
  have hdet := (hb τ).1
  rw [Matrix.det_of_isUpperTriangular htri] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

private theorem abs_psgn' (p0 n : ℕ) : |psgn p0 n| = 1 := by
  rw [psgn, Finset.abs_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> simp

private theorem dmin_eq_psgn_of_gram_diagonal {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
    {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) (τ : Ψ)
    (hx : gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (i : Fin (r + 1)) : dmin G x τ i = ((psgn p0 i : ℝ) : ℂ) := by
  rw [dmin, lminor, hx, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn,
    Complex.ofReal_prod, Finset.prod_range]
  simp

theorem exists_unitFr_rmul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ IsUnitFr X (rmul x b) := by
  obtain ⟨x₀, b, hb, hgram, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.ofReal_re]
    have h1 := abs_psgn' X.p0 i
    refine mul_self_pos.mpr fun h0 => ?_
    rw [h0, abs_zero] at h1
    exact zero_ne_one h1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.norm_real, Real.norm_eq_abs, abs_psgn']

theorem const_of_norm_factor_unitFr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (Jx : Type) (R T : Jx → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ → (∀ i, DifferentiableOn ℂ (R i) X.dom ∧ DifferentiableOn ℂ (T i) X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, R i (rmul x b) = bchar la b * R i x ∧ T i (rmul x b) = bchar la b * T i x) → (∀ x ∈ X.dom, IsUnitFr X x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x) → ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ X.dom, R i x = C * T i x := by
  intro E _ _ _ r X la Jx R T ρ hρ hRT hunit
  have hcd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := by
    intro τ
    unfold mat
    fun_prop
  have hopen : IsOpen X.dom := by
    show IsOpen {x | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (continuous_const.mul (Complex.continuous_re.comp (hcd τ i))))
  have hconn : IsPreconnected X.dom := (GlobalTheory.frames_isConnected E r X).isPreconnected
  refine const_of_norm_factor hopen hconn R T ρ hρ (fun i => (hRT i).1) (fun i => (hRT i).2.1) ?_

  intro x hx
  obtain ⟨b, hb, hxb, hu⟩ := exists_unitFr_rmul X hx
  obtain ⟨κ, hκ, hRTκ⟩ := hunit _ hxb hu
  refine ⟨κ, hκ, fun i => ?_⟩
  have hne := bchar_ne_zero_of_mem_bor la hb
  have h1 := hRTκ i
  rw [((hRT i).2.2 x hx b hb).1, ((hRT i).2.2 x hx b hb).2] at h1
  apply mul_left_cancel₀ hne
  rw [h1]
  ring

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetFrameNeZero
section
namespace GlobalTheory.Dict.Stab

open Matrix NumberField GlobalTheory GlobalTheory.SW GlobalTheory.SW.Lev GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem cop_mono {O : Type} [CommRing O] {𝔞 𝔟 : Ideal O} {s : O} (h : 𝔞 ≤ 𝔟)
    (hs : IsCoprime (Ideal.span {s}) 𝔞) : IsCoprime (Ideal.span {s}) 𝔟 := by
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs
  exact cop_iff.2 ⟨a, m, h hm, e⟩

variable {D : SW.Level X} {𝔐 : Ideal (𝓞 E)}

theorem cong_frame (hle : D.𝔪 ≤ 𝔐)
    (hJ : ∀ k ∈ D.J, ∀ i j, ∃ a ∈ 𝔐, ((k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j -
      (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j = Ideal.Quotient.mk D.𝔪 a)
    {ga : GL (Fin r) E} (hga : ga ∈ D.grp) (i : Fin r) : Cong X 𝔐 (lin ga (D.β i)) (D.β i) := by
  obtain ⟨-, k, hk, a, ha, h⟩ := (mem_grp ga).1 hga
  obtain ⟨s, hs, h⟩ := h i
  refine cong_trans ⟨s, cop_mono hle hs, Submodule.smul_mono_left hle h⟩ ?_
  have e : D.β i = ∑ j, (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i • D.β j := by
    simp [Matrix.one_apply]
  rw [cong_iff, e, ← Finset.sum_sub_distrib]
  refine le_loc _ (Submodule.sum_mem _ fun j _ => ?_)
  rw [← sub_smul]
  refine Submodule.smul_mem_smul ?_ (D.β_mem j)
  obtain ⟨c, hc, e'⟩ := hJ k hk j i
  have e1 : (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) j i =
      Ideal.Quotient.mk D.𝔪 ((1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i) := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [← ha, e1, Matrix.map_apply, ← map_sub] at e'
  have := add_mem (hle (Ideal.Quotient.eq.1 e')) hc
  rwa [sub_add_cancel] at this

theorem sub_mem_smul (hle : D.𝔪 ≤ 𝔐) {ga : GL (Fin r) E} (h : ∀ i, Cong X 𝔐 (lin ga (D.β i)) (D.β i))
    {L : Lt E r} (hL : L ∈ D.lats) (hfix : ∀ u ∈ L, lin ga u ∈ L) {u : Fin r → E} (hu : u ∈ L) :
    lin ga u - u ∈ 𝔐 • L := by
  obtain ⟨-, t, ht, h3, h4⟩ := hL
  obtain ⟨s, hs, hN⟩ := nakayama X.Λ_fg D.β_span
  have ht' := cop_mono hle ht.of_mul_right_left
  refine mem_of_loc (sub_mem (hfix u hu) hu) le_rfl ?_
  have h1 : Submodule.span (𝓞 E) (Set.range D.β) ≤ (loc 𝔐 (𝔐 • X.Λ)).comap (lin ga - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact cong_iff.1 (h i)
  have h2 := h1 (hN _ (h3 u hu))
  rw [Submodule.mem_comap, map_smul, map_smul] at h2
  obtain ⟨q, hq, h5⟩ := loc_loc ht' (loc_loc (cop_mono hle hs) h2)
  exact ⟨t * q, cop_mul ht' hq, by
    rw [mul_smul]; exact smul_map_mem LinearMap.id h4 h5⟩

noncomputable def quo (ga : GL (Fin r) E) (M : ℕ) : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) :=
  ((M : E)⁻¹) • (lin ga - LinearMap.id)

theorem quo_apply (ga : GL (Fin r) E) (M : ℕ) (u : Fin r → E) :
    quo ga M u = ((M : E)⁻¹) • (lin ga u - u) := rfl

theorem lin_eq_add {M : ℕ} (hM : M ≠ 0) (ga : GL (Fin r) E) (u : Fin r → E) :
    lin ga u = u + M • quo ga M u := by
  have : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  rw [quo_apply, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ this, one_smul, add_sub_cancel]

theorem div_mem {M : ℕ} (hM : M ≠ 0) (hn : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {L : Lt E r}
    {b : 𝓞 E} (hb : b ∈ conjI 𝔐) {z : Fin r → E} (hz : z ∈ 𝔐 • L) : b • ((M : E)⁻¹) • z ∈ L := by
  have : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine Submodule.smul_induction_on hz (fun a ha l hl => ?_) fun x y hx hy => ?_
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hn ▸ Ideal.mul_mem_mul ha hb)
    have hc' : (c : E) * M = a * b := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hc
    have e : b • ((M : E)⁻¹) • a • l = c • l := by
      rw [O_smul, O_smul, O_smul, smul_smul, smul_smul]
      congr 1
      field_simp
      linear_combination -hc'
    rw [e]; exact L.smul_mem _ hl
  · rw [smul_add, smul_add]; exact add_mem hx hy

theorem quo_mem {M : ℕ} (hM : M ≠ 0) (hn : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)})
    (hc : IsCoprime 𝔐 (conjI 𝔐)) {L : Lt E r} (hL : SelfD X L) {ga : GL (Fin r) E} (hu : IsUn X ga)
    (h : ∀ u ∈ L, lin ga u - u ∈ 𝔐 • L) (h' : ∀ u ∈ L, lin ga⁻¹ u - u ∈ 𝔐 • L)
    {u : Fin r → E} (hmem : u ∈ L) : quo ga M u ∈ L := by
  obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 hc
  rw [← one_smul (𝓞 E) (quo ga M u), ← e, add_smul]
  refine add_mem ((hL.2 _).2 fun y hy => ?_) (div_mem hM hn hm' (h u hmem))
  have hb : bar m ∈ conjI 𝔐 := mem_conjI.2 (by rwa [bar_bar])
  have hcc : cc ((M : E)⁻¹) = (M : E)⁻¹ := by simp [cc]
  have key (w : Fin r → E) : EF X (lin ga u - u) w = EF X u (lin ga⁻¹ w - w) := by
    have h1 := EF_add_left (X := X) (lin ga u - u) u w
    have h2 := EF_add_right (X := X) u (lin ga⁻¹ w - w) w
    rw [sub_add_cancel] at h1 h2
    rw [EF_lin hu, h2] at h1
    exact (add_right_cancel h1).symm
  obtain ⟨k, hk⟩ := (hL.2 u).1 hmem _ (div_mem hM hn hb (h' y hy))
  refine ⟨k, ?_⟩
  rw [EF_smul, quo_apply, EF_smulE, hcc, key, ← hk]
  congr 1
  simp only [lin_apply, O_smul, Matrix.mulVec_smul, smul_sub]
  rw [smul_comm, smul_comm ((M : E)⁻¹)]

theorem det_frame_ne_zero (D : SW.Level X) : (Matrix.of D.β).det ≠ 0 := by
  obtain ⟨s, hs, hN⟩ := nakayama X.Λ_fg D.β_span
  have hs0 : (s : E) ≠ 0 := by simpa using cop_ne_zero D.proper hs
  have hli : LinearIndependent E D.β := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    rw [← X.Λ_span, Submodule.span_le]
    intro v hv
    have := Submodule.span_le_restrictScalars (𝓞 E) E _ (hN v hv)
    exact (Submodule.smul_mem_iff _ hs0).1 this
  have : IsUnit (Matrix.of D.β) := Matrix.linearIndependent_rows_iff_isUnit.1 hli
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

theorem det_red {ga : GL (Fin r) E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red (fun i => lin ga (D.β i)) k) (hd : (ga : Matrix (Fin r) (Fin r) E).det = 1) :
    (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)).det = 1 := by
  obtain ⟨s₁, hs₁, h1, -⟩ := keeps h
  obtain ⟨s₂, hs₂, hN⟩ := nakayama X.Λ_fg D.β_span
  obtain ⟨a, ha, h⟩ := h
  have hs := cop_mul hs₂ hs₁
  set s := s₂ * s₁ with hsdef
  have h2 (i) : ∃ c : Fin r → 𝓞 E, ∑ j, c j • D.β j = s • lin ga (D.β i) := by
    rw [hsdef, mul_smul]
    exact (Submodule.mem_span_range_iff_exists_fun _).1 (hN _ (h1 _ (D.β_mem i)))
  choose c hc using h2
  have h3 (i j) : c i j - s * a j i ∈ D.𝔪 := by
    refine coeff_cong D (c := c i) (d := fun j => s * a j i) ?_ j
    rw [hc, cong_iff]
    simp only [mul_smul, ← Finset.smul_sum, ← smul_sub]
    exact Submodule.smul_mem _ _ (cong_iff.1 (h i))
  have h4 : (Matrix.of c).map (algebraMap (𝓞 E) E) * Matrix.of D.β =
      (s : E) • (Matrix.of D.β * (ga : Matrix (Fin r) (Fin r) E)ᵀ) := by
    ext i l
    have := congrFun (hc i) l
    rw [Finset.sum_apply] at this
    refine Eq.trans this ?_
    change (s : E) * ∑ j, (ga : Matrix (Fin r) (Fin r) E) l j * D.β i j =
      (s : E) * ∑ j, D.β i j * (ga : Matrix (Fin r) (Fin r) E) l j
    simp only [mul_comm]
  have h5 : (Matrix.of c).det = s ^ r := by
    have := congrArg Matrix.det h4
    rw [det_mul, det_smul, det_mul, det_transpose, hd, mul_one, Fintype.card_fin,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_pow]
    exact mul_right_cancel₀ (det_frame_ne_zero D) this
  have h6 : (Matrix.of c).map (Ideal.Quotient.mk D.𝔪) =
      Ideal.Quotient.mk D.𝔪 s • (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪))ᵀ := by
    ext i j
    rw [← ha]
    exact (Ideal.Quotient.eq.2 (h3 i j)).trans (map_mul _ _ _)
  have h7 := congrArg Matrix.det h6
  rw [det_smul, det_transpose, Fintype.card_fin, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h5,
    map_pow] at h7
  obtain ⟨b, m, hm, e⟩ := cop_iff.1 hs
  have hu : IsUnit (Ideal.Quotient.mk D.𝔪 s) := by
    refine IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk D.𝔪 b) ?_
    have := congrArg (Ideal.Quotient.mk D.𝔪) e
    rwa [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hm, add_zero, map_one] at this
  exact ((hu.pow r).mul_left_cancel (h7.symm.trans (mul_one _).symm))

end GlobalTheory.Dict.Stab

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.Dict.stab_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (M : ℕ), D.𝔪 ≤ 𝔐 → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → (∀ k ∈ D.J, ∀ i j, ∃ a ∈ 𝔐, ((k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j - (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j = Ideal.Quotient.mk D.𝔪 a) → ∀ ga ∈ D.grp, (∀ i, Cong X 𝔐 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) (D.β i)) ∧ ∀ L ∈ D.lats, mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') ∧ (∀ u ∈ D.sh L, ∃ u' ∈ D.sh L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') ∧ ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → 3 ≤ M → ((k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)).det = 1 := by
  intro E _ _ _ r X g bas _ n _ _ D 𝔐 M hle hn hJ ga hga
  have hM : M ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot D.ne_bot
    have hb : Lev.bar a ∈ conjI 𝔐 := Lev.mem_conjI.2 (by rw [Lev.bar_bar]; exact hle ha)
    have := Ideal.mul_mem_mul (hle ha) hb
    rw [hn, Nat.cast_zero, Ideal.span_singleton_zero, Ideal.mem_bot] at this
    rcases mul_eq_zero.1 this with h | h
    · exact ha0 h
    · exact ha0 (by rw [← Lev.bar_bar a, h, map_zero])
  have hc : IsCoprime 𝔐 (conjI 𝔐) := by
    obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 D.cop
    exact Ideal.isCoprime_iff_exists.2 ⟨m, hle hm, m', Lev.mem_conjI.2 (hle (Lev.mem_conjI.1 hm')), e⟩
  refine ⟨Stab.cong_frame hle hJ hga, fun L hL hfix => ?_⟩
  have hu := ((Lev.mem_grp ga).1 hga).1
  have f1 : ∀ u ∈ L, Lev.lin ga u ∈ L := fun u hu => hfix ▸ ⟨u, hfix.symm ▸ hu, rfl⟩
  have f2 : ∀ u ∈ L, Lev.lin ga⁻¹ u ∈ L := fun u hu => Lev.mem_mapL.1 (hfix.symm ▸ hu)
  have hq : ∀ u ∈ L, Stab.quo ga M u ∈ L := fun u hmem =>
    Stab.quo_mem hM hn hc hL.1 hu
      (fun _ => Stab.sub_mem_smul hle (Stab.cong_frame hle hJ hga) hL f1)
      (fun _ => Stab.sub_mem_smul hle (Stab.cong_frame hle hJ (inv_mem hga)) hL f2) hmem
  have h1 : ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u' :=
    fun u hmem => ⟨_, hq u hmem, Stab.lin_eq_add hM ga u⟩
  refine ⟨h1, fun u hmem => ⟨Stab.quo ga M u, fun b hb => ?_, Stab.lin_eq_add hM ga u⟩,
    fun k hk h3 => Stab.det_red hk ?_⟩
  · rw [← map_smul, ← one_smul (𝓞 E) (Stab.quo ga M _)]
    exact Lev.smul_map_mem _ (fun v hv => by rw [one_smul]; exact hq v hv) (hmem b hb)
  · refine GlobalTheory.CongruenceDet.det_eq_one E r M X.Gm L ga X.Gm_det hL.1.1 (Lev.span_lats hL) h3
      ⟨hu, fun x => ⟨f1 x, fun hx => ?_⟩⟩ h1
    exact Lev.lin_inv ga x ▸ f2 _ hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetHermitianFormAtFramePeriodCoordsOfUnitFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

private theorem herm_mulVec_mulVec' {g : ℕ} (H0 H1 B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z w, hermForm H1 (B *ᵥ z) (B *ᵥ w) = hermForm H0 z w) :
    H0 = Bᵀ * H1 * B.map conj := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single j 1 : Fin g → ℂ) = (Pi.single j 1 : Fin g → ℂ) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have e : hermForm H0 (Pi.single i 1) (Pi.single j 1) = H0 i j := by
    unfold hermForm
    rw [hs]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e] at h1
  rw [← h1]
  simp [hermForm, Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, Finset.mul_sum,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)

theorem det_hx_of_isUnitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, IsUnitFr X x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ z w, hermForm Hm z w = hx X bas idx x z w) → Hm.det = ((∏ τ : X.Ψ, X.c τ ^ r : ℝ) : ℂ) := by
  intro E _ _ _ r X g bas idx n hs hn x hx hu Hm hH
  have hG : ∀ a b, cc (X.Gm a b) = X.Gm b a := X.4
  have hA : x ∈ GG X.Ψ X.Gm X.p0 := by
    unfold Data.dom at hx
    exact hx
  obtain ⟨x₀, b, hb, ho, hbd, rfl⟩ :=
    (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm hG).1 x hA hu
  have ho' : X.IsOrtho x₀ := ho

  have hone : (1 : Matrix (Fin g) (Fin g) ℂ).map conj = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h1 : Hm = GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b) := by
    have h := herm_mulVec_mulVec' Hm (GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b)) 1 (by
      intro z w
      rw [Matrix.one_mulVec, Matrix.one_mulVec, hH, GlobalTheory.ThFr.hermForm_Hm]
      rfl)
    rw [h, hone, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

  have h0 : GlobalTheory.ThFr.Hm X bas idx x₀ = ((GlobalTheory.ThFr.borMat X b).submatrix idx idx)ᵀ *
      GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b) * ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).map conj :=
    herm_mulVec_mulVec' _ _ _ (fun z w =>
      GlobalTheory.ThFr.hermForm_Hm_rmul (bas := bas) (idx := idx) (x := x₀) (hb := hb) z w)
  have hdet0 := GlobalTheory.ThFr.det_Hm_of_isOrtho (idx := idx) (hs := hs) (ho := ho')
  have hnB : ‖((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det‖ = 1 := by
    rw [GlobalTheory.ThFr.det_borMat hb idx, norm_prod]
    apply Finset.prod_eq_one
    intro p _
    unfold GlobalTheory.ThFr.rowFac
    split_ifs <;> simp [hbd]
  have hc : (((GlobalTheory.ThFr.borMat X b).submatrix idx idx).map conj).det =
      conj ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det := by
    rw [RingHom.map_det]
    rfl
  have hm : ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det *
      conj ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnB]
    norm_num
  rw [h1, ← hdet0, h0, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  linear_combination (-(GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b)).det) * hm

end GlobalTheory.Dict
end

