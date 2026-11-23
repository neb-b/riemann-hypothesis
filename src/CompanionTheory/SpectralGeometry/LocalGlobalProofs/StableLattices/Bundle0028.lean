module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
section
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuDsDer

section general

variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]

def dL (a : E → E) (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (a q.1, 0)

def dR (b : E' → E') (Φ : E × E' → V) (q : E × E') : V := fderiv ℝ Φ q (0, b q.2)

theorem contDiff_dL {a : E → E} (ha : ContDiff ℝ ∞ a) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dL a Φ) := by
  exact (contDiff_infty_iff_fderiv.1 hΦ).2.clm_apply ((ha.comp contDiff_fst).prodMk contDiff_const)

theorem contDiff_dR {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (dR b Φ) := by
  exact (contDiff_infty_iff_fderiv.1 hΦ).2.clm_apply (contDiff_const.prodMk (hb.comp contDiff_snd))

theorem dR_dL {a : E → E} (ha : ContDiff ℝ ∞ a) {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V}
    (hΦ : ContDiff ℝ ∞ Φ) : dR b (dL a Φ) = dL a (dR b Φ) := by
  funext q
  have hΦ1 : ContDiff ℝ ∞ (fderiv ℝ Φ) := (contDiff_infty_iff_fderiv.1 hΦ).2
  have hc : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) q) q :=
    ((hΦ1.differentiable (by simp)) q).hasFDerivAt
  have hua : HasFDerivAt (fun q : E × E' => (a q.1, (0 : E')))
      (((fderiv ℝ a q.1).comp (ContinuousLinearMap.fst ℝ E E')).prod 0) q :=
    (((ha.differentiable (by simp)) q.1).hasFDerivAt.comp q hasFDerivAt_fst).prodMk (hasFDerivAt_const 0 q)
  have hub : HasFDerivAt (fun q : E × E' => ((0 : E), b q.2))
      ((0 : E × E' →L[ℝ] E).prod ((fderiv ℝ b q.2).comp (ContinuousLinearMap.snd ℝ E E'))) q :=
    (hasFDerivAt_const 0 q).prodMk (((hb.differentiable (by simp)) q.2).hasFDerivAt.comp q hasFDerivAt_snd)
  have hsymm := ((contDiff_infty.1 hΦ 2).contDiffAt (x := q)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  show fderiv ℝ (dL a Φ) q (0, b q.2) = fderiv ℝ (dR b Φ) q (a q.1, 0)
  rw [show dL a Φ = fun y => fderiv ℝ Φ y (a y.1, 0) from rfl,
    show dR b Φ = fun y => fderiv ℝ Φ y (0, b y.2) from rfl,
    (hc.clm_apply hua).fderiv, (hc.clm_apply hub).fderiv]
  simp
  exact hsymm _ _

end general

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def dW (W : List (Mat n)) (Φ : Mat n × Mat n → H) : Mat n × Mat n → H :=
  W.foldr (fun Y => dL fun g => g * Y) Φ

theorem contDiff_mulR (Y : Mat n) : ContDiff ℝ ∞ fun g : Mat n => g * Y := by
  exact contDiff_mul' contDiff_id contDiff_const

theorem contDiff_dW {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) : ∀ W, ContDiff ℝ ∞ (dW W Φ) := by
  intro W
  induction W with
  | nil => exact hΦ
  | cons Y W ih => exact contDiff_dL (contDiff_mulR Y) ih

theorem dR_dW {b : Mat n → Mat n} (hb : ContDiff ℝ ∞ b) {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) :
    ∀ W, dR b (dW W Φ) = dW W (dR b Φ) := by
  intro W
  induction W with
  | nil => rfl
  | cons Y W ih =>
    show dR b (dL (fun g => g * Y) (dW W Φ)) = dL (fun g => g * Y) (dW W (dR b Φ))
    rw [dR_dL (contDiff_mulR Y) hb (contDiff_dW hΦ W), ih]

theorem hasDerivAt_dL {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (Y g y : Mat n) :
    HasDerivAt (fun t => Φ (g * ex Y t, y)) (dL (fun g => g * Y) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g * ex Y t, y)) (g * Y, (0 : Mat n)) 0 :=
    (hasDerivAt_mul_ex g Y).prodMk (hasDerivAt_const 0 y)
  have h0 : (g, y) = (g * ex Y 0, y) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0

theorem hasDerivAt_dR {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (X g y : Mat n) :
    HasDerivAt (fun t => Φ (g, y * ex X t)) (dR (fun y => y * X) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g, y * ex X t)) ((0 : Mat n), y * X) 0 :=
    (hasDerivAt_const 0 g).prodMk (hasDerivAt_mul_ex y X)
  have h0 : (g, y) = (g, y * ex X 0) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0

variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

private theorem dW_eq_smul_dsW_of_eq_on_open (h : RepOn G σ) {u : H} (hu : IsSm G σ u) {Φ : Mat n × Mat n → H}
    (hΦ : ContDiff ℝ ∞ Φ) {y : Mat n} {O : Set (Mat n)} (hO : IsOpen O)
    (hΦu : ∀ g ∈ G, g ∈ O → Φ (g, y) = σ g u) :
    ∀ {W : List (Mat n)}, LieW G W → ∀ g ∈ G, g ∈ O → dW W Φ (g, y) = σ g (dsW σ W u) := by
  intro W
  induction W with
  | nil => intro _ g hg hgO; exact hΦu g hg hgO
  | cons Y W ih =>
    intro hW g hg hgO
    have hY : ∀ t, ex Y t ∈ G := hW Y (by simp)
    have hW' : LieW G W := fun X hX => hW X (by simp [hX])
    have hc : ContinuousAt (fun t : ℝ => g * ex Y t) 0 := (hasDerivAt_mul_ex g Y).continuousAt
    have hO' : O ∈ nhds (g * ex Y 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hgO
    have hev : (fun t => σ (g * ex Y t) (dsW σ W u)) =ᶠ[nhds 0] fun t => dW W Φ (g * ex Y t, y) := by
      filter_upwards [hc.preimage_mem_nhds hO'] with t ht
      exact (ih hW' _ (h.mul_mem g hg _ (hY t)) ht).symm
    have hd := (hasDerivAt_dL (contDiff_dW hΦ W) Y g y).congr_of_eventuallyEq hev
    rw [dsW_cons, apply_ds h hY hg (CompanionTheory.D.Upq.Sm.IsSm.differentiableAt h (CompanionTheory.D.Upq.Sm.IsSm.dsW h hu hW') hY)]
    exact hd.deriv.symm

private theorem hasDerivAt_dsW_smul_mul_ex (h : RepOn G σ) {x : H} (hx : IsSm G σ x) {F : Mat n → H}
    (hF : ContDiff ℝ ∞ F) {O : Set (Mat n)} (hO : IsOpen O) (hFx : ∀ g ∈ G, g ∈ O → σ g x = F g)
    {W : List (Mat n)} (hW : LieW G W) {p : Mat n} (hp : p ∈ G) (hpO : p ∈ O) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun τ : ℝ => dsW σ W (σ (p * ex X τ) x)) (dsW σ W (σ p (ds σ X x))) 0 := by
  have hΦ : ContDiff ℝ ∞ (fun q : Mat n × Mat n => F (q.1 * q.2)) := hF.comp contDiff_mul
  have h1 : (1 : Mat n) ∈ G := h.one_mem
  have hσ1 : ∀ v, σ 1 v = v := fun v => by rw [h.map_one]; rfl
  have hcont : ∀ y : Mat n, Continuous (fun g : Mat n => g * y) := fun y => (contDiff_mulR y).continuous
  have hpτ : ∀ᶠ τ in nhds (0 : ℝ), p * ex X τ ∈ O := by
    have hc : ContinuousAt (fun t : ℝ => p * ex X t) 0 := (hasDerivAt_mul_ex p X).continuousAt
    have hO' : O ∈ nhds (p * ex X 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hpO
    exact hc.preimage_mem_nhds hO'
  have hev : (fun τ : ℝ => dW W (fun q : Mat n × Mat n => F (q.1 * q.2)) (1, p * ex X τ)) =ᶠ[nhds 0]
      fun τ : ℝ => dsW σ W (σ (p * ex X τ) x) := by
    filter_upwards [hpτ] with τ hτ
    have hpτG : p * ex X τ ∈ G := h.mul_mem p hp _ (hX τ)
    have key := dW_eq_smul_dsW_of_eq_on_open (y := p * ex X τ) (O := (fun g => g * (p * ex X τ)) ⁻¹' O) h
      (CompanionTheory.D.Upq.Sm.IsSm.apply h hx hpτG) hΦ (hO.preimage (hcont _))
      (fun g hg hgO => by
        show F (g * (p * ex X τ)) = σ g (σ (p * ex X τ) x)
        rw [← hFx _ (h.mul_mem g hg _ hpτG) hgO, h.apply_mul hg hpτG]) hW 1 h1
      (by show 1 * (p * ex X τ) ∈ O; rw [one_mul]; exact hτ)
    rw [key, hσ1]
  have hd := hasDerivAt_dR (contDiff_dW hΦ W) X 1 p
  rw [dR_dW (contDiff_mulR X) hΦ W] at hd
  have hX1 : LieW G [X] := by
    intro Y hY t
    simp only [List.mem_singleton] at hY
    subst hY
    exact hX t
  have hds : IsSm G σ (ds σ X x) := CompanionTheory.D.Upq.Sm.IsSm.dsW h hx hX1
  have hΦ2 : ∀ g ∈ G, g ∈ (fun g => g * p) ⁻¹' O →
      dR (fun y => y * X) (fun q : Mat n × Mat n => F (q.1 * q.2)) (g, p) = σ g (σ p (ds σ X x)) := by
    intro g hg hgO
    rw [← (hasDerivAt_dR hΦ X g p).deriv]
    have hgp : g * p ∈ G := h.mul_mem g hg p hp
    rw [← h.apply_mul hg hp, apply_ds h hX hgp (CompanionTheory.D.Upq.Sm.IsSm.differentiableAt h hx hX)]
    apply Filter.EventuallyEq.deriv_eq
    have hc : ContinuousAt (fun t : ℝ => g * p * ex X t) 0 := (hasDerivAt_mul_ex (g * p) X).continuousAt
    have hO' : O ∈ nhds (g * p * ex X 0) := by rw [ex_zero, mul_one]; exact hO.mem_nhds hgO
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    show F (g * (p * ex X t)) = σ (g * p * ex X t) x
    rw [← mul_assoc, hFx _ (h.mul_mem _ hgp _ (hX t)) ht]
  have key2 := dW_eq_smul_dsW_of_eq_on_open h (CompanionTheory.D.Upq.Sm.IsSm.apply h hds hp) (contDiff_dR (contDiff_mulR X) hΦ)
    (hO.preimage (hcont p)) hΦ2 hW 1 h1 (by show 1 * p ∈ O; rw [one_mul]; exact hpO)
  rw [key2, hσ1] at hd
  exact hd.congr_of_eventuallyEq hev.symm

private theorem exists_contDiff_eq_on_nhds_of_contDiffOn {F : Mat n → H} {U : Set (Mat n)} {p : Mat n} (hU : IsOpen U) (hpU : p ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) :
    ∃ F' : Mat n → H, ContDiff ℝ ∞ F' ∧ ∃ O : Set (Mat n), IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧ ∀ g ∈ O, F' g = F g := by
  obtain ⟨r, hr0, hrU⟩ := Metric.isOpen_iff.1 hU p hpU
  let φ : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun g => (φ g : ℝ) • F g, ?_, Metric.ball p (r / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), fun g hg => hrU (Metric.ball_subset_ball (by linarith) hg),
    fun g hg => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Metric.ball p r
    · exact (φ.contDiff.contDiffAt).smul (hF.contDiffAt (hU.mem_nhds (hrU hz)))
    · have hzc : z ∈ (Metric.closedBall p (r / 2))ᶜ := by
        intro hz'
        exact hz (Metric.closedBall_subset_ball (by linarith) hz')
      have hev0 : ∀ᶠ g in nhds z, φ g = 0 := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hzc] with g hg
        apply φ.zero_of_le_dist
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hg
        exact hg.le
      have hev : (fun g => (φ g : ℝ) • F g) =ᶠ[nhds z] fun _ => (0 : H) := by
        filter_upwards [hev0] with g hg
        simp [hg]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · show (φ g : ℝ) • F g = F g
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hg), one_smul]

theorem dsDer : DsDer := by
  intro n Hm H _ _ _ σ hσ W hW p hp X hX x hx
  have h := hσ.rep
  have hLX : ∀ Y : Mat n, CompanionTheory.Bmu.Lie Hm Y → ∀ t, ex Y t ∈ Formalism.QuantumDeterminants.UH Hm :=
    fun Y hY t => ex_mem_of_lie hY t
  obtain ⟨U, F, hU, hpU, hFU, hFx⟩ := hx p hp
  obtain ⟨F', hF', O, hO, hpO, hOU, hF'O⟩ := exists_contDiff_eq_on_nhds_of_contDiffOn hU hpU hFU
  exact hasDerivAt_dsW_smul_mul_ex h hx hF' hO
    (fun g hg hgO => by rw [hF'O g hgO]; exact hFx g (hOU hgO) hg)
    (fun Y hY => hLX Y (hW Y hY)) hp hpO (hLX X hX)

end GlobalTheory.CompanionTheory.BmuDsDer

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExponentialMembership
section
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuExpMem

theorem lin_exp_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ m : ℕ, L (A ^ (m + 1)) = 0) : L (NormedSpace.exp A) = L 1 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hs : HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • A ^ m) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' A
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h1 := hs.map L hL
  have h2 : HasSum (fun m : ℕ => L (((m.factorial : ℂ)⁻¹) • A ^ m)) (L 1) := by
    have e : (fun m : ℕ => L (((m.factorial : ℂ)⁻¹) • A ^ m)) = fun m => if m = 0 then L 1 else 0 := by
      funext m
      cases m with
      | zero => simp
      | succ m => rw [map_smul, h m, smul_zero]; simp
    rw [e]
    exact hasSum_ite_eq 0 (L 1)
  exact h1.unique h2

theorem ex_mulVec {n : ℕ} (X : Mat n) (t : ℝ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) : ex X t *ᵥ v = v := by
  funext i
  have hsm : ∀ (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ), (c • M) *ᵥ v = c • (M *ᵥ v) := by
    intro c M
    funext l
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => (M *ᵥ v) i
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [hsm] }
  have hA : ∀ m : ℕ, L (((t : ℂ) • X) ^ (m + 1)) = 0 := by
    intro m
    show ((((t : ℂ) • X) ^ (m + 1)) *ᵥ v) i = 0
    rw [pow_succ, ← Matrix.mulVec_mulVec, hsm, hv, smul_zero, Matrix.mulVec_zero]
    rfl
  have e := lin_exp_eq ((t : ℂ) • X) L hA
  have e' : ((NormedSpace.exp ((t : ℂ) • X)) *ᵥ v) i = ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i := e
  show ((NormedSpace.exp ((t : ℂ) • X)) *ᵥ v) i = v i
  rw [e', Matrix.one_mulVec]

theorem ex_entry {n : ℕ} (X : Mat n) (t : ℝ) (a : ℕ) (j : Fin n)
    (h1 : ∀ i l : Fin n, a ≤ i.val → l.val < a → X i l = 0) (h2 : ∀ i : Fin n, a ≤ i.val → X i j = 0)
    (i : Fin n) (hi : a ≤ i.val) : ex X t i j = if i = j then 1 else 0 := by
  have hpow : ∀ m : ℕ, ∀ i' : Fin n, a ≤ i'.val → (X ^ (m + 1)) i' j = 0 := by
    intro m
    induction m with
    | zero => intro i' hi'; simpa using h2 i' hi'
    | succ m ih =>
      intro i' hi'
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      by_cases hl : l.val < a
      · rw [h1 i' l hi' hl, zero_mul]
      · rw [ih l (not_lt.1 hl), mul_zero]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun M N => rfl
      map_smul' := fun c M => rfl }
  have hA : ∀ m : ℕ, L (((t : ℂ) • X) ^ (m + 1)) = 0 := by
    intro m
    show (((t : ℂ) • X) ^ (m + 1)) i j = 0
    rw [smul_pow, Matrix.smul_apply, hpow m i hi, smul_zero]
  have e := lin_exp_eq ((t : ℂ) • X) L hA
  have e' : (NormedSpace.exp ((t : ℂ) • X)) i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j := e
  show (NormedSpace.exp ((t : ℂ) • X)) i j = _
  rw [e', Matrix.one_apply]

private theorem exp_mul_eq_mul_exp_of_semiconj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (B C H : 𝔸) (h : B * H = H * C) : NormedSpace.exp B * H = H * NormedSpace.exp C := by
  have hp : ∀ m : ℕ, B ^ m * H = H * C ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have e1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).mul_right H
  have e2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) C).mul_left H
  have hf : (fun m : ℕ => ((m.factorial : ℂ)⁻¹ • B ^ m) * H) =
      fun m => H * (((m.factorial : ℂ)⁻¹) • C ^ m) := by
    funext m
    rw [smul_mul_assoc, hp m, mul_smul_comm]
  rw [hf] at e1
  exact e1.unique e2

theorem expMem : ExpMem := by
  intro k r z X t
  have hint : ∀ B C H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, B * H = H * C →
      NormedSpace.exp B * H = H * NormedSpace.exp C := by
    intro B C H h
    letI : NormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
      Matrix.linftyOpNormedAlgebra
    exact exp_mul_eq_mul_exp_of_semiconj B C H h
  have hU : Lie (Formalism.QuantumDeterminants.Hpk k r) X → ex X t ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro hX
    have hX' : Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -(Formalism.QuantumDeterminants.Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
    have hAH : ((t : ℂ) • X)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * (-((t : ℂ) • X)) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, hX', Matrix.mul_neg, Matrix.mul_smul, smul_neg]
      simp [Complex.star_def, Complex.conj_ofReal]
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) =
      Formalism.QuantumDeterminants.Hpk k r
    rw [← Matrix.exp_conjTranspose, hint _ _ _ hAH, mul_assoc,
      ← Matrix.exp_add_of_commute (-((t : ℂ) • X)) ((t : ℂ) • X) (Commute.neg_left (Commute.refl _)),
      neg_add_cancel, NormedSpace.exp_zero, mul_one]
  refine ⟨fun h => ⟨hU h.1, fun a => ⟨ex_mulVec X t _ (h.2.1 a).1, ex_mulVec X t _ (h.2.1 a).2⟩,
    ex_mulVec X t z h.2.2⟩, fun h => ⟨hU h.1, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩⟩
  · refine ex_entry X t (a : ℕ) (Formalism.QuantumDeterminants.eI k r a) (fun i' l hi' hl => ?_) (fun i' hi' => h.2.1 a i' hi') i hi
    have hlr : l.val < r := lt_trans hl a.isLt
    have := h.2.1 ⟨l.val, hlr⟩ i' (le_of_lt (lt_of_lt_of_le hl hi'))
    simpa [Formalism.QuantumDeterminants.eI] using this
  · refine ex_entry X t r j (fun i' l hi' hl => ?_) (fun i' hi' => h.2.2 i' j hj1 hj2 hi') i hi
    have := h.2.1 ⟨l.val, hl⟩ i' (le_of_lt (lt_of_lt_of_le hl hi'))
    simpa [Formalism.QuantumDeterminants.eI] using this

end GlobalTheory.CompanionTheory.BmuExpMem
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormula
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeDeriv

theorem hasDerivAt_det {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (A' : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) (∑ j, ∑ i, adjugate (A 0) j i * A' i j) 0 := by
  have h1 : HasDerivAt (fun t => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ j, (∏ i ∈ univ.erase j, A 0 (σ i) i) • A' (σ j) j) 0 := by
    refine HasDerivAt.fun_sum fun σ _ => HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_finsetProd (f := fun i t => A t (σ i) i) fun i _ => h _ _
  have h2 : ∀ j, ∑ i, adjugate (A 0) j i * A' i j = ((A 0).updateCol j fun i => A' i j).det := by
    intro j
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  simp only [h2, Matrix.det_apply']
  convert h1 using 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul _ _ (mem_univ j), updateCol_self, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun i hi => updateCol_ne (ne_of_mem_erase hi)

theorem det_one_submatrix {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g).det = if univ.image f = univ.image g then 1 else 0 := by
  split_ifs with h
  · have : f = g := by
      refine (hf.range_inj hg).1 ?_
      have := congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
      simpa using this
    subst this
    rw [submatrix_one _ hf.injective, det_one]
  · have : ∃ i, f i ∉ univ.image g := by
      by_contra hc
      push Not at hc
      apply h
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, _, rfl⟩ := mem_image.1 hx
        exact hc i
      · rw [card_image_of_injective _ hf.injective, card_image_of_injective _ hg.injective]
    obtain ⟨i, hi⟩ := this
    refine det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [submatrix_apply, one_apply_ne]
    intro he
    exact hi (mem_image.2 ⟨j, mem_univ _, he.symm⟩)

theorem card_filter_lt {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (i : Fin m) :
    (((univ.image f).erase (f i)).filter fun c => c < f i).card = i := by
  have : (((univ.image f).erase (f i)).filter fun c => c < f i) = (Iio i).image f := by
    ext x
    simp only [mem_filter, mem_erase, mem_image, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨⟨_, j, rfl⟩, h⟩
      exact ⟨j, hf.lt_iff_lt.1 h, rfl⟩
    · rintro ⟨j, h, rfl⟩
      exact ⟨⟨(hf h).ne, j, rfl⟩, hf h⟩
  rw [this, card_image_of_injective _ hf.injective, Fin.card_Iio]

theorem image_succAbove {m n : ℕ} (f : Fin (m + 1) → Fin n) (hf : StrictMono f) (i : Fin (m + 1)) :
    univ.image (f ∘ i.succAbove) = (univ.image f).erase (f i) := by
  ext x
  simp only [mem_erase, mem_image, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne _ _ (hf.injective h), _, rfl⟩
  · rintro ⟨h, j, rfl⟩
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (fun e => h (by rw [e]))
    exact ⟨l, rfl⟩

theorem sum_adj {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) (a b : Fin n) :
    ∑ j, ∑ i, adjugate ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g) j i *
      (Matrix.single a b (1 : ℂ)) (f i) (g j) =
    if b ∈ univ.image g ∧ a ∉ (univ.image g).erase b ∧ univ.image f = insert a ((univ.image g).erase b) then
      (-1) ^ (((univ.image g).erase b).filter fun c => c < a).card *
        (-1) ^ (((univ.image g).erase b).filter fun c => c < b).card else 0 := by
  by_cases hb : b ∈ univ.image g
  swap
  · rw [if_neg (fun h => hb h.1)]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨_, rfl⟩
    exact hb (mem_image_of_mem _ (mem_univ _))
  by_cases ha : a ∈ univ.image f
  swap
  · rw [if_neg (by rintro ⟨_, _, h⟩; exact ha (h ▸ mem_insert_self _ _))]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨rfl, _⟩
    exact ha (mem_image_of_mem _ (mem_univ _))
  obtain ⟨j, _, rfl⟩ := mem_image.1 hb
  obtain ⟨i, _, rfl⟩ := mem_image.1 ha
  rw [sum_eq_single j, sum_eq_single i, single_apply_same, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := i.pos; omega⟩
    rw [adjugate_fin_succ_eq_det_submatrix, submatrix_submatrix,
      det_one_submatrix _ _ (hf.comp (Fin.strictMono_succAbove i)) (hg.comp (Fin.strictMono_succAbove j)),
      image_succAbove f hf, image_succAbove g hg]
    by_cases h : (univ.image f).erase (f i) = (univ.image g).erase (g j)
    · rw [if_pos h, if_pos, card_filter_lt g hg, ← h, card_filter_lt f hf, mul_one, pow_add]
      refine ⟨hb, ?_, ?_⟩
      · rw [← h]; exact notMem_erase _ _
      · rw [← h, insert_erase ha]
    · rw [if_neg h, if_neg, mul_zero]
      rintro ⟨_, h1, h2⟩
      apply h
      rw [h2, erase_insert h1]
  · intro i' _ hi
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hi (hf.injective h.1).symm
  · simp
  · intro j' _ hj
    refine sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hj (hg.injective h.2).symm
  · simp

theorem dR_wedge (k r m : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (J J' : Sub (2 * r + k + 1) m) :
    (wedge k r m).dR X J J' = ∑ j, ∑ i, adjugate ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) j i * X (J.1.orderEmbOfFin J.2 i) (J'.1.orderEmbOfFin J'.2 j) := by
  have h := hasDerivAt_det (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) (X.submatrix (J.1.orderEmbOfFin J.2) (J'.1.orderEmbOfFin J'.2))
      fun i j => PI.ComplexConjugateDerivative.exp_entry X _ _
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, submatrix_apply] at h
  exact h.deriv

theorem reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : reH k r Y + Complex.I • imH k r Y = Y := by
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [reH, imH, smul_smul, this, ← smul_add]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem dC_wedge_single : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by
  intro k r m a b J J'
  have h := sum_adj _ _ (J.1.orderEmbOfFin J.2).strictMono (J'.1.orderEmbOfFin J'.2).strictMono a b
  rw [Finset.image_orderEmbOfFin_univ, Finset.image_orderEmbOfFin_univ] at h
  rw [← h, FRep.dC, Matrix.add_apply, Matrix.smul_apply, dR_wedge, dR_wedge, smul_eq_mul, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← reH_add_imH k r (Matrix.single a b 1)]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.WedgeDeriv
end

