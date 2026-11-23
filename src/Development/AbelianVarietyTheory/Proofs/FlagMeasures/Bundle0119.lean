module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairIdealKillsDiscriminantModules
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroup
section
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff

open scoped Nat Topology

noncomputable section

namespace GlobalTheory.RightDerivSmooth

variable {n : ℕ}


set_option backward.isDefEq.respectTransparency false in
theorem exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by
  have hp : ∀ m : ℕ, Y ^ m * H = H * Z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) (NormedSpace.exp Y * H) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mul_right H
  have h2 : HasSum (fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m)) (H * NormedSpace.exp Z) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z).mul_left H
  have e : (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) = fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m) := by
    funext m
    rw [Matrix.smul_mul, hp, Matrix.mul_smul]
  rw [e] at h1
  exact h1.unique h2


set_option backward.isDefEq.respectTransparency false in
theorem inUH_exp {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := by
  have hY : ((t : ℂ) • X)ᴴ * H + H * ((t : ℂ) • X) = 0 := by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hX, smul_zero]
  generalize (t : ℂ) • X = Y at hY
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha', hb']


set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  open scoped Matrix.Norms.Operator in
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  open scoped Matrix.Norms.Operator in
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_entry X k j).const_mul _

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_local {H X g : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (hg : inUH H g)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (e : ∀ h ∈ U, inUH H h → f h = F h) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hc := hasDerivAt_mul_exp g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hd : HasFDerivAt F (fderiv ℝ F g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hc
  refine h1.congr_of_eventuallyEq ?_
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hc.continuousAt.eventually (hU.mem_nhds (by simpa only [h0] using hgU))
  filter_upwards [h2] with t ht
  exact e _ ht (inUH_mul hg (inUH_exp hX t))

end GlobalTheory.RightDerivSmooth

section
open GlobalTheory.RightDerivSmooth
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


set_option backward.isDefEq.respectTransparency false in
theorem GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  intro n H X E _ _ f hX hf
  have hder : ∀ g, inUH H g → ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), ∃ F : Matrix (Fin n) (Fin n) ℂ → E,
      IsOpen U ∧ g ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ (∀ h ∈ U, inUH H h → f h = F h) ∧
      ∀ h ∈ U, inUH H h → rdM X f h = fderiv ℝ F h (h * X) ∧
        HasDerivAt (fun t : ℝ => f (h * NormedSpace.exp ((t : ℂ) • X))) (rdM X f h) 0 := by
    intro g hg
    obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
    refine ⟨U, F, hU, hgU, hF, e, fun h hhU hh => ?_⟩
    have hd := hasDerivAt_local hX hh hU hhU hF e
    have hr : rdM X f h = fderiv ℝ F h (h * X) := hd.deriv
    exact ⟨hr, hr ▸ hd⟩
  refine ⟨?_, ?_, fun g hg => ?_⟩
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, e, -⟩ := hder g hg
    have hFc : ContinuousWithinAt F {g | inUH H g} g :=
      ((hF.continuousOn).continuousAt (hU.mem_nhds hgU)).continuousWithinAt
    refine hFc.congr_of_eventuallyEq ?_ (e g hgU hg)
    filter_upwards [inter_mem_nhdsWithin {g | inUH H g} (hU.mem_nhds hgU)] with h hh
    exact e h hh.2 hh.1
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    refine ⟨U, fun h => fderiv ℝ F h (h * X), hU, hgU, ?_, fun h hhU hh => (hr h hhU hh).1⟩
    have h1 : ContDiffOn ℝ ∞ (fun h => fderiv ℝ F h) U := hF.fderiv_of_isOpen hU (le_of_eq rfl)
    have h2 : ContDiff ℝ ∞ (fun h : Matrix (Fin n) (Fin n) ℂ => h * X) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff
    exact h1.clm_apply h2.contDiffOn
  · obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    exact (hr g hgU hg).2

end

theorem GlobalTheory.rdM_smoothOnH : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 :=
  fun n H X E _ _ f hX hf => GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group n H X E f hX hf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory

theorem rowsAut_idem_elementary : ∀ B : RowsAut,
    (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧ (∀ y, ‖B.e y‖ ≤ (B.e 1).re) ∧ Continuous B.e := by
  intro B
  obtain ⟨hlc, -, hstar, hpos, -⟩ := B.e_adm

  have him : (B.e 1).im = 0 := by
    have h := congrArg Complex.im (hstar 1)
    rw [inv_one, Complex.star_def, Complex.conj_im] at h
    linarith

  have hre : 0 ≤ (B.e 1).re := by
    have h := hpos 1 (fun _ => 1) (fun _ => 1)
    simp only [Fin.sum_univ_one, star_one, one_mul, inv_one] at h
    exact (Complex.nonneg_iff.mp h).1
  refine ⟨him, hre, ?_, hlc.continuous⟩
  intro y
  set a := (B.e 1).re with ha
  have h1 : B.e 1 = (a : ℂ) := Complex.ext (by simp [ha]) (by simp [him])
  set b := B.e y with hb
  have hyi : B.e y⁻¹ = star b := hstar y
  have key : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hs : star ((‖b‖ : ℝ) : ℂ) = ((‖b‖ : ℝ) : ℂ) := Complex.conj_ofReal _

  have h := hpos 2 ![1, y] ![b, -((‖b‖ : ℝ) : ℂ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_one, one_mul, mul_one, inv_mul_cancel, hyi, h1, star_neg, hs] at h
  have hE : star b * b * (a : ℂ) + star b * -((‖b‖ : ℝ) : ℂ) * b +
      (-((‖b‖ : ℝ) : ℂ) * b * star b + -((‖b‖ : ℝ) : ℂ) * -((‖b‖ : ℝ) : ℂ) * (a : ℂ)) =
      ((2 * ‖b‖ ^ 2 * (a - ‖b‖) : ℝ) : ℂ) := by
    push_cast at key ⊢
    linear_combination ((a : ℂ) - 2 * ((‖b‖ : ℝ) : ℂ)) * key
  rw [hE, Complex.zero_le_real] at h
  refine le_of_not_gt fun hlt => ?_
  have hb0 : 0 < ‖b‖ := lt_of_le_of_lt hre hlt
  have hneg : 2 * ‖b‖ ^ 2 * (a - ‖b‖) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruence
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Stab

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] in
theorem smul_eq (a : 𝓞 K) (v : V) : a • v = (a : K) • v := (algebraMap_smul K a v).symm

theorem cancel {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) {M : Submodule (𝓞 K) V} {v : V}
    (h : ∀ a ∈ J, a • v ∈ J • M) : v ∈ M := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
  have h1 : J • Submodule.span (𝓞 K) {v} ≤ J • M := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (h a ha)
  have h2 : Ideal.span {c} • Submodule.span (𝓞 K) {v} ≤ Ideal.span {c} • M := by
    rw [hJ', mul_comm, Submodule.mul_smul, Submodule.mul_smul]
    exact Submodule.smul_mono le_rfl h1
  have h3 := h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c)
    (Submodule.mem_span_singleton_self v))
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨m, hm, hmv⟩ := h3
  rw [smul_eq, smul_eq] at hmv
  have hc1 : (c : K) ≠ 0 := by exact_mod_cast hc0
  rwa [← smul_right_injective V hc1 hmv]

theorem exists_mul {M : Submodule (𝓞 K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ M := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem
  | exact _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem
  | (apply _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem ..)

variable [StarRing K]


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isom_of_mem {H : HermSpace K V} {r : ℕ} {F F' : FlagD H r} {s : V ≃ₗ[K] V}
    (hs : s ∈ Subgroup.closure {s : V ≃ₗ[K] V | F.InN (s : V →ₗ[K] V) ∧ F'.InN (s : V →ₗ[K] V)}) :
    s ∈ isomGrp H :=
  (Subgroup.closure_le (k := {t : V ≃ₗ[K] V | F.InN (t : V →ₗ[K] V) ∧ F'.InN (t : V →ₗ[K] V)}) (isomGrp H)).2 (fun t ht =>
    (mem_isomGrp H t).2 ht.1.1) hs


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem le_perp_perp (H : HermSpace K V) (S : Submodule K V) : S ≤ perp H (perp H S) := by
  intro x hx
  rw [mem_perp_iff]
  intro y hy
  rw [← H.herm, (mem_perp_iff H S y).1 hy x hx, star_zero]

end GlobalTheory.DegCnt.Stab


open GlobalTheory.DegCnt.Stab in
theorem GlobalTheory.DegCnt.stab_of_deep_congruence : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → ∀ s ∈ N.Rs, (∀ x ∈ N.P0, s x - x ∈ 𝔠 ^ (3 * e + 10) • N.P0) → s • Λ = Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 h1 h2 h3 e hsp hn s hs hcong
  have hkill := (_root_.GlobalTheory.DegCnt.Kill.main K V H hK r N g Λ hg hΛ 𝔠 h0 h1 h2 h3).1
  have hcompl : IsCompl N.Wt N.Pi := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).2.2.1
  have hiso := (mem_isomGrp H s).1 (isom_of_mem hs.1)
  have hfix : ∀ w ∈ N.Wt, s w = w := fun w hw =>
    (mem_fixingSubgroup_iff (V ≃ₗ[K] V)).1 hs.2 w hw
  have hdual : dual H Λ = Λ := hΛ.1.1.2
  have hspan : Submodule.span K (Λ : Set V) = ⊤ := hΛ.1.1.1.2
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H Λ x).1 (hdual.symm ▸ hx)).2
  have hIP : II N.F N.F' ≤ N.Pi :=
    (inf_le_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans
      (le_perp_perp H (V0 N.F N.F' ⊔ N.Ist))
  have hle : ∀ x ∈ Λ, s x ∈ Λ := by
    intro x hx
    obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.1
      (hcompl.sup_eq_top ▸ Submodule.mem_top : x ∈ N.Wt ⊔ N.Pi)
    have hpw : ∀ y ∈ N.Wt, H.B p y = 0 := (mem_perp_iff H N.Wt p).1 hp
    have hwd : w ∈ dual H (latTh N.F N.F' Λ) := by
      rw [hsp, mem_dual_iff]
      constructor
      · obtain ⟨d, hd, hdw⟩ := exists_mul (M := Λ) (v := w) (hspan ▸ Submodule.mem_top)
        have hd1 : (d : K) ≠ 0 := by exact_mod_cast hd
        have hw' : w = (d : K)⁻¹ • (d • w) := by rw [smul_eq, smul_smul, inv_mul_cancel₀ hd1, one_smul]
        rw [hw']
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Submodule.mem_sup_left ⟨hdw, (rs (𝓞 K) N.Wt).smul_mem d hw⟩
      · intro y hy
        obtain ⟨θ, hθ, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
        have e1 : H.B w i = 0 := by
          rw [← H.herm, (mem_perp_iff H N.Wt i).1 (hIP hi) w hw, star_zero]
        have e2 := hint _ hx θ hθ.1
        rw [map_add (f := _), LinearMap.add_apply, hpw θ hθ.2, add_zero] at e2
        rw [map_add (f := _), e1, add_zero]
        exact e2
    have hap : ∀ a ∈ 𝔠 ^ 3, a • p ∈ Λ ⊓ rs (𝓞 K) N.Pi := by
      intro a ha
      have := hkill (Submodule.smul_mem_smul ha hwd)
      rw [hsp] at this
      obtain ⟨θ, hθ, i, hi, h⟩ := Submodule.mem_sup.1 this
      have hiW : i ∈ N.Wt := by
        have : i = a • w - θ := by rw [← h]; abel
        rw [this]
        exact (rs (𝓞 K) N.Wt).sub_mem ((rs (𝓞 K) N.Wt).smul_mem a hw) hθ.2
      have hi0 : i = 0 := (Submodule.disjoint_def.1 hcompl.disjoint) i hiW (hIP hi)
      refine ⟨?_, (rs (𝓞 K) N.Pi).smul_mem a hp⟩
      have : a • p = a • (w + p) - θ := by rw [smul_add, ← h, hi0]; abel
      rw [this]
      exact Λ.sub_mem (Λ.smul_mem a hx) hθ.1
    have hbp : ∀ b ∈ 𝔠 ^ (e + 3), b • p ∈ N.P0 := by
      intro b hb
      rw [pow_add] at hb
      refine Submodule.mul_induction_on hb (fun m hm n hn' => ?_) (fun m n hm hn' => ?_)
      · rw [mul_smul]
        exact hn.2 (Submodule.smul_mem_smul hm (hap n hn'))
      · rw [add_smul]; exact N.P0.add_mem hm hn'
    have hsp' : s p - p ∈ 𝔠 ^ e • N.P0 := by
      refine cancel (pow_ne_zero (e + 3) h0) fun b hb => ?_
      have := hcong _ (hbp b hb)
      rw [smul_eq, map_smul, ← smul_sub, ← smul_eq] at this
      rw [← Submodule.mul_smul, ← pow_add]
      exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl this
    have : s (w + p) = (w + p) + (s p - p) := by rw [map_add (f := _), hfix w hw]; abel
    rw [this]
    exact Λ.add_mem hx (hn.1 hsp').1
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    exact hle x hx
  · intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists x s Λ).2 ⟨s.symm x, ?_, s.apply_symm_apply x⟩
    rw [← hdual, mem_dual_iff]
    refine ⟨hspan ▸ Submodule.mem_top, fun y hy => ?_⟩
    rw [← hiso, s.apply_symm_apply]
    exact hint x hx _ (hle y hy)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarCoeffOfEqReverse
section
open Formalism.BasicNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.GoodIdemReal

open GlobalTheory.SeriesSupportTest

theorem star_coeff_of_reverse : ∀ D : D7, (∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), f.Monic → f.coeff 0 ≠ 0 →
      ∀ x, star ((D.ntypes.eSer k f).coeff x) = (D.ntypes.eSer k (C (f.coeff 0)⁻¹ * f.reverse)).coeff x) →
    (∀ γ : G0g D.nd, star (D.ntypes.e0.coeff γ) = D.ntypes.e0.coeff γ) := by
  intro D hS γ
  classical
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩

  let ψ : ∀ k : Fin 2, (Fin D.R.r → ZMod (D.host.g k)) → (Fin D.R.r → ZMod (D.host.g k)) :=
    fun k a => if (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 then fun i => (dl (Formalism.CyclotomicNorms.monicOf a)).coeff i else a
  have hlab : ∀ k (a : Fin D.R.r → ZMod (D.host.g k)), (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 →
      (Formalism.CyclotomicNorms.monicOf a).Monic ∧ (Formalism.CyclotomicNorms.monicOf a).natDegree = D.R.r ∧ (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 :=
    fun k a ha => ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf a, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf a, ha⟩
  have hψm : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → Formalism.CyclotomicNorms.monicOf (ψ k a) = dl (Formalism.CyclotomicNorms.monicOf a) := by
    intro k a ha
    have hd := dl_lab (hlab k a ha)
    simp only [ψ, if_pos ha]
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ hd.1 hd.2.1
  have hψ0 : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0 → ψ k a = a := by
    intro k a ha
    simp only [ψ, ha, ne_eq, not_true_eq_false, if_false]
  have hψc : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → (Formalism.CyclotomicNorms.monicOf (ψ k a)).coeff 0 ≠ 0 := by
    intro k a ha
    rw [hψm k a ha, (dl_lab (hlab k a ha)).2.2]
    exact inv_ne_zero ha
  have hψinv : ∀ k, Function.Involutive (ψ k) := by
    intro k a
    by_cases ha : (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0
    · rw [hψ0 k a ha, hψ0 k a ha]
    · funext i
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (ψ k (ψ k a)) i, hψm k _ (hψc k a ha), hψm k a ha,
        dl_dl (hlab k a ha), Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

  let Φ : Equiv.Perm (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) :=
    Function.Involutive.toPerm (fun a kv => ψ kv.1 (a kv)) (fun a => funext fun kv => hψinv kv.1 (a kv))
  have hΦ : ∀ a kv, Φ a kv = ψ kv.1 (a kv) := fun _ _ => rfl
  let good : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → Prop :=
    fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))
  let T : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun a =>
    if good a then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)
    else 0
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a, T a := rfl

  have hgood : ∀ a, (∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0) → good a → good (Φ a) := by
    intro a ha h
    simp only [good] at h ⊢
    unfold NTypes.goodTuple at h ⊢
    intro k
    have hf : (fun v => Formalism.CyclotomicNorms.monicOf (Φ a ⟨k, v⟩)) = fun v => dl (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) :=
      funext fun v => hψm k _ (ha ⟨k, v⟩)
    have h1 := good_dl _ _ (h k).1
    have h2 := good_dl _ _ (h k).2
    simp only [inv_inv] at h1 h2
    simp only [hf]
    exact ⟨h2, h1⟩

  have hzero : ∀ a, ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 = 0 → T a = 0 := by
    intro a kv h0
    simp only [T]
    split_ifs
    · refine Finset.prod_eq_zero (Finset.mem_univ kv) ?_
      rw [D.ntypes.eSer_zero _ _ (fun h => h.2.2 h0)]
      first
        | rfl
        | simp
    · rfl
  have key : ∀ a, star (T a) = T (Φ a) := by
    intro a
    by_cases hz : ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0
    · have hz' : ∀ kv, (Formalism.CyclotomicNorms.monicOf (Φ a kv)).coeff 0 ≠ 0 := fun kv => hψc _ _ (hz kv)
      have hiff : good (Φ a) ↔ good a := by
        refine ⟨fun h => ?_, hgood a hz⟩
        have := hgood (Φ a) hz' h
        have e : Φ (Φ a) = a := funext fun kv => hψinv kv.1 (a kv)
        rwa [e] at this
      simp only [T, hiff]
      split_ifs
      · rw [star_prod]
        refine Finset.prod_congr rfl fun kv _ => ?_
        rw [hS kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) (Formalism.CyclotomicNorms.Sqf.monic_monicOf _) (hz kv), hΦ, hψm _ _ (hz kv)]
        rfl
      · exact star_zero _
    · push_neg at hz
      obtain ⟨kv, h0⟩ := hz
      rw [hzero a kv h0, hzero (Φ a) kv (by rw [hΦ, hψ0 _ _ h0]; exact h0), star_zero]
  have hfin : (Function.support T).Finite := Set.toFinite _
  have hstar : star (∑ᶠ a, T a) = ∑ᶠ a, star (T a) := by
    have := map_finsum (starAddEquiv (R := ℂ)) hfin
    simpa only [starAddEquiv_apply] using this
  rw [he, hstar]
  simp_rw [key]
  exact finsum_comp_equiv Φ

end GlobalTheory.GoodIdemReal
end

