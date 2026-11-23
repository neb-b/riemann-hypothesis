module

public import Mathlib
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModLThreeCocycleCondition
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicCocycleLift

variable {l : ℕ} [Fact l.Prime]

theorem toZModPow_eq_zero_iff (r : ℕ) (x : ℤ_[l]) :
    PadicInt.toZModPow r x = 0 ↔ (l : ℤ_[l]) ^ r ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

theorem continuous_toZModPow (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) ?_
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  refine ContinuousAt.congr (f := fun _ => (0 : ZMod (l ^ r))) continuousAt_const ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow] at hx
  exact hx.symm

theorem exists_continuous_div {X : Type*} [TopologicalSpace X] (f : X → ℤ_[l]) (hf : Continuous f)
    (a : ℤ_[l]) (ha : a ≠ 0) (hd : ∀ x, a ∣ f x) :
    ∃ c : X → ℤ_[l], Continuous c ∧ ∀ x, f x = a * c x := by
  choose c hc using hd
  refine ⟨c, ?_, hc⟩
  have ha' : (a : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 ha
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ c : X → ℚ_[l]) = fun x => (a : ℚ_[l])⁻¹ * (f x : ℚ_[l]) := by
    funext x
    rw [hc x, PadicInt.coe_mul, inv_mul_cancel_left₀ ha']
    rfl
  have h2 : Continuous fun x => (a : ℚ_[l])⁻¹ * (f x : ℚ_[l]) :=
    continuous_const.mul (continuous_subtype_val.comp hf)
  rw [← e] at h2
  exact h2

theorem exists_continuous_lift {X : Type*} [TopologicalSpace X] (r : ℕ) (f : X → ZMod (l ^ r))
    (hf : Continuous f) :
    ∃ F : X → ℤ_[l], Continuous F ∧ ∀ x, PadicInt.toZModPow r (F x) = f x := by
  have hs : Function.Surjective (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) :=
    ZMod.ringHom_surjective _
  exact ⟨fun x => Function.surjInv hs (f x),
    (continuous_of_discreteTopology (f := Function.surjInv hs)).comp hf,
    fun x => Function.surjInv_eq hs _⟩

variable {Γ : Type} [Group Γ]

noncomputable def dTwo (χ : Γ → ℤ_[l]) (u : Γ × Γ → ℤ_[l]) (p : Γ × Γ × Γ) : ℤ_[l] :=
  χ p.1 * u (p.2.1, p.2.2) - u (p.1 * p.2.1, p.2.2) + u (p.1, p.2.1 * p.2.2) - u (p.1, p.2.1)

def IsCocycleThree (χ : Γ → ℤ_[l]) (c : Γ × Γ × Γ → ℤ_[l]) : Prop :=
  ∀ g h k m, χ g * c (h, k, m) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m)
    + c (g, h, k) = 0

theorem isCocycleThree_dTwo (χ : Γ → ℤ_[l]) (hχ : ∀ g h, χ (g * h) = χ g * χ h)
    (u : Γ × Γ → ℤ_[l]) : IsCocycleThree χ (dTwo χ u) := by
  intro g h k m
  simp only [dTwo, hχ, mul_assoc]
  ring

theorem IsCocycleThree.sub {χ : Γ → ℤ_[l]} {c c' : Γ × Γ × Γ → ℤ_[l]} (hc : IsCocycleThree χ c)
    (hc' : IsCocycleThree χ c') : IsCocycleThree χ (fun p => c p - c' p) := by
  intro g h k m
  linear_combination hc g h k m - hc' g h k m

theorem IsCocycleThree.cancel {χ : Γ → ℤ_[l]} {c c' : Γ × Γ × Γ → ℤ_[l]} (hc : IsCocycleThree χ c)
    {a : ℤ_[l]} (ha : a ≠ 0) (e : ∀ p, c p = a * c' p) : IsCocycleThree χ c' := by
  intro g h k m
  have := hc g h k m
  simp only [e] at this
  apply mul_left_cancel₀ ha
  linear_combination this

variable [TopologicalSpace Γ] [ContinuousMul Γ]

theorem continuous_dTwo {χ : Γ → ℤ_[l]} (hχ : Continuous χ) {u : Γ × Γ → ℤ_[l]}
    (hu : Continuous u) : Continuous (dTwo χ u) := by
  unfold dTwo
  fun_prop


omit [ContinuousMul Γ] in
theorem exists_dTwo_eq (χ : Γ → ℤ_[l])
    (step : ∀ c : Γ × Γ × Γ → ℤ_[l], Continuous c → IsCocycleThree χ c →
      ∃ u c', Continuous u ∧ Continuous c' ∧ IsCocycleThree χ c' ∧
        ∀ p, c p = dTwo χ u p + l * c' p)
    (c : Γ × Γ × Γ → ℤ_[l]) (hc : Continuous c) (hz : IsCocycleThree χ c) :
    ∃ u, Continuous u ∧ ∀ p, c p = dTwo χ u p := by
  choose U C hU hC hCz hE using step
  let T := {c : Γ × Γ × Γ → ℤ_[l] // Continuous c ∧ IsCocycleThree χ c}
  let nx : T → T := fun t => ⟨C t.1 t.2.1 t.2.2, hC _ _ _, hCz _ _ _⟩
  let s : ℕ → T := fun n => nx^[n] ⟨c, hc, hz⟩
  let u : ℕ → Γ × Γ → ℤ_[l] := fun n => U (s n).1 (s n).2.1 (s n).2.2
  have hu : ∀ n, Continuous (u n) := fun n => hU _ _ _
  have hs : ∀ n p, (s n).1 p = dTwo χ (u n) p + l * (s (n + 1)).1 p := by
    intro n p
    have : s (n + 1) = nx (s n) := Function.iterate_succ_apply' _ _ _
    rw [this]
    exact hE _ _ _ p
  have hn : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hb : ∀ (n : ℕ) (x : ℤ_[l]), ‖(l : ℤ_[l]) ^ n * x‖ ≤ ‖(l : ℤ_[l])‖ ^ n := by
    intro n x
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) x.norm_le_one
  have hg : Summable fun n : ℕ => ‖(l : ℤ_[l])‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hn
  have hsum : ∀ x : ℕ → ℤ_[l], Summable fun n => (l : ℤ_[l]) ^ n * x n := fun x =>
    Summable.of_norm_bounded hg fun n => hb n _
  refine ⟨fun q => ∑' n, (l : ℤ_[l]) ^ n * u n q,
    continuous_tsum (fun n => continuous_const.mul (hu n)) hg fun n q => hb n _, fun p => ?_⟩
  have h1 : HasSum (fun n => (l : ℤ_[l]) ^ n * dTwo χ (u n) p)
      (dTwo χ (fun q => ∑' n, (l : ℤ_[l]) ^ n * u n q) p) := by
    have := ((((hsum fun n => u n (p.2.1, p.2.2)).hasSum.mul_left (χ p.1)).sub
      (hsum fun n => u n (p.1 * p.2.1, p.2.2)).hasSum).add
      (hsum fun n => u n (p.1, p.2.1 * p.2.2)).hasSum).sub
      (hsum fun n => u n (p.1, p.2.1)).hasSum
    have e : (fun n => (l : ℤ_[l]) ^ n * dTwo χ (u n) p) = fun n =>
        χ p.1 * ((l : ℤ_[l]) ^ n * u n (p.2.1, p.2.2)) - (l : ℤ_[l]) ^ n * u n (p.1 * p.2.1, p.2.2)
          + (l : ℤ_[l]) ^ n * u n (p.1, p.2.1 * p.2.2) - (l : ℤ_[l]) ^ n * u n (p.1, p.2.1) := by
      funext n
      simp only [dTwo]
      ring
    rw [e]
    exact this
  have h2 : ∀ N, ∑ n ∈ Finset.range N, (l : ℤ_[l]) ^ n * dTwo χ (u n) p
      = c p - (l : ℤ_[l]) ^ N * (s N).1 p := by
    intro N
    induction N with
    | zero => simp [s]
    | succ N ih => rw [Finset.sum_range_succ, ih, hs N p]; ring
  have h3 := h1.tendsto_sum_nat
  simp only [h2] at h3
  have h4 := (tendsto_const_nhds (x := c p)).sub (hsum fun n => (s n).1 p).tendsto_atTop_zero
  rw [sub_zero] at h4
  exact tendsto_nhds_unique h4 h3

theorem twoCocycle_lift : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (ρ1 : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g x, PadicInt.toZModPow 1 (ρ g x) = ρ1 g (PadicInt.toZModPow 1 x)) → (∀ c : Γ × Γ × Γ → ZMod (l ^ 1), Continuous c → (∀ g h k m, ρ1 g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → ZMod (l ^ 1), Continuous u ∧ ∀ g h k, ρ1 g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k)) → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ y ∈ Z2 ρr, ∃ z ∈ Z2 ρ, ∀ p, PadicInt.toZModPow r (z p) = y p := by
  intro l _ Γ _ _ _ ρ hρ ρ1 h1 H3 r ρr hr y hy
  set χ : Γ → ℤ_[l] := fun g => ρ g 1 with hχdef
  have hρχ : ∀ g x, ρ g x = χ g * x := by
    intro g x
    have := map_smul (ρ g) x 1
    rw [smul_eq_mul, mul_one, smul_eq_mul] at this
    rw [this, mul_comm]
  have hχm : ∀ g h, χ (g * h) = χ g * χ h := by
    intro g h
    rw [← hρχ]
    simp only [hχdef, map_mul, Module.End.mul_apply]
  have hχc : Continuous χ := hρ.comp (continuous_id.prodMk continuous_const)
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have step : ∀ c : Γ × Γ × Γ → ℤ_[l], Continuous c → IsCocycleThree χ c →
      ∃ u c', Continuous u ∧ Continuous c' ∧ IsCocycleThree χ c' ∧
        ∀ p, c p = dTwo χ u p + l * c' p := by
    intro c hc hz
    obtain ⟨v, hv, hvc⟩ := H3 (fun p => PadicInt.toZModPow 1 (c p))
      ((continuous_toZModPow 1).comp hc) (by
        intro g h k m
        have := congrArg (PadicInt.toZModPow 1) (hz g h k m)
        rw [← hρχ] at this
        simpa only [map_add (f := _), map_sub, h1, map_zero] using this)
    obtain ⟨u, hu, huv⟩ := exists_continuous_lift 1 v hv
    obtain ⟨c', hc', e⟩ := exists_continuous_div (fun p => c p - dTwo χ u p)
      (hc.sub (continuous_dTwo hχc hu)) l hl0 (by
        rintro ⟨g, h, k⟩
        rw [← pow_one (l : ℤ_[l]), ← toZModPow_eq_zero_iff]
        simp only [dTwo, ← hρχ, map_add (f := _), map_sub, h1, huv, hvc, sub_self])
    exact ⟨u, c', hu, hc', (hz.sub (isCocycleThree_dTwo χ hχm u)).cancel hl0 e,
      fun p => by linear_combination e p⟩
  obtain ⟨Y, hY, hYy⟩ := exists_continuous_lift r y hy.1
  obtain ⟨c, hc, e⟩ := exists_continuous_div (dTwo χ Y) (continuous_dTwo hχc hY)
    ((l : ℤ_[l]) ^ r) (pow_ne_zero _ hl0) (by
      rintro ⟨g, h, k⟩
      rw [← toZModPow_eq_zero_iff]
      simp only [dTwo, ← hρχ, map_add (f := _), map_sub, hr, hYy]
      exact hy.2 g h k)
  obtain ⟨u, hu, hcu⟩ := exists_dTwo_eq χ step c hc
    ((isCocycleThree_dTwo χ hχm Y).cancel (pow_ne_zero _ hl0) e)
  refine ⟨fun p => Y p - (l : ℤ_[l]) ^ r * u p,
    ⟨hY.sub (continuous_const.mul hu), fun g h k => ?_⟩, fun p => ?_⟩
  · have e1 := e (g, h, k)
    rw [hcu] at e1
    simp only [dTwo] at e1
    rw [hρχ]
    linear_combination e1
  · rw [map_sub, hYy, (toZModPow_eq_zero_iff r _).2 (dvd_mul_right _ _), sub_zero]

end GlobalTheory.PadicCocycleLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PacketSumSignCastNeZero
section
open Finset

namespace GlobalTheory

lemma packetSum_vdm_eq_det {r : ℕ} (β : Fin r → ℂ) :
    Formalism.PacketSums.vdm β = (∏ i : Fin r, ∏ _j ∈ Ioi i, (-1 : ℂ)) * (Matrix.vandermonde β).det := by
  rw [Matrix.det_vandermonde, ← Finset.prod_mul_distrib]
  unfold Formalism.PacketSums.vdm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  have : Finset.univ.filter (fun j => i < j) = Ioi i := by ext; simp
  rw [this]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

lemma packetSum_vdm_perm {r : ℕ} (α : Fin r → ℂ) (σ : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.vdm (fun i => α (σ i)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * Formalism.PacketSums.vdm α := by
  rw [packetSum_vdm_eq_det, packetSum_vdm_eq_det]
  have : Matrix.vandermonde (fun i => α (σ i)) = (Matrix.vandermonde α).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [this, Matrix.det_permute]
  ring

lemma packetSum_sign_cast_ne_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma packetSum_numK_perm {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK]
    (μ : Fin r → ℤ) (α : Fin r → ℂ) (y : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) =
      ((Equiv.Perm.sign y : ℤ) : ℂ) * ∑ w : WK,
        ((Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) : ℤ) : ℂ) *
          ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
  unfold Formalism.PacketSums.numK
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hp : ∏ i, α (y⁻¹ i) ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i) =
      ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
    rw [← Equiv.prod_comp y]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]
  rw [hp, ← mul_assoc]
  congr 1
  have hs : Equiv.Perm.sign (w : Equiv.Perm (Fin r)) =
      Equiv.Perm.sign y * Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [hs]; push_cast; ring

theorem packetSum : Formalism.PacketSums.PacketSum := by
  intro r WK _ T hbij μ α _ _
  set f : Equiv.Perm (Fin r) → ℂ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, α j ^ μ (σ⁻¹ j) with hf
  have hterm : ∀ y : Equiv.Perm (Fin r),
      Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α (y⁻¹ i)) =
        (∑ w : WK, f (y⁻¹ * (w : Equiv.Perm (Fin r)))) / Formalism.PacketSums.vdm α := by
    intro y
    rw [packetSum_numK_perm, packetSum_vdm_perm α y⁻¹, Equiv.Perm.sign_inv,
      mul_div_mul_left _ _ (packetSum_sign_cast_ne_zero y)]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_coe_sort T]
  rw [← Fintype.sum_bijective _ hbij (fun p : WK × T => f ((p.2 : Equiv.Perm (Fin r))⁻¹ * p.1)) f
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicH2Separated

theorem toZModPow_eq_iff {l : ℕ} [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    PadicInt.toZModPow r x = PadicInt.toZModPow r y ↔ ‖x - y‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero]

theorem continuous_reduction {l : ℕ} [Fact l.Prime] (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 (fun x => ?_) |>.continuous
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hl] with y hy
  rw [toZModPow_eq_iff]
  simpa [dist_eq_norm] using hy

theorem continuous_of_reductions {l : ℕ} [Fact l.Prime] {X : Type} [TopologicalSpace X]
    (b : X → ℤ_[l]) (hb : ∀ s : ℕ, Continuous fun x => PadicInt.toZModPow (s + 1) (b x)) :
    Continuous b := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  have hk' : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_le_zpow_right₀ h1 (by push_cast; omega)
  have hlc := ((IsLocallyConstant.iff_continuous _).2 (hb k)).eventually_eq x
  filter_upwards [hlc] with y hy
  rw [toZModPow_eq_iff] at hy
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hy.trans hk') hk

theorem finite_cocycles_compact_ultrametric_rep {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [Finite M] (rho : Representation R G M) [Finite (H1 rho)] : Finite (Z1 rho) := by
  have hB : Finite (B1 rho) :=
    Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (d0 rho))
  have hB' : Finite ((B1 rho).comap (Z1 rho).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 rho)) (fun x y h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun t : B1 rho => (t : G → M)) h)
  have h1 : Finite ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup := hB'
  have h2 : Finite (Z1 rho ⧸ ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup) :=
    inferInstanceAs (Finite (H1 rho))
  exact Finite.of_addSubgroup_quotient ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup

theorem finite_primitives {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [Finite M] (rho : Representation R G M) [Finite (H1 rho)]
    (z : G × G → M) : {β : G → M | Continuous β ∧ d1 rho β = z}.Finite := by
  rcases Set.eq_empty_or_nonempty {β : G → M | Continuous β ∧ d1 rho β = z} with h | ⟨c, hc⟩
  · rw [h]; exact Set.finite_empty
  have hZ : (Z1 rho : Set (G → M)).Finite := finite_cocycles_compact_ultrametric_rep rho
  refine (hZ.image (fun f => f + c)).subset ?_
  rintro β ⟨hβ, hd⟩
  refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
  have e : d1 rho (β - c) (g, h) = 0 := by rw [map_sub, hd, hc.2, sub_self]; rfl
  rw [d1_apply] at e
  have : (β - c) g + rho g ((β - c) h) - (β - c) (g * h) = 0 := by rw [← e]; abel
  exact (sub_eq_zero.1 this).symm

theorem mem_coboundaries_of_forall_pow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (ρr : ∀ r : ℕ, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x)) → (∀ r, 0 < r → Finite (H1 (ρr r))) → ∀ z ∈ Z2 ρ, (∀ r : ℕ, ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ) → z ∈ B2 ρ := by
  intro l _ Γ _ _ ρ ρr hρ hfin z _ hz
  have hd : ∀ (s : ℕ) (b : Γ → ℤ_[l]), d1 (ρr s) (fun g => PadicInt.toZModPow s (b g)) =
      fun p => PadicInt.toZModPow s (d1 ρ b p) := by
    intro s b
    funext ⟨g, h⟩
    simp only [d1_apply, map_add (f := _), map_sub, hρ]
  let α : ∀ s : ℕ, Set (Γ → ZMod (l ^ s)) := fun s =>
    {β | Continuous β ∧ d1 (ρr s) β = fun p => PadicInt.toZModPow s (z p)}
  have hα : ∀ s, (α (s + 1)).Finite := by
    intro s
    haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    haveI := hfin (s + 1) (Nat.succ_pos s)
    exact finite_primitives (ρr (s + 1)) _
  let T : ℕ → Set (Γ → ℤ_[l]) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : Γ → ℤ_[l]) g => PadicInt.toZModPow (s + 1) (b g)) ⁻¹' α (s + 1)
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_reduction _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨w, -, c, hc, hcd⟩ := hz (r + 1)
    refine ⟨c, Set.mem_iInter₂.2 fun s hs => ⟨(continuous_reduction _).comp hc, ?_⟩⟩
    rw [hd, hcd]
    funext p
    have h0 : PadicInt.toZModPow (s + 1) ((l : ℤ_[l]) ^ (r + 1)) = 0 := by
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow _ (by omega)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, h0, zero_mul, sub_zero]
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => PadicInt.toZModPow (s + 1) (b g)) ∈ α (s + 1) := fun s =>
    Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  refine ⟨b, continuous_of_reductions b fun s => (hb' s).1, ?_⟩
  funext p
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := (hb' n).2
    rw [hd] at this
    exact congrFun this p

end GlobalTheory.PadicH2Separated
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntLengthEqOfCardQuotientEqCardSubmodule
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem card_residueField_padicInt (l : ℕ) [Fact l.Prime] :
    Nat.card (IsLocalRing.ResidueField ℤ_[l]) = l := by
  rw [Nat.card_congr (PadicInt.residueField (p := l)).toEquiv, Nat.card_zmod]

theorem padicInt_length_eq_top_of_infinite (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X]
    [Module ℤ_[l] X] (h : ¬ Finite X) : Module.length ℤ_[l] X = ⊤ := by
  by_contra hne
  obtain ⟨n, -, hc⟩ := exists_length_eq_and_card_eq_pow_of_isFiniteLength ℤ_[l] X
    (Module.length_ne_top_iff.mp hne)
  rw [card_residueField_padicInt] at hc
  exact h (Nat.finite_of_card_ne_zero (by
    rw [hc]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero))

theorem padicInt_length_eq_of_card_eq (l : ℕ) [Fact l.Prime] (X Y : Type) [AddCommGroup X]
    [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y] [Finite X] [Finite Y]
    (h : Nat.card X = Nat.card Y) : Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  obtain ⟨n, hn, hc⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] X
  obtain ⟨m, hm, hd⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] Y
  rw [card_residueField_padicInt] at hc hd
  have : n = m := Nat.pow_right_injective (Fact.out : l.Prime).two_le (by
    simp only; rw [← hc, ← hd, h])
  rw [hn, hm, this]

theorem padicInt_length_eq_of_card_quotient_eq_card_submodule (l : ℕ) [Fact l.Prime] (X Y : Type)
    [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y]
    (N : ℕ → Submodule ℤ_[l] X) (P : ℕ → Submodule ℤ_[l] Y) (c : ℕ) (hN : Antitone N)
    (hsep : ∀ x, (∀ r, x ∈ N r) → x = 0) (hP : Monotone P) (hex : ∀ y, ∃ r, y ∈ P r)
    (hc : ∀ r, c ≤ r → Finite (P r) ∧ Nat.card (X ⧸ N r) = Nat.card (P r)) :
    Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  have key : ∀ r0, c ≤ r0 → (∀ r, r0 ≤ r → Nat.card (P r) ≤ Nat.card (P r0)) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro r0 h0 hb
    have hfin : ∀ r, c ≤ r → Finite (X ⧸ N r) := fun r hr => by
      have := (hc r hr).1
      exact Nat.finite_of_card_ne_zero (by rw [(hc r hr).2]; exact Nat.card_pos.ne')
    have hPtop : P r0 = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨r, hr⟩ := hex y
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := (hc _ (h0.trans hle)).1
      have hbij : Function.Bijective (Submodule.inclusion (hP hle)) :=
        (Submodule.inclusion_injective _).bijective_of_nat_card_le (hb _ hle)
      obtain ⟨z, hz⟩ := hbij.2 ⟨y, hP (le_max_left r r0) hr⟩
      have : (z : Y) = y := congrArg Subtype.val hz
      exact this ▸ z.2
    have hNbot : N r0 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      refine (Submodule.mem_bot _).mpr (hsep x fun r => ?_)
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := hfin _ (h0.trans hle)
      have hbij : Function.Bijective (Submodule.factor (hN hle)) :=
        (Submodule.factor_surjective _).bijective_of_nat_card_le (by
          rw [(hc _ (h0.trans hle)).2, (hc _ h0).2]; exact hb _ hle)
      have h1 : (N (max r r0)).mkQ x = 0 := hbij.1 (by
        rw [map_zero, Submodule.factor_mk]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hx)
      exact hN (le_max_left r r0) ((Submodule.Quotient.mk_eq_zero _).mp h1)
    have eX : (X ⧸ N r0) ≃ₗ[ℤ_[l]] X := Submodule.quotEquivOfEqBot _ hNbot
    have eY : (P r0) ≃ₗ[ℤ_[l]] Y := LinearEquiv.ofTop _ hPtop
    have := hfin _ h0
    have := (hc _ h0).1
    rw [← eX.length_eq, ← eY.length_eq]
    exact padicInt_length_eq_of_card_eq l _ _ (hc _ h0).2
  have bdd : ∀ B : ℕ, (∀ r, c ≤ r → Nat.card (P r) ≤ B) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro B hB
    have hS : ((fun r => Nat.card (P r)) '' {r | c ≤ r}).Finite :=
      (Set.finite_le_nat B).subset (by rintro _ ⟨r, hr, rfl⟩; exact hB r hr)
    obtain ⟨_, ⟨r0, hr0, rfl⟩, hmax⟩ := Set.exists_max_image _ id hS ⟨_, c, le_refl c, rfl⟩
    exact key r0 hr0 fun r hr => hmax _ ⟨r, le_trans hr0 hr, rfl⟩
  by_cases hX : Finite X
  · refine bdd (Nat.card X) fun r hr => ?_
    rw [← (hc r hr).2]
    exact Nat.card_le_card_of_surjective _ (N r).mkQ_surjective
  by_cases hY : Finite Y
  · exact bdd (Nat.card Y) fun r _ =>
      Nat.card_le_card_of_injective _ (P r).subtype_injective
  rw [padicInt_length_eq_top_of_infinite l X hX, padicInt_length_eq_top_of_infinite l Y hY]

end GlobalTheory
end

