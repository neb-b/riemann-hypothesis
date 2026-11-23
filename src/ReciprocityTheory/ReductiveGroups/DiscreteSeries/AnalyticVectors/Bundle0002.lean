module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Growth
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem actM_mem_layer_succ (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k) :
    actM E X x ∈ layer ε E V (k + 1) := by
  unfold actM
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (apply_mem_layer_succ hE hV a b hx)

theorem sqrt_sub_le_add {y d : ℝ} (hy : 0 ≤ y) : √(y ^ 2 - d) ≤ y + √(max 0 (-d)) := by
  have hs := Real.sqrt_nonneg (max 0 (-d))
  have hs2 : √(max 0 (-d)) ^ 2 = max 0 (-d) := Real.sq_sqrt (le_max_left _ _)
  have hm : -d ≤ max 0 (-d) := le_max_right _ _
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith

theorem norm_actM_le {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k) :
    ‖actM E X x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
  set f : Fin n × Fin n → ℝ := fun p => ‖X p.1 p.2‖ with hf
  set g : Fin n × Fin n → ℝ := fun p => if ε p.1 ≠ ε p.2 then ‖E p.1 p.2 x‖ else 0 with hg
  have h1 : ‖actM E X x‖ ≤ ∑ p : Fin n × Fin n, f p * g p := by
    unfold actM
    rw [LinearMap.sum_apply, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [LinearMap.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [LinearMap.smul_apply, norm_smul]
    by_cases hab : ε a = ε b
    · simp [hf, hg, hab, inP_apply_eq_zero hX hab]
    · simp [hf, hg, hab]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin n × Fin n)) f g
  have hfs : ∑ p : Fin n × Fin n, f p ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hgs : ∑ p : Fin n × Fin n, g p ^ 2 =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : ε a = ε b <;> simp [hg, hab]
  rw [hfs, hgs] at h2
  set y : ℝ := R + √2 * k with hy
  have hy0 : 0 ≤ y := by positivity
  have h3 : √(∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2) ≤
      (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
    calc _ ≤ √((y ^ 2 - d) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hR k x hx)
      _ ≤ √(max 0 (y ^ 2 - d)) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (le_max_left _ _),
            Real.sqrt_sq (norm_nonneg x)]
          exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      _ ≤ (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          have := sqrt_sub_le_add (d := d) hy0
          rcases le_total 0 (y ^ 2 - d) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h, Real.sqrt_zero]; positivity
  calc ‖actM E X x‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * ((R + √(max 0 (-d)) + √2 * k) * ‖x‖) :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem actM_pow_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) : ((actM E X) ^ m) x ∈ layer ε E V (k + m) := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact actM_mem_layer_succ hE hV hX ih

theorem norm_actM_pow_le (hE : IsGlRep E) (hV : IsKStableSub ε E V) {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) :
    ‖((actM E X) ^ m) x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
      (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := norm_actM_le hR0 hR hX (k + m) (actM_pow_mem_layer hE hV hX hx m)
    have hc : 0 ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) := by
      positivity
    calc _ ≤ _ := h
      _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) *
          (√(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
            (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = _ := by
          rw [Finset.prod_range_succ, pow_succ]
          push_cast
          ring

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.IteratedDerivOrbit
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem norm_orbit_apply (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (t : ℝ) (w : H) : ‖σ (NormedSpace.exp ((t : ℂ) • X)) w‖ = ‖w‖ :=
  hσ.2.1 _ (exp_smul_mem_UJset hX t) w

theorem hasDerivAt_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) ((actM E X v : D) : H)) t := by

  have key : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) (v : H)) := by
    funext s
    have hc : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
      ((Commute.refl X).smul_left _).smul_right _
    have hsum : ((s : ℂ) • X) = (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X := by
      rw [← add_smul]; congr 1; push_cast; ring
    rw [hsum, Matrix.exp_add_of_commute _ _ hc,
      hσ.1.2 _ (exp_smul_mem_UJset hX t) _ (exp_smul_mem_UJset hX (s - t))]
    rfl
  rw [key]
  have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H))
      ((actM E X v : D) : H) (t - t) := by
    rw [sub_self]; exact hD.deriv X hX v
  have h1 := HasDerivAt.comp_sub_const t t h0
  exact ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1

theorem iteratedDeriv_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).deriv, pow_succ', Module.End.mul_apply]

theorem contDiff_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_orbit hσ hD hX v m]
  exact fun t => (hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).differentiableAt

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.LayerSpan
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def layerWtVecs (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (k : ℕ) : Set M :=
  {w | ∃ ν ω : Fin n → ℝ, ∃ j ≤ k, IsNCSum ε j ω ∧
    (∃ v ∈ V, v ≠ 0 ∧ ∀ a, E a a v = (ν a : ℂ) • v) ∧ ∀ a, E a a w = ((ν + ω) a : ℂ) • w}

theorem isNCSum_add_root {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω) {a b : Fin n}
    (hab : ε a ≠ ε b) : IsNCSum ε (j + 1) (ω + root a b) := by
  obtain ⟨γ, hγ, rfl⟩ := hω
  refine ⟨Fin.snoc (α := fun _ => Fin n × Fin n) γ (a, b), fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hab
    · simpa using hγ i
  · rw [Fin.sum_univ_castSucc]
    simp

theorem diag_apply_of_weight (hE : IsGlRep E) {ω : Fin n → ℝ} {w : M}
    (hw : ∀ c, E c c w = (ω c : ℂ) • w) (a b c : Fin n) :
    E c c (E a b w) = ((ω + root a b) c : ℂ) • E a b w := by
  have h := congrArg (fun T : Module.End ℂ M => T w) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h2 : E c c (E a b w) = E a b (E c c w) +
      ((if c = a then E c b else 0) w - (if b = c then E a c else 0) w) := by
    rw [← h]
    abel
  have e1 : (if c = a then E c b else 0) w = ((if c = a then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : c = a
    · subst h'
      simp
    · simp [h']
  have e2 : (if b = c then E a c else 0) w = ((if c = b then 1 else 0 : ℝ) : ℂ) • E a b w := by
    by_cases h' : b = c
    · subst h'
      simp
    · simp [h', Ne.symm h']
  rw [h2, hw c, map_smul, e1, e2]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  module

theorem le_span_weightVecs (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    V ≤ Submodule.span ℂ {v | v ∈ V ∧ ∃ ν : Fin n → ℝ, ∀ a, E a a v = (ν a : ℂ) • v} := by
  haveI := hVf
  have hst : ∀ a, ∀ v ∈ V, E a a v ∈ V := fun a v hv => hVK a a rfl v hv
  let T : Fin n → Module.End ℂ V := fun a => (E a a).restrict (hst a)
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a
    refine LinearMap.IsSymmetric.restrict_invariant (T := E a a) (fun x y => ?_) (hst a)
    rw [hU a a x y]
    simp [adjSign]
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a c _
    have h := hE a a c c
    have hEc : E a a * E c c = E c c * E a a := by
      rw [← sub_eq_zero, h]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Ne.symm hac]
    show T a * T c = T c * T a
    refine LinearMap.ext fun v => Subtype.ext ?_
    show E a a (E c c v) = E c c (E a a v)
    exact congrArg (fun F : Module.End ℂ M => F (v : M)) hEc
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  intro x hx
  have hy : (⟨x, hx⟩ : V) ∈ ⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  show ((⟨x, hx⟩ : V) : M) ∈ _
  refine Submodule.iSup_induction _ (motive := fun y : V => (y : M) ∈ Submodule.span ℂ _) hy ?_ ?_ ?_
  · intro χ y hy
    rw [Submodule.mem_iInf] at hy
    by_cases hy0 : y = 0
    · subst hy0
      exact Submodule.zero_mem _
    · have hreal : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := by
        intro a
        have hev : Module.End.HasEigenvalue (T a) (χ a) := by
          first
            | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hy a, hy0⟩
            | exact (Submodule.ne_bot_iff _).2 ⟨y, hy a, hy0⟩
        exact Complex.conj_eq_iff_re.1 ((hsym a).conj_eigenvalue_eq_self hev)
      refine Submodule.subset_span ⟨y.2, fun a => (χ a).re, fun a => ?_⟩
      have h := Module.End.mem_eigenspace_iff.1 (hy a)
      have h' := congrArg Subtype.val h
      simp only [T, LinearMap.restrict_coe_apply, Submodule.coe_smul] at h'
      rw [h', hreal a]
  · exact Submodule.zero_mem _
  · intro y z hy hz
    simpa using Submodule.add_mem _ hy hz

theorem layerWtVecs_mono {k l : ℕ} (h : k ≤ l) : layerWtVecs ε E V k ⊆ layerWtVecs ε E V l := by
  rintro w ⟨ν, ω, j, hj, hω, hv, hw⟩
  exact ⟨ν, ω, j, hj.trans h, hω, hv, hw⟩

theorem layer_le_span (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) (k : ℕ) :
    layer ε E V k ≤ Submodule.span ℂ (layerWtVecs ε E V k) := by
  induction k with
  | zero =>
    refine (le_span_weightVecs hE hU hVf hVK).trans (Submodule.span_le.2 fun w hw => ?_)
    obtain ⟨hwV, ν, hν⟩ := hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨ν, 0, 0, le_refl 0, ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩,
        ⟨w, hwV, hw0, hν⟩, fun a => by simpa using hν a⟩
  | succ k ih =>
    show layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b) ≤ _
    refine sup_le (ih.trans (Submodule.span_mono (layerWtVecs_mono (Nat.le_succ k))))
      (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
    refine (Submodule.map_mono ih).trans ?_
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨w, ⟨ν, ω, j, hj, hω, hv, hw⟩, rfl⟩
    refine ⟨ν, ω + root a b, j + 1, by omega, isNCSum_add_root hω hab, hv, fun c => ?_⟩
    rw [diag_apply_of_weight hE hw a b c, add_assoc]

end Unitary

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_add' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, mul_smul]

theorem inner_map_map_of_isURep (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y := by
  unfold IsURepOn at hσ
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.2.1 g hg }
  exact L.inner_map_map x y

theorem inner_actM_add_inner_actM (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v w : D) :
    inner ℂ (actM E X v) w + inner ℂ v (actM E X w) = 0 := by
  have hσ' := hσ
  unfold IsURepOn at hσ'
  obtain ⟨-, -, hder⟩ := hD
  have hd := (hder X hX v).inner ℂ (hder X hX w)
  have hc : HasDerivAt (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
      ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) 0 0 := by
    have e : (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
        ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) = fun _ => inner ℂ (v : H) (w : H) := by
      funext t
      exact inner_map_map_of_isURep hσ (exp_smul_mem_UJset hX t) _ _
    rw [e]
    exact hasDerivAt_const _ _
  have h0 := hd.unique hc
  simp [hσ'.1.1] at h0
  first
    | (rw [Submodule.coe_inner, Submodule.coe_inner]; linear_combination h0)
    | (simpa [add_comm] using h0)

theorem actM_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) : actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_smul]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  ext i j
  simp [Jm, Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;> split_ifs <;> simp_all

theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  ext i j
  simp [Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem Jm_mul_Jm_mul (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * X) = X := by
  rw [← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem inG_sub_theta (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (M - Jm ε * Mᴴ * Jm ε) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_Jm,
    Jm_mul_Jm_mul, Matrix.mul_one] <;> abel

theorem inG_add_theta (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
  unfold inG
  have hs : star (-Complex.I) = Complex.I := by simp
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Jm_mul_Jm, Jm_mul_Jm_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  rw [hs, neg_smul, smul_add, smul_add]
  abel

theorem inner_actM_eq (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (M : Matrix (Fin n) (Fin n) ℂ) (x y : D) :
    inner ℂ (actM E M x) y = inner ℂ x (actM E (Jm ε * Mᴴ * Jm ε) y) := by
  have skA := inner_actM_add_inner_actM hσ hD (inG_sub_theta ε M) x y
  have skB := inner_actM_add_inner_actM hσ hD (inG_add_theta ε M) x y
  have hc : Complex.I / 2 * -Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, mul_neg, Complex.I_mul_I]
    norm_num
  have hM : M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  have hT : Jm ε * Mᴴ * Jm ε = (-(1 / 2) : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  rw [hT]
  conv_lhs => rw [hM]
  rw [actM_add', actM_add', actM_smul' E (1 / 2 : ℂ), actM_smul' E (-(1 / 2) : ℂ),
    actM_smul' E (Complex.I / 2)]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_div₀, map_one, map_ofNat, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * skA - (Complex.I / 2) * skB

theorem theta_single (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = adjSign ε a b • Matrix.single b a 1 := by
  ext i j
  simp [Jm, adjSign, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply] <;> split_ifs <;> simp_all

theorem isInfUnitary_of_isDerivedOn (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) :
    IsInfUnitary ε E := by
  unfold IsInfUnitary
  intro a b v w
  rw [← actM_single' E a b, inner_actM_eq hσ hD, theta_single, actM_smul', actM_single']
  rw [LinearMap.smul_apply, inner_smul_right]

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

