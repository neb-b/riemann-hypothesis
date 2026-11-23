module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.BfDep
section
noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ}

def ext' {m : ℕ} (τ : Fin m → Γ) (n : ℕ) : Γ := if h : n < m then τ ⟨n, h⟩ else 1

private theorem isClosed_simplex_fin_sum_le_one (q : ℕ) : IsClosed {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  show IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1})
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const

private theorem simplex_point_mem_of_convex_of_vertices_mem {q : ℕ} (hU : Convex ℝ U) (y : Fin (q + 1) → V) (hy : ∀ i, y i ∈ U)
    (t : Fin q → ℝ) (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) :
    y 0 + ∑ j, t j • (y j.succ - y 0) ∈ U := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  rw [e]
  apply hU.sum_mem
  · intro i _
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      linarith [ht.2]
    | succ i =>
      simp only [Fin.cons_succ]
      exact ht.1 i
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  · intro i _
    exact hy i

private theorem intS'_congr_of_eqOn_convex {q : ℕ} (hU : Convex ℝ U) (ω ω' : V → V [⋀^Fin q]→L[ℝ] ℝ)
    (hω : ∀ x ∈ U, ω x = ω' x) (y : Fin (q + 1) → V) (hy : ∀ i, y i ∈ U) :
    intS' ω y = intS' ω' y := by
  unfold intS'
  apply setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet
  intro t ht
  simp only [hω _ (simplex_point_mem_of_convex_of_vertices_mem hU y hy t ht)]

private theorem intS'_comp_continuousLinearMap {q : ℕ} (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (B : V →L[ℝ] V)
    (y : Fin (q + 1) → V) :
    intS' ω (fun l => B (y l)) = intS' (fun x => (ω (B x)).compContinuousLinearMap B) y := by
  unfold intS'
  apply setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet
  intro t _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, map_add (f := _), map_sum, map_smul,
    map_sub, Function.comp_def]

private theorem kf_eta_congr_of_eq_on_initial_of_pDep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ)
    (σ σ' : ℕ → Γ) (h : ∀ m, m + j ≤ k → σ m = σ' m) :
    Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
  funext x
  simp only [Kf]
  congr 1
  funext γ
  rw [hD k c j (cons γ σ) (cons γ σ')]
  intro n hn
  cases n with
  | zero => rfl
  | succ m => exact h m (by omega)

theorem Bf_dep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ) (hj : j ≤ k)
    (g g' : ℕ → Γ) (h : ∀ n ≤ k, g n = g' n) : Bf A φ c o j g = Bf A φ c o j g' := by
  simp only [Bf]
  rw [kf_eta_congr_of_eq_on_initial_of_pDep hD c j g g' (fun m hm => h m (by omega))]
  congr 1
  funext l
  rw [h _ (by have := l.isLt; omega)]

theorem Bf_inv (H : Hyp U A φ) (hE : PEquiv U A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c)
    {o : V} (ho : o ∈ U) (j : ℕ) (x : Γ) (g : ℕ → Γ) :
    Bf A φ c o j (fun n => x * g n) = Bf A φ c o j g := by
  simp only [Bf]
  have hpts : (fun l : Fin (j + 1) => A (x * g (k - j + ↑l)) o) =
      fun l : Fin (j + 1) => A x (A (g (k - j + ↑l)) o) := by
    funext l
    rw [map_mul]
    rfl
  have hpsi : ∀ γ, ∀ h ∈ U, psi A φ γ (A x h) = psi A φ (x⁻¹ * γ) h := by
    intro γ h _
    simp only [psi]
    rw [mul_inv_rev, inv_inv, map_mul]
    rfl
  rw [hpts, intS'_comp_continuousLinearMap]
  refine intS'_congr_of_eqOn_convex H.convex _ _ ?_ _ (fun _ => H.mapsTo _ o ho)
  intro h hh
  rw [(hE H k c hc.inv (A x) x⁻¹ (H.mapsTo x) hpsi j (fun n => x * g n) h hh).2]
  simp only [inv_mul_cancel_left]

private theorem apply_add_succAbove_eq_skip (g : ℕ → Γ) (a : ℕ) {n : ℕ} (i : Fin (n + 1)) (l : Fin n) :
    g (a + ↑(i.succAbove l)) = skip (a + ↑i) g (a + ↑l) := by
  simp only [skip]
  rcases lt_or_ge l.val i.val with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl), if_pos (by omega)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using hl), if_neg (by omega)]
    simp only [Fin.val_succ, Nat.add_assoc]

theorem tele (H : Hyp U A φ) (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ)
    (hC : PCoc U A φ) (hE : PEquiv U A φ) (hS : Stk U) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ)
    (hc : Coc c) {o : V} (ho : o ∈ U) :
    ∀ j ≤ k + 1, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ b : (ℕ → Γ) → ℝ,
      (∀ x g, b (fun n => x * g n) = b g) ∧ (∀ g g', (∀ n ≤ k, g n = g' n) → b g = b g') ∧
      ∀ g, Wf A φ c o 0 g = ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i g) + s * Wf A φ c o j g := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨1, Or.inl rfl, fun _ => 0, fun _ _ => rfl, fun _ _ _ => rfl, fun g => by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨s, hs, b, hbi, hbd, hb⟩ := ih (by omega)
    refine ⟨-s * (-1) ^ (k - j), ?_, fun g => b g + s * Bf A φ c o j g, ?_, ?_, fun g => ?_⟩
    · rcases hs with rfl | rfl <;> rcases neg_one_pow_eq_or ℝ (k - j) with h | h <;> rw [h] <;> norm_num
    · intro x g
      simp only [hbi, Bf_inv H hE c hc ho]
    · intro g g' hg
      simp only [hbd g g' hg, Bf_dep hD c o j (by omega) g g' hg]
    · rw [hb g]
      have hch := chain H hH hSm hD hC hS c hc ho (k - j) j (by omega) g
      have e : ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * (b (skip i g) + s * Bf A φ c o j (skip i g)) =
          ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i g) +
            s * ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * Bf A φ c o j (skip i g) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hch]
      ring

private theorem wf_zero_ext'_eq {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (g : Fin (k + 2) → Γ) :
    Wf A φ c o 0 (ext' g) = c g := by
  have ez : eta A φ c 0 (ext' g) =
      fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => ext' g ↑i) := rfl
  simp only [Wf]
  rw [ez]
  unfold intS'
  simp only [ContinuousAlternatingMap.constOfIsEmpty_apply]
  have hS : {t : Fin 0 → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} = Set.univ := by
    ext t
    simp
  have e : (fun i : Fin (k + 2) => ext' g ↑i) = g := by
    funext i
    simp [ext', i.isLt]
  rw [hS, e, setIntegral_univ, integral_const]
  simp [Measure.real, volume_pi, Measure.pi_empty_univ]

private theorem eta_succ_congr_of_coc_of_mem (H : Hyp U A φ) (hD : PDep A φ) (hC : PCoc U A φ) {k : ℕ}
    (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (σ σ' : ℕ → Γ) {h : V} (hh : h ∈ U) :
    eta A φ c (k + 1) σ h = eta A φ c (k + 1) σ' h := by
  have e := hC H k c hc (k + 1) le_rfl (cons (σ 0) σ') h hh
  have h1 : eta A φ c (k + 1) (skip 0 (cons (σ 0) σ')) = eta A φ c (k + 1) σ' :=
    hD k c (k + 1) _ _ (fun n hn => by
      obtain rfl : n = 0 := by omega
      rfl)
  have h2 : eta A φ c (k + 1) (skip 1 (cons (σ 0) σ')) = eta A φ c (k + 1) σ :=
    hD k c (k + 1) _ _ (fun n hn => by
      obtain rfl : n = 0 := by omega
      rfl)
  rw [Nat.sub_self] at e
  simp only [delG, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, pow_zero, pow_one, one_smul, neg_smul, h1, h2] at e
  rw [add_neg_eq_zero] at e
  exact e.symm

theorem pComp (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ) (hC : PCoc U A φ)
    (hE : PEquiv U A φ) : PComp U A φ := by
  intro H hStk k c hc o ho
  obtain ⟨s, hs, b, hbi, hbd, hW⟩ := tele H hH hSm hD hC hE hStk c hc ho (k + 1) le_rfl
  refine ⟨s, hs, fun y => b (ext' y), ?_, ?_⟩
  · intro x y
    beta_reduce
    rw [← hbi x (ext' y)]
    apply hbd
    intro n hn
    simp [ext', show n < k + 1 by omega]
  · intro g
    have h0 := hW (ext' g)
    rw [wf_zero_ext'_eq c o g] at h0
    have hWk : Wf A φ c o (k + 1) (ext' g) =
        intS' (eta A φ c (k + 1) fun _ => 1) (fun l : Fin (k + 2) => A (g l) o) := by
      simp only [Wf]
      have ep : (fun l : Fin (k + 2) => A (ext' g (k + 1 - (k + 1) + ↑l)) o) =
          fun l : Fin (k + 2) => A (g l) o := by
        funext l
        simp [ext', l.isLt]
      rw [ep]
      exact intS'_congr_of_eqOn_convex H.convex _ _ (fun h hh => eta_succ_congr_of_coc_of_mem H hD hC c hc _ _ hh) _
        (fun _ => H.mapsTo _ o ho)
    have hsum : ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i (ext' g)) =
        dC' (fun y => b (ext' y)) g := by
      simp only [dC']
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply hbd
      intro n hn
      have := apply_add_succAbove_eq_skip (ext' g) 0 i (⟨n, by omega⟩ : Fin (k + 1))
      simp only [zero_add, Fin.val_mk] at this
      rw [← this]
      simp [ext', show n < k + 1 by omega]
    rw [hWk, hsum] at h0
    rw [h0]
    ring

end PositivityTheory.KB.WhittakerCocycle

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Smooth
section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem eta_zero {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (σ : ℕ → Γ) :
    eta A φ c 0 σ = fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i) := rfl

theorem eta_succ {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ) :
    eta A φ c (j + 1) σ = extDeriv (Kf A φ (eta A φ c j) σ) := rfl

theorem psi_contDiffAt (H : Hyp U A φ) (γ : Γ) {h : V} (hh : h ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (psi A φ γ) h := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) φ (A γ⁻¹ h) :=
    H.smooth.contDiffAt (H.isOpen.mem_nhds (H.mapsTo _ h hh))
  exact h1.comp h (A γ⁻¹).contDiff.contDiffAt

theorem Kf_contDiffOn (hL : PLoc U A φ) (H : Hyp U A φ) {q : ℕ}
    (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (hβ : ∀ τ, ContDiffOn ℝ (⊤ : ℕ∞) (β τ) U) (σ : ℕ → Γ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Kf A φ β σ) U := by
  intro h hh
  obtain ⟨s, W, hW, hWU, hz⟩ := hL H h hh
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ∑ γ ∈ s, psi A φ γ x • β (cons γ σ) x) h := by
    apply ContDiffAt.sum
    intro γ _
    exact (psi_contDiffAt U A φ H γ hh).smul ((hβ _).contDiffAt (H.isOpen.mem_nhds hh))
  refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW] with x hx
  show (∑ᶠ γ, psi A φ γ x • β (cons γ σ) x) = _
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  by_contra hn
  apply hγ
  simp [hz γ hn x hx]

theorem extDeriv_contDiffOn (H : Hyp U A φ) {q : ℕ} {ω : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (hω : ContDiffOn ℝ (⊤ : ℕ∞) ω U) : ContDiffOn ℝ (⊤ : ℕ∞) (extDeriv ω) U := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ ω) U := hω.fderiv_of_isOpen H.isOpen (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ).contDiff.comp_contDiffOn hd

theorem pSmooth (hL : PLoc U A φ) : PSmooth U A φ := by
  intro H k c j σ
  have key : ∀ (i : ℕ) (τ : ℕ → Γ), ContDiffOn ℝ (⊤ : ℕ∞) (eta A φ c i τ) U := by
    intro i
    induction i with
    | zero =>
      intro τ
      rw [eta_zero]
      exact contDiffOn_const
    | succ i ih =>
      intro τ
      rw [eta_succ]
      exact extDeriv_contDiffOn U A φ H (Kf_contDiffOn U A φ hL H _ ih τ)
  exact ⟨key j σ, Kf_contDiffOn U A φ hL H _ (key j) σ⟩

theorem pClosed (hS : PSmooth U A φ) : PClosed U A φ := by
  intro H k c j σ h hh
  cases j with
  | zero =>
    rw [eta_zero]
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  | succ j =>
    rw [eta_succ]
    exact extDeriv_extDeriv_apply ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds hh))
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        first
        | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
        | (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.2 le_top)
        | simp)

theorem pDep : PDep A φ := by
  intro k c j
  induction j with
  | zero =>
    intro σ σ' hσ
    rw [eta_zero, eta_zero]
    have e : (fun i : Fin (k + 2) => σ i) = fun i : Fin (k + 2) => σ' i := by
      funext i
      have := i.isLt
      exact hσ i (by omega)
    rw [e]
  | succ j ih =>
    intro σ σ' hσ
    rw [eta_succ, eta_succ]
    have e : Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
      funext x
      simp only [Kf]
      congr 1
      funext γ
      rw [ih (cons γ σ) (cons γ σ')]
      intro n hn
      cases n with
      | zero => rfl
      | succ m => exact hσ m (by omega)
    rw [e]

end PositivityTheory.KB.WhittakerCocycle

end
end

