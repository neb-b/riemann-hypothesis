module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.AltSmulRightComp
section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

def Nr (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (h : V) (γ : Γ) : Prop :=
  ∃ hm : A γ⁻¹ h ∈ U, (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0}

theorem diffAt_of {U : Set V} (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {h : V} (hh : h ∈ U) : DifferentiableAt ℝ f h := by
  exact (hf.contDiffAt (hU.mem_nhds hh)).differentiableAt (by simp)

theorem psi_contDiffOn {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) (γ : Γ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (psi A φ γ) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => φ (A γ⁻¹ x)) U :=
    H.smooth.comp (A γ⁻¹).contDiff.contDiffOn (fun x hx => H.mapsTo γ⁻¹ x hx)
  exact h1

theorem nr_eventually {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) {γ : Γ} (hγ : ¬ Nr U A φ h γ) : psi A φ γ =ᶠ[𝓝 h] fun _ => 0 := by
  have hp : A γ⁻¹ h ∈ U := H.mapsTo _ h hh
  have hn : (⟨A γ⁻¹ h, hp⟩ : U) ∉ closure {x : U | φ x ≠ 0} := fun hc => hγ ⟨hp, hc⟩
  let g : U → U := fun x => ⟨A γ⁻¹ x, H.mapsTo _ x x.2⟩
  have hg : Continuous g :=
    ((A γ⁻¹).continuous.comp continuous_subtype_val).subtype_mk _
  have h1 : ∀ᶠ x in 𝓝 (⟨h, hh⟩ : U), g x ∈ (closure {x : U | φ x ≠ 0})ᶜ :=
    hg.continuousAt (isClosed_closure.isOpen_compl.mem_nhds hn)
  have h2 : ∀ᶠ x in 𝓝 (⟨h, hh⟩ : U), psi A φ γ x.1 = 0 := h1.mono fun x hx => by
    have h3 : g x ∉ {x : U | φ x ≠ 0} := fun h' => hx (subset_closure h')
    simp only [Set.mem_setOf_eq, not_not] at h3
    exact h3
  have h4 : ∀ᶠ x in Filter.map (fun x : U => (x : V)) (𝓝 (⟨h, hh⟩ : U)), psi A φ γ x = 0 := h2
  rw [map_nhds_subtype_val, H.isOpen.nhdsWithin_eq hh] at h4
  exact h4

theorem nr_fderiv {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) {γ : Γ} (hγ : ¬ Nr U A φ h γ) : fderiv ℝ (psi A φ γ) h = 0 := by
  rw [(nr_eventually H hh hγ).fderiv_eq]
  simp

theorem nr_mul {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} {O : Set Γ}
    (hOv : ∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
      (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O)
    {h : V} {γ γ' : Γ} (h1 : Nr U A φ h γ) (h2 : Nr U A φ h γ') : γ⁻¹ * γ' ∈ O := by
  obtain ⟨hm1, hc1⟩ := h1
  obtain ⟨hm2, hc2⟩ := h2
  have key : A (γ⁻¹ * γ')⁻¹ (A γ⁻¹ h) = A γ'⁻¹ h := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    rw [show (γ⁻¹ * γ')⁻¹ * γ⁻¹ = γ'⁻¹ by group]
  have hm : A (γ⁻¹ * γ')⁻¹ (A γ⁻¹ h) ∈ U := by rw [key]; exact hm2
  refine hOv (γ⁻¹ * γ') ⟨A γ⁻¹ h, hm1⟩ hc1 hm ?_
  convert hc2 using 1
  exact Subtype.ext key

theorem nr_exists {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) : ∃ γ, Nr U A φ h γ := by
  by_contra hne
  have hz : ∀ γ, φ (A γ⁻¹ h) = 0 := fun γ => by
    by_contra h0
    exact hne ⟨γ, H.mapsTo _ h hh, subset_closure h0⟩
  have hs := H.sum_one h hh
  simp only [hz, finsum_zero] at hs
  exact zero_ne_one hs

theorem c_bdd {O : Set Γ} (hO : O.Finite) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ τ : Fin (k + 2) → Γ, (∀ i, τ i ∈ O) → |c τ| ≤ C := by
  have hfin : (Set.pi Set.univ (fun _ : Fin (k + 2) => O)).Finite := Set.Finite.pi (fun _ => hO)
  obtain ⟨B, hB⟩ := (hfin.image (fun τ => |c τ|)).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun τ hτ => ?_⟩
  exact le_trans (hB ⟨τ, fun i _ => hτ i, rfl⟩) (le_max_left _ _)

theorem alt_smulRight_comp {n : ℕ} (f : V →L[ℝ] ℝ) (b : V [⋀^Fin n]→L[ℝ] ℝ) (T : V →L[ℝ] V) :
    (ContinuousAlternatingMap.alternatizeUncurryFin (f.smulRight b)).compContinuousLinearMap T =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((f.comp T).smulRight (b.compContinuousLinearMap T)) := by
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]
  rfl

theorem sum_compCLM {ι : Type} {n : ℕ} (s : Finset ι) (X : ι → V [⋀^Fin n]→L[ℝ] ℝ)
    (T : V →L[ℝ] V) :
    (∑ i ∈ s, X i).compContinuousLinearMap T = ∑ i ∈ s, (X i).compContinuousLinearMap T := by
  ext v
  simp [ContinuousAlternatingMap.sum_apply]

theorem nr_cons {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} {h : V} {γ : Γ} {σ : ℕ → Γ}
    (hγ : Nr U A φ h γ) (hσ : ∀ n, Nr U A φ h (σ n)) : ∀ n, Nr U A φ h (cons γ σ n) := by
  intro n
  cases n with
  | zero => exact hγ
  | succ n => exact hσ n

theorem claim {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (hL : PLoc U A φ)
    (hS : PSmooth U A φ) (hCl : PClosed U A φ) (H : Hyp U A φ) {O : Set Γ} (hO : O.Finite)
    (hOv : ∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
      (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O)
    {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ U, ∀ (T : V →L[ℝ] V) (M : ℝ), 0 ≤ M →
      (∀ γ, ‖(fderiv ℝ (psi A φ γ) h).comp T‖ ≤ M) → ∀ σ : ℕ → Γ, (∀ n, Nr U A φ h (σ n)) →
      ‖(eta A φ c j σ h).compContinuousLinearMap T‖ ≤ C * M ^ j := by
  classical
  obtain ⟨C0, hC0, hC0b⟩ := c_bdd hO c
  induction j with
  | zero =>
    refine ⟨C0, hC0, fun h hh T M hM hT σ hσ => ?_⟩
    have e : (eta A φ c 0 σ h).compContinuousLinearMap T
        = ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i) := by
      rw [eta.eq_1]
      ext m
      simp
    rw [e, ContinuousAlternatingMap.norm_constOfIsEmpty, pow_zero, mul_one, Real.norm_eq_abs]
    rw [← hc.inv (σ 0)⁻¹ (fun i => σ i)]
    exact hC0b _ (fun i => nr_mul hOv (hσ 0) (hσ i))
  | succ j ih =>
    obtain ⟨Cj, hCj, hCjb⟩ := ih
    refine ⟨(hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * Cj),
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) hCj),
      fun h hh T M hM hT σ hσ => ?_⟩
    obtain ⟨s, W, hW, hWU, hs⟩ := hL H h hh
    have hloc : Kf A φ (eta A φ c j) σ =ᶠ[𝓝 h]
        fun x => ∑ γ ∈ s, psi A φ γ x • eta A φ c j (cons γ σ) x := by
      filter_upwards [hW] with x hx
      show ∑ᶠ γ, psi A φ γ x • eta A φ c j (cons γ σ) x = _
      apply finsum_eq_sum_of_support_subset
      intro γ hγ
      by_contra hγs
      exact (Function.mem_support.mp hγ) (by simp [hs γ hγs x hx])
    have hdψ : ∀ γ, DifferentiableAt ℝ (psi A φ γ) h :=
      fun γ => diffAt_of H.isOpen (psi_contDiffOn H γ) hh
    have hdη : ∀ γ, DifferentiableAt ℝ (eta A φ c j (cons γ σ)) h :=
      fun γ => diffAt_of H.isOpen (hS H k c j (cons γ σ)).1 hh
    have hder : fderiv ℝ (Kf A φ (eta A φ c j) σ) h = ∑ γ ∈ s,
        (psi A φ γ h • fderiv ℝ (eta A φ c j (cons γ σ)) h
          + (fderiv ℝ (psi A φ γ) h).smulRight (eta A φ c j (cons γ σ) h)) := by
      rw [hloc.fderiv_eq, fderiv_fun_sum (A := fun γ x => psi A φ γ x • eta A φ c j (cons γ σ) x)
        (fun γ _ => by exact (hdψ γ).smul (hdη γ))]
      refine Finset.sum_congr rfl fun γ _ => ?_
      exact fderiv_fun_smul (hdψ γ) (hdη γ)
    have heta : eta A φ c (j + 1) σ h = ∑ γ ∈ s, ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ (psi A φ γ) h).smulRight (eta A φ c j (cons γ σ) h)) := by
      rw [show eta A φ c (j + 1) σ = extDeriv (Kf A φ (eta A φ c j) σ) from eta.eq_2 A φ c σ j]
      show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (Kf A φ (eta A φ c j) σ) h) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hder, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_add (f := _), map_smul, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
        ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
      have hz : ContinuousAlternatingMap.alternatizeUncurryFin
          (fderiv ℝ (eta A φ c j (cons γ σ)) h) = 0 := hCl H k c j (cons γ σ) h hh
      rw [hz, smul_zero, zero_add]
    obtain ⟨γ0, hγ0⟩ := nr_exists H hh
    have hcard : (s.filter (Nr U A φ h)).card ≤ hO.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun γ => γ0⁻¹ * γ)
      · intro γ hγ
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_coe] at hγ
        simp only [Finset.coe_filter, Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Finset.mem_coe]
        exact nr_mul hOv hγ0 hγ.2
      · intro a _ b _ hab
        exact mul_left_cancel hab
    have hB : 0 ≤ ((j : ℝ) + 1) * (M * (Cj * M ^ j)) :=
      mul_nonneg (by positivity) (mul_nonneg hM (mul_nonneg hCj (pow_nonneg hM _)))
    have hterm : ∀ γ ∈ s, ‖ContinuousAlternatingMap.alternatizeUncurryFin
        (((fderiv ℝ (psi A φ γ) h).comp T).smulRight
          ((eta A φ c j (cons γ σ) h).compContinuousLinearMap T))‖
        ≤ if Nr U A φ h γ then ((j : ℝ) + 1) * (M * (Cj * M ^ j)) else 0 := by
      intro γ _
      split_ifs with hγ
      · refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans ?_
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hT γ) (hCjb h hh T M hM hT _ (nr_cons hγ hσ)) (norm_nonneg _) hM)
          (by positivity)
      · refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans (le_of_eq ?_)
        rw [ContinuousLinearMap.norm_smulRight_apply, nr_fderiv H hh hγ]
        simp
    rw [heta, sum_compCLM]
    simp only [alt_smulRight_comp]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    calc ((s.filter (Nr U A φ h)).card : ℝ) * (((j : ℝ) + 1) * (M * (Cj * M ^ j)))
        ≤ (hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * (M * (Cj * M ^ j))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
      _ = (hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * Cj) * M ^ (j + 1) := by ring

theorem pBound (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (hL : PLoc U A φ)
    (hS : PSmooth U A φ) (hCl : PClosed U A φ) (hCoc : PCoc U A φ) (hD : PDep A φ) :
    PBound U A φ := by
  intro Hy O hO hOv _ k c hc
  obtain ⟨C, -, hC⟩ := claim hL hS hCl Hy hO hOv c hc (k + 1)
  refine ⟨C, fun h hh T M hM hT => ?_⟩
  obtain ⟨γ0, hγ0⟩ := nr_exists Hy hh
  have e1 : eta A φ c (k + 1) (fun _ => 1) = eta A φ c (k + 1) (skip 0 (cons γ0 fun _ => 1)) :=
    hD k c (k + 1) _ _ (fun n _ => by simp [skip, cons])
  have e2 : eta A φ c (k + 1) (skip 1 (cons γ0 fun _ => 1)) = eta A φ c (k + 1) (fun _ => γ0) :=
    hD k c (k + 1) _ _ (fun n hn => by
      have hn0 : n = 0 := by omega
      subst hn0
      simp [skip, cons])
  have e3 : eta A φ c (k + 1) (skip 0 (cons γ0 fun _ => 1)) h
      = eta A φ c (k + 1) (skip 1 (cons γ0 fun _ => 1)) h := by
    have e0 := hCoc Hy k c hc (k + 1) le_rfl (cons γ0 fun _ => 1) h hh
    apply sub_eq_zero.mp
    simpa [delG, Finset.sum_range_succ, sub_eq_add_neg] using e0
  rw [e1, e3, e2]
  exact hC h hh T M hM hT _ (fun _ => hγ0)

end PositivityTheory.KB.WhittakerCocycle

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.EtaTop
section
noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ}

def Stk (U : Set V) : Prop := ∀ (q : ℕ) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ), ContDiffOn ℝ 1 ω U →
  ∀ y : Fin (q + 2) → V, (∀ j, y j ∈ U) → dC' (intS' ω) y = intS' (extDeriv ω) y

def Wf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (eta A φ c j g) (fun l : Fin (j + 1) => A (g (k + 1 - j + l)) o)

def Bf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (Kf A φ (eta A φ c j) g) (fun l : Fin (j + 1) => A (g (k - j + l)) o)

theorem kf_dep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ σ' : ℕ → Γ)
    (h : ∀ n, n + j + 1 ≤ k + 1 → σ n = σ' n) :
    Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
  funext x
  simp only [Kf]
  congr 1
  funext γ
  rw [hD k c j (cons γ σ) (cons γ σ') (fun n hn => by
    cases n with
    | zero => rfl
    | succ m => exact h m (by omega))]

theorem eta_top (H : Hyp U A φ) (hD : PDep A φ) (hC : PCoc U A φ) {k : ℕ}
    (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (τ τ' : ℕ → Γ) (x : V) (hx : x ∈ U) :
    eta A φ c (k + 1) τ x = eta A φ c (k + 1) τ' x := by
  have h0 := hC H k c hc (k + 1) le_rfl (cons (τ 0) τ') x hx
  rw [Nat.sub_self] at h0
  have e1 : eta A φ c (k + 1) (skip 0 (cons (τ 0) τ')) = eta A φ c (k + 1) τ' := by
    congr 1
  have e2 : eta A φ c (k + 1) (skip 1 (cons (τ 0) τ')) = eta A φ c (k + 1) τ :=
    hD k c (k + 1) _ _ (fun n hn => by
      have : n = 0 := by omega
      subst this
      simp [skip, cons])
  simp only [delG, Finset.sum_range_succ, Finset.sum_range_zero, e1, e2] at h0
  simp at h0
  rw [add_neg_eq_zero] at h0
  exact h0.symm

private theorem neg_one_pow_add_one_add_eq_mul (a : ℕ) (m : ℕ) : (-1 : ℝ) ^ (a + 1 + m) = (-1) ^ a * (-1) ^ (m + 1) := by
  ring

theorem chain (H : Hyp U A φ) (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ)
    (hC : PCoc U A φ) (hS : Stk U) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) {o : V}
    (ho : o ∈ U) (a j : ℕ) (hk : a + j = k) (g : ℕ → Γ) :
    ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * Bf A φ c o j (skip i g) =
      Wf A φ c o j g + (-1) ^ a * Wf A φ c o (j + 1) g := by
  subst hk
  obtain ⟨ω, hω⟩ : ∃ ω, ω = Kf A φ (eta A φ c j) g := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin (j + 2) → V, Y = fun l : Fin (j + 2) => A (g (a + (l : ℕ))) o := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin (j + 1) → V, Z = fun l : Fin (j + 1) => A (g (a + 1 + (l : ℕ))) o :=
    ⟨_, rfl⟩
  have hYU : ∀ l, Y l ∈ U := fun l => by rw [hY]; exact H.mapsTo _ _ ho
  have hZU : ∀ l, Z l ∈ U := fun l => by rw [hZ]; exact H.mapsTo _ _ ho
  have hcont : ∀ σ, ContinuousOn (Kf A φ (eta A φ c j) σ) U :=
    fun σ => ((hSm H (a + j) c j σ).2).continuousOn
  have hK : ∀ i, a + 1 ≤ i → Kf A φ (eta A φ c j) (skip i g) = ω := by
    intro i hi
    rw [hω]
    exact kf_dep hD c j _ _ (fun n hn => by simp only [skip]; rw [if_pos (by omega)])
  have hF2 : ∀ x ∈ U, (∑ i ∈ Finset.range (a + 2),
      ((-1 : ℝ) ^ i) • Kf A φ (eta A φ c j) (skip i g)) x = eta A φ c j g x := by
    intro x hx
    have h1 := hH H j a (eta A φ c j) g x hx
    have h0 : ∀ γ, psi A φ γ x • delG (a + 1) (eta A φ c j) (cons γ g) x = 0 := by
      intro γ
      have := hC H (a + j) c hc j (by omega) (cons γ g) x hx
      rw [show a + j + 1 - j = a + 1 by omega] at this
      rw [this, smul_zero]
    have h2 : Kf A φ (delG (a + 1) (eta A φ c j)) g x = 0 := by
      simp only [Kf, h0, finsum_zero]
    rw [h2, sub_zero] at h1
    rw [← h1]
    simp only [delG, Finset.sum_apply]
  have hWj : Wf A φ c o j g = ∑ i ∈ Finset.range (a + 2),
      (-1 : ℝ) ^ i * intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    rw [← intS'_sum H.convex _ _ _ (fun i _ => hcont _) hZU]
    rw [intS'_congr H.convex hF2 hZU]
    simp only [Wf, hZ]
    congr 1
    funext l
    rw [show a + j + 1 - j + ↑l = a + 1 + ↑l by omega]
  have hBA : ∀ i, i < a + 1 → Bf A φ c o j (skip i g) = intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    intro i hi
    simp only [Bf, hZ]
    congr 1
    funext l
    simp only [skip]
    rw [if_neg (by omega), show a + j - j + ↑l + 1 = a + 1 + ↑l by omega]
  have hBB : ∀ m : Fin (j + 1), Bf A φ c o j (skip (a + 1 + ↑m) g) =
      intS' ω (fun l => Y (m.succ.succAbove l)) := by
    intro m
    simp only [Bf, hY]
    rw [hK _ (by omega)]
    congr 1
    funext l
    simp only [skip, Fin.succAbove]
    split_ifs <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;>
      first | (exfalso; omega) | (congr 3; omega)
  have hExt : extDeriv ω = eta A φ c (j + 1) g := by rw [hω]; rfl
  have hSt := hS j ω (by
    rw [hω]
    exact ((hSm H (a + j) c j g).2).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) Y hYU
  rw [hExt] at hSt
  rw [dC', Fin.sum_univ_succ] at hSt
  have hW1 : Wf A φ c o (j + 1) g = intS' (eta A φ c (j + 1) g) Y := by
    simp only [Wf, hY]
    congr 1
    funext l
    rw [show a + j + 1 - (j + 1) + ↑l = a + ↑l by omega]
  have hY0 : (fun l => Y ((0 : Fin (j + 2)).succAbove l)) = Z := by
    funext l
    simp only [hY, hZ, Fin.succAbove_zero, Fin.val_succ]
    rw [show a + (↑l + 1) = a + 1 + ↑l by omega]
  rw [hY0] at hSt
  rw [show a + j + 2 = (a + 1) + (j + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hBA i (Finset.mem_range.mp hi)])]
  rw [Finset.sum_range (fun m => (-1 : ℝ) ^ (a + 1 + m) * Bf A φ c o j (skip (a + 1 + m) g))]
  simp only [hBB]
  rw [Finset.sum_range_succ, hK _ le_rfl] at hWj
  rw [hWj, hW1, ← hSt]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, neg_one_pow_add_one_add_eq_mul, mul_assoc]
  rw [mul_add, ← Finset.mul_sum]
  ring

end PositivityTheory.KB.WhittakerCocycle

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.EvEqLc
section
noncomputable section

namespace PositivityTheory.KB.WhittakerCocycle

theorem ev_eq_lc {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F (Fin.partialProd g)) z := by
  unfold ev
  rw [Finsupp.linearCombination_apply]
  simp [smul_eq_mul]

private theorem partialProd_contractNth_mul_eq_succAbove {G : Type} [Group G] {k : ℕ} (g : Fin (k + 1) → G) (j l : Fin (k + 1)) :
    Fin.partialProd (Fin.contractNth j (· * ·) g) l = Fin.partialProd g (j.succ.succAbove l) := by
  induction l using Fin.induction with
  | zero =>
    rw [Fin.partialProd_zero, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
    simp
  | succ l ih =>
    rw [Fin.partialProd_succ, ih]
    rcases lt_trichotomy (l : ℕ) j with h | h | h
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.castSucc.succ := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.castSucc, Fin.contractNth_apply_of_lt _ _ _ _ h]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.partialProd_succ g l.castSucc,
        Fin.contractNth_apply_of_eq _ _ _ _ h, mul_assoc]
    · have e1 : j.succ.succAbove l.castSucc = l.castSucc.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e2 : j.succ.succAbove l.succ = l.succ.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)
      have e3 : (l.succ.castSucc : Fin (k + 2)) = l.castSucc.succ := by
        ext
        simp
      rw [e1, e2, Fin.partialProd_succ g l.succ, e3, Fin.contractNth_apply_of_gt _ _ _ _ h]

theorem lc_dC {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ)
    (hb : Inv (MonoidHom.id G) b) :
    Finsupp.linearCombination ℝ (fun g : Fin (k + 1) → G => dC b (Fin.partialProd g)) =
      (Finsupp.linearCombination ℝ (fun g : Fin k → G => b (Fin.partialProd g))).comp (bd G k) := by
  unfold Inv at hb
  refine Finsupp.lhom_ext (fun g r => ?_)
  rw [LinearMap.comp_apply]
  have hs : Finsupp.single g r = r • Finsupp.single g (1 : ℝ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, map_smul]
  congr 1
  rw [Finsupp.linearCombination_single, one_smul]
  unfold bd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum]
  simp only [map_smul, map_zsmul, Finsupp.linearCombination_single, one_smul, smul_eq_mul, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  unfold dC
  rw [Fin.sum_univ_succ]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have h0 := hb (g 0) (Fin.partialProd fun i => g i.succ)
    simp only [MonoidHom.id_apply, smul_eq_mul] at h0
    rw [← h0]
    congr 1
    funext l
    exact Fin.partialProd_succ' g l
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.val_succ]
    simp only [one_mul]
    congr 2
    funext l
    exact (partialProd_contractNth_mul_eq_succAbove g j l).symm

theorem pEv {G : Type} [Group G] {k : ℕ} (b : (Fin (k + 1) → G) → ℝ) (hb : Inv (MonoidHom.id G) b)
    (z : Chn G (k + 1)) (hz : IsCyc z) : ev (MonoidHom.id G) (dC b) 1 z = 0 := by
  rw [ev_eq_lc, lc_dC b hb, LinearMap.comp_apply]
  unfold IsCyc at hz
  rw [hz, map_zero]

end PositivityTheory.KB.WhittakerCocycle

end
end

