module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.SimplexMem

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.IntegrableOnSimp
section
noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def simp' (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

theorem isClosed_simp' (q : ℕ) : IsClosed (simp' q) := by
  have : simp' q = (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
    ext t; simp [simp']
  rw [this]
  exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)

theorem isCompact_simp' (q : ℕ) : IsCompact (simp' q) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0:ℝ)) (b := 1)).of_isClosed_subset (isClosed_simp' q) ?_
  intro t ht j _
  exact ⟨ht.1 j, le_trans (Finset.single_le_sum (fun i _ => ht.1 i) (Finset.mem_univ j)) ht.2⟩

private theorem simplex_point_mem_of_convex_of_mem_simp' {U : Set V} (hU : Convex ℝ U) {q : ℕ} {y : Fin (q + 1) → V}
    (hy : ∀ j, y j ∈ U) {t : Fin q → ℝ} (ht : t ∈ simp' q) :
    y 0 + ∑ j, t j • (y j.succ - y 0) ∈ U := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i : Fin (q + 1), (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul,
      one_smul]
    abel
  rw [e]
  refine hU.sum_mem (fun i _ => ?_) ?_ (fun i _ => hy i)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [ht.2]
    · simp only [Fin.cons_succ]
      exact ht.1 j
  · rw [Fin.sum_univ_succ]
    simp

theorem integrableOn_simp {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ω : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (hω : ContinuousOn ω U) {y : Fin (q + 1) → V} (hy : ∀ j, y j ∈ U) :
    IntegrableOn (fun t : Fin q → ℝ => ω (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0)
      (simp' q) := by
  have hg : Continuous fun t : Fin q → ℝ => y 0 + ∑ j, t j • (y j.succ - y 0) := by fun_prop
  have hc : ContinuousOn (fun t : Fin q → ℝ => ω (y 0 + ∑ j, t j • (y j.succ - y 0))) (simp' q) :=
    hω.comp hg.continuousOn fun t ht => simplex_point_mem_of_convex_of_mem_simp' hU hy ht
  exact (hc.eval_const _).integrableOn_compact (isCompact_simp' q)

theorem intS'_congr {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ω ω' : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (h : ∀ x ∈ U, ω x = ω' x) {y : Fin (q + 1) → V} (hy : ∀ j, y j ∈ U) :
    intS' ω y = intS' ω' y := by
  unfold intS'
  refine setIntegral_congr_fun (isClosed_simp' q).measurableSet fun t ht => ?_
  simp only [h _ (simplex_point_mem_of_convex_of_mem_simp' hU hy ht)]

theorem intS'_sum {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ι : Type} (s : Finset ι) (a : ι → ℝ)
    (ω : ι → V → V [⋀^Fin q]→L[ℝ] ℝ) (hω : ∀ i ∈ s, ContinuousOn (ω i) U) {y : Fin (q + 1) → V}
    (hy : ∀ j, y j ∈ U) :
    intS' (∑ i ∈ s, a i • ω i) y = ∑ i ∈ s, a i * intS' (ω i) y := by
  unfold intS'
  have e : ∀ t : Fin q → ℝ, ((∑ i ∈ s, a i • ω i) (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0)
      = ∑ i ∈ s, a i * ω i (y 0 + ∑ j, t j • (y j.succ - y 0)) (fun j => y j.succ - y 0) := by
    intro t
    simp [Finset.sum_apply, ContinuousAlternatingMap.sum_apply]
  simp_rw [e]
  have hs := integral_finsetSum (μ := volume.restrict (simp' q)) s
    fun i hi => (integrableOn_simp hU (hω i hi) hy).const_mul (a i)
  unfold simp' at hs
  rw [hs]
  simp_rw [integral_const_mul]

end PositivityTheory.KB.WhittakerCocycle

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PSmooth
section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

def PLoc : Prop := Hyp U A φ → ∀ h ∈ U, ∃ s : Finset Γ, ∃ W ∈ 𝓝 h, W ⊆ U ∧
  ∀ γ ∉ s, ∀ x ∈ W, psi A φ γ x = 0

def PHom : Prop := Hyp U A φ → ∀ (q n : ℕ) (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (σ : ℕ → Γ),
  ∀ h ∈ U, delG n (Kf A φ β) σ h = β σ h - Kf A φ (delG (n + 1) β) σ h

def PSmooth : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ),
  ContDiffOn ℝ (⊤ : ℕ∞) (eta A φ c j σ) U ∧ ContDiffOn ℝ (⊤ : ℕ∞) (Kf A φ (eta A φ c j) σ) U

def PClosed : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ : ℕ → Γ),
  ∀ h ∈ U, extDeriv (eta A φ c j σ) h = 0

def PDep : Prop := ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ σ' : ℕ → Γ),
  (∀ n, n + j ≤ k + 1 → σ n = σ' n) → eta A φ c j σ = eta A φ c j σ'

def PCoc : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), Coc c → ∀ j ≤ k + 1,
  ∀ (σ : ℕ → Γ), ∀ h ∈ U, delG (k + 1 - j) (eta A φ c j) σ h = 0

def PEquiv : Prop := Hyp U A φ → ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), (∀ g y, c (fun j => g * y j) = c y) →
  ∀ (B : V →L[ℝ] V) (a : Γ), (∀ h ∈ U, B h ∈ U) → (∀ γ, ∀ h ∈ U, psi A φ γ (B h) = psi A φ (a * γ) h) →
  ∀ (j : ℕ) (σ : ℕ → Γ), ∀ h ∈ U,
    (eta A φ c j σ (B h)).compContinuousLinearMap B = eta A φ c j (fun n => a * σ n) h ∧
    (Kf A φ (eta A φ c j) σ (B h)).compContinuousLinearMap B = Kf A φ (eta A φ c j) (fun n => a * σ n) h

def PBound : Prop := Hyp U A φ → ∀ O : Set Γ, O.Finite →
  (∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
    (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O) →
  (∃ C, ∀ h ∈ U, |φ h| ≤ C) →
  ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), Coc c → ∃ C, ∀ h ∈ U, ∀ (T : V →L[ℝ] V) (M : ℝ), 0 ≤ M →
    (∀ γ, ‖(fderiv ℝ (psi A φ γ) h).comp T‖ ≤ M) →
    ‖(eta A φ c (k + 1) (fun _ => 1) h).compContinuousLinearMap T‖ ≤ C * M ^ (k + 1)

def PComp : Prop := Hyp U A φ →
  (∀ (q : ℕ) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ), ContDiffOn ℝ 1 ω U → ∀ y : Fin (q + 2) → V, (∀ j, y j ∈ U) →
     dC' (intS' ω) y = intS' (extDeriv ω) y) →
  ∀ (k : ℕ) (c : (Fin (k + 2) → Γ) → ℝ), Coc c → ∀ o ∈ U, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
  ∃ b : (Fin (k + 1) → Γ) → ℝ, (∀ g y, b (fun j => g * y j) = b y) ∧
    ∀ g : Fin (k + 2) → Γ, c g = s * intS' (eta A φ c (k + 1) fun _ => 1) (fun l => A (g l) o) + dC' b g

end PositivityTheory.KB.WhittakerCocycle

end
end

