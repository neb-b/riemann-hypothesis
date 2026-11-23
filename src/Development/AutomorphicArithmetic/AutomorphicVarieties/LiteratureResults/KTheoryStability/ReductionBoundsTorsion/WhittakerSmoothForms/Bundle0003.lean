module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ExtDerivCongrNhds
section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

theorem cons_mul (a γ : Γ) (σ : ℕ → Γ) :
    (fun n => a * cons γ σ n) = cons (a * γ) (fun n => a * σ n) := by
  funext n; cases n <;> rfl

theorem extDeriv_congr_nhds {n : ℕ} {ω₁ ω₂ : V → V [⋀^Fin n]→L[ℝ] ℝ} {x : V} (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ x = extDeriv ω₂ x := by
  simp only [extDeriv, h.fderiv_eq]

theorem kf_equiv {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (hL : PLoc U A φ) (H : Hyp U A φ)
    {q : ℕ} (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) (B : V →L[ℝ] V) (a : Γ)
    (hB : ∀ h ∈ U, B h ∈ U) (hψ : ∀ γ, ∀ h ∈ U, psi A φ γ (B h) = psi A φ (a * γ) h)
    (hβ : ∀ σ, ∀ h ∈ U, (β σ (B h)).compContinuousLinearMap B = β (fun n => a * σ n) h)
    (σ : ℕ → Γ) {h : V} (hh : h ∈ U) :
    (Kf A φ β σ (B h)).compContinuousLinearMap B = Kf A φ β (fun n => a * σ n) h := by
  obtain ⟨s, W, hW, -, hs⟩ := hL H (B h) (hB h hh)
  have hfin : Function.HasFiniteSupport
      (fun γ => psi A φ γ (B h) • β (cons γ σ) (B h)) := by
    refine s.finite_toSet.subset ?_
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs (B h) (mem_of_mem_nhds hW)]
  have key : ∀ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
      (psi A φ γ (B h) • β (cons γ σ) (B h))
        = psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := by
    intro γ
    rw [map_smul, ← cons_mul, ← hβ _ h hh, ← hψ γ h hh]
    rfl
  calc (Kf A φ β σ (B h)).compContinuousLinearMap B
      = ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (∑ᶠ γ, psi A φ γ (B h) • β (cons γ σ) (B h)) := rfl
    _ = ∑ᶠ γ, ContinuousAlternatingMap.compContinuousLinearMapCLM B
          (psi A φ γ (B h) • β (cons γ σ) (B h)) := map_finsum _ hfin
    _ = ∑ᶠ γ, psi A φ (a * γ) h • β (cons (a * γ) (fun n => a * σ n)) h := finsum_congr key
    _ = Kf A φ β (fun n => a * σ n) h :=
      finsum_comp_equiv (Equiv.mulLeft a)
        (f := fun γ => psi A φ γ h • β (cons γ (fun n => a * σ n)) h)

theorem pEquiv (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (hL : PLoc U A φ)
    (hS : PSmooth U A φ) : PEquiv U A φ := by
  intro H k c hc B a hB hψ
  have hfd : ∀ x, fderiv ℝ B x = B := fun x => B.fderiv
  have he : ∀ j σ, ∀ h ∈ U, (eta A φ c j σ (B h)).compContinuousLinearMap B
      = eta A φ c j (fun n => a * σ n) h := by
    intro j
    induction j with
    | zero =>
      intro σ h hh
      rw [eta.eq_1, eta.eq_1]
      ext m
      simp [hc a (fun i => σ i)]
    | succ j ih =>
      intro σ h hh
      have hK : ∀ x ∈ U, (Kf A φ (eta A φ c j) σ (B x)).compContinuousLinearMap B
          = Kf A φ (eta A φ c j) (fun n => a * σ n) x :=
        fun x hx => kf_equiv hL H (eta A φ c j) B a hB hψ ih σ hx
      have hdiff : DifferentiableAt ℝ (Kf A φ (eta A φ c j) σ) (B h) :=
        ((hS H k c j σ).2.contDiffAt (H.isOpen.mem_nhds (hB h hh))).differentiableAt (by simp)
      have hpb := extDeriv_pullback (f := B) (x := h) (r := ⊤) hdiff B.contDiff.contDiffAt le_top
      simp only [hfd] at hpb
      rw [eta.eq_2, eta.eq_2, ← hpb]
      apply extDeriv_congr_nhds
      filter_upwards [H.isOpen.mem_nhds hh] with x hx
      exact hK x hx
  intro j σ h hh
  exact ⟨he j σ h hh, kf_equiv hL H (eta A φ c j) B a hB hψ (he j) σ hh⟩

end PositivityTheory.KB.WhittakerCocycle

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PosDefOfSphere
section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.KB.WhittakerCocycle

theorem posDef_of_sphere {N : ℕ} {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian)
    (h : ∀ v : Fin N → ℂ, ‖v‖ = 1 → 0 < (star v ⬝ᵥ (M *ᵥ v)).re) : M.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hM, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx' : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set u : Fin N → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hr.ne']
  have key : star x ⬝ᵥ (M *ᵥ x) = ((‖x‖ ^ 2 : ℝ) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [hu, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  rw [RCLike.pos_iff]
  refine ⟨?_, hM.im_star_dotProduct_mulVec_self x⟩
  rw [key]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  exact mul_pos (by positivity) (h u hu1)

theorem isOpen_posW {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) :
    IsOpen {h : HS L N | (mat h w).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro h0 h0p
  have hm : Continuous fun z : HS L N × (Fin N → ℂ) => mat z.1 w := by
    show Continuous fun z : HS L N × (Fin N → ℂ) => (z.1.1 w : Matrix (Fin N) (Fin N) ℂ)
    exact (continuous_apply w).comp (continuous_subtype_val.comp continuous_fst)
  have hg : Continuous fun z : HS L N × (Fin N → ℂ) => (star z.2 ⬝ᵥ (mat z.1 w *ᵥ z.2)).re :=
    Complex.continuous_re.comp ((continuous_snd.star).dotProduct (hm.matrix_mulVec continuous_snd))
  have hK : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1) := isCompact_sphere 0 1
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := h0)
    (P := fun h v => 0 < (star v ⬝ᵥ (mat h w *ᵥ v)).re) (fun v hv => by
      have hv0 : v ≠ 0 := by
        rintro rfl
        simp at hv
      have hpos : 0 < (star v ⬝ᵥ (mat h0 w *ᵥ v)).re := by
        have := (show (mat h0 w).PosDef from h0p).re_dotProduct_pos hv0
        simpa using this
      exact (isOpen_lt continuous_const hg).mem_nhds hpos)
  filter_upwards [hev] with h hh
  exact posDef_of_sphere (mat_herm h w) fun v hv => hh v (by simpa using hv)

theorem pos_open_convex (L : Type) [Field L] [NumberField L] (N : ℕ) :
    IsOpen (Pos L N) ∧ Convex ℝ (Pos L N) := by
  refine ⟨?_, ?_⟩
  · have : Pos L N = ⋂ w, {h : HS L N | (mat h w).PosDef} := by
      ext h
      simp [Pos]
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_posW w
  · intro x hx y hy a b ha hb hab w
    show (mat (a • x + b • y) w).PosDef
    rw [mat_add, mat_smul, mat_smul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hy w
    · exact ((hx w).smul ha').add_posSemidef ((hy w).posSemidef.smul hb)

theorem actL_scal {L : Type} [Field L] [NumberField L] {N : ℕ} (s : InfinitePlace L → ℂˣ)
    (hs : ∀ w w', ‖(s w : ℂ)‖ = ‖(s w' : ℂ)‖) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : HS L N, actL (scal L N s) h = r • h := by
  by_cases hne : Nonempty (InfinitePlace L)
  · obtain ⟨w0⟩ := hne
    have hs0 : (s w0 : ℂ) ≠ 0 := (s w0).ne_zero
    refine ⟨(‖(s w0 : ℂ)‖ ^ 2)⁻¹, by positivity, fun h => HS_ext fun w => ?_⟩
    have e : ((((scal L N s) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        Matrix.scalar (Fin N) ((s w : ℂ)⁻¹) := by
      simp only [scal, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val]
    rw [mat_actL, mat_smul, e]
    have hc : star ((s w : ℂ)⁻¹) * (s w : ℂ)⁻¹ = (((‖(s w0 : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', norm_inv, hs w w0]
      push_cast
      ring
    ext i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.smul_apply, Pi.star_apply]
    rw [Complex.real_smul, ← hc]
    ring
  · refine ⟨1, one_pos, fun h => HS_ext fun w => absurd ⟨w⟩ hne⟩

end PositivityTheory.KB.WhittakerCocycle

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.SkipSuccAbove
section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

theorem skip_zero_cons (γ : Γ) (σ : ℕ → Γ) : skip 0 (cons γ σ) = σ := by
  funext n; simp [skip, cons]

theorem skip_succ_cons (i : ℕ) (γ : Γ) (σ : ℕ → Γ) : skip (i + 1) (cons γ σ) = cons γ (skip i σ) := by
  funext n
  cases n with
  | zero => simp [skip, cons]
  | succ m => simp [skip, cons]

theorem delG_cons (n : ℕ) {X : Type} [AddCommGroup X] [Module ℝ X] (β : (ℕ → Γ) → X) (γ : Γ)
    (σ : ℕ → Γ) : delG (n + 1) β (cons γ σ) = β σ - delG n (fun τ => β (cons γ τ)) σ := by
  simp only [delG]
  rw [Finset.sum_range_succ', skip_zero_cons]
  simp only [skip_succ_cons, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    pow_zero, one_smul]
  abel

theorem skip_succAbove {m : ℕ} (σ : ℕ → Γ) (i : Fin (m + 2)) (l : Fin (m + 1)) :
    skip (i : ℕ) σ (l : ℕ) = σ ((i.succAbove l : Fin (m + 2)) : ℕ) := by
  rw [skip]
  rcases lt_or_ge (l : ℕ) (i : ℕ) with hl | hl
  · rw [if_pos hl, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hl)]
    simp
  · rw [if_neg (not_lt.mpr hl), Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hl)]
    simp

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

theorem pLoc : PLoc U A φ := by
  intro H h hh
  obtain ⟨t, ht, hfin⟩ := H.locFin ⟨h, hh⟩
  obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype U ⟨h, hh⟩ t).mp ht
  refine ⟨hfin.toFinset, u ∩ U, inter_mem hu (H.isOpen.mem_nhds hh), inter_subset_right, ?_⟩
  intro γ hγ x hx
  by_contra hne
  apply hγ
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨x, hx.2⟩, hne, hut hx.1⟩

theorem finsum_psi (hL : PLoc U A φ) (H : Hyp U A φ) {h : V} (hh : h ∈ U) :
    ∃ s : Finset Γ, ∃ W ∈ 𝓝 h, W ⊆ U ∧ ∀ x ∈ W, (∑ γ ∈ s, psi A φ γ x = 1) ∧
      ∀ {M : Type} [AddCommGroup M] [Module ℝ M] (F : Γ → M),
        ∑ᶠ γ, psi A φ γ x • F γ = ∑ γ ∈ s, psi A φ γ x • F γ := by
  obtain ⟨s, W, hW, hWU, hs⟩ := hL H h hh
  refine ⟨s, W, hW, hWU, fun x hx => ⟨?_, ?_⟩⟩
  · have h1 := H.sum_one x (hWU hx)
    rw [finsum_eq_sum_of_support_subset (s := s)] at h1
    · exact h1
    · intro γ hγ
      by_contra hγs
      exact hγ (hs γ hγs x hx)
  · intro M _ _ F
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs x hx]

theorem pHom (hL : PLoc U A φ) : PHom U A φ := by
  intro H q n β σ h hh
  obtain ⟨s, W, hW, hWU, hs⟩ := finsum_psi U A φ hL H hh
  obtain ⟨h1, hF⟩ := hs h (mem_of_mem_nhds hW)
  have hK : ∀ (β' : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) τ,
      Kf A φ β' τ h = ∑ γ ∈ s, psi A φ γ h • β' (cons γ τ) h :=
    fun β' τ => hF (fun γ => β' (cons γ τ) h)
  rw [hK (delG (n + 1) β)]
  simp only [delG_cons, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1,
    one_smul, sub_sub_cancel]
  simp only [delG, Finset.sum_apply, Pi.smul_apply, hK, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _

end PositivityTheory.KB.WhittakerCocycle

end
end

