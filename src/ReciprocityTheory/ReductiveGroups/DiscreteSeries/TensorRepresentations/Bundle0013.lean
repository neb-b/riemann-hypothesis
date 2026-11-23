module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CartanKType
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PosSemidefWeightedInnerNonneg
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerC
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem cns_kType_iso {ε : Fin n → Bool} {Λ₁ Λ₂ : Fin n → ℝ} (h : Λ₁ = Λ₂) (T₁ : S7.KType ε Λ₁)
    (T₂ : S7.KType ε Λ₂) : ∃ φ : T₁.V ≃ₗᵢ[ℂ] T₂.V, ∀ k v, φ (T₁.op k v) = T₂.op k (φ v) := by
  subst h
  obtain ⟨φ, hφ, -⟩ := HW.kType_unique T₁ T₂
  exact ⟨φ, hφ⟩

theorem cns_kt_weight_eq {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ₁ Λ₂ : Fin n → ℝ} {S₁ : Submodule ℂ H}
    (h₁ : Formalism.MainNotions.S.IsKTypeOf ε σ Λ₁ S₁) (h₂ : Formalism.MainNotions.S.IsKTypeOf ε σ Λ₂ ⊤) : Λ₁ = Λ₂ := by
  obtain ⟨-, hst1, -, ⟨v1, hv1S, hv10, hv1w⟩, hdom1⟩ := h₁
  obtain ⟨-, -, hirr2, ⟨v2, -, hv20, hv2w⟩, hdom2⟩ := h₂
  have hS1 : S₁ = ⊤ := by
    rcases hirr2 S₁ le_top hst1 with h | h
    · rw [h] at hv1S
      exact absurd ((Submodule.mem_bot ℂ).1 hv1S) hv10
    · exact h
  have c1 : Formalism.MainNotions.S.CDom ε Λ₁ Λ₂ := hdom2 Λ₁ v1 Submodule.mem_top hv10 hv1w
  have c2 : Formalism.MainNotions.S.CDom ε Λ₂ Λ₁ := hdom1 Λ₂ v2 (hS1 ▸ Submodule.mem_top) hv20 hv2w
  exact cdom_antisymm ε c1 c2

theorem cns_cpt_dec {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    (ρ : S7.KG ε →* unitary (Matrix (Fin n) (Fin n) ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous (fun k : S7.KG ε => ((ρ k : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → S7.KG ε, (∀ t : ℝ, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j) (dρ X i j) 0)
    (γw : Fin n → Fin n → ℝ) (hinj : Function.Injective γw)
    (hP1 : ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : Fin n => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) ν x →
      ∃ s, ν = Λ + γw s ∧ HW.KDom ε (Λ + γw s))
    (hP2 : ∀ s, Module.finrank ℂ (HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
      (Λ + γw s)) ≤ 1)
    (hP3 : ∀ s, HW.KDom ε (Λ + γw s) → ∃ x : PiLp 2 (fun _ : Fin n => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (Λ + γw s) x)
    (Sm : Finset (Fin n)) (hSm : ∀ s, s ∈ Sm ↔ HW.KDom ε (Λ + γw s))
    (Λs : Fin n → Fin n → ℝ) (hΛs : ∀ s ∈ Sm, Λs s = Λ + γw s) (Ts : ∀ s, S7.KType ε (Λs s)) :
    ∃ j : ∀ s, (Ts s).V →ₗ[ℂ] PiLp 2 (fun _ : Fin n => T.V),
      (∀ s ∈ Sm, ∀ v w, inner ℂ (j s v) (j s w) = inner ℂ v w) ∧
      (∀ s ∈ Sm, ∀ k v, j s ((Ts s).op k v) = HW.tensOp T ρ k (j s v)) ∧
      (∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ∀ v v', inner ℂ (j s v) (j s' v') = 0) ∧
      ∀ x, ∃ v : ∀ s, (Ts s).V, x = ∑ s ∈ Sm, j s (v s) := by
  classical
  let R : HW.KRep ε :=
    { V := PiLp 2 (fun _ : Fin n => T.V), τ := HW.tensTau T ρ, cont := HW.tensTau_cont T ρ hc,
      dτ := HW.tensD T dρ, hasDeriv := fun X hX γ hγ => HW.tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ) }
  have hRu : R.units = HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)) :=
    HW.tensKRep_units T ρ dρ hc hd
  have hRop : ∀ k, R.op k = HW.tensOp T ρ k := fun k => rfl
  obtain ⟨hrelR, hunitR⟩ := HW.kRepRel n ε R
  obtain ⟨m, x, μ, hx, horth, htop, -, -, hT⟩ := HW.compRed n ε R
  rw [hRu] at hrelR hunitR hx horth htop hT
  choose idx hidx hdom using fun i => hP1 (μ i) (x i) (hx i).1 (hx i).2
  have hidx_inj : Function.Injective idx := by
    intro i i' hii
    by_contra hne
    have hk : x i ∈ HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γw (idx i)) := (HW.count_mem_khwSub_iff _ _ _ _).2 (by rw [← hidx i]; exact (hx i).2)
    have hk' : x i' ∈ HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γw (idx i)) := (HW.count_mem_khwSub_iff _ _ _ _).2 (by rw [hii, ← hidx i']; exact (hx i').2)
    exact HW.count_not_two_of_finrank_le_one _ (hP2 (idx i)) hk hk' (hx i).1 (hx i').1
      (horth i i' hne _ (HW.count_mem_kSpan_self _ _ _) _ (HW.count_mem_kSpan_self _ _ _))
  have hpiece : ∀ (ν : Fin n → ℝ) (y : PiLp 2 (fun _ : Fin n => T.V)), y ≠ 0 →
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) ν y →
      ∃ k, μ k = ν := by
    intro ν y hy0 hy
    by_contra hno
    push Not at hno
    apply hy0
    refine HW.count_eq_zero_of_orth _ htop y fun k z hz => ?_
    exact Formalism.REAL.kOrth _ n ε _ ν (μ k) y (x k) hrelR hunitR hy (hx k).2 (hno k).symm y
      (HW.count_mem_kSpan_self _ _ _) z hz
  have hsurj : ∀ s ∈ Sm, ∃ i, idx i = s := by
    intro s hs
    obtain ⟨y, hy0, hy⟩ := hP3 s ((hSm s).1 hs)
    obtain ⟨i, hi⟩ := hpiece _ y hy0 hy
    exact ⟨i, hinj (add_left_cancel ((hidx i).symm.trans hi))⟩
  have hmem : ∀ i, idx i ∈ Sm := fun i => (hSm _).2 (hdom i)
  have hj : ∀ s, ∃ js : (Ts s).V →ₗ[ℂ] PiLp 2 (fun _ : Fin n => T.V), s ∈ Sm → ∃ i, idx i = s ∧
      (∀ v, js v ∈ Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)) ∧
      (∀ y ∈ Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i),
        ∃ v, js v = y) ∧
      (∀ v w, inner ℂ (js v) (js w) = inner ℂ v w) ∧
      (∀ k v, js ((Ts s).op k v) = HW.tensOp T ρ k (js v)) := by
    intro s
    by_cases hs : s ∈ Sm
    · obtain ⟨i, hi⟩ := hsurj s hs
      obtain ⟨Tk, φ, -, hφ, -, -⟩ := hT i
      obtain ⟨ψ, hψ⟩ := cns_kType_iso (show Λs s = μ i by rw [hΛs s hs, hidx i, hi]) (Ts s) Tk
      refine ⟨(Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)).subtype
        ∘ₗ φ.toLinearEquiv.toLinearMap ∘ₗ ψ.toLinearEquiv.toLinearMap, fun _ => ⟨i, hi, ?_, ?_, ?_, ?_⟩⟩
      · intro v
        exact (φ (ψ v)).2
      · intro y hy
        refine ⟨ψ.symm (φ.symm ⟨y, hy⟩), ?_⟩
        show (φ (ψ (ψ.symm (φ.symm ⟨y, hy⟩)))).1 = y
        rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
      · intro v w
        show inner ℂ (φ (ψ v)).1 (φ (ψ w)).1 =
          inner ℂ v w
        rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
      · intro k v
        show (φ (ψ ((Ts s).op k v))).1 = HW.tensOp T ρ k (φ (ψ v)).1
        rw [hψ, hφ, hRop]
    · exact ⟨0, fun h => absurd h hs⟩
  choose j hj using hj
  refine ⟨j, fun s hs => (hj s hs).choose_spec.2.2.2.1, fun s hs => (hj s hs).choose_spec.2.2.2.2,
    fun s hs s' hs' hne v v' => ?_, fun y => ?_⟩
  · obtain ⟨i, hi, hin, -⟩ := hj s hs
    obtain ⟨i', hi', hin', -⟩ := hj s' hs'
    have hii : i ≠ i' := fun h => hne (hi.symm.trans (h ▸ hi'))
    exact horth i i' hii _ (hin v) _ (hin' v')
  · have hy : y ∈ ⨆ i ∈ (univ : Finset (Fin m)),
        Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i) := by
      have e : (⨆ i ∈ (univ : Finset (Fin m)),
          Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)) =
          ⨆ i, Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i) := by
        simp
      rw [e, htop]
      exact Submodule.mem_top
    obtain ⟨μf, hμf⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy
    have hv : ∀ s, ∃ v : (Ts s).V, s ∈ Sm → ∀ i, idx i = s → j s v = (μf i : PiLp 2 (fun _ : Fin n => T.V)) := by
      intro s
      by_cases hs : s ∈ Sm
      · obtain ⟨i, hi, -, hsur, -⟩ := hj s hs
        obtain ⟨v, hv⟩ := hsur _ (μf i).2
        refine ⟨v, fun _ i' hi' => ?_⟩
        have : i' = i := hidx_inj (hi'.trans hi.symm)
        subst this
        exact hv
      · exact ⟨0, fun h => absurd h hs⟩
    choose v hv using hv
    refine ⟨v, ?_⟩
    rw [← hμf]
    exact Finset.sum_bij (fun a _ => idx a) (fun a _ => hmem a) (fun a _ b _ h => hidx_inj h)
      (fun b hb => let ⟨a, ha⟩ := hsurj b hb; ⟨a, mem_univ _, ha⟩)
      (fun a _ => (hv (idx a) (hmem a) a rfl).symm)

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CuspProjectionOrthogonality
section
noncomputable section

open Finset MeasureTheory
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem psi_coef_expand (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) :
    ob2PsiCoef dual Ψ ξ ζ g = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (ξ c) (Ψ g (ζ d)) := by
  simp only [ob2PsiCoef, inner_sum, inner_smul_right, oa1Phi]

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem continuous_spherical_psi (hP : IsPsiFor ε lam T Ψ) :
    Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
  (ffa_continuousOn hP.2.2.1).comp_continuous continuous_umat' (fun g => g.2)

theorem psi_twist_coef_memLp (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  simp_rw [psi_coef_expand]
  refine memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => ?_
  refine (hWT (ζ d) (ξ c)).of_le ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner
      ((continuous_spherical_psi hP).clm_apply continuous_const))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_tensor_phi_le_sqrt_hs g.2 dual c d) (norm_nonneg _)

theorem psi_term_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u v : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) (Formalism.REAL.muG ε) := by
  have h1 := (psi_twist_coef_memLp dual hP hWT ξ ζ).star
  have h2 : MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) :=
    memLp_muG_of_haar ε (fun x => inner ℂ u (Ψ' x v)) 2
      (fun μ hμ => (pdA_coef u v).comp_memLp' (hP'.2.2.2.2 μ hμ))
  exact h1.integrable_mul h2

end Psi

theorem psi_twist_at_one (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (hΨ : Ψ 1 = 1) (u : Fin n → T.V) :
    ob2B dual Ψ 1 u = u := by
  funext c
  have hφ : ∀ d, oa1Phi dual 1 c d = if c = d then 1 else 0 := by
    intro d
    cases dual
    · simp [oa1Phi, Matrix.one_apply]
    · simp [oa1Phi, Matrix.one_apply, eq_comm]
  simp [ob2B, hφ, hΨ, ite_smul]

section Main

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

def ob2Fij (dual : Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V))
    (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)) (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V))
    (i j : Fin (Module.finrank ℂ T'.V)) (g : Formalism.REAL.UJ ε) : ℂ :=
  starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
    (Formalism.MainNotions.S.umat g)) *
  inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))

theorem psi_pairing_at_one_re_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0) :
    0 < (∑ i, ∑ j, ob2Fij (ε := ε) dual Ψ Ψ' ι₀ i j 1).re := by
  set b := stdOrthonormalBasis ℂ T'.V
  have e : (∑ i, ∑ j, ob2Fij (ε := ε) dual Ψ Ψ' ι₀ i j 1) =
      ∑ j, ob2SI (ob2B dual Ψ 1 (ι₀ (b j))) (ι₀ (Ψ' 1 (b j))) :=
    psi_pairing_eq_inner dual Ψ Ψ' ι₀ (1 : Matrix (Fin n) (Fin n) ℂ)
  rw [e]
  simp only [psi_twist_at_one dual Ψ hP.2.1, hP'.2.1, ContinuousLinearMap.one_apply]
  obtain ⟨j, hj⟩ : ∃ j, ι₀ (b j) ≠ 0 := by
    by_contra h
    push Not at h
    exact hι₀ (b.toBasis.ext fun j => by simpa using h j)
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hj
  have key : ∀ x : T.V, (inner ℂ x x).re = ‖x‖ ^ 2 := fun x => inner_self_eq_norm_sq (𝕜 := ℂ) x
  simp only [ob2SI, Complex.re_sum, key]
  have hc' : ι₀ (b j) c ≠ 0 := by simpa using hc
  exact Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun c _ => by positivity)
    ⟨j, Finset.mem_univ _, Finset.sum_pos' (fun c _ => by positivity)
      ⟨c, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hc') 2⟩⟩

theorem continuous_psi_pairing_sum (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) :
    Continuous (fun g : Formalism.REAL.UJ ε => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) := by
  have h1 := continuous_spherical_psi hP
  have h2 := continuous_spherical_psi hP'
  have h3 := continuous_tensor_phi (ε := ε) dual
  simp only [ob2Fij, psi_coef_expand]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (Complex.continuous_conj.comp (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
      (h3 c d).mul (continuous_const.inner (h1.clm_apply continuous_const)))).mul
      (continuous_const.inner (h2.clm_apply continuous_const))

theorem psi_pairing_trace_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0)
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ob2TauF dual T k (ι₀ v)) :
    0 < (∑ i, ∑ j, ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
        (Formalism.MainNotions.S.umat g)) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))
        ∂(Formalism.REAL.muG ε)).re := by
  show 0 < (∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε)).re
  have hint : ∀ i j, Integrable (ob2Fij dual Ψ Ψ' ι₀ i j) (Formalism.REAL.muG ε) := fun i j =>
    psi_term_integrable dual hP hP' hWT _ _ _ _
  have hFi : Integrable (fun g => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) (Formalism.REAL.muG ε) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  have hsum : ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε) =
      ∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
  rw [← hsum]
  have hre : (∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε)).re =
      ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re ∂(Formalism.REAL.muG ε) :=
    (integral_re hFi).symm
  rw [hre]
  have hG0 : 0 ≤ fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re := by
    intro g
    have h := psi_pairing_nonneg dual hP hP' hpos hpos' ι₀ hK (g := Formalism.MainNotions.S.umat g) g.2
    have h' := (Complex.le_def.mp h).1
    rw [Complex.zero_re] at h'
    exact h'
  have hGc : Continuous fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re :=
    Complex.continuous_re.comp (continuous_psi_pairing_sum dual hP hP' ι₀)
  rw [integral_pos_iff_support_of_nonneg hG0 hFi.re]
  exact hGc.isOpen_support.measure_pos _ ⟨1, Function.mem_support.mpr (psi_pairing_at_one_re_pos dual hP hP' ι₀ hι₀).ne'⟩

end Main

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ExistsKEquivariantMap
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lowWeight_shifted (dual : Bool) (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF dual lam s) = cond dual (lowK ε lam - Pi.single s 1) (lowK ε lam + Pi.single s 1) := by
  cases dual <;> simp only [shiftF, lowK, cond] <;> abel

theorem exists_kEquivariant_map {ε : Fin n → Bool} (R : HW.KRep ε) {μ : Fin n → ℝ} (x : R.V) (hx : x ≠ 0)
    (hh : Formalism.REAL.KHighest ε R.units μ x) (T' : S7.KType ε μ) :
    ∃ f : T'.V →ₗ[ℂ] R.V, f ≠ 0 ∧ ∀ (k : S7.KG ε) (v : T'.V), f (T'.op k v) = R.op k (f v) := by
  obtain ⟨T'', φ, hφ, -, -⟩ := HW.kRepPiece n ε R μ x hx hh
  obtain ⟨ψ, hψ, -, -⟩ := HW.kType_unique T' T''
  refine ⟨(Submodule.subtype _).comp (φ.toLinearEquiv.toLinearMap.comp ψ.toLinearEquiv.toLinearMap), ?_, ?_⟩
  · intro h
    have h1 := LinearMap.congr_fun h T'.w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, ZeroMemClass.coe_eq_zero,
      LinearIsometryEquiv.map_eq_zero_iff] at h1
    have h2 := T'.w_norm
    rw [h1, norm_zero] at h2
    exact zero_ne_one h2
  · intro k v
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [hψ, hφ]

theorem tensor_unitary_rep {ε : Fin n → Bool} {Λ μ : Fin n → ℝ} (T : S7.KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : S7.KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : S7.KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → S7.KG ε, (∀ t : ℝ, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0)
    (T' : S7.KType ε μ) (x : PiLp 2 (fun _ : ι => T.V)) (hx : x ≠ 0)
    (hxh : Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) μ x) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (ι → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) =
        fun c => ∑ d, ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) c d • T.op k (ι₀ v d) := by
  rw [← HW.tensKRep_units T ρ dρ hc hd] at hxh
  obtain ⟨f, hf, hfK⟩ := exists_kEquivariant_map (HW.tensKRep T ρ dρ hc hd) x hx hxh T'
  let g : T'.V →ₗ[ℂ] PiLp 2 (fun _ : ι => T.V) := f
  have hg : ∀ k v, g (T'.op k v) = HW.tensOp T ρ k (g v) := fun k v => hfK k v
  refine ⟨(WithLp.linearEquiv 2 ℂ (ι → T.V)).toLinearMap ∘ₗ g, ?_, ?_⟩
  · intro h
    apply hf
    ext v
    have h1 := LinearMap.congr_fun h v
    have h2 : g v = 0 := by simpa using h1
    exact h2
  · intro k v
    funext c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hg]
    simp [HW.tensOp_apply]

theorem pieri_standard_embedding (dual : Bool) {ε : Fin n → Bool} {Λ Λ' : Fin n → ℝ} (T : S7.KType ε Λ) (T' : S7.KType ε Λ')
    (s : Fin n) (hΛ : Λ' = cond dual (Λ - Pi.single s 1) (Λ + Pi.single s 1)) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) =
        fun c => ∑ d, (cond dual (star (S7.toMK k c d)) (S7.toMK k c d)) • T.op k (ι₀ v d) := by
  have hdom := (HW.kTypeIntDom n ε Λ' T').2
  cases dual with
  | false =>
    have hΛ' : Λ' = Λ + HW.stdWt n s := hΛ
    subst hΛ'
    obtain ⟨x, hx, hxh⟩ := (HW.pieriStd n ε Λ T).2.2 s hdom
    exact tensor_unitary_rep T (HW.stdRho ε) LinearMap.id (HW.stdRho_cont ε) (HW.stdRho_hasDeriv ε) T' x hx hxh
  | true =>
    have hΛ' : Λ' = Λ + HW.dualWt n s := by
      rw [hΛ]; simp only [cond, HW.dualWt, sub_eq_add_neg]
    subst hΛ'
    obtain ⟨x, hx, hxh⟩ := (HW.pieriDual n ε Λ T).2.2 s hdom
    rw [← HW.dualD_units] at hxh
    exact tensor_unitary_rep T (HW.rhoDual ε) HW.dualD (HW.continuous_rhoDual ε) (HW.hasDeriv_rhoDual ε) T' x hx hxh

end ReciprocityTheory.ChartRestriction.DS
end
end

