module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0015
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyCapA
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem anyCap_word_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (w : List (Fin n × Fin n)) {x : M} (hx : x ∈ genSub E V) :
    (w.map fun p => E p.1 p.2).prod x ∈ genSub E V := by
  induction w with
  | nil => simpa using hx
  | cons p w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact ICD.gen_stable ih p.1 p.2

theorem anyCap_adj {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (V : Submodule ℂ M) (u : ℂ) :
    ∃ C : Module.End ℂ M, (∀ x ∈ genSub E V, C x ∈ genSub E V) ∧
      ∀ x y : M, inner ℂ x (Formalism.REAL.qdet E u y) = inner ℂ (C x) y := by
  classical
  obtain ⟨l, hl⟩ := qdet_eq_sum_words E u
  refine ⟨(l.map fun c => (starRingEnd ℂ c.1 * (c.2.map fun p => adjSign ε p.1 p.2).prod) •
      ((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod).sum, ?_, ?_⟩
  · intro x hx
    clear hl
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply]
      exact add_mem (Submodule.smul_mem _ _ (anyCap_word_mem _ hx)) ih
  · intro x y
    rw [hl]
    clear hl
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply,
        inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
      rw [ih]
      congr 1
      have h := eword_adjoint hU c.2 y x
      have h' : inner ℂ x ((c.2.map fun p => E p.1 p.2).prod y) =
          starRingEnd ℂ (c.2.map fun p => adjSign ε p.1 p.2).prod *
            inner ℂ (((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod x) y := by
        rw [← inner_conj_symm, h, map_mul, inner_conj_symm]
      rw [h', map_mul, starRingEnd_self_apply]
      ring

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RangeDatumEmbedding
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

end Gen

section Main

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def datumEmbedding (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] Hlam ε Ψ v₀ :=
  (ffaJ hP v₀).codRestrict (Hlam ε Ψ v₀) (fun v => datumEmbedding_mem_Hlam hP v)

theorem range_datumEmbedding (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    LinearMap.range (datumEmbedding hP v₀) = lowKSubLam ε Ψ v₀ := by
  have hspan : Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀)) = LinearMap.range (ffaJ hP v₀) := by
    exact Submodule.span_eq (LinearMap.range (ffaJ hP v₀))
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    have hs : uniformisationL2 ε Ψ v₀ v ∈ smD ε (rreg ε) := by
      exact datumEmbedding_mem_smooth hP v₀ v
    simp only [lowKSubLam, Submodule.mem_comap, Submodule.mem_map]
    refine ⟨⟨uniformisationL2 ε Ψ v₀ v, hs⟩, ?_, rfl⟩
    exact Submodule.subset_span ⟨v, rfl⟩
  · intro hx
    simp only [lowKSubLam, Submodule.mem_comap, Submodule.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hy' : (y : L2 ε) ∈ LinearMap.range (ffaJ hP v₀) := hspan ▸ hy
    obtain ⟨v, hv⟩ := hy'
    exact ⟨v, Subtype.ext (hv.trans hyx)⟩

theorem anyF (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) :
    ∃ j : T.V →L[ℂ] H, (∀ v, ‖j v‖ = ‖v‖) ∧
      (∀ (k : S7.KG ε) (v : T.V), σ (S7.toMK k) (j v) = j (T.op k v)) ∧
      LinearMap.range (j : T.V →ₗ[ℂ] H) = Formalism.MainNotions.S.lowKSub ε lam σ ∧
      ∀ g ∈ UJset ε, (ContinuousLinearMap.adjoint j).comp ((σ g).comp j) = Ψ g := by
  have hw : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hDS hgap hP hw
  have hc0 := datumEmbedding_highest_ne_zero hgap hP hw
  set c : ℝ := ‖uniformisationL2 ε Ψ T.w T.w‖ with hc
  have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc0)
  let jl : T.V →ₗ[ℂ] H := ((c : ℂ)⁻¹) • (U.toLinearEquiv.toLinearMap ∘ₗ datumEmbedding hP T.w)
  let j : T.V →L[ℂ] H := LinearMap.toContinuousLinearMap jl
  have hjv : ∀ v, j v = ((c : ℂ)⁻¹) • U (datumEmbedding hP T.w v) := fun v => rfl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  have hkey : ∀ g ∈ UJset ε, ∀ v v', inner ℂ (j v') (σ g (j v)) = inner ℂ v' (Ψ g v) := by
    intro g hg v v'
    rw [hjv, hjv, map_smul, ← hU g hg, inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map]
    have e := formulaF_sigLam hgap hP hw hg v v'
    rw [show datumEmbedding hP T.w v = (⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_Hlam hP v⟩ : Hlam ε Ψ T.w) from rfl,
      show datumEmbedding hP T.w v' = (⟨uniformisationL2 ε Ψ T.w v', datumEmbedding_mem_Hlam hP v'⟩ : Hlam ε Ψ T.w) from rfl, e]
    rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp
    rw [hc]
  have hiso : ∀ v, ‖j v‖ = ‖v‖ := by
    intro v
    have e := hkey 1 h1 v v
    rw [hDS.2.2.1.1.1, hP.2.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    have e2 : ‖j v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, e]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e2
  have hK : ∀ (k : S7.KG ε) v, σ (S7.toMK k) (j v) = j (T.op k v) := by
    intro k v
    rw [hjv, hjv, map_smul, ← hU _ (ffa_toMK_mem k)]
    congr 2
    apply Subtype.ext
    rw [sigLam_coe hgap hP hw (ffa_toMK_mem k)]
    exact rightRegular_datumEmbedding hP T.w v k
  have hrange : LinearMap.range (j : T.V →ₗ[ℂ] H) =
      (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap := by
    show LinearMap.range jl = _
    rw [LinearMap.range_smul _ _ (inv_ne_zero hcne), LinearMap.range_comp, range_datumEmbedding]
  have hintU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.toLinearMap (sigLam ε Ψ T.w g x) =
      σ g (U.toLinearEquiv.toLinearMap x) := by
    intro g hg x
    rw [mir_Kset_eq] at hg
    exact hU g (UnitaryGroupOfForm.K_mem_UJ hg) x
  have hintS : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.symm.toLinearMap (σ g x) =
      sigLam ε Ψ T.w g (U.toLinearEquiv.symm.toLinearMap x) := by
    intro g hg x
    apply U.injective
    have e := hintU g hg (U.toLinearEquiv.symm x)
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at e ⊢
    rw [e]
    simp
  have hlow : Formalism.MainNotions.S.lowKSub ε lam σ = (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap := by
    have hdef : Formalism.MainNotions.S.lowKSub ε lam σ =
        sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} := rfl
    have hset : {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} =
        {(lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap} := by
      ext S
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hS
        have h2 := (sigLam_lowK hgap hP hw).2 _
          ((isKTypeOf_map_iff _ U.toLinearEquiv.symm.injective hintS _ S).1 hS)
        rw [← h2, ← Submodule.map_comp]
        ext x
        simp
      · rintro rfl
        exact (isKTypeOf_map_iff _ U.toLinearEquiv.injective hintU _ _).1 (sigLam_lowK hgap hP hw).1
    rw [hdef, hset, sSup_singleton]
  refine ⟨j, hiso, hK, hrange.trans hlow.symm, fun g hg => ?_⟩
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun v' => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, hkey g hg v v']

end Main

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigCas
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_casOnSmooth (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : CasOnSmooth ε lam (sigLam ε Ψ v₀) :=
  casOnSmooth_of_isDS (isDS_sigLam hgap hP hv₀) hgap

end ReciprocityTheory.ChartRestriction.DS
end
end

