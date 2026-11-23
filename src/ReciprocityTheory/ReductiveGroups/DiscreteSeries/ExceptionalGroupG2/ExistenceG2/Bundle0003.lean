module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_genSub_irred (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (N : Submodule ℂ D) (hN : N ≤ genSub E V)
    (hNE : ∀ a b, ∀ x ∈ N, E a b x ∈ N) (hNK : ∀ k ∈ Kset ε, ∀ x ∈ N, ∃ y ∈ N, (y : H) = σ k x) :
    N = ⊥ ∨ N = genSub E V := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have hwG : w ∈ genSub E V := rorth_le_genSub hwV
  by_cases hVN : ∃ x ∈ N ⊓ V, x ≠ 0
  · obtain ⟨x, hx, hx0⟩ := hVN
    exact Or.inr (le_antisymm hN (schA_genSub_le hV N hNE hx.2 hx.1 hx0))
  push Not at hVN
  have hNk : IsKStableSub ε E N := fun a b _ x hx => hNE a b x hx
  have hfd : ∀ a, ∀ y ∈ N, (innerₛₗ ℂ w) (E a a y) = (lowK ε lam a : ℂ) * (innerₛₗ ℂ w) y := by
    intro a y _
    have h1 := hU a a w y
    simp only [hw.1 a, inner_smul_left, adjSign, if_true, one_mul, Complex.conj_ofReal] at h1
    simp only [innerₛₗ_apply_apply]
    exact h1.symm
  have hfl : ∀ a b, a < b → ε a = ε b → ∀ y ∈ N, (innerₛₗ ℂ w) (E b a y) = 0 := by
    intro a b hab h y _
    have h1 := hU a b w y
    rw [hw.2 a b hab h, inner_zero_left, show adjSign ε a b = 1 by simp [adjSign, h], one_mul] at h1
    simp only [innerₛₗ_apply_apply]
    exact h1.symm
  have horth : ∀ z ∈ N, inner ℂ z w = 0 := by
    intro z hz
    rw [← inner_eq_zero_symm]
    by_contra hne
    obtain ⟨u, huN, hu, huz, -⟩ :=
      schA_riesz hE hU hV.1 hV.2.1 N hN hNk (innerₛₗ ℂ w) (lowK ε lam) hfd hfl hz
    have huV : u ∈ V := khw_lowK_mem hE hU hV hc hgap (hN huN) hu
    have := hVN u ⟨huN, huV⟩
    rw [this, inner_zero_left, innerₛₗ_apply_apply] at huz
    exact hne huz.symm
  have hY : ∀ a b, ∀ y ∈ genSub E V ⊓ Nᗮ, E a b y ∈ genSub E V ⊓ Nᗮ := by
    intro a b y hy
    refine ⟨rorth_apply_mem_genSub a b hy.1, (Submodule.mem_orthogonal _ _).2 fun z hz => ?_⟩
    have h1 := hU b a z y
    rw [(Submodule.mem_orthogonal _ _).1 hy.2 _ (hNE b a z hz)] at h1
    calc inner ℂ z (E a b y) = (adjSign ε b a * adjSign ε b a) * inner ℂ z (E a b y) := by
          rw [schA_adjSign_sq, one_mul]
      _ = adjSign ε b a * (adjSign ε b a * inner ℂ z (E a b y)) := by ring
      _ = 0 := by rw [← h1, mul_zero]
  have hle := schA_genSub_le hV _ hY hwV ⟨hwG, (Submodule.mem_orthogonal _ _).2 horth⟩ hw0
  refine Or.inl ((Submodule.eq_bot_iff _).2 fun z hz => ?_)
  exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (hle (hN hz)).2 z hz)

theorem data_end_scalar (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (A : D →ₗ[ℂ] D) (hA : ∀ x ∈ genSub E V, A x ∈ genSub E V)
    (hAE : ∀ a b, ∀ x ∈ genSub E V, A (E a b x) = E a b (A x))
    (hAK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k x → (A y : H) = σ k (A x)) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, A x = c • x := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have hwG : w ∈ genSub E V := rorth_le_genSub hwV
  have hAw : IsKHWVec ε E (lowK ε lam) (A w) := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · rw [← hAE a a w hwG, hw.1 a, map_smul]
    · rw [← hAE a b w hwG, hw.2 a b hab h, map_zero]
  have hAwV : A w ∈ V := khw_lowK_mem hE hU hV hc hgap (hA w hwG) hAw
  obtain ⟨c, hc'⟩ := khw_line_of_kIrrHW hE hU hV hAwV hwV hAw hw hw0
  have hk : ∀ x, x ∈ LinearMap.ker (A - c • (1 : Module.End ℂ D)) ↔ A x = c • x := fun x => by
    simp [sub_eq_zero]
  have hX : ∀ a b, ∀ x ∈ genSub E V ⊓ LinearMap.ker (A - c • (1 : Module.End ℂ D)),
      E a b x ∈ genSub E V ⊓ LinearMap.ker (A - c • (1 : Module.End ℂ D)) := by
    intro a b x hx
    refine ⟨rorth_apply_mem_genSub a b hx.1, (hk _).2 ?_⟩
    rw [hAE a b x hx.1, (hk x).1 hx.2, map_smul]
  have hle := schA_genSub_le hV _ hX hwV ⟨hwG, (hk w).2 hc'⟩ hw0
  exact ⟨c, fun x hx => (hk x).1 (hle hx).2⟩

end Data

section Two

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] {lam₁ : Fin n → ℝ}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {lam₂ : Fin n → ℝ}
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

end Two

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamKTypeBounds
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
section Transfer

variable {n : ℕ} {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {ε : Fin n → Bool}

end Transfer

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}

variable {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem rreg_mem_Hlam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ v₀, rreg ε g x ∈ Hlam ε Ψ v₀ :=
  ReciprocityTheory.ChartRestriction.DS.G2.closGen_stable hgap (ReciprocityTheory.ChartRestriction.DS.rreg_isURepOn ε)
    (ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE (ReciprocityTheory.ChartRestriction.DS.rreg_isURepOn ε))
    (ReciprocityTheory.ChartRestriction.DS.datumV_isKIrrHW hP hv₀) (ReciprocityTheory.ChartRestriction.DS.datumV_casimir hP v₀)
    (ReciprocityTheory.ChartRestriction.DS.datumV_kStable hP v₀)

theorem sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (x : Hlam ε Ψ v₀) :
    ((sigLam ε Ψ v₀ g x : Hlam ε Ψ v₀) : L2 ε) = rreg ε g x := by
  have hmem : rreg ε g (x : L2 ε) ∈ Hlam ε Ψ v₀ := rreg_mem_Hlam hgap hP hv₀ g hg (x : L2 ε) x.2
  show (Hlam ε Ψ v₀).starProjection (rreg ε g (x : L2 ε)) = rreg ε g (x : L2 ε)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w _
  rw [sub_self, inner_zero_left]

theorem sigLam_isURepOn (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := by
  obtain ⟨⟨hr1, hrm⟩, hriso, hrc⟩ := rreg_isURepOn ε
  have hc : ∀ {g : Matrix (Fin n) (Fin n) ℂ}, g ∈ UJset ε → ∀ x : Hlam ε Ψ v₀,
      ((sigLam ε Ψ v₀ g x : Hlam ε Ψ v₀) : L2 ε) = rreg ε g x :=
    fun hg x => sigLam_coe hgap hP hv₀ hg x
  have h1mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * 1 = ReciprocityTheory.ChartRestriction.DS.Jm ε
    simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rw [hc h1mem, hr1]
    rfl
  · intro a ha b hb
    have ha' : aᴴ * (ReciprocityTheory.ChartRestriction.DS.Jm ε * a) = ReciprocityTheory.ChartRestriction.DS.Jm ε := by
      rw [← Matrix.mul_assoc]; exact ha
    have hb' : bᴴ * (ReciprocityTheory.ChartRestriction.DS.Jm ε * b) = ReciprocityTheory.ChartRestriction.DS.Jm ε := by
      rw [← Matrix.mul_assoc]; exact hb
    have hab : a * b ∈ UJset ε := by
      show (a * b)ᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * (a * b) = ReciprocityTheory.ChartRestriction.DS.Jm ε
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc (ReciprocityTheory.ChartRestriction.DS.Jm ε) a b, ← Matrix.mul_assoc aᴴ, ha', hb']
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rw [hc hab, hrm a ha b hb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      hc ha, hc hb]
  · intro g hg x
    show ‖((sigLam ε Ψ v₀ g x : Hlam ε Ψ v₀) : L2 ε)‖ = ‖(x : L2 ε)‖
    rw [hc hg]
    exact hriso g hg x
  · intro x
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (hrc (x : L2 ε)).congr (fun g hg => hc hg x)

theorem sigLam_irred (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ v₀) := by
  intro S hSc hSG
  have hσ := ReciprocityTheory.ChartRestriction.DS.rreg_isURepOn ε
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hV := ReciprocityTheory.ChartRestriction.DS.datumV_isKIrrHW hP hv₀
  have hc := ReciprocityTheory.ChartRestriction.DS.datumV_casimir hP v₀
  have hVK := ReciprocityTheory.ChartRestriction.DS.datumV_kStable hP v₀
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.coe_injective
  have hHc : IsClosed ((Hlam ε Ψ v₀ : Submodule ℂ (L2 ε)) : Set (L2 ε)) :=
    Submodule.isClosed_topologicalClosure _
  have hS'c : IsClosed ((S.map (Hlam ε Ψ v₀).subtype : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    rw [Submodule.map_coe]
    exact hHc.isClosedEmbedding_subtypeVal.isClosedMap _ hSc
  have hSG' : ∀ g ∈ UJset ε, ∀ x ∈ S.map (Hlam ε Ψ v₀).subtype,
      rreg ε g x ∈ S.map (Hlam ε Ψ v₀).subtype := by
    rintro g hg _ ⟨y, hy, rfl⟩
    exact ⟨sigLam ε Ψ v₀ g y, hSG g hg y hy, ReciprocityTheory.ChartRestriction.DS.G2.sigLam_coe hgap hP hv₀ hg y⟩
  rcases ReciprocityTheory.ChartRestriction.DS.G2.rigid_irred hgap hσ hD hV hc hVK _
      (ReciprocityTheory.ChartRestriction.DS.map_subtype_le_closGen S) hS'c hSG' with h | h
  · left
    exact Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
  · right
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_subtype_top]
    rfl

theorem Hlam_nontrivial (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Nontrivial (Hlam ε Ψ v₀) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply ReciprocityTheory.ChartRestriction.DS.datumV_ne_bot hP hv₀
  have h1 : (lowKSubLam ε Ψ v₀).map (Hlam ε Ψ v₀).subtype = ⊥ := by
    haveI := h
    rw [show lowKSubLam ε Ψ v₀ = ⊥ from Submodule.eq_bot_of_subsingleton, Submodule.map_bot]
  rw [ReciprocityTheory.ChartRestriction.DS.map_lowKSubLam] at h1
  exact Submodule.map_injective_of_injective Subtype.coe_injective (h1.trans (Submodule.map_bot _).symm)

theorem subtype_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, (Hlam ε Ψ v₀).subtype (sigLam ε Ψ v₀ g x) =
      rreg ε g ((Hlam ε Ψ v₀).subtype x) := by
  intro g hg x
  obtain ⟨h1, h2⟩ := hg
  have h2' : g * ReciprocityTheory.ChartRestriction.DS.Jm ε = ReciprocityTheory.ChartRestriction.DS.Jm ε * g := h2
  have hU : g ∈ UJset ε := by
    show gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * g = ReciprocityTheory.ChartRestriction.DS.Jm ε
    rw [Matrix.mul_assoc, ← h2', ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').mp h1, Matrix.one_mul]
  exact sigLam_coe hgap hP hv₀ hU x

theorem sigLam_lowK (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) (Formalism.QuantumDeterminants.lowK ε lam) (lowKSubLam ε Ψ v₀) ∧
      ∀ S : Submodule ℂ (Hlam ε Ψ v₀), Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) (Formalism.QuantumDeterminants.lowK ε lam) S →
        S = lowKSubLam ε Ψ v₀ := by
  have hσ := ReciprocityTheory.ChartRestriction.DS.rreg_isURepOn ε
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hV := ReciprocityTheory.ChartRestriction.DS.datumV_isKIrrHW hP hv₀
  have hc := ReciprocityTheory.ChartRestriction.DS.datumV_casimir hP v₀
  have hVK := ReciprocityTheory.ChartRestriction.DS.datumV_kStable hP v₀
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.coe_injective
  have hint := ReciprocityTheory.ChartRestriction.DS.G2.subtype_sigLam hgap hP hv₀
  refine ⟨?_, ?_⟩
  · rw [ReciprocityTheory.ChartRestriction.DS.isKTypeOf_map_iff (Hlam ε Ψ v₀).subtype hinj hint,
      ReciprocityTheory.ChartRestriction.DS.map_lowKSubLam]
    exact ReciprocityTheory.ChartRestriction.DS.isKTypeOf_of_isKIrrHW hσ hD hV hVK
      (fun μ x hx hx0 hμ => ReciprocityTheory.ChartRestriction.DS.datumV_weight_le hP hv₀ hx hx0 hμ)
  · intro S hS
    rw [ReciprocityTheory.ChartRestriction.DS.isKTypeOf_map_iff (Hlam ε Ψ v₀).subtype hinj hint] at hS
    have h := ReciprocityTheory.ChartRestriction.DS.G2.data_lowK_eq hgap hσ hD hV hc hVK (S.map (Hlam ε Ψ v₀).subtype)
      (ReciprocityTheory.ChartRestriction.DS.map_subtype_le_closGen S) hS
    rw [← ReciprocityTheory.ChartRestriction.DS.map_lowKSubLam] at h
    exact Submodule.map_injective_of_injective hinj h

theorem sigLam_kType_bounds (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {μ : Fin n → ℝ} (S : Submodule ℂ (Hlam ε Ψ v₀))
    (hS : Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ ∧
      ∀ h : ℝ, GapAtLeast ε lam h → 2 * (n : ℝ) < h → μ ≠ lowK ε lam →
        casValK ε (lowK ε lam) + 2 * (h - n + 1) ≤ casValK ε μ := by
  have hσ := ReciprocityTheory.ChartRestriction.DS.rreg_isURepOn ε
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hV := ReciprocityTheory.ChartRestriction.DS.datumV_isKIrrHW hP hv₀
  have hc := ReciprocityTheory.ChartRestriction.DS.datumV_casimir hP v₀
  have hVK := ReciprocityTheory.ChartRestriction.DS.datumV_kStable hP v₀
  have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.coe_injective
  have hint := ReciprocityTheory.ChartRestriction.DS.G2.subtype_sigLam hgap hP hv₀
  rw [ReciprocityTheory.ChartRestriction.DS.isKTypeOf_map_iff (Hlam ε Ψ v₀).subtype hinj hint] at hS
  have hle := ReciprocityTheory.ChartRestriction.DS.map_subtype_le_closGen S
  exact ⟨ReciprocityTheory.ChartRestriction.DS.G2.data_vogan hgap hσ hD hV hc hVK _ hle hS,
    fun h hh hbig hμ => ReciprocityTheory.ChartRestriction.DS.G2.data_casValK_gap hgap hσ hD hV hc hVK hh hbig _ hle hS hμ⟩

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

