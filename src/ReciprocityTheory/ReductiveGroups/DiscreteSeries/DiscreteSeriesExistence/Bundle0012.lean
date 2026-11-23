module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DataGenSubIrred
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

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

theorem data_form_scalar (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (b : D →ₗ⋆[ℂ] D →ₗ[ℂ] ℂ)
    (hbE : ∀ a c, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, b (E a c x) y = adjSign ε a c * b x (E c a y))
    (hbK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, ∀ x' ∈ genSub E V, ∀ y' ∈ genSub E V,
      (x' : H) = σ k x → (y' : H) = σ k y → b x' y' = b x y) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, b x y = c * inner ℂ (x : H) (y : H) := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have hwG : w ∈ genSub E V := rorth_le_genSub hwV
  have hww : inner ℂ w w ≠ 0 := inner_self_ne_zero.2 hw0
  set cc : ℂ := b w w / inner ℂ w w with hcdef
  set f : D →ₗ[ℂ] ℂ := b w - cc • innerₛₗ ℂ w with hf
  have hfapp : ∀ y, f y = b w y - cc * inner ℂ w y := fun y => by simp [hf]
  have hfw : f w = 0 := by rw [hfapp, hcdef, div_mul_cancel₀ _ hww, sub_self]
  have hfd : ∀ a, ∀ y ∈ genSub E V, f (E a a y) = (lowK ε lam a : ℂ) * f y := by
    intro a y hy
    have h1 := hbE a a w hwG y hy
    have h2 := hU a a w y
    simp only [hw.1 a, adjSign, if_true, one_mul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_ofReal, inner_smul_left] at h1 h2
    rw [hfapp, hfapp, ← h1, ← h2]
    ring
  have hfl : ∀ a b', a < b' → ε a = ε b' → ∀ y ∈ genSub E V, f (E b' a y) = 0 := by
    intro a b' hab h y hy
    have h1 := hbE a b' w hwG y hy
    have h2 := hU a b' w y
    rw [hw.2 a b' hab h, map_zero, LinearMap.zero_apply,
      show adjSign ε a b' = 1 by simp [adjSign, h], one_mul] at h1
    rw [hw.2 a b' hab h, inner_zero_left, show adjSign ε a b' = 1 by simp [adjSign, h], one_mul] at h2
    rw [hfapp, ← h1, ← h2]
    simp
  have hfz : ∀ y ∈ genSub E V, f y = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨u, huG, hu, huy, huV'⟩ := schA_riesz hE hU hV.1 hV.2.1 (genSub E V) le_rfl
      (fun a b _ x hx => rorth_apply_mem_genSub a b hx) f (lowK ε lam) hfd hfl hy
    have huV : u ∈ V := khw_lowK_mem hE hU hV hc hgap huG hu
    obtain ⟨c', hc'⟩ := khw_line_of_kIrrHW hE hU hV huV hwV hu hw hw0
    have h3 := huV' w ⟨hwG, hwV⟩
    rw [hfw, hc', inner_smul_left] at h3
    have hc0 : c' = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · simpa using h
      · exact absurd h hww
    rw [hc', hc0, zero_smul, inner_zero_left] at huy
    exact hne huy.symm
  let X : Submodule ℂ D :=
    { carrier := {x | x ∈ genSub E V ∧ ∀ y ∈ genSub E V, b x y = cc * inner ℂ x y}
      add_mem' := fun {x x'} hx hx' => ⟨(genSub E V).add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add (f := _), LinearMap.add_apply, hx.2 y hy, hx'.2 y hy, inner_add_left, mul_add]⟩
      zero_mem' := ⟨(genSub E V).zero_mem, fun y _ => by simp⟩
      smul_mem' := fun r x hx => ⟨(genSub E V).smul_mem r hx.1, fun y hy => by
        rw [map_smulₛₗ, LinearMap.smul_apply, hx.2 y hy, inner_smul_left, smul_eq_mul]; ring⟩ }
  have hX : ∀ a c, ∀ x ∈ X, E a c x ∈ X := by
    intro a c x hx
    refine ⟨rorth_apply_mem_genSub a c hx.1, fun y hy => ?_⟩
    rw [hbE a c x hx.1 y hy, hx.2 _ (rorth_apply_mem_genSub c a hy), hU]
    ring
  have hwX : w ∈ X := ⟨hwG, fun y hy => by
    have := hfz y hy
    rw [hfapp, sub_eq_zero] at this
    exact this⟩
  have hle := schA_genSub_le hV X hX hwV hwX hw0
  exact ⟨cc, fun x hx y hy => (hle hx).2 y hy⟩

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

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def dinj_jLin (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := uniformisationL2 ε Ψ v₀
  map_add' := datumEmbedding_add hP v₀
  map_smul' := datumEmbedding_smul hP v₀

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dinj_continuousOn_of_smoothOnGV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) : ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg₀U)] with g hg
  exact hfF g hg.2 hg.1

end

theorem uniformisationL2_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (uniformisationL2 ε Ψ v₀) := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat g ∈ UJset ε := fun g => g.2
  have hum : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hΨu : Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
    (dinj_continuousOn_of_smoothOnGV hP.2.2.1).comp_continuous hum hmem
  have hfc : ∀ v, Continuous (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) := by
    intro v
    simp only [jfun]
    exact continuous_const.inner (hΨu.clm_apply continuous_const)
  have hML : ∀ v, MemLp (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) 2
      (Formalism.REAL.muG ε) := by
    intro v
    have hH : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
    have h0 := hP.2.2.2.2 (Formalism.REAL.muG ε) hH
    have h2 := ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v)).comp_memLp' h0
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun g => ?_) h2
    simp [jfun] <;> rfl
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by unfold Formalism.REAL.muG; infer_instance
  have hz : ∀ v, uniformisationL2 ε Ψ v₀ v = 0 ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 := by
    intro v
    have hm := hML v
    have e1 : uniformisationL2 ε Ψ v₀ v = hm.toLp _ := by
      unfold uniformisationL2 toL2
      exact dif_pos hm
    rw [e1, Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h g
      have h5 := ((hfc v).ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).mp
        (hm.coeFn_toLp.symm.trans h)
      exact congrFun h5 g
    · intro h
      exact hm.coeFn_toLp.trans (Filter.Eventually.of_forall fun g => h g)
  have hstab : ∀ (k : S7.KG ε) (v : T.V),
      (∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0) →
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ (T.op k v) (Formalism.MainNotions.S.umat g) = 0 := by
    intro k v hv g
    have hk := hP.1 1 k (Formalism.MainNotions.S.umat g) (hmem g)
    have ht1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    have ho1 : T.op 1 = 1 := by simp [S7.KType.op]
    rw [ht1, ho1, one_mul, one_mul] at hk
    let y : Formalism.REAL.UJ ε := (k : S7.UJ ε)
    have hy : Formalism.MainNotions.S.umat (g * y) = Formalism.MainNotions.S.umat g * S7.toMK k := rfl
    have h3 := hv (g * y)
    rw [hy] at h3
    simp only [jfun] at h3 ⊢
    rw [hk] at h3
    simpa using h3
  have hne : uniformisationL2 ε Ψ v₀ v₀ ≠ 0 := by
    intro h0
    have h6 : jfun Ψ v₀ v₀ 1 = 0 := (hz v₀).1 h0 1
    simp only [jfun, hP.2.1, ContinuousLinearMap.one_apply] at h6
    exact hv₀ (inner_self_eq_zero.mp h6)
  have hker : ∀ v, v ∈ LinearMap.ker (dinj_jLin hP v₀) ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 :=
    fun v => LinearMap.mem_ker.trans (hz v)
  rcases T.irred (LinearMap.ker (dinj_jLin hP v₀))
      (fun k v hv => (hker _).2 (hstab k v ((hker v).1 hv))) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exfalso
    have hv : v₀ ∈ LinearMap.ker (dinj_jLin hP v₀) := by
      rw [h]
      exact Submodule.mem_top
    exact hne (LinearMap.mem_ker.1 hv)

end ReciprocityTheory.ChartRestriction.DS
end
end

