module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveLatticeHomRingOfIntegersOfFinrank
section
open NumberField

private lemma rk (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [h : DiscreteTopology Λ] : Module.finrank ℤ Λ ≤ 2 * g := by
  have h1 := Real.finrank_eq_int_finrank_of_discrete (E := Fin g → ℂ) (s := (Λ : Set (Fin g → ℂ))) (by rw [Submodule.span_eq]; exact h)
  have h2 : Set.finrank ℤ (Λ : Set (Fin g → ℂ)) = Module.finrank ℤ Λ := by
    unfold Set.finrank; rw [Submodule.span_eq]
  have h3 : Set.finrank ℝ (Λ : Set (Fin g → ℂ)) ≤ Module.finrank ℝ (Fin g → ℂ) := Submodule.finrank_le _
  have h4 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  omega

theorem UpperTheory.exists_injective_lattice_hom_ringOfIntegers_of_finrank_ge :
    ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
        (α : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), 2 * g ≤ Module.finrank ℚ E → DiscreteTopology Λ →
        ∀ (hs : ∀ s, ∀ z ∈ Λ, α s z ∈ Λ),
        ∃ ι : Λ →+ 𝓞 E, Function.Injective ι ∧ ∀ (s : 𝓞 E) (x : Λ), ι ⟨α s x, hs s x x.2⟩ = s * ι x := by
  intro E _ _ g Λ α hg hd hs
  by_cases h0 : ∀ x : Λ, x = 0
  · refine ⟨0, fun a b _ => by rw [h0 a, h0 b], fun s x => by simp⟩
  push Not at h0
  obtain ⟨x0, hx0⟩ := h0
  let ψ' : 𝓞 E →+ Λ :=
    { toFun := fun s => ⟨α s x0, hs s x0 x0.2⟩
      map_zero' := by ext1; simp
      map_add' := fun a b => by ext1; simp }
  let ψ : 𝓞 E →ₗ[ℤ] Λ := ψ'.toIntLinearMap
  have hψ : ∀ s, (ψ s : Fin g → ℂ) = α s x0 := fun s => rfl
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs0
    by_contra hne
    have hz : α s x0 = 0 := by rw [← hψ, hs0]; rfl
    have hm := Ideal.absNorm_mem (Ideal.span {s})
    have hn : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hne
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
    have : α (t * s) x0 = 0 := by rw [map_mul, Module.End.mul_apply, hz, map_zero]
    rw [ht, map_natCast, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at this
    rcases this with h | h
    · exact hn (by exact_mod_cast h)
    · exact hx0 (Subtype.ext h)
  have hr : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ Λ := by
    apply le_antisymm (Submodule.finrank_le _)
    rw [LinearMap.finrank_range_of_inj hinj, RingOfIntegers.rank]
    exact (rk g Λ).trans hg
  have hfin : Finite (Λ ⧸ LinearMap.range ψ) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  set d := Nat.card (Λ ⧸ LinearMap.range ψ) with hdd
  have hd0 : d ≠ 0 := Nat.card_pos.ne'
  have hmem : ∀ x : Λ, ∃ t, ψ t = d • x := by
    intro x
    have : (LinearMap.range ψ).mkQ (d • x) = 0 := by
      rw [map_nsmul]; exact card_nsmul_eq_zero'
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  choose f hf using hmem
  refine ⟨AddMonoidHom.mk' f (fun a b => hinj ?_), fun a b hab => ?_, fun s x => hinj ?_⟩
  · rw [map_add (f := _), hf, hf, hf, smul_add]
  · have h1 : f a = f b := hab
    have h2 : d • a = d • b := by rw [← hf, ← hf, h1]
    have h3 : (d : ℂ) • (a : Fin g → ℂ) = (d : ℂ) • (b : Fin g → ℂ) := by
      simp only [Nat.cast_smul_eq_nsmul]
      exact congrArg Subtype.val h2
    exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hd0) h3)
  · change ψ (f _) = ψ (s * f x)
    rw [hf]
    ext1
    rw [hψ, map_mul, Module.End.mul_apply, ← hψ, hf]
    exact (map_nsmul (α s) d (x : Fin g → ℂ)).symm
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsNsmulMemSumImageLatticeOfSurjectiveMod
section
open NumberField

theorem UpperTheory.exists_nsmul_mem_sum_image_lattice_of_surjective_mod :
    ∀ (gA gB p : ℕ) (ΛA : Submodule ℤ (Fin gA → ℂ)) (ΛB : Submodule ℤ (Fin gB → ℂ))
        (J : Fin p → (Fin gA → ℂ) →ₗ[ℂ] (Fin gB → ℂ)),
        Submodule.span ℝ (ΛA : Set (Fin gA → ℂ)) = ⊤ → DiscreteTopology ΛB →
        (∀ a, ∀ z ∈ ΛA, J a z ∈ ΛB) → (∀ w, ∃ v : Fin p → (Fin gA → ℂ), w - ∑ a, J a (v a) ∈ ΛB) →
        ∀ l ∈ ΛB, ∃ (N : ℕ) (x : Fin p → (Fin gA → ℂ)), 0 < N ∧ (∀ a, x a ∈ ΛA) ∧ N • l = ∑ a, J a (x a) := by
  intro gA gB p ΛA ΛB J hA hB hJ hsurj l hl
  classical
  set Φ : (Fin p → (Fin gA → ℂ)) →ₗ[ℝ] (Fin gB → ℂ) :=
    ∑ a, ((J a).restrictScalars ℝ).comp (LinearMap.proj a) with hΦ
  have hΦapp : ∀ x, Φ x = ∑ a, J a (x a) := by
    intro x
    simp [hΦ]
  let Sz : Submodule ℤ (Fin gB → ℂ) :=
    Submodule.map (Φ.restrictScalars ℤ) (Submodule.pi Set.univ (fun _ => ΛA))
  have hSzB : Sz ≤ ΛB := by
    rintro y ⟨x, hx, rfl⟩
    show Φ x ∈ ΛB
    rw [hΦapp]
    exact Submodule.sum_mem _ (fun a _ => hJ a (x a) (Submodule.mem_pi.mp hx a (Set.mem_univ a)))
  haveI : Countable ΛB := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hΦs : ∀ u, ∃ v, Φ v = u := by
    intro u
    by_contra hu
    push_neg at hu
    choose v hv using fun t : ℝ => hsurj (t • u)
    let f : ℝ → ΛB := fun t => ⟨t • u - Φ (v t), by rw [hΦapp]; exact hv t⟩
    have hf : Function.Injective f := by
      intro t t' htt
      have h1 : t • u - Φ (v t) = t' • u - Φ (v t') := congrArg Subtype.val htt
      by_contra hne
      apply hu ((t - t')⁻¹ • (v t - v t'))
      rw [map_smul, map_sub]
      have h2 : (t - t') • u = Φ (v t) - Φ (v t') := by
        rw [sub_smul, sub_eq_sub_iff_sub_eq_sub]
        exact h1
      rw [← h2, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
    exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hf.countable)
  have hspan : Submodule.span ℝ (Sz : Set (Fin gB → ℂ)) = ⊤ := by
    rw [eq_top_iff]
    rintro u -
    obtain ⟨v, rfl⟩ := hΦs u
    rw [hΦapp]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    have hva : v a ∈ Submodule.span ℝ (ΛA : Set (Fin gA → ℂ)) := by
      rw [hA]
      trivial
    have hsub : ((J a).restrictScalars ℝ) '' (ΛA : Set (Fin gA → ℂ)) ⊆ (Sz : Set (Fin gB → ℂ)) := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨Pi.single a z, Submodule.mem_pi.mpr (fun b _ => ?_), ?_⟩
      · by_cases hb : b = a
        · subst hb
          simpa using hz
        · simp [Pi.single_eq_of_ne hb]
      · show Φ (Pi.single a z) = J a z
        rw [hΦapp, Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · simp
    exact Submodule.span_mono hsub ((Submodule.span_image _).ge (Submodule.mem_map_of_mem hva))
  obtain ⟨t, htS, htspan, hti⟩ := exists_linearIndependent ℝ (Sz : Set (Fin gB → ℂ))
  let b : Module.Basis t ℝ (Fin gB → ℂ) :=
    Module.Basis.mk hti (by simp only [Subtype.range_coe, htspan, hspan, le_refl])
  haveI : Finite t := Module.Finite.finite_basis b
  haveI : Fintype t := Fintype.ofFinite t
  have hbS : ∀ i, b i ∈ Sz := fun i => by
    rw [Module.Basis.mk_apply]
    exact htS i.2
  have hzS : Submodule.span ℤ (Set.range b) ≤ Sz :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbS i)
  haveI : DiscreteTopology ΛB.toAddSubgroup := ‹DiscreteTopology ΛB›
  haveI : DiscreteTopology (ΛB : Set (Fin gB → ℂ)) := ‹DiscreteTopology ΛB›
  have hcl : IsClosed (ΛB : Set (Fin gB → ℂ)) := (ΛB.toAddSubgroup).isClosed_of_discreteTopology
  have hfin : ((ZSpan.fundamentalDomain b) ∩ (ΛB : Set (Fin gB → ℂ))).Finite :=
    Metric.finite_isBounded_inter_isClosed (isDiscrete_iff_discreteTopology.mpr ‹_›)
      (ZSpan.fundamentalDomain_isBounded b) hcl
  have hmem : ∀ n : ℕ, ZSpan.fract b (n • l) ∈ (ZSpan.fundamentalDomain b) ∩ (ΛB : Set (Fin gB → ℂ)) := by
    intro n
    refine ⟨ZSpan.fract_mem_fundamentalDomain b _, ?_⟩
    rw [ZSpan.fract_apply]
    exact ΛB.sub_mem (ΛB.nsmul_mem hl n) (hSzB (hzS (ZSpan.floor b (n • l)).2))
  obtain ⟨m, n, hmn, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  have hdiff : (n - m) • l ∈ Sz := by
    have h1 : (n - m) • l = n • l - m • l := by
      rw [eq_sub_iff_add_eq, ← add_nsmul, Nat.sub_add_cancel hmn.le]
    rw [ZSpan.fract_apply, ZSpan.fract_apply] at heq
    have h2 : n • l - m • l = (ZSpan.floor b (n • l) : Fin gB → ℂ) - ZSpan.floor b (m • l) := by
      rw [sub_eq_sub_iff_sub_eq_sub]
      exact heq.symm
    rw [h1, h2]
    exact Sz.sub_mem (hzS (ZSpan.floor b _).2) (hzS (ZSpan.floor b _).2)
  obtain ⟨x, hx, hxe⟩ := hdiff
  refine ⟨n - m, x, Nat.sub_pos_of_lt hmn, fun a => Submodule.mem_pi.mp hx a (Set.mem_univ a), ?_⟩
  rw [← hxe]
  exact hΦapp x
end

