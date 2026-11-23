module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CohBoundFree
section
open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.CuspRep CategoryTheory UpperTheory.V.Af UpperTheory.V.Af.CohB

@[reducible] private def act {G H : Type} [Group G] [Group H] (ι : H →* G) (Γ : Subgroup H) (U : Subgroup G) :
    MulAction ↥Γ (G ⧸ U) := MulAction.compHom _ (ι.comp Γ.subtype)

private theorem gen (hE : BddEquiv) (hA : AbsBound) (hF : FibCard) {G H : Type} [Group G] [Group H] (ι : H →* G)
    (Γ : Subgroup H) (U : Subgroup G) (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ u ∈ U, g = ι γ * t * u)
    (S : G → Subgroup H) (hS : ∀ g γ, γ ∈ S g ↔ g⁻¹ * ι γ * g ∈ U) (hB : ∀ g, Bdd ↥(Γ ⊓ S g)) :
    ∃ c : ℕ, ∀ U' : Subgroup G, U' ≤ U → U'.relIndex U ≠ 0 → ∀ D : ℕ, U'.relIndex U ≤ D →
      ∀ (d : ℕ) (ξ : ↥Γ →* Matrix (Fin d) (Fin d) ℂ),
        totCoh (Rep.of (@funRep ↥Γ _ (G ⧸ U') (act ι Γ U') d ξ)) ≤ (c * D * d : ℕ) := by
  classical
  letI := act ι Γ U
  have hsm : ∀ (γ : ↥Γ) (g : G), γ • (g : G ⧸ U) = ((ι γ.1 * g : G) : G ⧸ U) := fun _ _ => rfl
  obtain ⟨T, hT'⟩ := hT
  obtain ⟨c, hc⟩ := hA ↥Γ (G ⧸ U)
    ⟨T.image (↑), fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨γ, hγ, t, ht, u, hu, rfl⟩ := hT' g
      refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, Finset.mem_image.2 ⟨t, ht, ?_⟩⟩
      rw [hsm, QuotientGroup.eq]
      simpa [mul_assoc] using hu⟩
    (fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have e : MulAction.stabilizer ↥Γ (g : G ⧸ U) = (Γ ⊓ S g).subgroupOf Γ := by
        ext γ
        rw [MulAction.mem_stabilizer_iff, hsm, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hS,
          mul_assoc]
        exact ⟨fun h => ⟨γ.2, h⟩, fun h => h.2⟩
      exact hE ↥(Γ ⊓ S g) _
        ⟨((MulEquiv.subgroupCongr e).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)).symm⟩ (hB g))
  refine ⟨c, fun U' hle h0 D hD d ξ => ?_⟩
  letI := act ι Γ U'
  exact hc (G ⧸ U') (Subgroup.quotientMapOfLE hle)
    (fun γ x => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rfl) D
    (fun y => by rw [hF _ _ _ hle h0 y]; exact_mod_cast hD) d ξ

private theorem levelRep_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (Γ : Subgroup (GL (Fin n) F))
    (U : Subgroup (GL (Fin n) (Af F))) {d : ℕ} (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    levelRep Γ U ξ = @funRep ↥Γ _ (GL (Fin n) (Af F) ⧸ U) (act (ratAf F n) Γ U) d (ξ.comp Γ.subtype) := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun f => funext fun x => ?_
  change ξ γ *ᵥ f ((ratAf F n γ.1)⁻¹ • x) = ξ γ *ᵥ f ((ratAf F n (γ.1)⁻¹) • x)
  rw [map_inv]

private theorem cohBound_of (hE : BddEquiv) (hA : AbsBound) (hF : FibCard)
    (hO : FinOrbAbs) (hI : KLevIdx) (hD : FinDC) (h1 : ArithOne) (hC : ArithComm) :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) := by
  intro F _ _ hF' n Γ hΓ
  obtain ⟨c, hc⟩ := gen hE hA hF (ratAf F n) Γ (KLev F n 3)
    (hO _ _ (ratAf F n) Γ (KLev F n 3) (KLev F n 1) hΓ (hI F n 3 (by norm_num)).1 (hD F n))
    (fun g => arith g (KLev F n 3)) (fun g γ => mem_arith) fun g => (bddArith F hF' n _
      (h1 F n ▸ hC F n Γ hΓ g _ (by apply isOpen_KLev; norm_num) (by apply isCompact_KLev; norm_num)))
  refine ⟨c * 3 ^ (Module.finrank ℚ F * (n * n)), Module.finrank ℚ F * (n * n), fun M hM d ξ => ?_⟩
  have hle : KLev F n (3 * M) ≤ KLev F n 3 := KLev_le_of_dvd (dvd_mul_right 3 M)
  have hle1 : KLev F n 3 ≤ KLev F n 1 := KLev_le_of_dvd (one_dvd 3)
  obtain ⟨hi0, hi⟩ := hI F n (3 * M) (by omega)
  have hr0 : (KLev F n (3 * M)).relIndex (KLev F n 3) ≠ 0 := fun h => hi0 (Subgroup.relIndex_eq_zero_of_le_right hle1 h)
  have hr : (KLev F n (3 * M)).relIndex (KLev F n 3) ≤ (3 * M) ^ (Module.finrank ℚ F * (n * n)) :=
    (Subgroup.relIndex_le_of_le_right hle1 hi0).trans hi
  have key := hc _ hle hr0 _ hr d (ξ.comp Γ.subtype)
  rw [← levelRep_eq] at key
  have e : c * 3 ^ (Module.finrank ℚ F * (n * n)) * M ^ (Module.finrank ℚ F * (n * n)) * d =
      c * (3 * M) ^ (Module.finrank ℚ F * (n * n)) * d := by rw [mul_pow, mul_assoc c]
  rw [e]
  exact key

theorem UpperTheory.V.Af.cohBoundFree :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) :=
  cohBound_of UpperTheory.cohomology_bounded_equiv
    (UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound (UpperTheory.cohomology_part_bound_of_sum_bound UpperTheory.cohomology_sum_bound UpperTheory.cohomology_part_split) (UpperTheory.orbit_bound_of_shapiro_functorial (UpperTheory.shapiro_functorial_of_coinduction_bijective UpperTheory.cohomology_to_coinvariants_injective UpperTheory.cohomology_to_coinvariants_surjective)))
    UpperTheory.adelic_cohomology_fiber_card UpperTheory.adelic_cohomology_finite_orbit_bound (UpperTheory.level_subgroup_index_bound_of_card_ohat UpperTheory.card_ohat_quotient_natCast) UpperTheory.finite_adelic_double_cosets UpperTheory.arithmetic_subgroup_level_one UpperTheory.arithmetic_subgroups_commensurable
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspFin
section
open NumberField GlobalTheory.CuspRep UpperTheory.V

private theorem sqId {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) :
    ∑ i, ∑ j, E i j * E i j = Formalism.REAL.Cas E + (1 / 2 : ℂ) • ∑ i, ∑ j, (E i j - E j i) * (E i j - E j i) := by
  have h1 : ∑ i, ∑ j, E j i * E j i = ∑ i, ∑ j, E i j * E i j := Finset.sum_comm
  have h2 : ∑ i, ∑ j, E j i * E i j = ∑ i, ∑ j, E i j * E j i := Finset.sum_comm
  simp only [Formalism.REAL.Cas, sub_mul, mul_sub, Finset.sum_sub_distrib, h1, h2]
  module

private theorem aevalShift {M : Type} [AddCommGroup M] [Module ℂ M] (Ω D : Module.End ℂ M) (h : Commute Ω D) (ω : ℂ)
    (q : Polynomial ℂ) (x : M) (hx : Ω x = ω • x) :
    Polynomial.aeval (Ω + D) (q.comp (Polynomial.X - Polynomial.C ω)) x = Polynomial.aeval D q x := by
  have hp : ∀ (n : ℕ) (x : M), Ω x = ω • x → ((Ω + D - algebraMap ℂ _ ω) ^ n) x = (D ^ n) x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      have e : (Ω + D - algebraMap ℂ _ ω) x = D x := by simp [hx]
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, e, ih]
      rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply, hx, map_smul]
  rw [Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_eq_sum_range,
    Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hp _ x hx]

theorem UpperTheory.V.Af.cuspFormsFiniteReal :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (L : Subgroup (GL (Fin a) (Af F))), IsOpen (L : Set (GL (Fin a) (Af F))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (TR.Kinf F a) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ c : InfinitePlace F → ℂ → ℂ, FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F a | TR.IsCuspForm φ ∧ (∀ k ∈ L, TR.finRep F a k φ = φ) ∧ (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧ ∀ v u, TR.cap v u φ = c v u • φ}) := by
  intro F _ _ _ a L hL W _ _ _ ρ _ c
  classical
  obtain ⟨b, hb⟩ := UpperTheory.V.Af.CuspFin.exists_stdBasis F a
  have hbE : ∀ l, TR.lie F a (b l) = TR.Eop l.1 l.2.1 l.2.2 := fun l => by rw [hb]; rfl
  let S : Subalgebra ℂ (Module.End ℂ (TR.Sm F a)) :=
    { carrier := {z | ∃ t : ℂ, ∀ φ : TR.Sm F a, (∀ v u, TR.cap v u φ = c v u • φ) → z φ = t • φ}
      mul_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨t * s, fun φ h => by rw [Module.End.mul_apply, ht φ h, map_smul, hs φ h, mul_smul]⟩
      add_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, fun φ h => by rw [LinearMap.add_apply, ht φ h, hs φ h, add_smul]⟩
      algebraMap_mem' := fun t => ⟨t, fun φ _ => rfl⟩ }
  have hq : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a := a) v) u = TR.cap v (u - ((a : ℂ) - 1) / 2) := fun v u => by
    rw [TR.cap, sub_add_cancel]
  have hS : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a := a) v) u ∈ S := fun v u => ⟨_, fun φ h => by rw [hq]; exact h v _⟩
  have hZ : ∀ (v : InfinitePlace F) u, Formalism.REAL.qdet (TR.Eop (a := a) v) u ∈ TR.Zalg F a := fun v u =>
    Algebra.subset_adjoin ⟨v, _, hq v u⟩
  obtain ⟨ω, hω⟩ : ∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v) ∈ S :=
    sum_mem fun v _ => UpperTheory.V.Af.CuspFin.casMem _ _ _ (TR.glRel_Eop v) S (hS v)
  have hΩ : ∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v) ∈ TR.Zalg F a :=
    sum_mem fun v _ => UpperTheory.V.Af.CuspFin.casMem _ _ _ (TR.glRel_Eop v) _ (hZ v)
  have hone : TR.oneL F a = ∑ v, ∑ i, b (v, i, i) := by
    funext i j w
    simp only [hb, Finset.sum_apply]
    by_cases hij : i = j <;> simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hij, ite_and, ite_apply]
  obtain ⟨t, ht⟩ : TR.lie F a (TR.oneL F a) ∈ S := by
    rw [hone]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hbE]
    exact sum_mem fun v _ => GlobalTheory.CuspRep.Central.trace_mem _ (Subalgebra.toSubmodule S) (one_mem S) (hS v)
  let X : InfinitePlace F × Fin a × Fin a → TR.Lie F a := fun l => b l - b (l.1, l.2.2, l.2.1)
  have hX : ∀ l i j, X l j i = -X l i j := by
    rintro ⟨v, p, q⟩ i j
    simp only [X, hb, Pi.sub_apply, neg_sub]
    simp [Matrix.single_apply, and_comm]
  obtain ⟨q, hm, hd, hq0⟩ := UpperTheory.V.Af.CuspFin.typePoly F a W ρ _ X hX (1 / 2)
  have hΔ : ∑ l, TR.lie F a (b l) * TR.lie F a (b l) = ∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v) +
      (1 / 2 : ℂ) • ∑ l, TR.lie F a (X l) * TR.lie F a (X l) := by
    simp only [X, map_sub, hbE, Fintype.sum_prod_type]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => sqId (TR.Eop v)
  have hc : Commute (∑ v, Formalism.REAL.Cas (TR.Eop (E := F) (a := a) v))
      ((1 / 2 : ℂ) • ∑ l, TR.lie F a (X l) * TR.lie F a (X l)) :=
    (Commute.sum_right _ _ _ fun l _ => (TR.Cen.commute_Zalg_act hΩ (.lie (X l))).mul_right
      (TR.Cen.commute_Zalg_act hΩ (.lie (X l)))).smul_right _
  have hm' : (q.comp (Polynomial.X - Polynomial.C ω)).Monic := hm.comp (Polynomial.monic_X_sub_C ω) (by simp)
  have hd' : 0 < (q.comp (Polynomial.X - Polynomial.C ω)).natDegree := by
    rw [Polynomial.natDegree_comp]; simpa using hd
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ (UpperTheory.V.Af.CuspFin.eigenFinite_of UpperTheory.V.Af.CuspFin.mem_cuspForms_of _ b _ hm' hd' t L hL) (Submodule.span_mono ?_)
  rintro φ ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, by rw [hΔ, aevalShift _ _ hc ω q φ (hω φ h4), hq0 φ h3], ht φ h4⟩
end

