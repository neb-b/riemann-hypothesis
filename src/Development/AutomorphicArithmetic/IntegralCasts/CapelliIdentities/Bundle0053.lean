module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RestrictedProductMeasureSet
section
open MeasureTheory in
private theorem UpperTheory.restricted_product_measure_set
    (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
    (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
    (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v))
    [SigmaFinite μi] [∀ v, SigmaFinite (m v)]
    (hq : Measurable q) (hp : ∀ v, Measurable (p v)) (hK : ∀ v, MeasurableSet (K v))
    (h1 : ∀ v, m v (K v) = 1) (A : Set Gi) (hA : MeasurableSet A)
    (S : Finset V) (a : NNReal)
    (h : Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
      a • μi.prod (Measure.pi fun v : S => m v)) :
    μ {g | q g ∈ A ∧ ∀ v, p v g ∈ K v} = (a : ENNReal) * μi A := by
  have hf : Measurable (fun g => (q g, fun v : S => p v g)) :=
    hq.prodMk (Measurable.of_eval fun v => hp v)
  have hB : MeasurableSet (A ×ˢ (Set.univ.pi fun v : S => K v)) :=
    hA.prod (MeasurableSet.univ_pi fun v => hK v)
  have h2 := congrArg (fun ν => ν (A ×ˢ (Set.univ.pi fun v : S => K v))) h
  simp only [Measure.map_apply hf hB, Measure.restrict_apply (hf hB)] at h2
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.pi_pi] at h2
  simp only [h1, Finset.prod_const_one, mul_one] at h2
  rw [← h2]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_imp_iff]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, fun v => hb v⟩, fun v _ => hb v⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    refine ⟨ha, fun v => ?_⟩
    by_cases hv : v ∈ S
    · exact hb ⟨v, hv⟩
    · exact hc v hv

theorem UpperTheory.restricted_product_measure :
    ∀ (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
        (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
        (μ : MeasureTheory.Measure G) (μi : MeasureTheory.Measure Gi) (m : ∀ v, MeasureTheory.Measure (Gv v))
        [MeasureTheory.SigmaFinite μi] [∀ v, MeasureTheory.SigmaFinite (m v)],
        Measurable q → (∀ v, Measurable (p v)) → (∀ v, MeasurableSet (K v)) → (∀ v, m v (K v) = 1) →
        (∃ A : Set Gi, MeasurableSet A ∧ μi A ≠ 0 ∧ μi A ≠ ⊤) →
        ∀ (S T : Finset V) (a b : NNReal),
          MeasureTheory.Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
            a • μi.prod (MeasureTheory.Measure.pi fun v : S => m v) →
          MeasureTheory.Measure.map (fun g => (q g, fun v : T => p v g)) (μ.restrict {g | ∀ v ∉ T, p v g ∈ K v}) =
            b • μi.prod (MeasureTheory.Measure.pi fun v : T => m v) →
          a = b := by
  intro V G Gi Gv _ _ _ q p K μ μi m _ _ hq hp hK h1 ⟨A, hA, h0, ht⟩ S T a b hS hT
  have e1 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA S a hS
  have e2 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA T b hT
  have e : (a : ENNReal) * μi A = (b : ENNReal) * μi A := e1.symm.trans e2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 e)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RieszRepresentationSesquilinear
section
theorem UpperTheory.Reformulated.B.Qh51.riesz_representation_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [FiniteDimensional ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∀ (L : V →ₗ⋆[ℂ] ℂ), ∃ (u : V), ∀ (b : V), (L : V → ℂ) b = ((B : V → V →ₗ⋆[ℂ] ℂ) u : V → ℂ) b := by
  intro V _ _ _ B _ hpos L
  let e := Module.finBasis ℂ V
  let Φ : V →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    { toFun := fun u i => B u (e i)
      map_add' := fun u v => by funext i; simp
      map_smul' := fun c u => by funext i; simp }
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have h0 : B u = 0 := e.ext fun i => congrFun hu i
    by_contra hne
    have h := hpos u hne
    rw [h0] at h
    simp at h
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨u, hu⟩ := hsurj fun i => L (e i)
  have hL : L = B u := e.ext fun i => (congrFun hu i).symm
  exact ⟨u, fun b => by rw [hL]⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RightCosetSpaceCompact
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace.{u_1} :
    {G : Type u_1} → [inst : Group G] → Subgroup G → Type u_1 :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient (MulAction.orbitRel (↥Γ) G)

noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk.{u_1} :
    {G : Type u_1} → [inst : Group G] → (Γ : Subgroup G) → G → UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient.mk (MulAction.orbitRel (↥Γ) G)

theorem UpperTheory.Reformulated.B.RightCosetSpaceCompact.exists_isCompact_subset_mk_image.{u_1} :
    ∀ {G : Type u_1} [inst : Group G] (Γ : Subgroup G) [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] {K : Set (UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ)},
      IsCompact K → ∃ (D : Set G), IsCompact D ∧ K ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D := by
  intro G _ Γ _ _ _ K hK
  have hopen : IsOpenMap (UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ) :=
    isOpenMap_quotient_mk'_mul (Γ := ↥Γ) (T := G)
  refine hK.induction_on
    (p := fun S => ∃ D : Set G, IsCompact D ∧ S ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, Set.empty_subset _⟩
  · rintro s t hst ⟨D, hD, htD⟩
    exact ⟨D, hD, hst.trans htD⟩
  · rintro s t ⟨D, hD, hsD⟩ ⟨E, hE, htE⟩
    refine ⟨D ∪ E, hD.union hE, ?_⟩
    rw [Set.image_union]
    exact Set.union_subset_union hsD htE
  · intro x _
    obtain ⟨g, rfl⟩ : ∃ g : G, UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ g = x := Quotient.exists_rep x
    obtain ⟨D, hD, hgD⟩ := exists_compact_mem_nhds g
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hgD), D, hD, subset_rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEqOne
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe14.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

private lemma UpperTheory.Reformulated.B.Qe14.pow_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖η ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : η ^ (n + 1) - 1 = (η ^ n - 1) * (η - 1) + ((η ^ n - 1) + (η - 1)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ih h.le
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih h)

private lemma UpperTheory.Reformulated.B.Qe14.sum_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖∑ i ∈ Finset.range n, η ^ i - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∑ i ∈ Finset.range (n + 1), η ^ i - ((n + 1 : ℕ) : K)
        = (∑ i ∈ Finset.range n, η ^ i - (n : K)) + (η ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt ih (UpperTheory.Reformulated.B.Qe14.pow_close h n))

theorem UpperTheory.Reformulated.B.Qe14.root_eq_one :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {m : ℕ},
      ¬v ∣ m →
        ∀ {η : UpperTheory.Reformulated.B.Qe14.Om v},
          η ^ m = (1 : UpperTheory.Reformulated.B.Qe14.Om v) →
            ‖η - (1 : UpperTheory.Reformulated.B.Qe14.Om v)‖ < (1 : ℝ) → η = (1 : UpperTheory.Reformulated.B.Qe14.Om v) := by
  intro v inst m hm η hη h
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, η ^ i) * (η - 1) = 0 := by
    rw [geom_sum_mul, hη, sub_self]
  have h2 : ∑ i ∈ Finset.range m, η ^ i = 0 :=
    (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)
  have h3 := UpperTheory.Reformulated.B.Qe14.sum_close h m
  rw [h2, zero_sub, norm_neg] at h3
  have h4 : ((m : ℕ) : PadicAlgCl v) = algebraMap ℚ_[v] (PadicAlgCl v) (m : ℚ_[v]) := by
    simp
  have h5 : ‖((m : ℕ) : PadicAlgCl v)‖ = ‖(m : ℚ_[v])‖ := by
    rw [h4]; exact PadicAlgCl.norm_extends v _
  rw [h5, Padic.norm_natCast_lt_one_iff] at h3
  exact hm h3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootOrbit
section
theorem UpperTheory.Reformulated.B.Qi49.root_orbit :
    ∀ {A B G Ω : Type} [inst : CommRing A]
    [inst_1 : CommRing B] [inst_2 : Algebra A B] [inst_3 : Group G] [Finite G] [inst_5 : MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] [inst_8 : Field Ω] (φ ψ : B →+* Ω),
    φ.comp (Algebra.algebraMap A B) = ψ.comp (Algebra.algebraMap A B) →
      ∀ (b : B), ∃ (g : G), (ψ : B → Ω) b = (φ : B → Ω) (g • b) := by
  intro A B G Ω _ _ _ _ _ _ _ _ _ φ ψ h b
  classical
  cases nonempty_fintype G
  obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).1 (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
  have hmap : (MulSemiringAction.charpoly G b).map φ = (MulSemiringAction.charpoly G b).map ψ := by
    rw [← hp, Polynomial.map_map, Polynomial.map_map, h]
  have hroot : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, MulSemiringAction.eval_charpoly, map_zero]
  rw [← hmap, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hroot
  obtain ⟨g, -, hg⟩ := hroot
  refine ⟨g, ?_⟩
  simpa [sub_eq_zero] using hg
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SaturationByPowers
section
noncomputable def UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers.{u_1} :
    {A : Type u_1} → [inst : CommRing A] → Ideal A → A → Ideal A :=
  fun {A} _ J a =>
    { carrier := {x : A | ∃ n : ℕ, a ^ n * x ∈ J}
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : a ^ (m + n) * (x + y) = a ^ n * (a ^ m * x) + a ^ m * (a ^ n * y) := by ring
        rw [h]
        exact J.add_mem (J.mul_mem_left _ hm) (J.mul_mem_left _ hn)
      zero_mem' := ⟨0, by rw [mul_zero]; exact J.zero_mem⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : a ^ n * (c • x) = c * (a ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact J.mul_mem_left _ hn }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurScalar
section
noncomputable def UpperTheory.Reformulated.B.Qi17.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qi17.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qi17.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qi17.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.Qi17.schur_scalar :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qi17.IsIrr r →
        ∀ (g : GL (Fin n) k),
          (∀ (s : Γ), (r : Γ → GL (Fin n) k) s * g = g * (r : Γ → GL (Fin n) k) s) →
            ∃ (c : kˣ), (↑g : Matrix (Fin n) (Fin n) k) = (↑c : k) • (1 : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n r hr g hg
  obtain ⟨hne, -, hmin⟩ := hr
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hinv : UpperTheory.Reformulated.B.Qi17.IsInv r
      (Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c) := by
    intro s v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    have h : (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
        = (r s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hg s]
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have htop := (hmin _ le_top hinv).resolve_left hc
  have hgc : (g : Matrix (Fin n) (Fin n) k) = c • (1 : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c := by
      rw [htop]; exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hgc
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
    apply hv
    have h1 : (1 : Matrix (Fin n) (Fin n) k) = 0 := by
      rw [← g.mul_inv, hgc, zero_mul]
    rw [← Matrix.one_mulVec v, h1, Matrix.zero_mulVec]
  exact ⟨Units.mk0 c hc0, hgc⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurTwistHolds
section
noncomputable def UpperTheory.Reformulated.B.H13.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.H13.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.H13.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.H13.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.H13.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.H13.aux5 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (1 : Γ)) *
          (r : Γ → GL (Fin n) k) (1 : Γ) =
        (1 : GL (Fin n) k) := by
  intro Γ k _ _ n r χ
  simp

theorem UpperTheory.Reformulated.B.H13.aux6 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s t : Γ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (s * t)) *
          (r : Γ → GL (Fin n) k) (s * t) =
        (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s *
          ((Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) t) * (r : Γ → GL (Fin n) k) t) := by
  intro Γ k _ _ n r χ s t
  have hc : ∀ (c : kˣ) (A : GL (Fin n) k),
      A * Matrix.GeneralLinearGroup.scalar (Fin n) c = Matrix.GeneralLinearGroup.scalar (Fin n) c * A := by
    intro c A
    apply Units.ext
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute (c : k) (fun x => Commute.all _ _) (A : Matrix (Fin n) (Fin n) k)).eq.symm
  rw [map_mul, map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (r s), hc, mul_assoc]

noncomputable def UpperTheory.Reformulated.B.H13.tw :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* kˣ) → Γ →* GL (Fin n) k :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) ↦
      {
        toFun := fun (s : Γ) ↦
          (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s,
        map_one' := UpperTheory.Reformulated.B.H13.aux5 r χ, map_mul' := UpperTheory.Reformulated.B.H13.aux6 r χ : Γ →* GL (Fin n) k }

noncomputable def UpperTheory.Reformulated.B.H13.SchurTw :
    Prop :=
    ∀ (Γ Γ' k : Type) [inst : Group Γ] [inst_1 : Group Γ'] [inst_2 : Field k] [IsAlgClosed k] (n : ℕ)
      (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
      UpperTheory.Reformulated.B.H13.IsIrr (r.comp φ) →
        δ.comp φ = (1 : Γ' →* kˣ) → UpperTheory.Reformulated.B.H13.RepIso r (UpperTheory.Reformulated.B.H13.tw r δ) → δ = (1 : Γ →* kˣ)

theorem UpperTheory.Reformulated.B.H13.schur_twist_holds :
    UpperTheory.Reformulated.B.H13.SchurTw := by
  intro Γ Γ' k _ _ _ _ n r φ δ hirr hδ hiso
  obtain ⟨hne, -, hmin⟩ := hirr
  obtain ⟨g, hg⟩ := hiso
  have hg' : ∀ s : Γ, Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s * g = g * r s := by
    intro s
    have h : Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s = g * r s * g⁻¹ := hg s
    rw [h, inv_mul_cancel_right]
  have hcomm : ∀ t : Γ', r (φ t) * g = g * r (φ t) := by
    intro t
    have h1 : δ (φ t) = 1 := DFunLike.congr_fun hδ t
    have h := hg' (φ t)
    rwa [h1, map_one, one_mul] at h
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v : Fin n → k,
      v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c ↔
        (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have htop : Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c = ⊤ := by
    refine (hmin _ le_top ?_).resolve_left hc
    intro t v hv
    rw [hmem] at hv ⊢
    have h : (r (φ t) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k)
        = (g : Matrix (Fin n) (Fin n) k) * (r (φ t) : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    change (g : Matrix (Fin n) (Fin n) k).mulVec ((r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v)
      = c • (r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hgv : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [← hmem, htop]
    exact Submodule.mem_top
  have hcent : ∀ A : GL (Fin n) k, g * A = A * g := by
    intro A
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgv, hgv, Matrix.mulVec_smul]
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton (Fin n → k) inferInstance
  obtain ⟨i⟩ := hn
  refine MonoidHom.ext fun s => ?_
  have h := hg' s
  rw [hcent, mul_left_inj, mul_eq_right] at h
  have h2 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) i i) h
  apply Units.ext
  simpa using h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SectionLift
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.Yt7.Sp R' ⟶ UpperTheory.Reformulated.B.Yt7.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

open CategoryTheory AlgebraicGeometry in
private theorem UpperTheory.Reformulated.B.Yt7.ring_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {A : Type} [CommRing A] (φ : R →+* A) (hφ : φ.Finite)
    (ψ : A →+* K) (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, σ.comp φ = RingHom.id R ∧ (algebraMap R K).comp σ = ψ := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have hi : (algebraMap R K).IsIntegralElem (ψ a) := by
      rw [← h]
      exact (hφ.to_isIntegral a).map ψ
    exact IsIntegrallyClosed.isIntegral_iff.mp hi
  let e : R ≃+* (algebraMap R K).range :=
    RingEquiv.ofBijective (algebraMap R K).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have key : ∀ a : A, algebraMap R K (e.symm ⟨ψ a, hmem a⟩) = ψ a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hmem a⟩)
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext r
    apply hinj
    exact (key (φ r)).trans (RingHom.congr_fun h r)
  · ext a
    exact key a

open CategoryTheory AlgebraicGeometry in
private theorem UpperTheory.Reformulated.B.Yt7.section_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {P : Scheme} (g : P ⟶ Spec (CommRingCat.of R)) [IsFinite g]
    (s : Spec (CommRingCat.of K) ⟶ P)
    (h : s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ P,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t = s := by
  have : IsAffine P := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ g)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (s ≫ P.isoSpec.hom)
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, ← h]
    simp
  obtain ⟨σ, h1, h2⟩ := UpperTheory.Reformulated.B.Yt7.ring_lift (K := K) φ.hom hfin ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1' : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h1
  have h2' : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ P.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h1', Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, h2', hψ]
    simp

theorem UpperTheory.Reformulated.B.Yt7.lift_finite :
    ∀ {R K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K]
      [IsIntegrallyClosed R] {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f]
      (y : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ S) (w : UpperTheory.Reformulated.B.Yt7.Sp K ⟶ X),
      CategoryTheory.CategoryStruct.comp w f =
          CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) y →
        ∃ (v : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ X),
          CategoryTheory.CategoryStruct.comp v f = y ∧
            CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) v = w := by
  intro R K _ _ _ _ _ _ X S f _ y w h
  obtain ⟨t, ht1, ht2⟩ := UpperTheory.Reformulated.B.Yt7.section_lift (K := K) (CategoryTheory.Limits.pullback.snd f y)
    (CategoryTheory.Limits.pullback.lift w _ h) (CategoryTheory.Limits.pullback.lift_snd _ _ _)
  refine ⟨CategoryTheory.CategoryStruct.comp t (CategoryTheory.Limits.pullback.fst f y), ?_, ?_⟩
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.condition,
      ← CategoryTheory.Category.assoc, ht1, CategoryTheory.Category.id_comp]
  · rw [← CategoryTheory.Category.assoc, ht2, CategoryTheory.Limits.pullback.lift_fst]
end

