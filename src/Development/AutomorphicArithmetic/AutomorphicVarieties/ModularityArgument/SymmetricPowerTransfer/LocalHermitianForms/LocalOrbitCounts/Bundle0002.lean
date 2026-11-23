module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LatCls
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem latCls_core {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (e₁ e₂ : Etau K τ)
    (hd : e₁.re * e₂.im - e₁.im * e₂.re ≠ 0) (hn : QuadraticAlgebra.norm e₁ ≠ 0)
    (hb : QuadraticAlgebra.trace (e₂ * star e₁) / QuadraticAlgebra.norm e₁ ∈ (algebraMap O K).range)
    (hc : QuadraticAlgebra.norm e₂ / QuadraticAlgebra.norm e₁ ∈ (algebraMap O K).range) :
    ∃ (y : (Etau K τ)ˣ) (x : Etau K τ), x.im ≠ 0 ∧ QuadraticAlgebra.trace x ∈ (algebraMap O K).range ∧
    QuadraticAlgebra.norm x ∈ (algebraMap O K).range ∧
    ((Submodule.span O {e₁, e₂} : Submodule O (Etau K τ)) : Set (Etau K τ)) =
      ((y : Etau K τ) * ·) '' (Submodule.span O {1, x} : Submodule O (Etau K τ)) := by
  have hu : IsUnit e₁ := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (isUnit_iff_ne_zero.2 hn)
  have hinv : (↑hu.unit⁻¹ : Etau K τ) = (QuadraticAlgebra.norm e₁)⁻¹ • star e₁ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [IsUnit.unit_spec, mul_smul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
      Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hone : e₁ * (↑hu.unit⁻¹ : Etau K τ) = 1 := by
    rw [hinv, mul_smul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
      Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hnu : QuadraticAlgebra.norm (↑hu.unit⁻¹ : Etau K τ) = (QuadraticAlgebra.norm e₁)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, hone, map_one]
  refine ⟨hu.unit, ↑hu.unit⁻¹ * e₂, ?_, ?_, ?_, ?_⟩
  · rw [hinv, smul_mul_assoc, QuadraticAlgebra.im_smul, smul_eq_mul]
    apply mul_ne_zero (inv_ne_zero hn)
    have : (star e₁ * e₂).im = e₁.re * e₂.im - e₁.im * e₂.re := by
      simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
      ring
    rw [this]
    exact hd
  · rw [hinv, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm (star e₁), ← div_eq_inv_mul]
    exact hb
  · rw [map_mul, hnu, mul_comm, ← div_eq_mul_inv]
    exact hc
  · have key : ((↑hu.unit : Etau K τ) * ·) '' ((Submodule.span O {1, ↑hu.unit⁻¹ * e₂} :
        Submodule O (Etau K τ)) : Set (Etau K τ)) =
        (((Submodule.span O {1, ↑hu.unit⁻¹ * e₂} : Submodule O (Etau K τ)).map
          (LinearMap.mulLeft O (↑hu.unit : Etau K τ))) : Set (Etau K τ)) := by
      rw [Submodule.map_coe]
      rfl
    rw [key, Submodule.map_span, Set.image_pair]
    simp only [LinearMap.mulLeft_apply, IsUnit.unit_spec, mul_one]
    rw [← mul_assoc, hone, one_mul]

private theorem latCls_basis {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {τ : K} (S : Set (Etau K τ)) (hS : IsLat O τ S) :
    ∃ e₁ e₂ : Etau K τ, e₁.re * e₂.im - e₁.im * e₂.re ≠ 0 ∧
      S = (Submodule.span O {e₁, e₂} : Submodule O (Etau K τ)) := by
  obtain ⟨s, rfl⟩ := hS.fg
  have hspan := hS.span
  set M : Submodule O (Etau K τ) := Submodule.span O (s : Set (Etau K τ)) with hM
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O M
  let f : Module.Free.ChooseBasisIndex O M → Etau K τ := fun i => (b i : Etau K τ)
  have hliO : LinearIndependent O f := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hliK : LinearIndependent K f := (LinearIndependent.iff_fractionRing O K).1 hliO
  have hMf : M = Submodule.span O (Set.range f) := by
    have : Set.range f = M.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have htop : ⊤ ≤ Submodule.span K (Set.range f) := by
    rw [← hspan, Submodule.span_le]
    intro z hz
    have hz' : z ∈ ((Submodule.span O (Set.range f) : Submodule O (Etau K τ)) : Set (Etau K τ)) := by
      rw [← hMf]
      exact hz
    exact Submodule.span_subset_span O K _ hz'
  let bK := Module.Basis.mk hliK htop
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O M) = 2 := by
    rw [← Module.finrank_eq_card_basis bK,
      Module.finrank_eq_card_basis (QuadraticAlgebra.basis (-1 : K) τ), Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hR : Set.range f = {f (e 0), f (e 1)} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := e.surjective i
      fin_cases j <;> simp
    · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩
  refine ⟨f (e 0), f (e 1), ?_, ?_⟩
  · have hli2 : LinearIndependent K ![f (e 0), f (e 1)] := by
      have : ![f (e 0), f (e 1)] = f ∘ e := by
        funext i
        fin_cases i <;> rfl
      rw [this]
      exact hliK.comp e e.injective
    rw [LinearIndependent.pair_iff] at hli2
    intro h0
    have h1 := hli2 (f (e 1)).im (-(f (e 0)).im) (by
      refine QuadraticAlgebra.ext ?_ ?_
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul, smul_eq_mul,
          QuadraticAlgebra.re_zero]
        linear_combination h0
      · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul, smul_eq_mul,
          QuadraticAlgebra.im_zero]
        ring)
    have h2 := hli2 (f (e 1)).re (-(f (e 0)).re) (by
      refine QuadraticAlgebra.ext ?_ ?_
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul, smul_eq_mul,
          QuadraticAlgebra.re_zero]
        ring
      · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul, smul_eq_mul,
          QuadraticAlgebra.im_zero]
        rw [h1.1, neg_eq_zero.1 h1.2]
        ring)
    have hz : f (e 0) = 0 :=
      QuadraticAlgebra.ext (neg_eq_zero.1 h2.2) (neg_eq_zero.1 h1.2)
    exact hliK.ne_zero (e 0) hz
  · rw [← hR, ← hMf]

set_option maxHeartbeats 400000 in
private theorem latCls_val {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (a b c : K) (h : b ^ 2 - 4 * a * c ≠ 0) :
    (a ≠ 0 ∧ b / a ∈ (algebraMap O K).range ∧ c / a ∈ (algebraMap O K).range) ∨
    (c ≠ 0 ∧ b / c ∈ (algebraMap O K).range ∧ a / c ∈ (algebraMap O K).range) ∨
    (a + b + c ≠ 0 ∧ (b + 2 * c) / (a + b + c) ∈ (algebraMap O K).range ∧ c / (a + b + c) ∈ (algebraMap O K).range) := by
  have hR : ∀ x : K, x ∈ (algebraMap O K).range ↔ ValuationRing.valuation O K x ≤ 1 := by
    intro x
    rw [← ValuationRing.range_algebraMap_eq, Valuation.mem_integer_iff]
  set v := ValuationRing.valuation O K with hv
  have hdiv : ∀ x y : K, y ≠ 0 → (x / y ∈ (algebraMap O K).range ↔ v x ≤ v y) := by
    intro x y hy
    rw [hR, map_div₀, div_le_one₀ ((v.pos_iff).2 hy)]
  have h2 : v 2 ≤ 1 := (hR 2).1 ⟨2, map_ofNat _ 2⟩
  have hz : ∀ x y : K, v x ≤ v y → y = 0 → x = 0 := by
    intro x y hxy hy
    subst hy
    rw [map_zero] at hxy
    exact (v.zero_iff).1 (le_antisymm hxy zero_le')
  have hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0) := by
    rintro ⟨rfl, rfl, rfl⟩
    simp at h
  by_cases hA : v b ≤ v a ∧ v c ≤ v a
  · left
    have ha : a ≠ 0 := fun ha => hne ⟨ha, hz _ _ hA.1 ha, hz _ _ hA.2 ha⟩
    exact ⟨ha, (hdiv _ _ ha).2 hA.1, (hdiv _ _ ha).2 hA.2⟩
  by_cases hC : v b ≤ v c ∧ v a ≤ v c
  · right; left
    have hc : c ≠ 0 := fun hc => hne ⟨hz _ _ hC.2 hc, hz _ _ hC.1 hc, hc⟩
    exact ⟨hc, (hdiv _ _ hc).2 hC.1, (hdiv _ _ hc).2 hC.2⟩
  right; right
  have hab : v a < v b := by
    by_contra hba
    push_neg at hba
    have h1 : v a < v c := by
      by_contra h1
      push_neg at h1
      exact hA ⟨hba, h1⟩
    exact hC ⟨hba.trans h1.le, h1.le⟩
  have hcb : v c < v b := by
    by_contra hbc
    push_neg at hbc
    have h1 : v c < v a := by
      by_contra h1
      push_neg at h1
      exact hC ⟨hbc, h1⟩
    exact hA ⟨hbc.trans h1.le, h1.le⟩
  have hs : v (a + b + c) = v b := by
    have e : a + b + c = (a + c) + b := by ring
    rw [e, v.map_add_eq_of_lt_right (v.map_add_lt hab hcb)]
  have hb0 : b ≠ 0 := (v.pos_iff).1 (lt_of_le_of_lt zero_le' hab)
  have hs0 : a + b + c ≠ 0 := by
    rw [← v.ne_zero_iff, hs, v.ne_zero_iff]
    exact hb0
  refine ⟨hs0, (hdiv _ _ hs0).2 ?_, (hdiv _ _ hs0).2 (by rw [hs]; exact hcb.le)⟩
  rw [hs]
  apply v.map_add_le le_rfl
  rw [map_mul]
  exact (mul_le_of_le_one_left' h2).trans hcb.le

theorem UpperTheory.V.Z.Sym.Loc.latCls :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 →
    ∀ S : Set (Etau K τ), IsLat O τ S → ∃ (y : (Etau K τ)ˣ) (x : Etau K τ), x.im ≠ 0 ∧ QuadraticAlgebra.trace x ∈ (algebraMap O K).range ∧
    QuadraticAlgebra.norm x ∈ (algebraMap O K).range ∧ S = ((y : Etau K τ) * ·) '' (Submodule.span O {1, x} : Submodule O (Etau K τ)) := by
  intro O K _ _ _ _ _ Δ τ hL hτ S hS
  haveI := hL.frac
  obtain ⟨e₁, e₂, hd, rfl⟩ := latCls_basis S hS
  have hdisc : (trace (e₂ * star e₁)) ^ 2 - 4 * QuadraticAlgebra.norm e₁ * QuadraticAlgebra.norm e₂ ≠ 0 := by
    have e : (trace (e₂ * star e₁)) ^ 2 - 4 * QuadraticAlgebra.norm e₁ * QuadraticAlgebra.norm e₂ =
        (τ ^ 2 - 4) * (e₁.re * e₂.im - e₁.im * e₂.re) ^ 2 := by
      simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
      ring
    rw [e]
    exact mul_ne_zero hτ (pow_ne_zero _ hd)
  rcases latCls_val (O := O) _ _ _ hdisc with ⟨ha, hb, hc⟩ | ⟨hc0, hb, ha⟩ | ⟨hs, hb, hc⟩
  · exact latCls_core e₁ e₂ hd ha hb hc
  · have ht : trace (e₁ * star e₂) = trace (e₂ * star e₁) := by
      simp only [QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
      ring
    have hd' : e₂.re * e₁.im - e₂.im * e₁.re ≠ 0 := by
      intro h0
      apply hd
      linear_combination -h0
    obtain ⟨y, x, h1, h2, h3, h4⟩ := latCls_core (O := O) e₂ e₁ hd' hc0 (by rw [ht]; exact hb) ha
    refine ⟨y, x, h1, h2, h3, ?_⟩
    rw [← h4, Set.pair_comm]
  · have hn : QuadraticAlgebra.norm (e₁ + e₂) =
        QuadraticAlgebra.norm e₁ + trace (e₂ * star e₁) + QuadraticAlgebra.norm e₂ := by
      simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      ring
    have ht : trace (e₂ * star (e₁ + e₂)) = trace (e₂ * star e₁) + 2 * QuadraticAlgebra.norm e₂ := by
      simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      ring
    have hd' : (e₁ + e₂).re * e₂.im - (e₁ + e₂).im * e₂.re ≠ 0 := by
      intro h0
      apply hd
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] at h0
      linear_combination h0
    obtain ⟨y, x, h1, h2, h3, h4⟩ := latCls_core (O := O) (e₁ + e₂) e₂ hd' (by rw [hn]; exact hs)
      (by rw [ht, hn]; exact hb) (by rw [hn]; exact hc)
    refine ⟨y, x, h1, h2, h3, ?_⟩
    rw [← h4]
    congr 1
    apply le_antisymm
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | hz
      · have : z = (z + e₂) - e₂ := by abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | hz
      · exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact Submodule.subset_span (by simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WTrans
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem stab_smul_comm {T Y : Type} [CommGroup T] [MulAction T Y] (t : T) (y : Y) :
    MulAction.stabilizer T (t • y) = MulAction.stabilizer T y := by
  ext s
  simp only [MulAction.mem_stabilizer_iff]
  rw [smul_smul, mul_comm, ← smul_smul, smul_left_cancel_iff]

private theorem out_mk_smul {T Y : Type} [Group T] [MulAction T Y] (y : Y) :
    ∃ t : T, (Quotient.mk (MulAction.orbitRel T Y) y).out = t • y := by
  obtain ⟨t, ht⟩ := MulAction.orbitRel_apply.mp (Quotient.mk_out (s := MulAction.orbitRel T Y) y)
  exact ⟨t, ht.symm⟩

private theorem mk_smul_eq {T Y : Type} [Group T] [MulAction T Y] (t : T) (y : Y) :
    Quotient.mk (MulAction.orbitRel T Y) (t • y) = Quotient.mk (MulAction.orbitRel T Y) y := by
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit y t))

private theorem wcount_sub {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (k : Y → ℂ) :
    wcount C k = ∑ᶠ o : {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0},
      ((MulAction.stabilizer T o.1.out).relIndex C : ℂ) * k o.1.out := by
  classical
  set g : MulAction.orbitRel.Quotient T Y → ℂ :=
    fun o => ((MulAction.stabilizer T o.out).relIndex C : ℂ) * k o.out with hg
  have hs : Function.support g ⊆ {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0} := by
    intro o ho
    simp only [Set.mem_setOf_eq]
    intro h0
    exact (Function.mem_support.mp ho) (by simp [hg, h0])
  have h1 := finsum_set_coe_eq_finsum_mem (f := g) {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0}
  rw [← finsum_mem_inter_support g, Set.inter_eq_right.mpr hs, finsum_mem_support] at h1
  exact h1.symm

theorem UpperTheory.V.Z.Sym.Loc.wTrans :
    ∀ (T Y Y' : Type) [CommGroup T] [MulAction T Y] [MulAction T Y'] (C : Subgroup T) (k : Y → ℂ) (k' : Y' → ℂ) (R : Y → Y' → Prop),
    (∀ (t : T) y, k (t • y) = k y) → (∀ (t : T) y', k' (t • y') = k' y') → (∀ (t : T) y y', R y y' → R (t • y) (t • y')) →
    (∀ y y', R y y' → k y = k' y') → (∀ y, k y ≠ 0 → ∃! y', R y y') → (∀ y', k' y' ≠ 0 → ∃! y, R y y') →
    wcount C k = wcount C k' := by
  classical
  intro T Y Y' _ _ _ C k k' R hk hk' hR hkk hex hex'
  rw [wcount_sub C k, wcount_sub C k']
  have stab_eq : ∀ y y', R y y' → k y ≠ 0 → k' y' ≠ 0 →
      MulAction.stabilizer T y = MulAction.stabilizer T y' := by
    intro y y' hyy hy hy'
    ext s
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro hs
      have h1 : R y (s • y') := by simpa [hs] using hR s y y' hyy
      exact (hex y hy).unique h1 hyy
    · intro hs
      have h1 : R (s • y) y' := by simpa [hs] using hR s y y' hyy
      exact (hex' y' hy').unique h1 hyy
  let pick : ∀ o : {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0}, Y' :=
    fun o => Classical.choose (hex o.1.out o.2).exists
  have pick_R : ∀ o, R o.1.out (pick o) := fun o => Classical.choose_spec (hex o.1.out o.2).exists
  have pick_k : ∀ o, k' (pick o) ≠ 0 := fun o => by
    rw [← hkk _ _ (pick_R o)]
    exact o.2
  have e_mem : ∀ o, Quotient.mk (MulAction.orbitRel T Y') (pick o) ∈
      {o' : MulAction.orbitRel.Quotient T Y' | k' o'.out ≠ 0} := by
    intro o
    obtain ⟨t, ht⟩ := out_mk_smul (T := T) (pick o)
    show k' _ ≠ 0
    rw [ht, hk']
    exact pick_k o
  let e : {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0} →
      {o' : MulAction.orbitRel.Quotient T Y' | k' o'.out ≠ 0} :=
    fun o => ⟨Quotient.mk _ (pick o), e_mem o⟩
  refine finsum_eq_of_bijective e ⟨?_, ?_⟩ ?_
  · intro o1 o2 h
    have h' : Quotient.mk (MulAction.orbitRel T Y') (pick o1) = Quotient.mk _ (pick o2) :=
      congrArg Subtype.val h
    obtain ⟨t, ht⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h')
    have h2 : R (t • o2.1.out) (pick o1) := by
      rw [← ht]
      exact hR t _ _ (pick_R o2)
    have h3 : t • o2.1.out = o1.1.out := (hex' _ (pick_k o1)).unique h2 (pick_R o1)
    apply Subtype.ext
    rw [← Quotient.out_eq o1.1, ← Quotient.out_eq o2.1, ← h3, mk_smul_eq]
  · rintro ⟨o', ho'⟩
    obtain ⟨z, hz, -⟩ := hex' o'.out ho'
    have hkz : k z ≠ 0 := by
      rw [hkk _ _ hz]
      exact ho'
    have hmem : Quotient.mk (MulAction.orbitRel T Y) z ∈
        {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0} := by
      obtain ⟨s, hs⟩ := out_mk_smul (T := T) z
      show k _ ≠ 0
      rw [hs, hk]
      exact hkz
    refine ⟨⟨_, hmem⟩, ?_⟩
    obtain ⟨s, hs⟩ := out_mk_smul (T := T) z
    have h1 : R (Quotient.mk (MulAction.orbitRel T Y) z).out (s • o'.out) := by
      rw [hs]
      exact hR s _ _ hz
    have h2 : pick ⟨_, hmem⟩ = s • o'.out := (hex _ hmem).unique (pick_R ⟨_, hmem⟩) h1
    apply Subtype.ext
    show Quotient.mk _ (pick ⟨_, hmem⟩) = o'
    rw [h2, mk_smul_eq, Quotient.out_eq]
  · intro o
    obtain ⟨t, ht⟩ := out_mk_smul (T := T) (pick o)
    show _ = ((MulAction.stabilizer T (Quotient.mk (MulAction.orbitRel T Y') (pick o)).out).relIndex C : ℂ) *
      k' (Quotient.mk (MulAction.orbitRel T Y') (pick o)).out
    rw [ht, stab_smul_comm, hk', ← hkk _ _ (pick_R o), stab_eq _ _ (pick_R o) o.2 (pick_k o)]
end

