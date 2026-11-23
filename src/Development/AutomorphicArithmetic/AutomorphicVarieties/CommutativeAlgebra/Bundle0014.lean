module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LocGraded

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem map_mem_max {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R}
    (hx : x ∈ maximalIdeal R) : f x ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  exact hx

private theorem ext_X {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {σ : Type} [Finite σ] {R' : Type} [CommRing R'] [Algebra O R']
    [IsCO O R'] (F G : MvPowerSeries σ O →ₐ[O] R') (hm : ∀ s, F (X s) ∈ maximalIdeal R')
    (h : ∀ s, F (X s) = G (X s)) : F = G := by
  have hC : ∀ (H : MvPowerSeries σ O →ₐ[O] R') (x : O), H (C x) = Algebra.ofId O R' x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  exact (co_ev O O R' σ (Algebra.ofId O R') (fun s => F (X s)) hm).unique ⟨hC F, fun _ => rfl⟩
    ⟨hC G, fun s => (h s).symm⟩

theorem UpperTheory.V.Alg.coord_grading :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (S : Type) (e : S → R) (wt : S → X), (∀ s, e s ∈ maximalIdeal R) →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R'), (∀ s, f (e s) = f' (e s)) → f = f') →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) →
        ∃ f' : R →ₐ[O] R', ∀ s, f' (e s) = t (Multiplicative.ofAdd (wt s)) * f (e s)) →
      ∃ (W : WPres O X R) (u : W.σ → S), (∀ i, W.z i = e (u i) ∧ W.wt i = wt (u i)) ∧ ∀ s, e s ∈ W.part (wt s) := by
  intro O _ _ _ _ X _ _ _ R _ _ _ S e wt hem hgen hst
  classical
  have hspan : maximalIdeal R ≤ Ideal.span (Set.range e) ⊔ (maximalIdeal O).map (Algebra.ofId O R) ⊔
      maximalIdeal R ^ 2 := by
    refine co_span O R O (Algebra.ofId O R) (Set.range e) (by rintro _ ⟨s, rfl⟩; exact hem s) ?_
    intro f f' _ h
    haveI := (co_res O).2
    exact hgen _ f f' fun s => h _ ⟨s, rfl⟩
  obtain ⟨T, hT, hTs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (Set.range e)).1
    (IsNoetherian.noetherian _)
  choose u hu using fun i : T => hT i.2
  obtain ⟨π, ⟨hπC, hπX⟩, -⟩ := co_ev O O R T (Algebra.ofId O R) (fun i => e (u i)) fun i => hem _
  have hsurj : Function.Surjective π := by
    haveI := co_mvps O O T
    refine co_surj O (MvPowerSeries T O) R π (hspan.trans (sup_le_sup_right (sup_le ?_ ?_) _))
    · show Submodule.span R (Set.range e) ≤ _
      rw [hTs, Submodule.span_le]
      intro x hx
      have h1 : x = π (MvPowerSeries.X ⟨x, hx⟩) := by rw [hπX, hu]
      rw [h1]
      refine Ideal.mem_map_of_mem π fun hU => ?_
      have := hU.map π
      rw [hπX] at this
      exact hem _ this
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, ← hπC]
      refine Ideal.mem_map_of_mem π fun hU => ?_
      have := hU.map (constantCoeff : MvPowerSeries T O →+* O)
      rw [constantCoeff_C] at this
      exact ha this
  have hπm : ∀ i, π (MvPowerSeries.X i) ∈ maximalIdeal R := fun i => by rw [hπX]; exact hem _
  have hhom : IsHomog O (fun i : T => wt (u i)) (RingHom.ker π) := by
    refine homog_of_stable O X R T _ π hπm ?_
    intro R' _ _ _ f t ht hf f' hf' x hx
    let g : R →ₐ[O] R' := (Ideal.Quotient.liftₐ (RingHom.ker π) f hf).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
    have hg : ∀ y, g (π y) = f y := fun y => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (π y) = Ideal.Quotient.mk _ y := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      show Ideal.Quotient.liftₐ (RingHom.ker π) f hf ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (π y)) = _
      rw [this]
      rfl
    obtain ⟨g', hg'⟩ := hst R' g t ht
    have : g'.comp π = f' := ext_X _ _ (fun i => map_mem_max g' (hπm i)) fun i => by
      rw [AlgHom.comp_apply, hf', ← hg, hπX, hg']
    rw [← this, AlgHom.comp_apply, hx, map_zero]
  let W : WPres O X R := { σ := T, wt := fun i => wt (u i), π := π, surj := hsurj, homog := hhom }
  refine ⟨W, u, fun i => ⟨hπX i, rfl⟩, fun s => eigen_mem O X R W hπm (e s) (wt s) ?_⟩
  intro R' _ _ _ f f' t ht h
  obtain ⟨g', hg'⟩ := hst R' f t ht
  have h1 : g'.comp π = f'.comp π := ext_X _ _ (fun i => map_mem_max g' (hπm i)) fun i => by
    have h2 : f' (π (MvPowerSeries.X i)) = t (Multiplicative.ofAdd (wt (u i))) * f (π (MvPowerSeries.X i)) := h i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h2, hπX, hg']
  have h3 : f' (e s) = g' (e s) := by
    obtain ⟨y, hy⟩ := hsurj (e s)
    rw [← hy]
    exact (DFunLike.congr_fun h1 y).symm
  rw [h3, hg']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrNoeth
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_noeth :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsNoetherianRing W.A ∧ Algebra.FiniteType (W.gr 0) W.A ∧ ∀ j, ∃ s : Finset W.A, (∀ a ∈ s, a ∈ W.gr j) ∧ W.gr j = W.gr 0 * Submodule.span O (s : Set W.A) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz
  classical
  haveI := W.fin
  haveI hco : IsCO O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal O X R W hz
  haveI : IsNoetherianRing (W.gr 0) := IsCO.toIsNoetherian O
  have hgen : Algebra.adjoin (W.gr 0) (Set.range W.zA) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    have ha : a ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      rw [gr_gen O R X W]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · have e : algebraMap (W.gr 0) W.A ⟨x, hx⟩ = x := rfl
        rw [← e]
        exact Subalgebra.algebraMap_mem _ _
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r =>
      have hr : algebraMap O W.A r ∈ W.gr 0 := SetLike.algebraMap_mem_graded W.gr r
      have e : algebraMap (W.gr 0) W.A ⟨_, hr⟩ = algebraMap O W.A r := rfl
      rw [← e]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  haveI hft : Algebra.FiniteType (W.gr 0) W.A :=
    ⟨⟨Finset.univ.image W.zA, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩
  refine ⟨Algebra.FiniteType.isNoetherianRing (W.gr 0) W.A, hft, ?_⟩
  intro j
  have hmono : ∀ m : W.σ →₀ ℕ, monomial m (1 : O) ∈ wtPart O W.wt (Finsupp.weight W.wt m) := by
    intro m n hn
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact hn rfl
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
  let mA : (W.σ →₀ ℕ) → W.A := fun m =>
    ⟨W.π (monomial m 1), W.part_le_A (Submodule.mem_map_of_mem (hmono m))⟩
  have hsj : ∀ a ∈ μ.image mA, a ∈ W.gr j := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hw : Finsupp.weight W.wt m = j := hμS hm
    show (W.π (monomial m 1) : R) ∈ W.part j
    rw [← hw]
    exact Submodule.mem_map_of_mem (hmono m)
  refine ⟨μ.image mA, hsj, ?_⟩
  apply le_antisymm
  · intro a ha
    have ha' : (a : R) ∈ W.part j := ha
    obtain ⟨f, hf, hfa⟩ := Submodule.mem_map.mp ha'
    obtain ⟨b, hb, hfb⟩ := hμ f (fun n hn => hf n hn)
    let bA : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (b m), W.part_le_A (Submodule.mem_map_of_mem (hb m))⟩
    have hsum : a = ∑ m ∈ μ, bA m * mA m := by
      apply Subtype.ext
      rw [← hfa]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [hfb, map_sum, map_mul, bA, mA]
    rw [hsum]
    refine Submodule.sum_mem _ fun m hm => Submodule.mul_mem_mul ?_ ?_
    · show (W.π (b m) : R) ∈ W.part 0
      exact Submodule.mem_map_of_mem (hb m)
    · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mA hm))
  · rw [Submodule.mul_le]
    intro x hx y hy
    have hy' : y ∈ W.gr j := (Submodule.span_le.mpr fun z hz => hsj z hz) hy
    simpa using SetLike.GradedMul.mul_mem hx hy'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.IsWRing
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.isWRing :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin), (∀ s, -2 ≤ W.wt s ∧ W.wt s ≤ 2) → IsWRing W.gr (W.originA h) := by
  classical
  intro O _ _ _ _ R _ _ _ W h hw
  haveI := W.fin
  have hz : ∀ s, W.z s ∈ maximalIdeal R := by
    intro s
    by_contra hs
    have hu : IsUnit (W.z s) := by
      by_contra hn
      exact hs ((IsLocalRing.mem_maximalIdeal _).2 hn)
    have h0 : W.origin h (W.z s) = 0 := by
      simp only [WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have hu' := hu.map (W.origin h)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  refine ⟨wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ R W hz, ?_, ?_⟩
  · refine ⟨(Finset.univ.filter (fun i => W.wt i ≠ 0)).image W.zA, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      have hi' : W.wt i ≠ 0 := (Finset.mem_filter.1 hi).2
      have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
      obtain ⟨h1, h2⟩ := hw i
      rcases (show W.wt i = -2 ∨ W.wt i = -1 ∨ W.wt i = 1 ∨ W.wt i = 2 by omega) with e | e | e | e
      · exact Or.inl (e ▸ hm)
      · exact Or.inr (Or.inl (e ▸ hm))
      · exact Or.inr (Or.inr (Or.inl (e ▸ hm)))
      · exact Or.inr (Or.inr (Or.inr (e ▸ hm)))
    · refine top_unique ?_
      rw [← gr_gen O R ℤ W]
      apply Algebra.adjoin_mono
      rintro x (hx | ⟨i, rfl⟩)
      · exact Or.inl hx
      · by_cases hi : W.wt i = 0
        · left
          have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
          rw [hi] at hm
          exact hm
        · right
          simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi, rfl⟩
  · intro j hj f hf
    obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 hf
    have hc : MvPowerSeries.constantCoeff g = 0 := by
      have := hg 0 (by simpa using hj.symm)
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using this
    have hfg : (f : R) = W.π g := hgf.symm
    change W.origin h f.1 = 0
    rw [hfg, WPres.origin_π, hc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LocGradedTop
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lc_of_fib {Γ A B : Type} [TopologicalSpace Γ] {f : Γ → A} {g : Γ → B} (hf : IsLocallyConstant f)
    (h : ∀ x y, f x = f y → g x = g y) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_eventually_eq] at hf ⊢
  exact fun x => (hf x).mono fun y hy => h _ _ hy

private theorem exists_grpTop (Γ : Type) [Group Γ] (T : TopologicalSpace Γ) :
    ∃ T' : TopologicalSpace Γ, @IsTopologicalGroup Γ T' _ ∧
      ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ ↔ @IsLocallyConstant Γ M T' φ := by
  classical
  let S := {K : Subgroup Γ // K.Normal ∧ @IsLocallyConstant Γ (Γ ⧸ K) T (fun x => (x : Γ ⧸ K))}
  let ρ : ∀ K : S, Γ →* Equiv.Perm (Γ ⧸ K.1) := fun K => MulAction.toPermHom Γ (Γ ⧸ K.1)
  let T' : TopologicalSpace Γ := ⨅ K : S, TopologicalSpace.induced (ρ K) ⊥
  have htg : ∀ K : S, @IsTopologicalGroup Γ (TopologicalSpace.induced (ρ K) ⊥) _ := by
    intro K
    letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
    haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
    exact topologicalGroup_induced (ρ K)
  refine ⟨T', topologicalGroup_iInf htg, ?_⟩
  intro M _ φ
  have hρT : ∀ K : S, @IsLocallyConstant Γ _ T (ρ K) := by
    intro K
    refine @lc_of_fib Γ _ _ T _ _ K.2.2 ?_
    intro x y hxy
    ext c
    induction c using QuotientGroup.induction_on with
    | H z =>
      simp only [ρ, MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_coe]
      rw [QuotientGroup.eq] at hxy ⊢
      have := K.2.1.conj_mem _ hxy z⁻¹
      simpa [mul_assoc] using this
  have hρT' : ∀ K : S, @IsLocallyConstant Γ _ T' (ρ K) := by
    intro K
    letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
    haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
    rw [@IsLocallyConstant.iff_continuous Γ _ T']
    apply continuous_iInf_dom (i := K)
    exact continuous_induced_dom
  constructor
  · intro hφ
    let K : Subgroup Γ := φ.ker
    have hK : ∀ x y : Γ, (x : Γ ⧸ K) = y ↔ φ x = φ y := by
      intro x y
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul]
      constructor
      · intro e
        calc φ x = φ x * (φ x⁻¹ * φ y) := by rw [e, mul_one]
          _ = φ y := by rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      · intro e
        rw [← e, ← map_mul, inv_mul_cancel, map_one]
    have hmk : @IsLocallyConstant Γ (Γ ⧸ K) T (fun x => (x : Γ ⧸ K)) :=
      @lc_of_fib Γ _ _ T _ _ hφ fun x y e => (hK x y).2 e
    let K' : S := ⟨K, MonoidHom.normal_ker φ, hmk⟩
    refine @lc_of_fib Γ _ _ T' _ _ (hρT' K') ?_
    intro x y hxy
    have := congrArg (fun e : Equiv.Perm (Γ ⧸ K) => e ((1 : Γ) : Γ ⧸ K)) hxy
    simp only [ρ, K', MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_coe, mul_one] at this
    rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this
    exact (hK x y).1 this
  · intro hφ
    have hid : @Continuous Γ Γ T T' id := by
      apply continuous_iInf_rng.2
      intro K
      apply continuous_induced_rng.2
      letI : TopologicalSpace (Equiv.Perm (Γ ⧸ K.1)) := ⊥
      haveI : DiscreteTopology (Equiv.Perm (Γ ⧸ K.1)) := ⟨rfl⟩
      exact (@IsLocallyConstant.iff_continuous Γ _ T _ _ _).1 (hρT K)
    exact @IsLocallyConstant.comp_continuous Γ Γ M T T' φ id hφ hid

private def tr {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [Fintype ι] [DecidableEq ι]
    {rbar : Γ →* Matrix ι ι (ResidueField O)} (T T' : TopologicalSpace Γ)
    (h : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ → @IsLocallyConstant Γ M T' φ)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : @Lift O _ _ Γ ι _ T _ _ rbar R _ _ _) :
    @Lift O _ _ Γ ι _ T' _ _ rbar R _ _ _ :=
  @Lift.mk O _ _ Γ ι _ T' _ _ rbar R _ _ _ (@Lift.hom O _ _ Γ ι _ T _ _ rbar R _ _ _ r)
    (fun a b N => by
      let φ : Γ →* Matrix ι ι (R ⧸ maximalIdeal R ^ N) :=
        (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix.toMonoidHom.comp
          (@Lift.hom O _ _ Γ ι _ T _ _ rbar R _ _ _ r)
      have h1 : @IsLocallyConstant Γ _ T φ := by
        rw [@IsLocallyConstant.iff_eventually_eq Γ _ T]
        intro x
        have h2 := fun a b => (@IsLocallyConstant.iff_eventually_eq Γ _ T _).1
          (@Lift.cont O _ _ Γ ι _ T _ _ rbar R _ _ _ r a b N) x
        have h3 := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => h2 a b
        exact h3.mono fun y hy => Matrix.ext fun a b => hy a b
      exact @lc_of_fib _ _ _ T' _ _ (h _ φ h1) fun x y e => congrFun (congrFun e a) b)
    (@Lift.red O _ _ Γ ι _ T _ _ rbar R _ _ _ r)

theorem UpperTheory.V.Alg.loc_graded_top :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (N : Subgroup Γ) (L : Cond O rbar), Φ.IsLocCond r0.hom N L →
          ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsHomog O W.wt (RingHom.ker (p.comp W.π)) →
          ∀ r' : Lift O rbar R', Φ.InH r0.hom R' r' → L R' r' → (∀ s a b, r'.hom s a b ∈ (W.part (w a - w b)).map p.toLinearMap) →
          ∃ r : Lift O rbar R, Φ.InH r0.hom R r ∧ L R r ∧ r.map p = r' ∧ ∀ s a b, r.hom s a b ∈ W.part (w a - w b) := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ T rbar r0 hbar hr0 N L hL R _ _ _ R' _ _ _ p hp hker W hz hW r' hr' hLr' hpart
  obtain ⟨U, hU, hiff⟩ : ∃ U : PLift (TopologicalSpace Γ), @IsTopologicalGroup Γ U.down _ ∧
      ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ ↔ @IsLocallyConstant Γ M U.down φ := by
    obtain ⟨T', h1, h2⟩ := exists_grpTop Γ T
    exact ⟨⟨T'⟩, h1, h2⟩
  have hf : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M T φ → @IsLocallyConstant Γ M U.down φ :=
    fun M _ φ => (hiff M φ).1
  have hb : ∀ (M : Type) [Monoid M] (φ : Γ →* M), @IsLocallyConstant Γ M U.down φ → @IsLocallyConstant Γ M T φ :=
    fun M _ φ => (hiff M φ).2
  let L' : @Cond O _ _ Γ ι _ U.down _ _ rbar := fun S _ _ _ r => L S (tr U.down T hb r)
  have hL' : @FormData.IsLocCond O _ ι X _ _ _ w Φ _ Γ _ U.down rbar r0.hom N L' := by
    refine @FormData.IsLocCond.mk O _ ι X _ _ _ w Φ _ Γ _ U.down rbar r0.hom N L' ?_ ?_ ?_ ?_ ?_
    · intro S _ _ _ r hr
      obtain ⟨I, hI⟩ := hL.closed S (tr U.down T hb r) hr
      refine ⟨I, fun S' _ _ _ f => ?_⟩
      convert hI S' f using 2
      exact Lift.ext rfl
    · intro S _ _ _ r r2 h hr hh hc hLr
      exact hL.conj S (tr U.down T hb r) (tr U.down T hb r2) h hr hh hc hLr
    · intro S _ _ _ r r2 t hr ht htc hLr
      exact hL.torus S (tr U.down T hb r) (tr U.down T hb r2) t hr ht htc hLr
    · intro S S' _ _ _ _ _ _ q hq hk s hs hLs
      obtain ⟨r1, hr1, hL1, hm1⟩ := hL.lift S S' q hq hk (tr U.down T hb s) hs hLs
      refine ⟨tr T U.down hf r1, hr1, ?_, ?_⟩
      · exact (congrArg (L S) (Lift.ext rfl : tr U.down T hb (tr T U.down hf r1) = r1)).mpr hL1
      · have e := congrArg (@Lift.hom O _ _ Γ ι _ T _ _ rbar S' _ _ _) hm1
        exact Lift.ext e
    · intro S S' _ _ _ _ _ _ q hq hk r1 r2 hr1 hr2 hm hL1
      have e := congrArg (@Lift.hom O _ _ Γ ι _ U.down _ _ rbar S' _ _ _) hm
      exact hL.tangent S S' q hq hk (tr U.down T hb r1) (tr U.down T hb r2) hr1 hr2 (Lift.ext e) hL1
  have hLr'' : L' R' (tr T U.down hf r') := by
    exact (congrArg (L R') (Lift.ext rfl : tr U.down T hb (tr T U.down hf r') = r')).mpr hLr'
  obtain ⟨r, hr, hLr, hmap, hpart'⟩ := @loc_graded O _ _ _ _ ι X _ _ _ _ _ w Φ h2 Γ _ U.down hU rbar
    (tr T U.down hf r0) hbar hr0 N L' hL' R _ _ _ R' _ _ _ p hp hker W hz hW (tr T U.down hf r') hr' hLr'' hpart
  have e := congrArg (@Lift.hom O _ _ Γ ι _ U.down _ _ rbar R' _ _ _) hmap
  exact ⟨tr U.down T hb r, hr, hLr, Lift.ext e, hpart'⟩
end

