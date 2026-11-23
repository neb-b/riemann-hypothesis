module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanMapRingHomEqTop
section
theorem UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top :
    ∀ {k K G ι : Type} [inst : Field k] [inst_1 : Field K]
    [Fintype ι] [DecidableEq ι] (φ : k →+* K) (f : G → Matrix ι ι k),
    Submodule.span k (Set.range f) = ⊤ → Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) = ⊤ := by
  intro k K G ι _ _ _ _ φ f h
  have key : ∀ M : Matrix ι ι k, M ∈ Submodule.span k (Set.range f) →
      M.map (⇑φ : k → K) ∈
        Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero =>
      have e : (0 : Matrix ι ι k).map (⇑φ : k → K) = 0 := by
        ext i j
        simp
      rw [e]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have e : (x + y).map (⇑φ : k → K) = x.map (⇑φ : k → K) + y.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : (a • x).map (⇑φ : k → K) = φ a • x.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro N _
  rw [Matrix.matrix_eq_sum_single N]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (N i j)
      = N i j • (Matrix.single i j (1 : k)).map (⇑φ : k → K) := by
    ext a b
    by_cases hab : i = a ∧ j = b <;> simp [Matrix.single, hab]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ (h ▸ Submodule.mem_top))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanOfVariable
section
theorem UpperTheory.Reformulated.B.SpanOfVariable.span_X :
    ∀ {O σ : Type} [inst : CommRing O] (I : Ideal (MvPowerSeries σ O))
    (s : Finset σ),
    (∀ i ∈ s, MvPowerSeries.X i ∈ I) →
      ∀ (f : MvPowerSeries σ O),
        (∀ (n : σ →₀ ℕ),
            (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
          f ∈ I := by
  intro O σ inst I s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ f hf
    have h0 : f = 0 := by
      ext n
      rw [hf n (by simp), map_zero]
    rw [h0]
    exact I.zero_mem
  | insert a s ha ih =>
    intro hX f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have hgI : g ∈ I := by
      refine ih (fun i hi => hX i (Finset.mem_insert_of_mem hi)) g ?_
      intro n hn
      rw [hg]
      split_ifs with h
      · refine hf n ?_
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have hd : MvPowerSeries.X a ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have hfg : f - g ∈ I := I.mem_of_dvd hd (hX a (Finset.mem_insert_self a s))
    have := I.add_mem hfg hgI
    rwa [sub_add_cancel] at this
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanTopFamily
section
noncomputable def UpperTheory.Reformulated.B.SpanTopFamily.Mι :
    {E K : Type} →
      [inst : Field E] →
        [inst_1 : Field K] →
          (O : ValuationSubring K) →
            (E →+* K) → {n : Type} → Submodule (NumberField.RingOfIntegers E) (n → E) → Submodule (↥O) (n → K) :=
    fun {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
        (L : Submodule (NumberField.RingOfIntegers E) (n → E)) ↦
      Submodule.span (↥O) ((fun (l : n → E) (j : n) ↦ (ι : E → K) (l j)) '' (↑L : Set (n → E)))

theorem UpperTheory.Reformulated.B.SpanTopFamily.span_top :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by
  intro E K _ _ _ O ι n _ _ L hL
  have key : ∀ v : n → E, v ∈ Submodule.span E (↑L : Set (n → E)) →
      (fun j => ι (v j)) ∈ Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero =>
      have : (fun j : n => ι ((0 : n → E) j)) = 0 := by
        funext j; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun j : n => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
        funext j; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun j : n => ι ((a • x) j)) = ι a • (fun j => ι (x j)) := by
        funext j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ' w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := key (Pi.single i 1) (by rw [hL]; trivial)
  have e : (fun j : n => ι ((Pi.single i 1 : n → E) j)) = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialLinearMap
section
private theorem UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self {I : Type} [Fintype I] [DecidableEq I]
    {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
    (v : I) (a : (i : I) → Module.Dual ℂ (W i)) (x : (i : I) → W i) (y : W v) :
    ∏ j ∈ Finset.univ.erase v, a j (Function.update x v y j)
      = ∏ j ∈ Finset.univ.erase v, a j (x j) :=
  Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne {I : Type} [Fintype I] [DecidableEq I]
    {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
    {v i : I} (h : i ≠ v) (a : (i : I) → Module.Dual ℂ (W i)) (x : (i : I) → W i) (y : W i) :
    ∏ j ∈ Finset.univ.erase v, a j (Function.update x i y j)
      = a i y * ∏ j ∈ (Finset.univ.erase v).erase i, a j (x j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩),
    Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

noncomputable def UpperTheory.Reformulated.B.SpecialLinearMap.slM :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → MultilinearMap (RingHom.id ℂ) W (W v) :=
  fun {I} _ dI {_} _ _ v a =>
    { toFun := fun x => (∏ j ∈ Finset.univ.erase v, a j (x j)) • x v
      map_update_add' := fun {d} x i y z => by
        obtain rfl : d = dI := Subsingleton.elim _ _
        by_cases h : i = v
        · subst h
          simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self, Function.update_self, smul_add]
        · simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne h, Function.update_of_ne (Ne.symm h),
            map_add, add_mul, add_smul]
      map_update_smul' := fun {d} x i c y => by
        obtain rfl : d = dI := Subsingleton.elim _ _
        by_cases h : i = v
        · subst h
          simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self, Function.update_self,
            RingHom.id_apply]
          exact smul_comm _ _ _
        · simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne h, Function.update_of_ne (Ne.symm h),
            map_smul, RingHom.id_apply, smul_eq_mul, mul_assoc, mul_smul] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialMapFinite
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R' ⟶ UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

theorem UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main :
    ∀ {A : Type} [inst : CommRing A] {Y Z : AlgebraicGeometry.Scheme} {f g : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp A ⟶ Y} (s : Y ⟶ Z)
      [AlgebraicGeometry.IsSeparated s],
      CategoryTheory.CategoryStruct.comp f s = CategoryTheory.CategoryStruct.comp g s →
        ∀ {N : Type} (I : N → Ideal A),
          (∀ (x : A), (∀ (n : N), x ∈ I n) → x = (0 : A)) →
            (∀ (n : N),
                CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) f =
                  CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) g) →
              f = g := by
  open AlgebraicGeometry CategoryTheory CategoryTheory.Limits in
  intro A _ Y Z f g s _ h N I hI hn
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  have : IsSeparated Y'.hom := ‹_›
  have : IsAffine X'.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hcl : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  obtain ⟨haff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (equalizer.ι f' g').left
  have hfac : ∀ n, ∃ l : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp (A ⧸ I n) ⟶ (equalizer f' g').left,
      l ≫ (equalizer.ι f' g').left = UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) := by
    intro n
    let T' : Over Z := Over.mk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) ≫ f ≫ s)
    let ι' : T' ⟶ X' := Over.homMk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)))
    have hc : ι' ≫ f' = ι' ≫ g' := by
      ext1
      exact hn n
    refine ⟨(equalizer.lift ι' hc).left, ?_⟩
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hinj : Function.Injective (equalizer.ι f' g').left.appTop := by
    refine (injective_iff_map_eq_zero (equalizer.ι f' g').left.appTop.hom).mpr fun y hy ↦ ?_
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = y :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom y, by simp⟩
    have ha : a = 0 := by
      refine hI a fun n ↦ ?_
      obtain ⟨l, hl⟩ := hfac n
      have h1 : (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 0 := by
        rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [hy]
        exact map_zero _
      have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))
      have h3 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).inv (Ideal.Quotient.mk (I n) a) = 0 := by
        have h4 := congr($h2 a)
        simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h4
        exact h4.trans h1
      have h5 := congr((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).hom $h3)
      simp only [map_zero] at h5
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using h5
    simp [ha]
  have hiso : IsIso (equalizer.ι f' g').left.appTop := by
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  have hE : IsIso (equalizer.ι f' g').left :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (equalizer.ι f' g').left)).mpr
      (inferInstanceAs (IsIso (Spec.map (equalizer.ι f' g').left.appTop)))
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpectrumNonemptyOfCountableRank
section
open Polynomial in
private lemma spectrum_nonempty_of_countable_rank {V : Type} [AddCommGroup V] [_root_.Module ℂ V]
    [Nontrivial V] (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (T : Module.End ℂ V) :
    (spectrum ℂ T).Nonempty := by
  classical
  by_contra hne
  have hunit : ∀ a : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) a) := fun a => by
    have h : a ∉ spectrum ℂ T := fun h => hne ⟨a, h⟩
    rw [spectrum.notMem_iff] at h
    exact IsUnit.sub_iff.mp h
  have hR : ∀ a : ℂ, ∃ R : Module.End ℂ V, (T - algebraMap ℂ (Module.End ℂ V) a) * R = 1 :=
    fun a => (hunit a).exists_right_inv
  choose R hR using hR
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hdep : ¬ LinearIndependent ℂ (fun a : ℂ => R a v) := by
    intro hli
    have h1 := hli.cardinal_le_rank
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)
  rw [linearIndependent_iff'] at hdep
  push_neg at hdep
  obtain ⟨s, m, hm, i, hi, hmi⟩ := hdep
  let q : ℂ → ℂ[X] := fun a => ∏ j ∈ s.erase a, (X - C j)
  let p : ℂ[X] := ∑ a ∈ s, C (m a) * q a
  have key : ∀ a ∈ s, aeval T (∏ j ∈ s, (X - C j)) * R a = aeval T (q a) := by
    intro a ha
    rw [← Finset.prod_erase_mul s _ ha, map_mul, mul_assoc]
    have : aeval T (X - C a) = T - algebraMap ℂ (Module.End ℂ V) a := by simp
    rw [this, hR, mul_one]
  have hp : aeval T p v = 0 := by
    have h1 := congrArg (aeval T (∏ j ∈ s, (X - C j))) hm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h1
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, aeval_C, ← key a ha, map_smul]
    simp [Module.End.mul_apply, Module.algebraMap_end_apply]
  have hp0 : p ≠ 0 := by
    intro h0
    have h1 : eval i p = m i * ∏ j ∈ s.erase i, (i - j) := by
      simp only [p, Polynomial.eval_finsetSum, eval_mul, eval_C]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [q, eval_prod]
      · intro b hb hbi
        have : eval i (q b) = 0 := by
          simp only [q, eval_prod]
          refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hbi.symm, hi⟩) (by simp)
        rw [this, mul_zero]
    rw [h0, eval_zero] at h1
    have h2 : ∏ j ∈ s.erase i, (i - j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    exact (mul_ne_zero hmi h2) h1.symm
  have hnu : ¬ IsUnit (aeval T p) := by
    intro hu
    have hinj := ((Module.End.isUnit_iff _).mp hu).injective
    exact hv (hinj (by rw [hp, map_zero]))
  have hprod := (IsAlgClosed.splits p).eq_prod_roots
  have lead_ne := leadingCoeff_ne_zero.mpr hp0
  have lead_unit : IsUnit (algebraMap ℂ (Module.End ℂ V) p.leadingCoeff) :=
    (Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  rw [hprod, aeval_mul, ((Commute.all _ _).map (aeval T : ℂ[X] →ₐ[ℂ] _)).isUnit_mul_iff,
    aeval_C] at hnu
  obtain ⟨k, hk, -⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod (not_and.mp hnu lead_unit)
  exact hne ⟨k, hk⟩

theorem UpperTheory.Reformulated.B.DYhd6.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [Nontrivial V],
      Module.rank ℂ V ≤ Cardinal.aleph0 →
        ∀ (B : Subalgebra ℂ (Module.End ℂ V)),
          (∀ (N : Submodule ℂ V), (∀ b ∈ B, ∀ x ∈ N, (b : V → V) x ∈ N) → N = ⊥ ∨ N = ⊤) →
            ∀ (f : Module.End ℂ V) (s : Finset V), ∃ b ∈ B, ∀ m ∈ s, (f : V → V) m = (b : V → V) m := by
  intro V _ _ _ hV B hB f s
  have hsc : ∀ (c : ℂ) (x : V), c • x = (algebraMap ℂ B c) • x := fun c x => by
    change c • x = ((algebraMap ℂ (Module.End ℂ V) c : Module.End ℂ V)) x
    simp [Module.algebraMap_end_apply]
  have hbc : ∀ (b : B) (c : ℂ) (x : V), b • (c • x) = c • (b • x) := fun b c x =>
    (b : Module.End ℂ V).map_smul c x
  haveI hsimple : IsSimpleModule B V :=
    { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
      eq_bot_or_eq_top := fun N => by
        let N' : Submodule ℂ V :=
          { carrier := N
            add_mem' := fun h1 h2 => N.add_mem h1 h2
            zero_mem' := N.zero_mem
            smul_mem' := fun c x hx => by
              rw [hsc]
              exact N.smul_mem _ hx }
        rcases hB N' (fun b hb x hx => N.smul_mem (⟨b, hb⟩ : B) hx) with h | h
        · left
          rw [eq_bot_iff]
          intro x hx
          have : x ∈ N' := hx
          rw [h] at this
          simpa using this
        · right
          rw [eq_top_iff]
          intro x _
          have : x ∈ N' := by rw [h]; trivial
          exact this }
  have hscal : ∀ d : Module.End B V, ∃ a : ℂ, ∀ x, d x = a • x := by
    intro d
    let T : Module.End ℂ V :=
      { toFun := d
        map_add' := d.map_add
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          rw [hsc, d.map_smul, ← hsc] }
    obtain ⟨a, ha⟩ := spectrum_nonempty_of_countable_rank hV T
    let e : V →ₗ[B] V :=
      { toFun := fun x => a • x - d x
        map_add' := fun x y => by
          rw [smul_add, map_add d x y]
          abel
        map_smul' := fun b x => by
          simp only [RingHom.id_apply]
          rw [d.map_smul, smul_sub, hbc] }
    rcases LinearMap.bijective_or_eq_zero e with hb | h0
    · exfalso
      apply ha
      rw [spectrum.mem_resolventSet_iff, Module.End.isUnit_iff]
      have hfe : ⇑(algebraMap ℂ (Module.End ℂ V) a - T) = ⇑e := by
        funext x
        simp [T, e, Module.algebraMap_end_apply]
      rw [hfe]
      exact hb
    · refine ⟨a, fun x => ?_⟩
      have : a • x - d x = 0 := congrArg (fun g : V →ₗ[B] V => g x) h0
      exact (sub_eq_zero.mp this).symm
  let F : Module.End (Module.End B V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun d x => by
        obtain ⟨a, ha⟩ := hscal d
        simp only [RingHom.id_apply, Module.End.smul_def]
        rw [ha, ha, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun m hm => hr m hm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SqShift
section
theorem UpperTheory.Reformulated.B.Qk59.sq_shift :
    ∀ {G : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    {μ : MeasureTheory.Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) D μ →
      ∀ {f : G → ℝ},
        (∀ γ ∈ Γ, ∀ (y : G), f (γ * y) = f y) → ∀ (g : G), ∫ (y : G) in D, f (y * g) ∂μ = ∫ (y : G) in D, f y ∂μ := by
  intro G _ _ _ _ _ μ _ _ Γ _ D hD f hf g
  have hD' : MeasureTheory.IsFundamentalDomain (↥Γ) ((fun y : G => y * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv
      (MeasureTheory.measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id
      (fun γ y => by
        show ((γ : G) * y) * g⁻¹ = (γ : G) * (y * g⁻¹)
        exact mul_assoc _ _ _)
  have h1 := (MeasureTheory.measurePreserving_mul_right μ g).setIntegral_preimage_emb
    (measurableEmbedding_mulRight g) f ((fun y : G => y * g⁻¹) ⁻¹' D)
  have h2 : (fun y : G => y * g) ⁻¹' ((fun y : G => y * g⁻¹) ⁻¹' D) = D := by
    ext y
    simp
  rw [h2] at h1
  rw [h1]
  exact hD'.setIntegral_eq hD (fun γ y => hf γ γ.2 y)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareNormBound
section
theorem UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ),
    ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS0 : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ))
            (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ)
      ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumChar
section
theorem UpperTheory.Reformulated.B.Qe46.sum_char :
    ∀ {G : Type} [inst : CommGroup G] [inst_1 : Fintype G] (χ : G →* ℂˣ),
    χ ≠ (1 : G →* ℂˣ) → ∑ z : G, (↑((χ : G → ℂˣ) z) : ℂ) = (0 : ℂ) := by
  intro G _ _ χ hχ
  have hne : (Units.coeHom ℂ).comp χ ≠ 1 := by
    intro h
    apply hχ
    ext z
    have hz := DFunLike.congr_fun h z
    simpa using hz
  simpa using sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) hne
end

