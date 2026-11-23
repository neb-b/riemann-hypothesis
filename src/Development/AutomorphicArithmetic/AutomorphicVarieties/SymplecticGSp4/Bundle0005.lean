module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem wcomp_mul_homog (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add (f := _), h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

private theorem span_coeffs {O R X κ N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    (W : WPres O X R) [Fintype κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i)) (u : N → X)
    (B : Submodule O R) (hB : ∀ n i, W.part (u n - c i) ≤ B) (x : R) (hx' : x ∈ ⨆ n, W.part (u n))
    (hx : x ∈ Ideal.span (Set.range g)) : ∃ a : κ → R, (∀ i, a i ∈ B) ∧ x = ∑ i, a i * g i := by
  classical
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = g i := fun i => hg i
  choose e he heg using hg'
  have hl : ∃ f, W.π f = x ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
      ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
    refine Submodule.iSup_induction (fun n => W.part (u n))
      (motive := fun z : R => ∃ f, W.π f = z ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
        ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
    · rintro i _ ⟨f, hf, rfl⟩
      exact ⟨f, rfl, {u i}, fun j hj => ⟨i, (Finset.mem_singleton.1 hj).symm⟩,
        fun n hn => hf n (by simpa using hn)⟩
    · exact ⟨0, map_zero _, ∅, by simp, fun n _ => map_zero _⟩
    · rintro a b ⟨f, hf, s, ht, hs⟩ ⟨f', hf', s', ht', hs'⟩
      refine ⟨f + f', by rw [map_add (f := _), hf, hf'], s ∪ s', fun j hj => ?_, fun n hn => ?_⟩
      · rcases Finset.mem_union.1 hj with h | h
        · exact ht j h
        · exact ht' j h
      · rw [Finset.mem_union, not_or] at hn
        rw [map_add (f := _), hs n hn.1, hs' n hn.2, add_zero]
  obtain ⟨f, hf, s, ht, hs⟩ := hl
  have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact hs n h
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
  choose G hG using fun i => W.surj (a i)
  have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, hf, ← ha, map_sum]
    simp [hG, heg]
  have key : ∀ j, W.π (wcomp O W.wt j f) = ∑ i, W.π (wcomp O W.wt (j - c i) (G i)) * g i := by
    intro j
    have h2 := W.homog _ h1 j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
  refine ⟨fun i => ∑ j ∈ s, W.π (wcomp O W.wt (j - c i) (G i)), fun i => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => ?_
    obtain ⟨n, rfl⟩ := ht j hj
    exact hB n i ⟨_, wcomp_mem O W.wt _ _, rfl⟩
  · rw [← hf]
    conv_lhs => rw [hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [key, Finset.sum_mul]
    exact Finset.sum_comm

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.kerA :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, (∀ f : M.A, M.toSS f = 0 ↔ f ∈ M.eqns.ideal) ∧ (∀ n (x : M.SS), x.1 ∈ M.sPart (0, n) → ∃ f ∈ M.gr n, M.toSS f = x) ∧ ∀ n, ∀ f ∈ M.gr n, (M.toSS f).1 ∈ M.sPart (0, n) := by
  intro Ω _ _ _ l _ c D _ M
  refine ⟨fun f => ⟨fun hf => ?_, fun hf => ?_⟩, ?_, ?_⟩
  · have h0 : (f : M.R) ∈ RingHom.ker M.π := congrArg Subtype.val hf
    rw [M.ker, ← Set.Sum.elim_range, ← Set.Sum.elim_range] at h0
    obtain ⟨a, ha, hfa⟩ := span_coeffs M.W (Sum.elim (Sum.elim M.F M.E) M.Z)
      (fun i => ((0 : ℤ), Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i))
      (by
        rintro ((i | i) | i)
        · exact M.hF i
        · exact M.hE i
        · exact (M.hZ i).1)
      (fun n : ℤ => ((0 : ℤ), n)) (Subalgebra.toSubmodule M.A)
      (fun n i x hx => M.aPart_le (n := n - Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i)
        (by simpa [Model.aPart] using hx))
      f f.2 h0
    have hf' : f = ∑ i, (⟨a i, ha i⟩ : M.A) * Sum.elim (Sum.elim M.eqns.F M.eqns.E) M.eqns.Z i := by
      apply Subtype.ext
      rw [hfa, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl ?_
      rintro ((i | i) | i) - <;> rfl
    rw [hf']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    rcases i with (i | i) | i
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Or.inr ⟨i, rfl⟩
  · have hle : M.eqns.ideal ≤ RingHom.ker M.toSS := by
      refine Ideal.span_le.2 fun x hx => ?_
      have hk : (x : M.R) ∈ RingHom.ker M.π := by
        rw [M.ker]
        refine Ideal.subset_span ?_
        rcases hx with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
        · exact Or.inl (Or.inl ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inl (Or.inr ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inr ⟨i, rfl⟩
      exact Subtype.ext hk
    exact hle hf
  · rintro n x ⟨f, hf, hfx⟩
    exact ⟨⟨f, M.aPart_le (n := n) hf⟩, hf, Subtype.ext hfx⟩
  · intro n f hf
    exact ⟨f, hf, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WeightAlgebraGeneratedDegreeTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem aW_comb {σ : Type} [Fintype σ] (lam : σ → ℤ) (hl : ∀ s, lam s = -1 ∨ lam s = 0 ∨ lam s = 1)
    (P : (σ →₀ ℕ) → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (h1 : ∀ s, lam s = 0 → P (Finsupp.single s 1))
    (h2 : ∀ s t, lam s = 1 → lam t = -1 → P (Finsupp.single s 1 + Finsupp.single t 1)) :
    ∀ m, Finsupp.weight lam m = 0 → P m := by
  classical
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro hm
  have step : ∀ g : σ →₀ ℕ, g ≠ 0 → g ≤ m → Finsupp.weight lam g = 0 → P g → P m := fun g hg hle hw hP => by
    have e : m - g + g = m := tsub_add_cancel_of_le hle
    have hlt : m - g < m := by
      conv_rhs => rw [← e]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg)
    have hw' : Finsupp.weight lam (m - g) = 0 := by
      have := congrArg (Finsupp.weight lam) e
      rwa [map_add, hw, add_zero, hm] at this
    rw [← e]
    exact hadd _ _ (ih _ hlt hw') hP
  by_cases hz : ∃ s, m s ≠ 0 ∧ lam s = 0
  · obtain ⟨s, hs, hs0⟩ := hz
    refine step (Finsupp.single s 1) (by simp) ?_ (by simp [Finsupp.weight_single, hs0]) (h1 s hs0)
    rw [Finsupp.single_le_iff]
    omega
  by_cases hp : (∃ s, m s ≠ 0 ∧ lam s = 1) ∧ ∃ t, m t ≠ 0 ∧ lam t = -1
  · obtain ⟨⟨s, hs, hs1⟩, t, ht, ht1⟩ := hp
    have hst : s ≠ t := by
      rintro rfl
      omega
    refine step _ (by simp) ?_ (by simp [Finsupp.weight_single, hs1, ht1]) (h2 s t hs1 ht1)
    intro u
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with a b b
    · exact absurd (a.trans b.symm) hst
    · subst a; omega
    · subst b; omega
    · omega
  have hsum : ∑ s, (m s : ℤ) * lam s = 0 := by
    rw [← hm, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : m = 0 := by
    ext u
    push Not at hz
    rcases not_and_or.1 hp with hp | hp
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, (m s : ℤ) * lam s ≤ 0 := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonpos hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, 0 ≤ (m s : ℤ) * lam s := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonneg (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
  rw [this]
  exact h0

private theorem aW_wts : ∀ w ∈ wts, (w.1 = -1 ∨ w.1 = 0 ∨ w.1 = 1) ∧ (-1 ≤ w.2 ∧ w.2 ≤ 1) := by decide

private theorem aW_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (B : Subalgebra O R) (h0 : ∀ x ∈ W.part 0, x ∈ B)
    (h1 : ∀ s, (W.wt s).1 = 0 → W.z s ∈ B)
    (h2 : ∀ s t, (W.wt s).1 = 1 → (W.wt t).1 = -1 → W.z s * W.z t ∈ B) (n : ℤ) :
    ∀ x ∈ W.part (0, n), x ∈ B := by
  have hmon : ∀ m, Finsupp.weight (fun s => (W.wt s).1) m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ B := by
    refine aW_comb _ (fun s => (aW_wts _ (hw s)).1) _ (by simp) (fun a b ha hb => ?_) h1 (fun s t hs ht => ?_)
    · have := mul_mem ha hb
      rwa [← map_mul, MvPowerSeries.monomial_mul_monomial, one_mul] at this
    · have := h2 s t hs ht
      rwa [WPres.z, WPres.z, ← map_mul, MvPowerSeries.X_def, MvPowerSeries.X_def,
        MvPowerSeries.monomial_mul_monomial, one_mul] at this
  have hfst : ∀ m : W.σ →₀ ℕ, Finsupp.weight (fun s => (W.wt s).1) m = (Finsupp.weight W.wt m).1 := fun m => by
    induction m using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, Prod.fst_add]
    | single s k => simp [Finsupp.weight_single]
  obtain ⟨μ, hμ, hdec⟩ := part_span O R (ℤ × ℤ) W {m | Finsupp.weight W.wt m = (0, n)} (0, n) (fun _ h => h)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨b, hb, rfl⟩ := hdec f hf
  show W.π _ ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine sum_mem fun m hm => ?_
  rw [map_mul]
  refine mul_mem (h0 _ ⟨b m, hb m, rfl⟩) (hmon m ?_)
  have : Finsupp.weight W.wt m = (0, n) := hμ hm
  rw [hfst, this]

private theorem weight_algebra_generated_degree_two {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (a : ℤ → Submodule O R) [SetLike.GradedMonoid a] (ha : ∀ n, a n = W.part (0, n)) :
    ∃ s : Finset (gradedSub a), (∀ x ∈ s, x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧
      Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ s) = ⊤ := by
  classical
  let U : Set R := Set.range W.z ∪ Set.range fun p : W.σ × W.σ => W.z p.1 * W.z p.2
  have hU : U.Finite := (Set.finite_range _).union (Set.finite_range _)
  let T : Set (gradedSub a) := {x | (x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧ x.1 ∈ U}
  have hT : T.Finite := (hU.preimage Subtype.val_injective.injOn).subset fun x hx => hx.2
  refine ⟨hT.toFinset, fun x hx => (hT.mem_toFinset.1 hx).1, ?_⟩
  rw [hT.coe_toFinset]
  set S := Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ T) with hS
  have key : ∀ n : ℤ, -2 ≤ n → n ≤ 2 → ∀ y ∈ W.part (0, n), y ∈ U → y ∈ S.map (gradedSub a).val := by
    intro n hn hn' y hy hyU
    rw [← ha] at hy
    refine ⟨⟨y, le_iSup a n hy⟩, Algebra.subset_adjoin ?_, rfl⟩
    have h4 : n = 0 ∨ n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 := by omega
    rcases h4 with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hy
    · exact Or.inr ⟨Or.inl hy, hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inl hy), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hy)), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hy)), hyU⟩
  have main := aW_gen W hw (S.map (gradedSub a).val)
    (fun y hy => by
      have hy' : y ∈ a 0 := by rw [ha]; exact hy
      exact ⟨⟨y, le_iSup a 0 hy'⟩, Algebra.subset_adjoin (Or.inl hy'), rfl⟩)
    (fun s hs => by
      have hb := (aW_wts _ (hw s)).2
      refine key (W.wt s).2 (by omega) (by omega) _ ?_ (Or.inl ⟨s, rfl⟩)
      rw [← hs]
      exact W.z_mem s)
    (fun s t hs ht => by
      have hb := (aW_wts _ (hw s)).2
      have hb' := (aW_wts _ (hw t)).2
      refine key ((W.wt s).2 + (W.wt t).2) (by omega) (by omega) _ ?_ (Or.inr ⟨(s, t), rfl⟩)
      have h5 : W.z s * W.z t ∈ W.part (W.wt s + W.wt t) :=
        SetLike.GradedMul.mul_mem (W.z_mem s) (W.z_mem t)
      have h6 : W.wt s + W.wt t = (0, (W.wt s).2 + (W.wt t).2) :=
        Prod.ext (by rw [Prod.fst_add, hs, ht]; rfl) rfl
      rwa [h6] at h5)
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hxS : x ∈ S.map (gradedSub a).val :=
    Submodule.iSup_induction a (motive := fun x => x ∈ S.map (gradedSub a).val) hx (fun n y hy => main n y (ha n ▸ hy))
      (zero_mem _) (fun a b ha hb => add_mem ha hb)
  obtain ⟨y, hy, hxy⟩ := hxS
  obtain rfl : y = ⟨x, hx⟩ := Subtype.ext hxy
  exact hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aW :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], IsWRing M.gr M.x0 := by
  intro Ω _ _ _ l _ c D _ M _
  classical
  have hz : ∀ s, M.W.z s ∈ maximalIdeal M.R := fun s => by
    rw [← res_eq_zero_iff c.O, ← res_map (M.W.origin M.org), WPres.z, M.W.origin_π, MvPowerSeries.constantCoeff_X,
      map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    refine ⟨?_, ?_, ?_⟩
  · haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O (ℤ × ℤ) M.R M.W hz
    let p : M.W.gr 0 →ₐ[c.O] M.gr 0 :=
      { toFun := fun F => ⟨⟨F.1.1, M.aPart_le (n := 0) F.2⟩, F.2⟩
        map_one' := rfl
        map_mul' := fun F G => rfl
        map_zero' := rfl
        map_add' := fun F G => rfl
        commutes' := fun c => rfl }
    haveI : Nontrivial (M.gr 0) := ⟨⟨0, 1, fun h =>
      zero_ne_one (α := M.R) (congrArg (fun x : M.gr 0 => ((x : M.A) : M.R)) h)⟩⟩
    refine co_quot c.O (M.W.gr 0) (M.gr 0) p ?_
    rintro ⟨⟨x, hxA⟩, hx⟩
    exact ⟨⟨⟨x, M.W.part_le_A (j := 0) hx⟩, hx⟩, rfl⟩
  · exact weight_algebra_generated_degree_two M.W M.wt_mem M.aPart (fun _ => rfl)
  · rintro j hj f ⟨g, hg, hgf⟩
    have hgf' : M.W.π g = (f : M.R) := hgf
    show M.W.origin M.org (f : M.R) = 0
    rw [← hgf', M.W.origin_π, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg 0 (by rw [map_zero]; exact fun h => hj (congrArg Prod.snd h).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.XvanExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cob_of_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases ha : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ (z g)).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    rw [hm g, ha g, one_mul, sub_self]
  · push_neg at ha
    obtain ⟨g₀, hg₀⟩ := ha
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.2 hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ _).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    have key : φ ((a g₀ - 1)⁻¹ • z g₀) = m := by
      rw [map_smul, hm g₀, smul_eq_mul, ← sub_one_mul, inv_mul_cancel_left₀ hne]
    rw [map_sub, map_sub, map_smul, key, hm g, smul_eq_mul, sub_self]

theorem UpperTheory.V.GradeZeroInterpolatingElement.xvanExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + red (γ g : c.O) * z h) → D.UnrT z 0 → (∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = red (γ g : c.O) * m - m) → ∃ m, ∀ g, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD k _ red hred γ hγ z hz hcoc hunr hloc
  have hlh : IsLocalHom red := ⟨fun a ha => by
    by_contra hn
    have h0 := hred a ((mem_maximalIdeal a).2 hn)
    rw [h0] at ha
    exact not_isUnit_zero ha⟩
  letI : Algebra (ResidueField c.O) k := (ResidueField.lift red).toAlgebra
  have hι : ∀ a : c.O, red a = algebraMap (ResidueField c.O) k (residue c.O a) := fun a =>
    (ResidueField.lift_residue_apply red a).symm
  have hX : D.XVan γ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hD.xvan D.al (by simp)).1
    · exact (hD.xvan D.be (by simp)).1
    · exact (hD.xvan D.th (by simp)).1
    · exact (hD.xvan D.al (by simp)).2
    · exact (hD.xvan D.be (by simp)).2
    · exact (hD.xvan D.th (by simp)).2
  simp only [hι]
  apply cob_of_coord (fun g => Raw.bar γ g) z
  intro φ
  have h1 : ∀ g h, φ (z (g * h)) = φ (z g) + Raw.bar γ g * φ (z h) := by
    intro g h
    rw [hcoc g h, map_add (f := _), hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have h2 : D.UnrT (fun g => φ (z g)) 0 := by
    intro A hA g hg hb
    simp only [hunr A hA g hg hb, map_zero]
  have h3 : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, φ (z g) = Raw.bar γ g * m - m := by
    intro v hv
    obtain ⟨m, hm⟩ := hloc v hv
    refine ⟨φ m, fun g hg => ?_⟩
    rw [hm g hg, hι, ← Algebra.smul_def, map_sub, map_smul, smul_eq_mul]
  exact hX (fun g => φ (z g)) (hz.comp fun x => φ x) h1 h2 h3
end

