module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0020
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0035
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0001
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0028
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsoluteValueAlt
section
theorem UpperTheory.Reformulated.B.ContDiffOnLocalExtension.abs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ∞} {U : Set E},
  IsOpen U → ∀ {F : E → V}, ContDiffOn ℝ (m : WithTop ℕ∞) F U → ∀ {x : E}, x ∈ U →
    ∃ G : E → V, ContDiff ℝ (m : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F :=
  @UpperTheory.exists_smooth_extension_near
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsoluteValueAltAlt
section
theorem UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs : ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
    {t : E | t * σ t = 1}.Infinite :=
  UpperTheory.infinite_norm_one_elements
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BoundedSums
section
noncomputable def UpperTheory.Reformulated.B.BoundedSums.Bdd :
    {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop :=
    fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), V.Ge K (s n)

noncomputable def UpperTheory.Reformulated.B.BoundedSums.BddS :
    {C : Type} → [inst : Field C] → {σ : Type} → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → MvPowerSeries σ C) → Prop :=
    fun {C : Type} [Field C] {σ : Type} (V : Formalism.L2.FormalSeriesBounds.VF C) (f : ℕ → MvPowerSeries σ C) ↦
      ∀ (μ : σ →₀ ℕ), UpperTheory.Reformulated.B.BoundedSums.Bdd V fun (n : ℕ) ↦ (MvPowerSeries.coeff μ : MvPowerSeries σ C → C) (f n)

private theorem UpperTheory.Reformulated.B.BoundedSums.bdd_sum {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {α : Type}
    (T : Finset α) (s : α → ℕ → C) (h : ∀ a ∈ T, UpperTheory.Reformulated.B.BoundedSums.Bdd V (s a)) :
    UpperTheory.Reformulated.B.BoundedSums.Bdd V fun n ↦ ∑ a ∈ T, s a n := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simpa using Formalism.L2.FormalSeriesBounds.VF.Ge.zero (V := V) 0⟩
  | insert a T ha ih =>
    obtain ⟨K, hK⟩ := h a (Finset.mem_insert_self a T)
    obtain ⟨L, hL⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨min K L, fun n => ?_⟩
    show V.Ge (min K L) (∑ b ∈ insert a T, s b n)
    rw [Finset.sum_insert ha]
    exact ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))

private theorem UpperTheory.Reformulated.B.BoundedSums.bddS_mul {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ : Type}
    {f g : ℕ → MvPowerSeries σ C} (hf : UpperTheory.Reformulated.B.BoundedSums.BddS V f)
    (hg : UpperTheory.Reformulated.B.BoundedSums.BddS V g) : UpperTheory.Reformulated.B.BoundedSums.BddS V fun n ↦ f n * g n := by
  classical
  intro μ
  have h := UpperTheory.Reformulated.B.BoundedSums.bdd_sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (fun p n => MvPowerSeries.coeff p.1 (f n) * MvPowerSeries.coeff p.2 (g n)) (fun p _ => by
      obtain ⟨K, hK⟩ := hf p.1
      obtain ⟨L, hL⟩ := hg p.2
      exact ⟨K + L, fun n => (hK n).mul (hL n)⟩)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n => ?_⟩
  show V.Ge K (MvPowerSeries.coeff μ (f n * g n))
  rw [MvPowerSeries.coeff_mul]
  exact hK n

theorem UpperTheory.Reformulated.B.BoundedSums.prod :
    ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C},
      (∀ i ∈ S, UpperTheory.Reformulated.B.BoundedSums.BddS V (f i)) → UpperTheory.Reformulated.B.BoundedSums.BddS V fun (n : ℕ) ↦ ∏ i ∈ S, f i n := by
  intro C _ V σ ι S f h
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro μ
    refine ⟨0, fun n => ?_⟩
    show V.Ge 0 (MvPowerSeries.coeff μ (∏ i ∈ (∅ : Finset ι), f i n))
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.one
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.zero 0
  | insert a S ha ih =>
    have h2 := UpperTheory.Reformulated.B.BoundedSums.bddS_mul (h a (Finset.mem_insert_self a S))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.prod_insert ha] using h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirCommutation
section
theorem UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm :
    ∀ {A : Type} [inst : Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A),
      Formalism.REAL.GlRel E → ∀ (c d : Fin n), ε c = ε d → Formalism.REAL.CasK ε E * E c d = E c d * Formalism.REAL.CasK ε E := by
  intro A _ n ε E h c d hcd
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a := by
    intro a b
    have h1 := h b a c d
    have h2 := h a b c d
    have : E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a
        = E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0))
          + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
      noncomm_ring
    rw [this, ← h1, ← h2]
    noncomm_ring
  have S1 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
      = ∑ b, if ε c = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have S4 : ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0)
      = ∑ b, if ε d = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have S2 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
      = ∑ a, if ε a = ε d then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have S3 : ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
      = ∑ a, if ε a = ε c then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e : Formalism.REAL.CasK ε E * E c d - E c d * Formalism.REAL.CasK ε E =
      ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0) := by
    simp only [Formalism.REAL.CasK, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have e2 : ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0)
      = ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
        - ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
        + ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
        - ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [key]
    split_ifs <;> simp
  rw [← sub_eq_zero, e, e2, S1, S2, S3, S4, hcd]
  abel
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalueSecond
section
theorem UpperTheory.Reformulated.B.ComplexCommonEigenvectorOfFinrankEq.common_eig :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), Commute (f i) (f j)) →
      ∀ (n : ℕ) (W : Submodule ℂ M),
        Module.finrank ℂ ↥W = n →
          W ≠ ⊥ →
            (∀ (i : ι), ∀ x ∈ W, (f i : M → M) x ∈ W) →
              ∃ v ∈ W, v ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) v = c • v := by
  intro ι M _ _ _ f hc n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hW hinv
  by_cases h : ∀ i, ∃ c : ℂ, ∀ x ∈ W, f i x = c • x
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
    exact ⟨v, hv, hv0, fun i => (h i).imp fun c hc' => hc' v hv⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
    obtain ⟨c, hce⟩ := Module.End.exists_eigenvalue
      ((f i).restrict (p := W) (q := W) (hinv i) : Module.End ℂ W)
    obtain ⟨w, hw⟩ := hce.exists_hasEigenvector
    have hw1 : f i (w : M) = c • (w : M) := congrArg Subtype.val hw.apply_eq_smul
    have hw0 : (w : M) ≠ 0 := fun e => hw.2 (Subtype.ext e)
    have hlt : W ⊓ (f i).eigenspace c < W := by
      refine lt_of_le_of_ne inf_le_left fun e => hi ⟨c, fun x hx => ?_⟩
      rw [← e] at hx
      exact Module.End.mem_eigenspace_iff.1 hx.2
    have hne : W ⊓ (f i).eigenspace c ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, hw0⟩
    obtain ⟨v, hv, hv0, hall⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt)
      (W ⊓ (f i).eigenspace c) rfl hne (fun j x hx => by
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.2 ?_⟩
        have h1 : f i x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
        have h2 : f i (f j x) = f j (f i x) := LinearMap.congr_fun (hc i j).eq x
        rw [h2, h1, map_smul])
    exact ⟨v, hv.1, hv0, hall⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvectorExistence
section
private theorem common_eigenvector_commuting_family {T D : Type}
    [AddCommGroup D] [_root_.Module ℂ D] [FiniteDimensional ℂ D] (φ : T → _root_.Module.End ℂ D)
    (hc : ∀ (s t : T), Commute (φ s) (φ t)) :
    ∀ (n : ℕ) (W : Submodule ℂ D), _root_.Module.finrank ℂ W = n → W ≠ ⊥ →
      (∀ (t : T), ∀ x ∈ W, φ t x ∈ W) →
      ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hn hW hinv
    by_cases hs : ∀ t, ∃ c : ℂ, ∀ x ∈ W, φ t x = c • x
    · choose a ha using hs
      obtain ⟨l, hlW, hl⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨l, a, hl, fun t => ha t l hlW⟩
    · push Not at hs
      obtain ⟨t, ht⟩ := hs
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨c, hcv⟩ := _root_.Module.End.exists_eigenvalue ((φ t).restrict (hinv t))
      obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
      have hv0 : (v : D) ≠ 0 := fun h => hv.2 (Subtype.ext h)
      have hv1 : φ t (v : D) = c • (v : D) := by
        have := congrArg Subtype.val hv.apply_eq_smul
        simpa using this
      let E : Submodule ℂ D := W ⊓ _root_.Module.End.eigenspace (φ t) c
      have hE : ∀ y, y ∈ E ↔ y ∈ W ∧ φ t y = c • y := by
        intro y
        simp [E, Submodule.mem_inf, _root_.Module.End.mem_eigenspace_iff]
      have hEbot : E ≠ ⊥ := by
        intro h
        have : (v : D) ∈ E := (hE _).2 ⟨v.2, hv1⟩
        rw [h] at this
        exact hv0 (by simpa using this)
      have hlt : E < W := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hxW, hx⟩ := ht c
        exact hx ((hE x).1 (h ▸ hxW)).2
      have hfr : _root_.Module.finrank ℂ E < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      refine ih _ hfr E rfl hEbot ?_
      intro s y hy
      obtain ⟨hyW, hyc⟩ := (hE y).1 hy
      refine (hE _).2 ⟨hinv s y hyW, ?_⟩
      have h1 : φ t (φ s y) = φ s (φ t y) := by
        have := (hc t s).eq
        exact congrArg (fun f : _root_.Module.End ℂ D => f y) this
      rw [h1, hyc, map_smul]

theorem UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector :
    ∀ {T D : Type}
    [inst : AddCommGroup D] [inst_1 : _root_.Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D] (φ : T → Module.End ℂ D),
    (∀ (s t : T), Commute (φ s) (φ t)) → ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro T D _ _ _ _ φ hc
  exact common_eigenvector_commuting_family φ hc _ ⊤ rfl top_ne_bot (fun _ _ _ => Submodule.mem_top)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DensePiDecomposition
section
open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff {σ O : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    simp [h0]
  | insert i s _ ih =>
    intro f hf
    let h : MvPowerSeries σ O := fun n => if n i = 0 then coeff n f else 0
    have hh : ∀ n, coeff n h = if n i = 0 then coeff n f else 0 := fun _ => rfl
    have h1 : h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
      refine ih h fun n hn => ?_
      rw [hh]
      split_ifs with hi
      · refine hf n fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hi
        · exact hn j hj
      · rfl
    have h2 : (X i : MvPowerSeries σ O) ∣ f - h := by
      refine X_dvd_iff.2 fun n hn => ?_
      rw [map_sub, hh, if_pos hn, sub_self]
    have h3 : f - h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨i, rfl⟩)
    simpa using Ideal.add_mem _ h3 h1

open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp {σ O : Type} [CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O) :
    ∃ (c : O) (g : σ → MvPowerSeries σ O),
      f = algebraMap O (MvPowerSeries σ O) c + ∑ i, g i * X i := by
  classical
  have h := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff Finset.univ
    (f - algebraMap O (MvPowerSeries σ O) (coeff 0 f)) (by
      intro n hn
      have h0 : n = 0 := by
        ext i
        simpa using hn i (Finset.mem_univ i)
      subst h0
      simp [MvPowerSeries.algebraMap_apply])
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  exact ⟨coeff 0 f, g, by rw [hg]; ring⟩

theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.pi_dense :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {X : Type} [inst_2 : AddCommGroup X] {R : Type}
      [inst_3 : CommRing R] [inst_4 : Algebra O R] [inst_5 : UpperTheory.V.Alg.IsCO O R] (W : UpperTheory.V.Alg.WPres O X R),
      (∀ (s : W.σ), W.z s ∈ IsLocalRing.maximalIdeal R) →
        ∀ (N : ℕ) (x : R), ∃ a ∈ W.A, x - a ∈ IsLocalRing.maximalIdeal R ^ N := by
  intro O _ _ X _ R _ _ _ W hz N
  induction N with
  | zero => intro x; exact ⟨0, W.A.zero_mem, by simp⟩
  | succ N ih =>
    intro x
    obtain ⟨f, rfl⟩ := W.surj x
    obtain ⟨c, g, rfl⟩ := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp f
    choose a ha hm using fun i => ih (W.π (g i))
    refine ⟨algebraMap O R c + ∑ i, a i * W.z i, ?_, ?_⟩
    · exact W.A.add_mem (W.A.algebraMap_mem c)
        (W.A.sum_mem fun i _ => W.A.mul_mem (ha i) (W.part_le_A (W.z_mem i)))
    · have he : W.π (algebraMap O _ c + ∑ i, g i * MvPowerSeries.X i)
          - (algebraMap O R c + ∑ i, a i * W.z i) = ∑ i, (W.π (g i) - a i) * W.z i := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), AlgHom.commutes, map_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, sub_mul]
        rfl
      rw [he, pow_succ]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hm i) (hz i)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagHermitian
section
theorem UpperTheory.Reformulated.B.Gka4.diag_hermitian :
    ∀ (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] (σ : E →ₐ[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
        ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E),
          HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ T →
            ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ),
              HeckeCharacterZeroLocus.SiegelWeilU.cT (↑σ : E →+* E) (↑g : Matrix (Fin n) (Fin n) E) * T * (↑g : Matrix (Fin n) (Fin n) E) =
                Matrix.diagonal fun (i : Fin n) ↦ (Algebra.algebraMap F E : F → E) (↑(D i) : F) := by
  intro F E _ _ _ _ _ σ hCM n T hT
  obtain ⟨-, hC, h2, hτ⟩ := hCM
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ τ, hτ τ, star_star]
  have hnr : ¬ NumberField.ComplexEmbedding.IsReal τ := by
    intro hr
    have := hC.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at this
    exact this hr
  obtain ⟨α, hα⟩ : ∃ α, σ α ≠ α := by
    by_contra hcon
    push_neg at hcon
    apply hnr
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have := hτ τ x
    rw [hcon x] at this
    exact this.symm
  have hfix := UpperTheory.fixed_quadratic_mem_base h2 σ α hα
  obtain ⟨g, D, h⟩ := UpperTheory.hermitian_diagonalisation σ hinv hfix n T hT.1 hT.2
  exact ⟨g, D, h⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCommonEigenvectorSecond
section
theorem UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), f i * f j = f j * f i) →
      ∀ (W : Submodule ℂ M),
        W ≠ ⊥ →
          (∀ (i : ι), ∀ y ∈ W, (f i : M → M) y ∈ W) →
            ∃ y ∈ W, y ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) y = c • y := by
  intro ι M _ _ _ f hc W hW hinv
  obtain ⟨V, ⟨hVW, hV0, hVinv⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ M)).has_min
      {V : Submodule ℂ M | V ≤ W ∧ V ≠ ⊥ ∧ ∀ i, ∀ y ∈ V, f i y ∈ V} ⟨W, le_rfl, hW, hinv⟩
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  refine ⟨y, hVW hyV, hy0, fun i => ?_⟩
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV0
  obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue ((f i).restrict (hVinv i) : Module.End ℂ V)
  obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
  have hv1 : f i (v : M) = c • (v : M) := by
    have h := congrArg Subtype.val hv.apply_eq_smul
    simpa using h
  have hv0 : (v : M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  refine ⟨c, ?_⟩
  by_contra hne
  refine hmin (V ⊓ (f i).eigenspace c) ⟨inf_le_left.trans hVW, ?_, ?_⟩ ?_
  · intro h
    have hm : (v : M) ∈ V ⊓ (f i).eigenspace c :=
      ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv1⟩
    rw [h] at hm
    exact hv0 ((Submodule.mem_bot ℂ).mp hm)
  · intro j z hz
    refine ⟨hVinv j z hz.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
    have hz2 : f i z = c • z := Module.End.mem_eigenspace_iff.mp hz.2
    have h : f i (f j z) = f j (f i z) := by
      rw [← Module.End.mul_apply, hc i j, Module.End.mul_apply]
    rw [h, hz2, map_smul]
  · refine lt_of_le_of_ne inf_le_left fun h => hne ?_
    have hm : y ∈ V ⊓ (f i).eigenspace c := by rw [h]; exact hyV
    exact Module.End.mem_eigenspace_iff.mp hm.2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulIntegral
section
private theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral {E : Type} [Field E] [NumberField E]
    (a : E) : ∃ M : ℕ, M ≠ 0 ∧ ∃ b : NumberField.RingOfIntegers E, (b : E) = (M : E) * a := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ (y • (y • a)) := hint.smul y
  refine ⟨(y * y).natAbs, Int.natAbs_ne_zero.mpr (mul_ne_zero hy hy), ⟨y • (y • a), h2⟩, ?_⟩
  have h3 : (((y * y).natAbs : ℕ) : E) = ((y * y : ℤ) : E) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
  rw [h3]
  change y • (y • a) = _
  rw [smul_smul, zsmul_eq_mul]

theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → E), ∃ (N : ℕ), N ≠ (0 : ℕ) ∧ N • u ∈ X.Λ := by
  intro E _ _ _ r X u
  have hu : u ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [nsmul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx N
    · rw [mul_smul]; exact nsmul_mem hy M
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, b, hb⟩ := UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral a
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h : (M * N) • a • x = b • (N • x) := by
      funext i
      change (M * N) • (a * x i) = (b : E) * (N • x i)
      rw [hb, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [h]
    exact X.Λ.smul_mem b hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPFSum
section
theorem UpperTheory.Reformulated.B.IsPFSum.isPF_sum :
    ∀ {A : Type} [inst : Ring A] [inst_1 : Algebra ℂ A] {ι : Type} (s : Finset ι) {f : ι → ℂ → A},
      (∀ i ∈ s, UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF (f i)) → UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF fun (Y : ℂ) ↦ ∑ i ∈ s, f i Y := by
  intro A _ _ ι s f h
  classical
  unfold UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF at h ⊢
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun Y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨q, hq⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨p + q, fun Y => ?_⟩
    have h1 : (∑ i ∈ s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) q := hq Y
    show (∑ i ∈ insert a s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) (p + q)
    rw [Finset.sum_insert ha, hp, h1, Polynomial.eval_add]
end

