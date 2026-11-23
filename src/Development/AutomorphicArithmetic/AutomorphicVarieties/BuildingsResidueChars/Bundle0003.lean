module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOrdinaryProjectorOfEventuallyPeriodic
section
private theorem UpperTheory.pow_preserves_submodule {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (n : ℕ) :
    ∀ f ∈ U, (T ^ n) f ∈ U := by
  induction n with
  | zero =>
    intro f hf
    simpa using hf
  | succ n ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT f hf)

private theorem UpperTheory.periodic_difference_shift {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) :
    (T ^ (m + q)) f - (T ^ m) f ∈ U := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h' := UpperTheory.pow_preserves_submodule U T hT r _ h
  have e : (T ^ r) ((T ^ (a + q)) f - (T ^ a) f) = (T ^ (a + r + q)) f - (T ^ (a + r)) f := by
    rw [show a + r + q = r + (a + q) by ring, show a + r = r + a by ring,
      pow_add T r (a + q), pow_add T r a, Module.End.mul_apply, Module.End.mul_apply, map_sub]
  rw [e] at h'
  exact h'

private theorem UpperTheory.periodic_difference_mul_period {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) (c : ℕ) :
    (T ^ (m + q * c)) f - (T ^ m) f ∈ U := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h2 := UpperTheory.periodic_difference_shift U T hT f a q h (m + q * c) (by omega)
    have e : m + q * (c + 1) = m + q * c + q := by ring
    rw [e]
    have hs := U.add_mem h2 ih
    rw [sub_add_sub_cancel] at hs
    exact hs

private theorem UpperTheory.factorial_powers_cauchy {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a p : ℕ)
    (h : (T ^ (a + (p + 1))) f - (T ^ a) f ∈ U) :
    ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j → (T ^ i.factorial) f - (T ^ j.factorial) f ∈ U := by
  obtain ⟨N, hN⟩ : ∃ N, N = a * (p + 1) := ⟨_, rfl⟩
  have haN : a ≤ N := by
    rw [hN]
    exact Nat.le_mul_of_pos_right a (Nat.succ_pos p)
  have hbase : ∀ i, N + (p + 1) ≤ i → (T ^ i.factorial) f - (T ^ N) f ∈ U := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.succ_pos p) (show p + 1 ≤ i by omega)
    have hi' : N ≤ i.factorial := le_trans (by omega) (Nat.self_le_factorial i)
    have hak : a ≤ k := by
      rw [hk, hN, mul_comm] at hi'
      exact Nat.le_of_mul_le_mul_left hi' (Nat.succ_pos p)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hak
    have e : i.factorial = N + (p + 1) * c := by
      rw [hk, hN, Nat.succ_eq_add_one]
      ring
    rw [e]
    exact UpperTheory.periodic_difference_mul_period U T hT f a (p + 1) h N haN c
  refine ⟨N + (p + 1), fun i j hi hj => ?_⟩
  have hs := U.sub_mem (hbase i hi) (hbase j hj)
  rwa [sub_sub_sub_cancel_right] at hs

theorem UpperTheory.exists_ordinaryProjector_of_eventually_periodic :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (V : ℕ → Submodule A M) (T : Module.End A M), Antitone V → (∀ k, ∀ f ∈ V k, T f ∈ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ a : ℕ → M, (∀ k, a (k + 1) - a k ∈ V k) → ∃ L, ∀ k, L - a k ∈ V k) → (∀ f k, ∃ a p : ℕ, (T ^ (a + (p + 1))) f - (T ^ a) f ∈ V k) → ∃ e : Module.End A M, ∀ f k, (∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - e f ∈ V k) ∧ (∃ n : ℕ, (T ^ (n + 1)) (e f) - e f ∈ V k) ∧ (f ∈ V k → e f ∈ V k) ∧ ((∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V k) → e f - f ∈ V k) := by
  intro A M _ _ _ V T hV hT hsep hcomp hper
  have hJ : ∀ f k, ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j →
      (T ^ i.factorial) f - (T ^ j.factorial) f ∈ V k := by
    intro f k
    obtain ⟨a, p, h⟩ := hper f k
    exact UpperTheory.factorial_powers_cauchy (V k) T (hT k) f a p h
  choose J hJ using hJ
  let Nm : M → ℕ → ℕ := fun f k => ∑ i ∈ Finset.range (k + 1), J f i
  have hNmJ : ∀ f k, J f k ≤ Nm f k := fun f k =>
    Finset.single_le_sum (f := J f) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hNmmono : ∀ f k, Nm f k ≤ Nm f (k + 1) := fun f k => by
    simp only [Nm]
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  have hseq : ∀ f k, (T ^ (Nm f (k + 1)).factorial) f - (T ^ (Nm f k).factorial) f ∈ V k :=
    fun f k => hJ f k _ _ (le_trans (hNmJ f k) (hNmmono f k)) (hNmJ f k)
  have hlim : ∀ f, ∃ L, ∀ k, L - (T ^ (Nm f k).factorial) f ∈ V k := fun f =>
    hcomp (fun k => (T ^ (Nm f k).factorial) f) (hseq f)
  choose L hL using hlim
  let P : M → M → Prop := fun f x => ∀ k, ∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - x ∈ V k
  have hPL : ∀ f, P f (L f) := by
    intro f k
    refine ⟨Nm f k, fun j hj => ?_⟩
    have h1 := hJ f k j (Nm f k) (le_trans (hNmJ f k) hj) (hNmJ f k)
    have hs := (V k).sub_mem h1 (hL f k)
    rwa [sub_sub_sub_cancel_right] at hs
  have huniq : ∀ f x y, P f x → P f y → x = y := by
    intro f x y hx hy
    have hxy : x - y = 0 := by
      apply hsep
      intro k
      obtain ⟨J1, h1⟩ := hx k
      obtain ⟨J2, h2⟩ := hy k
      have hs := (V k).sub_mem (h2 (max J1 J2) (le_max_right _ _)) (h1 (max J1 J2) (le_max_left _ _))
      rwa [sub_sub_sub_cancel_left] at hs
    exact sub_eq_zero.mp hxy
  have hPadd : ∀ f g x y, P f x → P g y → P (f + g) (x + y) := by
    intro f g x y hx hy k
    obtain ⟨J1, h1⟩ := hx k
    obtain ⟨J2, h2⟩ := hy k
    refine ⟨max J1 J2, fun j hj => ?_⟩
    have hs := (V k).add_mem (h1 j (le_trans (le_max_left _ _) hj))
      (h2 j (le_trans (le_max_right _ _) hj))
    rw [map_add (f := _)]
    convert hs using 1
    abel
  have hPsmul : ∀ (c : A) f x, P f x → P (c • f) (c • x) := by
    intro c f x hx k
    obtain ⟨J1, h1⟩ := hx k
    refine ⟨J1, fun j hj => ?_⟩
    have hs := (V k).smul_mem c (h1 j hj)
    rwa [smul_sub, ← map_smul] at hs
  let e : Module.End A M :=
    { toFun := L
      map_add' := fun f g => huniq (f + g) _ _ (hPL _) (hPadd f g _ _ (hPL f) (hPL g))
      map_smul' := fun c f => huniq (c • f) _ _ (hPL _) (hPsmul c f _ (hPL f)) }
  refine ⟨e, fun f k => ⟨hPL f k, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, p, h⟩ := hper f k
    obtain ⟨J1, h1⟩ := hPL f k
    refine ⟨p, ?_⟩
    show (T ^ (p + 1)) (L f) - L f ∈ V k
    obtain ⟨j, hjdef⟩ : ∃ j, j = max J1 a := ⟨_, rfl⟩
    have hja : a ≤ j.factorial := le_trans (by omega) (Nat.self_le_factorial _)
    have hA := h1 j (by omega)
    have hB := UpperTheory.periodic_difference_shift (V k) T (hT k) f a (p + 1) h j.factorial hja
    have hC := UpperTheory.pow_preserves_submodule (V k) T (hT k) (p + 1) _ hA
    have eq : (T ^ (p + 1)) ((T ^ j.factorial) f) = (T ^ (j.factorial + (p + 1))) f := by
      rw [add_comm j.factorial (p + 1), pow_add T (p + 1) j.factorial, Module.End.mul_apply]
    have hsum := (V k).add_mem ((V k).add_mem ((V k).neg_mem hC) hB) hA
    rw [map_sub, eq] at hsum
    convert hsum using 1
    abel
  · intro hf
    obtain ⟨J1, h1⟩ := hPL f k
    have hA := h1 J1 le_rfl
    have hB := UpperTheory.pow_preserves_submodule (V k) T (hT k) J1.factorial f hf
    show L f ∈ V k
    have hs := (V k).sub_mem hB hA
    rwa [sub_sub_cancel] at hs
  · rintro ⟨n, hn⟩
    have h0 : (T ^ (0 + (n + 1))) f - (T ^ 0) f ∈ V k := by simpa using hn
    obtain ⟨J1, h1⟩ := hPL f k
    obtain ⟨N, hN⟩ : ∃ N, N = max J1 (n + 1) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.succ_pos n) (show n + 1 ≤ N by omega)
    have hB := UpperTheory.periodic_difference_mul_period (V k) T (hT k) f 0 (n + 1) h0 0 le_rfl c
    rw [zero_add, pow_zero, ← hc] at hB
    have hA := h1 N (by omega)
    show L f - f ∈ V k
    have hs := (V k).sub_mem hB hA
    rw [sub_sub_sub_cancel_left] at hs
    simpa using hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LeSpanIntegralValuedOfGaloisStable
section
private theorem UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ]
    [Algebra.IsAlgebraic O ℂ] (z : ℂ) (hz : ∀ γ : ℂ ≃ₐ[O] ℂ, γ z = z) :
    ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * z = algebraMap O ℂ a := by
  letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ
  haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ
  haveI : Algebra.IsAlgebraic (FractionRing O) ℂ :=
    Algebra.IsAlgebraic.extendScalars (FaithfulSMul.algebraMap_injective O (FractionRing O))
  haveI : CharZero (FractionRing O) := RingHom.charZero (algebraMap (FractionRing O) ℂ)
  haveI : Algebra.IsSeparable (FractionRing O) ℂ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsAlgClosure (FractionRing O) ℂ := ⟨inferInstance, inferInstance⟩
  haveI : Normal (FractionRing O) ℂ := inferInstance
  haveI : IsGalois (FractionRing O) ℂ := ⟨⟩
  have hmem : z ∈ Set.range (algebraMap (FractionRing O) ℂ) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed z).2 (fun f => hz (f.restrictScalars O))
  obtain ⟨q, rfl⟩ := hmem
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) q
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  show algebraMap O ℂ b * algebraMap (FractionRing O) ℂ (IsLocalization.mk' (FractionRing O) a b) =
    algebraMap O ℂ a
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ (b : O),
    IsScalarTower.algebraMap_apply O (FractionRing O) ℂ a, ← map_mul, mul_comm,
    IsLocalization.mk'_spec]

theorem UpperTheory.le_span_integralValued_of_galoisStable :
    ∀ (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (X : Type) [Finite X] (I : Submodule ℂ (X → ℂ)), (∀ γ : ℂ ≃ₐ[O] ℂ, ∀ x ∈ I, (fun g => γ (x g)) ∈ I) → I ≤ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
  intro O _ _ _ _ _ X _ I hI
  classical
  haveI := Fintype.ofFinite X
  have hfix : ∀ x ∈ I, (∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x) →
      x ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro x hx hγ
    have hc : ∀ g, ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * x g = algebraMap O ℂ a :=
      fun g => UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed O (x g) (fun γ => congrFun (hγ γ) g)
    choose a b hb hab using hc
    have hB : algebraMap O ℂ (∏ g, b g) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun g _ =>
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O ℂ)).2 (hb g))
    have hmem : algebraMap O ℂ (∏ g, b g) • x ∈
        Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
      apply Submodule.subset_span
      refine ⟨I.smul_mem _ hx, fun g => ⟨a g * ∏ h ∈ Finset.univ.erase g, b h, ?_⟩⟩
      show algebraMap O ℂ (a g * ∏ h ∈ Finset.univ.erase g, b h) = algebraMap O ℂ (∏ g, b g) * x g
      rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ g)]
      simp only [map_mul, ← hab g]
      ring
    have h2 := Submodule.smul_mem _ (algebraMap O ℂ (∏ g, b g))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hB, one_smul] at h2
  have key : ∀ n : ℕ, ∀ y ∈ I, (Finset.univ.filter (fun g => y g ≠ 0)).card ≤ n →
      y ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro n
    induction n with
    | zero =>
      intro y hy hc
      have hy0 : y = 0 := by
        funext g
        by_contra h
        have := Finset.card_pos.2
          ⟨g, (by simpa using h : g ∈ Finset.univ.filter (fun g => y g ≠ 0))⟩
        omega
      rw [hy0]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro y hy hc
      by_cases h0 : y = 0
      · rw [h0]
        exact Submodule.zero_mem _
      obtain ⟨g0, hg0⟩ : ∃ g, y g ≠ 0 := by
        by_contra h
        push_neg at h
        exact h0 (funext h)
      obtain ⟨x, hx⟩ : ∃ x : X → ℂ, x = (y g0)⁻¹ • y := ⟨_, rfl⟩
      have hxI : x ∈ I := by
        rw [hx]
        exact I.smul_mem _ hy
      have hxg0 : x g0 = 1 := by
        rw [hx]
        simp [hg0]
      have hsupp : ∀ g, x g = 0 ↔ y g = 0 := by
        intro g
        rw [hx]
        simp [hg0]
      have hyx : y = y g0 • x := by
        rw [hx, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      by_cases hall : ∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x
      · rw [hyx]
        exact Submodule.smul_mem _ _ (hfix x hxI hall)
      · push_neg at hall
        obtain ⟨γ, hγ⟩ := hall
        obtain ⟨d, hd⟩ : ∃ d : X → ℂ, d = (fun g => γ (x g)) - x := ⟨_, rfl⟩
        have hdI : d ∈ I := by
          rw [hd]
          exact I.sub_mem (hI γ x hxI) hxI
        have hd0 : d ≠ 0 := by
          rw [hd]
          exact sub_ne_zero.2 hγ
        obtain ⟨g1, hg1⟩ : ∃ g, d g ≠ 0 := by
          by_contra h
          push_neg at h
          exact hd0 (funext h)
        have hdsupp : ∀ g, y g = 0 → d g = 0 := by
          intro g hg
          rw [hd]
          simp [(hsupp g).2 hg]
        have hdg0 : d g0 = 0 := by
          rw [hd]
          simp [hxg0]
        have hy1 : y g1 ≠ 0 := fun e => hg1 (hdsupp g1 e)
        have hdcard : (Finset.univ.filter (fun g => d g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => d g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g0 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun e => hg (e ▸ hdg0), fun e => hg (hdsupp g e)⟩
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g0 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hg0])
          omega
        have hdW := ih d hdI hdcard
        obtain ⟨y', hy'⟩ : ∃ y' : X → ℂ, y' = y - (y g1 / d g1) • d := ⟨_, rfl⟩
        have hy'I : y' ∈ I := by
          rw [hy']
          exact I.sub_mem hy (I.smul_mem _ hdI)
        have hy'card : (Finset.univ.filter (fun g => y' g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => y' g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g1 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_⟩
            · rintro rfl
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hg1, sub_self]
            · intro e
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e, hdsupp g e, mul_zero, sub_zero]
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g1 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hy1])
          omega
        have hy'W := ih y' hy'I hy'card
        have hyy : y = y' + (y g1 / d g1) • d := by
          rw [hy', sub_add_cancel]
        rw [hyy]
        exact Submodule.add_mem _ hy'W (Submodule.smul_mem _ _ hdW)
  intro y hy
  exact key _ y hy le_rfl
end

