module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LayerApproximation
section
private theorem UpperTheory.Reformulated.B.LayerApproximation.first_layer {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ (2 : ℕ)) :
    ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2 := by
  have hspan : ∀ y ∈ Ideal.span T, ∃ a ∈ A, a ∈ m ∧ y - a ∈ m ^ 2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨t, (hT t ht).1, (hT t ht).2, by simp⟩
    | zero => exact ⟨0, A.zero_mem, m.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨b, hb, hbm, hvb⟩ := hv
      refine ⟨a + b, A.add_mem ha hb, m.add_mem ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb
    | smul r u _ hu =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨c, hc⟩ := h0 r
      refine ⟨algebraMap O R c * a, A.mul_mem (A.algebraMap_mem c) ha,
        m.mul_mem_left _ ham, ?_⟩
      have e : r • u - algebraMap O R c * a = r * (u - a) + (r - algebraMap O R c) * a := by
        rw [smul_eq_mul]; ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hc ham
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hm hx)
  obtain ⟨a, ha, ham, hya⟩ := hspan y hy
  refine ⟨a, ha, ham, ?_⟩
  have e : y + z - a = (y - a) + z := by ring
  rw [e]
  exact Ideal.add_mem _ hya hz

private theorem UpperTheory.Reformulated.B.LayerApproximation.all_layers {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (h1 : ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2) (N : ℕ) :
    ∀ x ∈ m ^ N, ∃ a ∈ A, a ∈ m ^ N ∧ x - a ∈ m ^ (N + 1) := by
  induction N with
  | zero =>
    intro x _
    obtain ⟨c, hc⟩ := h0 x
    exact ⟨algebraMap O R c, A.algebraMap_mem c, by simp, by simpa using hc⟩
  | succ N ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨a, ha, ham, hya⟩ := ih y hy
      obtain ⟨b, hb, hbm, hzb⟩ := h1 z hz
      refine ⟨a * b, A.mul_mem ha hb, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ham hbm
      · have e : y * z - a * b = y * (z - b) + (y - a) * b := by ring
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show N + 1 + 1 = N + 2 from rfl, pow_add]
          exact Ideal.mul_mem_mul hy hzb
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hya hbm
    · rintro u v ⟨a, ha, ham, hua⟩ ⟨b, hb, hbm, hvb⟩
      refine ⟨a + b, A.add_mem ha hb, Ideal.add_mem _ ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb

theorem UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : CommRing R]
    [inst_2 : Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R),
    (∀ (x : R), ∃ (a : O), x - (Algebra.algebraMap O R : O → R) a ∈ m) →
      (∀ t ∈ T, t ∈ A ∧ t ∈ m) → m ≤ Ideal.span T ⊔ m ^ (2 : ℕ) → ∀ (N : ℕ) (x : R), ∃ a ∈ A, x - a ∈ m ^ N := by
  intro O R _ _ _ m A T h0 hT hm N x
  have h1 := UpperTheory.Reformulated.B.LayerApproximation.first_layer m A T h0 hT hm
  induction N with
  | zero => exact ⟨0, A.zero_mem, by simp⟩
  | succ N ih =>
    obtain ⟨a, ha, hxa⟩ := ih
    obtain ⟨b, hb, -, hab⟩ := UpperTheory.Reformulated.B.LayerApproximation.all_layers m A h0 h1 N _ hxa
    refine ⟨a + b, A.add_mem ha hb, ?_⟩
    have e : x - (a + b) = x - a - b := by ring
    rw [e]
    exact hab
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeSpanSingletonOfForallMemEq
section
theorem UpperTheory.Reformulated.B.Yhc2.le_span_singleton_of_forall_mem_eq.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π ξ : R} [IsAdicComplete (Ideal.span {π}) R] {J : Ideal R},
      (∀ x ∈ J, ∃ (a : R), ∃ z ∈ J, x = a * ξ + z * π) → J ≤ Ideal.span {ξ} := by
  intro R _ π ξ hc J h x hx
  choose! a z hz he using h
  have hsm : ∀ (n : ℕ) (u v : R),
      u ≡ v [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule R R)] ↔ π ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
      Ideal.mem_span_singleton]
  have hzs : ∀ n : ℕ, z^[n] x ∈ J := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hz _ ih
  let f : ℕ → R := fun n => ∑ i ∈ Finset.range n, a (z^[i] x) * π ^ i
  have hf : ∀ n, f (n + 1) = f n + a (z^[n] x) * π ^ n := fun n => Finset.sum_range_succ _ _
  have key : ∀ n, x = f n * ξ + z^[n] x * π ^ n := by
    intro n
    induction n with
    | zero => simp [f]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hf]
      have h1 := he _ (hzs n)
      linear_combination ih + π ^ n * h1
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {π}) ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [hsm]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hf, ← sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow π hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcau
  have h0 : x - L * ξ = 0 := by
    apply IsHausdorff.haus hc.toIsHausdorff
    intro n
    rw [hsm]
    obtain ⟨c, hc'⟩ := (hsm _ _ _).1 (hL n)
    exact ⟨c * ξ + z^[n] x, by linear_combination key n + ξ * hc'⟩
  exact Ideal.mem_span_singleton'.2 ⟨L, (sub_eq_zero.1 h0).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftEigen
section
theorem UpperTheory.Reformulated.B.R4.lift_eigen :
    ∀ {T V : Type} [inst : CommGroup T]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V},
    (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) v = (↑((ψ : T → ℂˣ) t) : ℂ) • v) →
      μ ≠ ψ →
        y ∉ ℂ ∙ v →
          (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) y - (↑((μ : T → ℂˣ) t) : ℂ) • y ∈ ℂ ∙ v) →
            v ≠ (0 : V) →
              ∃ (z : V), z ≠ (0 : V) ∧ ∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) z = (↑((μ : T → ℂˣ) t) : ℂ) • z := by
  intro T V _ _ _ ρ ψ μ v y hv hne hy hmod _
  obtain ⟨s, hs⟩ : ∃ s, μ s ≠ ψ s := DFunLike.ne_iff.mp hne
  have hs' : ((μ s : ℂˣ) : ℂ) - ((ψ s : ℂˣ) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hs (Units.ext h)
  refine ⟨ρ s y - ((ψ s : ℂˣ) : ℂ) • y, ?_, ?_⟩
  · intro h0
    apply hy
    have h1 := hmod s
    rw [sub_eq_zero.mp h0, ← sub_smul, ← neg_sub, neg_smul, neg_mem_iff] at h1
    exact (Submodule.smul_mem_iff _ hs').mp h1
  · intro t
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmod t)
    have hty : ρ t y = ((μ t : ℂˣ) : ℂ) • y + b • v := by
      rw [hb]; abel
    have hcomm : ρ t (ρ s y) = ρ s (ρ t y) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [map_sub, map_smul, hcomm, hty, map_add (f := _), map_smul, map_smul, hv s]
    module
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftMap
section
theorem UpperTheory.Reformulated.B.Qk56.lift_map :
    ∀ {α β : Type} (f : α → β) (B : Multiset α)
    (t : Multiset β), (∀ x ∈ t, x ∈ Multiset.map f B) → ∃ (t' : Multiset α), Multiset.map f t' = t ∧ ∀ x ∈ t', x ∈ B := by
  intro α β f B t
  induction t using Multiset.induction_on with
  | empty => exact fun _ => ⟨0, Multiset.map_zero f, fun x hx => absurd hx (Multiset.notMem_zero x)⟩
  | cons b s ih =>
    intro h
    obtain ⟨s', hs', hB⟩ := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    obtain ⟨a, ha, hab⟩ := Multiset.mem_map.1 (h b (Multiset.mem_cons_self b s))
    refine ⟨a ::ₘ s', by rw [Multiset.map_cons, hab, hs'], fun x hx => ?_⟩
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hB x hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LimitOfFinite
section
theorem UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite.{u_1, u_2}
    {A : Type u_1} {M : Type u_2} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m : ℕ, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L : M, ∀ m : ℕ, f m - L ∈ (I ^ m • ⊤ : Submodule A M) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have key : ∀ (J : Ideal A) (x : M), x ∈ (J • ⊤ : Submodule A M) →
      ∃ d : Fin n → A, (∀ i, d i ∈ J) ∧ ∑ i, d i • s i = x := by
    intro J x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      have hy : y ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
      refine ⟨fun i => r * c i, fun i => J.mul_mem_right _ hr, ?_⟩
      rw [← hc, Finset.smul_sum]
      simp [mul_smul]
    · rintro x y ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
      refine ⟨fun i => d i + e i, fun i => J.add_mem (hd i) (he i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
  choose d hd hdf using fun m => key (I ^ m) _ (hf m)
  let g : ℕ → Fin n → A := fun m i => ∑ k ∈ Finset.range m, d k i
  have hg : ∀ m, f m = f 0 - ∑ i, g m i • s i := by
    intro m
    induction m with
    | zero => simp [g]
    | succ m ih =>
      have h1 : ∑ i, g (m + 1) i • s i = ∑ i, g m i • s i + ∑ i, d m i • s i := by
        simp [g, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      rw [h1, hdf m, ← sub_sub, ← ih]
      abel
  have hc : ∀ i, ∀ m k, m ≤ k → g m i - g k i ∈ I ^ m := by
    intro i m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have h1 : g m i - g (k + 1) i = g m i - g k i - d k i := by
        simp only [g, Finset.sum_range_succ]; ring
      rw [h1]
      exact (I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmk (hd k i))
  have hl : ∀ i, ∃ a : A, ∀ m, g m i - a ∈ I ^ m := by
    intro i
    obtain ⟨a, ha⟩ := hI.prec (f := fun m => g m i) (by
      intro m k hmk
      rw [SModEq.sub_mem]
      simpa using hc i m k hmk)
    refine ⟨a, fun m => ?_⟩
    have := ha m
    rw [SModEq.sub_mem] at this
    simpa using this
  choose a ha using hl
  refine ⟨f 0 - ∑ i, a i • s i, fun m => ?_⟩
  have h2 : f m - (f 0 - ∑ i, a i • s i) = -∑ i, (g m i - a i) • s i := by
    rw [hg m]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [h2]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem_smul (ha i m) Submodule.mem_top)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinBound
section
theorem UpperTheory.Reformulated.B.Qj19.lin_bound.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] ℂ),
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧ ∀ (B : Matrix ι ι ℂ) (C : ℝ), (∀ (i j : ι), ‖B i j‖ ≤ C) → ‖(L : Matrix ι ι ℂ → ℂ) B‖ ≤ K * C := by
  intro ι _ _ L
  refine ⟨∑ i, ∑ j, ‖L (Matrix.single i j 1)‖, by positivity, fun B C hB => ?_⟩
  have h : L B = ∑ i, ∑ j, B i j * L (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hB i j) (norm_nonneg _)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinearIndependentEigenvectors
section
theorem UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {Ξ P : Type}
    (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ),
    Function.Injective ev →
      ∀ (v : Ξ → V),
        (∀ (ξ : Ξ), v ξ ≠ (0 : V)) → (∀ (ξ : Ξ) (p : P), (T p : V → V) (v ξ) = ev ξ p • v ξ) → LinearIndependent ℂ v := by
  intro V _ _ Ξ P T ev hinj v hv hT
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : ev i ≠ ev a := fun h => ha (hinj h ▸ hi)
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
      have h1 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev j p) • v j = 0 := by
        have h := congrArg (T p) hg
        set_option synthInstance.maxHeartbeats 100000 in
          simpa only [map_add (f := _), map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev a p) • v j = 0 := by
        have h := congrArg (fun x => ev a p • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm] using h
      have h3 : ∑ j ∈ s, (g j * (ev j p - ev a p)) • v j = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)
      have h4 := ih (fun j => g j * (ev j p - ev a p)) h3 i hi
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hp)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LintegralSwapNorm
section
open MeasureTheory in
theorem UpperTheory.Reformulated.B.Qf2.lintegral_swap_norm :
    ∀ {X T : Type} [inst : Group X]
    [inst_1 : TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [inst_6 : MeasurableSpace X] [BorelSpace X] [inst_8 : Group T] [inst_9 : TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [inst_14 : MeasurableSpace T] [BorelSpace T]
    (μ : MeasureTheory.Measure X) [μ.IsHaarMeasure] (ν : MeasureTheory.Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (i : T →* X),
    Continuous (⇑i : T → X) →
      ∀ {a b Ψ : X → ENNReal},
        Measurable a →
          Measurable b →
            Measurable Ψ →
              (∀ (t : T) (x : X), Ψ ((i : T → X) t * x) = Ψ x) →
                (∀ (x : X), ∫⁻ (t : T), a ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                  (∀ (x : X), ∫⁻ (t : T), b ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                    ∫⁻ (x : X), Ψ x * a x ∂μ = ∫⁻ (x : X), Ψ x * b x ∂μ := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi a b Ψ ha hb hΨ hinv hA hB
  have him : Measurable (i : T → X) := hi.measurable
  have m1 : Measurable (fun p : X × T => i p.2 * p.1) :=
    (him.comp measurable_snd).mul measurable_fst
  have m2 : Measurable (fun p : X × T => i p.2⁻¹ * p.1) :=
    (him.comp measurable_snd.inv).mul measurable_fst
  have f1 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * a x * b (i t * x)) :=
    ((hΨ.comp measurable_fst).mul (ha.comp measurable_fst)).mul (hb.comp m1)
  have f2 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * b x * a (i t⁻¹ * x)) :=
    ((hΨ.comp measurable_fst).mul (hb.comp measurable_fst)).mul (ha.comp m2)
  have e1 : ∀ x : X, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν = Ψ x * a x := by
    intro x
    have hm : Measurable (fun t : T => b (i t * x)) := hb.comp (him.mul_const x)
    rw [lintegral_const_mul _ hm, hB x, mul_one]
  have e2 : ∀ x : X, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν = Ψ x * b x := by
    intro x
    have hm : Measurable (fun t : T => a (i t⁻¹ * x)) :=
      ha.comp ((him.comp measurable_inv).mul_const x)
    rw [lintegral_const_mul _ hm, lintegral_inv_eq_self (fun t : T => a (i t * x)), hA x, mul_one]
  have e3 : ∀ t : T, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ = ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ := by
    intro t
    rw [← lintegral_mul_left_eq_self (fun x => Ψ x * b x * a (i t⁻¹ * x)) (i t)]
    refine lintegral_congr fun x => ?_
    simp only [hinv, map_inv, inv_mul_cancel_left]
    ring
  calc ∫⁻ x, Ψ x * a x ∂μ = ∫⁻ x, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν ∂μ :=
        lintegral_congr fun x => (e1 x).symm
    _ = ∫⁻ t, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ ∂ν := lintegral_lintegral_swap f1.aemeasurable
    _ = ∫⁻ t, ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ ∂ν := lintegral_congr e3
    _ = ∫⁻ x, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν ∂μ :=
        (lintegral_lintegral_swap f2.aemeasurable).symm
    _ = ∫⁻ x, Ψ x * b x ∂μ := lintegral_congr e2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocConstOfKer
section
theorem UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker :
    ∀ {G M : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : Group M] (χ : G →* M),
    IsOpen (↑χ.ker : Set G) → IsLocallyConstant (⇑χ : G → M) := by
  intro G M _ _ _ _ χ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑χ.ker : Set G),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : χ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalHeightDeterminant
section
noncomputable def UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight.{u_1} :
    {E : Type u_1} → [inst : NormedField E] → {n : ℕ} → GL (Fin n) E → ℝ :=
    fun {E : Type u_1} [NormedField E] {n : ℕ} (g : GL (Fin n) E) ↦
      Max.max (1 : ℝ)
        (↑(Finset.univ.sup fun (p : Fin n × Fin n) ↦
              Max.max ‖(↑g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊ ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) :
          ℝ)

theorem UpperTheory.Reformulated.B.LocalHeightDeterminant.norm_det_le_pow.{u_1} :
    ∀ {R : Type u_1} [inst : NormedField R] [IsUltrametricDist R] {n : ℕ} (g : GL (Fin n) R),
      ‖(↑g : Matrix (Fin n) (Fin n) R).det‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by
  intro R _ _ n g
  have h1 : (1 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := le_max_left _ _
  have h0 : (0 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := zero_le_one.trans h1
  have hent : ∀ i j, ‖(↑g : Matrix (Fin n) (Fin n) R) i j‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := by
    intro i j
    refine le_trans ?_ (le_max_right _ _)
    rw [← coe_nnnorm, NNReal.coe_le_coe]
    exact (le_max_left _ _).trans (Finset.le_sup (f := fun (p : Fin n × Fin n) ↦
      Max.max ‖(↑g : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊
        ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊) (Finset.mem_univ (i, j)))
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 n) ?_
  intro σ _
  have hs : ‖Equiv.Perm.sign σ • ∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      = ‖∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, norm_prod]
  calc ∏ i, ‖(↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      ≤ ∏ _i : Fin n, UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hent _ _)
    _ = UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalQuotientHomExt
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

theorem UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext :
    ∀ (q : ℕ) {R : Type} [inst : CommRing R] {f g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q →+* R},
      (f : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) =
          (g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) →
        f = g := by
  intro q R _ f g h
  have hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ))
    exact RingHom.ext_int _ _
  have hCa : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a) :=
    fun a => RingHom.congr_fun hC a
  have hmul : ∀ m n : ℤ, (LaurentPolynomial.T m : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q) * LaurentPolynomial.T n
      = LaurentPolynomial.T (m + n) := fun m n => (LaurentPolynomial.T_add m n).symm
  have h1 : f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have h2 : g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have hinv : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    calc f (LaurentPolynomial.T (-1))
        = f (LaurentPolynomial.T (-1)) * (g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1))) := by
          rw [h2, mul_one]
      _ = (f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1))) * g (LaurentPolynomial.T (-1)) := by
          rw [← h]; ring
      _ = g (LaurentPolynomial.T (-1)) := by rw [h1, one_mul]
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih => rw [← hmul, map_mul, map_mul, ih, h]
    | pred i ih => rw [sub_eq_add_neg, ← hmul, map_mul, map_mul, ih, hinv]
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr]
  | C_mul_T n a =>
    rw [map_mul, map_mul, hCa, hT]
end

