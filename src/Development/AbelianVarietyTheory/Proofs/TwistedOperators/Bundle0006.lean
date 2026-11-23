module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEach
section
namespace GlobalTheory

theorem expand_pi_of_expand_each {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i) :
    f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  classical
  by_cases hm : ∃ i, m i = 0
  · obtain ⟨i0, hi0⟩ := hm
    have h1 : f g = 0 := by
      rw [hf i0 g hg]
      apply Finset.sum_eq_zero
      intro j _
      exact absurd j.2 (by omega)
    haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by have := (J i0).2; omega⟩
    rw [h1, Finset.univ_eq_empty, Finset.sum_empty]
  push_neg at hm
  let j0 : ∀ i, Fin (m i) := fun i => ⟨0, Nat.pos_of_ne_zero (hm i)⟩
  let T : Finset ι → ∀ i, Finset (Fin (m i)) := fun s i => if i ∈ s then Finset.univ else {j0 i}
  let H : Finset ι → (∀ i, Fin (m i)) → (∀ i, X i) → (∀ i, X i) :=
    fun s J g i => if i ∈ s then k i (J i) else g i
  have hmem : ∀ s (J : ∀ i, Fin (m i)), J ∈ Fintype.piFinset (T s) ↔ ∀ i, i ∉ s → J i = j0 i := by
    intro s J
    rw [Fintype.mem_piFinset]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [T, hi]
  have key : ∀ s : Finset ι, ∀ g : ∀ i, X i, (∀ i, g i ∈ K i) →
      f g = ∑ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hT : T ∅ = fun i => {j0 i} := by funext i; simp [T]
      rw [hT, Fintype.piFinset_singleton, Finset.sum_singleton, Finset.prod_empty, mul_one]
      congr 1
    | insert a s ha ih =>
      intro g hg
      have hHK : ∀ J, ∀ i, H s J g i ∈ K i := by
        intro J i
        simp only [H]
        split_ifs
        exacts [hk _ _, hg i]
      rw [ih g hg]
      have step : ∀ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i)
          = ∑ j, f (H (insert a s) (Function.update J a j) g)
              * ∏ i ∈ insert a s, c i (Function.update J a j i) (g i) := by
        intro J _
        rw [hf a _ (hHK J), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e1 : Function.update (H s J g) a (k a j) = H (insert a s) (Function.update J a j) g := by
          funext i
          by_cases hia : i = a
          · subst hia
            simp [H]
          · simp [H, Function.update_of_ne hia, Finset.mem_insert, hia]
        have e2 : H s J g a = g a := by simp [H, ha]
        rw [e1, e2, Finset.prod_insert ha, Function.update_self]
        have e3 : ∏ i ∈ s, c i (Function.update J a j i) (g i) = ∏ i ∈ s, c i (J i) (g i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have : i ≠ a := fun h => ha (h ▸ hi)
          rw [Function.update_of_ne this]
        rw [e3]
        ring
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_nbij' (fun p => Function.update p.1 a p.2)
        (fun J' => (Function.update J' a (j0 a), J' a)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Finset.mem_coe, hmem]
        intro i hi
        rw [Finset.mem_insert, not_or] at hi
        rw [Function.update_of_ne hi.1]
        exact hp.1 i hi.2
      · intro J' hJ'
        simp only [Finset.mem_coe, hmem] at hJ'
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
          Finset.mem_univ, and_true, hmem]
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp
        · rw [Function.update_of_ne hia]
          exact hJ' i (by simp [hia, hi])
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
        funext i
        by_cases hia : i = a
        · subst hia
          rw [Function.update_self]
          exact (hp.1 _ ha).symm
        · rw [Function.update_of_ne hia]
      · intro J' _
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨J, j⟩ _
        rfl
  rw [key Finset.univ g hg]
  have hTu : T Finset.univ = fun _ => Finset.univ := by funext i; simp [T]
  rw [hTu, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 2
  funext i
  simp [H]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankEqCardMulAndTraceEqZeroOfFreeValues
section
namespace GlobalTheory

theorem trace_eq_zero_of_coord_move {X W : Type} [Fintype X] [DecidableEq X] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (π : X → X) (hπ : ∀ c, π c ≠ c)
    (φ : X → Module.End ℂ W) (M : Module.End ℂ (X → W)) (hM : ∀ f c, M f c = φ c (f (π c))) :
    LinearMap.trace ℂ (X → W) M = 0 := by
  classical

  let b := Pi.basis (fun _ : X => Module.finBasis ℂ W)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hM,
    Pi.single_eq_of_ne (hπ i.1), map_zero, map_zero, Finsupp.zero_apply]

theorem finrank_eq_card_mul_and_trace_eq_zero_of_free_values :
    ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  intro Y X B W _ _ _ _ _ _ cls ev S hcls hinj hcls_eq hfree
  classical
  haveI : Fintype X := Fintype.ofFinite X

  obtain ⟨s, hs⟩ : ∃ s : X → Y, ∀ x, cls (s x) = x :=
    ⟨fun x => (hcls x).choose, fun x => (hcls x).choose_spec⟩

  let Φ : S →ₗ[ℂ] (X → W) := LinearMap.pi (fun x => (ev (s x)).comp S.subtype)
  have hΦ : ∀ (T : S) x, Φ T x = ev (s x) T := fun _ _ => rfl
  have hzero : ∀ T ∈ S, (∀ x, ev (s x) T = 0) → T = 0 := by
    intro T hT h0
    apply hinj
    intro h
    obtain ⟨φ, hφ⟩ := hcls_eq (s (cls h)) h (hs _)
    rw [hφ T hT, h0, map_zero]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    refine Subtype.ext (hzero T T.2 (fun x => ?_))
    have hx := congrFun hT x
    rw [hΦ] at hx
    exact hx
  have hΦsurj : Function.Surjective Φ := by
    intro g
    choose T hTS hTg hT0 using fun x => hfree (s x) (g x)
    refine ⟨⟨∑ x, T x, Submodule.sum_mem _ (fun x _ => hTS x)⟩, ?_⟩
    funext y
    show ev (s y) (∑ x, T x) = g y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single y]
    · exact hTg y
    · intro x _ hxy
      apply hT0
      rw [hs, hs]
      exact Ne.symm hxy
    · intro h
      exact absurd (Finset.mem_univ y) h
  let Ψ : S ≃ₗ[ℂ] (X → W) := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hfd : FiniteDimensional ℂ S := LinearEquiv.finiteDimensional Ψ.symm
  refine ⟨hfd, ?_, ?_⟩
  · rw [Ψ.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  · intro H _ _ e he hrange A t hA ht

    let eS : H ≃ₗ[ℂ] S := (LinearEquiv.ofInjective e he).trans (LinearEquiv.ofEq _ _ hrange)
    let Θ : H ≃ₗ[ℂ] (X → W) := eS.trans Ψ
    have hΘ : ∀ x c, Θ x c = ev (s c) (e x) := fun _ _ => rfl
    haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional Θ.symm
    rw [← LinearMap.trace_conj' A Θ]
    choose φ hφ using fun c => hcls_eq (s (cls (t (s c)))) (t (s c)) (hs _)
    refine trace_eq_zero_of_coord_move (fun c => cls (t (s c)))
      (fun c => by have h := ht (s c); rwa [hs] at h) φ _ ?_
    intro g c
    obtain ⟨x, rfl⟩ := Θ.surjective g
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, hA]
    have hmem : e x ∈ S := by
      rw [← hrange]
      exact LinearMap.mem_range_self e x
    exact hφ c (e x) hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsetFunctionsRecoveredFromValues
section
namespace GlobalTheory

open Module

theorem finset_functions_recovered_from_values {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ))
    (hF : ∀ u ∈ F, u ∈ V) :
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  classical
  set W : Submodule ℂ (X → ℂ) := Submodule.span ℂ (F : Set (X → ℂ)) with hWdef
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_finset ℂ F
  have hWV : W ≤ V := Submodule.span_le.mpr (fun u hu => hF u hu)
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : X → ℂ) x := fun x w => rfl
  set S : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev) with hSdef
  have hcoan : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : X → ℂ) = 0 := by
      funext x
      have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
      simpa [hev] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
    rw [← this, hcoan, Submodule.dualAnnihilator_bot]
  let b := Module.finBasis ℂ W
  have hμ : ∀ i, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord i := by
    intro i
    have : b.coord i ∈ S := by rw [hS]; trivial
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp this
  choose μ hμ using hμ
  set s : Finset X := Finset.univ.biUnion (fun i => (μ i).support) with hsdef
  have hsub : ∀ i, (μ i).support ⊆ s := fun i x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  refine ⟨s,
    fun x => ∑ i, μ i x • ((b i : W) : X → ℂ), ?_, ?_⟩
  · intro x
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hWV (b i).2))
  · intro u hu
    let w : W := ⟨u, Submodule.subset_span hu⟩
    have hw : (w : X → ℂ) = u := rfl
    have hrep : ∀ i, b.repr w i = ∑ x ∈ s, μ i x * u x := by
      intro i
      have h1 : b.repr w i = b.coord i w := rfl
      rw [h1, ← hμ i, Finsupp.sum_of_support_subset (μ i) (hsub i)]
      · simp [LinearMap.sum_apply, hev, hw]
      · intro x _; simp
    calc u = ((∑ i, b.repr w i • b i : W) : X → ℂ) := by rw [b.sum_repr w]
      _ = ∑ i, b.repr w i • ((b i : W) : X → ℂ) := by
          rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
      _ = _ := by
        simp_rw [hrep, Finset.smul_sum, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroup
section
open MeasureTheory

namespace GlobalTheory

open MeasureTheory in
theorem _root_.GlobalTheory.fourier_uniqueness_of_openSubgroup : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  intro H A _ _ _ _ _ μ _ _ χ hs ha0 h0t hadd L hL hsep φ Kc hK hsupp hφL hint
  by_contra hφ
  obtain ⟨t₀, ht₀⟩ : ∃ t, φ t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (funext h)
  have hχne : ∀ a s, χ a s ≠ 0 := fun a s h => by
    have := hs a s (-s)
    rw [add_neg_cancel, ha0, h, zero_mul] at this
    exact one_ne_zero this
  haveI : DiscreteTopology (H ⧸ L) := QuotientAddGroup.discreteTopology hL
  have hTfin : (QuotientAddGroup.mk '' Kc : Set (H ⧸ L)).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  let r : H ⧸ L → H := Quotient.out
  have hr : ∀ t : H, ∃ l ∈ L, r (t : H ⧸ L) = t + l := fun t => by
    obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add L t
    exact ⟨l, l.2, hl⟩
  have hmkr : ∀ q : H ⧸ L, ((r q : H) : H ⧸ L) = q := fun q => Quotient.out_eq q
  have hpre : ∀ q : H ⧸ L, (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) : Set H) =
      (fun h => -r q + h) ⁻¹' (L : Set H) := by
    intro q
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← hmkr q]
    rw [eq_comm]
    exact QuotientAddGroup.eq
  have hmeas : ∀ q : H ⧸ L, μ (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) = μ L := by
    intro q
    rw [hpre, measure_preimage_add]
  have hmset : ∀ q : H ⧸ L, MeasurableSet (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) := by
    intro q
    rw [hpre]
    exact (hL.preimage (continuous_const_add (-r q))).measurableSet
  have hLtop : μ L < ⊤ := by
    have hsub : (QuotientAddGroup.mk ⁻¹' ({(t₀ : H ⧸ L)} : Set (H ⧸ L))) ⊆ Kc := by
      intro x hx
      by_contra hxK
      have hx' : -t₀ + x ∈ L := QuotientAddGroup.eq.mp hx.symm
      have := hφL t₀ _ hx'
      rw [add_neg_cancel_left, hsupp x hxK] at this
      exact ht₀ this.symm
    rw [← hmeas (t₀ : H ⧸ L)]
    exact (measure_mono hsub).trans_lt hK.measure_lt_top
  have hLpos : 0 < μ.real L := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hL.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLtop.ne
  have hχL : ∀ a, (∀ l ∈ L, χ a l = 1) → ∀ t l, l ∈ L → χ a (t + l) = χ a t := by
    intro a ha t l hl
    rw [hs, ha l hl, mul_one]
  have hsum : ∀ a, (∀ l ∈ L, χ a l = 1) →
      ∑ q ∈ hTfin.toFinset, χ a (r q) * φ (r q) = 0 := by
    intro a ha
    have hpt : (fun t => χ a t * φ t) = fun t => ∑ q ∈ hTfin.toFinset,
        (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))).indicator
          (fun _ => χ a (r q) * φ (r q)) t := by
      funext t
      obtain ⟨l, hl, hrt⟩ := hr t
      by_cases htT : (t : H ⧸ L) ∈ (QuotientAddGroup.mk '' Kc : Set (H ⧸ L))
      · rw [Finset.sum_eq_single (t : H ⧸ L)]
        · rw [Set.indicator_of_mem (show t ∈ QuotientAddGroup.mk ⁻¹' ({(t : H ⧸ L)} : Set (H ⧸ L)) from rfl), hrt, hχL a ha t l hl, hφL t l hl]
        · intro q _ hq
          exact Set.indicator_of_notMem (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from
            fun h => hq (Set.mem_singleton_iff.mp h).symm) _
        · intro h
          exact absurd (hTfin.mem_toFinset.mpr htT) h
      · have htK : t ∉ Kc := fun h => htT ⟨t, h, rfl⟩
        rw [hsupp t htK, mul_zero]
        symm
        refine Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem
          (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from fun h => htT ?_) _
        rw [show (t : H ⧸ L) = q from Set.mem_singleton_iff.mp h]
        exact hTfin.mem_toFinset.mp hq
    have hI := hint a ha
    rw [hpt, MeasureTheory.integral_finsetSum] at hI
    · simp_rw [integral_indicator_const _ (hmset _), measureReal_def, hmeas,
        ← measureReal_def] at hI
      rw [← Finset.smul_sum] at hI
      exact (smul_eq_zero.mp hI).resolve_left hLpos.ne'
    · intro q _
      refine IntegrableOn.integrable_indicator ?_ (hmset q)
      exact integrableOn_const (by rw [hmeas]; exact hLtop.ne)
  let A' : AddSubmonoid A :=
    { carrier := {a | ∀ l ∈ L, χ a l = 1}
      zero_mem' := fun l _ => h0t l
      add_mem' := fun {a b} ha hb l hl => by rw [hadd, ha l hl, hb l hl, mul_one] }
  let f : H ⧸ L → (Multiplicative A' →* ℂ) := fun q =>
    { toFun := fun g => χ ((Multiplicative.toAdd g : A') : A) (r q)
      map_one' := h0t _
      map_mul' := fun g g' => hadd _ _ _ }
  have hfinj : Function.Injective f := by
    intro q q' hqq
    by_contra hne
    have hx : r q - r q' ∉ L := by
      intro hx
      apply hne
      rw [← hmkr q, ← hmkr q']
      refine QuotientAddGroup.eq.mpr ?_
      have := L.neg_mem hx
      rwa [neg_sub, ← neg_add_eq_sub] at this
    obtain ⟨a, ha, hax⟩ := hsep _ hx
    have hval := DFunLike.congr_fun hqq (Multiplicative.ofAdd (⟨a, ha⟩ : A'))
    change χ a (r q) = χ a (r q') at hval
    apply hax
    have e : χ a (r q) = χ a (r q - r q') * χ a (r q') := by rw [← hs, sub_add_cancel]
    rw [hval] at e
    exact mul_right_cancel₀ (hχne a (r q')) (by rw [one_mul]; exact e.symm)
  have hli : LinearIndependent ℂ
      (fun q : hTfin.toFinset => (f q : Multiplicative A' → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative A') ℂ).comp (fun q : hTfin.toFinset => f q)
      (hfinj.comp Subtype.val_injective)
  have hzero := Fintype.linearIndependent_iff.mp hli (fun q => φ (r q)) (by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h := hsum _ (Multiplicative.toAdd g).2
    rw [← Finset.sum_coe_sort] at h
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h
    exact mul_comm _ _)
  have ht₀T : (t₀ : H ⧸ L) ∈ hTfin.toFinset :=
    hTfin.mem_toFinset.mpr ⟨t₀, by_contra fun h => ht₀ (hsupp t₀ h), rfl⟩
  have h0 := hzero ⟨_, ht₀T⟩
  obtain ⟨l, hl, hrt⟩ := hr t₀
  change φ (r (t₀ : H ⧸ L)) = 0 at h0
  rw [hrt, hφL t₀ l hl] at h0
  exact ht₀ h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FubiniRightConvolutionBoundedContinuous
section
open MeasureTheory

namespace GlobalTheory

theorem fubini_right_convolution_bounded_continuous
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G)
    (h𝓕 : μ 𝓕 < ⊤) (m : Measure H) [SFinite m] (α : H → ℂ) (hα : Integrable α m)
    (ψ φ : G → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ) (A B : ℝ)
    (hA : ∀ g, ‖ψ g‖ ≤ A) (hB : ∀ g, ‖φ g‖ ≤ B) :
    IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧
    Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧
    ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ
      = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simpa [Measure.restrict_apply_univ] using h𝓕⟩
  set F : G → H → ℂ := fun x h => ψ x * (α h * φ (x * (h : G))) with hFdef
  have hcont : Continuous (fun p : G × H => ψ p.1 * φ (p.1 * (p.2 : G))) :=
    (hψ.comp continuous_fst).mul (hφ.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict 𝓕).prod m) := by
    have h1 : AEStronglyMeasurable (fun p : G × H => ψ p.1 * φ (p.1 * (p.2 : G))) ((μ.restrict 𝓕).prod m) :=
      hcont.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : G × H => α p.2) ((μ.restrict 𝓕).prod m) :=
      hα.aestronglyMeasurable.comp_snd
    refine (h1.mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hFdef, Pi.mul_apply]; ring
  have hbd : Integrable (fun p : G × H => (1 : ℝ) * ((A * B) * ‖α p.2‖)) ((μ.restrict 𝓕).prod m) :=
    (integrable_const (1 : ℝ)).mul_prod (hα.norm.const_mul (A * B))
  have hint : Integrable (Function.uncurry F) ((μ.restrict 𝓕).prod m) := by
    refine hbd.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hFdef, norm_mul, one_mul]
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
    calc ‖ψ p.1‖ * (‖α p.2‖ * ‖φ (p.1 * (p.2 : G))‖) ≤ A * (‖α p.2‖ * B) := by
          gcongr
          · exact hA _
          · exact hB _
      _ = A * B * ‖α p.2‖ := by ring
  have hL : ∀ x, ∫ h, F x h ∂m = ψ x * ∫ h, α h * φ (x * (h : G)) ∂m := fun x =>
    integral_const_mul _ _
  have hR : ∀ h : H, ∫ x in 𝓕, F x h ∂μ = α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ := by
    intro h
    rw [← integral_const_mul]
    congr 1; funext x; simp only [hFdef]; ring
  refine ⟨?_, ?_, ?_⟩
  · have := hint.integral_prod_left
    exact (by simpa [Function.uncurry, hL] using this : Integrable _ (μ.restrict 𝓕))
  · have := hint.integral_prod_right
    simpa [Function.uncurry, hR] using this
  · have := integral_integral_swap hint
    simpa [hL, hR] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransport
section
namespace GlobalTheory

theorem hasSum_quotient_transport :
    ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H),
      (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ,
      HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  intro G H _ _ e K K' hK f hf s hs
  have hrel : ∀ a b : G, (QuotientGroup.leftRel K) a b ↔ (QuotientGroup.leftRel K') (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK, map_mul, map_inv]

  let ψ : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv hrel
  have hψ : ∀ q : G ⧸ K, f (e.symm (ψ q).out) = f q.out := by
    intro q
    have h2 : ψ q = QuotientGroup.mk (e q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h3 : (e q.out)⁻¹ * (ψ q).out ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', h2]
    have h4 : e.symm (ψ q).out = q.out * e.symm ((e q.out)⁻¹ * (ψ q).out) := by
      rw [map_mul, map_inv, MulEquiv.symm_apply_apply, mul_inv_cancel_left]
    rw [h4, hf _ _ ((hK _).2 (by simpa using h3))]
  have hcomp : (fun a : G ⧸ K => f a.out) = (fun b : H ⧸ K' => f (e.symm b.out)) ∘ ψ := by
    funext q
    exact (hψ q).symm
  rw [hcomp]
  exact (Equiv.hasSum_iff ψ).2 hs

end GlobalTheory
end

