module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.BddAboveOfSpanningPeriods
section
namespace GlobalTheory

theorem bddAbove_of_spanning_periods (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (g : R → ℝ) (hg : Continuous g) (S : Set R)
    (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) :
    ∃ C : ℝ, ∀ x, g x ≤ C := by
  classical
  let P : AddSubgroup R :=
    { carrier := {p | ∀ x, g (x + p) = g x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by
        rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        rw [← this]; simp }
  have hP : Submodule.span ℝ (P : Set R) = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    intro s hs
    obtain ⟨N, hN, h⟩ := hper s hs
    have h1 : (N : ℝ) • s ∈ Submodule.span ℝ (P : Set R) := Submodule.subset_span h
    have h2 := Submodule.smul_mem _ ((N : ℝ)⁻¹) h1
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at h2
  obtain ⟨t, htP, hspan, hli⟩ := exists_linearIndependent ℝ (P : Set R)
  have hfin : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b : Module.Basis t ℝ R := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, hP])
  have hb : Submodule.span ℤ (Set.range b) ≤ AddSubgroup.toIntSubmodule P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i = (i : R) := by simp [b]
    rw [this]
    exact htP i.2
  have hK : IsCompact (Metric.closedBall (0 : R) (∑ i, ‖b i‖)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hfl : ((ZSpan.floor b x : R)) ∈ P := hb (ZSpan.floor b x).2
  have hx : g x = g (ZSpan.fract b x) := by
    have := hfl (ZSpan.fract b x)
    rw [← this, ZSpan.fract_apply]; simp
  rw [hx]
  apply hC
  exact ⟨_, by simpa using ZSpan.norm_fract_le b x, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHyperbolicCompletion
section
namespace GlobalTheory

open Module


open Module in
theorem _root_.GlobalTheory.exists_hyperbolic_completion :
    ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → h.Nondegenerate → ∀ (W : Submodule E V), (∀ x ∈ W, (∀ y ∈ W, h x y = 0) → x = 0) → ∀ (i : ℕ) (e : Fin i → V), LinearIndependent E e → (∀ a b, h (e a) (e b) = 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0) → Module.finrank E W + 2 * i = Module.finrank E V → ∃ f : Fin i → V, (∀ a b, h (f a) (f b) = 0) ∧ (∀ a b, h (f a) (e b) = if a = b then 1 else 0) ∧ (∀ a, ∀ x ∈ W, h x (f a) = 0) ∧ W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ := by
  intro E V _ _ _ _ _ _ h hs hn W hW i e he hee heW hdim
  set m := finrank E W with hm
  let b := Module.finBasis E W
  let w : Fin m → V := fun j => (b j : V)
  have hwW : ∀ j, w j ∈ W := fun j => (b j).2
  let u : Fin i ⊕ Fin m → V := Sum.elim e w
  have hw : LinearIndependent E w := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hu : LinearIndependent E u := by
    refine he.sum_type hw ?_
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hxW : x ∈ W := (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwW j)) hx2
    refine hW x hxW fun y hy => ?_
    have hle : Submodule.span E (Set.range e) ≤ LinearMap.ker (h y) :=
      Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact heW a y hy)
    rw [← hs.eq, show h y x = 0 from hle hx1, map_zero]
  let L : V →ₗ[E] (Fin i ⊕ Fin m → E) := LinearMap.pi fun k => h (u k)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨μ, hμ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hz : ∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k = 0 := by
      refine hn.1 _ fun y => ?_
      have h0 : μ (L y) = 0 := hle (LinearMap.mem_range_self L y)
      rw [LinearMap.pi_apply_eq_sum_univ] at h0
      have h1 : h (∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k) y = ∑ k, L y k • μ fun j => if k = j then (1 : E) else 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, L, LinearMap.pi_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1, h0]
    have hc0 : ∀ k, μ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
      have := Fintype.linearIndependent_iff.mp hu _ hz k
      simpa using this
    apply hμ
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [hc0, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]
  choose g hg using fun a : Fin i => hL fun k => if k = Sum.inl a then (1 : E) else 0
  have hge : ∀ a b, h (e b) (g a) = if b = a then 1 else 0 := fun a b => by
    have := congrFun (hg a) (Sum.inl b)
    simpa [L, u] using this
  have hgw : ∀ a j, h (w j) (g a) = 0 := fun a j => by
    have := congrFun (hg a) (Sum.inr j)
    simpa [L, u] using this
  have hgW : ∀ a, ∀ x ∈ W, h x (g a) = 0 := by
    intro a x hx
    have hx' : x = ∑ j, b.repr ⟨x, hx⟩ j • w j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hx']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hgw]
  set f : Fin i → V := fun a => g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c with hf
  have hfa : ∀ a, f a = g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c := fun a => rfl
  have hfe : ∀ a b, h (e b) (f a) = if b = a then 1 else 0 := by
    intro a b
    rw [hfa]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sub, map_sum, hee, hge]
  have hfe' : ∀ a b, h (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hs.eq, hfe]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hfW : ∀ a, ∀ x ∈ W, h x (f a) = 0 := by
    intro a x hx
    rw [hfa]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sub, map_sum, hgW a x hx, heW _ x hx]
  have hff : ∀ a b, h (f a) (f b) = 0 := by
    intro a b
    have hs' : starRingEnd E (h (g b) (g a)) = h (g a) (g b) := hs.eq (g b) (g a)
    have h1 : h (f a) (f b) = h (f a) (g b) - 2⁻¹ * h (g a) (g b) := by
      conv_lhs => rw [hfa b]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sub, map_sum, hfe']
    rw [h1, hfa a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sub, map_sum, hge, hs', map_ofNat]
    ring
  let v : Fin i ⊕ (Fin i ⊕ Fin m) → V := Sum.elim f u
  have hu0 : ∀ c k, h (e c) (u k) = 0 := by
    intro c k
    rcases k with d | j
    · exact hee c d
    · show h (e c) (w j) = 0
      rw [← hs.eq, heW c _ (hwW j)]
      simp
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro γ hγ
    simp only [v] at hγ
    rw [Fintype.sum_sum_type] at hγ
    simp only [Sum.elim_inl, Sum.elim_inr] at hγ
    have hfst : ∀ a, γ (Sum.inl a) = 0 := by
      intro a
      have := congrArg (h (e a)) hγ
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_add (f := _), map_sum, hfe, hu0] using this
    have hrest : ∑ k, γ (Sum.inr k) • u k = 0 := by simpa [hfst] using hγ
    intro k
    rcases k with a | k
    · exact hfst a
    · exact Fintype.linearIndependent_iff.mp hu _ hrest k
  have hspan : Submodule.span E (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by simp; omega)
  refine ⟨f, hff, hfe', hfW, ?_⟩
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rcases k with a | c | j
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨c, rfl⟩))
  · exact Submodule.mem_sup_left (hwW j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei
section
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory

theorem exists_isAddHaarMeasure_isAddFundamentalDomain_preimage :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H), Continuous e → Continuous e.symm → ∀ (Γ : AddSubgroup G) (Λ : AddSubgroup H), (∀ x, e x ∈ Λ ↔ x ∈ Γ) → ∀ (μ : Measure H) (𝓕 : Set H), μ.IsAddHaarMeasure → IsAddFundamentalDomain Λ 𝓕 μ → ∃ ν : Measure G, ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) ν ∧ ∀ φ : H → ℝ, ∫ w in e ⁻¹' 𝓕, φ (e w) ∂ν = ∫ w in 𝓕, φ w ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ e he hes Γ Λ hΓ μ 𝓕 hμ h𝓕
  let m : G ≃ᵐ H :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  refine ⟨μ.map e.symm, AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he), ?_, ?_⟩
  · let f : Λ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro φ
    exact hmp.setIntegral_preimage_emb m.measurableEmbedding φ 𝓕

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNatMulMemRingOfIntegers
section
namespace GlobalTheory.NatMulMemRingOfIntegers

theorem exists_nat_mul_mem_ringOfIntegers {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ (k : ℕ), 0 < k ∧ ∃ (r : NumberField.RingOfIntegers E), (r : E) = (k : E) * e := by
  have h0 : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have halg : IsAlgebraic ℤ e := (IsAlgebraic.of_finite ℚ e).restrictScalars ℤ
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with hy | hy
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨(y : E) * e, (mem_integralClosure_iff ℤ E).mpr hint⟩, ?_⟩
    show (y : E) * e = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_natCast]
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨-((y : E) * e), (mem_integralClosure_iff ℤ E).mpr hint.neg⟩, ?_⟩
    show -((y : E) * e) = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_neg, Int.cast_natCast]
    ring

end GlobalTheory.NatMulMemRingOfIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
section
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.AdeleDiscrete

theorem exists_nhds_zero_principal_eq_zero : ∀ (F : Type) [Field F] [NumberField F], ∃ U ∈ nhds (0 : AdeleRing (𝓞 F) F), ∀ x : F, algebraMap F (AdeleRing (𝓞 F) F) x ∈ U → x = 0 := by
  intro F _ _
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (0 : v.Completion) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  refine ⟨_, (hU.prod hV).mem_nhds ⟨fun v _ => Metric.mem_ball_self one_pos,
    fun v => zero_mem _⟩, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by
    have h := h2 v
    rw [AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  have hlt : ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F a) < 1 := fun w => by
    have h := h1 w trivial
    rw [mem_ball_zero_iff, AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.norm_coe] at h
    exact h
  by_contra h0
  have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

end GlobalTheory.AdeleDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsProdXSubCOfMonic
section
open Polynomial

namespace GlobalTheory.MonicRootsProduct

theorem exists_prod_X_sub_C_of_monic (p : ℂ[X]) (hm : p.Monic) :
    ∃ r : Fin p.natDegree → ℂ, ∏ j, (X - C (r j)) = p := by
  classical
  have hc : p.roots.toList.length = p.natDegree := by
    rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  refine ⟨fun j => p.roots.toList[(j : ℕ)]'(by rw [hc]; exact j.2), ?_⟩
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    IsAlgClosed.card_roots_eq_natDegree
  rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe,
    ← Fin.prod_univ_fun_getElem] at hprod
  exact (Fintype.prod_equiv (finCongr hc.symm) _ _ (fun j => rfl)).trans hprod

theorem exists_roots {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ, ∏ j : Fin δ, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  have hdeg := Polynomial.degree_sum_fin_lt c
  have hmon : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).Monic := Polynomial.monic_X_pow_add hdeg
  have hd : (X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ)).natDegree = δ := by
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  obtain ⟨r, hr⟩ := exists_prod_X_sub_C_of_monic _ hmon
  exact ⟨fun j => r (Fin.cast hd.symm j),
    (Fintype.prod_equiv (finCongr hd.symm) _ _ (fun j => rfl)).trans hr⟩

end GlobalTheory.MonicRootsProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpNegMulSqrtDivPowLe
section
namespace GlobalTheory

theorem exp_neg_mul_sqrt_div_pow_le (a : ℝ) (D : ℕ) (ha : 0 < a) :
    ∃ C : ℝ, ∀ m : ℕ, Real.exp (-(a * m * ((m : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) /
      (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ D ≤ C * Real.sqrt (((m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  refine ⟨Real.exp a * ((D + 1).factorial : ℝ) / a ^ (D + 1), fun m => ?_⟩
  set s : ℝ := (m : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by rw [hs]; have := m.cast_nonneg (α := ℝ); linarith
  have hs0 : 0 < s := by linarith
  set x : ℝ := s ^ (-(1 / 2 : ℝ)) with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hs0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
  have hx2 : x ^ 2 * s = 1 := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  have hmx : (m : ℝ) * x = x⁻¹ - x := by
    have : (m : ℝ) = s - 1 := by rw [hs]; ring
    rw [this]; field_simp; nlinarith [hx2]
  set n := D + 1 with hn
  have hK : 0 < Real.exp a * (n.factorial : ℝ) / a ^ n := by positivity

  have hpow := Real.pow_div_factorial_le_exp (a / x) (by positivity) n
  have hexp : Real.exp (-(a * m * x)) * Real.exp (a / x) ≤ Real.exp a := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : a * m * x = a * (x⁻¹ - x) := by rw [mul_assoc, hmx]
    rw [this, div_eq_mul_inv]
    nlinarith
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have h1 : Real.exp (-(a * m * x)) * ((a / x) ^ n / n.factorial) ≤ Real.exp a :=
    le_trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hexp
  have h2 : Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_pow, div_div, mul_div_assoc', div_le_iff₀ (by positivity)] at h1
    have e : Real.exp a * (n.factorial : ℝ) / a ^ n * x * x ^ D
        = Real.exp a * (x ^ n * n.factorial) / a ^ n := by
      rw [hn, pow_succ]; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [h1]

  have hxs : x ≤ Real.sqrt x := by
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0.le).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
  calc Real.exp (-(a * m * x)) / x ^ D ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * x := h2
    _ ≤ Real.exp a * (n.factorial : ℝ) / a ^ n * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hxs hK.le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.Imports
section
namespace GlobalTheory.PolynomialCoeffEq

open Module

theorem coeff_eq {R : Type} [AddCommGroup R] [Module ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) {n : ℕ} (v : Basis (Fin n) ℝ R)
    (hv : ∀ i j, i ≠ j → g (v i) (v j) = 0) (x : R) (k : Fin n) :
    g x (v k) = v.repr x k * g (v k) (v k) := by
  conv_lhs => rw [← v.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · intro i _ hik
    rw [hv i k hik, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem main : ∀ {R : Type} [inst : AddCommGroup R] [inst_1 : Module ℝ R] [FiniteDimensional ℝ R] (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ (u v : R), ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) v = ((g : R → R →ₗ[ℝ] ℝ) v : R → ℝ) u) → (∀ (u : R), u ≠ (0 : R) → (0 : ℝ) < ((g : R → R →ₗ[ℝ] ℝ) u : R → ℝ) u) → ∃ (n : ℕ) (e : Fin n → R), ∀ (x : R), ∑ k : Fin n, ((g : R → R →ₗ[ℝ] ℝ) x : R → ℝ) (e k) • e k = x := by
  intro R _ _ _ g hsym hpos
  have h2 : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := g) ⟨hsym⟩
  have hv' : ∀ i j, i ≠ j → g (v i) (v j) = 0 := LinearMap.BilinForm.iIsOrtho_def.mp hv
  have hpos' : ∀ k, 0 < g (v k) (v k) := fun k => hpos _ (v.ne_zero k)
  refine ⟨_, fun k => (Real.sqrt (g (v k) (v k)))⁻¹ • v k, fun x => ?_⟩
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, coeff_eq g v hv' x k, smul_smul]
  congr 1
  have hs := Real.mul_self_sqrt (hpos' k).le
  have he : (Real.sqrt (g (v k) (v k)))⁻¹ * (v.repr x k * g (v k) (v k)) *
      (Real.sqrt (g (v k) (v k)))⁻¹ =
      v.repr x k * (g (v k) (v k) * (Real.sqrt (g (v k) (v k)) * Real.sqrt (g (v k) (v k)))⁻¹) := by
    ring
  rw [he, hs, mul_inv_cancel₀ (hpos' k).ne', mul_one]

end GlobalTheory.PolynomialCoeffEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
section
open NumberField IsDedekindDomain MeasureTheory
open scoped Pointwise

namespace GlobalTheory


open Pointwise in
theorem integrableOn_fundamentalDomain_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  intro G _ _ _ _ _ Γ _ K hK hcov μ hμ 𝓕 h𝓕 f hf hinv
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ g, ‖f g‖ ≤ C := by
    intro g
    obtain ⟨γ, hγ, hγg⟩ := hcov g
    rw [← hinv γ hγ g]
    exact hC _ hγg
  have hcover : 𝓕 ⊆ ⋃ γ : Γ, (γ • K ∩ 𝓕) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    refine Set.mem_iUnion.mpr ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hγx
  have hle : μ 𝓕 ≤ μ K :=
    calc μ 𝓕 ≤ μ (⋃ γ : Γ, (γ • K ∩ 𝓕)) := measure_mono hcover
      _ ≤ ∑' γ : Γ, μ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ K := (h𝓕.measure_eq_tsum K).symm
  exact Measure.integrableOn_of_bounded (hle.trans_lt hK.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) (ae_of_all _ hbound)

end GlobalTheory
end

