module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AvPrimeDimOne
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem av_no_two_chain {S : Type*} [CommRing S] [IsDomain S] {A B : Ideal S} [A.IsPrime]
    [B.IsPrime] (h1 : ⊥ < A) (h2 : A < B) (hB : B.height ≤ 1) : False := by
  have hA : 1 ≤ A.height := le_add_self.trans (Ideal.height_add_one_le_of_lt_of_isPrime h1)
  have hB₂ : (2 : ℕ∞) ≤ B.height := calc
    (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ A.height + 1 := add_le_add hA le_rfl
    _ ≤ B.height := Ideal.height_add_one_le_of_lt_of_isPrime h2
  exact (by norm_num : ¬ (2 : ℕ∞) ≤ 1) (hB₂.trans hB)

theorem av_key {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] (g : S)
    (hg : g ≠ 0) (H : ∀ Q : Ideal S, Q.IsPrime → Q ≠ ⊥ → g ∈ Q) (Q : Ideal S) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : Q.IsMaximal := by
  classical
  by_contra hQm
  set m := IsLocalRing.maximalIdeal S with hm_def
  have hQlt : Q < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top)
    (fun h => hQm (h ▸ IsLocalRing.maximalIdeal.isMaximal S))
  haveI : (Ideal.span {g}).IsPrincipal := ⟨⟨g, rfl⟩⟩
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S (Ideal.span {g})

  have hmin : ∀ P ∈ (Ideal.span {g}).minimalPrimes, P.IsPrime ∧ P ≠ ⊥ ∧ P.height ≤ 1 := by
    intro P hP
    refine ⟨hP.1.1, ?_, ?_⟩
    · intro h
      apply hg
      have := hP.1.2 (Ideal.mem_span_singleton_self g)
      rw [h] at this
      exact (Submodule.mem_bot S).mp this
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP

  have hbelow : ∀ P' : Ideal S, P'.IsPrime → P' ≠ ⊥ →
      ∃ P ∈ (Ideal.span {g}).minimalPrimes, P ≤ P' := by
    intro P' hP' h0
    exact Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr (H P' hP' h0))

  have hm_not : ∀ P ∈ (Ideal.span {g}).minimalPrimes, ¬ m ≤ P := by
    intro P hP hmP
    obtain ⟨P0, hP0, hP0Q⟩ := hbelow Q hQ hQ0
    obtain ⟨hPp, -, hPh⟩ := hmin P hP
    obtain ⟨hP0p, hP00, -⟩ := hmin P0 hP0
    haveI := hPp
    haveI := hP0p
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00)
      (lt_of_le_of_lt hP0Q (lt_of_lt_of_le hQlt hmP)) hPh

  obtain ⟨x, hxm, hxP⟩ : ∃ x ∈ m, ∀ P ∈ (Ideal.span {g}).minimalPrimes, x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hsub : (m : Set S) ⊆ ⋃ P ∈ (hfin.toFinset : Set (Ideal S)), ((id P : Ideal S) : Set S) := by
      intro y hy
      obtain ⟨P, hP, hyP⟩ := hcon y hy
      exact Set.mem_iUnion₂.mpr ⟨P, by simpa using hP, hyP⟩
    obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun P hP _ _ => (hmin P (by simpa using hP)).1)).mp hsub
    exact hm_not P (by simpa using hP) hle
  obtain ⟨P0, hP0, -⟩ := hbelow Q hQ hQ0
  have hx0 : x ≠ 0 := by
    intro h
    apply hxP P0 hP0
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨P', hP', -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem m).mpr hxm)
  haveI := hP'.1.1
  have hxP' : x ∈ P' := hP'.1.2 (Ideal.mem_span_singleton_self x)
  have hP'0 : P' ≠ ⊥ := by
    intro h
    rw [h] at hxP'
    exact hx0 ((Submodule.mem_bot S).mp hxP')
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have hP'h : P'.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P' hP'
  obtain ⟨P, hP, hPP'⟩ := hbelow P' hP'.1.1 hP'0
  obtain ⟨hPp, hP00, -⟩ := hmin P hP
  rcases lt_or_eq_of_le hPP' with hlt | heq
  · haveI := hPp
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00) hlt hP'h
  · apply hxP P hP
    rw [heq]
    exact hxP'

theorem av_prime_dim_one {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : 1 ≤ ringKrullDim R) (h : R) (hh : h ≠ 0) :
    ∃ p : Ideal R, p.IsPrime ∧ ringKrullDim (R ⧸ p) = 1 ∧ h ∉ p := by
  classical
  set m := IsLocalRing.maximalIdeal R with hm_def
  have hm0 : m ≠ ⊥ := by
    intro e
    have hF : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr e
    rw [ringKrullDim_eq_zero_of_isField hF] at hdim
    exact absurd hdim (by norm_num)

  obtain ⟨p, ⟨hpP, hhp, hpm⟩, hpmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ h ∉ q ∧ q ≠ m}
    ⟨⊥, Ideal.isPrime_bot, fun h' => hh ((Submodule.mem_bot R).mp h'), fun e => hm0 e.symm⟩
  haveI := hpP
  refine ⟨p, hpP, ?_, hhp⟩
  have hplt : p < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpP.ne_top) hpm
  obtain ⟨y, hym, hyp⟩ := SetLike.exists_of_lt hplt
  set f := Ideal.Quotient.mk p with hf_def
  haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
  have hfz : ∀ a : R, f a = 0 ↔ a ∈ p := fun a => Ideal.Quotient.eq_zero_iff_mem
  have hg0 : f (h * y) ≠ 0 := by
    rw [Ne, hfz]
    intro hm'
    rcases hpP.mem_or_mem hm' with h1 | h1
    · exact hhp h1
    · exact hyp h1

  have hall : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → f (h * y) ∈ Q := by
    intro Q hQ hQ0
    haveI := hQ
    have hq : (Q.comap f).IsPrime := inferInstance
    have hpq : p < Q.comap f := by
      refine lt_of_le_of_ne (fun a ha => ?_) (fun e => hQ0 ?_)
      · show f a ∈ Q
        rw [(hfz a).mpr ha]
        exact Q.zero_mem
      · rw [eq_bot_iff]
        intro z hz
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
        have ha : a ∈ Q.comap f := hz
        rw [← e] at ha
        exact (Submodule.mem_bot _).mpr ((hfz a).mpr ha)
    show h * y ∈ Q.comap f
    by_cases hhq : h ∈ Q.comap f
    · exact Ideal.mul_mem_right _ _ hhq
    · have hqm : Q.comap f = m := by
        by_contra hne
        exact hpmax _ ⟨hq, hhq, hne⟩ hpq
      rw [hqm]
      exact Ideal.mul_mem_left _ _ hym
  have hmax : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → Q.IsMaximal :=
    fun Q hQ hQ0 => av_key (f (h * y)) hg0 hall Q hQ hQ0
  apply le_antisymm
  · unfold ringKrullDim Order.krullDim
    refine iSup_le fun s => ?_
    by_contra hlt
    have h2 : 2 ≤ s.length := by
      by_contra h2
      apply hlt
      have : s.length ≤ 1 := by omega
      exact_mod_cast this
    have a01 : s ⟨0, by omega⟩ < s ⟨1, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    have a12 : s ⟨1, by omega⟩ < s ⟨2, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at a01 a12
    have hne : (s ⟨1, by omega⟩).asIdeal ≠ ⊥ := fun e => not_lt_bot (e ▸ a01)
    have hM := hmax _ (s ⟨1, by omega⟩).isPrime hne
    exact a12.ne (hM.eq_of_le (s ⟨2, by omega⟩).isPrime.ne_top a12.le)
  · haveI hMp : (m.map f).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hplt.le)
    have hlt : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (R ⧸ p)) < ⟨m.map f, hMp⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine bot_lt_iff_ne_bot.mpr fun e => ?_
      have hy : f y ∈ m.map f := Ideal.mem_map_of_mem f hym
      have e' : m.map f = ⊥ := e
      rw [e'] at hy
      exact hyp ((hfz y).mp ((Submodule.mem_bot _).mp hy))
    have e1 := Order.height_add_one_le hlt
    calc (1 : WithBot ℕ∞) ≤ ((Order.height (⟨m.map f, hMp⟩ : PrimeSpectrum (R ⧸ p)) : ℕ∞) :
          WithBot ℕ∞) := by exact_mod_cast (le_add_self.trans e1)
      _ ≤ ringKrullDim (R ⧸ p) := Order.height_le_krullDim _

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BinomRatio
section
namespace ReciprocityTheory.ChartRestriction.G.T0

private theorem choose_succ_mul_succ_eq_choose_mul_sub (n k : ℕ) (h : k ≤ n) :
    ((n.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((n.choose k : ℕ) : ℝ) * ((n : ℝ) - k) := by
  have h1 := Nat.choose_succ_right_eq n k
  have h2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub h
  rw [← h2]
  exact_mod_cast h1

theorem sub_mul_choose_le_mul_choose (T D : ℕ) (hT : D * (2 * D + 7) ≤ T) :
    ∀ k ≤ D, ((T : ℝ) - k * (2 * D + 7)) * (((T + 2 * D + 6).choose k : ℕ) : ℝ) ≤
      (T : ℝ) * (((T - 1).choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have h7 : 7 * D ≤ T := by nlinarith [Nat.zero_le (D * D)]
    have hA := choose_succ_mul_succ_eq_choose_mul_sub (T + 2 * D + 6) k (by omega)
    have hB := choose_succ_mul_succ_eq_choose_mul_sub (T - 1) k (by omega)
    have ha : ((T + 2 * D + 6 : ℕ) : ℝ) = (T : ℝ) + 2 * D + 6 := by push_cast; ring
    have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [ha] at hA
    rw [hT1] at hB
    have hkT : ((k : ℝ) + 2) ≤ T := by exact_mod_cast (show k + 2 ≤ T by omega)
    have hb : (0 : ℝ) ≤ (T : ℝ) - 1 - k := by linarith
    have hCA : (0 : ℝ) ≤ (((T + 2 * D + 6).choose k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiff : (0 : ℝ) ≤ ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
        ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) := by
      have e : ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) =
          (2 * (D : ℝ) + 7) * ((k : ℝ) + 1) * (2 * (D : ℝ) + 6) := by ring
      rw [e]; positivity
    have P := mul_le_mul_of_nonneg_right ih hb
    have Q := mul_nonneg hCA hdiff
    have key : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
        (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ≤
        (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      have e1 : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          ((((T + 2 * D + 6).choose k : ℕ) : ℝ) * ((T : ℝ) + 2 * D + 6 - k)) := by
        linear_combination ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * hA
      have e2 : (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          (T : ℝ) * ((((T - 1).choose k : ℕ) : ℝ) * ((T : ℝ) - 1 - k)) := by
        linear_combination (T : ℝ) * hB
      rw [e1, e2]
      nlinarith [P, Q]
    push_cast
    exact le_of_mul_le_mul_right key hk1

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FlatLength
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped TensorProduct

private theorem length_baseChange_of_isSimpleModule {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (X : Type*) [AddCommGroup X] [Module R X] [hX : IsSimpleModule R X] :
    Module.length S (S ⊗[R] X) = Module.length R X := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hX
  have hIm : I.map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.eq_maximalIdeal hI, hm]
  have e2 : (S ⊗[R] X) ≃ₗ[S] (S ⧸ IsLocalRing.maximalIdeal S) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.trans
        (Submodule.quotEquivOfEq _ _ hIm))
  have : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  have : IsSimpleModule S (S ⊗[R] X) := IsSimpleModule.congr e2
  rw [Module.length_eq_one, Module.length_eq_one]

private theorem length_baseChange_of_submodule_simple_quotient {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) [IsSimpleModule R (M ⧸ N)]
    (ih : Module.length S (S ⊗[R] N) = Module.length R N) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  have hinj : Function.Injective (N.subtype.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
  have hsurj : Function.Surjective (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S N.mkQ_surjective
  have hex : Function.Exact (N.subtype.baseChange S) (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact S (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
  rw [Module.length_eq_add_of_exact _ _ hinj hsurj hex,
    Module.length_eq_add_of_exact _ _ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N),
    ih, length_baseChange_of_isSimpleModule hm (M ⧸ N)]

private theorem length_baseChange_of_isFiniteLength {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  induction h with
  | @of_subsingleton M' _ _ _ =>
    have : Subsingleton (S ⊗[R] M') := by
      have h0 : ∀ z : S ⊗[R] M', z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul s m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact ⟨fun a b => by rw [h0 a, h0 b]⟩
    rw [Module.length_eq_zero, Module.length_eq_zero]
  | of_simple_quotient _ ih =>
    exact length_baseChange_of_submodule_simple_quotient hm _ ih

private theorem length_le_length_baseChange_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length R Q ≤ Module.length S (S ⊗[R] Q) := by
  have hmono : ∀ N N' : Submodule R Q, N ≤ N' →
      LinearMap.range (N.subtype.baseChange S) ≤ LinearMap.range (N'.subtype.baseChange S) := by
    intro N N' h x hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨(Submodule.inclusion h).baseChange S z, ?_⟩
    rw [← Submodule.subtype_comp_inclusion _ _ h, LinearMap.baseChange_comp, LinearMap.comp_apply]
  have hrefl : ∀ N N' : Submodule R Q,
      LinearMap.range (N'.subtype.baseChange S) ≤ LinearMap.range (N.subtype.baseChange S) →
        N' ≤ N := by
    intro N N' h
    have hz : ∀ w : S ⊗[R] N, (N.mkQ.baseChange S) ((N.subtype.baseChange S) w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul s n =>
        have hn : N.mkQ (N.subtype n) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr n.2
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hn, TensorProduct.tmul_zero]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
    have h0 : (N.mkQ ∘ₗ N'.subtype).lTensor S = 0 := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨w, hw⟩ :=
        LinearMap.mem_range.mp (h (LinearMap.mem_range_self (N'.subtype.baseChange S) z))
      have hb : ((N.mkQ ∘ₗ N'.subtype).baseChange S) z = 0 := by
        rw [LinearMap.baseChange_comp, LinearMap.comp_apply, ← hw, hz]
      rw [LinearMap.zero_apply]
      rwa [LinearMap.baseChange_eq_ltensor] at hb
    have hf : N.mkQ ∘ₗ N'.subtype = 0 :=
      (Module.FaithfullyFlat.zero_iff_lTensor_zero R S _).mpr h0
    intro x hx
    have hx0 := LinearMap.congr_fun hf ⟨x, hx⟩
    simpa using hx0
  have hsm : StrictMono (fun N : Submodule R Q => LinearMap.range (N.subtype.baseChange S)) :=
    fun N N' hlt => lt_of_le_of_ne (hmono N N' hlt.le)
      (fun heq => hlt.ne (le_antisymm hlt.le (hrefl N N' heq.ge)))
  have h1 : (Module.length R Q : WithBot ℕ∞) ≤ (Module.length S (S ⊗[R] Q) : WithBot ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_le_of_strictMono _ hsm
  exact WithBot.coe_le_coe.mp h1

theorem length_baseChange_eq {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length S (S ⊗[R] Q) = Module.length R Q := by
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hge := length_le_length_baseChange_of_faithfullyFlat (R := R) (S := S) Q
  by_cases hQ : Module.length R Q = ⊤
  · rw [hQ] at hge ⊢
    exact top_le_iff.mp hge
  · exact length_baseChange_of_isFiniteLength hm (Module.length_ne_top_iff.mp hQ)

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped BigOperators ComplexOrder
open Finset Matrix

theorem psd_det_re_le_one_of_diag (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef)
    (hd : ∀ c, H c c = 1) : H.det.re ≤ 1 := by
  have hHerm := hH.isHermitian
  have htr : ∑ i, hHerm.eigenvalues i = N := by
    have h := hHerm.trace_eq_sum_eigenvalues
    have h2 : H.trace = N := by simp [Matrix.trace, hd]
    rw [h2] at h
    have h4 := congrArg (RCLike.re : ℂ → ℝ) h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, RCLike.ofReal_re, RCLike.natCast_re] at h4
    linarith
  have hre : H.det.re = ∏ i, hHerm.eigenvalues i := by
    rw [hHerm.det_eq_prod_eigenvalues]
    first
      | (norm_cast)
      | simp [← Complex.ofReal_prod]
  rw [hre]
  calc ∏ i, hHerm.eigenvalues i ≤ ∏ i, Real.exp (hHerm.eigenvalues i - 1) :=
        Finset.prod_le_prod₀ (fun i _ => hH.eigenvalues_nonneg i)
          (fun i _ => by linarith [Real.add_one_le_exp (hHerm.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hHerm.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by simp [Finset.sum_sub_distrib, htr]

theorem psd_det_re_le_prod_diag (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) :
    G.det.re ≤ ∏ c, (G c c).re := by
  classical
  have hdiag : ∀ c, G c c = ((G c c).re : ℂ) := fun c =>
    (Complex.conj_eq_iff_re.mp (by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hG.1 c) c)).symm
  have hnn : ∀ c, 0 ≤ (G c c).re := fun c => (Complex.nonneg_iff.mp (hG.diag_nonneg (i := c))).1
  by_cases hz : ∃ c, (G c c).re = 0
  · obtain ⟨c, hc⟩ := hz
    have hcol : G *ᵥ Pi.single c 1 = 0 := by
      rw [← hG.dotProduct_mulVec_zero_iff]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hdiag c, hc]
      simp
    have hdet : G.det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero c
      intro i
      have h := congrFun hcol i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
    rw [hdet, Complex.zero_re]
    exact Finset.prod_nonneg fun c _ => hnn c
  · push_neg at hz
    have hpos : ∀ c, 0 < (G c c).re := fun c => lt_of_le_of_ne (hnn c) (Ne.symm (hz c))
    set d : Fin N → ℝ := fun c => (Real.sqrt (G c c).re)⁻¹ with hd_def
    have hdr : ∀ c, d c * (G c c).re * d c = 1 := fun c => by
      have hs := Real.mul_self_sqrt (hnn c)
      have hsq : Real.sqrt (G c c).re ≠ 0 := (Real.sqrt_pos.mpr (hpos c)).ne'
      simp only [hd_def]
      field_simp
      nlinarith [hs]
    set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun c => (d c : ℂ) with hD_def
    have hD : Dᴴ = D := by simp [hD_def, Matrix.diagonal_conjTranspose]
    have hH : (D * G * D).PosSemidef := by
      have h := hG.conjTranspose_mul_mul_same D
      rwa [hD] at h
    have hHd : ∀ c, (D * G * D) c c = 1 := by
      intro c
      simp only [hD_def, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [hdiag c]
      exact_mod_cast hdr c
    have h1 := psd_det_re_le_one_of_diag N _ hH hHd
    have hdet : (D * G * D).det = (((∏ c, d c) ^ 2 : ℝ) : ℂ) * G.det := by
      simp only [hD_def, Matrix.det_mul, Matrix.det_diagonal]
      push_cast
      ring
    rw [hdet, Complex.re_ofReal_mul] at h1
    have hprod : (∏ c, d c) ^ 2 * ∏ c, (G c c).re = 1 := by
      rw [show (∏ c, d c) ^ 2 * ∏ c, (G c c).re = ∏ c, (d c * (G c c).re * d c) by
        rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun c _ => by ring]
      exact Finset.prod_eq_one fun c _ => hdr c
    have hp : 0 < (∏ c, d c) ^ 2 :=
      pow_pos (Finset.prod_pos fun c _ => inv_pos.mpr (Real.sqrt_pos.mpr (hpos c))) 2
    by_contra hlt
    push_neg at hlt
    have := mul_lt_mul_of_pos_left hlt hp
    linarith

theorem hadamard_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  have hdet : (A * Aᴴ).det.re = ‖A.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [show star A.det = (starRingEnd ℂ) A.det from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hdiag : ∀ i, ((A * Aᴴ) i i).re = ∑ j, ‖A i j‖ ^ 2 := fun i => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show star (A i j) = (starRingEnd ℂ) (A i j) from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have key := psd_det_re_le_prod_diag n (A * Aᴴ) (Matrix.posSemidef_self_mul_conjTranspose A)
  rw [hdet] at key
  simp only [hdiag] at key
  have hs : ∀ i, 0 ≤ ∑ j, ‖A i j‖ ^ 2 := fun i => Finset.sum_nonneg fun j _ => by positivity
  calc ‖A.det‖ = Real.sqrt (‖A.det‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [← Finset.prod_pow]
        have h : ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) ^ 2 = ∏ i, ∑ j, ‖A i j‖ ^ 2 :=
          Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hs i)
        rw [h]
        exact key
    _ = ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) :=
        Real.sqrt_sq (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)

end ReciprocityTheory.ChartRestriction.G.T0
end

