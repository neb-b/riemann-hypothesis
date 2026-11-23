module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCmPatch
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.patched_depth_dim :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      Module.Finite L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      (∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs) ∧
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = ((r + e : ℕ) : WithBot ℕ∞) := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y hL hy hq hfree hfin
  refine ⟨exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree, ?_⟩
  obtain ⟨xs, hlen, hxs, hreg⟩ := exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree
  have hys : ∀ z ∈ List.ofFn y, z ∈ maximalIdeal B := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hy i
  have h1 := GlobalTheory.supportDim_le_supportDim_quotient_add_length (M := M) hys
  rw [GlobalTheory.ofList_ofFn_eq_span_range, List.length_ofFn] at h1
  have h2 := supportDim_le_of_finite L B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M))
  rw [hL] at h2
  have hdim : Module.supportDim B M ≤ ((xs.length : ℕ) : WithBot ℕ∞) := by
    refine h1.trans ?_
    rw [hlen]
    calc Module.supportDim B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) + ((r : ℕ) : WithBot ℕ∞)
        ≤ ((e : ℕ) : WithBot ℕ∞) + ((r : ℕ) : WithBot ℕ∞) := by gcongr
      _ = ((r + e : ℕ) : WithBot ℕ∞) := by
        rw [add_comm]; norm_cast
  intro Z hZ
  have := dim_minimalPrime_eq B M xs hxs hreg.toIsWeaklyRegular hdim Z hZ
  rw [this, hlen]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotLoc
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem prime_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) : (Ideal.span (x '' (s : Set κ))).IsPrime := by
  have h := (regular_quotient_cotInd R s (x ∘ ((↑) : s → κ)) (hx.comp _ Subtype.val_injective)).2.2
  have e : Set.range (x ∘ ((↑) : s → κ)) = x '' (s : Set κ) := by
    rw [Set.range_comp]
    congr 1
    ext a
    simp
  rwa [e] at h

private theorem not_mem_sub (R : Type) [CommRing R] [IsLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) (a : κ) (ha : a ∉ s) :
    x a ∉ Ideal.span (x '' (s : Set κ)) := by
  classical
  intro hmem
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).mp hmem
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul R (x i))] at hlx
  simp only [smul_eq_mul] at hlx
  let b : κ → R := Pi.single a 1
  have h0 : ∑ k, (b k - l k) * x k ∈ maximalIdeal R ^ 2 := by
    have hz : ∑ k, (b k - l k) * x k = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, hlx]
      simp [b, Pi.single_apply]
    rw [hz]
    exact zero_mem _
  have h1 := hx.indep _ h0 a
  rw [(Finsupp.mem_supported' R l).mp hl a ha, sub_zero] at h1
  simp only [b, Pi.single_eq_same] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem height_sub (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ]
    (x : κ → R) (hx : CotInd R x) (s : Finset κ) :
    (s.card : ℕ∞) ≤ (Ideal.span (x '' (s : Set κ))).height := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    haveI := prime_sub R κ x hx s
    haveI := prime_sub R κ x hx (insert a s)
    have hlt : Ideal.span (x '' (s : Set κ)) < Ideal.span (x '' ((insert a s : Finset κ) : Set κ)) := by
      refine lt_of_le_of_ne (Ideal.span_mono (Set.image_mono (by simp))) fun e => ?_
      apply not_mem_sub R κ x hx s a ha
      rw [e]
      exact Ideal.subset_span ⟨a, by simp, rfl⟩
    have h1 := Ideal.height_strict_mono_of_isPrime hlt
    rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
    exact Order.add_one_le_of_lt (ih.trans_lt h1)

theorem UpperTheory.V.AlgebraTools.regular_localization_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∀ (p : Ideal R) [p.IsPrime], p = Ideal.span (Set.range x) →
      p.height = (Fintype.card κ : ℕ) ∧ IsRegularLocalRing (Localization.AtPrime p) := by
  classical
  intro R _ _ κ _ x hx p _ hp
  have hge : ((Fintype.card κ : ℕ) : ℕ∞) ≤ p.height := by
    have h1 := height_sub R κ x hx Finset.univ
    rwa [Finset.card_univ, Finset.coe_univ, Set.image_univ, ← hp] at h1
  have hle : p.height ≤ ((Fintype.card κ : ℕ) : ℕ∞) := by
    have e : Ideal.span ((Finset.univ.image x : Finset R) : Set R) = p := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hp]
    have hmin : p ∈ (Ideal.span ((Finset.univ.image x : Finset R) : Set R)).minimalPrimes := by
      rw [e, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton p
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_image_le
  have heq : p.height = ((Fintype.card κ : ℕ) : ℕ∞) := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl,
    IsLocalization.AtPrime.under_maximalIdeal _ p, heq, ← Localization.AtPrime.map_eq_maximalIdeal]
  have hmap : Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      Ideal.map (algebraMap R (Localization.AtPrime p)) (Ideal.span (Set.range x)) := congrArg _ hp
  rw [hmap, Ideal.map_span, ← Set.range_comp]
  have h3 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Localization.AtPrime p)
    (Set.finite_range (algebraMap R (Localization.AtPrime p) ∘ x))
  have h4 : (Set.range (algebraMap R (Localization.AtPrime p) ∘ x)).ncard ≤ Fintype.card κ := by
    rw [← Set.image_univ, ← Finset.coe_univ]
    exact (Set.ncard_coe_finset _ ▸ Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
  exact_mod_cast h3.trans h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfQuot
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem card_le_dim (R : Type) [CommRing R] [IsRegularLocalRing R] (r : ℕ) (x : Fin r → R)
    (hx : CotInd R x) : (r : WithBot ℕ∞) ≤ ringKrullDim R := by
  obtain ⟨s, y, -, -, hc⟩ := cotInd_extend R _ x hx
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc, Fintype.card_fin]
  exact_mod_cast Nat.le_add_right r s

private theorem exists_max (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) :
    ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ (∀ k, x k ∈ I) ∧
      I ≤ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 := by
  classical
  let P : ℕ → Prop := fun r => ∃ x : Fin r → R, CotInd R x ∧ ∀ k, x k ∈ I
  have h0 : P 0 := ⟨Fin.elim0, ⟨fun k => k.elim0, fun _ _ k => k.elim0⟩, fun k => k.elim0⟩
  have hb : ∀ r, P r → r ≤ (maximalIdeal R).spanFinrank := by
    rintro r ⟨x, hx, -⟩
    have := card_le_dim R r x hx
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at this
    exact_mod_cast this
  obtain ⟨x, hx, hxI⟩ : P (Nat.findGreatest P (maximalIdeal R).spanFinrank) :=
    Nat.findGreatest_spec (Nat.zero_le _) h0
  refine ⟨_, x, hx, hxI, fun t ht => ?_⟩
  by_contra hn
  have h1 : P (Nat.findGreatest P (maximalIdeal R).spanFinrank + 1) := by
    refine ⟨Fin.cons t x, ⟨?_, ?_⟩, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact hI ht
      · exact hx.mem j
    · intro a ha
      rw [Fin.sum_univ_succ] at ha
      simp only [Fin.cons_zero, Fin.cons_succ] at ha
      have ha0 : a 0 ∈ maximalIdeal R := by
        by_contra hu
        have hu' : IsUnit (a 0) := by simpa using hu
        apply hn
        rw [← Ideal.unit_mul_mem_iff_mem _ hu']
        have h2 : ∑ i, a i.succ * x i ∈ Ideal.span (Set.range x) :=
          Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
        have h3 := sub_mem (Ideal.mem_sup_right (S := Ideal.span (Set.range x)) ha)
          (Ideal.mem_sup_left h2)
        simpa using h3
      have h4 : a 0 * t ∈ maximalIdeal R ^ 2 := by
        rw [sq]
        exact Ideal.mul_mem_mul ha0 (hI ht)
      have h5 : ∑ i, a i.succ * x i ∈ maximalIdeal R ^ 2 := by
        simpa using sub_mem ha h4
      intro k
      exact Fin.cases ha0 (fun j => hx.indep (fun i => a i.succ) h5 j) k
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ht
      · exact hxI j
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hb _ h1) h1

theorem UpperTheory.V.AlgebraTools.exists_cotInd_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ∃ (r : ℕ) (x : Fin r → R), CotInd R x ∧ Ideal.span (Set.range x) = I := by
  intro R _ _ I _
  have hne : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hI : I ≤ maximalIdeal R := le_maximalIdeal hne
  obtain ⟨r, x, hx, hxI, hle⟩ := exists_max R I hI
  refine ⟨r, x, hx, ?_⟩
  have hJ : Ideal.span (Set.range x) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hxI k
  obtain ⟨s, y, hxy, -, hc⟩ := cotInd_extend R _ x hx
  obtain ⟨-, hd, hp⟩ := regular_quotient_cotInd R _ x hx
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hy : CotInd (R ⧸ I) (fun j => Ideal.Quotient.mk I (y j)) := by
    refine ⟨fun j => hmax ▸ Ideal.mem_map_of_mem _ (hxy.mem (Sum.inr j)), fun a ha => ?_⟩
    choose b hb using fun j => Ideal.Quotient.mk_surjective (a j)
    have h1 : Ideal.Quotient.mk I (∑ j, b j * y j) ∈
        Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R ^ 2) := by
      rw [Ideal.map_pow, hmax]
      simpa [hb] using ha
    rw [Ideal.mem_quotient_iff_mem_sup] at h1
    have h2 : ∑ j, b j * y j ∈ Ideal.span (Set.range x) ⊔ maximalIdeal R ^ 2 :=
      sup_le le_sup_right hle h1
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h2
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
    have h3 : ∑ k, Sum.elim (fun i => - c i) b k * Sum.elim x y k ∈ maximalIdeal R ^ 2 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, ← huv, neg_mul, Finset.sum_neg_distrib]
      simpa using hv
    intro j
    rw [← hb j, ← hmax]
    exact Ideal.mem_map_of_mem _ (hxy.indep _ h3 (Sum.inr j))
  have hs := card_le_dim _ s _ hy
  refine le_antisymm hJ fun t ht => ?_
  by_contra hn
  have : IsDomain (R ⧸ Ideal.span (Set.range x)) := (Ideal.Quotient.isDomain_iff_prime _).2 hp
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range x)) t ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h4 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hJ)
    (Ideal.Quotient.factor_surjective hJ) (mem_nonZeroDivisors_of_ne_zero h0)
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact ht)
  have h5 : ((s : WithBot ℕ∞) + 1) + (Fintype.card (Fin r) : ℕ) ≤ ringKrullDim R := by
    rw [← hd]
    gcongr
    exact le_trans (by gcongr) h4
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hc] at h5
  have h6 : s + 1 + Fintype.card (Fin r) ≤ Fintype.card (Fin r) + s := by exact_mod_cast h5
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFin
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem pullback_fin_relation {k C : Type} [Field k] [CommRing C] [Algebra k C] (S : Subalgebra k C)
    [Module.Finite k S] (T : Set C) (hT : T ⊆ S) (hfg : (Ideal.span T).FG)
    (hI : ∀ x ∈ Ideal.span T, IsUnit (1 - x))
    (hd : ∀ (n : ℕ) (c : C), ∃ a ∈ S, ∃ s ∈ S, IsUnit s ∧ s * c - a ∈ Ideal.span T ^ n) :
    Module.Finite k C := by
  set J := Ideal.span T with hJ
  have hinv : ∀ s ∈ S, IsUnit s → ∃ t ∈ S, t * s = 1 := by
    intro s hsS hs
    let f : S →ₗ[k] S := LinearMap.mulLeft k (⟨s, hsS⟩ : S)
    have hfi : Function.Injective f := by
      intro x y hxy
      have h1 : s * (x : C) = s * (y : C) := congrArg Subtype.val hxy
      exact Subtype.ext (hs.mul_left_cancel h1)
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hfi) 1
    refine ⟨y, y.2, ?_⟩
    have h2 : s * (y : C) = 1 := congrArg Subtype.val hy
    rw [mul_comm]
    exact h2
  have hC : ∀ (n : ℕ) (c : C), ∃ a ∈ S, c - a ∈ J ^ n := by
    intro n c
    obtain ⟨a, haS, s, hsS, hs, hmem⟩ := hd n c
    obtain ⟨t, htS, hts⟩ := hinv s hsS hs
    refine ⟨t * a, S.mul_mem htS haS, ?_⟩
    have e : c - t * a = t * (s * c - a) := by
      calc c - t * a = (t * s) * c - t * a := by rw [hts, one_mul]
        _ = t * (s * c - a) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ t hmem
  let W : ℕ → Submodule k S := fun n =>
    Submodule.comap S.val.toLinearMap ((J ^ n).restrictScalars k)
  have hWmem : ∀ n (x : S), x ∈ W n ↔ (x : C) ∈ J ^ n := fun n x => Iff.rfl
  have hWle : ∀ n, W (n + 1) ≤ W n := by
    intro n x hx
    rw [hWmem] at hx ⊢
    exact Ideal.pow_le_pow_right (Nat.le_succ n) hx
  obtain ⟨n0, hn0⟩ : ∃ n0, W n0 ≤ W (n0 + 1) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ n, Module.finrank k (W (n + 1)) < Module.finrank k (W n) := by
      intro n
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hWle n) (fun h => hcon n h.ge))
    have hbd : ∀ n, n + Module.finrank k (W n) ≤ Module.finrank k (W 0) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        have := hlt m
        omega
    have := hbd (Module.finrank k (W 0) + 1)
    omega
  have hstep : J ^ n0 ≤ J ^ (n0 + 1) := by
    intro x hx
    obtain ⟨a, haS, hxa⟩ := hC (n0 + 1) x
    have haJ : a ∈ J ^ n0 := by
      have h1 : x - a ∈ J ^ n0 := Ideal.pow_le_pow_right (Nat.le_succ n0) hxa
      have h2 := Ideal.sub_mem _ hx h1
      simpa using h2
    have ha1 : a ∈ J ^ (n0 + 1) := (hWmem (n0 + 1) ⟨a, haS⟩).mp (hn0 ((hWmem n0 ⟨a, haS⟩).mpr haJ))
    have h3 := Ideal.add_mem _ hxa ha1
    simpa using h3
  have hzero : J ^ n0 = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J (J ^ n0) (Ideal.FG.pow (n := n0) hfg)
    · rw [smul_eq_mul, ← pow_succ']
      exact hstep
    · intro x hx
      rw [Ideal.mem_jacobson_bot]
      intro y
      have h := hI (-(x * y)) (J.neg_mem (J.mul_mem_right y hx))
      rw [sub_neg_eq_add, add_comm] at h
      exact h
  have hsurj : Function.Surjective S.val.toLinearMap := by
    intro c
    obtain ⟨a, haS, hca⟩ := hC n0 c
    rw [hzero, Ideal.mem_bot, sub_eq_zero] at hca
    exact ⟨⟨a, haS⟩, hca.symm⟩
  exact Module.Finite.of_surjective _ hsurj
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFlat
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.flat :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → Module.Flat R B := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI : Module.Flat (Localization.AtPrime p) (CplAt R p) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.Flat R (CplAt R p) := Module.Flat.trans R (Localization.AtPrime p) (CplAt R p)
  obtain ⟨e⟩ := IsCplAt.nonempty_algEquiv R p B (CplAt R p) h (isCplAt_cplAt R p)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplReg
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.regular :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (B : Type) [CommRing B] [IsLocalRing B]
      [Algebra R B], IsCplAt R p B → IsRegularLocalRing (Localization.AtPrime p) →
      IsRegularLocalRing B ∧ ringKrullDim B = ringKrullDim (Localization.AtPrime p) := by
  intro R _ _ p _ B _ _ _ hB hT
  obtain ⟨e⟩ := IsCplAt.nonempty_algEquiv R p B (CplAt R p) hB (isCplAt_cplAt R p)
  have hC : IsRegularLocalRing (CplAt R p) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion (Localization.AtPrime p)
  refine ⟨IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← hC.spanFinrank_maximalIdeal,
    ← hT.spanFinrank_maximalIdeal]
  exact congrArg _ (AdicCompletion.spanFinrank_maximalIdeal_eq (R := Localization.AtPrime p))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartPrime
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (Q : Ideal (MvPolynomial ι P)) [Q.IsPrime],
      (maximalIdeal P).map (MvPolynomial.C : P →+* MvPolynomial ι P) ≤ Q →
      ((chartIdeal z m c).map (algebraMap _ (Localization.AtPrime Q))).IsPrime := by
  intro P _ _ ι _ _ z m hx c Q _ hQ
  obtain ⟨_, hcot⟩ := regular_polynomial_localization P ι Q hQ
  let φ : MvPolynomial ι P →+* Localization.AtPrime Q := algebraMap _ _
  let w : ι → Localization.AtPrime Q := fun j => φ (MvPolynomial.C (m j))
  let l : ι → Localization.AtPrime Q := fun j => φ (lam P c j)
  let y : Matrix ι ι (Localization.AtPrime Q) := z.map (φ.comp MvPolynomial.C)
  have h1 : CotInd (Localization.AtPrime Q) (Sum.elim (fun ij : ι × ι => y ij.1 ij.2) w) := by
    have h := hcot _ _ hx
    convert h using 1
    funext k
    rcases k with k | k <;> rfl
  have hl : l c = 1 := by
    simp [l, lam]
  have h2 := chartGen_cotInd (Localization.AtPrime Q) ι y w l c h1 hl
  have h3 := (regular_quotient_cotInd (Localization.AtPrime Q) _ _ h2).2.2
  have hf : ⇑φ ∘ chartGen z m c = Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c := by
    funext k
    rcases k with k | k
    · simp only [Function.comp, chartGen, Sum.elim_inl]
      rw [RingHom.map_mulVec, Matrix.map_map]
      rfl
    · simp [chartGen, w, l]
  have key : (chartIdeal z m c).map φ =
      Ideal.span (Set.range (Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c)) := by
    rw [chartIdeal, Ideal.map_span, ← Set.range_comp, hf]
  exact key ▸ h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDvrIc
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.integralClosure_complete_dvr :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      (F K : Type) [Field F] [Field K] [Algebra A F] [IsFractionRing A F] [Algebra F K] [Algebra A K]
      [IsScalarTower A F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
      (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra B K] [IsScalarTower A B K] [IsIntegralClosure B A K],
      Module.Finite A B ∧ Module.Free A B ∧ IsFractionRing B K ∧
      ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B ∧ IsLocalHom (algebraMap A B) ∧
        (Finite (ResidueField A) → Finite (ResidueField B)) := by
  intro A _ _ _ _ F K _ _ _ _ _ _ _ _ _ B _ _ _ _ _ _
  have hinjK : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective A F)
  have hinj : Function.Injective (algebraMap A B) := by
    rw [IsScalarTower.algebraMap_eq A B K, RingHom.coe_comp] at hinjK
    exact hinjK.of_comp
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI hfin : Module.Finite A B := IsIntegralClosure.finite A F K B
  haveI hfree : Module.Free A B := Module.free_of_finite_type_torsion_free'
  have hfr : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension A F K B
  haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure A F K
  haveI hdvr : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsIntegralClosure.equiv A (integralClosure A K) K B)
  haveI hloc : IsLocalHom (algebraMap A B) := inferInstance
  refine ⟨hfin, hfree, hfr, hdvr, GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite A B,
    hloc, fun h => ?_⟩
  exact IsLocalRing.ResidueField.finite_of_finite h
end

