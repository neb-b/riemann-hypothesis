module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
public import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.FrobSplit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Tw

private theorem int_mem {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω x ∈ A := by
  have hi : IsIntegral ℤ (algebraMap L Ω x) := x.isIntegral_coe.algebraMap
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
  rw [← hy]
  exact y.2

private theorem exists_above {F L Ω : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v ∧ IsPlaceOver A w := by
  let φ : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring (int_mem A)
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap φ :=
    fun x => (A.valuation_lt_one_iff (φ x)).symm
  have hu : ((IsLocalRing.maximalIdeal A).comap φ).under (𝓞 F) = v.asIdeal := by
    ext x
    rw [← hA x, IsScalarTower.algebraMap_apply F L Ω]
    exact (hP (algebraMap (𝓞 F) (𝓞 L) x)).symm
  haveI : ((IsLocalRing.maximalIdeal A).comap φ).LiesOver v.asIdeal := ⟨hu.symm⟩
  exact ⟨⟨(IsLocalRing.maximalIdeal A).comap φ, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _⟩,
    HeightOneSpectrum.ext hu, hP⟩

private theorem normV_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [show normV w = Ideal.absNorm w.asIdeal by
        rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply],
      show normV (w.under (𝓞 K)) = Ideal.absNorm (w.under (𝓞 K)).asIdeal by
        rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := Nat.card_eq_fintype_card
  rw [e]
  by_contra hlt
  refine Polynomial.X_pow_sub_X_ne_zero (R := 𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [Polynomial.natDegree_X_pow_sub_X hq, Finset.card_univ]
    exact not_le.1 hlt

private theorem two_of_sum {ι : Type} [Fintype ι] (f : ι → ℕ) (hf : ∀ i, 0 < f i) (hs : ∑ i, f i = 2) (a : ι)
    (ha : f a = 1) : ∃ b, b ≠ a ∧ f b = 1 ∧ ∀ c, c = a ∨ c = b := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha] at hs
  have h1 : ∑ i ∈ Finset.univ.erase a, f i = 1 := by omega
  obtain ⟨b, hb⟩ : (Finset.univ.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at h1
    simp at h1
  rw [← Finset.add_sum_erase _ _ hb] at h1
  have := hf b
  refine ⟨b, Finset.ne_of_mem_erase hb, by omega, fun c => ?_⟩
  by_contra hc
  rw [not_or] at hc
  have h2 : f c ≤ ∑ i ∈ (Finset.univ.erase a).erase b, f i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hc.1, hc.2])
  have := hf c
  omega

theorem UpperTheory.V.Af.Tw.frobSplit :
    UpperTheory.V.Af.Tw.FrobSplit := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hur hA s hs
  classical
  obtain ⟨w, hwv, hw⟩ := exists_above (L := L) hA
  have hq : 1 < normV v := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hle : normV w ≤ normV v := by
    refine normV_le w hq fun x => ?_
    rw [← hw]
    have h3 := hs.2 _ ((A.valuation_le_one_iff _).2 (int_mem A x))
    have h4 : resG F L Ω s (algebraMap L Ω x) = algebraMap L Ω x := s.commutes x
    rw [h4] at h3
    simpa using h3
  haveI := v.isMaximal
  haveI := w.isPrime
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    rw [normV_under' (K := F) w, hwv] at hle
    have h5 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos _ _
    have h6 : w.asIdeal.inertiaDeg (𝓞 F) ≤ 1 :=
      (Nat.pow_le_pow_iff_right hq).1 (by rwa [pow_one])
    omega
  have hl : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 F) = v → u.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) :=
    fun u hu => ⟨u.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 F)).ne_bot]
    exact hur w hwv
  haveI := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L, h2] at hsum
  obtain ⟨⟨Q, hQ, hQv⟩, hne, h1, hall⟩ := two_of_sum _
    (fun P => Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)) hsum
    ⟨w.asIdeal, hl w hwv⟩ (by simp only [he, hf])
  let w' : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw' : w'.under (𝓞 F) = v := HeightOneSpectrum.ext hQv.over.symm
  have hf' : w'.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_left h1
  refine ⟨w, w', fun h => hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)), fun u => ⟨fun hu => ?_, ?_⟩,
    hw, ?_, ?_⟩
  · rcases hall ⟨u.asIdeal, hl u hu⟩ with h | h
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro (rfl | rfl)
    exacts [hwv, hw']
  · rw [normV_under' (K := F) w, hwv, hf, pow_one]
  · rw [normV_under' (K := F) w', hw', hf', pow_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.InfTriv
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.NormCompat

namespace UpperTheory.V.Af.Tw

variable {E : Type} [Field E] [NumberField E]

private theorem mem_infConn_of (w : InfinitePlace E) (x : (w.Completion)ˣ) (S : Set w.Completion)
    (hS : IsPreconnected S) (h0 : 0 ∉ S) (h1 : 1 ∈ S) (hx : (x : w.Completion) ∈ S) : infIdele E w x ∈ infConn E := by
  classical
  let T : Set (w.Completion)ˣ := Units.val ⁻¹' S
  have hT : IsPreconnected T := by
    have himg : Units.val '' T = S := by
      ext a
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ha
        have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
        exact ⟨Units.mk0 a ha0, ha, rfl⟩
    rw [← Units.isEmbedding_val₀.isInducing.isPreconnected_image, himg]
    exact hS
  let φ : (w.Completion)ˣ →* (InfiniteAdeleRing E)ˣ :=
    Units.map (MonoidHom.mulSingle (fun v : InfinitePlace E => v.Completion) w)
  have hφ : Continuous φ := Continuous.units_map _ (continuous_mulSingle w)
  have hsub : φ '' T ⊆ connectedComponent (1 : (InfiniteAdeleRing E)ˣ) :=
    (hT.image _ hφ.continuousOn).subset_connectedComponent ⟨1, h1, map_one φ⟩
  unfold infConn
  refine ⟨φ x, hsub ⟨x, hx, rfl⟩, ?_⟩
  exact Units.ext rfl

private theorem mem_of_sign (N : Subgroup (Ideles E)) (hN : infConn E ≤ N)
    (hs : ∀ w : InfinitePlace E, w.IsReal → infIdele E w (-1) ∈ N) (w : InfinitePlace E) (x : (w.Completion)ˣ) :
    infIdele E w x ∈ N := by
  have key : ∀ (K : Type) [NormedField K] (e : w.Completion ≃ᵢ K), (∀ a, e a = 0 ↔ a = 0) → e 1 = 1 →
      ∀ T : Set K, IsPreconnected T → (0 : K) ∉ T → (1 : K) ∈ T →
      ∀ y : (w.Completion)ˣ, e y ∈ T → infIdele E w y ∈ N := by
    intro K _ e he0 he1 T hT hT0 hT1 y hy
    apply hN
    refine mem_infConn_of w y (e.symm '' T) (hT.image _ e.symm.continuous.continuousOn) ?_ ?_ ?_
    · rintro ⟨b, hb, hb0⟩
      have hb' : b = e 0 := by rw [← hb0, e.apply_symm_apply]
      rw [hb', (he0 0).2 rfl] at hb
      exact hT0 hb
    · refine ⟨1, hT1, ?_⟩
      rw [← he1]
      exact e.symm_apply_apply 1
    · exact ⟨e y, hy, e.symm_apply_apply _⟩
  rcases InfinitePlace.isReal_or_isComplex w with hr | hc
  · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hr
    have he0 : ∀ a, e a = 0 ↔ a = 0 := fun a =>
      map_eq_zero_iff (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr)
        (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr).injective
    have he1 : e 1 = 1 := map_one (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr)
    have hneg : ∀ a, e (-a) = - e a := fun a =>
      map_neg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hr) a
    have hx0 : e x ≠ 0 := fun h => x.ne_zero ((he0 _).1 h)
    rcases lt_or_gt_of_ne hx0 with hlt | hgt
    · have hm : infIdele E w (-x) ∈ N := key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi
        (by simp) (by simp) (-x) (by
          show e (-(x : w.Completion)) ∈ Set.Ioi 0
          rw [hneg]
          exact neg_pos.2 hlt)
      have hx : x = (-1) * (-x) := by simp
      rw [hx, map_mul]
      exact N.mul_mem (hs w hr) hm
    · exact key ℝ e he0 he1 (Set.Ioi 0) isPreconnected_Ioi (by simp) (by simp) x hgt
  · let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    have he0 : ∀ a, e a = 0 ↔ a = 0 := fun a =>
      map_eq_zero_iff (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding w).injective
    have he1 : e 1 = 1 := map_one (InfinitePlace.Completion.extensionEmbedding w)
    refine key ℂ e he0 he1 {0}ᶜ ?_ (by simp) (by simp) x ?_
    · exact (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 0).isPreconnected
    · exact fun h => x.ne_zero ((he0 _).1 h)

private theorem eq_prod_infIdele (z : Ideles E) (hz : z.val.2 = 1) :
    ∃ y : ∀ w : InfinitePlace E, (w.Completion)ˣ, z = ∏ w, infIdele E w (y w) := by
  classical
  let y : ∀ w : InfinitePlace E, (w.Completion)ˣ := fun w => ⟨z.val.1 w, z.inv.1 w,
    congrFun (congrArg Prod.fst z.val_inv) w, congrFun (congrArg Prod.fst z.inv_val) w⟩
  refine ⟨y, ?_⟩
  ext1
  rw [Units.coe_prod]
  have h1 := map_prod (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
    (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ
  have h2 := map_prod (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
    (fun i => ((infIdele E i (y i)).val : InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)) Finset.univ
  refine Prod.ext ?_ ?_
  · refine Eq.trans ?_ h1.symm
    funext v
    have h3 := map_prod (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) v)
      (fun i => (Pi.mulSingle i (z.val.1 i) : ∀ w : InfinitePlace E, w.Completion)) Finset.univ
    refine Eq.trans ?_ h3.symm
    rw [Finset.prod_eq_single v]
    · show z.val.1 v = Pi.mulSingle v (z.val.1 v) v
      rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      show Pi.mulSingle b (z.val.1 b) v = 1
      exact Pi.mulSingle_eq_of_ne hb.symm _
    · intro h
      exact absurd (Finset.mem_univ v) h
  · refine Eq.trans ?_ h2.symm
    rw [hz]
    symm
    apply Finset.prod_eq_one
    intro i _
    rfl

end UpperTheory.V.Af.Tw

theorem UpperTheory.V.Af.Tw.infTriv :
    UpperTheory.V.Af.Tw.InfTriv := by
  intro F Ω B _ _ _ _ _ _ _ _ _ art ha ν hν hc z σ hz hσ
  let N : Subgroup (Ideles F) := ((liftAb ν hν).comp art).ker
  have hN : infConn F ≤ N := fun x hx => by
    have h : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hx)
    show liftAb ν hν (art x) = 1
    rw [show art x = 1 from h, map_one]
  have hs : ∀ w : InfinitePlace F, w.IsReal → infIdele F w (-1) ∈ N := fun w hw => by
    obtain ⟨j, c, hj, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w hw
    show liftAb ν hν (art _) = 1
    rw [GlobalTheory.HilbertFromArtin.art_sign_eq ha j c hj, liftAb_toAb]
    exact hc c ⟨j, hj⟩
  obtain ⟨y, hy⟩ := eq_prod_infIdele z hz
  have hm : z ∈ N := hy ▸ prod_mem fun w _ => mem_of_sign N hN hs w (y w)
  have hm' : liftAb ν hν (art z) = 1 := hm
  rwa [hσ, liftAb_toAb] at hm'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.LevPow
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (unitIdl)

namespace UpperTheory.V.Af.Tw

private theorem loc (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : v.adicCompletion K, Valued.v x = 1 → ∀ k : ℕ, M ∣ k →
      Valued.v (x ^ k - 1) ≤ Valued.v (N : v.adicCompletion K) := by
  classical
  let I : Ideal (v.adicCompletionIntegers K) := Ideal.span {(N : v.adicCompletionIntegers K)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    apply hN
    have := congrArg (fun r : v.adicCompletionIntegers K => (r : v.adicCompletion K)) h
    simpa using this
  haveI := Formalism.UG.P.glint_finite_quotient_of_dvr inferInstance I hI
  haveI : Finite (v.adicCompletionIntegers K ⧸ I)ˣ :=
    Finite.of_injective (fun u : (v.adicCompletionIntegers K ⧸ I)ˣ => (u : v.adicCompletionIntegers K ⧸ I))
      (fun a b h => Units.ext h)
  refine ⟨Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ, Nat.card_pos, ?_⟩
  intro x hx k hk
  have hxR : x ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hx.le
  have hyR : x⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hx, inv_one]
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  let u : (v.adicCompletionIntegers K)ˣ :=
    ⟨⟨x, hxR⟩, ⟨x⁻¹, hyR⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨j, rfl⟩ := hk
  have h1 : (Units.map (Ideal.Quotient.mk I).toMonoidHom u) ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) = 1 := by
    rw [pow_mul, pow_card_eq_one', one_pow]
  have h2 : ((⟨x, hxR⟩ : v.adicCompletionIntegers K) ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) - 1) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have := congrArg Units.val h1
    simpa [u] using this
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  have hy' : x ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) - 1 =
      (y : v.adicCompletion K) * (N : v.adicCompletion K) := by
    have := congrArg (fun r : v.adicCompletionIntegers K => (r : v.adicCompletion K)) hy
    simpa using this.symm
  rw [hy', map_mul]
  have hyle : Valued.v (y : v.adicCompletion K) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2
  simpa using mul_le_mul' hyle (le_refl (Valued.v (N : v.adicCompletion K)))

theorem levPow : LevPow := by
  unfold LevPow
  intro K _ _ N hN
  choose M hMpos hM using fun v : HeightOneSpectrum (𝓞 K) => loc K hN v
  have hN0 : Ideal.span {(N : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  have hfin := Ideal.finite_factors hN0
  refine ⟨∏ v ∈ hfin.toFinset, M v, Finset.prod_pos (fun v _ => hMpos v), ?_⟩
  intro u hu
  refine ⟨pow_mem hu _, fun v => ?_⟩
  have hpow : ∀ P : ℕ, (u ^ P).val.2 v = (u.val.2 v) ^ P := by
    intro P
    induction P with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Units.val_mul, pow_succ, ← ih]
      rfl
  have hu1 : Valued.v (u.val.2 v) = 1 := hu v
  show Valued.v ((u ^ (∏ v ∈ hfin.toFinset, M v)).val.2 v - 1) ≤ Valued.v (N : v.adicCompletion K)
  rw [hpow]
  by_cases hv : v ∈ hfin.toFinset
  · exact hM v _ hu1 _ (Finset.dvd_prod_of_mem M hv)
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton] at hv
    have hlt := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) v (N : 𝓞 K)).not.2 hv
    have hle := HeightOneSpectrum.valuation_le_one (K := K) v (N : 𝓞 K)
    have h2 := PI.IntAdCpctOpenWork.valued_algebraMap v (N : K)
    simp at h2 hlt hle
    have hN1 : Valued.v (N : v.adicCompletion K) = 1 := by
      rw [h2]
      exact le_antisymm hle hlt
    rw [hN1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [map_pow, hu1, one_pow]
    · rw [map_one]

end UpperTheory.V.Af.Tw
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.LocProd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

private noncomputable def UpperTheory.V.Af.Tw.compAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def UpperTheory.V.Af.Tw.infPart (K : Type) [Field K] [NumberField K] :
    AdeleRing (𝓞 K) K →* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem UpperTheory.V.Af.Tw.loc_same {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_same _ _ _

private theorem UpperTheory.V.Af.Tw.loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 w = 1 := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

theorem UpperTheory.V.Af.Tw.locProd :
    UpperTheory.V.Af.Tw.LocProd := by
  unfold UpperTheory.V.Af.Tw.LocProd
  intro F L _ _ _ _ _ v x
  classical
  let y : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ := fun w =>
    Units.map (finiteCompletionMap F L w).toMonoidHom
      (Units.map (UpperTheory.V.Af.Tw.compAt F (HeightOneSpectrum.under (𝓞 F) w)) (localIdele F v x))
  have hy : ∀ w, ((y w : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      finiteCompletionMap F L w ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w)) :=
    fun w => rfl
  have hmem : ∀ w : HeightOneSpectrum (𝓞 L),
      w ∈ aboveF F v ↔ HeightOneSpectrum.under (𝓞 F) w = v :=
    fun w => by
      unfold aboveF
      simp
  have key : ∀ a b : AdeleRing (𝓞 L) L, UpperTheory.V.Af.Tw.infPart L a = UpperTheory.V.Af.Tw.infPart L b →
      (∀ w, UpperTheory.V.Af.Tw.compAt L w a = UpperTheory.V.Af.Tw.compAt L w b) → a = b :=
    fun a b h1 h2 => Prod.ext h1 (RestrictedProduct.ext _ _ h2)
  refine ⟨y, ?_, ?_⟩
  · apply Units.ext
    rw [Units.coe_prod]
    apply key
    · rw [map_prod]
      have h1 : ∀ w, UpperTheory.V.Af.Tw.infPart L ((localIdele L w (y w)).val) = 1 := fun w => rfl
      simp only [h1, Finset.prod_const_one]
      show infiniteAdeleMap F L 1 = 1
      exact map_one _
    · intro w'
      rw [map_prod]
      show finiteCompletionMap F L w' ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w')) =
        ∏ w ∈ aboveF F v, (localIdele L w (y w)).val.2 w'
      by_cases hw' : HeightOneSpectrum.under (𝓞 F) w' = v
      · rw [Finset.prod_eq_single w']
        · rw [UpperTheory.V.Af.Tw.loc_same, hy]
        · intro b _ hb
          exact UpperTheory.V.Af.Tw.loc_ne (Ne.symm hb) _
        · intro h
          exact absurd ((hmem w').mpr hw') h
      · rw [UpperTheory.V.Af.Tw.loc_ne hw', map_one, Finset.prod_eq_one]
        intro b hb
        exact UpperTheory.V.Af.Tw.loc_ne (fun h => hw' (by rw [h]; exact (hmem b).mp hb)) _
  · intro hunr hx w hw
    subst hw
    unfold IsUnifAt at hx ⊢
    rw [hy, UpperTheory.V.Af.Tw.loc_same, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, hunr w rfl, pow_one]
    exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.SplitIso
section
open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal

theorem UpperTheory.V.Af.Tw.splitIso :
    UpperTheory.V.Af.Tw.SplitIso := by
  intro F L _ _ _ _ _ h2 w w' hne hunder
  classical
  set v := HeightOneSpectrum.under (𝓞 F) w with hv
  haveI hw : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  haveI hw' : w'.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hunder).symm⟩
  have hsum := sum_ramificationIdx_mul_inertiaDeg L v
  rw [h2] at hsum
  have hpos : ∀ u : PlacesOver L v, 1 ≤ (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F) := fun u =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  let a : PlacesOver L v := ⟨w, hw⟩
  let b : PlacesOver L v := ⟨w', hw'⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h).symm
  have hle := Finset.add_le_sum (s := Finset.univ)
    (f := fun u : PlacesOver L v => (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) hab
  have hle2 := hle.trans_eq hsum
  have ha1 := hpos a
  have hb1 := hpos b
  have h1 : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    change _ + _ ≤ 2 at hle2
    change 1 ≤ w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) at ha1
    change 1 ≤ w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) at hb1
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) +
      w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle2
    omega
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hfin : Module.finrank (v.adicCompletion F) (w.adicCompletion L) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w, h1]
  have hbij : Function.Bijective (completionMap v w) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin
  let e := RingEquiv.ofBijective (completionMap v w) hbij
  refine ⟨(e.symm : w.adicCompletion L →+* v.adicCompletion F), ?_, ?_⟩
  · refine GlobalTheory.DenseCompl.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective L w) _ ?_
    intro y
    obtain ⟨x, rfl⟩ := hbij.2 y
    have hx : (e.symm : w.adicCompletion L →+* v.adicCompletion F) (completionMap v w x) = x :=
      e.symm_apply_apply x
    rw [hx, valued_completionMap, he, pow_one]
  · intro x
    exact e.symm_apply_apply x
end

