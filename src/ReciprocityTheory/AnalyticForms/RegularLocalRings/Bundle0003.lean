module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
section
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

section LocGen

variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}

lemma ds_core (hV : ∀ x : W, ∃ c, x ∈ V c)
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {U : W.affineOpens} (s a : Γ(W, U))
    (ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen s → W.presheaf.germ U.1 z hz a ∈ dsK V g z) :
    ∃ m : ℕ, s ^ m * a ∈ dsJ V g U := by
  classical
  have hc : ∀ z : U.1, ∃ t : Γ(W, U), ∃ c, W.basicOpen t ≤ V c ∧ (z : W) ∈ W.basicOpen t := by
    intro z
    obtain ⟨c, hc⟩ := hV z
    obtain ⟨t, ht, hzt⟩ := U.2.exists_basicOpen_le ⟨(z : W), hc⟩ z.2
    exact ⟨t, c, ht, hzt⟩
  choose t c ht hzt using hc
  have hm : ∀ z : U.1, ∃ m : ℕ, ∀ y (hy : y ∈ W.basicOpen (t z)),
      W.presheaf.germ U.1 y (W.basicOpen_le (t z) hy) (s ^ m * a) ∈ dsK V g y :=
    fun z => ds_local hg s a ha (c z) (t z) (ht z)
  choose m hm using hm
  obtain ⟨F, hF⟩ := U.2.isCompact.elim_finite_subcover
    (fun z : U.1 => (W.basicOpen (t z) : Set W))
    (fun z => (W.basicOpen (t z)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hzt ⟨y, hy⟩⟩)
  refine ⟨∑ z ∈ F, m z, mem_dsJ.2 fun y hy => ?_⟩
  obtain ⟨z, hzF, hyz⟩ := Set.mem_iUnion₂.1 (hF hy)
  have hle : m z ≤ ∑ z ∈ F, m z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzF
  have h1 := hm z y hyz
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]
  exact Ideal.mul_mem_left _ _ h1

lemma dsJ_basicOpen (hV : ∀ x : W, ∃ c, x ∈ V c)
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    (U : W.affineOpens) (f : Γ(W, U)) :
    (dsJ V g U).map (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom =
      dsJ V g (W.affineBasicOpen f) := by
  apply le_antisymm
  · refine Ideal.map_le_of_le_comap fun b hb => ?_
    change (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b ∈ dsJ V g (W.affineBasicOpen f)
    refine mem_dsJ.2 fun y hy => ?_
    have h1 := (mem_dsJ.1 hb) y (W.basicOpen_le f hy)
    have e : W.presheaf.germ (W.affineBasicOpen f).1 y hy
        ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b) =
        W.presheaf.germ U.1 y (W.basicOpen_le f hy) b :=
      TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) y hy b
    rw [e]
    exact h1
  · intro b hb
    letI := (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom.toAlgebra
    haveI := U.2.isLocalization_basicOpen f
    obtain ⟨⟨a, s'⟩, hab⟩ := IsLocalization.surj (Submonoid.powers f) b
    obtain ⟨n, hn⟩ := s'.2
    simp only [RingHom.algebraMap_toAlgebra, ← hn] at hab
    have ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen f →
        W.presheaf.germ U.1 z hz a ∈ dsK V g z := by
      intro z hz hzf
      have h1 := (mem_dsJ.1 hb) z hzf
      have e1 : W.presheaf.germ (W.basicOpen f) z hzf
          ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom a) = W.presheaf.germ U.1 z hz a :=
        TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf a
      have e2 : W.presheaf.germ (W.basicOpen f) z hzf
          ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ n)) =
            W.presheaf.germ U.1 z hz (f ^ n) :=
        TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf (f ^ n)
      rw [← e1, ← hab, map_mul, e2]
      exact Ideal.mul_mem_right _ _ h1
    obtain ⟨m, hm⟩ := ds_core hV hg f a ha
    have hx : (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) ∈
        (dsJ V g U).map (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom :=
      Ideal.mem_map_of_mem _ hm
    have hu : IsUnit ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n))) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    have heq : b * (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n)) =
        (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) := by
      rw [map_mul, ← hab, pow_add, map_mul]
      ring
    obtain ⟨v, hv⟩ := hu
    have hb' : b = (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) * ↑v⁻¹ := by
      rw [← heq, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [hb']
    exact Ideal.mul_mem_right _ _ hx

end LocGen

theorem exists_idealSheaf_of_locGen {W : Scheme.{0}} {ι' : Type} (V : ι' → W.Opens)
    (hV : ∀ x : W, ∃ c, x ∈ V c) (g : ∀ c, Γ(W, V c))
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c')) :
    ∃ G : W.IdealSheafData, ∀ c (x : W) (hx : x ∈ V c),
      FinalTheorems.stalkId G x = Ideal.span {W.presheaf.germ (V c) x hx (g c)} := by
  refine ⟨⟨fun U => dsJ V g U, fun U f => dsJ_basicOpen hV hg U f, _, rfl⟩, fun c x hx => ?_⟩
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset hx
  rw [ds_stalkId_eq_map _ ⟨U', hU'⟩ x hxU']
  change Ideal.map _ (dsJ V g ⟨U', hU'⟩) = _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, ← dsK_eq hg c hx]
    exact (mem_dsJ.1 hf) x hxU'
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hle : U' ≤ V c := hsub
    have hr : W.presheaf.map (homOfLE hle).op (g c) ∈ dsJ V g ⟨U', hU'⟩ := by
      rw [mem_dsJ]
      intro y hy
      rw [dsK_eq hg c (hsub hy)]
      apply Ideal.subset_span
      simp
    have e : W.presheaf.germ U' x hxU' (W.presheaf.map (homOfLE hle).op (g c)) =
        W.presheaf.germ (V c) x hx (g c) := by simp
    rw [← e]
    exact Ideal.mem_map_of_mem _ hr

theorem effCartier_of_stalkId {W : Scheme.{0}} [IsNoetherian W] (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by
  intro x
  obtain ⟨U0, hU0, hxU0, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : IsNoetherianRing Γ(W, U0) := IsLocallyNoetherian.component_noetherian ⟨U0, hU0⟩
  obtain ⟨t, ht, hst⟩ := hG x
  letI := (W.presheaf.germ U0 x hxU0).hom.toAlgebra
  haveI := hU0.isLocalization_stalk ⟨x, hxU0⟩
  have hI : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) =
      Ideal.span {t} := by
    rw [← hst, ds_stalkId_eq_map G ⟨U0, hU0⟩ x hxU0]
    rfl
  obtain ⟨y, ⟨h, hh, rfl⟩, c, hyc⟩ := ds_gen_of_span
    ((algebraMap Γ(W, U0) (W.presheaf.stalk x)) '' (G.ideal ⟨U0, hU0⟩ : Set Γ(W, U0))) t ht hI
  have hmap : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(W, U0) (W.presheaf.stalk x) h} := by
    rw [hI, hyc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(W, U0) (W.presheaf.stalk x) h ∈
      nonZeroDivisors (W.presheaf.stalk x) := by
    rw [hyc]
    exact mul_mem c.isUnit.mem_nonZeroDivisors ht
  obtain ⟨σ, hσ, hT⟩ := ds_spread (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal _ h hh hmap hnzd
  letI := (W.presheaf.map (homOfLE <| W.basicOpen_le σ).op).hom.toAlgebra
  haveI := hU0.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(W, W.basicOpen σ)
  refine ⟨W.affineBasicOpen (U := ⟨U0, hU0⟩) σ, algebraMap Γ(W, U0) Γ(W, W.basicOpen σ) h, ?_, h2, ?_⟩
  · have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x)
      (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal σ).2 hσ
    exact (Scheme.mem_basicOpen W σ x hxU0).2 hu
  · rw [← G.map_ideal_basicOpen ⟨U0, hU0⟩ σ]
    exact h1

theorem mem_support_iff_stalkId {W : Scheme.{0}} (G : W.IdealSheafData) (x : W) :
    x ∈ (G.support : Set W) ↔ FinalTheorems.stalkId G x ≠ ⊤ := by
  obtain ⟨U', hU', hxU', -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hxU : x ∈ (⟨U', hU'⟩ : W.affineOpens).1 := hxU'
  refine (Scheme.IdealSheafData.mem_support_iff_of_mem hxU).trans ?_
  rw [Scheme.mem_zeroLocus_iff, ds_stalkId_eq_map G _ x hxU]
  constructor
  · intro h htop
    obtain ⟨f, hf, hu⟩ : ∃ f ∈ G.ideal ⟨U', hU'⟩, IsUnit (W.presheaf.germ U' x hxU' f) := by
      by_contra hno
      push_neg at hno
      have hle : Ideal.map (W.presheaf.germ U' x hxU').hom (G.ideal ⟨U', hU'⟩) ≤
          IsLocalRing.maximalIdeal _ := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        exact (IsLocalRing.mem_maximalIdeal _).2 (hno f hf)
      rw [htop] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)
    exact h f hf ((Scheme.mem_basicOpen _ _ _ _).2 hu)
  · intro h f hf hxf
    apply h
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
      ((Scheme.mem_basicOpen _ _ _ hxU).1 hxf)

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
section
namespace ReciprocityTheory.AnForm.R

open IsLocalRing

variable {R : Type*} [CommRing R]

theorem exists_le_associated_of_dvd_prod_primes [IsDomain R] {ι : Type*} (f : ι → R) :
    ∀ (s : Multiset ι), (∀ i ∈ s, Prime (f i)) → ∀ {x : R}, x ∣ (s.map f).prod →
      ∃ t ≤ s, Associated x (t.map f).prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro _ x hx
    refine ⟨0, le_refl _, ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero] at hx ⊢
    exact associated_one_iff_isUnit.2 (isUnit_of_dvd_one hx)
  | cons a s ih =>
    intro hs x hx
    have ha : Prime (f a) := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ i ∈ s, Prime (f i) := fun i hi => hs i (Multiset.mem_cons_of_mem hi)
    rw [Multiset.map_cons, Multiset.prod_cons] at hx
    by_cases hax : f a ∣ x
    · obtain ⟨y, rfl⟩ := hax
      have hy : y ∣ (s.map f).prod := (mul_dvd_mul_iff_left ha.ne_zero).1 hx
      obtain ⟨t, ht, hyt⟩ := ih hs' hy
      refine ⟨a ::ₘ t, Multiset.cons_le_cons a ht, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact hyt.mul_left (f a)
    · obtain ⟨z, hz⟩ := hx
      have h1 : f a ∣ x * z := ⟨(s.map f).prod, hz.symm⟩
      have h2 : f a ∣ z := (ha.dvd_or_dvd h1).resolve_left hax
      obtain ⟨w, rfl⟩ := h2
      have h3 : (s.map f).prod = x * w := by
        apply mul_left_cancel₀ ha.ne_zero
        rw [hz]
        ring
      obtain ⟨t, ht, hxt⟩ := ih hs' ⟨w, h3⟩
      exact ⟨t, ht.trans (Multiset.le_cons_self s a), hxt⟩

theorem prime_of_regular_params [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (i : Fin n) : Prime (f i) := by
  have hm : f i ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  exact prime_of_not_mem_sq hm ((regular_params_spec f hspan hdim).1 i)

theorem eq_unit_mul_monomial [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) {x : R} (hx0 : x ≠ 0) (hrad : (∏ i ∈ J, f i) ∈ (Ideal.span {x}).radical) :
    ∃ (u : Rˣ) (m : Fin n → ℕ), (∀ i, i ∉ J → m i = 0) ∧ x = u * ∏ i ∈ J, f i ^ m i := by
  obtain ⟨k, hk⟩ := hrad
  rw [Ideal.mem_span_singleton] at hk
  have hprimes : ∀ i ∈ k • J.val, Prime (f i) := fun i _ => prime_of_regular_params f hspan hdim i
  have hprod : ((k • J.val).map f).prod = (∏ i ∈ J, f i) ^ k := by
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
    rfl
  rw [← hprod] at hk
  obtain ⟨t, ht, hxt⟩ := exists_le_associated_of_dvd_prod_primes f (k • J.val) hprimes hk
  have htJ : ∀ i, i ∉ J → Multiset.count i t = 0 := fun i hi => Multiset.count_eq_zero.2 fun hit =>
    hi (Multiset.mem_of_mem_nsmul (Multiset.mem_of_le ht hit))
  obtain ⟨u, hu⟩ := hxt.symm
  refine ⟨u, fun i => Multiset.count i t, htJ, ?_⟩
  rw [← hu, Finset.prod_multiset_map_count, mul_comm]
  congr 1
  apply Finset.prod_subset
  · intro i hi
    by_contra hiJ
    exact Multiset.count_ne_zero.2 (Multiset.mem_toFinset.1 hi) (htJ i hiJ)
  · intro i _ hi
    rw [Multiset.count_eq_zero.2 (fun h => hi (Multiset.mem_toFinset.2 h)), pow_zero]

theorem ord_localization_eq_exponent [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] :
    Ring.ord (Localization.AtPrime (Ideal.span {f i}))
        (algebraMap R (Localization.AtPrime (Ideal.span {f i})) (u * ∏ j ∈ J, f j ^ m j)) =
      (m i : ℕ∞) := by
  have : IsDomain R := isDomain_of_isRegularLocalRing
  set P := Ideal.span {f i} with hP
  set S := Localization.AtPrime P
  have hpr : ∀ j, Prime (f j) := prime_of_regular_params f hspan hdim

  have hout : ∀ j, j ≠ i → f j ∉ P := by
    intro j hji hj
    rw [hP, Ideal.mem_span_singleton] at hj
    obtain ⟨c, hc⟩ := hj
    have hdc : f j ∣ f i * c := ⟨1, by rw [mul_one, hc]⟩
    rcases (hpr j).dvd_or_dvd hdc with h | h
    · exact (regular_params_spec f hspan hdim).2 j i hji
        (associated_of_dvd_dvd h ⟨c, hc⟩)
    · obtain ⟨d, rfl⟩ := h
      have : f j * 1 = f j * (f i * d) := by linear_combination hc
      have h1 := mul_left_cancel₀ (hpr j).ne_zero this
      exact (hpr i).not_isUnit (isUnit_of_dvd_one ⟨d, h1⟩)
  have hunit : ∀ j, j ≠ i → IsUnit (algebraMap R S (f j)) := fun j hj =>
    IsLocalization.map_units S (⟨f j, hout j hj⟩ : P.primeCompl)
  set π := algebraMap R S (f i)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors P)
  have hπ0 : π ≠ 0 := fun h => (hpr i).ne_zero (hinj (by rw [map_zero]; exact h))
  have hπnzd : π ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hπ0
  have hmax : Ideal.span {π} = maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    show Ideal.span {π} = Ideal.map (algebraMap R S) (Ideal.span {f i})
    rw [Ideal.map_span, Set.image_singleton]
  have hord1 : Ring.ord S π = 1 := by
    unfold Ring.ord
    rw [hmax, Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  rw [← Finset.mul_prod_erase J _ hi, map_mul, map_mul, map_pow,
    Ring.ord_mul_of_isUnit_left ((Units.isUnit u).map _)]
  have hrest : IsUnit (algebraMap R S (∏ j ∈ J.erase i, f j ^ m j)) := by
    rw [map_prod]
    exact IsUnit.prod_iff.mpr fun j hj => by
      rw [map_pow]; exact (hunit j (Finset.ne_of_mem_erase hj)).pow _
  rw [Ring.ord_mul_of_isUnit_right hrest, Ring.ord_pow hπnzd, hord1, nsmul_eq_mul, mul_one]

end ReciprocityTheory.AnForm.R
end

