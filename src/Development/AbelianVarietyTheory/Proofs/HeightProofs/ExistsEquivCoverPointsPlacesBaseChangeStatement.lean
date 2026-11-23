module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEquivCoverPointsPlacesBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open IsLocalRing GlobalTheory GlobalTheory.ResDegPlace in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_coverPoints_places_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Finite ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif (A := A) ϖ → ∀ [∀ ζ : Pts R' A, IsDVRAt ζ] (Ψ : ∀ c, A →ₐ[R'] F' ⊗[F] L c), (∀ c, Function.Surjective (Ψ c)) → (∀ a, (∀ c, Ψ c a = 0) → a = 0) → (∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1) → ∃ e : Pts R' A ≃ Σ c, ValPl.PlacesOver R (L c), ∀ ζ, fdeg ζ = (letI := resAlg (F := F) (e ζ).2.1; Module.finrank (IsLocalRing.ResidueField ((vRing (e ζ).2.1).comap (algebraMap F (L (e ζ).1)))) (IsLocalRing.ResidueField (vRing (e ζ).2.1))) ∧ ∃ u : AddValuation (F' ⊗[F] L (e ζ).1) (WithTop ℤ), (∀ g, u ((1 : F') ⊗ₜ[F] g) = (e ζ).2.1 g) ∧ ∀ a, ord ϖ ζ a = u (Ψ (e ζ).1 a) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres ι _ L _ _ _ _ _ _ A _ _ ϖ hϖ hD Ψ
    hsurj hinj hsep
  have ord_pos_iff (h : IsUnif (A := A) ϖ) (ζ : Pts R' A) [IsDVRAt ζ] (a : As R' A) :
      0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
    rw [ord_of_mem ζ h a.2, ← not_iff_not, ← vL_eq_zero_iff]
    change ¬ 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
    generalize vL ζ a = v
    cases v with
    | top => simp
    | coe j =>
      rw [ENat.map_natCast, ← WithTop.coe_zero, WithTop.coe_lt_coe]
      simp
  have surjective_of_detect [∀ ζ : Pts R' A, IsDVRAt ζ] (h : IsUnif (A := A) ϖ) {T : Type} [Finite T]
      (Z : T → Pts R' A) (hZ : ∀ x, (∀ t, 0 ≤ ord ϖ (Z t) x) → x ∈ As R' A) :
      Function.Surjective Z := by
    classical
    cases nonempty_fintype T
    intro ζ
    by_contra hne
    have hex : ∀ t, ∃ a ∈ (Z t).asIdeal, a ∉ ζ.asIdeal := by
      intro t
      by_contra hc
      push Not at hc
      exact hne ⟨t, MaximalSpectrum.ext ((Z t).isMaximal.eq_of_le ζ.isMaximal.ne_top hc)⟩
    choose a ha ha' using hex
    have := ζ.isMaximal.isPrime
    have hb : ∏ t, a t ∉ ζ.asIdeal := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨t, -, ht⟩
      exact ha' t ht
    have hbt : ∀ t, ∏ t, a t ∈ (Z t).asIdeal := fun t =>
      Ideal.prod_mem _ (Finset.mem_univ t) (ha t)
    generalize ∏ t, a t = b at hb hbt
    obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
    set n : ℕ := ∑ t, ep ϖ (Z t) with hn
    have hx : v * (b : A) ^ n ∈ As R' A := by
      apply hZ
      intro t
      have h1 : ord ϖ (Z t) (algebraMap R' A ϖ * (v * (b : A) ^ n)) = n • ord ϖ (Z t) b := by
        rw [← mul_assoc, hv, one_mul, ord_pow _ h]
      rw [ord_mul _ h, ord_unif _ h] at h1
      have h2 := (ord_pos_iff h (Z t) b).2 (hbt t)
      have h3 : ep ϖ (Z t) ≤ n :=
        Finset.single_le_sum (f := fun t => ep ϖ (Z t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      have h4 := ep_pos (Z t) h
      generalize ord ϖ (Z t) (v * (b : A) ^ n) = p at h1
      generalize ord ϖ (Z t) (b : A) = q at h1 h2
      generalize ep ϖ (Z t) = e at h1 h3 h4
      induction p using WithTop.recTopCoe with
      | top => exact le_top
      | coe p =>
        induction q using WithTop.recTopCoe with
        | top =>
          obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [hm, succ_nsmul, add_top, ← WithTop.coe_add] at h1
          exact absurd h1 WithTop.coe_ne_top
        | coe q =>
          rw [← WithTop.coe_add, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at h1
          have h5 : 0 < q := by exact_mod_cast h2
          have h6 : (e : ℤ) ≤ n := by exact_mod_cast h3
          have h7 : 0 ≤ p := by nlinarith
          exact_mod_cast h7
    have hp : b ^ n = algebraMap R' (As R' A) ϖ * ⟨_, hx⟩ := by
      apply Subtype.ext
      change (b : A) ^ n = algebraMap R' A ϖ * (v * (b : A) ^ n)
      rw [← mul_assoc, hv, one_mul]
    exact hb (ζ.isMaximal.isPrime.mem_of_pow_mem n (hp ▸ Ideal.mul_mem_right _ _ (unif_mem h ζ)))
  choose w' hw1 hw2 hw3 hw4 using fun c =>
    exists_unique_place_baseChange R R' F F' hmax hres (L c)
      (isIntegral_iff_mem_span_one_tmul_integralClosure R R' F F' hmax hres (L c))
  have existsPoint (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ As R' A, 0 ≤ u a)
      (hpos : 0 < u (algebraMap R' A ϖ)) (h1 : ∃ a, u a = 1) :
      ∃ ζ : Pts R' A, ∀ a, ord ϖ ζ a = u a := by
    have hP := valCentreOn_isPrime (As R' A) u h0
    have hcm : ((valCentreOn (As R' A) u h0).comap (algebraMap R' (As R' A))).IsMaximal := by
      have hle : IsLocalRing.maximalIdeal R' ≤
          (valCentreOn (As R' A) u h0).comap (algebraMap R' (As R' A)) := by
        rw [hϖ.irreducible.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
          mem_valCentreOn]
        exact hpos
      have := (IsLocalRing.maximalIdeal.isMaximal R').eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
      rw [← this]
      infer_instance
    have hmax : (valCentreOn (As R' A) u h0).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R') _ hcm
    let ζ : Pts R' A := ⟨valCentreOn (As R' A) u h0, hmax⟩
    have hz : ∀ s : As R' A, s ∉ ζ.asIdeal → u (s : A) = 0 := fun s hs =>
      le_antisymm (not_lt.1 hs) (h0 _ s.2)
    refine ⟨ζ, ?_⟩
    have hζDVR : IsDVRAt ζ := hD ζ
    have : IsDomain (Loc ζ) := hζDVR.isDomain
    have : IsDiscreteValuationRing (Loc ζ) := hζDVR.isDVR
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
    obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj ζ.asIdeal.primeCompl p
    have hπ : Irreducible (algebraMap (As R' A) (Loc ζ) π) := by
      have ht : IsUnit (algebraMap (As R' A) (Loc ζ) t) := IsLocalization.map_units _ t
      have : Associated p (algebraMap (As R' A) (Loc ζ) π) := ⟨ht.unit, hπt⟩
      exact this.irreducible hp
    have hπpos : 0 < u (π : A) := by
      by_contra hc
      exact hπ.not_isUnit ((IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal π).2 hc)
    have key : ∀ a : As R' A, (vL ζ a = ⊤ ∧ u (a : A) = ⊤) ∨
        ∃ n : ℕ, vL ζ a = n ∧ u (a : A) = n • u (π : A) := by
      intro a
      by_cases ha : algebraMap (As R' A) (Loc ζ) a = 0
      · refine Or.inl ⟨(vL_eq_top_iff ζ a).2 ha, ?_⟩
        rw [addVal_eq_of_associated_loc ζ u hz a 0 (by rw [ha, map_zero])]
        simp
      · obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
        refine Or.inr ⟨n, ?_, ?_⟩
        · rw [vL_eq_addVal]
          exact IsDiscreteValuationRing.addVal_def _ w hπ n hw
        · rw [addVal_eq_of_associated_loc ζ u hz a (π ^ n)
            (by rw [hw, map_pow]; exact associated_unit_mul_left _ _ w.isUnit)]
          rw [SubmonoidClass.coe_pow, u.map_pow]
    have hϖtop : u (algebraMap R' A ϖ) ≠ ⊤ := by
      intro ht
      obtain ⟨v, hv⟩ := hϖ.isUnit.exists_right_inv
      have := congrArg u hv
      rw [u.map_mul, ht, top_add, u.map_one] at this
      exact WithTop.top_ne_zero this
    have hϖe : u (algebraMap R' A ϖ) = ep ϖ ζ • u (π : A) := by
      rcases key (algebraMap R' (As R' A) ϖ) with ⟨_, h2⟩ | ⟨n, h2, h3⟩
      · exact absurd h2 hϖtop
      · rw [← coe_ep ζ hϖ, Nat.cast_inj] at h2
        rw [h2]
        exact h3
    have hmtop : u (π : A) ≠ ⊤ := by
      intro ht
      apply hϖtop
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ hϖ).ne'
      rw [hϖe, hk, succ_nsmul, ht, add_top]
    obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.1 hmtop
    have hM0 : 0 < M := by
      rw [← hM] at hπpos
      exact_mod_cast hπpos
    have key2 : ∀ x : A, (ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
        ∃ z : ℤ, ord ϖ ζ x = z ∧ u x = ((z * M : ℤ) : WithTop ℤ) := by
      intro x
      obtain ⟨k, hk⟩ := hϖ.denom x
      have e1 := ord_pow_smul ζ hϖ k x
      rw [ord_of_mem ζ hϖ hk] at e1
      have e2 : u (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) * M : ℤ) : WithTop ℤ) + u x := by
        rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖe, ← hM, ← WithTop.coe_nsmul,
          ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_assoc]
      rcases key ⟨_, hk⟩ with ⟨h2, h3⟩ | ⟨n, h2, h3⟩
      · left
        rw [h2, ENat.map_top, eq_comm, WithTop.add_eq_top] at e1
        change u (ϖ ^ k • x) = ⊤ at h3
        rw [h3, eq_comm, WithTop.add_eq_top] at e2
        exact ⟨e1.resolve_left WithTop.coe_ne_top, e2.resolve_left WithTop.coe_ne_top⟩
      · right
        rw [h2, ENat.map_natCast] at e1
        change u (ϖ ^ k • x) = _ at h3
        rw [h3, ← hM, ← WithTop.coe_nsmul, nsmul_eq_mul] at e2
        refine ⟨n - k * ep ϖ ζ, ?_, ?_⟩
        · generalize ord ϖ ζ x = y at e1
          cases y with
          | top => simp at e1
          | coe y =>
            rw [← WithTop.coe_add, WithTop.coe_inj] at e1
            rw [WithTop.coe_inj]
            linarith
        · generalize u x = y at e2
          cases y with
          | top => exact absurd (e2.trans (add_top _)) WithTop.coe_ne_top
          | coe y =>
            rw [← WithTop.coe_add, WithTop.coe_inj] at e2
            rw [WithTop.coe_inj]
            linarith
    have hM1 : M = 1 := by
      obtain ⟨a, ha⟩ := h1
      rcases key2 a with ⟨_, h3⟩ | ⟨z, _, h3⟩
      · rw [ha] at h3
        exact absurd h3 WithTop.one_ne_top
      · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h3
        exact Int.eq_one_of_mul_eq_one_left hM0.le h3.symm
    intro a
    rcases key2 a with ⟨h2, h3⟩ | ⟨z, h2, h3⟩
    · rw [h2, h3]
    · rw [h2, h3, hM1, mul_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∀ t : Σ c, ValPl.PlacesOver R (L c), ∃ ζ : Pts R' A,
      ∀ a, ord ϖ ζ a = w' t.1 t.2 (Ψ t.1 a) := by
    rintro ⟨c, w⟩
    refine existsPoint ((w' c w).comap (Ψ c).toRingHom) ?_ ?_ ?_
    · intro a ha
      exact (hw2 c _).1 (IsIntegral.map (Ψ c) ha) w
    · have hm : ϖ ∈ Ideal.span {algebraMap R R' π} := by
        rw [← PlaceExt.maximalIdeal_eq_span hmax hπ]
        exact hϖ.irreducible.not_isUnit
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
      change 0 < w' c w (Ψ c (algebraMap R' A ϖ))
      rw [AlgHom.commutes, ← hr, map_mul, AddValuation.map_mul, PlaceExt.algebraMap_eq_one_tmul,
        hw1]
      exact lt_of_lt_of_le ((w.2.2 π).2.2 hπ.not_isUnit)
        (le_add_of_nonneg_left ((hw2 c _).1 isIntegral_algebraMap w))
    · obtain ⟨g, hg⟩ := w.2.1.2
      obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
      refine ⟨a, ?_⟩
      change w' c w (Ψ c a) = 1
      rw [ha, hw1, hg]
  choose Z hZ using hex
  have hZinj : Function.Injective Z := by
    rintro ⟨c, w⟩ ⟨c', w₂⟩ he
    have h1 : ∀ a, w' c w (Ψ c a) = w' c' w₂ (Ψ c' a) := fun a => by
      rw [← hZ ⟨c, w⟩ a, he, hZ]
    obtain rfl : c = c' := by
      by_contra hc
      obtain ⟨a, h0, h1'⟩ := hsep c c' hc
      have := h1 a
      rw [h0, h1', AddValuation.map_zero, AddValuation.map_one] at this
      exact WithTop.top_ne_zero this
    congr 1
    apply Subtype.ext
    apply AddValuation.ext
    intro g
    obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
    rw [← hw1, ← hw1, ← ha, h1]
  have : ∀ c, Finite (ValPl.PlacesOver R (L c)) := fun c => by
    have := integralClosure.isDedekindDomain R F (L c)
    have := integralClosure.isFractionRing_of_finite_extension (A := R) F (L c)
    exact (ValPl.placesOver_finite (O := R) (F := F) (L := L c)).to_subtype
  have hZsurj : Function.Surjective Z := by
    refine surjective_of_detect hϖ Z fun x hx => ?_
    refine CoverPlaces.isIntegral_of_forall Ψ hinj x fun c => (hw2 c _).2 fun w => ?_
    have := hx ⟨c, w⟩
    rwa [hZ] at this
  refine ⟨(Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm, fun ζ => ?_⟩
  have hζ : Z ((Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ) = ζ :=
    (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).apply_symm_apply ζ
  generalize (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ = t at hζ ⊢
  subst hζ
  obtain ⟨c, w⟩ := t
  refine ⟨?_, w' c w, hw1 c w, hZ ⟨c, w⟩⟩
  have existsApprox (ζ : Pts R' A) [IsDVRAt ζ] (x : A) (hx : 0 ≤ ord ϖ ζ x) :
      ∃ a : As R' A, 0 < ord ϖ ζ ((a : A) - x) := by
    obtain ⟨n, hn⟩ := hϖ.denom x
    have h1 := hx
    rw [ord_eq ζ hϖ hn, ordAt_nonneg_iff ζ hϖ, vL_eq_addVal, vL_eq_addVal,
      IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c
    have h2 : algebraMap (As R' A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As R' A)) =
        algebraMap (As R' A) (Loc ζ) (algebraMap R' (As R' A) ϖ ^ n * b) := by
      rw [map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
    have h3 : (algebraMap R' A ϖ) ^ n * ((((t : As R' A) : A) * ((s : As R' A) : A)) * x) =
        (algebraMap R' A ϖ) ^ n * (((t : As R' A) : A) * (b : A)) := by
      have := congrArg Subtype.val ht
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this
      have e : ((algebraMap R' (As R' A) ϖ : As R' A) : A) = algebraMap R' A ϖ := rfl
      rw [e] at this
      linear_combination this
    have h4 := (hϖ.isUnit.pow n).mul_right_inj.1 h3
    obtain ⟨d, i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2
    refine ⟨d * (t * b), ?_⟩
    have h5 : ((d * (t * b) : As R' A) : A) - x = ((-i : As R' A) : A) * x := by
      have := congrArg Subtype.val hdi
      simp only [AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
        NegMemClass.coe_neg] at this ⊢
      linear_combination x * this - (d : A) * h4
    rw [h5, ord_mul ζ hϖ]
    exact add_pos_of_pos_of_nonneg ((ord_pos_iff hϖ ζ _).2 (ζ.asIdeal.neg_mem hi)) hx
  have residueDegree {K : Type} [Field K] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
      (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation K (WithTop ℤ)) (hw : w ∈ ValPl.PlacesOver R K)
      {S : Type} [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (jK : K →+* S)
      (hΨ : Function.Surjective Ψ)
      (hcomp : ∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = jK (algebraMap R K r))
      (hι : ∀ g, u (jK g) = w g) (hord : ∀ a, ord ϖ ζ a = u (Ψ a))
      (happrox : ∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - jK g)) :
      fdeg ζ = (letI := resAlg (F := F) w
        Module.finrank (ResidueField ((vRing w).comap (algebraMap F K))) (ResidueField (vRing w))) := by
    let := resAlg (F := F) w
    let T : Subring (As R' A × vRing w) :=
      { carrier := {z | 0 < u (Ψ (z.1 : A) - jK (z.2 : K))}
        mul_mem' := by
          intro z z' hz hz'
          change 0 < u (Ψ ((z.1 : A) * z'.1) - jK ((z.2 : K) * z'.2))
          have e : Ψ ((z.1 : A) * z'.1) - jK ((z.2 : K) * z'.2) =
              (Ψ (z'.1 : A) - jK (z'.2 : K)) * Ψ z.1 + (Ψ (z.1 : A) - jK (z.2 : K)) * jK z'.2 := by
            rw [map_mul, map_mul]; ring
          rw [e]
          refine u.map_lt_add ?_ ?_
          · rw [u.map_mul, ← hord]
            exact add_pos_of_pos_of_nonneg hz' (ord_nonneg ζ hϖ z.1.2)
          · rw [u.map_mul, hι]
            exact add_pos_of_pos_of_nonneg hz z'.2.2
        one_mem' := by
          change 0 < u (Ψ 1 - jK 1)
          simp
        add_mem' := by
          intro z z' hz hz'
          change 0 < u (Ψ ((z.1 : A) + z'.1) - jK ((z.2 : K) + z'.2))
          rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
          exact u.map_lt_add hz hz'
        zero_mem' := by
          change 0 < u (Ψ 0 - jK 0)
          simp
        neg_mem' := by
          intro z hz
          change 0 < u (Ψ (-(z.1 : A)) - jK (-(z.2 : K)))
          rw [map_neg, map_neg, ← neg_sub', u.map_neg]
          exact hz }
    have hT : ∀ z : T, 0 < u (Ψ (z.1.1 : A) - jK (z.1.2 : K)) := fun z => z.2
    let jw : R →+* vRing w := (algebraMap R K).codRestrict (vRing w) (fun r => (hw.2 r).1)
    let j : R →+* T := (((algebraMap R' (As R' A)).comp (algebraMap R R')).prod jw).codRestrict T
      (fun r => by
        change 0 < u (Ψ (algebraMap R' A (algebraMap R R' r)) - jK (algebraMap R K r))
        rw [hcomp, sub_self]; simp)
    have hOw : ∀ a : R, algebraMap R F a ∈ (vRing w).comap (algebraMap F K) := fun a => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact (hw.2 a).1
    let φ : R →+* (vRing w).comap (algebraMap F K) := (algebraMap R F).codRestrict _ hOw
    let p : T →+* ResidueField (Loc ζ) := ((residue (Loc ζ)).comp (algebraMap (As R' A) (Loc ζ))).comp
      ((RingHom.fst _ _).comp T.subtype)
    let q : T →+* ResidueField (vRing w) := (residue (vRing w)).comp
      ((RingHom.snd _ _).comp T.subtype)
    refine finrank_eq_of_surjective j ((residue R').comp (algebraMap R R')) ((residue _).comp φ) p q
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y
      obtain ⟨y, rfl⟩ := hres y
      obtain ⟨r, rfl⟩ := residue_surjective y
      exact ⟨r, rfl⟩
    · intro y
      obtain ⟨x, rfl⟩ := residue_surjective y
      obtain ⟨a, ha⟩ := exists_eq_of_nonneg hw (x : F) x.2
      exact ⟨a, congrArg (residue _) (Subtype.ext ha)⟩
    · intro y
      have := ζ.isMaximal
      obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective ζ.asIdeal y
      obtain ⟨g, hg, hag⟩ := happrox (Ψ a) (by rw [← hord]; exact ord_nonneg ζ hϖ a.2)
      exact ⟨⟨(a, ⟨g, hg⟩), hag⟩, rfl⟩
    · intro y
      obtain ⟨g, rfl⟩ := residue_surjective y
      obtain ⟨x, hx⟩ := hΨ (jK g)
      obtain ⟨a, ha⟩ := existsApprox ζ x (by rw [hord, hx, hι]; exact g.2)
      rw [hord, map_sub, hx] at ha
      exact ⟨⟨(a, g), ha⟩, rfl⟩
    · intro z
      change residue (Loc ζ) (algebraMap (As R' A) (Loc ζ) z.1.1) = 0 ↔ residue (vRing w) z.1.2 = 0
      rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal_vRing,
        IsLocalization.AtPrime.to_map_mem_maximal_iff (Loc ζ) ζ.asIdeal, ← ord_pos_iff hϖ, hord, ← hι]
      refine ⟨pos_of_sub_pos u ?_, pos_of_sub_pos u (hT z)⟩
      rw [← neg_sub, u.map_neg]
      exact hT z
    · intro r
      rfl
    · intro r
      change residue (vRing w) (comapIncl (vRing w) (algebraMap F K) (φ r)) = residue (vRing w) (jw r)
      congr 1
      exact Subtype.ext (IsScalarTower.algebraMap_apply R F K r).symm
  refine residueDegree _ w.1 w.2 (w' c w) (Ψ c).toRingHom
    (Algebra.TensorProduct.includeRight : L c →ₐ[F] F' ⊗[F] L c).toRingHom (hsurj c) ?_
    (hw1 c w) (hZ ⟨c, w⟩) (hw3 c w)
  intro r
  exact ((Ψ c).commutes _).trans (PlaceExt.algebraMap_eq_one_tmul r)
