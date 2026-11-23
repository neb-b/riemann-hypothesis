module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentPolynomialOfIsAlgClose
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.LaurentUnits
open LaurentPolynomial Polynomial

variable (K : Type) [Field K]

theorem isDomain : IsDomain (LaurentPolynomial K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (X : K[X])) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)

theorem isPrincipalIdealRing : IsPrincipalIdealRing (LaurentPolynomial K) := by
  refine ⟨fun P => ?_⟩
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (P.comap (algebraMap K[X] (LaurentPolynomial K))))
  refine ⟨algebraMap K[X] (LaurentPolynomial K) g, ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (X : K[X])) (LaurentPolynomial K) P, Ideal.under_def, hg,
    Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

theorem units_eq (u : (LaurentPolynomial K)ˣ) :
    ∃ (c : K) (m : ℤ), (u : LaurentPolynomial K) = LaurentPolynomial.C c * T m := by
  obtain ⟨n, p, hp⟩ := exists_T_pow (u : LaurentPolynomial K)
  obtain ⟨n', r, hr⟩ := exists_T_pow ((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K)
  have hpr : p * r = X ^ (n + n') := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hr, Polynomial.toLaurent_X_pow]
    have : (u : LaurentPolynomial K) * T n * (((u⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) * T n')
        = T n * T n' := by
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul]
    rw [this, ← T_add]; push_cast; rfl
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X (n + n')).1 ⟨r, hpr.symm⟩
  obtain ⟨v, hv⟩ := hi.symm
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 v.isUnit
  refine ⟨c, (i : ℤ) - n, ?_⟩
  have h1 : (u : LaurentPolynomial K) * T n = LaurentPolynomial.C c * T i := by
    rw [← hp, ← hv, ← hc, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_comm]
  calc (u : LaurentPolynomial K) = (u : LaurentPolynomial K) * T n * T (-(n : ℤ)) := by
        rw [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
    _ = LaurentPolynomial.C c * T ((i : ℤ) - n) := by rw [h1, mul_assoc, ← T_add, sub_eq_add_neg]

theorem pic_subsingleton : Subsingleton (CommRing.Pic (LaurentPolynomial K)) := by
  haveI := isDomain K
  haveI := isPrincipalIdealRing K
  haveI := UniqueFactorizationMonoid.toGCDMonoid (LaurentPolynomial K)
  infer_instance

theorem isDedekindDomain : IsDedekindDomain (LaurentPolynomial K) := by
  haveI := isDomain K
  haveI := isPrincipalIdealRing K
  infer_instance

theorem laurent_monomial_exponent_eq {a b : ℤ} {c : K} (h : (T a : LaurentPolynomial K) = LaurentPolynomial.C c * T b) : a = b := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_mul] at h
    exact (isUnit_T (R := K) a).ne_zero h
  have h2 := congrArg LaurentPolynomial.degree h
  rw [degree_T, degree_C_mul_T _ _ hc] at h2
  exact WithBot.coe_inj.1 h2

theorem val_T_unit_zpow (m : ℤ) :
    ((((isUnit_T 1).unit : (LaurentPolynomial K)ˣ) ^ m : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = T m := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, ← T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    have : ((((isUnit_T 1).unit)⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = T (-1) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec, ← T_add]; simp
    rw [this, ← T_add]; ring_nf

end GlobalTheory.LaurentUnits

namespace GlobalTheory.GmAlgClosed
open LaurentPolynomial GlobalTheory.LaurentUnits

variable (q : ℕ) [NeZero q] (K : Type) [Field K]

noncomputable abbrev gEq : Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤) ≃+* LaurentPolynomial K :=
  (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial K))).commRingCatIsoToRingEquiv

theorem isUnit_q_L (hq : IsUnit (q : K)) : IsUnit (q : LaurentPolynomial K) := by
  simpa using hq.map (algebraMap K (LaurentPolynomial K))

theorem isUnit_q_Γ (hq : IsUnit (q : LaurentPolynomial K)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤)) := by
  simpa using hq.map (gEq K).symm.toRingHom

noncomputable def kumL (hq : IsUnit (q : LaurentPolynomial K)) :
    (LaurentPolynomial K)ˣ →* Multiplicative (Ht q (sp (LaurentPolynomial K)) 1 1) where
  toFun u := Multiplicative.ofAdd (kum q (Units.map (gEq K).symm.toRingHom.toMonoidHom u))
  map_one' := by
    have h := ((a6add_holds q).2 (1 : (Γ(Spec (CommRingCat.of (LaurentPolynomial K)), ⊤))ˣ) 1
      (isUnit_q_Γ q K hq)).1
    rw [mul_one] at h
    rw [map_one, ofAdd_eq_one]
    exact add_left_cancel (b := kum q _) (c := 0) (by rw [add_zero]; exact h.symm)
  map_mul' u v := by
    rw [map_mul, ((a6add_holds q).2 _ _ (isUnit_q_Γ q K hq)).1, ofAdd_add]

theorem kumL_pow_q (hq : IsUnit (q : LaurentPolynomial K)) (u : (LaurentPolynomial K)ˣ) :
    kumL q K hq (u ^ q) = 1 := by
  show Multiplicative.ofAdd (kum q _) = 1
  rw [map_pow, ((a6add_holds q).2 _ 1 (isUnit_q_Γ q K hq)).2, ofAdd_zero]

noncomputable abbrev tau : (LaurentPolynomial K)ˣ := (isUnit_T 1).unit

theorem zsmul_q (hq : IsUnit (q : LaurentPolynomial K)) :
    zmultiplesHom _ (Multiplicative.toAdd (kumL q K hq (tau K))) (q : ℤ) = 0 := by
  rw [zmultiplesHom_apply, natCast_zsmul, ← toAdd_pow, ← map_pow, kumL_pow_q, toAdd_one]

noncomputable def fL (hq : IsUnit (q : LaurentPolynomial K)) : ZMod q →+ Ht q (sp (LaurentPolynomial K)) 1 1 :=
  ZMod.lift q ⟨zmultiplesHom _ (Multiplicative.toAdd (kumL q K hq (tau K))), zsmul_q q K hq⟩

theorem fL_intCast (hq : IsUnit (q : LaurentPolynomial K)) (m : ℤ) :
    fL q K hq (m : ZMod q) = Multiplicative.toAdd (kumL q K hq (tau K ^ m)) := by
  rw [fL, ZMod.lift_coe]
  show zmultiplesHom _ _ m = _
  rw [zmultiplesHom_apply, map_zpow, toAdd_zpow]

variable [IsAlgClosed K]

theorem fL_surjective (hq : IsUnit (q : LaurentPolynomial K)) : Function.Surjective (fL q K hq) := by
  intro x
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree q (LaurentPolynomial K) hq
    (fun c _ => @Subsingleton.elim _ (pic_subsingleton K) _ _) x
  set u : (LaurentPolynomial K)ˣ := Units.map (gEq K).toRingHom.toMonoidHom u'
  have hu : Units.map (gEq K).symm.toRingHom.toMonoidHom u = u' := by ext; simp [u]
  obtain ⟨c, m, hcm⟩ := units_eq K u
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hcm
    exact u.ne_zero hcm
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero (NeZero.ne q))
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hc (by rw [← hd, zero_pow (NeZero.ne q)])
  set w : (LaurentPolynomial K)ˣ := Units.map (LaurentPolynomial.C : K →+* LaurentPolynomial K).toMonoidHom (Units.mk0 d hd0)
  have huw : u = w ^ q * tau K ^ m := by
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, val_T_unit_zpow, hcm, ← hd, map_pow]
    rfl
  refine ⟨(m : ZMod q), ?_⟩
  rw [fL_intCast, ← hu', ← hu]
  show _ = Multiplicative.toAdd (kumL q K hq u)
  rw [huw, map_mul, kumL_pow_q, one_mul]

theorem fL_injective (hq : IsUnit (q : LaurentPolynomial K)) : Function.Injective (fL q K hq) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have hz' : fL q K hq ((z.val : ℤ) : ZMod q) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hz
  rw [fL_intCast, zpow_natCast] at hz'
  obtain ⟨v, hv⟩ := GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial K) hq _ hz'
  have hv' : tau K ^ z.val = (Units.map (gEq K).toRingHom.toMonoidHom v) ^ q := by
    have := congrArg (Units.map (gEq K).toRingHom.toMonoidHom) hv
    rw [← map_pow, ← this]; ext; simp
  obtain ⟨c, k, hck⟩ := units_eq K (Units.map (gEq K).toRingHom.toMonoidHom v)
  have hT : (T (z.val : ℤ) : LaurentPolynomial K) = LaurentPolynomial.C (c ^ q) * T ((q : ℤ) * k) := by
    have := congrArg (fun w : (LaurentPolynomial K)ˣ => (w : LaurentPolynomial K)) hv'
    simp only [Units.val_pow_eq_pow_val, hck, IsUnit.unit_spec, T_pow, mul_one, mul_pow, map_pow] at this
    rw [map_pow]; exact this
  have he := laurent_monomial_exponent_eq K hT
  have hlt : ((z.val : ℕ) : ℤ) < q := by exact_mod_cast ZMod.val_lt z
  have hq0 : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h0 : ((z.val : ℕ) : ℤ) = 0 := by
    rcases le_or_gt k 0 with hk | hk
    · nlinarith
    · nlinarith
  exact (ZMod.val_eq_zero z).1 (by exact_mod_cast h0)

theorem exists_root_L (hq : IsUnit (q : K)) :
    ∃ ζ : LaurentPolynomial K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q K) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne')
  refine ⟨algebraMap K _ ζ, ?_⟩
  rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    Polynomial.map_cyclotomic, hζ.eq_zero, map_zero]

end GlobalTheory.GmAlgClosed

theorem GlobalTheory.EtC.gm_algClosed_cohomology : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial K)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial K)) 1 i ≃+ ZMod q) := by
  intro q _ K _ _ hq n i
  haveI := GlobalTheory.LaurentUnits.isDedekindDomain K
  refine ⟨fun hn => GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (LaurentPolynomial K) hq n i hn, ?_⟩
  have hqL := GlobalTheory.GmAlgClosed.isUnit_q_L q K hq
  obtain ⟨e1⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (LaurentPolynomial K) hqL (GlobalTheory.GmAlgClosed.exists_root_L q K hq) 1 i 1
  exact ⟨e1.trans (AddEquiv.ofBijective _
    ⟨GlobalTheory.GmAlgClosed.fL_injective q K hqL, GlobalTheory.GmAlgClosed.fL_surjective q K hqL⟩).symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySubsingletonEtaleOverPolynomi
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtAlgCD

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem subsingleton_of_ringEquiv (q : ℕ) (d i : ℤ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Subsingleton (Ht q (sp A) d i)] : Subsingleton (Ht q (sp B) d i) := by
  constructor
  intro x y
  have h : ∀ z : Ht q (sp B) d i,
      pull _ (spMap (e : A →+* B)) _ _ (pull _ (spMap (e.symm : B →+* A)) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  rw [← h x, ← h y, Subsingleton.elim (pull _ (spMap (e.symm : B →+* A)) _ _ x) (pull _ _ _ _ y)]

theorem subsingleton_prod (q : ℕ) (d i : ℤ) (A B : Type) [CommRing A] [CommRing B]
    [Subsingleton (Ht q (sp A) d i)] [Subsingleton (Ht q (sp B) d i)] :
    Subsingleton (Ht q (sp (A × B)) d i) := by
  constructor
  intro x y
  exact (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B d i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem subsingleton_of_subsingleton_ring (q : ℕ) (d i : ℤ) (A : Type) [CommRing A] [Subsingleton A] :
    Subsingleton (Ht q (sp A) d i) := by
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A A d i).2 (a, b)
  have hfs : RingHom.fst A A = RingHom.snd A A := RingHom.ext fun _ => Subsingleton.elim _ _
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2, hfs]

def piFinSuccRingEquiv (n : ℕ) (B : Fin (n + 1) → Type) [∀ j, CommRing (B j)] :
    (∀ j, B j) ≃+* B 0 × ∀ j : Fin n, B j.succ where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem subsingleton_pi (q : ℕ) (d i : ℤ) : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)],
    (∀ j, Subsingleton (Ht q (sp (B j)) d i)) → Subsingleton (Ht q (sp (∀ j, B j)) d i) := by
  intro n
  induction n with
  | zero =>
    intro B _ _
    exact subsingleton_of_subsingleton_ring q d i _
  | succ n ih =>
    intro B _ hB
    have := ih (fun j => B j.succ) (fun j => hB j.succ)
    have := hB 0
    have := subsingleton_prod q d i (B 0) (∀ j : Fin n, B j.succ)
    exact subsingleton_of_ringEquiv q d i (piFinSuccRingEquiv n B).symm

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD


open Polynomial in
theorem dimensionLEOne_of_etale (K E : Type) [Field K] [CommRing E] [IsDomain E] [Algebra K[X] E]
    [Algebra.Etale K[X] E] : Ring.DimensionLEOne E := by
  have h1 : ringKrullDim E ≤ 1 := by
    refine (GlobalTheory.AffineCover.ringKrullDim_le_of_quasiFinite K[X] E).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  refine ⟨fun {p} hp0 hp => ?_⟩
  have h2 := Order.krullDim_le_one_iff.1 h1 ⟨p, hp⟩
  rcases h2 with h | h
  · exfalso
    have := h (show (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) ≤ ⟨p, hp⟩ from bot_le)
    exact hp0 (le_bot_iff.1 this)
  · obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
    have := h (show (⟨p, hp⟩ : PrimeSpectrum E) ≤ ⟨m, hm.isPrime⟩ from hpm)
    have hmp : m ≤ p := this
    exact (le_antisymm hpm hmp) ▸ hm

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD


open Polynomial in
theorem subsingleton_of_domain (hcurve : GlobalTheory.EtC.C2) (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K]
    [CommRing E] [IsDomain E] [Algebra K[X] E] [Algebra.Etale K[X] E] (hq : IsUnit (q : K))
    (n i : ℤ) (hn : 2 ≤ n) : Subsingleton (Ht q (sp E) n i) := by
  letI : Algebra K E := ((algebraMap K[X] E).comp (algebraMap K K[X])).toAlgebra
  haveI : IsScalarTower K K[X] E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType K E := Algebra.FiniteType.trans (S := K[X]) inferInstance inferInstance
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing K[X] E
  haveI : IsIntegrallyClosed E := GlobalTheory.isIntegrallyClosed_of_smooth K[X] E
  haveI : Ring.DimensionLEOne E := dimensionLEOne_of_etale K E
  haveI : IsDedekindDomain E := {}
  exact hcurve q K E hq n i hn

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD

theorem isCoprime_of_minimalPrimes {E : Type} [CommRing E]
    (hloc : ∀ (p : Ideal E) [p.IsPrime], IsDomain (Localization.AtPrime p))
    {p q : Ideal E} (hp : p ∈ minimalPrimes E) (hq : q ∈ minimalPrimes E) (hpq : p ≠ q) :
    IsCoprime p q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hloc m
  let P0 : Ideal E := (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap E (Localization.AtPrime m))
  haveI : P0.IsPrime := Ideal.comap_isPrime _ _
  have key : ∀ r : Ideal E, r ∈ minimalPrimes E → r ≤ m → r = P0 := by
    intro r hr hrm
    have hsub : P0 ≤ r := by
      intro x hx
      have hx0 : algebraMap E (Localization.AtPrime m) x = 0 := hx
      obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 hx0
      have hsr : s ∉ r := fun h => hs (hrm h)
      have : s * x ∈ r := by rw [hsx]; exact r.zero_mem
      exact (hr.1.1.mem_or_mem this).resolve_left hsr
    exact le_antisymm (hr.2 ⟨inferInstance, bot_le⟩ hsub) hsub
  exact hpq ((key p hp (le_sup_left.trans hle)).trans (key q hq (le_sup_right.trans hle)).symm)

theorem isLocalizationAway_of_pi {E ι : Type} [CommRing E] [DecidableEq ι] (f : ι → Ideal E)
    (Φ : E ≃+* ∀ j, E ⧸ f j) (hΦ : ∀ x j, Φ x j = Ideal.Quotient.mk (f j) x) (j : ι) :
    IsLocalization.Away (Φ.symm (Pi.single j 1)) (E ⧸ f j) := by
  set e := Φ.symm (Pi.single j 1) with he
  have hΦe : Φ e = Pi.single j 1 := by simp [e]
  have hid : IsIdempotentElem e := by
    apply Φ.injective
    rw [map_mul, hΦe]
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  refine IsLocalization.away_of_isIdempotentElem hid ?_ Ideal.Quotient.mk_surjective
  change RingHom.ker (Ideal.Quotient.mk (f j)) = _
  rw [Ideal.mk_ker]
  apply le_antisymm
  · intro x hx
    have : x = x * (1 - e) := by
      apply Φ.injective
      ext k
      rw [map_mul, map_sub, map_one, hΦe]
      by_cases hk : k = j
      · subst hk
        have h0 : Φ x k = 0 := by rw [hΦ]; exact Ideal.Quotient.eq_zero_iff_mem.2 hx
        simp [h0]
      · simp [Pi.single_eq_of_ne hk]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change 1 - e ∈ f j
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hΦ, map_sub, map_one, hΦe]
    simp

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD


open Polynomial in
theorem etale_polynomial_cd_le_one : ∀ (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K]
    [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E], IsUnit (q : K) →
    ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp E) n i) := by
  classical
  intro q _ K E _ _ _ _ _ hq n i hn
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing K[X] E
  haveI : IsReduced E := GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed K[X] E
  have hloc : ∀ (p : Ideal E) [p.IsPrime], IsDomain (Localization.AtPrime p) := fun p _ =>
    (GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale K[X] p _).1
  let ι := {p : Ideal E // p ∈ minimalPrimes E}
  haveI : Finite ι := (minimalPrimes.finite_of_isNoetherianRing E).to_subtype
  letI : Fintype ι := Fintype.ofFinite ι
  let f : ι → Ideal E := Subtype.val
  have hcop : Pairwise (Function.onFun IsCoprime f) := fun a b hab =>
    isCoprime_of_minimalPrimes hloc a.2 b.2 (fun h => hab (Subtype.ext h))
  have hinf : ⨅ j, f j = ⊥ := by
    have h1 : ⨅ j, f j = sInf (minimalPrimes E) := (sInf_eq_iInf' (minimalPrimes E)).symm
    rw [h1]
    change sInf (Ideal.minimalPrimes ⊥) = ⊥
    rw [Ideal.sInf_minimalPrimes]
    exact nilradical_eq_zero E
  let ψ : E →+* ∀ j, E ⧸ f j := RingHom.pi fun j => Ideal.Quotient.mk (f j)
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ ⨅ j, f j := Ideal.mem_iInf.2 fun j => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hx j)
    rwa [hinf, Ideal.mem_bot] at this
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨z, rfl⟩ := (Ideal.quotientInfRingEquivPiQuotient f hcop).surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, by ext j; first | rfl | simp [ψ, Ideal.quotientInfRingEquivPiQuotient, Ideal.quotientInfToPiQuotient]⟩
  let Φ : E ≃+* ∀ j, E ⧸ f j := RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hfac : ∀ j, Subsingleton (Ht q (sp (E ⧸ f j)) n i) := by
    intro j
    haveI : (f j).IsPrime := j.2.1.1
    haveI : IsLocalization.Away (Φ.symm (Pi.single j 1)) (E ⧸ f j) :=
      isLocalizationAway_of_pi f Φ (fun x j => rfl) j
    haveI : Algebra.Etale E (E ⧸ f j) := Algebra.Etale.of_isLocalizationAway (Φ.symm (Pi.single j 1))
    haveI : Algebra.Etale K[X] (E ⧸ f j) := Algebra.Etale.comp K[X] E _
    exact subsingleton_of_domain GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (E ⧸ f j) hq n i hn
  let σ := (Fintype.equivFin ι).symm
  haveI := subsingleton_pi q n i (Fintype.card ι) (fun k => E ⧸ f (σ k)) (fun k => hfac (σ k))
  haveI := subsingleton_of_ringEquiv q n i (RingEquiv.piCongrLeft (fun j => E ⧸ f j) σ)
  exact subsingleton_of_ringEquiv q n i Φ.symm

end GlobalTheory.EtAlgCD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodic
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem thV_invV_eq : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec
  have hC' := hC
  obtain ⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩ := hC'
  funext w
  obtain ⟨x, y⟩ := w
  let P : (Fin N → AF F) → ℂ := fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))
  have hPc : Continuous P := by
    refine (hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)
    refine (continuous_const.mul ?_).neg
    fun_prop
  have hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u := fun ξ u => integrand_periodic hq x u ξ
  have hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) =
      invV ψ ν 𝓓 f (rat ξ + x) := by
    intro ξ
    unfold invV
    congr 1
    funext u
    have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
    have h := hq ξ 0 (x, u)
    rw [h0, Prod.mk_add_mk, zero_add] at h
    rw [h, Bd_half]
    simp only [P]
    rw [mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]
    linear_combination two_mul_invOf (rat ξ ⬝ᵥ u)
  have hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖) :=
    (GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x
  have hser := GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P
    (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y
  have hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) := by
    simp only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  rw [hfxy, hser, ← tsum_mul_right]
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  refine tsum_congr fun ξ => ?_
  show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _
  rw [Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]
  ring

end GlobalTheory.ThetaTransform
end

