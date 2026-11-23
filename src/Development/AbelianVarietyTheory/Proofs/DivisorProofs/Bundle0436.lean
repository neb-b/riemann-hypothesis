module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEq
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA.IntRep

open NumberField IsDedekindDomain in
open scoped Quaternion Topology in
private lemma coe_adicCompletionIntegers_inv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {x y : v.adicCompletionIntegers F} (h : x * y = 1) :
    (y : v.adicCompletion F) = (x : v.adicCompletion F)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  exact_mod_cast h

open IsDedekindDomain NumberField IsLocalRing in
open Polynomial in
private lemma exists_root_monic_quadratic_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)] (p q a₀ : R)
    (h : a₀ ^ 2 + p * a₀ + q ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (2 * a₀ + p)) :
    ∃ a : R, a ^ 2 + p * a + q = 0 ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨a, ha, haa⟩ := HenselianRing.is_henselian (X ^ 2 + (C p * X + C q))
    (monic_X_pow_add degree_linear_lt) a₀
    (by simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using h)
    (by
      have : eval a₀ (derivative (X ^ 2 + (C p * X + C q))) = 2 * a₀ + p := by
        simp [derivative_X_pow]; ring
      rw [this]; exact hu.map _)
  exact ⟨a, by simpa only [IsRoot, eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using ha,
    haa⟩

open IsDedekindDomain NumberField IsLocalRing in
open Polynomial in
private lemma exists_binary_form_eq_unit {O : Type*} [CommRing O] [IsLocalRing O]
    [HenselianRing O (maximalIdeal O)] [Finite (ResidueField O)] (t n u : O)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : O, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  have hu' := (residue_ne_zero_iff_isUnit u).2 hu
  by_cases h2 : IsUnit (2 : O)
  · have h2k : (2 : ResidueField O) ≠ 0 := by
      have := (residue_ne_zero_iff_isUnit (2 : O)).2 h2
      rwa [map_ofNat] at this
    set i : O := ↑h2.unit⁻¹ with hi_def
    have hi : 2 * i = 1 := h2.mul_val_inv
    set e : O := (t ^ 2 - 4 * n) * i ^ 2 with he_def
    have he : IsUnit e := hD.mul ((h2.unit⁻¹).isUnit.pow 2)
    have hek := (residue_ne_zero_iff_isUnit e).2 he
    haveI := Fintype.ofFinite (ResidueField O)
    have hchar : ringChar (ResidueField O) ≠ 2 := by
      intro h
      haveI := ringChar.eq_iff.mp h
      exact h2k (by simpa using CharP.cast_eq_zero (ResidueField O) 2)
    obtain ⟨α, σ, hασ⟩ := FiniteField.exists_root_sum_quadratic
      (f := X ^ 2 - C (residue O u)) (g := C (-(residue O e)) * X ^ 2)
      (degree_X_pow_sub_C (by norm_num) _) (degree_C_mul_X_pow 2 (neg_ne_zero.2 hek))
      (FiniteField.odd_card_of_char_ne_two hchar)
    obtain ⟨x₀, rfl⟩ := residue_surjective α
    obtain ⟨s₀, rfl⟩ := residue_surjective σ
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hασ
    have hm : x₀ ^ 2 - e * s₀ ^ 2 - u ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff]
      simp only [map_sub, map_mul, map_pow]
      linear_combination hασ
    have key : ∃ X s : O, X ^ 2 - e * s ^ 2 = u := by
      by_cases hx : IsUnit x₀
      · obtain ⟨X, hX, -⟩ := exists_root_monic_quadratic_henselian 0 (-(e * s₀ ^ 2 + u)) x₀
          (by convert hm using 1; ring) (by simpa using h2.mul hx)
        exact ⟨X, s₀, by linear_combination hX⟩
      · have hs : IsUnit s₀ := by
          by_contra hs
          rw [← residue_ne_zero_iff_isUnit, not_not] at hx hs
          apply hu'
          rw [hx, hs] at hασ
          linear_combination -hασ
        set E : O := ↑he.unit⁻¹ with hE_def
        have hE : e * E = 1 := he.mul_val_inv
        obtain ⟨s, hs', -⟩ := exists_root_monic_quadratic_henselian 0 (-(x₀ ^ 2 - u) * E) s₀
          (by
            have : s₀ ^ 2 + 0 * s₀ + -(x₀ ^ 2 - u) * E = -E * (x₀ ^ 2 - e * s₀ ^ 2 - u) := by
              linear_combination (-s₀ ^ 2) * hE
            rw [this]; exact Ideal.mul_mem_left _ _ hm)
          (by simpa using h2.mul hs)
        exact ⟨x₀, s, by linear_combination (-e) * hs' - (x₀ ^ 2 - u) * hE⟩
    obtain ⟨X, s, hXs⟩ := key
    exact ⟨X - t * s * i, s, by
      linear_combination hXs + (t ^ 2 * s ^ 2 * i - n * s ^ 2 * (1 + 2 * i) - t * X * s) * hi⟩
  · have h2k : (2 : ResidueField O) = 0 := by
      by_contra h
      exact h2 ((residue_ne_zero_iff_isUnit _).1 (by rwa [map_ofNat]))
    have h4 : (4 : ResidueField O) = 0 := by
      rw [show (4 : ResidueField O) = 2 * 2 by norm_num, h2k, zero_mul]
    have ht : IsUnit t := by
      rw [← residue_ne_zero_iff_isUnit] at hD ⊢
      intro h
      apply hD
      rw [map_sub, map_mul, map_pow, h, map_ofNat, h4]
      ring
    have hchar : ringChar (ResidueField O) = 2 :=
      CharP.ringChar_of_prime_eq_zero Nat.prime_two (by simpa using h2k)
    obtain ⟨ρ, hρ⟩ := FiniteField.isSquare_of_char_two hchar (residue O u)
    obtain ⟨r₀, rfl⟩ := residue_surjective ρ
    have hr₀ : IsUnit r₀ := by
      rw [← residue_ne_zero_iff_isUnit]
      rintro h
      rw [h, mul_zero] at hρ
      exact hu' hρ
    set c : O := r₀ ^ 2 - u with hc_def
    have hc : c ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, hc_def, map_sub, map_pow, hρ]
      ring
    have hb : IsUnit (t * r₀) := ht.mul hr₀
    set β : O := ↑hb.unit⁻¹ with hβ_def
    have hβ : t * r₀ * β = 1 := hb.mul_val_inv
    obtain ⟨w, hw, hw1⟩ := exists_root_monic_quadratic_henselian (-1) (n * β ^ 2 * c) 1
      (by
        have : (1 : O) ^ 2 + -1 * 1 + n * β ^ 2 * c = (n * β ^ 2) * c := by ring
        rw [this]; exact Ideal.mul_mem_left _ _ hc)
      (by norm_num)
    have hwu : IsUnit w := by
      rw [← residue_ne_zero_iff_isUnit]
      have := (residue_eq_zero_iff _).2 hw1
      rw [map_sub, map_one, sub_eq_zero] at this
      rw [this]; exact one_ne_zero
    set ω : O := ↑hwu.unit⁻¹ with hω_def
    have hω : w * ω = 1 := hwu.mul_val_inv
    exact ⟨r₀, -c * β * ω, by
      linear_combination (-c * ω) * hβ + (c * ω ^ 2) * hw + (-c * (w * ω + 1) + c * ω) * hω⟩


open NumberField IsDedekindDomain in
open scoped Quaternion Topology in
theorem _root_.GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F,
      ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b],
        _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧
          u.imK ∈ v.adicCompletionIntegers F := by
  intro F _ _ a b ha hb
  obtain ⟨α, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  obtain ⟨β, e, he, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) b
  have hα : α ≠ 0 := by rintro rfl; simp at ha
  have hβ : β ≠ 0 := by rintro rfl; simp at hb
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
  have hx0 : α * d * β * e * 2 ≠ 0 := by
    have : (2 : 𝓞 F) ≠ 0 := two_ne_zero
    positivity
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors (I := Ideal.span {α * d * β * e * 2})
    (by simpa using hx0)).subset fun v hv => ?_)
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hx
  apply hv
  haveI := _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hunit := (_root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 hx
  simp only [map_mul, IsUnit.mul_iff] at hunit
  obtain ⟨⟨⟨⟨hA, hD⟩, hB⟩, hE⟩, h2⟩ := hunit
  rw [map_ofNat] at h2
  set a' : v.adicCompletionIntegers F :=
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) α * ↑hD.unit⁻¹ with ha'_def
  set b' : v.adicCompletionIntegers F :=
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) β * ↑hE.unit⁻¹ with hb'_def
  have ha'K : (a' : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F α / algebraMap (𝓞 F) F d) := by
    rw [map_div₀, ha'_def, MulMemClass.coe_mul,
      coe_adicCompletionIntegers_inv v hD.mul_val_inv]
    rfl
  have hb'K : (b' : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F β / algebraMap (𝓞 F) F e) := by
    rw [map_div₀, hb'_def, MulMemClass.coe_mul,
      coe_adicCompletionIntegers_inv v hE.mul_val_inv]
    rfl
  have ha'u : IsUnit a' := hA.mul (hD.unit⁻¹).isUnit
  have hb'u : IsUnit b' := hB.mul (hE.unit⁻¹).isUnit
  set ai : v.adicCompletionIntegers F := ↑ha'u.unit⁻¹ with hai_def
  have hai : a' * ai = 1 := ha'u.mul_val_inv
  intro t ht
  set T : v.adicCompletionIntegers F := ⟨t, ht⟩ with hT
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletionIntegers F, IsUnit (T ^ 2 - 1 + a' * b' * z ^ 2) := by
    by_cases hc : IsUnit (T ^ 2 - 1)
    · exact ⟨0, by simpa using hc⟩
    · refine ⟨1, ?_⟩
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, not_not] at hc
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add (f := _), hc, zero_add, one_pow, mul_one]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (ha'u.mul hb'u)
  obtain ⟨r, s, hrs⟩ := exists_binary_form_eq_unit 0 (b' * ai) ((T ^ 2 - 1 + a' * b' * z ^ 2) * ai)
    (by
      rw [show (0 : v.adicCompletionIntegers F) ^ 2 - 4 * (b' * ai) = -(2 * 2 * (b' * ai)) by ring]
      exact ((h2.mul h2).mul (hb'u.mul (ha'u.unit⁻¹).isUnit)).neg)
    (hz.mul (ha'u.unit⁻¹).isUnit)
  have hO : T ^ 2 - a' * r ^ 2 - b' * s ^ 2 + a' * b' * z ^ 2 = 1 := by
    linear_combination (-a') * hrs + (b' * s ^ 2 - (T ^ 2 - 1) - a' * b' * z ^ 2) * hai
  refine ⟨⟨t, r, s, z⟩, ?_, rfl, r.2, s.2, z.2⟩
  unfold _root_.GlobalTheory.QSA.nrm
  rw [← ha'K, ← hb'K]
  have := congrArg (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) hO
  push_cast at this
  exact this

end GlobalTheory.QSA.IntRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyZmodTorsorGaloisProductMapBijectiveColStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (actA : Multiplicative (ZMod q) →* (A ≃ₐ[F.obj j] A)),
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj j] A) q (GlobalTheory.TorsorColim.bcAct c.pt actA)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj k) (F.obj k ⊗[F.obj j] A) q
        (GlobalTheory.TorsorColim.bcAct (F.obj k) actA)) := by
  first | (exact @GlobalTheory.TorsorColim.eventually_prodMapOf_bijective) | (exact GlobalTheory.TorsorColim.eventually_prodMapOf_bijective) | (intros; apply GlobalTheory.TorsorColim.eventually_prodMapOf_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLes
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LesChar

variable {R' : Type} [CommRing R']

theorem resAug_comm (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G = resAug F ≫ resMap R φ :=
  (InjectiveResolution.Hom.ι'_comp_hom'
    (⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
      InjectiveResolution.desc_commutes_zero φ _ _⟩ : InjectiveResolution.Hom _ _ φ)).symm

theorem mk_ofHom_eq {K L : Cx R'} {f g : K ⟶ L} (ho : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨-1, by omega, Cochain.ofHomotopy ho, by ext; simp [δ_ofHomotopy]⟩

theorem exact_part : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) → ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n)
      (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl)
      (HK.post R K S.f (n + 1)) := by
  intro R _ S e h K n
  obtain ⟨hid, -, hcomp, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  obtain ⟨-, -, hass⟩ := GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes R (add_zero n) (zero_add 1) (rfl : n + 1 = n + 1) (rfl : n + 1 = n + 1)
  obtain ⟨x1, x2, x3⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K (resMap R S.f) n
  have hg : ∀ x, HK.post R K S.g n x = cpush K e.hom n (cpush K (mappingCone.inr (resMap R S.f)) n x) := by
    intro x
    rw [← hcomp]
    exact (congrFun (congrArg DFunLike.coe ((hhtp _ _ ⟨h⟩ K n).2)) x).symm
  have hz : ∀ x, HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl x =
      cpost K (mappingCone.fst (resMap R S.f)) n (n + 1) rfl (cpush K e.inv n x) := fun x => hass _ _ _
  have hie : ∀ x, cpush K e.inv n (cpush K e.hom n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyHomInvId⟩ K n).2]
    exact (hid K _ n x).2
  have hei : ∀ x, cpush K e.hom n (cpush K e.inv n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyInvHomId⟩ K n).2]
    exact (hid K _ n x).2
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [hg, ← map_zero (cpush K e.hom n)]
    constructor
    · intro hy
      exact (x1 _).1 (by rw [← hie (cpush K (mappingCone.inr (resMap R S.f)) n y), hy, hie])
    · intro hy
      rw [(x1 _).2 hy]
  · rw [hz]
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x2 _).1 hy
      exact ⟨x, by rw [hg, hx, hei]⟩
    · rintro ⟨x, rfl⟩
      rw [hg, hie]
      exact (x2 _).2 ⟨x, rfl⟩
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x3 _).1 hy
      exact ⟨cpush K e.hom n x, by rw [hz, hie, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [hz]
      exact (x3 _).2 ⟨_, rfl⟩

theorem zcomp_ofHom_ofHom {K L M N : Cx R'} {n : ℤ} (f : K ⟶ L) (g : L ⟶ M) (b : Cocycle M N n) :
    zcomp (Cocycle.ofHom f) (zcomp (Cocycle.ofHom g) b (zero_add n)) (zero_add n) =
      zcomp (Cocycle.ofHom (f ≫ g)) b (zero_add n) := by
  ext1
  change (Cochain.ofHom f).comp ((Cochain.ofHom g).comp b.1 (zero_add n)) (zero_add n) =
    (Cochain.ofHom (f ≫ g)).comp b.1 (zero_add n)
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem assemble {D C I₃ I₁ X : Cx R'} (q : D ⟶ X) (a : X ⟶ I₃) (m : D ⟶ C) (eh : C ⟶ I₃) (ei : I₃ ⟶ C)
    (fst : Cocycle C I₁ 1) (w : Cocycle X I₁ 1) (hh : Homotopy (eh ≫ ei) (𝟙 C))
    (cmp : CohomologyClass.mk (Cocycle.ofHom (q ≫ a)) = CohomologyClass.mk (Cocycle.ofHom (m ≫ eh)))
    (key : CohomologyClass.mk (zcomp (Cocycle.ofHom m) fst (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))) :
    cpull q I₁ 1 (CohomologyClass.mk (zcomp (Cocycle.ofHom a) (zcomp (Cocycle.ofHom ei) fst (zero_add 1)) (zero_add 1))) =
      cpull q I₁ 1 (CohomologyClass.mk w) := by
  have h1 : CohomologyClass.mk (Cocycle.ofHom ((m ≫ eh) ≫ ei)) = CohomologyClass.mk (Cocycle.ofHom m) :=
    mk_ofHom_eq (((Homotopy.ofEq (Category.assoc _ _ _)).trans (hh.compLeft m)).trans
      (Homotopy.ofEq (Category.comp_id m)))
  change CohomologyClass.mk (zcomp (Cocycle.ofHom q) _ (zero_add 1)) = CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))
  rw [zcomp_ofHom_ofHom, ← key, ← cpost_mk, cmp, cpost_mk, zcomp_ofHom_ofHom, ← cpost_mk, h1, cpost_mk]

theorem exists_connecting_cocycle : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  intro R _ S hS
  obtain ⟨e, ⟨h⟩⟩ := GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv R S hS
  refine ⟨_, exact_part R S e h, 1, ?_⟩
  intro φ ψ hφ hψ w hw
  rw [one_smul]
  have hc := resAug_comm R S.f
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact := hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI := mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₁).IsKInjective := by unfold res; infer_instance
  apply (GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))
    (res R S.X₁) 1).1
  exact assemble _ _ _ _ _ _ _ e.homotopyHomInvId (GlobalTheory.T.mappingCone_shortExact_augmentation_class_eq R S hS hc e h) (GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero R S hc φ ψ hφ hψ w hw)

end GlobalTheory.EtC.LesChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator
section
noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((NumberField.discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l
    ((NumberField.discr E).natAbs.factorization l) (ordCompl[l] (NumberField.discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  simp only [multiplicity_eq_count_normalizedFactors hirr, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement


end GlobalTheory.DifferentElement
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticWeakSolOfPolynomialLaplacianZeroStatement
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elliptic_weakSol_of_polynomial_laplacian_zero : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ r > 0, ∃ (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → symb m a x ξ ≠ 0) ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g : G, WeakSol (oneSys m a) (Metric.ball 0 r) (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b (y)))) := by
  first | exact @GlobalTheory.HCA.exists_elliptic_weakSol_of_aeval_eq_zero | exact GlobalTheory.HCA.exists_elliptic_weakSol_of_aeval_eq_zero | (intros; apply GlobalTheory.HCA.exists_elliptic_weakSol_of_aeval_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleSqSubMulSqStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  first | (exact @GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (exact GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (intros; apply GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsSpecFromPairsStatement
section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_functions_spec_from_pairs : ∀ {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X) (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1)), (∀ p q : Pair x, ∀ hpq : p ≤ q, ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) → ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by
  first | exact @GlobalTheory.CechDR.AffLoc.exists_glue_pair | exact GlobalTheory.CechDR.AffLoc.exists_glue_pair | (intros; apply GlobalTheory.CechDR.AffLoc.exists_glue_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftEtaleSheafOfLinearMapsExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  first | (exact @GlobalTheory.EtC.lift_homSh) | (exact GlobalTheory.EtC.lift_homSh) | (intros; apply GlobalTheory.EtC.lift_homSh  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointSeparateStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' : ∀ (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F), j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) → Function.Injective (j₁.comp (algebraMap B A)) → ∀ a : A, j₁ a ≠ j₂ a → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ, y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  first | exact @GlobalTheory.exists_ne_zero_forall_complexPoint_separate | exact GlobalTheory.exists_ne_zero_forall_complexPoint_separate | (intros; apply GlobalTheory.exists_ne_zero_forall_complexPoint_separate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermTransportModularFamiliesValuesStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_transport_modular_families_values : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  first | exact @GlobalTheory.QFam.exists_perm_transport_families | exact GlobalTheory.QFam.exists_perm_transport_families | (intros; apply GlobalTheory.QFam.exists_perm_transport_families <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackMulPOfPTorsionInvariantStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_mulP_of_pTorsion_invariant : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1)), ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0 → ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0 → ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by
  first | exact @GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq | exact GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq | (intros; apply GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq <;> assumption)
end

