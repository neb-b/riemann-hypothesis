module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedEmbeddingOfInvolutionAlgebra
section
noncomputable section

namespace GlobalTheory.UnitLemma.UnrAny

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem pow_eq_one_eq_of_residue {S : Type*} [CommRing S] [IsLocalRing S] {n : ℕ} (hn : IsUnit (n : S))
    {y₁ y₂ : S} (h₁ : y₁ ^ n = 1) (h₂ : y₂ ^ n = 1) (h : residue S y₁ = residue S y₂) : y₁ = y₂ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have key : (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) * (y₁ - y₂) = 0 := by
    rw [Commute.geom_sum₂_mul (Commute.all _ _), h₁, h₂, sub_self]
  have hr : residue S (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) =
      (n : ResidueField S) * residue S y₂ ^ (n - 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [Finset.sum_congr rfl (g := fun _ => residue S y₂ ^ (n - 1)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    intro i hi
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hi
    omega
  have hu : IsUnit (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hr]
    refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · simpa using (hn.map (residue S)).ne_zero
    · intro h0
      have := congrArg (residue S) h₂
      rw [map_pow, h0, zero_pow hn0, map_one] at this
      exact zero_ne_one this
  have := (hu.mul_right_eq_zero).1 key
  exact sub_eq_zero.1 this

theorem card_sub_one_isUnit (S : Type*) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    IsUnit ((Nat.card (ResidueField S) - 1 : ℕ) : S) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub Nat.card_pos, Nat.cast_one]
  haveI := Fintype.ofFinite (ResidueField S)
  rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
  simp

theorem exists_unr_embedding_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  intro K B hu _ hi hl d hcard K' φ hU hz
  obtain ⟨z, hzp, hzadj⟩ := hz
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hR
  have hq0 : K.q ≠ 0 := by
    intro h0
    have : 0 < Nat.card (ResidueField K.O) := Nat.card_pos
    rw [K.card_res, h0] at this
    simp at this
  have hq' : K'.q = K.q ^ d := hU.1
  set N := K'.q ^ 2 - 1 with hNdef
  have hcardR : Nat.card (ResidueField R) = K'.q ^ 2 := by rw [hcard, hq', ← pow_mul, mul_comm]
  have hd : d ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq'
    rw [hq', one_pow] at hcardR
    have : Subsingleton (ResidueField R) := (Nat.card_eq_one_iff_unique.1 hcardR).1
    exact not_subsingleton (ResidueField R) this
  haveI : Finite (ResidueField R) := Nat.finite_of_card_ne_zero (by rw [hcardR, hq']; exact pow_ne_zero _ (pow_ne_zero _ hq0))

  haveI : Module.Finite K.O R := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : HenselianLocalRing K.O := GlobalTheory.henselianLocalRing_of_henselianRing K.O
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_finite K.O R
  have h1q : 1 < K'.q ^ 2 := by rw [← K'.card_res]; exact Finite.one_lt_card
  have hN : N ≠ 0 := by omega
  have hNR : IsUnit (N : R) := by
    have := card_sub_one_isUnit R
    rwa [hcardR] at this
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul K.O K'.E := (faithfulSMul_iff_algebraMap_injective _ _).2
    (φ.injective.comp (IsFractionRing.injective K.O K.E))
  have hzN : z ^ N = 1 := hzp.pow_eq_one
  have hzint : IsIntegral K.O z :=
    ⟨_, monic_X_pow_sub_C (1 : K.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hmdvd : minpoly K.O z ∣ X ^ N - C 1 := minpoly.isIntegrallyClosed_dvd hzint (by simp [hzN])
  obtain ⟨yR, hyR⟩ := _root_.GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root R ((minpoly K.O z).map (algebraMap K.O R))
    ((minpoly.monic hzint).map _)
    (by rw [(minpoly.monic hzint).natDegree_map]; exact (minpoly.natDegree_pos hzint).ne')
    (by
      rw [hcardR]
      have := Polynomial.map_dvd (algebraMap K.O R) hmdvd
      simpa using this)
  have hyN : yR ^ N = 1 := by
    obtain ⟨h, hh⟩ := hmdvd
    have := congrArg (fun p => (p.map (algebraMap K.O R)).eval yR) hh
    simp only [Polynomial.map_mul, eval_mul, hyR, zero_mul] at this
    simpa [sub_eq_zero] using this

  have hzE : IsIntegral K.E z := hzint.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzE hzadj
  have hgen : pb.gen = z := rfl
  have hy : aeval (yR : B.A) (minpoly K.E pb.gen) = 0 := by
    rw [hgen, minpoly.isIntegrallyClosed_eq_field_fractions' K.E hzint, aeval_map_algebraMap,
      ← Polynomial.aeval_subalgebra_coe, aeval_def, ← eval_map, hyR]
    rfl
  let ψ : K'.E →+* B.A := (pb.lift (yR : B.A) hy).toRingHom
  have hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e := fun e => (pb.lift (yR : B.A) hy).commutes e
  have hψz : ψ z = yR := pb.lift_gen _ hy
  haveI : Nontrivial B.A := nontrivial_of_ne (0 : B.A) 1 fun h => zero_ne_one (Subtype.ext h : (0 : R) = 1)
  have hψi : Function.Injective ψ := ψ.injective

  let τR : R →+* R := (B.σ : B.A →+* B.A).restrict R R fun x hx => Orbit.adjoin_stable B hu hi hx
  have hτR : ∀ x : R, (τR x : B.A) = B.σ x := fun x => rfl
  have hτ2 : ∀ x, τR (τR x) = x := fun x => Subtype.ext (B.σ_σ x)
  obtain ⟨a, b, hab, hres⟩ := K.c_res
  have hτa : τR (algebraMap K.O R a) = algebraMap K.O R b := by
    apply Subtype.ext
    rw [hτR]
    change B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hab, ← IsScalarTower.algebraMap_apply]
  have hne : residue R (τR (algebraMap K.O R a)) ≠ residue R (algebraMap K.O R a) := by
    rw [hτa]
    intro h
    have h2 : residue R (algebraMap K.O R (a - b)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff] at h2
    have hu' : IsUnit (a - b) := by
      by_contra hc
      exact hres ((IsLocalRing.mem_maximalIdeal _).2 hc)
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 (hu'.map _)
  obtain ⟨hfr1, hfr2⟩ := _root_.GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots R K'.q hcardR τR hτ2 ⟨_, hne⟩
  choose τ' hτ' using K'.c_int
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let cO : K'.O →+* K'.O :=
    { toFun := τ'
      map_one' := hinj' (by rw [← hτ']; simp)
      map_mul' := fun a b => hinj' (by simp [← hτ'])
      map_zero' := hinj' (by rw [← hτ']; simp)
      map_add' := fun a b => hinj' (by simp [← hτ']) }
  have hcO : ∀ x, algebraMap K'.O K'.E (cO x) = K'.c (algebraMap K'.O K'.E x) := fun x => (hτ' x).symm
  have hc2 : ∀ x, cO (cO x) = x := fun x => hinj' (by rw [hcO, hcO, K'.c_c])
  obtain ⟨a', b', hab', hres'⟩ := K'.c_res
  have hne' : residue K'.O (cO a') ≠ residue K'.O a' := by
    have : cO a' = b' := hinj' (by rw [hcO, hab'])
    rw [this]
    intro h
    apply hres'
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  obtain ⟨-, hfc⟩ := _root_.GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots K'.O K'.q K'.card_res cO hc2 ⟨_, hne'⟩
  obtain ⟨zO, hzO⟩ : ∃ zO : K'.O, algebraMap K'.O K'.E zO = z :=
    IsIntegrallyClosed.isIntegral_iff.1
      ⟨_, monic_X_pow_sub_C (1 : K'.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hzON : zO ^ N = 1 := hinj' (by rw [map_pow, hzO, hzN, map_one])
  have hcz : K'.c z = z ^ K'.q := by
    rw [← hzO, ← hcO, hfc zO hzON, map_pow]
  have hσz : B.σ (ψ z) = ψ (K'.c z) := by
    rw [hψz, ← hτR, hfr2 yR hyN, hcz, map_pow, hψz]
    rfl
  have hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e) := by
    intro e
    have he : e ∈ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} := hzadj ▸ Algebra.mem_top
    induction he using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hσz
    | algebraMap e =>
      change B.σ (ψ (φ e)) = ψ (K'.c (φ e))
      rw [← hU.2.1, hψ, hψ, B.σ_alg]
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

  have hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ R := by
    intro y
    have hadj := _root_.GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers K K' d φ hU hd z hzp hzadj _ (_root_.GlobalTheory.UnitLemma.Unr.intO K K' d φ hU hd y)
    generalize algebraMap K'.O K'.E y = x at hadj ⊢
    induction hadj using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hψz]; exact yR.2
    | algebraMap a =>
      change ψ (φ (algebraMap K.O K.E a)) ∈ R
      rw [hψ, ← IsScalarTower.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨ψ, hψ, hσ, hO, ?_⟩
  haveI : NeZero N := ⟨hN⟩
  have hcoe : ∀ n : ℕ, ((yR ^ n : R) : B.A) = ψ (z ^ n) := fun n => by rw [map_pow, hψz]; rfl
  have hwp : IsPrimitiveRoot (residue R yR) N := by
    refine ⟨by rw [← map_pow, hyN, map_one], fun l hl => hzp.dvd_of_pow_eq_one l ?_⟩
    have h1 : yR ^ l = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [map_pow, hl, map_one])
    apply hψi
    rw [← hcoe, h1, map_one]
    rfl
  set gR : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ with hgR
  have hgu : gR * τR gR = 1 := Subtype.ext hu
  have hg0 : residue R gR ≠ 0 := (IsUnit.map (residue R) (⟨⟨gR, τR gR, hgu, by rw [mul_comm]; exact hgu⟩, rfl⟩ : IsUnit gR)).ne_zero
  have hgN : residue R gR ^ N = 1 := by
    haveI := Fintype.ofFinite (ResidueField R)
    have := FiniteField.pow_card_sub_one_eq_one _ hg0
    rwa [← Nat.card_eq_fintype_card, hcardR] at this
  obtain ⟨j, -, hj⟩ := hwp.eq_pow_of_pow_eq_one hgN
  let zOu : K'.Oˣ := Units.ofPowEqOne zO N hzON hN
  have hs : algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O) = z ^ j := by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_ofPowEqOne, hzO]
  refine ⟨zOu ^ j, ?_, ?_⟩
  · set e := j + j * K'.q with he
    have hres : residue R (yR ^ e) = 1 := by
      rw [map_pow, he, pow_add, pow_mul, hj, ← hfr1 gR, ← map_mul, hgu, map_one]
    have hye : yR ^ e = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [hres, map_one])
    rw [hs, map_pow, hcz, ← pow_mul, ← pow_add, mul_comm K'.q j, ← he]
    apply hψi
    rw [← hcoe, hye, map_one]
    rfl
  · have : (⟨ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)), hO _⟩ : R) = yR ^ j :=
      Subtype.ext (by
        change ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)) = ((yR ^ j : R) : B.A)
        rw [hs, hcoe])
    rw [this, map_pow, hj]

end GlobalTheory.UnitLemma.UnrAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFilteredStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  first | (exact @GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_action_model_of_isColimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ExtHom

variable {R : Type} [CommRing R]

theorem cochain_sgl_neg_one_eq_zero (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0]
    (β : Cochain (sgl F) I (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : p = 0
  · subst hp
    exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F p hp).eq_of_src _ _

theorem ofHom_eq_of_cls {T I : Cx R} {f g : T ⟶ I}
    (h : CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g)) :
    ∃ β : Cochain T I (-1), Cochain.ofHom f = δ (-1) 0 β + Cochain.ofHom g := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (-1) (by omega)] at h
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, ?_⟩
  rw [hβ]
  simp

end GlobalTheory.EtC.ExtHom


open GlobalTheory.EtC.ExtHom in
theorem GlobalTheory.EtC.extHom_of_quasiIso : ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m') := by
  intro R _ F T I _ _ ε _
  have hb := GlobalTheory.EtC.cpull_bijective_of_quasiIso R ε I 0
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨y, hy⟩ := hb.2 (CohomologyClass.mk (Cocycle.ofHom a))
    obtain ⟨z, rfl⟩ := y.mk_surjective
    refine ⟨Cocycle.homOf z, ?_⟩
    have hz : Cocycle.ofHom (ε ≫ Cocycle.homOf z) = zcomp (Cocycle.ofHom ε) z (zero_add 0) := by
      apply Cocycle.ext
      simp [zcomp, Cochain.ofHom_comp]
    have h2 : CohomologyClass.mk (Cocycle.ofHom (ε ≫ Cocycle.homOf z)) = CohomologyClass.mk (Cocycle.ofHom a) := by
      rw [hz]; exact hy
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls h2
    rw [cochain_sgl_neg_one_eq_zero F I β, δ_zero, zero_add] at hβ
    exact (Cocycle.equivHom _ _).injective (Cocycle.ext hβ)
  · have h1 : cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m)) = cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m')) := by
      simp only [cpull, cpre_mk]
      congr 1
      apply Cocycle.ext
      change (Cochain.ofHom ε).comp (Cochain.ofHom m) (zero_add 0) = (Cochain.ofHom ε).comp (Cochain.ofHom m') (zero_add 0)
      rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp, h]
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls (hb.1 h1)
    exact ⟨(Cochain.equivHomotopy m m').symm ⟨β, hβ⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorWedgeEqOfLocalizedSpanStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_wedge_eq_of_localized_span : ∀ (R L M : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup M] [Module L M] (S : Submonoid R) (n : ℕ) (g w : Fin n → M), (∀ i, ∃ r ∈ S, ∃ c : Fin n → R, algebraMap R L r • w i = ∑ l, algebraMap R L (c l) • g l) → ∃ r ∈ S, ∃ c : R, algebraMap R L r • ExteriorAlgebra.ιMulti L n w = algebraMap R L c • ExteriorAlgebra.ιMulti L n g := by
  first | (exact @GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti) | (exact GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti) | (intros; apply GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreZeroMemCoinvariants
section
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isFirstMax_unique {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J)
    (h' : IsFirstMax Y J') : J = J' := by
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (fun H => lt_irrefl _ (H.trans_le ((h.2 J').1)))
  · exact idx.injective he
  · exact absurd ((h.2 J').2 hl) (fun H => lt_irrefl _ (H.trans_le ((h'.2 J).1)))

theorem sec_val {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J : Fin a ↪ Fin d} (h : IsFirstMax Y J) :
    (sec Y).val = Y.submatrix id J := by
  have hex : ∃ J, IsFirstMax Y J := ⟨J, h⟩
  rw [sec, dite_eq_left hex]
  show Y.submatrix id hex.choose = _
  rw [isFirstMax_unique hex.choose_spec h]

theorem continuousOn_sec {a d : ℕ} : ContinuousOn (sec (k := k) (a := a) (d := d)) {Y | Y.rank = a} := by
  intro Y hY
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.RankFibreKer.exists_isFirstMax k a d Y ((_root_.GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero k a d Y).1 hY)
  rw [isEmbedding_val_GL.isInducing.continuousWithinAt_iff]
  refine ContinuousAt.continuousWithinAt ?_
  have hc : Continuous fun Y : Matrix (Fin a) (Fin d) k => Y.submatrix id J :=
    (continuous_id.matrix_submatrix id J)
  refine hc.continuousAt.congr ?_
  filter_upwards [_root_.GlobalTheory.RankFibreKer.isFirstMax_eventually k a d Y J hJ] with Y' hY'
  exact (sec_val hY').symm

theorem sec_mem_slice {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (hY : Y.rank = a) :
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.RankFibreKer.exists_isFirstMax k a d Y ((_root_.GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero k a d Y).1 hY)
  exact GlobalTheory.T.section_inverse_into_slice k a d Y J hJ

theorem vol_ne_zero [MeasurableSpace k] [BorelSpace k] {a : ℕ} (K : Subgroup (GL (Fin a) k))
    (hK : IsOpen (K : Set (GL (Fin a) k))) (hKO : K ≤ KO k (Fin a)) :
    (haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) ≠ 0 := by
  have h0 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ 0 :=
    (hK.measure_pos (haarVol (KO k (Fin a))) ⟨1, K.one_mem⟩).ne'
  have h1 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ ⊤ :=
    ((measure_mono (μ := haarVol (KO k (Fin a))) (show (K : Set (GL (Fin a) k)) ⊆ KO k (Fin a) from hKO)).trans_lt
      (by rw [haarVol_self isOpen_KO le_rfl]; exact ENNReal.one_lt_top)).ne
  exact ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩

theorem fibre_ker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b),
    GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  intro k _ _ _ _ _ _ a b ν β hν _ Φ hΦ hfib
  have hun : ∀ (Z : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k), Z ∈ slice k a (a + b) →
      g.val * Z ∈ slice k a (a + b) → g = 1 := GlobalTheory.T.slice_stabilizer_trivial k a (a + b)
  have hsc := continuousOn_sec (k := k) (a := a) (d := a + b)
  have hsl := sec_mem_slice (k := k) (a := a) (d := a + b)
  obtain ⟨U, hU, hUf⟩ := GlobalTheory.T.continuous_slice_section_integral k a (a + b) Φ hΦ sec hsc hsl hun
  let Kf : Subgroup (GL (Fin a) k) :=
    { carrier := {x | ∀ g : GL (Fin a) k, ∀ Z ∈ slice k a (a + b), Φ (g.val * x.val * Z) = Φ (g.val * Z)}
      one_mem' := fun g Z _ => by simp
      mul_mem' := fun {x y} hx hy g Z hZ => by
        rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, hy (g * x) Z hZ, Units.val_mul, hx g Z hZ]
      inv_mem' := fun {x} hx g Z hZ => by
        have := hx (g * x⁻¹) Z hZ
        rw [Units.val_mul, Matrix.mul_assoc (g.val), ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one] at this
        exact this.symm }
  have hKf : IsOpen (Kf : Set (GL (Fin a) k)) := Subgroup.isOpen_of_mem_nhds Kf (g := 1)
    (Filter.mem_of_superset hU fun x hx g Z hZ => hUf x hx g Z hZ)
  let K : Subgroup (GL (Fin a) k) := KO k (Fin a) ⊓ (detChar (Fin a) ν).ker ⊓ Kf
  have hK : IsOpen (K : Set (GL (Fin a) k)) := (isOpen_KO.inter hν.detChar).inter hKf
  have hKO : K ≤ KO k (Fin a) := le_trans inf_le_left inf_le_left
  have htw : ∀ x ∈ K, tw ν (a + b) x = 1 := fun x hx => by
    have h1 : ν (gdet x) = 1 := hx.1.2
    simp [tw, h1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.1.1)]
  have hright : ∀ (g x : GL (Fin a) k) (Z : Matrix (Fin a) (Fin (a + b)) k), x ∈ K → Z ∈ slice k a (a + b) →
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := fun g x Z hx hZ => hx.2 g Z hZ
  obtain ⟨C, hC, hEC⟩ := GlobalTheory.T.continuous_slice_section_measure k a (a + b) Φ hΦ sec hsc hsl hun
  obtain ⟨R, hRd, hRc⟩ := _root_.GlobalTheory.compact_finite_leftCoset_reps (GL (Fin a) k) K hK C hC
  set T : Set (Matrix (Fin a) (Fin (a + b)) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a (a + b), Y = x.val * Z} with hT
  have hrank : ∀ Y, Φ Y ≠ 0 → Y.rank = a := fun Y hY => by
    by_contra h; exact hY (hΦ.2 Y h)
  refine GlobalTheory.T.coinvariant_of_locally_constant_twist k ν β a b Φ (T.indicator 1) R hΦ.1
    (GlobalTheory.T.isLocallyConstant_indicator_mul_slice k a (a + b) K hK hKO (_root_.GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero k a (a + b)) sec hsc hsl hun) (fun Y => ?_) (fun Y => ?_)
  · by_cases hY : Φ Y = 0
    · simp [hY]
    obtain ⟨g, hg⟩ : ∃ g : GL (Fin a) k, (g⁻¹).val * Y ∈ slice k a (a + b) := ⟨sec Y, hsl Y (hrank Y hY)⟩
    set Z := (g⁻¹).val * Y with hZdef
    have hYZ : Y = g.val * Z := by rw [hZdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
    obtain ⟨r, hr, hrg⟩ := hRc g (hEC g Z hg (hYZ ▸ hY))
    rw [Finset.sum_eq_single r]
    · rw [Set.indicator_of_mem, Pi.one_apply, one_mul]
      exact ⟨r⁻¹ * g, hrg, Z, hg, by rw [hYZ, Units.val_mul, Matrix.mul_assoc]⟩
    · intro r' hr' hne
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨x', hx', Z', hZ', he⟩
      have h1 : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z ∈ slice k a (a + b) := by
        have : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z = Z' := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [← hYZ, he, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [this]; exact hZ'
      have h2 := hun Z _ hg h1
      have h3 : g = r' * x' := by
        calc g = r' * x' * (x'⁻¹ * r'⁻¹ * g) := by group
          _ = r' * x' := by rw [h2, mul_one]
      exact hne (hRd r hr r' hr' (by
        have : r⁻¹ * r' = (r⁻¹ * g) * x'⁻¹ := by rw [h3]; group
        rw [this]; exact K.mul_mem hrg (K.inv_mem hx'))).symm
    · intro h; exact absurd hr h
  · by_cases hY : Y ∈ T
    · obtain ⟨x, hx, Z, hZ, rfl⟩ := hY
      rw [Set.indicator_of_mem (show x.val * Z ∈ T from ⟨x, hx, Z, hZ, rfl⟩), Pi.one_apply, one_mul]
      have e1 : ∀ r : GL (Fin a) k, Φ (r.val * (x.val * Z)) = Φ (r.val * Z) := fun r => by
        rw [← Matrix.mul_assoc]; exact hright r x Z hx hZ
      simp only [e1]
      have hZr : Z.rank = a := by
        obtain ⟨J, hJ, -⟩ := hZ
        exact (_root_.GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero k a (a + b) Z).2 ⟨J, by simp [minor, hJ]⟩
      have hint := _root_.GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets k a K hK hKO (fun g => Φ (g.val * Z) * tw ν (a + b) g)
        (fun g x' hx' => by
          simp only [Units.val_mul, tw_mul, htw x' hx', mul_one]
          rw [hright g x' Z hx' hZ])
        R hRd (fun g hg => hRc g (hEC g Z hZ (left_ne_zero_of_mul hg)))
      rw [_root_.GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero k ν β a b Φ hfib Z hZr] at hint
      have hv := vol_ne_zero K hK hKO
      have := (mul_eq_zero.1 hint.symm).resolve_left (by exact_mod_cast hv)
      rw [← this]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    · simp [Set.indicator_of_notMem hY]

end GlobalTheory.RankFibreKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedUnitsModRatNormsStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_fixedUnits_mod_rat_norms : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ j : E, IsUnit j → τ j = -j → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  first | (exact @GlobalTheory.EtaleCls.classes_mod_rat_norms) | (exact GlobalTheory.EtaleCls.classes_mod_rat_norms) | (intros; apply GlobalTheory.EtaleCls.classes_mod_rat_norms  <;> assumption)
end

