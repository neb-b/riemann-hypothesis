module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedInvolutionFieldEmbedding
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

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

theorem exists_unr_embedding : ∀ (K : UQ), K.Odd → ∀ B : InvAlg K, B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  intro K _ B hu _ hi hl d hcard K' φ hU hz
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

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlock
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem rowMap_mul (g h : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) :
    rowMap (g * h) Y = rowMap h (rowMap g Y) := by
  obtain ⟨A, u, c, l⟩ := Y
  simp only [rowMap, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i <;> ring

theorem rowMap_one (Y : Gl r F) : rowMap (1 : SpecialLinearGroup (Fin 2) F) Y = Y := by
  obtain ⟨A, u, c, l⟩ := Y
  simp [rowMap]

theorem continuous_rowMap (g : SpecialLinearGroup (Fin 2) F) : Continuous (rowMap (r := r) g) := by
  unfold rowMap
  fun_prop

theorem isTest_rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (hh : IsTest h) : IsTest (rowAct g h) := by
  let e : Gl r F ≃ₜ Gl r F :=
    { toFun := rowMap g, invFun := rowMap g⁻¹
      left_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      right_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      continuous_toFun := continuous_rowMap g, continuous_invFun := continuous_rowMap g⁻¹ }
  exact ⟨hh.1.comp_continuous (continuous_rowMap g), hh.2.comp_homeomorph e⟩

end GlobalTheory.JR.WeilMix

open GlobalTheory.JR.WeilMix in
theorem GlobalTheory.JR.weil_repG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  intro F E _ _ _ _ _ r M ψ hψ
  have hT := _root_.GlobalTheory.JR.WeilMix.ptrB_isTest F E r M ψ hψ
  have hI := GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column F E r M ψ hψ
  have hL := _root_.GlobalTheory.JR.WeilMix.ptrB_linear F E r M ψ hψ
  have hW := _root_.GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB F E r M ψ hψ
  have hψc : IsLocallyConstant (fun x : F => ψ x) := ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).1
  have h4 : ∀ f, IsTest f → ptrB M ψ (ptrB M ψ (ptrB M ψ (ptrB M ψ f))) = f := by
    intro f hf
    rw [hI _ (hT _ (hT _ hf)), hI _ hf]
    funext Y; simp [negB]
  refine ⟨weil M ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g f hf
    exact hT _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf))))
  · intro f hf
    have : rowAct (1 : SpecialLinearGroup (Fin 2) F) (ptrB M ψ f) = ptrB M ψ f := by
      funext Y; simp [rowAct, rowMap_one]
    simp only [weil, this]
    exact h4 f hf
  · intro g h f hf
    simp only [weil]
    rw [h4 _ (isTest_rowAct h _ (hT _ hf))]
    congr 3
    funext Y; simp [rowAct, rowMap_mul]
  · intro g c f f' hf hf'
    have hR : ∀ (a b : Gl r F → ℂ), rowAct g (c • a + b) = c • rowAct g a + rowAct g b := by
      intro a b; funext Y; simp [rowAct]
    simp only [weil]
    rw [hL c f f' hf hf', hR, hL _ _ _ (isTest_rowAct g _ (hT _ hf)) (isTest_rowAct g _ (hT _ hf')),
      hL _ _ _ (hT _ (isTest_rowAct g _ (hT _ hf))) (hT _ (isTest_rowAct g _ (hT _ hf'))),
      hL _ _ _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf)))) (hT _ (hT _ (isTest_rowAct g _ (hT _ hf'))))]
  · intro f hf
    refine ⟨fun t Y => ?_, ?_⟩
    · let ft : Gl r F → ℂ := fun Y => ψ (t * mom Y 0) * f Y
      have hft : IsTest ft := by
        refine ⟨IsLocallyConstant.mul (hψc.comp_continuous ?_) hf.1, hf.2.mul_left⟩
        simp only [mom, pow_zero, Matrix.one_mulVec]
        fun_prop
      have key : rowAct (nS t) (ptrB M ψ f) = ptrB M ψ ft := by
        funext Y
        obtain ⟨A, u, c, l⟩ := Y
        simp only [rowAct, rowMap, ptrB, nS, ft]
        congr 1
        funext b
        change f (A, b, (fun i => c i * 1 + u i * 0), l) *
          ψ (b ⬝ᵥ (fun i => c i * t + u i * 1)) = _
        simp only [mul_one, mul_zero, add_zero, mom, pow_zero, Matrix.one_mulVec]
        have hu : (fun i => c i * t + u i) = t • c + u := by funext i; simp [mul_comm]
        rw [hu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b c,
          AddChar.map_add_eq_mul]
        ring
      show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (nS t) (ptrB M ψ f)))) Y = _
      rw [key, h4 ft hft]
    · show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (wS F) (ptrB M ψ f)))) = _
      rw [hI _ (hT _ (isTest_rowAct _ _ (hT _ hf)))]
      exact hW f hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInvariantsOfScalarNeOneTwist
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem finite_invariants_of_smul_ne_one : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  intro O _ _ _ _ M _ _ e G _ ρ g a ha hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hb : a - 1 ≠ 0 := sub_ne_zero.2 ha
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hkill : ∀ m : ρ.invariants, ϖ ^ c • (m : M) = 0 := by
    intro m
    have hm : ρ g (m : M) = m := (Representation.mem_invariants ρ (m : M)).1 m.2 g
    have h1 : (a - 1) • (m : M) = 0 := by
      rw [sub_smul, one_smul, ← hg, hm, sub_self]
    rw [hu, mul_smul] at h1
    have h2 := congrArg (fun x : M => ((u⁻¹ : Oˣ) : O) • x) h1
    simp only [smul_zero, smul_smul] at h2
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h2
  haveI := (lev_pow_card hϖ e c).1
  refine Finite.of_injective (fun m : ρ.invariants => (Lev.mk (m : M) (hkill m) : Lev M (ϖ ^ c))) ?_
  intro x y hxy
  have := congrArg Lev.val hxy
  simp only [Lev.val_mk] at this
  exact Subtype.ext this

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwistStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h2_bounded_twist : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  first | exact @GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | exact GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | (intros; apply GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionMemInducedDegreeOneCharDiff
section
open GlobalTheory.BI GlobalTheory.BrauerZero

noncomputable section
namespace GlobalTheory.BrauerZero

theorem ind_eq_ind_map_subgroupOf {G : Type} [Group G] [Finite G] (E : Subgroup G) (H : Subgroup E)
    (φ : H → ℂ) :
    ind H φ = ind ((H.map E.subtype).subgroupOf E)
      (fun k => φ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
        ⟨((k : E) : G), k.2⟩)) := by
  classical
  have hS : (H.map E.subtype).subgroupOf E = H := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hc : Nat.card ((H.map E.subtype).subgroupOf E) = Nat.card H :=
    Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv
  funext g
  simp only [ind, hc]
  congr 1
  refine finsum_congr fun x => ?_
  simp only [ext0]
  by_cases hy : x⁻¹ * g * x ∈ H
  · have hy' : x⁻¹ * g * x ∈ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dite_eq_left hy, dite_eq_left hy']
    congr 1
    apply (Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  · have hy' : x⁻¹ * g * x ∉ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dite_eq_right hy, dite_eq_right hy']

theorem ind_mem_D0_of_mem_D0 : ∀ {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ),
    f ∈ D0 E → ind E f ∈ D0 G := by
  intro G _ _ E f hf
  induction hf using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨H, χ, rfl⟩ := hx
    have hK : H.map E.subtype ≤ E := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    let χ' : H.map E.subtype →* ℂˣ :=
      χ.comp (Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm.toMonoidHom
    rw [ind_sub, ind_eq_ind_map_subgroupOf E H (fun h => (χ h : ℂ)),
      ind_eq_ind_map_subgroupOf E H (fun _ => (1 : ℂ))]
    have h1 : ind E (ind ((H.map E.subtype).subgroupOf E) (fun k =>
        ((χ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
          ⟨((k : E) : G), k.2⟩) : ℂˣ) : ℂ))) = ind (H.map E.subtype) (fun k => (χ' k : ℂ)) :=
      GlobalTheory.T.inducedClassFunctionFromSubgroup_trans (H.map E.subtype) E hK (fun k => (χ' k : ℂ))
    have h2 := GlobalTheory.T.inducedClassFunctionFromSubgroup_trans (H.map E.subtype) E hK (fun _ => (1 : ℂ))
    rw [h1, h2]
    exact AddSubgroup.subset_closure ⟨H.map E.subtype, χ', rfl⟩
  | zero =>
    have : ind E (0 : E → ℂ) = 0 := (indAddHomComplex E).map_zero
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : ind E (a + b) = ind E a + ind E b := (indAddHomComplex E).map_add a b
    rw [this]; exact add_mem ha hb
  | neg a _ ha =>
    have : ind E (-a) = -ind E a := (indAddHomComplex E).map_neg a
    rw [this]; exact neg_mem ha

end GlobalTheory.BrauerZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1EqStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_card_H0_H1_eq : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  first | exact @GlobalTheory.ShapeNeg.transfer_card_H0_H1 | exact GlobalTheory.ShapeNeg.transfer_card_H0_H1 | (intros; apply GlobalTheory.ShapeNeg.transfer_card_H0_H1 <;> assumption)
end

