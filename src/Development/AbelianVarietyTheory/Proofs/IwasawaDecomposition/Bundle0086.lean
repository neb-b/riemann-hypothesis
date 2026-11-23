module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaActsOnTameRoot
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem fund_phiB_alg (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  GlobalTheory.CrisMaps.φB_phiA l x

theorem fund_zB (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) :
    Per.zB l z = algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) :=
  (GlobalTheory.RingIface.zB_eq_aB_zA l z).trans (GlobalTheory.RingIface.aB_eq_alg l _)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fundamental_exact (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l)
    (hφ : Per.φB l b = b) (hF : C.ι b ∈ Per.FilD l 0) :
    ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = b := by
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨-, hinj, -, -⟩ := _root_.GlobalTheory.MemLoc.BdRField.bdR_isField l
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := _root_.GlobalTheory.MemLoc.filD_laws l
  have hj := _root_.GlobalTheory.MemLoc.crisP_injective l C.j C.j_cris
  obtain ⟨htu, ht1, -, hlu⟩ := _root_.GlobalTheory.MemLoc.core_t_unit_fil l C
  have htφ := _root_.GlobalTheory.MemLoc.TPhi.t_phi l C
  obtain ⟨-, -, huz, -, -, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  have hA : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
    intro y y' h
    apply hj
    apply hinj
    rw [← C.ι_j, ← C.ι_j, h]
  have e1 : phiA l x = (l : Per.Acris l) ^ r * x := by
    apply hA
    rw [← fund_phiB_alg, map_mul, map_pow, map_natCast, ← hx, map_mul, map_pow, hφ,
      fund_phiB_alg, htφ, map_mul, map_natCast, mul_pow]
    ring
  have ht1' : algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ∈ Per.FilD l 1 :=
    (hP 1 _).2 ht1
  have htr : ∀ n : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ^ n ∈ Per.FilD l (n : ℤ) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact h1
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ]
      exact hmul _ _ _ _ ih ht1'
  have e2 : C.j x ∈ Per.FilP l r := by
    rw [← hP, ← C.ι_j, ← hx, map_mul, map_pow, C.ι_j]
    have := hmul _ _ _ _ hF (htr r)
    rwa [zero_add] at this
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C r x e1 e2
  have e3 : (l : Per.Bcris l) ^ k * b = Per.zB l z := by
    apply (htu.pow r).mul_right_cancel
    have := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hx, ← fund_zB, ← mul_assoc] at this
    exact this
  refine ⟨(z : ℚ_[l]) / (l : ℚ_[l]) ^ k, ?_⟩
  apply (hlu.pow k).mul_left_cancel
  rw [e3, ← huz]
  have hl : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have e4 : (z : ℚ_[l]) = (l : ℚ_[l]) ^ k * ((z : ℚ_[l]) / (l : ℚ_[l]) ^ k) := by
    field_simp
  conv_rhs => rw [e4]
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
section
namespace GlobalTheory.AnalyticNormality

open IsLocalRing

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  have hnoeth := _root_.GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion
  have hquot := _root_.GlobalTheory.adicCompletion_quotient_ringEquiv
  have hengine := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient
  have hclosed := GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
  have hdom := _root_.GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced
  have hred := _root_.GlobalTheory.CompletionReduced.isReduced_adicCompletion
  have hcond := _root_.GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType
  intro A _ _ _ _ _ _
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  set m := maximalIdeal A with hm
  let R := AdicCompletion m A
  haveI : IsNoetherianRing R := hnoeth A m
  haveI : Module.Flat A R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsReduced R := hred A m (IsLocalRing.maximalIdeal_le_jacobson _)
  obtain ⟨x, hx0, hx⟩ := hcond A
  have hxR : algebraMap A R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular A x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap A R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hredq : ∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R)) := by
    intro q hq _
    obtain ⟨e⟩ := hquot A m q
    haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType A (A ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (A ⧸ q)
      haveI : IsScalarTower ℤ A (A ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ A (A ⧸ q)
    have hj : m.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ q)) := by
      haveI : IsLocalRing (A ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      refine Ideal.mem_comap.mpr (IsLocalRing.maximalIdeal_le_jacobson _ ?_)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ q)ˣ).1
      have h1 : Ideal.Quotient.mk q (a * b) = 1 := by
        rw [map_mul, hb]; exact hu.mul_val_inv
      have h2 : a * b - 1 ∈ q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : a * b - 1 ∈ m := IsLocalRing.le_maximalIdeal hq.ne_top h2
      have h4 : (1 : A) ∈ m := by
        have := m.sub_mem (m.mul_mem_right b ha) h3
        simpa using this
      exact (Ideal.ne_top_iff_one m).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h4
    haveI := hred (A ⧸ q) _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  have hcl : IsIntegrallyClosed R := by
    refine hclosed R (algebraMap A R x) hxR ?_ hx
    intro P _ hP
    obtain ⟨h1, h2⟩ := hengine A R x hx0 hredq P hP
    exact ⟨h1, inferInstance⟩
  exact ⟨hdom R hcl, hcl⟩

end GlobalTheory.AnalyticNormality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
section
open CategoryTheory Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.LabelUniqueAll

open Finset

theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    ∀ k, k ≤ d → MvPolynomial.aeval a (MvPolynomial.esymm (Fin d) ℂ k) =
      MvPolynomial.aeval b (MvPolynomial.esymm (Fin d) ℂ k) := by
  first
  | exact @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | (apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq ..)

theorem map_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have he := esymm_eq_of_psum_eq a b h
  have hp : ((Finset.univ.val.map a).map fun t => X - C t).prod =
      ((Finset.univ.val.map b).map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ), ← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ),
      he j (by simpa [Nat.lt_succ_iff] using hj)]
  have := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  exact this

theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]; omega

variable {g : ℕ} [Fact g.Prime]

theorem natDegree_minpoly_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hkd : k ≤ d) : (minpoly (ZMod g) (L.gen d ^ k)).natDegree = d := by
  set γ := L.gen d
  set m := g ^ d - 1 with hmdef
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hord : orderOf γ = m := L.gen_order d hd
  have hγm : γ ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hγ0 : γ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hfix : (γ ^ k) ^ (g ^ d) = γ ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, show g ^ d = m + 1 by omega, pow_succ, hγm, one_mul]
  have hdvd : (minpoly (ZMod g) (γ ^ k)).natDegree ∣ d :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ d).2 hfix
  have hfe : (γ ^ k) ^ (g ^ (minpoly (ZMod g) (γ ^ k)).natDegree) = γ ^ k :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ _).1 dvd_rfl
  have he0 : 0 < (minpoly (ZMod g) (γ ^ k)).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
  generalize (minpoly (ZMod g) (γ ^ k)).natDegree = e at hdvd hfe he0 ⊢
  by_contra hne
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc; omega
    · simp at hc; omega
    · omega
  have hge : 2 ≤ g ^ e := le_trans hg2 (Nat.le_self_pow he0.ne' g)
  have hone : γ ^ (k * (g ^ e - 1)) = 1 := by
    have : γ ^ k * γ ^ (k * (g ^ e - 1)) = γ ^ k * 1 := by
      rw [mul_one, ← pow_add]
      conv_rhs => rw [← hfe, ← pow_mul]
      congr 1
      have : g ^ e = (g ^ e - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ hγ0) this
  have hmd : m ∣ k * (g ^ e - 1) := hord ▸ orderOf_dvd_of_pow_eq_one hone
  have hpos : 0 < k * (g ^ e - 1) := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos hmd
  have hec : e * 2 ≤ e * c := Nat.mul_le_mul_left e hc2
  have h2 : d ≤ 2 * (d - e) := by omega
  have h3 : 2 * (d - e) ≤ 2 ^ (d - e) := two_mul_le_two_pow _
  have h4 : 2 ^ (d - e) ≤ g ^ (d - e) := Nat.pow_le_pow_left hg2 _
  have h5 : d * g ^ e ≤ g ^ d := by
    calc d * g ^ e ≤ g ^ (d - e) * g ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ d := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have h6 : k * (g ^ e - 1) ≤ d * (g ^ e - 1) := Nat.mul_le_mul_right _ hkd
  have h7 : d * (g ^ e - 1) = d * g ^ e - d := Nat.mul_sub_one _ _
  omega

theorem label_eq (L : LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : Gn g d → ℂ)
    (h : IsCuspOf L P χ) (h' : IsCuspOf L P' χ) : P = P' := by
  obtain ⟨hPl, hc, hval⟩ := h
  obtain ⟨hPl', -, hval'⟩ := h'
  have hd : 0 < d := hc.1
  obtain ⟨x, hx⟩ := LabelUnique.exists_mem hd hPl
  obtain ⟨x', hx'⟩ := LabelUnique.exists_mem hd hPl'
  have hx1 := LabelUnique.pow_sub_one_eq_one hPl hx
  have hx1' := LabelUnique.pow_sub_one_eq_one hPl' hx'
  have hteich : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → L.teich w ^ (g ^ d - 1) = 1 := fun w hw => by
    rw [← map_pow, hw, map_one]
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hγ0 : L.gen d ≠ 0 := by
    have hγm : L.gen d ^ (g ^ d - 1) = 1 := by rw [← L.gen_order d hd]; exact pow_orderOf_eq_one _
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hsums : ∀ k, 1 ≤ k → k ≤ d → ∑ i : Fin d, L.teich (x ^ (g ^ (i : ℕ))) ^ k =
      ∑ i : Fin d, L.teich (x' ^ (g ^ (i : ℕ))) ^ k := by
    intro k hk1 hkd
    have hdeg := natDegree_minpoly_gen_pow L hd hk1 hkd
    obtain ⟨y, hy, hz⟩ := GlobalTheory.GLm.exists_irreducible_charpoly_mem_rootsBar g d (L.gen d ^ k)
      (pow_ne_zero _ hγ0) hdeg
    have e1 := hval x hx y hy _ hz
    have e2 := hval' x' hx' y hy _ hz
    rw [e1] at e2
    have e3 := mul_left_cancel₀ (pow_ne_zero (d - 1) (by norm_num : (-1 : ℂ) ≠ 0)) e2
    have conv : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → ∀ i : ℕ,
        thetaOf L d w ((L.gen d ^ k) ^ (g ^ i)) = L.teich (w ^ (g ^ i)) ^ k := by
      intro w hw i
      rw [← pow_mul, LabelUnique.thetaOf_gen_pow L d hd w (hteich w hw), map_pow, ← pow_mul,
        Nat.mul_comm]
    simp only [conv x hx1, conv x' hx1'] at e3
    rw [Fin.sum_univ_eq_sum_range (fun i => L.teich (x ^ g ^ i) ^ k),
      Fin.sum_univ_eq_sum_range (fun i => L.teich (x' ^ g ^ i) ^ k)]
    exact e3
  have hm := map_eq_of_psum_eq _ _ hsums
  have hmem : L.teich x ∈ Finset.univ.val.map (fun i : Fin d => L.teich (x ^ (g ^ (i : ℕ)))) :=
    Multiset.mem_map.2 ⟨⟨0, hd⟩, Finset.mem_univ_val _, by simp⟩
  rw [hm] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  have hxe : x = x' ^ (g ^ (i : ℕ)) :=
    L.teich_inj _ _ (LabelUnique.ne_zero_of_mem hPl hx)
      (pow_ne_zero _ (LabelUnique.ne_zero_of_mem hPl' hx')) hi.symm
  have h1 : aeval x P' = 0 := by
    rw [hxe]; exact LabelUnique.aeval_pow_eq_zero (LabelUnique.aeval_eq_zero_of_mem hPl'.1.ne_zero hx') i
  have h2 := minpoly.eq_of_irreducible_of_monic hPl'.2.1 h1 hPl'.1
  rw [h2, LabelUnique.minpoly_eq_of_mem hPl hx]

end GlobalTheory.GLq.LabelUniqueAll

namespace GlobalTheory.GLq

theorem isCuspOf_label_unique_allPrimes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime]
    (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ),
    GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' :=
  fun _ _ _ L d P P' χ h h' => LabelUniqueAll.label_eq L d P P' χ h h'

end GlobalTheory.GLq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlaceStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_inertia_tameChar_other_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TameMove.tameRep_move | exact GlobalTheory.TameMove.tameRep_move | (intros; apply GlobalTheory.TameMove.tameRep_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerRStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_tameChar_primitiveRoot_of_uniformizerRoot : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  first | exact @GlobalTheory.TameRootSurj.main | exact GlobalTheory.TameRootSurj.main | (intros; apply GlobalTheory.TameRootSurj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntSmulMem
section
open NumberField Formalism.BasicNotions

namespace GlobalTheory.AutLattice

section
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_int_smul_mem (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem ..)

theorem finrank_int_eq (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) :
    Module.finrank ℤ L = Module.finrank ℚ E * Module.finrank E V := by
  let _i : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  rw [Module.finrank_mul_finrank ℚ E V,
    IsLocalization.finrank_eq ℚ (N := V) (nonZeroDivisors ℤ) le_rfl]
  let f : L →ₗ[ℤ] V := L.subtype.toAddMonoidHom.toIntLinearMap
  have : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    { map_units := fun s =>
        (isLocalizedModule_id (nonZeroDivisors ℤ) V ℚ).map_units s
      surj := fun v => by
        obtain ⟨n, hn, h⟩ := exists_int_smul_mem L hL v
        exact ⟨(⟨n • v, h⟩, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), rfl⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : x = y := Subtype.ext h
        rw [this]⟩ }
  exact (IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) f le_rfl).symm

end

theorem card_dvd_minkM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V), L.FG → Submodule.span E (L : Set V) = ⊤ → ∀ G : Subgroup (V ≃ₗ[E] V), Finite G → (∀ g ∈ G, ∀ x ∈ L, g x ∈ L) → Nat.card G ∣ minkM (Module.finrank ℚ E * Module.finrank E V) := by
  intro hM E V _ _ _ _ _ _ _ L hfg hL G hG hGL
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree E V
  have : Module.Free ℤ L := inferInstance
  rw [← finrank_int_eq L hL]
  let b := Module.finBasis ℤ L
  let r : G →* Module.End ℤ L :=
    { toFun := fun g => AddMonoidHom.toIntLinearMap
        { toFun := fun x => ⟨g.1 x.1, hGL g.1 g.2 x.1 x.2⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }
      map_one' := by ext x; rfl
      map_mul' := fun g h => by ext x; rfl }
  have hr : Function.Injective r := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hL
    intro x hx
    exact congrArg Subtype.val (LinearMap.congr_fun hgh ⟨x, hx⟩)
  let φ : G →* GL (Fin (Module.finrank ℤ L)) ℤ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply hr
    apply (LinearMap.toMatrixAlgEquiv b).injective
    exact congrArg Units.val hgh
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM _ φ.range (Finite.of_equiv _ e.toEquiv)

end GlobalTheory.AutLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaActsOnTameRootStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_acts_on_tame_root : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ ζ : Ω, ζ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ π = ζ * π := by
  first | exact @GlobalTheory.TameSurj.main | exact GlobalTheory.TameSurj.main | (intros; apply GlobalTheory.TameSurj.main <;> assumption)
end

