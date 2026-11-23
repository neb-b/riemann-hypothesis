module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TPhi

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem untilt_pow_eq_one (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) (n : ℕ) :
    (e ^ n).untilt = 1 := by
  rw [map_pow, he, one_pow]

theorem log_pow (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (e : Per.Fl l) (he : e.untilt = 1) (x : Per.BdRp l) (hx : Per.IsLog l e x) (n : ℕ) :
    ∀ y : Per.BdRp l, Per.IsLog l (e ^ n) y → y = (n : Per.BdRp l) * x := by
  induction n with
  | zero =>
    intro y hy
    have h0 := untilt_pow_eq_one l e he 0
    have h := LogAdd.log_add l (e ^ 0) (e ^ 0) y y y h0 h0 hy hy (by rwa [← pow_add])
    rw [Nat.cast_zero, zero_mul]
    exact left_eq_add.mp h
  | succ n ih =>
    intro y hy
    have hn := untilt_pow_eq_one l e he n
    obtain ⟨s, _, hs, -, -⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l (e ^ n) hn
    have hs' := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l (e ^ n) s hn hs).2.2.2 j hj
    have h := LogAdd.log_add l (e ^ n) e (j s) x y hn he hs' hx (by rwa [← pow_succ])
    rw [h, ih _ hs', Nat.cast_succ, add_mul, one_mul]

theorem t_phi : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l,
    phiA l C.t = (l : Per.Acris l) * C.t := by
  intro l _ C
  have he : C.ε.untilt = 1 := (core_isEps l C).1
  obtain ⟨-, -, h3, h4⟩ := _root_.GlobalTheory.MemLoc.LogFun.log_fun l C.ε C.t he C.t_log
  have h5 := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l (C.ε ^ l) _ (untilt_pow_eq_one l _ he l) h3).2.2.2 C.j C.j_cris
  apply _root_.GlobalTheory.MemLoc.crisP_injective l C.j C.j_cris
  rw [map_mul, map_natCast]
  exact log_pow l C.j C.j_cris C.ε he _ (h4 C.j C.j_cris) l _ h5

end GlobalTheory.MemLoc.TPhi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
section
noncomputable section
namespace GlobalTheory.MemLoc.TAct
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

variable {l : ℕ} [Fact l.Prime]

theorem logA_mul {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) {e e' : Per.Fl l} {y y' : Per.Acris l}
    (he : e.untilt = 1) (he' : e'.untilt = 1) (hy : IsLogA e y) (hy' : IsLogA e' y') :
    IsLogA (e * e') (y + y') := by
  have hee : (e * e').untilt = 1 := by rw [map_mul, he, he', one_mul]
  obtain ⟨z, _, hz, -, -⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l (e * e') hee
  have h := GlobalTheory.MemLoc.LogAdd.log_add l e e' (j y) (j y') (j z) he he'
    ((_root_.GlobalTheory.MemLoc.LogFun.log_fun l e y he hy).2.2.2 j hj) ((_root_.GlobalTheory.MemLoc.LogFun.log_fun l e' y' he' hy').2.2.2 j hj)
    ((_root_.GlobalTheory.MemLoc.LogFun.log_fun l _ z hee hz).2.2.2 j hj)
  rw [← map_add (f := _)] at h
  rw [← _root_.GlobalTheory.MemLoc.crisP_injective l j hj h]
  exact hz

theorem logA_pow {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) {e : Per.Fl l} {y : Per.Acris l}
    (he : e.untilt = 1) (hy : IsLogA e y) (n : ℕ) : IsLogA (e ^ n) ((n : Per.Acris l) * y) := by
  induction n with
  | zero =>
    have h1 : (1 : Per.Fl l).untilt = 1 := map_one _
    obtain ⟨z, _, hz, -, -⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l 1 h1
    have h2 := logA_mul hj h1 h1 hz hz
    rw [one_mul] at h2
    have h3 := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l 1 z h1 hz).1 _ h2
    have h4 : z = 0 := by simpa using h3
    rw [pow_zero, Nat.cast_zero, zero_mul, ← h4]
    exact hz
  | succ n ih =>
    have := logA_mul hj (by rw [map_pow, he, one_pow]) he ih hy
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact this

theorem iter_pow (e : Per.Fl l) (m : ℕ) :
    (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e) ^ (l ^ m) = e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have : ∀ x : Per.Fl l, ((frobeniusEquiv (Per.Fl l) l).symm x) ^ l = x := fun x => by
      rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
    rw [this, ih]

theorem eps_untilt (C : Core l) : C.ε.untilt = 1 := by
  have h := C.ε_root 0
  rw [C.ζ_zero, map_one] at h
  exact Subtype.ext h

theorem zeta_pow (C : Core l) (m : ℕ) : C.ζ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [C.ζ_zero]
  | succ m ih => rw [pow_succ', pow_mul, C.ζ_succ, ih]

theorem cong (C : Core l) (g : GQ l) (m : ℕ) : ∃ w : Per.Acris l,
    sigA g C.t - ((PadicInt.toZModPow m (C.χ g : ℤ_[l])).val : Per.Acris l) * C.t = (l : Per.Acris l) ^ m * w := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set a := (PadicInt.toZModPow m (C.χ g : ℤ_[l])).val with ha
  obtain ⟨b, hb⟩ : ∃ b, a + b = l ^ m := Nat.exists_eq_add_of_le (ZMod.val_lt _).le |>.imp fun _ h => h.symm
  set em := ((frobeniusEquiv (Per.Fl l) l).symm)^[m] C.ε with hem
  have hε := eps_untilt C
  have hr : ((em.untilt : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m) := C.ε_root m
  have he : (Per.σF g em * em ^ b).untilt = 1 := by
    rw [map_mul, map_pow, GlobalTheory.RingBasics.untilt_σF]
    apply Subtype.ext
    have h1 : ((Per.σO g em.untilt : Per.OC l) : ℂ_[l]) = Per.σC g (em.untilt : ℂ_[l]) :=
      GlobalTheory.RingIface.sigO_coe l g _
    have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (C.ζ m)) = algebraMap (Om l) ℂ_[l] (g (C.ζ m)) :=
      GlobalTheory.RingBasics.σC_coe g _
    push_cast
    rw [h1, hr, h2, C.χ_cyc g m _ (zeta_pow C m), ← ha, ← map_pow, ← map_mul, ← pow_add, hb, zeta_pow, map_one]
  obtain ⟨z, _, hz, -, -⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l _ he
  have h1 := logA_pow C.j_cris he hz (l ^ m)
  have hgε : (Per.σF g C.ε).untilt = 1 := by rw [GlobalTheory.RingBasics.untilt_σF, hε, map_one]
  have h2 := logA_mul C.j_cris hgε (by rw [map_pow, hε, one_pow])
    ((_root_.GlobalTheory.MemLoc.LogFun.log_fun l _ _ hε C.t_log).2.1 g) (logA_pow C.j_cris hε C.t_log b)
  have h3 : (Per.σF g em * em ^ b) ^ (l ^ m) = Per.σF g C.ε * C.ε ^ b := by
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm b, pow_mul, hem, iter_pow]
  rw [h3] at h1
  have h4 := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l _ _ (by rw [map_mul, hgε, map_pow, hε, one_pow, one_mul]) h1).1 _ h2
  refine ⟨z - C.t, ?_⟩
  have h5 : (a : Per.Acris l) + b = (l : Per.Acris l) ^ m := by exact_mod_cast congrArg (Nat.cast : ℕ → Per.Acris l) hb
  push_cast at h4
  linear_combination h4 - C.t * h5

theorem t_act : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l),
    sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  intro l _ C g
  haveI := (acris_basic l).1
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Per.Acris l)})]
  intro m
  obtain ⟨w, hw⟩ := cong C g m
  set x : ℤ_[l] := (C.χ g : ℤ_[l])
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) hc
  rw [map_mul, map_sub, map_pow, map_natCast, map_natCast, RingHom.comp_apply, RingHom.comp_apply] at hc'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨w - algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t, ?_⟩
  linear_combination - hw - C.t * hc'

end GlobalTheory.MemLoc.TAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionReducedOfJacobson
section
open IsLocalRing

namespace GlobalTheory.CompletionReduced

theorem map_le_jacobson_of_comap_isMaximal {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : ∀ M : Ideal B, M.IsMaximal → (M.comap f).IsMaximal) (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) : I.map f ≤ Ideal.jacobson (⊥ : Ideal B) := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro M ⟨-, hM⟩
  rw [Ideal.map_le_iff_le_comap]
  exact hI.trans (sInf_le ⟨bot_le, hf M hM⟩)

theorem exists_lt_of_add_one_le (e : WithBot ℕ∞) (n : ℕ) (h0 : 0 ≤ e) (h : e + 1 ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, m < n ∧ e ≤ (m : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe, top_add] at h'
      exact absurd h' (by simp)
    | coe k =>
      refine ⟨k, ?_, le_rfl⟩
      have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      exact_mod_cast this

theorem isReduced_of_normal (n : ℕ)
    (ih : ∀ m < n, ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      ringKrullDim D ≤ (m : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
        IsReduced (AdicCompletion J D))
    (N : Type) [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra.EssFiniteType ℤ N]
    (hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞)) (I : Ideal N)
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal N)) : IsReduced (AdicCompletion I N) := by
  haveI : IsNoetherianRing N := Algebra.EssFiniteType.isNoetherianRing ℤ N
  by_cases hbot : I = ⊥
  · subst hbot
    exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.toRingEquiv.toRingHom
      (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.injective
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let R := AdicCompletion I N
  haveI : IsNoetherianRing R := _root_.GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion N I
  haveI : Module.Flat N R := AdicCompletion.flat_of_isNoetherian I
  have hxR : algebraMap N R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular N x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap N R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hxjac : algebraMap N R x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have h1 : IsAdicComplete I R := AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)
    have h2 : IsAdicComplete (I.map (algebraMap N R)) R := (IsAdicComplete.map_algebraMap_iff _ _).2 h1
    exact IsAdicComplete.le_jacobson_bot (I.map (algebraMap N R)) (Ideal.mem_map_of_mem _ hxI)
  have hredq : ∀ q : Ideal N, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap N R)) := by
    intro q hq hxq
    obtain ⟨e⟩ := _root_.GlobalTheory.adicCompletion_quotient_ringEquiv N I q
    haveI : IsDomain (N ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType N (N ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (N ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (N ⧸ q)
      haveI : IsScalarTower ℤ N (N ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ N (N ⧸ q)
    have hj : I.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (N ⧸ q)) :=
      map_le_jacobson_of_comap_isMaximal _
        (fun M hM => Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) I hIjac
    have hd1 : ringKrullDim (N ⧸ q) + 1 ≤ (n : WithBot ℕ∞) := by
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
      have h2 : ringKrullDim (N ⧸ q) ≤ ringKrullDim (N ⧸ Ideal.span {x}) :=
        ringKrullDim_le_of_surjective _
          (Ideal.Quotient.factor_surjective (by rwa [Ideal.span_singleton_le_iff_mem]))
      exact ((add_le_add h2 le_rfl).trans h1).trans hdimN
    obtain ⟨m, hmn, hm⟩ := exists_lt_of_add_one_le _ n ringKrullDim_nonneg_of_nontrivial hd1
    haveI := ih m hmn (N ⧸ q) hm _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  refine _root_.GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes R (algebraMap N R x) hxR hxjac ?_
  intro P _ hP
  obtain ⟨h1, -⟩ := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient N R x hx0 hredq P hP
  exact h1

theorem isReduced_of_dim_le : ∀ (n : ℕ) (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    ringKrullDim D ≤ (n : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
      IsReduced (AdicCompletion J D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ _ _ hdim J hJ
  haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D

  let N := integralClosure D (FractionRing D)
  haveI : Module.Finite D N := _root_.GlobalTheory.finite_integralClosure_of_essFiniteType_int D
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing D)
  have hinj : Function.Injective (algebraMap D N) := by
    intro a b hab
    have := congrArg (fun y : N => (y : FractionRing D)) hab
    exact IsFractionRing.injective D (FractionRing D) this
  have hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞) := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]; exact hdim
  haveI : Algebra.EssFiniteType D N := inferInstance
  haveI hessN : @Algebra.EssFiniteType ℤ N _ _ (Ring.toIntAlgebra _) := by
    letI := Ring.toIntAlgebra N
    haveI : IsScalarTower ℤ D N := .of_algebraMap_eq fun z => by simp
    exact Algebra.EssFiniteType.comp ℤ D N
  have hIjac : J.map (algebraMap D N) ≤ Ideal.jacobson (⊥ : Ideal N) :=
    map_le_jacobson_of_comap_isMaximal _
      (fun M hM => Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) M) J hJ
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_injective_adicCompletion_map_of_finite D N hinj J
  haveI := isReduced_of_normal n ih N hdimN _ hIjac
  exact isReduced_of_injective f hf

theorem isReduced_adicCompletion : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D]
    (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  intro D _ _ _ J hJ
  have hlt := _root_.GlobalTheory.ringKrullDim_lt_top_of_essFiniteType D
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim D ≤ (m : WithBot ℕ∞) := by
    generalize ringKrullDim D = e at hlt ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe k => exact ⟨k, le_rfl⟩
  exact isReduced_of_dim_le m D hm J hJ

end GlobalTheory.CompletionReduced
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfQuotFontaineXiPowTorsionFreeSeparated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem quot_pow_torsionFree_sep {A O : Type*} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    (θ : A →+* O) (ξ p : A) (hξ : ξ ≠ 0) (hker : ∀ a, θ a = 0 ↔ ξ ∣ a) (hp : θ p ≠ 0)
    (hsep : ∀ x : O, (∀ k : ℕ, θ p ^ k ∣ x) → x = 0) (n : ℕ) :
    (∀ a : A, ξ ^ n ∣ p * a → ξ ^ n ∣ a) ∧
      ∀ a : A, (∀ k : ℕ, ∃ b : A, ξ ^ n ∣ a - p ^ k * b) → ξ ^ n ∣ a := by
  have h0 : ∀ (m : ℕ) (x : A), ξ ^ (m + 1) ∣ x → θ x = 0 := fun m x hx =>
    (hker x).2 ((dvd_pow_self ξ m.succ_ne_zero).trans hx)
  have hθξ : θ ξ = 0 := (hker ξ).2 dvd_rfl
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have h1 := h0 n _ ha
      rw [map_mul] at h1
      obtain ⟨a', rfl⟩ := (hker a).1 ((mul_eq_zero.1 h1).resolve_left hp)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hξ] at ha
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      exact ih.1 a' ha
    · have h1 : θ a = 0 := hsep _ fun k => by
        obtain ⟨b, hb⟩ := ha k
        have h2 := h0 n _ hb
        rw [map_sub, map_mul, map_pow, sub_eq_zero] at h2
        exact ⟨θ b, h2⟩
      obtain ⟨a', rfl⟩ := (hker a).1 h1
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      refine ih.2 a' fun k => ?_
      obtain ⟨b, hb⟩ := ha k
      have h2 := h0 n _ hb
      rw [map_sub, h1, map_mul, map_pow, zero_sub, neg_eq_zero] at h2
      obtain ⟨b', rfl⟩ := (hker b).1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero k hp))
      refine ⟨b', ?_⟩
      rwa [pow_succ', mul_left_comm, ← mul_sub, mul_dvd_mul_iff_left hξ] at hb

theorem ainf_quot_xi_pow_torsionFree_sep : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ ∀ a : Per.Ainf l, (∀ k : ℕ, ∃ b : Per.Ainf l, xi e ^ n ∣ a - ((l : ℕ) : Per.Ainf l) ^ k * b) → xi e ^ n ∣ a := by
  intro l _ e he n
  obtain ⟨-, hdom, -, hk⟩ := theta_ker_facts l
  obtain ⟨h1, h2⟩ := hk e he
  refine quot_pow_torsionFree_sep (Per.θ l) (xi e) _ h2 (fun a => ?_) ?_ (fun x hx => ?_) n
  · rw [← RingHom.mem_ker, h1, Ideal.mem_span_singleton]
  · rw [map_natCast]
    exact fun h => GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)
  · rw [map_natCast] at hx
    refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.OC l)}) inferInstance x fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiltRootOfUnity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_tilt_root_of_unity : ∀ (l : ℕ) [Fact l.Prime] (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → ∃ e : Per.Fl l, e ^ m = 1 ∧ (e.untilt : ℂ_[l]) = (x : ℂ_[l]) := by
  intro l hl x m hm hlm hx
  obtain ⟨h1, h2, h3⟩ := tilt_facts l
  have hxC : (x : ℂ_[l]) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) ℂ_[l]) hx
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(x : ℂ_[l])‖ ≤ 1 := by
    have h := congrArg norm hxC
    rw [norm_pow, norm_one] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h).le
  obtain ⟨y, hyx⟩ : ∃ y : Per.OC l, (y : ℂ_[l]) = (x : ℂ_[l]) := ⟨⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩, rfl⟩
  have hy : y ^ m = 1 := Subtype.ext (by push_cast; rw [hyx, hxC])
  have hc : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (m.totient - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hc
  have hstep : ∀ z : Per.OC l, z ^ m = 1 → (z ^ a) ^ l = z := fun z hz => by
    rw [← pow_mul]
    simpa using pow_eq_pow_of_modEq ha hz
  have hpm : ∀ n : ℕ, (y ^ a ^ n) ^ m = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  obtain ⟨e, he⟩ := h1 (fun n => y ^ a ^ n) (fun n => by
    show (y ^ a ^ (n + 1)) ^ l = y ^ a ^ n
    rw [pow_succ, pow_mul]
    exact hstep _ (hpm n))
  refine ⟨e, h2 _ fun n => by rw [h3, he, hpm], ?_⟩
  have h0 := he 0
  rw [pow_zero, pow_one] at h0
  rw [← hyx, ← h0]
  rfl

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV

namespace GlobalTheory.Mem.StabDet

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.UpperTheory.Reformulated.B.Ybf4.isIntegral_det L hfg hsp γ hγ

theorem eq_pm_one_of_unitary {R : Ranks} (H : Formalism.BasicNotions.Host R) :
    letI := H.cmStar; ∀ z : H.E, z ∈ unitary H.E → IsIntegral ℤ z → ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  letI := H.cmStar
  intro z hu hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star z * z = 1 := hu.1
    have h2 : φ (star z) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  exact ⟨n, hn, hp⟩

end GlobalTheory.Mem.StabDet
end

