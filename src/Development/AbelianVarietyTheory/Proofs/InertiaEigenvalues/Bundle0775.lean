module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefActIo

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_fock_of_vac {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hB : B.Good) (hψ : ψ.Good)
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hB.frame.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, GlobalTheory.RealFockAction.om_vac hB hψ hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem act_of_mem_GfC (B : Base S T) {k : GA D S} (hk : k ∈ GfC S) : B.act k = 1 := by
  have e : realGL B.F.θ S k = 1 := by
    funext τ
    change (Formalism.UG.bc (B.F.θ τ)) (infHom S k) = 1
    rw [show infHom S k = 1 from hk, map_one]
  rw [Base.act, MonoidHom.comp_apply, e, map_one]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem thetaVector_laws (hC : GlobalTheory.Hk3.Core R F) (t : T0) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧
      (∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) (R.vP i t)) ∧
      Function.Injective (R.ptP i t) := by
  have hP := hC.thP
  have hM := hC.models
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h := hP.pt_theta i t 1
    have e : R.ptP i t 1 = R.vP i t := by
      unfold RealDat.ptP pureTensorO pureTensorL
      rw [show (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 from rfl,
        Module.Basis.constr_basis]
      simp [opPow]
    rwa [e] at h
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hf
  have hne : R.vP i t ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i t)
  exact ⟨hf, hv, GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _
    (hP.ωP i t).std hM.inf (fun τ => GlobalTheory.OneMapRef.VecP.isCartanInv_one_of_onb (hM.BV i τ)) (hM.BV i) hf hne hv⟩

theorem act_ioP_inf (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    ∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  intro u hu x w
  obtain ⟨hf, hv, hinj⟩ := thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  apply hinj
  rw [hpt, hpt, ← om_fock_of_vac hB hψ hω hf' hv' hu, ← hpt, ← hpt]
  exact (hC.thP.ioP i t).1 u hu x w

theorem act_ioP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    (∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w)) ∧
      ∀ (u : GA D (Vc D i)) x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  refine ⟨act_ioP_inf hC hB h hψ ht, fun u x w => ?_⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin u
  set a := GlobalTheory.AutMult.toInf (Vc D i) u
  set k := GlobalTheory.AutMult.toFin (Vc D i) u
  rw [← e, map_mul, map_mul, act_of_mem_GfC B k.2, (hC.models.cV i).1 _ k.2, mul_one, mul_one]
  exact act_ioP_inf hC hB h hψ ht _ a.2 x w

end GlobalTheory.CoefActIo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegral
section
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

theorem bnd_of_integral_over_prime : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  intro E _ _ p hp n A hA
  let S : Set (HeightOneSpectrum (𝓞 E)) := {Q | ∃ i j, ¬ Valued.v ((A i j) Q) ≤ 1}
  have hS : S.Finite := by
    have hsub : S ⊆ ⋃ i, ⋃ j, {Q | ¬ (A i j) Q ∈ Q.adicCompletionIntegers E} := by
      rintro Q ⟨i, j, h⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨i, j, fun hm => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm)⟩
    refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub
    exact Filter.eventually_cofinite.mp (A i j).2
  refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
  · have hpQ : (p : 𝓞 E) ∉ Q.asIdeal := by
      obtain ⟨i', j', h⟩ := hQ
      exact fun hm => h (hA Q hm i' j')
    exact exists_coprime_natCast_mul_v_le_one p hp Q hpQ _
  · by_contra h
    exact hQ ⟨i, j, h⟩

end GlobalTheory.StdAtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOver
section
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

theorem exists_pow_mul_v_le_one_of_mem {E : Type} [Field E] [NumberField E]
    (p : ℕ) (hp : p.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hpQ : (p : 𝓞 E) ∈ Q.asIdeal)
    (x : Q.adicCompletion E) :
    ∃ a : ℕ, ∀ d : ℕ, a ≤ d → Valued.v (((p ^ d : ℕ) : Q.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hbx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b}) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have hmem : (N : 𝓞 E) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  set e := N.factorization p with he
  set r := N / p ^ e with hr
  have hcop : r.Coprime p := (Nat.coprime_ordCompl hp hN0).symm
  have hsplit : p ^ e * r = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hrQ : (r : 𝓞 E) ∉ Q.asIdeal := by
    intro hrQ
    have h1 : ((Nat.gcd r p : ℕ) : ℤ) = r * Nat.gcdA r p + p * Nat.gcdB r p := Nat.gcd_eq_gcd_ab r p
    rw [hcop] at h1
    have h2 := congrArg (Int.cast : ℤ → 𝓞 E) h1
    push_cast at h2
    have h3 : (1 : 𝓞 E) ∈ Q.asIdeal := by
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hrQ) (Ideal.mul_mem_right _ _ hpQ)
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hvr : Valued.v ((r : Q.adicCompletion E)) = 1 := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (r : 𝓞 E)
    have h2 : Q.valuation E (algebraMap (𝓞 E) E (r : 𝓞 E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hrQ
    simp only [map_natCast] at h1 h2
    rw [h1, h2]
  have hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1 := by
    have e' : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) *
        (algebraMap (𝓞 E) (Q.adicCompletion E) b) := by
      rw [← map_mul, hc, map_natCast]
    rw [e', mul_assoc, Valuation.map_mul, mul_comm _ x]
    refine mul_le_one' ?_ hbx
    have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hex : Valued.v (((p ^ e : ℕ) : Q.adicCompletion E) * x) ≤ 1 := by
    rw [← hsplit] at hNx
    rw [Nat.cast_mul, mul_comm ((p ^ e : ℕ) : Q.adicCompletion E), mul_assoc, Valuation.map_mul,
      hvr, one_mul] at hNx
    exact hNx
  refine ⟨e, fun d hd => ?_⟩
  have hde : p ^ d = p ^ (d - e) * p ^ e := by rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hde, Nat.cast_mul, mul_assoc, Valuation.map_mul]
  exact mul_le_one' (natCast_adicCompletion_v_le_one Q _) hex

theorem exists_pow_clears_denom_over :
    ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((((p ^ d : ℕ) : FiniteAdeleRing (𝓞 E) E) * A i j) Q) ≤ 1 := by
  intro E _ _ p hp n A
  classical
  have h0 : Ideal.span {(p : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hF := Ideal.finite_factors h0
  have hmemF : ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal →
      Q ∈ {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {(p : 𝓞 E)}} := fun Q hQ =>
    Ideal.dvd_span_singleton.mpr hQ
  let f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ := fun t =>
    if h : (p : 𝓞 E) ∈ t.1.asIdeal then
      Classical.choose (exists_pow_mul_v_le_one_of_mem p hp t.1 h ((A t.2.1 t.2.2) t.1)) else 0
  let T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n) := hF.toFinset ×ˢ Finset.univ
  refine ⟨T.sup f, fun d hd Q hQ i j => ?_⟩
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, map_natCast, ← hev]
  have hmem : (Q, i, j) ∈ T := by
    simp only [T, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_univ, and_true]
    exact hmemF Q hQ
  have hle : f (Q, i, j) ≤ d := le_trans (Finset.le_sup hmem) hd
  have hspec := Classical.choose_spec (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q))
  have hfQ : f (Q, i, j) = Classical.choose (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q)) := by
    simp only [f, dif_pos hQ]
  exact hspec d (hfQ ▸ hle)

end GlobalTheory.StdAtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LevelFix

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLiftFiniteGroup_one_of_mem_coeffSpaceLevel (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) (hk : k ∈ levW R i) :
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k := by
  refine ⟨hk.1, hk.2.1, ?_⟩
  have h2 := hk.2.2
  have e : (R.datWp i R.triv).P.H = ⊥ := rfl
  rw [e] at h2
  exact Subgroup.mem_bot.1 h2

theorem realDatum_identity_lifts_identity (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_flag_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have := (levChar D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))).map_one
  unfold levChi
  rw [map_one]
  exact congrArg Units.val this

theorem levW_fix_vP (R : RealDat D A Ks) (F : Face D A) (h : Laws R F) (i : Fin D.R.m) (t : T)
    (k : GA D (Wc D i)) (hk : k ∈ levW R i) : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  have e := _root_.GlobalTheory.VecInv.omega_lifts_vP R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 1 k (realDatum_identity_lifts_identity R i t)
    (isLiftFiniteGroup_one_of_mem_coeffSpaceLevel R i k hk)
  rw [e, levChi_flag_one R i t, inv_one, one_smul]

theorem levFix : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h _ i t k hk P
  have hv : R.ωP i t (1, k) (R.vP i t) = (1 : ℂ) • R.vP i t := by
    rw [one_smul]; exact levW_fix_vP R F h i t k hk
  have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) h.models.inf
    (h.thP.ωP i t) _ _ _ _ _ (h.thP.pt_theta i t) 1 (Subgroup.one_mem _) k hk.1 1 hv P
  exact this.trans (one_smul ℂ _)

end GlobalTheory.RawLift.LevelFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtension
section
noncomputable section

namespace GlobalTheory.CoefExtC

section General

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.AdTh.CoefExt

variable {K : Type} [Field K] {σ : K →+* ℂ} {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n}
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_ext (c' : VV K lam →ₛₗ[σ] W) (hs : Submodule.span ℂ (Set.range c') = ⊤)
    (hli : LinearIndependent ℂ fun j => c' (bVV K lam j)) :
    ∃ c : VV ℂ lam →ₗ[ℂ] W, (∀ v, c (up σ lam v) = c' v) ∧ Function.Bijective c ∧
      ∀ d : VV ℂ lam →ₗ[ℂ] W, (∀ v, d (up σ lam v) = c' v) → d = c := by
  classical
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun j => up σ lam (bVV K lam j)) := by
    intro v _
    obtain ⟨a, rfl⟩ := exists_coord σ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcard : Fintype.card (VVIdx lam) = Module.finrank ℂ (VV ℂ lam) := (Module.finrank_eq_card_basis (bVV ℂ lam)).symm
  let b : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) := basisOfTopLeSpanOfCardEqFinrank _ hsp hcard
  have hb : ∀ j, b j = up σ lam (bVV K lam j) := fun j => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hsp hcard) j
  have hsw : ⊤ ≤ Submodule.span ℂ (Set.range fun j => c' (bVV K lam j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bVV K lam).sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let w : Module.Basis (VVIdx lam) ℂ W := Module.Basis.mk hli hsw
  have hc : ∀ j, (b.equiv w (Equiv.refl _)) (up σ lam (bVV K lam j)) = c' (bVV K lam j) := by
    intro j
    rw [← hb, Module.Basis.equiv_apply]
    exact Module.Basis.mk_apply hli hsw j
  refine ⟨(b.equiv w (Equiv.refl _)).toLinearMap, fun v => ?_, (b.equiv w (Equiv.refl _)).bijective, fun d hd => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bVV K lam).sum_repr v, up_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smulₛₗ, LinearEquiv.coe_coe, hc]
  · refine b.ext fun j => ?_
    rw [hb, hd, LinearEquiv.coe_coe, hc]

theorem li_basis (c' : VV K lam →ₛₗ[σ] W)
    (h : ∀ (m : ℕ) (b : Fin m → VV K lam), LinearIndependent K b → LinearIndependent ℂ fun j => c' (b j)) :
    LinearIndependent ℂ fun j => c' (bVV K lam j) := by
  let e := Fintype.equivFin (VVIdx lam)
  have h1 := h _ (bVV K lam ∘ e.symm) ((bVV K lam).linearIndependent.comp _ e.symm.injective)
  have h2 := h1.comp e e.injective
  simpa [Function.comp_def] using h2

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 800000 in
theorem exists_extC_bijective_unique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∃ c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, ExtC R i (inC M.c') M.c0' c ∧ Function.Bijective c ∧ ∀ c', ExtC R i (inC M.c') M.c0' c' → c' = c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hE : ∀ v, O.c0' (GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨-, h2, h3⟩ := hT.mapL i
  obtain ⟨c, h4, h5, h6⟩ := exists_ext (W := (R.cV i).W) O.c0' (GlobalTheory.AdTh.CoefExt.span_top (W := (R.cV i).W) hE h3)
    (li_basis (W := (R.cV i).W) O.c0' fun m b hb => GlobalTheory.AdTh.CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb)
  refine ⟨c, fun v v' hv => ?_, h5, fun d hd => h6 d fun v => hd v _ rfl⟩
  rw [show v' = GlobalTheory.AdTh.CoefExt.up (inC O.c') (lamV D i) v from Subtype.ext hv]
  exact h4 v

end GlobalTheory.CoefExtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverCharacterTrivialOnLevelDeterminants
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CoverXiDet

theorem natM_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
  rw [← l.prod] at h
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h

theorem natM_mem_of_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l l₂ : Level H)
    (I P : Ideal (𝓞 E)) (h : l₂.Mb = l.Mb * I) (hI : I ≤ P) : ((l₂.M : ℕ) : 𝓞 E) ∈ P := by
  have h1 := natM_mem_Mb l₂
  rw [h] at h1
  exact hI (Ideal.mul_le_right (I := l.Mb) (J := I) h1)

end GlobalTheory.CoverXiDet

namespace GlobalTheory.CoverXiDet


set_option maxHeartbeats 4000000 in
theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (t : Tp) (u : GA D (Wc D i)), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ t).l₂.M : ℕ) • w) → M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hM t u _ hw
  have hL := hC.lev
  have hN : ∀ PP ∈ R.Q (tup t), (((M.dδ t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP =>
    natM_mem_of_half _ _ _ _ ((hM.cov t).1).2.2.2.1 ((hM.tuple t).half.2.1 PP hPP)
  obtain ⟨xi', hxi1, hxi2, -, -⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi (tup t))
    (hL.xi_fin (tup t)).choose (hL.xi_fin (tup t)).choose_spec.1 (hL.xi_fin (tup t)).choose_spec.2 (hL.xi_triv (tup t))
    (hL.xi_tame (tup t))
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Wc D i) u
  have e1 := (hM.tuple t).xi u x hx
  have e2 := hxi1 u x hx
  have e3 : xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
    refine hxi2 _ (M.dδ t).l₂.odd (GlobalTheory.TupleCover.unrAt_of_not_mem R hL (tup t) _ hN) u ?_
    obtain ⟨w, hw1, hw2⟩ := hw
    exact ⟨w, (GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers D).symm ▸ hw1, hw2⟩
  apply Units.ext
  rw [e1, ← e2, e3]

end GlobalTheory.CoverXiDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdelesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotentPlaceChart_finiteAdeles : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), LevChart e PP v φ ι := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_levChart | exact GlobalTheory.DownLift.SplitCoef.exists_levChart | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_levChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → (harm m w B).map (harmFn m w B) = Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  first | exact @GlobalTheory.ExportSeries.Onto.map_harm_eq | exact GlobalTheory.ExportSeries.Onto.map_harm_eq | (intros; apply GlobalTheory.ExportSeries.Onto.map_harm_eq <;> assumption)
end

