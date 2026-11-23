module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.HostCls
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoprimeAbsNormCcKOfGIdx
section
open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem exists_prime_ge_dvd_absNorm {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] {p : ℕ} (hp : p.Prime) (I : Ideal S) (hI : I ≠ ⊥)
    (h : p ∣ Ideal.absNorm I) :
    ∃ P : Ideal S, P.IsPrime ∧ I ≤ P ∧ p ∣ Ideal.absNorm P := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ J hJ =>
    rw [Ideal.isUnit_iff.1 hJ, Ideal.absNorm_top] at h
    exact absurd (Nat.dvd_one.1 h) hp.one_lt.ne'
  | h₃ J P hJ hP ih =>
    rw [map_mul] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ⟨P, Ideal.isPrime_of_prime hP, Ideal.mul_le_left, h⟩
    · obtain ⟨Q, hQ, hle, hd⟩ := ih hJ h
      exact ⟨Q, hQ, Ideal.mul_le_right.trans hle, hd⟩

theorem coprime_absNorm_ccK_of_gIdx :
    ∀ (D : D7) (T p : ℕ), GIdx D.host T p → Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  intro D T p h
  obtain ⟨hp, -, hc, -⟩ := h
  have hj : jacobiSym (-(D.host.d : ℤ)) p ≠ 1 :=
    ((primeClass_eq_inert_iff _).1 hc).2.2.2.1
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨P, hP, hle, hdP⟩ := exists_prime_ge_dvd_absNorm hp _ D.host.ccK_ne_bot hd
  obtain ⟨h1, h2⟩ := D.host.ccK_split P hP hle
  rw [← (Nat.prime_dvd_prime_iff_eq hp h1).1 hdP] at h2
  exact hj h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC TensorProduct

namespace GlobalTheory.IntClLocal

theorem isLocalRing_of_isIntegral_of_henselian (O : Type) [CommRing O] [HenselianLocalRing O]
    (S : Type) [CommRing S] [IsDomain S] [Algebra O S] [Algebra.IsIntegral O S] : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have : Module.Finite O (Algebra.adjoin O {a}) :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
  have := GlobalTheory.TameKummer.isLocalRing_of_finite O (Algebra.adjoin O {a})
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨a, Algebra.self_mem_adjoin_singleton O a⟩ : Algebra.adjoin O {a}) with h | h
  · exact Or.inl (h.map (Algebra.adjoin O {a}).val)
  · exact Or.inr (by simpa using h.map (Algebra.adjoin O {a}).val)

end GlobalTheory.IntClLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTrace
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.TraceOrigin


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ev_eq_trace_quot : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  intro k _ _ F K _ _ _ _ _ _ d x hc ev hker h a ha
  haveI : Module.IsTorsionFree (rA k x {0}) (integralClosure (rA k x {0}) K) := inferInstance
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {0}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI := hc.fin
  haveI : Module.Finite (rA k x {0}) (integralClosure (rA k x {0}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {0} (Finset.singleton_nonempty 0)).1
  haveI := GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hc 0
  haveI : IsIntegrallyClosed (integralClosure (rA k x {0}) K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  have hsurj : Function.Surjective ev := fun c => ⟨algebraMap k _ c, ev.commutes c⟩
  haveI hmax : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hsurj
  let h' : integralClosure (rA k x {0}) K := ⟨h.1, h.2⟩
  have hint : a = Algebra.intTrace (rA k x {0}) (integralClosure (rA k x {0}) K) h' := by
    apply Subtype.ext
    exact ha.trans (Algebra.algebraMap_intTrace (A := rA k x {0}) (K := F) (L := K) h').symm
  have key := GlobalTheory.trace_quotient_eq_of_projective (rA k x {0}) (integralClosure (rA k x {0}) K) (RingHom.ker ev) h'
  set p := RingHom.ker ev with hp
  let e₁ : (rA k x {0}) ⧸ p ≃+* k := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
  have he₁ : ∀ y, e₁ (Ideal.Quotient.mk p y) = ev y := fun y => rfl
  let φ : integralClosure (rA k x {0}) K ≃+* rB k K x {0} :=
    { toFun := fun b => ⟨b.1, b.2⟩, invFun := fun b => ⟨b.1, b.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  set J : Ideal (rB k K x {0}) := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))) with hJdef
  have hJ : J = (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))).map φ := by
    rw [hker, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  let e₂ := Ideal.quotientEquiv (p.map (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K))) J φ hJ
  have hcomm : (algebraMap k (rB k K x {0} ⧸ J)).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap _ _) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_)
    change Ideal.Quotient.mk J (algebraMap k _ (ev y)) = Ideal.Quotient.mk J (φ (algebraMap _ _ y))
    rw [Ideal.Quotient.eq]
    have hmem : y - algebraMap k _ (ev y) ∈ p := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h3 : φ (algebraMap (rA k x {0}) (integralClosure (rA k x {0}) K) (y - algebraMap k _ (ev y))) ∈ J :=
      hJ ▸ Ideal.mem_map_of_mem φ (Ideal.mem_map_of_mem _ hmem)
    convert J.neg_mem h3 using 1
    rw [map_sub, map_sub, neg_sub]
    congr 1
    apply Subtype.ext
    change algebraMap k K (ev y) = algebraMap F K (algebraMap k F (ev y))
    exact IsScalarTower.algebraMap_apply k F K _
  have htr := Algebra.trace_eq_of_equiv_equiv e₁ e₂ hcomm (Ideal.Quotient.mk _ h')
  rw [key] at htr
  have h2 : e₂ (Ideal.Quotient.mk _ h') = Ideal.Quotient.mk J h := rfl
  have := congrArg e₁ htr
  rw [RingEquiv.apply_symm_apply, h2, he₁] at this
  rw [hint, this]

end GlobalTheory.PD.TraceOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
section
namespace GlobalTheory.LocalInv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem weightRegular_definite : ∀ (D : D7), GlobalTheory.LocalInv.WeightRegular D.nd D.naut :=
  fun D => weightRegular_of_ext D.nd D.naut D.nbc

end GlobalTheory.LocalInv
end

