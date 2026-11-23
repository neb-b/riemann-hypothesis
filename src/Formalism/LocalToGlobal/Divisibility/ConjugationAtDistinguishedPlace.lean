module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.AdjoinCycZeta
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0003
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist

@[expose] public section

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

instance normalQb : Normal ℚ Qb :=
  haveI : IsAlgClosure ℚ Qb := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  IsAlgClosure.normal ℚ Qb

def conjQb (ι : Qb →+* ℂ) : Qb ≃ₐ[ℚ] Qb :=
  AlgEquiv.ofRingEquiv (f := (algC ((starRingEnd ℂ).comp ι)).trans (algC ι).symm) (fun r => by simp)

theorem conjQb_spec (ι : Qb →+* ℂ) (x : Qb) : ι (conjQb ι x) = starRingEnd ℂ (ι x) := by
  have key : conjQb ι x = (algC ι).symm (algC ((starRingEnd ℂ).comp ι) x) := rfl
  rw [key, ← algC_coe ι ((algC ι).symm (algC ((starRingEnd ℂ).comp ι) x)),
    RingEquiv.apply_symm_apply, algC_coe] <;> rfl

theorem conjQb_conjQb (ι : Qb →+* ℂ) (x : Qb) : conjQb ι (conjQb ι x) = x := by
  apply ι.injective
  rw [conjQb_spec, conjQb_spec, Complex.conj_conj]

def cLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : LL ≃ₐ[ℚ] LL := (conjQb ι).restrictNormal LL

theorem cLL_coe (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : LL) : ((cLL ι LL x : LL) : Qb) = conjQb ι x := by
  first
  | exact AlgEquiv.restrictNormal_commutes (conjQb ι) LL x
  | exact AlgEquiv.restrictNormal_commutes (conjQb ι) x

theorem cLL_cLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : LL) : cLL ι LL (cLL ι LL x) = x := by
  apply Subtype.ext
  rw [cLL_coe, cLL_coe, conjQb_conjQb]

@[reducible] def starLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : StarRing LL where
  star := cLL ι LL
  star_involutive := cLL_cLL ι LL
  star_mul a b := by rw [map_mul, mul_comm]
  star_add a b := map_add _ a b

def CoF (_ι : Qb →+* ℂ) (LL : Fld) : Type := LL

namespace CoF

variable (ι : Qb →+* ℂ) (LL : Fld)

instance : Field (CoF ι LL) := inferInstanceAs (Field LL)

instance [FiniteDimensional ℚ LL] : NumberField (CoF ι LL) where
  to_charZero := inferInstanceAs (CharZero LL)
  to_finiteDimensional := inferInstanceAs (FiniteDimensional ℚ LL)

instance [Normal ℚ LL] : StarRing (CoF ι LL) := starLL ι LL

def val : CoF ι LL →+* Qb := LL.val.toRingHom

end CoF

def sig0 (ι : Qb →+* ℂ) (LL : Fld) : CoF ι LL →+* ℂ := ι.comp (CoF.val ι LL)

def v0 (ι : Qb →+* ℂ) (LL : Fld) : InfinitePlace (CoF ι LL) := InfinitePlace.mk (sig0 ι LL)

def K0 (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : Subfield (CoF ι LL) := cmMax (CoF ι LL)

def tauLL {L LL : Fld} [Normal ℚ LL] (h : L ≤ LL) (s : L →ₐ[ℚ] Qb) : L →ₐ[ℚ] LL :=
  ((s.liftNormal Qb).restrictNormal LL).comp (inclusion h)

end Formalism.L2.DIV
