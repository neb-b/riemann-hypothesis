module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapStab
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0013
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0006
public import Formalism.LocalRingCardinality.DataNChoice
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0003
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0003
public import Formalism.LocalRingCardinality.Bundle0006
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.HermitianLattices.Bundle0003

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.CC.Idx

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

end Defs

section SA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem inverse_in_adic_integers (c : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) [Decidable (Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1)] :
    (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹) ∈ w.adicCompletionIntegers F := by
  split_ifs with h
  · exact zero_mem _
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
    have h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) = 1 :=
      le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v w c)) (not_lt.1 h)
    rw [h1, inv_one]


open Classical in
def a_u (c : 𝓞 F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹, Filter.Eventually.of_forall fun w => inverse_in_adic_integers c w⟩

theorem a_u_mem (c : 𝓞 F) : a_u c ∈ intAd F := fun w => inverse_in_adic_integers c w

theorem mem_S_of_loc (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ w, prV (E := E) w x ∈ intV E w) :
    x ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  obtain ⟨c, hc0, hc⟩ := loc_int_bound F E
  have hfin := levelaf_finite_places c hc0
  have key : x = ∑ v ∈ hfin.toFinset, afsplitIE v (prV (E := E) v x) +
      ((1 : E) ⊗ₜ[F] a_u c) * (levelafC E c * x) := by
    rw [← sub_eq_zero]
    apply afsplit_inj
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_add (f := _), map_sum, map_mul, map_mul, sub_eq_zero, afsplit_prV_tmul]
    unfold levelafC
    rw [afsplit_prV_tmul]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single w (fun v _ hv => afsplit_prV_IE_ne v w (Ne.symm hv) _)
        (fun h => absurd hw h), afsplit_prV_IE]
      have h0 : (a_u c) w = 0 := if_pos (by simpa using hw)
      rw [h0, TensorProduct.tmul_zero, zero_mul, add_zero]
    · rw [Finset.sum_eq_zero (fun v hv => afsplit_prV_IE_ne v w (by rintro rfl; exact hw hv) _), zero_add]
      have h0 : (a_u c) w = (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹ := if_neg (by simpa using hw)
      rw [h0, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        show (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) c) w = algebraMap (𝓞 F) (w.adicCompletion F) c from rfl,
        inv_mul_cancel₀ (levelaf_algebraMap_ne_zero w c hc0), ← Algebra.TensorProduct.one_def, one_mul]
  rw [key]
  refine add_mem (Subring.sum_mem _ fun v _ => afsplit_IE_int v _ (h v)) (mul_mem ?_ (hc x h))
  exact Subring.subset_closure (Or.inr ⟨⟨a_u c, a_u_mem c⟩, rfl⟩)

end SA

section SP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]


end SP

section SL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

end SL

section K

end K

section TAbs

variable {A : Type} [CommRing A] (O : Subring A) {n : Type} [Fintype n] [DecidableEq n] (i0 : n) (p q qi : A)
  (Lb Ld : Submodule O (n → A))

variable (hp : p ∈ O) (hq : q ∈ O) (hqi : q * qi = 1)
  (mLb : ∀ y, y ∈ Lb ↔ (∃ c ∈ O, y i0 = p * c) ∧ ∀ i, i ≠ i0 → y i ∈ O)
  (mLd : ∀ y, y ∈ Ld ↔ q * y i0 ∈ O ∧ ∀ i, i ≠ i0 → y i ∈ O)






end TAbs

section TConc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t_unit_inv {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (τ : A →+* A) (g : GL n A)
    (hg : g ∈ UJ τ (1 : Matrix n n A)) (i j : n) : ((g⁻¹ : GL n A) : Matrix n n A) i j = τ ((g : Matrix n n A) j i) := by
  have h : cT τ (g : Matrix n n A) * 1 * (g : Matrix n n A) = 1 := hg
  rw [Matrix.mul_one] at h
  have h2 : ((g⁻¹ : GL n A) : Matrix n n A) = cT τ (g : Matrix n n A) := by
    calc ((g⁻¹ : GL n A) : Matrix n n A) = (cT τ (g : Matrix n n A) * (g : Matrix n n A)) * ((g⁻¹ : GL n A) : Matrix n n A) := by
          rw [h, Matrix.one_mul]
      _ = cT τ (g : Matrix n n A) := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2]
  rfl

variable {k : ℕ} (P : Par F E k)

end TConc

section TMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end TMain

section Asm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {k : ℕ} (P : Par F E k)

variable {P} {f : ℕ}

end Asm

section Host

variable {R : Ranks} (H : Host R)

end Host

end Formalism.MainNotions.Gaps.CC.Idx

end
