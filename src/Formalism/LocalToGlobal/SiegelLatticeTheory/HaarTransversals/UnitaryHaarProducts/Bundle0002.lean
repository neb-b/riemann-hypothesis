module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDiff
section
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

theorem splitDiff_holds : SplitDiff := by
  intro F E _ _ _ _ _ p P hp hPm hpP hpP2 h
  haveI : P.IsPrime := hPm.isPrime
  have hDE : differentIdeal ℤ (𝓞 E) ≤ P := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)]
    exact le_trans Ideal.mul_le_right h
  have hdvd : P ∣ differentIdeal ℤ (𝓞 E) := Ideal.dvd_iff_le.mpr hDE
  rw [dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain] at hdvd
  apply hdvd
  have hpu : ((p : ℤ)) ∈ P.under ℤ := by
    show (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
    rw [Ideal.mem_comap]
    simpa using hpP
  have hne : P.under ℤ ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpu
    exact hp.ne_zero (by exact_mod_cast hpu)
  haveI : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' (P.under ℤ) P hne]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]
    exact Ideal.map_comap_le
  · intro hle
    have h2 := hle (Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 E)) hpu)
    apply hpP2
    simpa using h2

end Formalism.L2.SG.Pf.LatEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLatPf
section
open NumberField NumberField.InfinitePlace

namespace Formalism.L2.SG.Pf

theorem oeApprox_holds : Formalism.L2.SG.Pf.UnipLat.OEApprox := by
  intro F E _ _ _ _ _ _ hE _ φ hφ
  classical

  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis E))
  refine ⟨R, fun t => ?_⟩

  let w : InfinitePlace F → InfinitePlace E := fun v => InfinitePlace.mk (φ v)
  have hw : ∀ v, (w v).comap (algebraMap F E) = v := by
    intro v
    have hcomp : (φ v).comp (algebraMap F E) = v.embedding := RingHom.ext (hφ v)
    simp only [w, InfinitePlace.comap_mk, hcomp, InfinitePlace.mk_embedding]
  have hinj : ∀ v v', w v = w v' → v = v' := by
    intro v v' h
    rw [← hw v, ← hw v', h]
  let c : InfinitePlace F → ℂ := fun v =>
    if (w v).embedding = φ v then t v else (starRingEnd ℂ) (t v)
  let x : mixedEmbedding.mixedSpace E :=
    (0, fun u => if h : ∃ v, u.1 = w v then c h.choose else 0)
  have hmem : x - ZSpan.fract (mixedEmbedding.latticeBasis E) x ∈
      mixedEmbedding.integerLattice E := by
    rw [← mixedEmbedding.mem_span_latticeBasis, ZSpan.fract_apply, sub_sub_cancel]
    exact (ZSpan.floor _ x).2
  obtain ⟨m, hm⟩ := hmem
  have hm' : mixedEmbedding E (m : E) = x - ZSpan.fract (mixedEmbedding.latticeBasis E) x := hm
  refine ⟨m, fun v => ?_⟩
  have hc : (w v).IsComplex := hE.isComplex (w v)
  let u : {u : InfinitePlace E // u.IsComplex} := ⟨w v, hc⟩
  have hxu : x.2 u = c v := by
    have hex : ∃ v', u.1 = w v' := ⟨v, rfl⟩
    show (if h : ∃ v', u.1 = w v' then c h.choose else 0) = c v
    rw [dite_eq_left hex, hinj _ _ hex.choose_spec.symm]
  have hfr : x - mixedEmbedding E (m : E) = ZSpan.fract (mixedEmbedding.latticeBasis E) x := by
    rw [hm', sub_sub_cancel]
  have hval : (ZSpan.fract (mixedEmbedding.latticeBasis E) x).2 u
      = c v - (w v).embedding (m : E) := by
    rw [← hfr, Prod.snd_sub, Pi.sub_apply, hxu, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hb : ‖c v - (w v).embedding (m : E)‖ ≤ R := by
    rw [← hval]
    exact ((norm_le_pi_norm _ u).trans (norm_snd_le _)).trans
      (hR _ (ZSpan.fract_mem_fundamentalDomain _ x))
  by_cases h : (w v).embedding = φ v
  · have hcv : c v = t v := if_pos h
    rw [hcv, h] at hb
    exact hb
  · have h2 : (w v).embedding = ComplexEmbedding.conjugate (φ v) :=
      (InfinitePlace.embedding_mk_eq (φ v)).resolve_left h
    have hcv : c v = (starRingEnd ℂ) (t v) := if_neg h
    rw [hcv, h2, ComplexEmbedding.conjugate_coe_eq, ← map_sub, Complex.norm_conj] at hb
    exact hb

end Formalism.L2.SG.Pf
end

