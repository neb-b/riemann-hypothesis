module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUFinal

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfIsoX
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem a_succ_le_n : D.R.rS + 1 + D.R.rS + 1 ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  have h3 := D.R.m_add_three_le_k
  have h4 := D.R.r_eq
  omega

theorem omVBadT_of_iso (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoExt X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_red X u' ψ hStd hLat hGram
    (fun v hv => extP_of _ _ _ _ _ _ _ (a_succ_le_n X) (hIso v hv)) hLI hRed hFI hFS

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfTrX
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

theorem host_el (x0 : 𝓞 X.B.I.F) : ∃ d0 : 𝓞 D.host.F, ((d0 : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := by
  have hmem : X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ∈ D.host.F := (X.ιE_F _).2 ⟨x0, rfl⟩
  set y : D.host.F := ⟨_, hmem⟩
  have hi : IsIntegral ℤ (X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F))) :=
    ((RingOfIntegers.isIntegral_coe x0).map (algebraMap X.B.I.F X.B.I.E).toIntAlgHom).map (X.ιE : X.B.I.E →+* D.host.E).toIntAlgHom
  have hy : IsIntegral ℤ y :=
    (isIntegral_algHom_iff ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom Subtype.val_injective).1 hi
  exact ⟨⟨y, (mem_integralClosure_iff ℤ _).2 hy⟩, rfl⟩

theorem dd2 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ (ddS D ^ k)⁻¹) :
    sc (E := X.B.I.E) v ((dV v) ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨x0, hx0, hv0⟩ := (dV_isDiffVal v).2.2
  obtain ⟨d0, hd0e⟩ := host_el X x0
  have hd0 : d0 ∈ differentIdeal ℤ (𝓞 D.host.F) := (hT d0).2 ⟨x0, hx0, hd0e.symm⟩
  set g : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d0 with hg_def
  have hgE : (g : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := hd0e
  set c : Fv X.B.I.F v := algebraMap X.B.I.F (Fv X.B.I.F v) (x0 : X.B.I.F) with hc_def
  have hvd0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv0; exact hvd0 hv0.symm
  have hg0 : (g : D.host.E) ≠ 0 := by
    rw [hgE]; intro h
    apply hc0
    have : algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F) = 0 := by
      rw [← map_zero X.ιE] at h; exact X.ιE.injective h
    rw [hc_def, (algebraMap X.B.I.F X.B.I.E).injective (this.trans (map_zero _).symm), map_zero]
  have hgk : (g : D.host.E) ^ k ∈ ddS D ^ k := by
    rw [ddS_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (d0 ^ k),
      Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hd0 k), by rw [map_pow, map_pow]⟩
  have hne : ddS D ^ k ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hgk
    exact hg0 (by by_contra hne0; exact (pow_ne_zero k hne0) hgk)
  have hprod : x * (g : D.host.E) ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hx hgk
    rwa [inv_mul_cancel₀ hne] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
  have key : X.ιE.symm x * (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ^ k = X.ιE.symm (o : D.host.E) := by
    have h1 : ((o : D.host.E)) = x * (g : D.host.E) ^ k := ho
    rw [h1, map_mul, map_pow, hgE, RingEquiv.symm_apply_apply]
  have key2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) *
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (c ^ k) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key, map_mul, map_pow, map_pow, hc_def, alg_alg]
  have hu : Valued.v (dV v * c⁻¹) = 1 := by rw [map_mul, map_inv₀, ← hv0, mul_inv_cancel₀ (hv0 ▸ hvd0)]
  have hid : (dV v * c⁻¹) ^ k * c ^ k = dV v ^ k := by
    rw [mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hc0), mul_one]
  have e : sc (E := X.B.I.E) v (dV v ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((dV v * c⁻¹) ^ k) *
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key2]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (dV v ^ k) * _ = _
    rw [← hid, map_mul]; ring
  rw [e]
  refine oev_mul v (alg_int_mem X v _ ?_) (incl_mem v (⟨X.ιE.symm (o : D.host.E),
    (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E))
  rw [map_pow, hu, one_pow]

theorem omVDdLoc_of (hT : OmVDdTr X) : OmVDdLoc X := by
  intro v a
  have hlt : ((a.castSucc : Fin (D.R.rS + 1)) : ℕ) < D.R.rS := by simp
  have halp : alp v D.R.rS a.castSucc = (dV v)⁻¹ ^ (D.R.rS - (a : ℕ)) := by
    unfold alp; rw [if_pos hlt]; simp
  have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
    rw [Nat.cast_sub a.isLt.le]
  have haa : aaD D a = (ddS D ^ (D.R.rS - (a : ℕ)))⁻¹ := by
    unfold aaD; rw [hk, zpow_neg, zpow_natCast]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [haa, inv_inv] at hx; rw [halp]; exact dd1 X hT v _ x hx
  · rw [haa] at hx; rw [halp, inv_pow, inv_inv]; exact dd2 X hT v _ x hx

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHermBoxHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volUHermBox_holds {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) : VolUHermBox X ψ := by
  intro hψ hs v hv
  obtain ⟨hg, -, hd⟩ := VolUT.typ_arith X v hv
  have hann := VolUTr.annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v
  have hfin := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := VolUL.sd_facts ψ v hψ hfin hann hd (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  haveI := hH
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨P, hPmax, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
      exact bot_le)
  obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
  set σ := X.B.I.cm.sig with hσ
  have hσx : ∀ x, σ x = star x := fun x => rfl
  have hinv : ∀ y, σ (σ y) = y := fun y => by rw [hσx, hσx, star_star]
  have ht : σ (θ : X.B.I.E) = (t : X.B.I.E) := by rw [hσx]; exact htθ.symm
  have hne : (θ : X.B.I.E) ≠ t := by
    intro h
    apply hnot
    have : θ - t = 0 := by ext; simp [h]
    rw [this]; exact P.zero_mem
  have hnt : ∃ x, σ x ≠ x := ⟨θ, by rw [ht]; exact fun h => hne h.symm⟩
  have hfix : star (((θ : X.B.I.E) - t) ^ 2) = ((θ : X.B.I.E) - t) ^ 2 := by
    have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
    have h1 : star (t : X.B.I.E) = θ := by rw [htθ', star_star]
    rw [star_pow, star_sub, h1, ← htθ']
    ring
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed _).1 hfix
  have hint : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E f) := by
    rw [hf]
    have h1 : (((θ - t) ^ 2 : 𝓞 X.B.I.E) : X.B.I.E) = ((θ : X.B.I.E) - t) ^ 2 := by push_cast; ring
    rw [← h1]
    exact RingOfIntegers.isIntegral_coe _
  have hfint : IsIntegral ℤ f :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)
      (algebraMap X.B.I.F X.B.I.E).injective).mp hint
  set e : 𝓞 X.B.I.F := ⟨f, hfint⟩ with he
  have he2 : ((θ : X.B.I.E) - t) ^ 2 = algebraMap X.B.I.F X.B.I.E (e : X.B.I.F) := hf.symm
  have hev : e ∉ v.asIdeal := by
    intro hm
    rw [← hPv] at hm
    have hm' : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e ∈ P := hm
    have heq : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) e = (θ - t) ^ 2 := by
      apply RingOfIntegers.coe_injective
      rw [← IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) (𝓞 X.B.I.E) X.B.I.E,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, map_pow, map_sub]
      exact he2.symm
    rw [heq] at hm'
    exact hnot (hPmax.isPrime.mem_of_pow_mem 2 hm')
  obtain ⟨θ0, Δ, hθO, hθ, hΔ, hΔ0⟩ := VolV.theta_exists σ v hinv hnt hfin θ t ht e he2 hev
  have htr := VolUTr.TrW.trace_v v σ hinv hnt hfin
  intro c hc
  exact VolV.hermBox_meas σ v _ hfin htr (gAt_prime X v).ne_zero hg hθO hθ hΔ hΔ0 _ hO c hc

end Formalism.L2.SG.Pf.NcVal
end
end

