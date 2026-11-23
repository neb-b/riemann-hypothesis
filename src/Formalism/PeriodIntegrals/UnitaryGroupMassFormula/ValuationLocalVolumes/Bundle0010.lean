module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FfHSelfOfSnd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0024

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DcountSplit
section
noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

theorem keySplit (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - (2 * x ^ (n + 1) - 1) - (x - 1) * (x ^ (2 * n + 1) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - x ^ (-(n : ℤ))) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  field_simp
  ring

theorem dcount_split {k : Type} [Field k] [Finite k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k)) {a' : ℕ}
    (haM : a' ≤ M) (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0} + 1 =
      2 * Nat.card k ^ (M - a') := by
  classical
  have := Fintype.ofFinite k
  have hk0 : 0 < Nat.card k := Nat.card_pos
  have e2 : Nat.card k ^ M = Nat.card k ^ (M - a') * Nat.card k ^ a' := by
    rw [← pow_add, Nat.sub_add_cancel haM]
  have h1 := card_half_snd J T0 hu Y hY
  have h2 := card_half_fst J T0 hu Y hY
  rw [e2] at h1 h2
  have c1 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h1
  have c2 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h2
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at c1 c2 ⊢
  set s1 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0)
  set s2 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0)
  have hs : Finset.univ.filter (fun x : Fin M → k × k =>
      (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0) =
      s1 ∪ s2 := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rw [notFree_iff]
    constructor
    · rintro ⟨hP, _, h | h⟩
      · exact Or.inr ⟨hP, h⟩
      · exact Or.inl ⟨hP, h⟩
    · rintro (⟨hP, h⟩ | ⟨hP, h⟩)
      · exact ⟨hP, ffH_self_of_snd J x h, Or.inr h⟩
      · exact ⟨hP, ffH_self_of_fst J x h, Or.inl h⟩
  have hi : s1 ∩ s2 = {0} := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, ⟨_, h1⟩⟩
      funext l; exact Prod.ext (h1 l) (h2 l)
    · rintro rfl
      exact ⟨⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩, ⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩⟩
  have hu2 := Finset.card_union_add_card_inter s1 s2
  rw [hi, Finset.card_singleton, c1, c2] at hu2
  rw [hs, hu2]
  ring

end PI.OmVe
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FixedMemRange
section
noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix Polynomial

theorem keyInert (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - 1 - (x - 1) * (x ^ (2 * n + 1) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - (-1) ^ n * x ^ (-(n : ℤ))) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, he.add_one.neg_one_pow]
    field_simp
    ring
  · rw [ho.neg_one_pow, ho.add_one.neg_one_pow]
    field_simp
    ring

theorem fixed_mem_range {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (h2 : Module.finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) (t : K) (ht : σ t = t) :
    ∃ c : k, t = algebraMap k K c := by
  classical
  haveI : FiniteDimensional k K := inferInstance
  haveI : IsGalois k K := inferInstance
  have hcard : Fintype.card (K ≃ₐ[k] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ τ : K ≃ₐ[k] K, τ = AlgEquiv.refl ∨ τ = σ := by
    intro τ
    by_contra h
    push_neg at h
    have h3 : ({AlgEquiv.refl, σ, τ} : Finset (K ≃ₐ[k] K)).card ≤ 2 := hcard ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hne, Ne.symm h.1]), Finset.card_pair (Ne.symm h.2)] at h3
    omega
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed t).mpr (fun τ => by
    rcases hall τ with rfl | rfl
    · rfl
    · exact ht)
  exact ⟨c, hc.symm⟩

end PI.OmVe
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FrameVectorMemBaseLattice
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem crdOf_mem {y : (VS D).V} (hy : y ∈ (VS D).L0) : crdOf X.B.I X.ιE X.bas y ∈ abelian₂ X := by
  show crdOf X.B.I X.ιE X.bas y ∈ X.B.I.L
  rw [X.L_eq]
  simp only [crdOf, RingEquiv.apply_symm_apply]
  rw [X.bas.sum_repr]
  exact hy

theorem frame_vector_mem_base_lattice : X.zu u' ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u'))

theorem yTup_z_mem (v : PlX X) : yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  have hs : scl X v (zi (D := D)) = 1 := by
    simp only [scl, zi, Fin.append_left]; exact alp_last v D.R.rS
  have h1 : yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (tupH (frameOf X u') (zi (D := D))) := by
    funext i
    change sc (E := X.B.I.E) v (scl X v (zi (D := D))) * _ = _
    rw [hs]
    simp only [sc, ← Algebra.TensorProduct.one_def, one_mul]
    rfl
  rw [h1, tupH_eq]
  refine Submodule.subset_span ⟨_, crdOf_mem X ?_, rfl⟩
  simp only [hv, zi, Fin.append_left, Fin.snoc_last]
  exact frame_vector_mem_base_lattice X u'

def OmVMemEF : Prop :=
  ∀ (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)), i ≠ zi (D := D) → yTup X u' v i ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

theorem omVMem_of (h : OmVMemEF X u') : OmVMem X u' := by
  intro v i
  by_cases hi : i = zi (D := D)
  · subst hi; exact yTup_z_mem X u' v
  · exact h v i hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.NegNatUnit
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem negNat_unit (v : PlX X) (T : ℕ) (hT : ((T : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal) :
    ∃ u ∈ OEv (E := X.B.I.E) v, inclR (Fv X.B.I.F v) (-((T : ℕ) : X.B.I.E)) * u = 1 := by
  set t : Fv X.B.I.F v := ((T : ℕ) : Fv X.B.I.F v) with ht_def
  have hv1 : Valued.v t = 1 := val_natCast_eq_one v _ hT
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1
  have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  refine ⟨(⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E),
    Submodule.smul_mem _ _ (inclR_mem_OEv X v _), ?_⟩
  have e1 : (⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) t⁻¹ *
        inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
    rw [← Algebra.smul_def]; rfl
  rw [e1, mul_left_comm, ← map_mul]
  have e2 : (-((T : ℕ) : X.B.I.E)) * (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) = ((T : ℕ) : X.B.I.E) := by
    push_cast; ring
  rw [e2, map_natCast, ← map_natCast (algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)), ← map_mul,
    inv_mul_cancel₀ ht0, map_one]

theorem zi_val : (zi (D := D)).val = D.R.rS := by simp [zi]

theorem hR_comb (v : PlX X) (c : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
    (j : Fin (D.R.rS + 1 + D.R.rS)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v j) (∑ i, c i • yTup X u' v i) =
      c (piv D.R.rS j) * inclR (Fv X.B.I.F v) (cD X u' j) := by
  rw [hR_sum_right]
  have hg : ∀ i, hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v j) (yTup X u' v i) =
      inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) := fun i =>
    congrFun (congrFun (omVGram_holds X u' v) j) i
  simp only [hR_smulE_right, hg, gramE_entry, apply_ite (inclR (Fv X.B.I.F v)), map_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem omVPrim_of (hM : OmVMem X u') (hZ : OmVZPrim X u') : OmVPrim X u' := by
  intro v
  refine ⟨hM v, fun c hc => ?_⟩
  have hne : ∀ i, i ≠ zi (D := D) → c i ∈ OEv (E := X.B.I.E) v := by
    intro i hi
    have hj : piv D.R.rS (piv D.R.rS i) = i := piv_invol D.R.rS i
    have hjz : (piv D.R.rS i).val ≠ D.R.rS := by
      intro h
      apply hi
      have : piv D.R.rS i = zi (D := D) := Fin.ext (by rw [h, zi_val])
      rw [← hj, this, pivot_castAdd_last]
    have h1 := hR_comb X u' v c (piv D.R.rS i)
    rw [hj, cD, if_neg hjz, map_one, mul_one] at h1
    rw [← h1]
    exact omVSD_fwd X v (hM v _) hc
  intro i
  by_cases hi : i = zi (D := D)
  · subst hi
    have hz : c (zi (D := D)) • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
      have e : c (zi (D := D)) • yTup X u' v (zi (D := D)) =
          (∑ i, c i • yTup X u' v i) - ∑ i ∈ Finset.univ.erase (zi (D := D)), c i • yTup X u' v i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (zi (D := D))), add_sub_cancel_right]
      rw [e]
      refine Submodule.sub_mem _ hc (Submodule.sum_mem _ fun i hi => lat_oev_smul X v ?_ (hM v i))
      exact hne i (Finset.ne_of_mem_erase hi)
    by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
    · exact hZ v hT _ hz
    · obtain ⟨u, hu, hu1⟩ := negNat_unit X v (Tw u') hT
      have h1 := hR_comb X u' v c (zi (D := D))
      rw [pivot_castAdd_last, cD, if_pos zi_val] at h1
      have h2 : c (zi (D := D)) * inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E)) ∈ OEv (E := X.B.I.E) v := by
        rw [← h1]; exact omVSD_fwd X v (hM v _) hc
      have h3 : c (zi (D := D)) = (c (zi (D := D)) * inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E))) * u := by
        rw [mul_assoc, hu1, mul_one]
      rw [h3]
      exact oev_mul v h2 hu
  · exact hne i hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfStepsX
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVdEx_holds : OmVdEx X ψ := fun v hS =>
  ⟨(PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).1,
    (PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).2.1⟩

theorem omVdUniq_holds : OmVdUniq X ψ := fun v => omUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem omVdSdW_holds : OmVdSdW X ψ := fun v =>
  SdB.sdVolW_of_perf X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVdSdH_holds : OmVdSdH X ψ := fun v =>
  SdB.sdVolH_of_perf X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVBadT_of_steps (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hM : ∀ v : PlX X, MeasP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hI : ∀ v : PlX X, IdxP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of X u' ψ hStd hLat hGram (omVdEx_holds X ψ) (omVdUniq_holds X ψ)
    (fun v hv => orbP_of _ _ _ _ _ _ _ (hExt v hv))
    (fun v => fibP_of_dual _ _ _ _ _ _ _ (hPC v) (hPD v))
    (fun v hv => countP_of _ _ _ _ _ _ _ (hM v) (hI v) (hCl v hv) (hPC v))
    (omVdSdW_holds X ψ) (omVdSdH_holds X ψ)

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHoldsX
section
namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem omVScale_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVScale X u' ψ :=
  omVScale_holds X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OneMemOev
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem incl_mem (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

theorem one_mem_oev : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := incl_mem (F := F) (E := E) v 1
  simpa using h

theorem denseF (c ε : Fv F v) (hε : ε ≠ 0) :
    ∃ b : F, ∃ o ∈ v.adicCompletionIntegers F, algebraMap F (Fv F v) b - c = ε * o := by
  have hO : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) := Valued.isOpen_integer _
  have hU : IsOpen {k : Fv F v | (k - c) * ε⁻¹ ∈ v.adicCompletionIntegers F} :=
    hO.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (v := v) (K := F)).exists_mem_open hU
    ⟨c, by simp [zero_mem]⟩
  refine ⟨b, _, hb, ?_⟩
  field_simp

theorem tmul_eq (c : Fv F v) (x : E) :
    c ⊗ₜ[F] x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c * inclR (F := F) (Fv F v) x := by
  simp [inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem alg_alg (b : F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) b) = inclR (F := F) (Fv F v) (algebraMap F E b) := by
  rw [← IsScalarTower.algebraMap_apply]
  simp [inclR]

theorem approx (M : ℤ) (hM : M ≠ 0) (t : Fv F v ⊗[F] E) :
    ∃ e : E, ∃ w ∈ OEv (E := E) v, t - inclR (F := F) (Fv F v) e = (M : Fv F v ⊗[F] E) * w := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | tmul c x =>
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
    have hi : IsIntegral ℤ (m • x) := hint x (Finset.mem_singleton_self x)
    set o : 𝓞 E := ⟨m • x, hi⟩ with ho
    set mF : Fv F v := algebraMap F (Fv F v) (m : F) with hmF
    have hmF0 : mF ≠ 0 := (map_ne_zero _).2 (Int.cast_ne_zero.2 hm)
    have hMF0 : algebraMap F (Fv F v) (M : F) ≠ 0 := (map_ne_zero _).2 (Int.cast_ne_zero.2 hM)
    obtain ⟨b, u, hu, hb⟩ := denseF v (c / mF) (algebraMap F (Fv F v) (M : F)) hMF0
    refine ⟨algebraMap F E b * (m • x), (⟨-u, neg_mem hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E),
      Submodule.smul_mem _ _ (incl_mem v o), ?_⟩
    have hb' : mF * algebraMap F (Fv F v) b - c = mF * (algebraMap F (Fv F v) (M : F) * u) := by
      rw [← hb]; field_simp
    have hb'' := congrArg (algebraMap (Fv F v) (Fv F v ⊗[F] E)) hb'
    simp only [map_sub, map_mul, hmF, alg_alg, map_intCast] at hb''
    have ho' : inclR (F := F) (Fv F v) (o : E) = (m : Fv F v ⊗[F] E) * inclR (F := F) (Fv F v) x := by
      rw [ho]; show inclR (F := F) (Fv F v) (m • x) = _; rw [zsmul_eq_mul, map_mul, map_intCast]
    have hs : (⟨-u, neg_mem hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) =
        -(algebraMap (Fv F v) (Fv F v ⊗[F] E) u * inclR (F := F) (Fv F v) (o : E)) := by
      rw [← neg_mul, ← map_neg, ← Algebra.smul_def]; rfl
    rw [hs, ho', tmul_eq, zsmul_eq_mul, map_mul, map_mul, map_intCast]
    linear_combination (-(inclR (F := F) (Fv F v) x)) * hb''
  | add t t' h1 h2 =>
    obtain ⟨e1, w1, hw1, he1⟩ := h1
    obtain ⟨e2, w2, hw2, he2⟩ := h2
    refine ⟨e1 + e2, w1 + w2, Submodule.add_mem _ hw1 hw2, ?_⟩
    rw [map_add (f := _)]; linear_combination he1 + he2

def trV : Fv F v ⊗[F] E →ₗ[Fv F v] Fv F v :=
  (Algebra.TensorProduct.rid F (Fv F v) (Fv F v)).toLinearMap ∘ₗ LinearMap.baseChange (Fv F v) (Algebra.trace F E)

theorem trV_tmul (c : Fv F v) (x : E) : trV v (c ⊗ₜ[F] x) = Algebra.trace F E x • c := rfl

theorem trV_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : trV v x ∈ v.adicCompletionIntegers F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, _, rfl⟩ := hx
    change trV v ((1 : Fv F v) ⊗ₜ[F] (o : E)) ∈ _
    rw [trV_tmul, Algebra.smul_def, mul_one]
    have hI : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    set r : 𝓞 F := ⟨_, (mem_integralClosure_iff ℤ F).2 hI⟩ with hr
    have h1 : Algebra.trace F E (o : E) = (r : F) := rfl
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (r : F)
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers,
      show algebraMap F (Fv F v) (r : F) = ((r : F) : Fv F v) from rfl, this, HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one r
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c x _ h =>
    change trV v ((c : Fv F v) • x) ∈ _
    rw [map_smul, smul_eq_mul]; exact mul_mem c.2 h

theorem trV_alg (c : Fv F v) :
    trV v (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap F (Fv F v) (Module.finrank F E : F) * c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trV_tmul,
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, Algebra.smul_def]

theorem pow_unbdd {a b : WithZero (Multiplicative ℤ)} (ha : 1 < a) (hb : b ≠ 0) :
    ∃ k : ℕ, 1 < b * a ^ k := by
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.1 hb
  have ha0 : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.1 ha0
  have hα : 0 < Multiplicative.toAdd α := by
    have h := WithZero.coe_lt_coe.1 (show ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < α from ha)
    exact Multiplicative.ofAdd_lt.1 h
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_lt_coe,
    ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_pow, toAdd_one]
  rw [nsmul_eq_mul]; push_cast
  have h3 : (|Multiplicative.toAdd β| + 1) * 1 ≤ (|Multiplicative.toAdd β| + 1) * Multiplicative.toAdd α :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  linarith [neg_abs_le (Multiplicative.toAdd β)]

theorem int_of_alg (c : Fv F v) (hc : algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v) :
    c ∈ v.adicCompletionIntegers F := by
  by_contra hn
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hn
  have hpow : ∀ k : ℕ, algebraMap (Fv F v) (Fv F v ⊗[F] E) (c ^ k) ∈ OEv (E := E) v := by
    intro k
    induction k with
    | zero => rw [pow_zero, map_one]; exact one_mem_oev v
    | succ k ih => rw [pow_succ, map_mul]; exact oev_mul v ih hc
  have hd0 : algebraMap F (Fv F v) (Module.finrank F E : F) ≠ 0 :=
    (map_ne_zero _).2 (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  obtain ⟨k, hk⟩ := pow_unbdd hn ((Valuation.ne_zero_iff _).2 hd0)
  have := trV_mem v (hpow k)
  rw [trV_alg, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow] at this
  exact absurd this (not_le.2 hk)

end Gen

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

