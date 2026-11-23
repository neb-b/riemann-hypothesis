module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0017

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoExtOf
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem one_mem_O : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := (PI.OmLocU.Orb.oSub (E := E) v).1

theorem prod_int {m : ℕ} (f : Fin m → Fv F v ⊗[F] E) (hf : ∀ i, f i ∈ OEv (E := E) v) :
    ∏ i, f i ∈ OEv (E := E) v :=
  Finset.prod_induction _ (· ∈ OEv (E := E) v) (fun _ _ => oEv_mul v) (one_mem_O v) (fun i _ => hf i)

theorem det_int {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v) :
    A.det ∈ OEv (E := E) v := by
  rw [Matrix.det_apply]
  refine oEv_sum v _ _ fun p _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> rw [h]
  · rw [one_smul]; exact prod_int v _ fun i => hA _ _
  · rw [Units.neg_smul, one_smul]; exact oEv_neg v (prod_int v _ fun i => hA _ _)

theorem adj_int {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v) :
    ∀ i j, A.adjugate i j ∈ OEv (E := E) v := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det_int v _ fun k l => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs
    · exact one_mem_O v
    · exact oEv_zero v
  · exact hA k l

theorem uniPrim {a : ℕ} (hSD : IsSDLoc σ J v Λ) (X : TupV (E := E) v n a)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ)
    (hu : ∃ u ∈ OEv (E := E) v, (gramR (Fv F v) σ J X).det ∈ OEv (E := E) v ∧ (gramR (Fv F v) σ J X).det * u = 1) :
    IsPrim v Λ X := by
  refine ⟨hX, fun c hc i => ?_⟩
  have hGi : ∀ i j, gramR (Fv F v) σ J X i j ∈ OEv (E := E) v := fun i j => hR_mem_oEv σ J v Λ hSD (hX i) (hX j)
  have hGc : ∀ j, Matrix.mulVec (gramR (Fv F v) σ J X) c j ∈ OEv (E := E) v := by
    intro j
    have := hR_mem_oEv σ J v Λ hSD (hX j) hc
    rw [hR_sum_smul_right] at this
    have e : Matrix.mulVec (gramR (Fv F v) σ J X) c j = ∑ i, c i * hR (Fv F v) σ J (X j) (X i) := by
      simp only [Matrix.mulVec, dotProduct, gramR]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]; exact this
  obtain ⟨u, huO, -, hdu⟩ := hu
  have key : c i = u * Matrix.mulVec (gramR (Fv F v) σ J X).adjugate
      (Matrix.mulVec (gramR (Fv F v) σ J X) c) i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, ← mul_assoc, mul_comm u, hdu, one_mul]
  rw [key]
  refine oEv_mul v huO ?_
  simp only [Matrix.mulVec, dotProduct]
  exact oEv_sum v _ _ fun j _ => oEv_mul v (adj_int v _ hGi i j) (hGc j)

def IsoW (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ T : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E),
    (∃ u ∈ OEv (E := E) v, T.det ∈ OEv (E := E) v ∧ T.det * u = 1) ∧
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
      ∃ w ∈ latLoc (E := E) v Λ, gramR (Fv F v) σ J (augT v X w) = T

theorem isoExt_of (a : ℕ) (Y : TupV (E := E) v n a) (hW : IsoW σ J ψ v Λ a Y) : IsoExt σ J ψ v Λ a Y := by
  intro hG
  obtain ⟨T, hTu, h⟩ := hW hG
  refine ⟨T, hTu, fun X hX hXY => ?_⟩
  obtain ⟨w, hw, hg⟩ := h X hX hXY
  refine ⟨w, uniPrim σ J v Λ hG.2.2.1 _ (fun i => ?_) (by rw [hg]; exact hTu), hg⟩
  induction i using Fin.lastCases with
  | last => simp [augT]; exact hw
  | cast j => rw [augT_castSucc]; exact hX.1 j

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVMemEFHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

theorem mem_diff_iff {K : Type} [Field K] [NumberField K] (x : 𝓞 K) :
    x ∈ differentIdeal ℤ (𝓞 K) ↔ ∀ y : K, (∀ a : 𝓞 K, Algebra.trace ℚ K (y * a) ∈ (algebraMap ℤ ℚ).range) →
      IsIntegral ℤ ((x : K) * y) := by
  have h1 : x ∈ differentIdeal ℤ (𝓞 K) ↔ (x : K) ∈ IsLocalization.coeSubmodule K (differentIdeal ℤ (𝓞 K)) := by
    rw [IsLocalization.mem_coeSubmodule]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨x', hx', he⟩
      have : x' = x := Subtype.ext he
      rwa [← this]
  rw [h1, coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h y hy
    have h2 := h y (by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
      simpa [Algebra.traceForm_apply] using hy a')
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h2
    rw [← hb]
    exact RingOfIntegers.isIntegral_coe b
  · intro h y hy
    rw [Submodule.mem_traceDual] at hy
    have hint := h y (fun a => by simpa [Algebra.traceForm_apply] using hy _ (Submodule.mem_one.2 ⟨a, rfl⟩))
    exact Submodule.mem_one.2 ⟨⟨_, (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩

theorem diff_map {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K ≃+* K')
    (x : 𝓞 K) (x' : 𝓞 K') (hxx : e (x : K) = (x' : K')) (hx : x ∈ differentIdeal ℤ (𝓞 K)) :
    x' ∈ differentIdeal ℤ (𝓞 K') := by
  rw [mem_diff_iff] at hx ⊢
  intro y' hy'
  have htr : ∀ z : K, Algebra.trace ℚ K' (e z) = Algebra.trace ℚ K z := fun z =>
    Algebra.trace_eq_of_algEquiv e.toRatAlgEquiv z
  have hy : ∀ a : 𝓞 K, Algebra.trace ℚ K (e.symm y' * a) ∈ (algebraMap ℤ ℚ).range := by
    intro a
    have hi : IsIntegral ℤ (e (a : K)) := (RingOfIntegers.isIntegral_coe a).map (e : K →+* K').toIntAlgHom
    have h3 := hy' ⟨e a, (mem_integralClosure_iff ℤ K').2 hi⟩
    rw [← htr, map_mul, RingEquiv.apply_symm_apply]
    exact h3
  have h4 := (hx _ hy).map (e : K →+* K').toIntAlgHom
  change IsIntegral ℤ (e ((x : K) * e.symm y')) at h4
  rwa [map_mul, RingEquiv.apply_symm_apply, hxx] at h4

variable {D : D7} (X : HidaSetting D)

def eF : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    (((X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F
      (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => iota_alg_inj X (congrArg Subtype.val h), fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F (y : D.host.E)).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem eF_val (a : X.B.I.F) : ((eF X a : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E a) := rfl

theorem omVDdTr_holds : OmVDdTr X := by
  intro d
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := pre_int X d
    refine ⟨x, diff_map (eF X).symm d x ?_ hd, hx⟩
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [eF_val]; exact hx.symm)
  · rintro ⟨x, hx, hxd⟩
    exact diff_map (eF X) x d (Subtype.ext (by rw [eF_val]; exact hxd)) hx

theorem omVDdLoc_holds : OmVDdLoc X := omVDdLoc_of X (omVDdTr_holds X)

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVPrim_holds : OmVPrim X u' := omVPrim_of_dd X u' (omVDdLoc_holds X)

theorem omVPrim_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVPrim X u' := omVPrim_holds X u'

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolVFinal
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volTypV_holds {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) :
    VolTypV X u u' ψ :=
  volTypV_of_box X u u' ψ (volUHermBox_holds X ψ)

end Formalism.L2.SG.Pf.NcVal
end
end

