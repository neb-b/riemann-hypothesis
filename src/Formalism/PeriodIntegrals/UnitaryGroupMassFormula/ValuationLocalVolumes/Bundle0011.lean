module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolULeaf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTr

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimCosOf
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem near_int {a : ℕ} (ϖ : Fv F v) (hϖ : IsUnif v ϖ) (A : Fin a → Fin a → Fv F v ⊗[F] E)
    (hA : ∀ i j, A i j ∈ OEv (E := E) v) (d : Fin a → Fv F v ⊗[F] E)
    (hu : ∀ i, d i + sc (E := E) v ϖ * ∑ j, A i j * d j ∈ OEv (E := E) v) : ∀ i, d i ∈ OEv (E := E) v := by
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  have hev : ∀ i, ∀ᶠ k in atTop, ϖ ^ k • d i ∈ OEv (E := E) v := by
    intro i
    have ht : Tendsto (fun k : ℕ => ϖ ^ k • d i) atTop (𝓝 0) := by
      have := hπ.smul_const (d i)
      simpa using this
    exact ht ((isOpen_oEv (E := E) v).mem_nhds (oEv_zero v))
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 hev).exists
  have key : ∀ m : ℕ, (∀ i, sc (E := E) v (ϖ ^ m) * d i ∈ OEv (E := E) v) → ∀ i, d i ∈ OEv (E := E) v := by
    intro m
    induction m with
    | zero =>
      intro h i
      simpa [sc_one] using h i
    | succ m ih =>
      intro h
      apply ih
      intro i
      have hS : ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) =
          sc (E := E) v (ϖ ^ m) * sc (E := E) v ϖ * ∑ j, A i j * d j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ, ← sc_mul]
        ring
      have e : sc (E := E) v (ϖ ^ m) * d i = sc (E := E) v (ϖ ^ m) * (d i + sc (E := E) v ϖ * ∑ j, A i j * d j) -
          ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) := by
        rw [hS]
        ring
      rw [e, sub_eq_add_neg]
      exact oEv_add v (sc_mul_mem_oEv v (pow_mem hint m) (hu i))
        (oEv_neg v (oEv_sum v _ _ fun j _ => oEv_mul v (hA i j) (h j)))
  exact key N fun i => by rw [← smul_eq_sc]; exact hN i

theorem primCos_of (a : ℕ) (hD : PrimDual σ J ψ v Λ a) : PrimCos σ J ψ v Λ a := by
  intro hS hL hSD hUn ϖ hϖ X hX Z hZ
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨P, hP, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hZ
  obtain ⟨W, hW, hd⟩ := hD hS hSD hUn hL X hX
  have hPs : ϖ ^ (0 + 1) • P ∈ lamS v Λ a := lamS_smul v Λ (pow_mem hint _) hP
  refine ⟨fun i => (latLoc (E := E) v Λ).add_mem (hX.1 i) (hPs i), fun c hc => ?_⟩
  have hsm : ∀ j i, hR (Fv F v) σ J (W j) ((ϖ ^ (0 + 1) • P) i) = sc (E := E) v ϖ * hR (Fv F v) σ J (W j) (P i) := by
    intro j i
    have := hR_smul_smul σ J v 1 (ϖ ^ (0 + 1)) (W j) (P i)
    rw [one_smul, one_mul, zero_add, pow_one] at this
    rw [zero_add, pow_one]
    exact this
  have hpair : ∀ j, hR (Fv F v) σ J (W j) (∑ i, c i • (X + ϖ ^ (0 + 1) • P) i) =
      c j + sc (E := E) v ϖ * ∑ i, hR (Fv F v) σ J (W j) (P i) * c i := by
    intro j
    rw [hR_sum_smul_right]
    have h1 : ∀ i, c i * hR (Fv F v) σ J (W j) ((X + ϖ ^ (0 + 1) • P) i) =
        c i * (if i = j then 1 else 0) + sc (E := E) v ϖ * (hR (Fv F v) σ J (W j) (P i) * c i) := by
      intro i
      rw [Pi.add_apply, hR_add_right, (hd i j).2, hsm j i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_ite]
  exact near_int v ϖ hϖ (fun j i => hR (Fv F v) σ J (W j) (P i))
    (fun j i => hR_mem_oEv σ J v Λ hSD (hW j) (hP i)) c
    (fun j => by rw [← hpair j]; exact hR_mem_oEv σ J v Λ hSD (hW j) hc)

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimIff
section
noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))
  (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
  (he1 : gramR (Fv F v) σ J e = 1)


include he1 in
theorem prim_iff (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {a : ℕ} (x : lamA v Λ a) :
    IsPrim v Λ (x : TupV (E := E) v n a) ↔ LinearIndependent K (phi σ J v Λ hSD he π a x) := by
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  have hcomb : ∀ d : Fin a → OR (E := E) v,
      (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) ∈ latLoc (E := E) v Λ := fun d =>
    Submodule.sum_mem _ fun i _ => Orb.oSmul v Λ hL _ (d i).2 _ (memA v Λ x i)
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hP κ hκ i
    choose d hd using fun j => hπ.1 (κ j)
    have hw := hcomb d
    have hz : ∀ p, π ⟨hR (Fv F v) σ J (e p) (∑ j, (d j : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) j),
        (hSD _).1 hw _ (bas_mem v Λ he p)⟩ = 0 := by
      intro p
      refine (coord_comb σ J v Λ hSD he π x d p _).trans ?_
      have := congrFun hκ p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simpa [hd] using this
    obtain ⟨w', hw', hww⟩ := ker_vec σ J v Λ hSD he he1 hπ hw hz
    have hc := hP.2 (fun j => sc (E := E) v ϖ⁻¹ * d j) (by
      have e2 : (∑ j, (sc (E := E) v ϖ⁻¹ * d j) • (x : TupV (E := E) v n a) j) =
          sc (E := E) v ϖ⁻¹ • ∑ j, (d j : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
      rw [e2, hww, smul_smul, sc_mul, inv_mul_cancel₀ h0, sc_one, one_smul]
      exact hw') i
    rw [← hd i]
    apply (hπ.2.1 _).2
    refine ⟨_, hc, ?_⟩
    rw [← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]
  · intro hLI
    refine ⟨fun i => memA v Λ x i, fun c hc => ?_⟩
    have key : ∀ m : ℕ, ∀ c : Fin a → Fv F v ⊗[F] E,
        (∑ i, c i • (x : TupV (E := E) v n a) i) ∈ latLoc (E := E) v Λ →
        (∀ i, sc (E := E) v (ϖ ^ m) * c i ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v := by
      intro m
      induction m with
      | zero => intro c _ hm i; simpa [sc_one] using hm i
      | succ m ih =>
        intro c hc hm
        apply ih c hc
        set u := ∑ i, c i • (x : TupV (E := E) v n a) i with hu
        have hpm : sc (E := E) v (ϖ ^ m) ∈ OEv (E := E) v := by
          simpa using sc_mul_mem_oEv v (pow_mem hint m) (Orb.oSub (E := E) v).1
        have hu' : sc (E := E) v (ϖ ^ m) • u ∈ latLoc (E := E) v Λ := Orb.oSmul v Λ hL _ hpm _ hc
        let d : Fin a → OR (E := E) v := fun i => ⟨_, hm i⟩
        have hwe : (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) =
            sc (E := E) v ϖ • (sc (E := E) v (ϖ ^ m) • u) := by
          rw [smul_smul, sc_mul, ← pow_succ', hu, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
        have hw := hcomb d
        have hz : ∀ p, ∑ i, π (d i) * phi σ J v Λ hSD he π a x i p = 0 := by
          intro p
          rw [← coord_comb σ J v Λ hSD he π x d p ((hSD _).1 hw _ (bas_mem v Λ he p))]
          apply (hπ.2.1 _).2
          refine ⟨hR (Fv F v) σ J (e p) (sc (E := E) v (ϖ ^ m) • u),
            (hSD _).1 hu' _ (bas_mem v Λ he p), ?_⟩
          show hR (Fv F v) σ J (e p) (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) = _
          rw [hwe, Orb.hR_smul_right]
        have hd0 := hLI (fun i => π (d i)) (by
          funext p
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact hz p)
        intro i
        obtain ⟨g, hg, hge⟩ := (hπ.2.1 (d i)).1 (hd0 i)
        have : sc (E := E) v (ϖ ^ m) * c i = g := by
          have h1 : sc (E := E) v ϖ * (sc (E := E) v (ϖ ^ m) * c i) = sc (E := E) v ϖ * g := by
            rw [← mul_assoc, sc_mul, ← pow_succ']
            exact hge
          have h2 := congrArg (fun y => sc (E := E) v ϖ⁻¹ * y) h1
          simp only [← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul] at h2
          exact h2
        rw [this]
        exact hg
    obtain ⟨m, hm⟩ := exists_pow_mem v hϖ c
    exact key m c hc hm

end PI.OmVg
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTyp
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VolUT

section V

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (algebraMap F (Fv F v) (x : F)) ≤ 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F x)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h
  have h' : Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := h
  rw [h']
  exact v.intValuation_le_one x

theorem val_unit (x : 𝓞 F) (hx : x ∉ v.asIdeal) : Valued.v (algebraMap F (Fv F v) (x : F)) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F x)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hx] at h
  exact h

theorem val_dV (h : ¬ (differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)) : Valued.v (dV v) = 1 := by
  obtain ⟨y, hy, hyv⟩ := Set.not_subset.1 h
  unfold dV
  split_ifs with hd
  · obtain ⟨-, hle, x, hx, hxe⟩ := hd.choose_spec
    have h1 := hle y hy
    rw [val_unit v y hyv] at h1
    rw [← hxe] at h1 ⊢
    exact le_antisymm (val_int v x) h1
  · exact map_one _

theorem absV_of_val_one {x : Fv F v} (h : Valued.v x = 1) : absV v x = 1 := by
  unfold absV
  rw [dite_eq_right (by rw [h]; exact one_ne_zero)]
  have : WithZero.unzero (show Valued.v x ≠ 0 by rw [h]; exact one_ne_zero) = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [this]
  simp

theorem absV_g (g : ℕ) (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = g) (hg1 : (g : 𝓞 F) ∈ v.asIdeal)
    (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) : absV v (g : Fv F v) = (g : ℝ)⁻¹ := by
  have hv := VolUAr.val_natCast_of v g hg1 hg2
  have e1 : ((g : v.adicCompletionIntegers F) : v.adicCompletion F) = (g : Fv F v) := by simp
  rw [e1] at hv
  unfold absV
  rw [dite_eq_right (by rw [hv]; exact WithZero.coe_ne_zero)]
  have hu : WithZero.unzero (show Valued.v (g : Fv F v) ≠ 0 by rw [hv]; exact WithZero.coe_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
    rfl
  rw [hu, toAdd_ofAdd, Ideal.absNorm_apply, Submodule.cardQuot_apply, hcard, zpow_neg, zpow_one]

end V

section X

variable {D : D7} (X : HidaSetting D)

theorem gAt_mem (v : PlX X) (hv : TypAt X v) : ((gAt X v : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
  have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
    (D.host.g_prime 1).ne_zero v).1 hv
  unfold gAt
  split_ifs with h
  · exact h
  · exact hty.resolve_left h

theorem gAt_split (v : PlX X) : {w : HeightOneSpectrum (𝓞 X.B.I.E) |
    ((gAt X v : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
  unfold gAt
  split_ifs
  · exact VolUAr.split_transport X.ιE _ (D.nd.g_split 0)
  · exact VolUAr.split_transport X.ιE _ (D.nd.g_split 1)

theorem typ_arith (v : PlX X) (hv : TypAt X v) :
    absV v (gAt X v : Fv X.B.I.F v) = (gAt X v : ℝ)⁻¹ ∧ Valued.v (dV v) = 1 ∧ absV v (dV v) = 1 := by
  haveI : Fact (gAt X v).Prime := ⟨gAt_prime X v⟩
  have hmem := gAt_mem X v hv
  obtain ⟨he, hf⟩ := VolUAr.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gAt X v) (gAt_split X v) v hmem
  obtain ⟨hc, hn⟩ := VolUAr.arith_of_loc (gAt X v) v hmem he hf
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) (S := 𝓞 X.B.I.F) (p := v.asIdeal)).2 he
  have hnd : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 X.B.I.F) := not_dvd_differentIdeal_iff.mpr hun
  rw [Ideal.dvd_iff_le] at hnd
  have hval := val_dV v hnd
  exact ⟨absV_g v (gAt X v) hc hmem hn, hval, absV_of_val_one v hval⟩

end X

end VolUT

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem volU_steps_of (hC : CondAll) (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (v : PlX X) (hv : TypAt X v)
    (hH : VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS) (hT : VolTTFCong X u u' v) : VolUSteps X u u' ψ v := by
  obtain ⟨hg, hdv, hd⟩ := VolUT.typ_arith X v hv
  have hann : VolUL.AnnAt (E := X.B.I.E) ψ v := VolUTr.annX_of X ψ hC hψ hs v
  have hfin := X.B.I.cm.deg2
  have hg0 : gAt X v ≠ 0 := (gAt_prime X v).ne_zero
  exact ⟨VolUL.volTAff_of ψ v hψ hfin hann hd hg0 hg _, VolUL.volTLocPres_of ψ v hψ hfin hann hd _, hH, hT,
    volTUOEq_of v hdv hg0 _, VolUL.volTProdU_of' ψ v hψ hfin hann hd hg0 hg _,
    (VolUL.sd_facts ψ v hψ hfin hann hd _).2.2⟩

theorem volTypV_of_cnt (hC : CondAll)
    (hH : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS)
    (hT : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTTFCong X u u' v) : VolTypV X u u' ψ :=
  volTypV_of_steps' X u u' ψ fun hh v hv =>
    volU_steps_of X u u' ψ hC hh.1 hh.2.1 v hv (hH hh v hv) (hT hh v hv)

end OfX

end Formalism.L2.SG.Pf.NcVal
end
end

