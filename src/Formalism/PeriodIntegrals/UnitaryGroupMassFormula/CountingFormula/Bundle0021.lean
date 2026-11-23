module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CardLeOfNonpos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.AnisotropicComplementDefinite
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tn_ne_zero (D : D7) (u : D.what₂.Word) : (Tn u : D.host.E) ≠ 0 := by
  unfold Tn
  exact Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem tau_negT (D : D7) (u : D.what₂.Word) (φ : D.host.E →+* ℂ) : (φ (-(Tn u))).re < 0 := by
  have hT := (D.mem u).A.T_prime.pos
  first
    | simp [Tn, hT]
    | (unfold Tn; simp; exact hT)

theorem rank_VS (D : D7) : (VS D).rank = D.R.k + D.R.rS + (D.R.rS + 1) := by
  unfold VS
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, zero_mul, add_zero]
  omega

theorem wbDef_pos (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    Formalism.HermitianLattices.Ext.L3.IsTotPosDef (hPerp (hWb D F0) (zbar D F0)) := by
  rintro ⟨y, hy⟩ hne φ
  induction y using Submodule.Quotient.induction_on with
  | H a => ?_
  have hya : (VS D).hT F0.z a.1 = 0 := by
    have h := hy
    rw [wPerp, LinearMap.mem_ker, zbar, hWb_mk] at h
    exact h
  have hna : a.1 ∉ F0.X := by
    intro hmem
    apply hne
    apply Subtype.ext
    show Submodule.Quotient.mk a = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmem
  have hval : hPerp (hWb D F0) (zbar D F0) ⟨Submodule.Quotient.mk a, hy⟩ ⟨Submodule.Quotient.mk a, hy⟩ =
      (VS D).hT a.1 a.1 := hWb_mk D F0 a a
  rw [hval]
  by_contra hle
  push Not at hle
  have hT0 := tn_ne_zero D u
  have hzX : ∀ x ∈ F0.X, (VS D).hT F0.z x = 0 := fun x hx => hT_perp_X D F0 (z_mem_perp D F0) hx
  let v : Option (Option (Fin D.R.rS)) → (VS D).V :=
    fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e)
  have hv : LinearIndependent D.host.E v := by
    show LinearIndependent D.host.E
      (fun o => Option.casesOn' o a.1 (fun o' => Option.casesOn' o' F0.z F0.e) : Option (Option (Fin D.R.rS)) → (VS D).V)
    rw [linearIndependent_option', linearIndependent_option']
    refine ⟨⟨F0.e_indep, ?_⟩, ?_⟩
    · intro hz
      have h := hzX F0.z hz
      rw [F0.z_norm] at h
      exact hT0 (neg_eq_zero.1 h)
    · intro ha
      have hle' : Submodule.span D.host.E
          (Set.range (fun o' : Option (Fin D.R.rS) => Option.casesOn' o' F0.z F0.e)) ≤
          F0.X ⊔ Submodule.span D.host.E {F0.z} := by
        rw [Submodule.span_le]
        rintro _ ⟨o, rfl⟩
        cases o with
        | none => exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        | some i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (hle' ha)
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have h1 : (VS D).hT F0.z a.1 = c * (-(Tn u)) := by
        rw [← hxw, map_add (f := _), map_smul, hzX x hx, F0.z_norm, smul_eq_mul, zero_add]
      rw [hya] at h1
      have hc : c = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · exact h
        · exact absurd (neg_eq_zero.1 h) hT0
      apply hna
      rw [← hxw, hc, zero_smul, add_zero]
      exact hx
  have horth : ∀ o o', o ≠ o' → (VS D).hT (v o) (v o') = 0 := by
    intro o o' hne'
    match o, o', hne' with
    | none, none, h => exact absurd rfl h
    | none, some none, _ =>
      show (VS D).hT a.1 F0.z = 0
      rw [← (VS D).herm.eq F0.z a.1, hya, map_zero]
    | none, some (some j), _ => exact hT_perp_X D F0 a.2 (Submodule.subset_span ⟨j, rfl⟩)
    | some none, none, _ => exact hya
    | some none, some none, h => exact absurd rfl h
    | some none, some (some j), _ => exact hzX _ (Submodule.subset_span ⟨j, rfl⟩)
    | some (some i), none, _ => exact hT_X_perp D F0 (Submodule.subset_span ⟨i, rfl⟩) a.2
    | some (some i), some none, _ => exact F0.z_orth i
    | some (some i), some (some j), _ => exact F0.e_iso i j
  have hnp : ∀ o, (φ ((VS D).hT (v o) (v o))).re ≤ 0 := by
    intro o
    match o with
    | none => exact hle
    | some none =>
      show (φ ((VS D).hT F0.z F0.z)).re ≤ 0
      rw [F0.z_norm]
      exact le_of_lt (tau_negT D u φ)
    | some (some i) =>
      show (φ ((VS D).hT (F0.e i) (F0.e i))).re ≤ 0
      rw [F0.e_iso i i]
      simp
  have hcard := WbDefH.card_le_of_nonpos (VS D) φ (D.sp.cm.cmUnram.2.1 φ) (D.sp.Y_sig 0 φ) v hv horth hnp
  have hs : (VS D).sig φ = D.R.sigY0 := D.sp.baseSpace_signature_eq φ
  rw [hs] at hcard
  simp [Ranks.sigY0] at hcard

private theorem perpS_eq_ker_pi_hT (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    perpS (VS D) F0.X = LinearMap.ker (LinearMap.pi fun a => (VS D).hT (F0.e a)) := by
  ext y
  rw [LinearMap.mem_ker]
  constructor
  · intro hy
    have hy2 : ∀ x ∈ F0.X, (VS D).hT x y = 0 := hy
    funext a
    exact hy2 _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro hy
    have hy' : ∀ a, (VS D).hT (F0.e a) y = 0 := fun a => congrFun hy a
    show ∀ x ∈ F0.X, (VS D).hT x y = 0
    intro x hx
    unfold Formalism.MainNotions.S.FlagG.X at hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hy' a
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul c x _ h1 => simp [h1]

private theorem range_pi_hT_eq_top (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    LinearMap.range (LinearMap.pi fun a => (VS D).hT (F0.e a)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have key : ∀ a, f (fun j => if a = j then 1 else 0) = 0 := by
    have hw : ∀ y, (VS D).hT (∑ a, star (f (fun j => if a = j then 1 else 0)) • F0.e a) y = 0 := by
      intro y
      have h1 : f ((LinearMap.pi fun a => (VS D).hT (F0.e a)) y) = 0 :=
        LinearMap.mem_ker.mp (hf (LinearMap.mem_range_self _ y))
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
      simpa [LinearMap.pi_apply, smul_eq_mul, mul_comm] using h1
    have h0 := (VS D).nondeg.1 _ hw
    intro a
    have := Fintype.linearIndependent_iff.mp F0.e_indep
      (fun a => star (f (fun j => if a = j then 1 else 0))) h0 a
    simpa using this
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp [key]

theorem wbDef_dim (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) :
    finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) = D.R.k := by
  unfold wPerp
  have hle : F0.X ≤ perpS (VS D) F0.X := by
    rw [perpS_eq_ker_pi_hT D u F0]
    unfold Formalism.MainNotions.S.FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext b
    exact F0.e_iso b a
  have hX : finrank D.host.E F0.X = D.R.rS := by
    unfold Formalism.MainNotions.S.FlagG.X
    rw [finrank_span_eq_card F0.e_indep, Fintype.card_fin]
  have hnX : finrank D.host.E (nX D F0) = D.R.rS :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans hX
  have hP : finrank D.host.E (perpS (VS D) F0.X) + D.R.rS = D.R.k + D.R.rS + (D.R.rS + 1) := by
    rw [perpS_eq_ker_pi_hT D u F0]
    have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun a => (VS D).hT (F0.e a))
    rw [range_pi_hT_eq_top D u F0, finrank_top, Module.finrank_fin_fun] at h1
    have h2 := (VS D).rank_eq
    rw [rank_VS D] at h2
    omega
  have hq : finrank D.host.E (WbQ D F0) + finrank D.host.E (nX D F0) =
      finrank D.host.E (perpS (VS D) F0.X) :=
    Submodule.finrank_quotient_add_finrank (nX D F0)
  have hsurj : Function.Surjective (hWb D F0 (zbar D F0)) := by
    intro c
    refine ⟨(c / -(Tn u)) • zbar D F0, ?_⟩
    rw [map_smul, hWb_zbar, smul_eq_mul]
    have hT0 := tn_ne_zero D u
    field_simp
  have hk := LinearMap.finrank_range_add_finrank_ker (hWb D F0 (zbar D F0))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hk
  omega

theorem anisotropic_complement_definite : WbDef := by
  unfold WbDef
  intro D u F0
  exact ⟨wbDef_pos D u F0, wbDef_dim D u F0⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountCoeEqMultiplicity
section
open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem count_coe_eq_multiplicity {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors R) K) = (multiplicity v.asIdeal I : ℤ) := by
  rw [FractionalIdeal.count_coeIdeal K v hI, Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI v]

theorem eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {I J : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]

def belowP {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (P : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))
  isPrime := P.isPrime.comap _
  ne_bot := by
    intro h
    have hmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
    exact Ring.ne_bot_of_isMaximal_of_not_isField hmax (NumberField.RingOfIntegers.not_isField F) h

theorem exists_above {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 K), belowP P = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQc, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQc

theorem norm_mass_assembly : NormAssembly := by
  intro K F _ _ _ _ _ h2 J w hJ0 hc
  classical
  set wv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => w v.asIdeal with hwv

  have hcJ : ∀ P : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K P J =
      ((P.asIdeal.ramificationIdx (𝓞 F) * wv (belowP P) : ℕ) : ℤ) := fun P =>
    hc _ P (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal) rfl
  have he : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
    intro P
    haveI := P.isPrime
    exact (Ideal.ramificationIdx_pos (R := 𝓞 F) P.asIdeal).ne'

  have hfinJ := FractionalIdeal.finite_factors (K := K) J
  have hsupp : {v : HeightOneSpectrum (𝓞 F) | wv v ≠ 0}.Finite := by
    refine (hfinJ.image belowP).subset ?_
    intro v hv
    obtain ⟨P, rfl⟩ := exists_above (K := K) v
    refine ⟨P, ?_, rfl⟩
    show FractionalIdeal.count K P J ≠ 0
    rw [hcJ P]
    exact_mod_cast Nat.mul_ne_zero (he P) hv

  have hmsF : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  set IF : Ideal (𝓞 F) := ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ wv v with hIF
  have hIF0 : IF ≠ ⊥ := by
    rw [hIF, finprod_eq_prod _ hmsF]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  have hcF : ∀ v : HeightOneSpectrum (𝓞 F), multiplicity v.asIdeal IF = wv v := by
    intro v
    have h1 := count_coe_eq_multiplicity (K := F) v hIF0
    have h2 : ((IF : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ᶠ u : HeightOneSpectrum (𝓞 F), (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ ((wv u : ℕ) : ℤ) := by
      rw [hIF, FractionalIdeal.coeIdeal_finprod (nonZeroDivisors (𝓞 F)) F le_rfl]
      simp_rw [FractionalIdeal.coeIdeal_pow, zpow_natCast]
    rw [h2, FractionalIdeal.count_finprod] at h1
    · exact_mod_cast h1.symm
    · show {u | ¬ ((wv u : ℕ) : ℤ) = 0}.Finite
      simpa using hsupp

  have hJ : J = ((IF.map (algebraMap (𝓞 F) (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have hm0 : IF.map (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hIF0
    refine eq_of_count_eq hJ0 (by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]) fun P => ?_
    rw [hcJ P, count_coe_eq_multiplicity P hm0]
    haveI : P.asIdeal.LiesOver (belowP (K := K) (F := F) P).asIdeal := ⟨rfl⟩
    have hem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hIF0
      (belowP (K := K) (F := F) P).irreducible P.irreducible P.ne_bot
    rw [(FiniteMultiplicity.of_prime_left P.prime hm0).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left (belowP (K := K) (F := F) P).prime hIF0).emultiplicity_eq_multiplicity,
      hcF, Ideal.ramificationIdx'_eq_ramificationIdx _ P.asIdeal (belowP (K := K) (F := F) P).ne_bot] at hem
    exact_mod_cast hem.symm

  have hfr : Module.finrank (𝓞 F) (𝓞 K) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K]
    exact h2
  have hNJ : (FractionalIdeal.absNorm J : ℝ) = ((Ideal.absNorm IF : ℕ) : ℝ) ^ 2 := by
    rw [hJ, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap, hfr]
    push_cast
    rfl
  have hNIF : Ideal.absNorm IF = ∏ᶠ v : HeightOneSpectrum (𝓞 F), Ideal.absNorm v.asIdeal ^ wv v := by
    rw [hIF, map_finprod Ideal.absNorm hmsF]
    simp only [map_pow]
  have hms2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show Ideal.absNorm v.asIdeal ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  have hms3 : Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    refine hsupp.subset ?_
    intro v hv h0
    apply hv
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v = 1
    rw [show wv v = 0 from h0, pow_zero]
  let e : HeightOneSpectrum (𝓞 F) ≃ {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    { toFun := fun v => ⟨v.asIdeal, v.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime,
        Ring.ne_bot_of_isMaximal_of_not_isField p.2 (NumberField.RingOfIntegers.not_isField F)⟩
      left_inv := fun v => rfl
      right_inv := fun p => rfl }
  have ht : (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ wv v := by
    rw [← e.tprod_eq]
    exact tprod_eq_finprod hms3
  have hcast := map_finprod (Nat.castRingHom ℝ) hms2
  simp only [map_pow, eq_natCast] at hcast
  rw [hNJ, hNIF, ht, hcast]

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowsMassOfParts
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

end Pos

section Generic

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

end Generic

section Bridge

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem hWb_isSymm : (hWb D F0).IsSymm := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [hWb_mk, hWb_mk]
  exact (VS D).herm.eq a.1 b.1

theorem one_mem_stabF : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := by
  refine ⟨Subgroup.one_mem _, fun j => ?_, rfl⟩
  ext x
  simp

theorem one_mem_hz {V1 : Type} [AddCommGroup V1] [Module D.host.E V1]
    (h1 : V1 →ₗ⋆[D.host.E] V1 →ₗ[D.host.E] D.host.E) (z : V1) :
    (1 : V1 ≃ₗ[D.host.E] V1) ∈ hz h1 z :=
  ⟨Subgroup.one_mem _, rfl⟩

theorem gmap_one' {V1 : Type} [AddCommGroup V1] [Module D.host.E V1] [Module (𝓞 D.host.E) V1]
    [IsScalarTower (𝓞 D.host.E) D.host.E V1] (M : Submodule (𝓞 D.host.E) V1) :
    Formalism.HermitianLatticesTheory.gmap (1 : V1 ≃ₗ[D.host.E] V1) M = M := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end Bridge

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

