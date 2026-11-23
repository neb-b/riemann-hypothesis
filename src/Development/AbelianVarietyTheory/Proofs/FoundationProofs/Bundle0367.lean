module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrdinaryNormalFormUnramifiedSource
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfSrc

theorem upper_triangular_conj_lower_right_entry_eq {k : Type} [Field k] (B : GL (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k)
    (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (hX : X 1 0 = 0) :
    ((B : Matrix (Fin 2) (Fin 2) k) * X * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = X 1 1 := by
  have hinv := GlobalTheory.NfEx.inv_up B hB
  have h1 : ((B⁻¹ * B : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by simp
  have a11 := congrFun (congrFun h1 1) 1
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv.1, zero_mul, zero_add, Matrix.one_apply_eq] at a11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hB, hX, zero_mul, zero_add, mul_zero]
  calc _ = X 1 1 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 * (B : Matrix (Fin 2) (Fin 2) k) 1 1 := by ring
    _ = _ := by rw [mul_assoc, a11, mul_one]

end GlobalTheory.NfSrc

theorem GlobalTheory.Ord2.exists_nf_srcUr : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → SrcL ι e W → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l) (g : Newform (2 * e + 1)), RepIso W W' ∧ Nf e S A W' ∧ SrcUr ι e A W' g := by
  intro l _ Ω _ _ _ ι e W hl he hW hS
  obtain ⟨⟨g0, χ, A, κ, hM0, ha0, hχ, hatt, hA, hfl, hin⟩, hne⟩ := hS
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨M, hM, hMa⟩ := hW.away
  obtain ⟨S, hSa, hSu⟩ := GlobalTheory.T.unramified_of_levelAway_inertia_characters l Ω W M hM hMa
  let r : G ℚ Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj g).toMonoidHom.comp W
  have hrc : Continuous r := by
    show Continuous fun s => g * W s * g⁻¹
    exact (continuous_const.mul hW.cont).mul continuous_const
  obtain ⟨E, hE, hEm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l (G ℚ Ω) 2 r
    (fun i j => ((Units.continuous_val.comp hrc).matrix_elem i j))
  obtain ⟨B, hB10, hBint⟩ := _root_.GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral l (G ℚ Ω) E r hE hrc hEm
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CoefJoin.coef_of_finite l E hE
  let h : GL (Fin 2) (Qbar l) := B * g
  let W' : R2 Ω l := (MulAut.conj h).toMonoidHom.comp W
  have hh : ∀ s, W' s = h * W s * h⁻¹ := fun s => rfl
  have hW' : ∀ s, W' s = B * r s * B⁻¹ := fun s => by
    show h * W s * h⁻¹ = B * (g * W s * g⁻¹) * B⁻¹
    simp only [h, mul_inv_rev]; group
  have hiso : RepIso W W' := ⟨h, hh⟩
  have hdt : dt W' = dt W := by
    ext s
    rw [GlobalTheory.Ord2.TwDet.dt_coe, GlobalTheory.Ord2.TwDet.dt_conj W h s]
    rfl
  have hdet : ∀ s, (dt W' s : Qbar l) = (mat W' s).det := fun s => rfl
  have hker : ∀ s, W' s = 1 ↔ W s = 1 := fun s => by
    show h * W s * h⁻¹ = 1 ↔ W s = 1
    constructor
    · intro hh; rw [mul_inv_eq_one, mul_eq_left] at hh; exact hh
    · intro hh; rw [hh]; simp
  have hinv := GlobalTheory.NfEx.inv_up B hB10
  have hup : ∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) A), mat W' s 1 0 = 0 ∧ mat W' s 0 0 = (κ 0 ⟨s, hs⟩ : Qbar l) ∧
      mat W' s 1 1 = (κ 1 ⟨s, hs⟩ : Qbar l) := by
    intro s hs
    have h1 := (hg ⟨s, hs⟩).1 1 0 (by decide)
    have h2 := (hg ⟨s, hs⟩).2 0
    have h3 := (hg ⟨s, hs⟩).2 1
    have := GlobalTheory.NfEx.up2 (B : Matrix (Fin 2) (Fin 2) (Qbar l)) ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
      ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1 hinv.1
    have e1 : mat W' s = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      simp only [mat, hW', Units.val_mul]
    refine ⟨by rw [e1]; exact this.1, ?_, ?_⟩
    · rw [e1, this.2, ← h2]
      change _ = ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0
      calc _ = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 := by ring
        _ = _ := by rw [hinv.2, one_mul]
    · rw [e1, GlobalTheory.NfSrc.upper_triangular_conj_lower_right_entry_eq B ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1]
      exact h3

  have hline : ∀ (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A),
      mat W' s 0 0 = eps l s ^ e * (χ s : Qbar l) := by
    intro s hs
    have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
    obtain ⟨u10, u00, u11⟩ := hup s hd
    have hi := hin ⟨s, hd⟩ hs
    have hD : (dt W s : Qbar l) = mat W' s 0 0 * mat W' s 1 1 := by
      rw [← hdt, hdet, Matrix.det_fin_two, u10, mul_zero, sub_zero]
    have hdne : (dt W s : Qbar l) ≠ 0 := Units.ne_zero _
    simp only [zpow_natCast] at hi
    rw [← u11] at hi
    simp only [eps]
    calc mat W' s 0 0 = mat W' s 0 0 * (mat W' s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ e * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l))) := by
          rw [hi, mul_one]
      _ = (mat W' s 0 0 * mat W' s 1 1) * (dt W s : Qbar l)⁻¹ * ((cycBar ℚ Ω l s : Qbar l) ^ e * (χ s : Qbar l)) := by ring
      _ = _ := by rw [← hD, mul_inv_cancel₀ hdne, one_mul]
  refine ⟨S, A, W', g0, hiso, ?_, ?_⟩
  · refine
      { l_odd := hl
        e_pos := he
        cont := ?_
        int := ⟨c, fun s i j => (hc _).2 ⟨?_, ?_⟩⟩
        above := hSa
        unr := ?_
        det2 := by rw [hdt]; exact hW.det2
        odd := by rw [hdt]; exact hW.odd
        irr := _root_.GlobalTheory.IrrConj.irr_of_repIso Ω l W W' hiso hW.irr
        atL := hA
        upper := fun s hs => (hup s hs).1
        wt := ?_
        ne := ?_ }
    · show Continuous fun s => h * W s * h⁻¹
      exact (continuous_const.mul hW.cont).mul continuous_const
    · have := (hBint s i j).1; simpa only [mat, hW'] using this
    · have := (hBint s i j).2; simpa only [mat, hW'] using this
    · intro w hw B' hB' s hs
      exact (hker s).2 (hSu w hw B' hB' hs)
    · refine ⟨l - 1, ?_, fun s hs => ?_⟩
      · have := (Fact.out : l.Prime).two_le; omega
      · rw [hline s hs, mul_pow, ← pow_mul]
        have hχ1 := _root_.GlobalTheory.KillsMuOrd.charPow_sub_one_eq_one Ω l _ χ s hχ
        rw [← Units.val_pow_eq_pow_val (χ s), hχ1, Units.val_one, mul_one]
    · obtain ⟨s, hs⟩ := hne A κ hA ⟨g, hg⟩
      refine ⟨s, s.2, ?_⟩
      rw [(hup s s.2).2.1]
      intro hh
      exact hs (Units.ext hh)
  · refine ⟨hM0, ha0, χ, hχ, ?_, ?_⟩
    · rw [hdt]
      exact SrcConj.att_conj ι g0 _ _ h (SrcConj.tw_conj W W' _ h hh) hatt
    · intro s hs
      have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
      rw [(hup s hd).2.2, hdt]
      exact hin ⟨s, hd⟩ hs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteLTorsionSelmerRankTwoAdjoint
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem finite_lTorsion_divSel : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), ContainsAbove S l → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → Finite {x : DivSel c W S A // l • x = 0} := by
  intro hL l _ Ω _ _ _ S A W c hS hW hO hN
  have hH : Finite (H1 (resRep c W hO S hN)) :=
    (hL.gf ℚ Ω l 1 (ResPlane c) S (resRep c W hO S hN) one_pos hS (_root_.GlobalTheory.Ord2.resRep_contAction l Ω S W c hO hN hW)).2.1
  have key : ∀ x : {x : DivSel c W S A // l • x = 0}, ∃ (z : G ℚ Ω → Fin 2 → Qbar l) (hz : z ∈ divSelCoc c W S A)
      (y : Fin 2 → Qbar l), VecE c y ∧ (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
      (QuotientAddGroup.mk ⟨z, hz⟩ : DivSel c W S A) = x.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨y, hy, hzy⟩ := hx
    refine ⟨z, hz, y, hy, fun s i => ?_, rfl⟩
    have := hzy s i
    simpa only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] using this
  choose z hz y hy hzy hx using key
  refine Finite.of_injective (fun x => (Submodule.Quotient.mk
    ⟨descS S (resCoc c W (z x) (y x)), _root_.GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous l Ω S A W c hO hN hW (z x) (hz x) (y x) (hy x) (hzy x)⟩ :
      H1 (resRep c W hO S hN))) ?_
  intro x x' h
  rw [Submodule.Quotient.eq, Submodule.mem_comap, (mem_coboundaries1 _ _)] at h
  obtain ⟨m, hm⟩ := h
  have hd := _root_.GlobalTheory.Ord2.divCob_of_resCoc_cohom l Ω W c hO (z x) (z x') (y x) (y x') (hy x) (hy x') (hzy x) (hzy x') ⟨m, fun s => by
    have := hm (toGS Ω (S : Set Pl) s)
    simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at this
    rw [descS_resCoc_toGS c W S A hO hN (hz x) (y x) (hzy x) s,
      descS_resCoc_toGS c W S A hO hN (hz x') (y x') (hzy x') s] at this
    rw [this, resRep_toGS]⟩
  apply Subtype.ext
  rw [← hx x, ← hx x', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : (↑(-(⟨z x, hz x⟩ : divSelCoc c W S A) + ⟨z x', hz x'⟩) : G ℚ Ω → Fin 2 → Qbar l) = -(z x - z x') := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
  rw [this]
  exact (divCob c W).neg_mem hd

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedElementLthPowerMod
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

open Polynomial IsLocalRing

theorem exists_residue_pow_pow_eq (l : ℕ) [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hl1 : A.valuation (l : Ω) < 1) (xA : A) :
    ∃ N : ℕ, 0 < N ∧ residue A xA ^ (l ^ N) = residue A xA := by
  first
  | exact @_root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed
  | exact _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed
  | (apply _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed ..)

theorem fixA_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ a : fixA A, ∃ (b : fixA A) (z : A), (a : A) = (b : A) ^ l + (l : A) * z := by
  intro l _ Ω _ _ _ A hO a
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl1 : A.valuation (l : Ω) < 1 := GlobalTheory.Ord2.VanishNarrow.valuation_lt_one hO
  obtain ⟨N, hN, hr⟩ := exists_residue_pow_pow_eq l A hl1 (a : A)
  refine ⟨a ^ (l ^ (N - 1)), ?_⟩
  have hb : ((a ^ (l ^ (N - 1)) : fixA A) : A) ^ l = (a : A) ^ (l ^ N) := by
    rw [SubmonoidClass.coe_pow, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hN]
  rw [hb]
  set cA : A := (a : A) - (a : A) ^ (l ^ N) with hcA
  have hcfix : cA ∈ fixA A := (fixA A).sub_mem a.2 ((fixA A).pow_mem a.2 _)
  have hcm : cA ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, hcA, map_sub, map_pow, hr, sub_self]
  have hcv : A.valuation (cA : Ω) < 1 := by
    have := (A.valuation_lt_one_iff _).1 hcm
    simpa using this
  suffices h : ∃ z : A, cA = (l : A) * z by
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    rw [← hz, hcA]
    ring
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hvl0 : A.valuation (l : Ω) ≠ 0 := (_root_.map_ne_zero _).2 hl0
  by_cases hc0 : (cA : Ω) = 0
  · exact ⟨0, by rw [mul_zero]; exact Subtype.ext hc0⟩
  obtain ⟨k, hk⟩ := GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed l Ω A hO (cA : Ω) hc0 (mem_fixA.1 hcfix)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast] at hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero] at hk; exact absurd hk hcv.ne
    have hz : A.valuation ((cA : Ω) / (l : Ω)) ≤ 1 := by
      rw [map_div₀, hk, ← Nat.sub_add_cancel hn, pow_succ, mul_div_assoc, div_self hvl0, mul_one]
      exact pow_le_one' hl1.le _
    refine ⟨⟨(cA : Ω) / (l : Ω), (A.valuation_le_one_iff _).1 hz⟩, Subtype.ext ?_⟩
    change (cA : Ω) = (l : Ω) * ((cA : Ω) / (l : Ω))
    rw [mul_div_cancel₀ _ hl0]
  · exfalso
    rw [zpow_neg, zpow_natCast] at hk
    have e : A.valuation (cA : Ω) * A.valuation (l : Ω) ^ n = 1 := by
      rw [hk, inv_mul_cancel₀ (pow_ne_zero _ hvl0)]
    have : A.valuation (cA : Ω) * A.valuation (l : Ω) ^ n ≤ A.valuation (cA : Ω) :=
      mul_le_of_le_one_right' (pow_le_one' hl1.le _)
    rw [e] at this
    exact absurd hcv (not_lt.2 this)

end GlobalTheory.RecOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp

theorem sum_mulChar_eq_sum_units {K : Type} [CommRing K] {n : ℕ} (ψ : MulChar (ZMod n) K)
    (f : ZMod n → K) [Fintype (ZMod n)] :
    ∑ a : ZMod n, ψ a * f a = ∑ b : (ZMod n)ˣ, ψ b * f b := by
  classical
  rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun a _ h => by
    by_contra hu; exact h (by rw [MulChar.map_nonunit ψ hu, zero_mul]))]
  refine (Finset.sum_nbij' (fun b : (ZMod n)ˣ => (b : ZMod n)) (fun a => if h : IsUnit a then h.unit else 1)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro b _; simp
  · intro a _; simp
  · intro b _; simp
  · intro a ha
    have hu : IsUnit a := (Finset.mem_filter.1 ha).2
    simp [hu]
  · intro b _; rfl

theorem gSum_mul_gSum_inv_prim : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l)
    (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive →
    gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  intro l _ m z ψ hz hψ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let e : AddChar (ZMod (l ^ m)) (Qbar l) := AddChar.zmodChar (l ^ m) hz.pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root (l ^ m) hz
  have h1 : gSum m z ψ = gaussSum ψ e := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.zmodChar_apply]
  have h2 : gSum m z⁻¹ ψ⁻¹ = gaussSum ψ⁻¹ e⁻¹ := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.inv_apply', AddChar.zmodChar_apply, inv_pow]
  rw [h1, h2, GlobalTheory.KummerEisensteinGalois.gaussSum_mul_gaussSum_inv_prim hψ he]
  push_cast
  rfl

end GlobalTheory.KZ.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTower
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeGal

theorem B_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

def trSL (t : ℤ) : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem trSL_mem_Gam (N l : ℕ) (t : ℤ) : trSL t ∈ Gam N l := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]; simp [trSL]
  · rw [CongruenceSubgroup.Gamma0_mem]; simp [trSL]

theorem B_inv_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (t : ℤ) : X.act l !![1, t; 0, 1] b = b :=
  B_inv X N l w b hb (trSL t) (trSL_mem_Gam N l t)

theorem op_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.op N l T (X.galB l s b) = X.galB l s (X.op N l T b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw T hT s b hb
  have hgb : X.galB l s b ∈ X.B N l w := _root_.GlobalTheory.KZ.StabGal.galB_mem_B ε X hε hj N l w hl hN hNl hw s b hb
  have hinv := B_inv_tr X N l w _ hgb

  have hup : ∀ q : ℕ, 0 < q →
      (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) (X.galB l s b) =
        X.galB l s ((∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) b) := by
    intro q hq
    obtain ⟨e, he, hζ⟩ := _root_.GlobalTheory.algEquiv_primitiveRoot_pow s q hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    rw [← GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit X l _ hinv q e hq he]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (_root_.GlobalTheory.KZ.GalUpper.galB_act_upper ε X hε hj N l w hl hN hNl hw s q e hq hζ (j : ℤ) b hb).symm

  have hdiam : ∀ d : ℕ, Nat.Coprime d N → sgD N l d ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l := by
    intro d hd
    have hex := _root_.GlobalTheory.diam_exists N l d (by omega) hNl hd
    exact (Classical.epsilon_spec hex).1
  cases T with
  | T q =>
    obtain ⟨hqp, hqd⟩ := hT
    have hqN : Nat.Coprime q N :=
      (Nat.Coprime.coprime_dvd_right (Dvd.intro l rfl) ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqd))
    have hq : 0 < q := hqp.pos
    simp only [Tower.op, Tower.heckeT, LinearMap.add_apply, map_add (f := _)]
    rw [hup q hq]
    congr 1
    have hdet1 : 0 < (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [(sgD N l q).2]; exact one_pos
    have hdet2 : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two_of]; exact_mod_cast hq
    rw [← Tower.act_act Ω ε X l _ _ hdet1 hdet2, ← Tower.act_act Ω ε X l _ _ hdet1 hdet2,
      _root_.GlobalTheory.KZ.Tower.galB_act_diag ε X hε l q hq s,
      _root_.GlobalTheory.KZ.GammaZeroComm.galB_act_comm ε X hε hj N l w hl hN hNl hw (sgD N l q) (hdiam q hqN) s b hb]
  | U =>
    simp only [Tower.op, Tower.heckeU]
    exact hup l (Fact.out : l.Prime).pos
  | D d =>
    simp only [Tower.op, Tower.diam]
    exact (_root_.GlobalTheory.KZ.GammaZeroComm.galB_act_comm ε X hε hj N l w hl hN hNl hw (sgD N l d) (hdiam d hT) s b hb).symm

end GlobalTheory.KZ.HeckeGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtCoLSum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

namespace GlobalTheory.LambdaValuationPowers

theorem htCoL_sum : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l)
    (ι : Type) [Fintype ι] (a : ι → Qbar l) (Z : ι → ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : ι → Qbar l),
    (∀ i, ‖a i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (a i)) → (∀ i, GlobalTheory.LambdaValuationPowers.HTCoL A c j (Z i) m c₀ y (h i)) →
    GlobalTheory.LambdaValuationPowers.HTCoL A c j (fun r s y' => ∑ i, a i * Z i r s y') m c₀ y (∑ i, a i * h i) := by
  intro l _ Ω _ _ A c j ι _ a Z m c₀ y h ha hZ
  choose q o w hint hcg using hZ
  let e : Fin (Fintype.card (Σ i, Fin (q i))) ≃ (Σ i, Fin (q i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (q i)), fun k => a (e k).1 * o (e k).1 (e k).2, fun k => w (e k).1 (e k).2, ?_, ?_⟩
  · intro k
    obtain ⟨h1, h2, h3⟩ := hint (e k).1 (e k).2
    refine ⟨?_, ?_, h3⟩
    · rw [norm_mul]; exact mul_le_one₀ (ha _).1 (norm_nonneg _) h1
    · intro σ hσ hσ'
      rw [map_mul, (ha _).2 σ hσ hσ', h2 σ hσ hσ']
  · intro s hs hcyc
    have hre : (∑ k : Fin (Fintype.card (Σ i, Fin (q i))), a (e k).1 * o (e k).1 (e k).2 * (j (s (w (e k).1 (e k).2)) - j (w (e k).1 (e k).2)))
        = ∑ i, a i * ∑ r, o i r * (j (s (w i r)) - j (w i r)) := by
      rw [Equiv.sum_comp e (fun x => a x.1 * o x.1 x.2 * (j (s (w x.1 x.2)) - j (w x.1 x.2)))]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    unfold Cg
    rw [hre]
    have key : (l : Qbar l) ^ c₀ * (∑ i, a i * Z i m s y) -
        ((l : Qbar l) ^ c₀ * (∑ i, a i * h i) * lamv l m s + ∑ i, a i * ∑ r, o i r * (j (s (w i r)) - j (w i r)))
        = ∑ i, a i * ((l : Qbar l) ^ c₀ * Z i m s y - ((l : Qbar l) ^ c₀ * h i * lamv l m s + ∑ r, o i r * (j (s (w i r)) - j (w i r)))) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    have := hcg i s hs hcyc
    unfold Cg at this
    calc ‖a i‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (ha i).1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact this

end GlobalTheory.LambdaValuationPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosureStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) → ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | exact GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | (intros; apply GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed <;> assumption)
end

