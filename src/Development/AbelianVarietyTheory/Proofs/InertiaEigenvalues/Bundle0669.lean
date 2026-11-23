module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemOfLpCharLpSpEqSumList
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicRingEquivAdicCompletionPlaceUnramifiedDegre
section
open NumberField IsDedekindDomain Polynomial ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

theorem resCard_padic (g : ℕ) [Fact g.Prime] : GlobalTheory.SplitWeil.resCard ℚ_[g] = g := by
  let e : 𝒪[ℚ_[g]] ≃+* ℤ_[g] :=
  { toFun := fun x => ⟨x.1, by
      have h := (Valuation.mem_integer_iff _ _).1 x.2
      have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 x.1).not.1 (by rw [map_one]; exact not_lt.2 h)
      rwa [norm_one, not_lt] at this⟩
    invFun := fun x => ⟨x.1, (Valuation.mem_integer_iff _ _).2 (by
      have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 x.1).not.2 (by rw [norm_one]; exact not_lt.2 x.2)
      rwa [map_one, not_lt] at this)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
  unfold GlobalTheory.SplitWeil.resCard
  rw [Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv e).trans PadicInt.residueField).toEquiv, Nat.card_zmod]

theorem padic_v_map_le_one_iff {E : Type} [Field E] [NumberField E] {g : ℕ} [Fact g.Prime]
    {w : HeightOneSpectrum (𝓞 E)} (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (y : ℚ_[g]) :
    Valued.v (i y) ≤ 1 ↔ ‖y‖ ≤ 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one,
    valuation_map_le_one_iff i hi y]
  have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 y).not
  rwa [map_one, norm_one, not_lt, not_lt] at this

end GlobalTheory.LocalFieldIso


open GlobalTheory.LocalFieldIso in
theorem GlobalTheory.LocalFieldIso.padic_iso_place : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) [Fact g.Prime] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ((g : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 ∧ Formalism.ConjugateSelfDual.normV w = g := by
  intro E _ _ g _ w i hi
  have hv : ∀ y : E, Valued.v (algebraMap E (w.adicCompletion E) y) = w.valuation E y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y
  have hgc : i (g : ℚ_[g]) = algebraMap E (w.adicCompletion E) (((g : ℕ) : 𝓞 E) : E) := by simp
  have hgp : 1 < (g : ℝ) := by exact_mod_cast (Fact.out : g.Prime).one_lt
  refine ⟨?_, ?_, ?_⟩
  · have h := GlobalTheory.Published.DepthZeroTypeModel.v_lt_one i hi (k := (g : ℚ_[g])) Padic.norm_p_lt_one
    rw [hgc, hv, HeightOneSpectrum.valuation_of_algebraMap] at h
    rwa [HeightOneSpectrum.intValuation_lt_one_iff_mem] at h
  · intro hg2
    have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_mem w _ 2).2 hg2
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
    set P := algebraMap E (w.adicCompletion E) π with hP
    have hPv : Valued.v P = WithZero.exp (-1) := by rw [hP, hv, hπ]
    have hP0 : P ≠ 0 := by intro h; rw [h, map_zero] at hPv; exact WithZero.exp_ne_zero hPv.symm
    set x := i.symm P with hx
    have hix : i x = P := by simp [hx]
    have hx0 : x ≠ 0 := by intro h; apply hP0; rw [← hix, h, map_zero]
    have hxlt : ‖x‖ < 1 := by
      by_contra hc
      have h1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 hc)
      have h3 := (padic_v_map_le_one_iff i hi _).2 h1
      rw [map_inv₀, hix, map_inv₀, hPv, ← WithZero.exp_neg, neg_neg] at h3
      exact absurd h3 (not_le.2 (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num))
    have hxle : ‖x‖ ≤ (g : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one x (-1)).2 (by simpa using hxlt)
    have hy : Valued.v (i ((g : ℚ_[g]) * x⁻¹ ^ 2)) ≤ 1 := by
      rw [map_mul, hgc, map_pow, map_inv₀, hix, Valuation.map_mul, hv, HeightOneSpectrum.valuation_of_algebraMap,
        Valuation.map_pow, map_inv₀, hPv]
      refine le_trans (mul_le_mul_of_nonneg_right h2 zero_le') (le_of_eq ?_)
      rw [← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add]
      norm_num
    have hn := (padic_v_map_le_one_iff i hi _).1 hy
    rw [norm_mul, norm_pow, norm_inv, Padic.norm_p] at hn
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have : (g : ℝ)⁻¹ ≤ ‖x‖ ^ 2 := by
      rwa [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)] at hn
    rw [zpow_neg_one] at hxle
    have hg0 : (0 : ℝ) < (g : ℝ)⁻¹ := by positivity
    have h5 : ‖x‖ ^ 2 ≤ ((g : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ hxpos.le hxle 2
    have h6 : ((g : ℝ)⁻¹) ^ 2 < (g : ℝ)⁻¹ := by
      rw [sq]; exact mul_lt_of_lt_one_left hg0 (inv_lt_one_of_one_lt₀ hgp)
    linarith
  · rw [← GlobalTheory.LocLanglands.resCard_eq_normV, resCard_eq i hi, resCard_padic]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEq
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne.SpUnique

open SpSummand

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section Rep

variable {V U U' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] [AddCommGroup U'] [Module ℂ U']
  [FiniteDimensional ℂ U'] {ρ : Representation ℂ (Weil h) V} {k : ℕ} {c : Weil h → ℂ}

theorem hasCopy_sum_left {b : WDRep h U} (b' : WDRep h U') (H : HasCopy ρ k c b) :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inl ℂ U U' ∘ₗ ((b.N ^ k) ∘ₗ g), LinearMap.inl ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.fst (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simpa using this
    · simp
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem hasCopy_sum_right (b : WDRep h U) {b' : WDRep h U'} (H : HasCopy ρ k c b') :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inr ℂ U U' ∘ₗ ((b'.N ^ k) ∘ₗ g), LinearMap.inr ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.snd (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simp
    · simpa using this
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem powZero_sum {b : WDRep h U} {b' : WDRep h U'} (H : PowZero k b) (H' : PowZero k b') :
    PowZero k (b.sum b') := by
  unfold PowZero at *
  rw [sum_N_pow, H, H', LinearMap.prodMap_zero]

theorem powZero_of_le (a : WDRep h U) (ha : a.ρ.IsIrreducible) {m : ℕ} (hmk : m ≤ k) :
    PowZero k (a.tensor (WDRep.sp h (m + 1))) := by
  unfold PowZero
  rw [tensor_sp_N_pow a (N_eq_zero_of_irr a ha), shiftEnd_pow_eq_zero (by omega),
    LinearMap.lTensor_zero]

theorem hasCopyW_lpSum_left (x y : WD h) (H : HasCopyW ρ k c x) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_left b H

theorem hasCopyW_lpSum_right (x y : WD h) (H : HasCopyW ρ k c y) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_right a H

theorem powZeroW_lpSum_of (x y : WD h) (H : PowZeroW k x) (H' : PowZeroW k y) :
    PowZeroW k (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, powZeroW_mk]
      rw [powZeroW_mk] at H H'
      exact powZero_sum H H'

theorem powZeroW_lpZero : PowZeroW k (WD.lpZero (h := h)) := by
  rw [WD.lpZero, powZeroW_mk]
  show (WDRep.diag h _).N ^ (k + 1) = 0
  rw [WDRep.diag_N, zero_pow (Nat.succ_ne_zero k)]

theorem hasCopyW_sumList {α : Type} (F : α → WD h) (l : List α) (p : α) (hp : p ∈ l)
    (H : HasCopyW ρ k c (F p)) : HasCopyW ρ k c (sumList (l.map F)) := by
  induction l with
  | nil => cases hp
  | cons q l ih =>
    change HasCopyW ρ k c ((F q).lpSum (sumList (l.map F)))
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hasCopyW_lpSum_left _ _ H
    · exact hasCopyW_lpSum_right _ _ (ih hp)

theorem powZeroW_sumList {α : Type} (F : α → WD h) (l : List α) (H : ∀ p ∈ l, PowZeroW k (F p)) :
    PowZeroW k (sumList (l.map F)) := by
  induction l with
  | nil => exact powZeroW_lpZero
  | cons q l ih =>
    change PowZeroW k ((F q).lpSum (sumList (l.map F)))
    exact powZeroW_lpSum_of _ _ (H q List.mem_cons_self) (ih fun p hp => H p (List.mem_cons_of_mem _ hp))

end Rep

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
    rw [ih]
  | swap x y l =>
    show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
    rw [← WD.lpSum_assoc, ← WD.lpSum_assoc, WD.lpSum_comm x y]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem lpDim_pos (p : WD h × ℕ) (hp : IsIrrWD p.1) :
    0 < WD.lpDim (p.1.lpChar (WD.lpSp h (p.2 + 1))) := by
  obtain ⟨n, a, ha, hirr⟩ := hp
  rw [WD.lpDim_tensor, WD.lpDim_lpSp, ← ha, WD.lpDim_mk, Module.finrank_fin_fun]
  obtain ⟨v, hv⟩ := exists_ne_zero hirr
  have hn : n ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim _ _)
  exact Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos _)

theorem perm_of_sumList_lpChar_lpSp_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l l' : List (WD h × ℕ)), (∀ p ∈ l, IsIrrWD p.1) → (∀ p ∈ l', IsIrrWD p.1) → sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) = sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' := by
  intro E Ω _ _ _ _ _ A w h l l'
  classical
  suffices H : ∀ n (l l' : List (WD h × ℕ)), l.length = n → (∀ p ∈ l, IsIrrWD p.1) →
      (∀ p ∈ l', IsIrrWD p.1) →
      sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) =
        sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' from
    H _ l l' rfl
  intro n
  induction n with
  | zero =>
    intro l l' hn hl hl' heq
    obtain rfl := List.length_eq_zero_iff.1 hn
    cases l' with
    | nil => exact List.Perm.nil
    | cons q l'' =>
      exfalso
      have hd := congrArg WD.lpDim heq
      change WD.lpDim (WD.lpZero (h := h)) = WD.lpDim (WD.lpSum _ (sumList _)) at hd
      rw [WD.lpDim_zero, WD.lpDim_sum] at hd
      have := lpDim_pos q (hl' q List.mem_cons_self)
      beta_reduce at hd
      omega
  | succ n ih =>
    intro l l' hn hl hl' heq
    have hne : l ≠ [] := by
      rintro rfl
      simp at hn
    obtain ⟨⟨y, k⟩, hp, hmax⟩ : ∃ p ∈ l, ∀ q ∈ l, q.2 ≤ p.2 := by
      obtain ⟨p, hp, hmax⟩ := l.toFinset.exists_max_image Prod.snd
        (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne; exact ⟨x, List.mem_toFinset.2 hx⟩)
      exact ⟨p, List.mem_toFinset.1 hp, fun q hq => hmax q (List.mem_toFinset.2 hq)⟩
    obtain ⟨m, a, rfl, ha⟩ := hl _ hp

    have hQ : HasCopyW a.ρ k (lastEig h k)
        (sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1))))) := by
      refine hasCopyW_sumList _ l _ hp ?_
      show HasCopyW a.ρ k (lastEig h k) ((WD.mk a).lpChar (WD.lpSp h (k + 1)))
      rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk]
      exact hasCopy_self a ha k
    have hZ : PowZeroW k
        (sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1))))) := by
      refine powZeroW_sumList _ l fun q hq => ?_
      rcases q with ⟨y', k'⟩
      obtain ⟨m', a', rfl, ha'⟩ := hl _ hq
      show PowZeroW k ((WD.mk a').lpChar (WD.lpSp h (k' + 1)))
      rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk]
      exact powZero_of_le a' ha' (hmax _ hq)
    rw [heq] at hQ hZ
    obtain ⟨⟨y', k'⟩, hq', hqQ, hqZ⟩ := exists_mem_of_sumList _ l' hQ hZ
    obtain ⟨n', a', rfl, ha'⟩ := hl' _ hq'
    dsimp only at hqQ hqZ
    rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk] at hqQ
    rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk] at hqZ
    obtain ⟨hm, hiso⟩ := eq_of_hasCopy a ha a' ha' k' k hqQ hqZ
    have hp' : (WD.mk a, k) ∈ l' := by
      have : ((WD.mk a', k') : WD h × ℕ) = (WD.mk a, k) := Prod.ext (WD.sound hiso).symm hm
      rw [← this]
      exact hq'

    set p : WD h × ℕ := (WD.mk a, k) with hpdef
    set F : WD h × ℕ → WD h := fun p => p.1.lpChar (WD.lpSp h (p.2 + 1)) with hF
    have e1 : sumList (l.map F) = (F p).lpSum (sumList ((l.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp).map F)
    have e2 : sumList (l'.map F) = (F p).lpSum (sumList ((l'.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp').map F)
    have hc : sumList ((l.erase p).map F) = sumList ((l'.erase p).map F) := by
      refine WD.lpSum_cancel_right E Ω A w h _ _ (F p) ?_
      rw [WD.lpSum_comm, ← e1, WD.lpSum_comm, ← e2]
      exact heq
    have hlen : (l.erase p).length = n := by
      rw [List.length_erase_of_mem hp, hn]
      rfl
    have := ih (l.erase p) (l'.erase p) hlen (fun q hq => hl q (List.mem_of_mem_erase hq))
      (fun q hq => hl' q (List.mem_of_mem_erase hq)) hc
    exact ((List.perm_cons_erase hp).trans (this.cons p)).trans (List.perm_cons_erase hp').symm

end GlobalTheory.WeilDeligne.SpUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisNonGraphLagrangianSumEqZeroCuspidal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open scoped GlobalTheory.GaugeEx

noncomputable section
namespace GlobalTheory.RallisCusp

theorem nonGraph_sum_eq_zero : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  intro D hEis hMove hInv hKill hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI : Countable (Lag W) := lag_countable D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  haveI := hS.haarW
  have hw := hS.weil
  have hpres : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (om p f) := hw.om_pres
  have hom : ∀ (g h : GA D W) f, om (1, g) (om (1, h) f) = om (1, g * h) f := by
    intro g h f
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

  have hmove : ∀ (γ : GQ W) (Y : Lag W) (g : GA D W) (F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₂ →
      lagTerm μ 𝓕 (fr (lagAct W γ Y)) (om (1, g) f₁) F₂ = lagTerm μ 𝓕 (fr Y) (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ := by
    intro γ Y g F₂ hF₂
    have h1 := (hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, g) f₁) F₂ (hpres _ _ hf₁) hF₂).1
      (lagAct W γ Y) _ (isLagFrame_lagAct W γ Y (fr Y) (hS.frame Y))
    have h2 := ((hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ (hpres _ _ hf₁) hF₂).2
      γ γ.2 (gqMat W γ) (gqMat_map W γ).symm).1 (fr Y)
    rw [← h1, ← h2, hom, mul_inv_cancel_left]

  have hslice : ∀ g₂ : GA D W, ∑' Y : NGLag W, ∫⁻ g in 𝓖, ‖star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)‖ₑ ∂νW ≠ ⊤ →
      ∑' Y : NGLag W, ∫ g in 𝓖, star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) ∂νW = 0 := by
    intro g₂ hfin
    have hF₂ := hpres (1, g₂) f₂ hf₂
    have hGQ : Countable (GQ W) := by
      haveI : Countable (Matrix (Fin W.rank) (Fin W.rank) D.host.E) :=
        inferInstanceAs (Countable (Fin W.rank → Fin W.rank → D.host.E))
      refine Function.Injective.countable (f := fun γ : GQ W => gqMat W γ) ?_
      intro γ δ h
      apply Subtype.ext
      apply GlobalTheory.MixModel.mt_injective W
      have := congrArg (fun c => c.map (incA D)) h
      simpa only [gqMat_map] using this
    refine _root_.GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer νW inferInstance (GQ W) hGQ 𝓖 hS.fdW (ngAct W) (ngAct_one W) (ngAct_mul W)
      (fun Y g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) ?_ ?_ hfin ?_
    · intro γ Y g
      show star (φ₁ g) * lagTerm μ 𝓕 (fr (lagAct W γ Y.1)) _ _ = _
      rw [hmove γ Y.1 g _ hF₂, ha₁.left _ (inv_mem γ.2) g]
    · intro Y
      exact ((continuous_star.comp ha₁.cont).mul (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2)).aestronglyMeasurable
    · intro Y Γ hΓ 𝓓 h𝓓 hint
      obtain ⟨s, I, hI, hspan⟩ := _root_.GlobalTheory.RawLift.exists_isoFrame_comap_inl D W Y.1 Y.2
      have hle : Γ ≤ GQ W := fun g hg => ((hΓ g).1 hg).1
      have hfix : ∀ g (hg : g ∈ Γ), lagAct W ⟨g, hle hg⟩ Y.1 = Y.1 := by
        intro g hg
        obtain ⟨h, e⟩ := (hΓ g).1 hg
        exact congrArg Subtype.val e
      have key := hKill W νW hS.haarW s I hI Γ hle
        (fun n hn => (hΓ n).2 ⟨hn.2, Subtype.ext (_root_.GlobalTheory.RallisCuspStab.lagAct_eq_of_mem_NI D W Y.1 s I hI hspan ⟨n, hn.2⟩ hn.1)⟩)
        (fun γ hγ n hn => GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent D W Y.1 s I hI hspan ⟨γ, hle hγ⟩ (hfix γ hγ) n hn) 𝓓 h𝓓
        (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) (fun g => star (φ₁ g))
        (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2) ?_ ?_ ?_ ?_ ?_
      · rw [← key]
        congr 1
        funext g
        ring
      · intro γ hγ g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, γ * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        have := hmove ⟨γ, hle hγ⟩ Y.1 (γ * g) _ hF₂
        rw [hfix γ hγ] at this
        rw [this]
        congr 3
        exact congrArg (Prod.mk 1) (inv_mul_cancel_left γ g)
      · intro n hn g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, n * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        rw [← hom]
        exact hInv ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y.1 s I hI hspan n hn _ _ (hpres _ _ hf₁) hF₂
      · exact ⟨fun γ hγ g => by show star (φ₁ (γ * g)) = star (φ₁ g); rw [ha₁.left γ hγ g],
          by
            obtain ⟨U, hU, hk⟩ := ha₁.level
            exact ⟨U, hU, fun k hk1 hk2 g => by show star (φ₁ (g * k)) = star (φ₁ g); rw [hk k hk1 hk2 g]⟩,
          continuous_star.comp ha₁.cont⟩
      · intro r C hC μ' 𝓕' hμ' h𝓕' g
        have := hc₁ r C hC μ' 𝓕' hμ' h𝓕' g
        show ∫ n in 𝓕', (starRingEnd ℂ) (φ₁ ((n : GA D W) * g)) ∂μ' = 0
        rw [integral_conj, this, map_zero]
      · have e : (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) =
            fun g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) := funext fun g => mul_comm _ _
        show IntegrableOn (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) 𝓓 νW
        rw [e]
        exact hint
  have hφ₁c : Continuous φ₁ := ha₁.cont
  refine _root_.GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner (X := NGLag W) inferInstance νW inferInstance 𝓖
    (fun Y p => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂)) ?_ ?_ ?_
  · intro Y
    have hm := GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hw hS.covol f₁ f₂ hf₁ hf₂ (fr Y.1)
    exact (((continuous_star.comp hφ₁c).comp continuous_fst).mul (ha₂.cont.comp continuous_snd)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable
  · have h0 := hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂
    refine ne_top_of_le_ne_top h0 (lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_)
    have e : ∀ Y : NGLag W, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ =
        (fun Y : Lag W => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ) Y.1 := by
      intro Y
      have hs : ‖star (φ₁ g₁)‖ₑ = ‖φ₁ g₁‖ₑ := by simp [enorm_eq_nnnorm]
      simp only
      rw [enorm_mul, enorm_mul, hs]
      ring
    rw [tsum_congr e]
    exact (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
  · intro g₂ hfin
    by_cases h0 : φ₂ g₂ = 0
    · simp [h0]
    · have e1 : ∀ Y : NGLag W, ∫ g₁ in 𝓖, star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW =
          φ₂ g₂ * ∫ g₁ in 𝓖, star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW := by
        intro Y
        rw [← integral_const_mul]
        congr 1
        funext g₁
        ring
      have e2 : ∀ Y : NGLag W, ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW =
          ‖φ₂ g₂‖ₑ * ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW := by
        intro Y
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        congr 1
        funext g₁
        rw [enorm_mul, enorm_mul, enorm_mul]
        ring
      simp only at hfin ⊢
      rw [tsum_congr e2, ENNReal.tsum_mul_left] at hfin
      rw [tsum_congr e1, tsum_mul_left, hslice g₂ ?_, mul_zero]
      intro htop
      rw [htop, ENNReal.mul_top (enorm_ne_zero.2 h0)] at hfin
      exact hfin rfl

end GlobalTheory.RallisCusp
end
end

