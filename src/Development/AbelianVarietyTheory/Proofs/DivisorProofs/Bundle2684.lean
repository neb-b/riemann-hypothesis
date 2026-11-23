module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionCompStructureEqGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchSecOfUnf
section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom

noncomputable section

namespace GlobalTheory.FlatDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


theorem framesOn_eq {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hgeo : FnAlgClosed (Xo := Xo) (c := c)) (Z : Comp Xo c) : ∃ k, framesOn U Z = {z | z.1 = k ∧ z.2 ∈ (U.X z.1).dom} := by
  obtain ⟨q, hq⟩ : ∃ q : U.Comp ≃ Comp Xo c, ∀ k (y : (U.X k).dom) (s : Sp (CAt σ)),
      GlobalTheory.AllWt.ptF (U.un k y) s ∈ (q k).1 :=
    GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU
      (fun k => GlobalTheory.CompBij.frames_nonempty _) hgeo
  refine ⟨q.symm Z, Set.ext fun ⟨k, y⟩ => ⟨?_, ?_⟩⟩
  · rintro ⟨hy, hl⟩
    refine ⟨?_, hy⟩
    have hk : q k = Z := by
      by_contra hne
      let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) (hq k ⟨y, hy⟩ s) (hl s)
    exact (Equiv.eq_symm_apply q).2 hk
  · rintro ⟨hk, hy⟩
    obtain rfl : k = q.symm Z := hk
    refine ⟨hy, fun s => ?_⟩
    have := hq (q.symm Z) ⟨y, hy⟩ s
    rwa [Equiv.apply_symm_apply] at this


open GlobalTheory.BdryUnit in
theorem const_length {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hgeo : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c} {τ : Psi H} {Y : Model Xo c (RingHom.id c.F)} {V : (Xo.XF c).Opens}
    {sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1} {f : Rul Xo c} (hV : (V : Set (Xo.XF c)) = Z)
    (hn : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig) (hh : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig) (hr : Reads Y V τ sig f) :
    ∃ b : ℝ, 0 < b ∧ homN U x (wtOf Dw (flatWt Dw τ) 0) f '' framesOn U Z = {b} := by
  obtain ⟨k, hk⟩ := framesOn_eq U hσ hU hgeo Z
  have hτ : relab c σ τ.1 ∈ (U.X k).Ψ := by
    refine ((hU.2.1 k).2 _).2 ?_
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0
  obtain ⟨a, ha⟩ := rdU_eq_mul_horizGen U hσ hU τ hn hh hr k hτ
  obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty (U.X k)
  have hy' : (⟨k, y⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z := by rw [hk]; exact ⟨rfl, hy⟩
  have ha0 : a ≠ 0 := by
    obtain ⟨h1, h2⟩ := ha ⟨y, hy⟩ (hV ▸ hy'.2)
    exact left_ne_zero_of_mul (h2 ▸ h1)
  refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 (U.X k).Gm.det‖),
    mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha0) (Real.sqrt_pos.2 (norm_pos_iff.2
      ((map_ne_zero _).2 (U.X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨_, hy'⟩, ?_⟩⟩
  rintro ⟨k', y'⟩ hz
  have hz' := hz
  rw [hk] at hz'
  obtain ⟨rfl, hy₁⟩ : k' = k ∧ y' ∈ (U.X k').dom := hz'
  have h1 := (ha ⟨y', hy₁⟩ (hV ▸ hz.2)).2
  rw [← pnorm_horizGen (U.X k') ⟨_, hτ⟩ hy₁, homN, ptN, modelWt_flatWt U hσ hU τ k' hτ]
  simp only at h1
  simp only [Data.pnorm, h1, norm_mul, mul_assoc]

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}

theorem evR_sig_mul_inv (s : ArchSec U x Z (flatWt Dw τ)) {k : Type} [Field k] [Algebra c.F k] {y : FrPt Xo c k}
    (h : LiesOn Z y) : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
  rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem h (GlobalTheory.FlagTan.fromTest_of_isLocalRing y)]

theorem detLaw_sig (s : ArchSec U x Z (flatWt Dw τ)) : DetLaw Z s.sig τ.1 (conjEmb τ.1) :=
  ⟨s.sig_mem.1, fun _ _ _ z y _ h g₁ g₂ h₁ h₂ => GlobalTheory.FlatGL.evR_flat_chg τ s.sig_mem z y h g₁ g₂ h₁ h₂⟩

theorem detLaw_inv (s : ArchSec U x Z (flatWt Dw τ)) : DetLaw Z s.inv (conjEmb τ.1) τ.1 := by
  refine ⟨s.inv_mem.1, fun k _ _ z y hy h g₁ g₂ h₁ h₂ => ?_⟩
  have hz : LiesOn Z z := by
    have e : GlobalTheory.AllWt.ptF z = GlobalTheory.AllWt.ptF y := by
      apply pullback.hom_ext
      · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_fst, pullback.lift_fst, h]
      · rw [GlobalTheory.AllWt.ptF, GlobalTheory.AllWt.ptF, pullback.lift_snd, pullback.lift_snd]
    exact fun p => e ▸ hy p
  have k1 := GlobalTheory.FlatGL.evR_flat_chg τ s.sig_mem z y h g₂ g₁ h₂ h₁
  have k2 := evR_sig_mul_inv s hy
  have k3 := evR_sig_mul_inv s hz
  linear_combination (-(evR Xo c s.inv z * evR Xo c s.inv y)) * k1 + (g₂.det * evR Xo c s.inv y) * k3 -
    (g₁.det * evR Xo c s.inv z) * k2


set_option synthInstance.maxHeartbeats 400000 in
theorem archSec_denom (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (s : ArchSec U x Z (flatWt Dw τ))
    (hs : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0) :
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  have hb : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) →
      (letI := io.toAlgebra; LiesOn Z y₀.1) →
      evI y₀ s.sig ∈ (algebraMap T.V T.Fr).range ∧ evI y₀ s.inv ∈ (algebraMap T.V T.Fr).range := by
    intro T io y₀ h1 h2
    letI := io.toAlgebra
    have h3 := hs T io y₀ h1 h2
    have h4 : evI y₀ s.sig * evI y₀ s.inv = 1 := evR_sig_mul_inv s h2
    have h5 := left_ne_zero_of_mul_eq_one h4
    have h6 := right_ne_zero_of_mul_eq_one h4
    rw [nval_of_ne h5, EReal.coe_eq_zero, Nat.cast_one, div_one, Int.cast_eq_zero] at h3
    have h7 := vV_mul (V := T.V) h5 h6
    rw [h4, show vV T.V (1 : T.Fr) = 0 by simp [vV], h3] at h7
    exact ⟨Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) h3.ge,
      Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) (by omega)⟩
  obtain ⟨m₁, hm₁, h₁⟩ := Cover.exists_denom hpq hA Z (detLaw_sig s) fun T io y₀ h1 h2 => (hb T io y₀ h1 h2).1
  obtain ⟨m₂, hm₂, h₂⟩ := Cover.exists_denom hpq hA Z (detLaw_inv s) fun T io y₀ h1 h2 => (hb T io y₀ h1 h2).2
  have hn : ∀ (n : ℕ), 0 < n → ∀ la, ∀ v ∈ valOn Z la, ∀ f : Rul Xo c, 0 ≤ v f → 0 ≤ v ((n : c.F) • f) := by
    intro n hn la v hv f hf
    rw [(isVal_valOn hv).smul _ _ (Nat.cast_ne_zero.2 hn.ne')]
    refine add_nonneg (EReal.coe_nonneg.2 ?_) hf
    have := Formalism.L2.Pj.vAdd_int_nonneg la (a := (n : 𝓞 c.F)) (by
      have : (n : c.F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      simpa using this)
    have h2 : 0 ≤ Formalism.BasicNotions.vAdd la (n : c.F) := by simpa using this
    exact_mod_cast h2
  refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun la v hv => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact hn _ hm₂ la v hv _ (h₁ la v hv)
  · rw [Nat.cast_mul, mul_smul]
    exact hn _ hm₁ la v hv _ (h₂ la v hv)

end GlobalTheory.FlatDenom


namespace GlobalTheory.FlatDenom

section Powers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)

def HasBddSec (la : GlobalTheory.AllWt.Weight Dw) : Prop :=
  ∃ (s : ArchSec U x Z la) (m : ℕ), 0 < m ∧ ∀ w, ∀ v ∈ valOn Z w, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv)

variable {U x Z} {la la' : GlobalTheory.AllWt.Weight Dw}

theorem homN_sig (s : ArchSec U x Z la) {σ : c.F →+* ℂ} {z} (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (wtOf Dw la 0) s.sig z = s.cInf σ := (image_eq_singleton_iff.1 (s.norm_inf σ)).2 z hz

theorem homN_inv (s : ArchSec U x Z la) {σ : c.F →+* ℂ} {z} (hz : z ∈ framesOn (U (goodOf c σ)) Z) :
    homN (U (goodOf c σ)) x (wtOf Dw (-la) 0) s.inv z = (s.cInf σ)⁻¹ := by
  have h := homN_mul (U (goodOf c σ)) x (even_wtOf (-la) 0) (even_wtOf la 0) s.inv s.sig z hz.1
  rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm s.inv, s.mul_inv, homN_sig s hz,
    homN_idem _ x hz.1 hz.2 (tested_of_homN_ne _ x hz.1 ((homN_sig s hz).symm ▸ (s.cInf_pos σ).ne'))] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem HasBddSec.neg (h : HasBddSec U x Z la) : HasBddSec U x Z (-la) := by
  obtain ⟨s, m, hm, h⟩ := h
  exact ⟨⟨s.inv, s.sig, exOf_neg la ▸ s.inv_mem, by rw [exOf_neg, neg_neg]; exact s.sig_mem, s.idem_inv, s.idem_sig,
    by rw [mul_comm, s.mul_inv], s.cInf⁻¹, fun σ => inv_pos.2 (s.cInf_pos σ), fun σ => image_eq_singleton_iff.2
      ⟨(image_eq_singleton_iff.1 (s.norm_inf σ)).1, fun z hz => homN_inv s hz⟩⟩, m, hm,
    fun w v hv => (h w v hv).symm⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem HasBddSec.add (h : HasBddSec U x Z la) (h' : HasBddSec U x Z la') : HasBddSec U x Z (la + la') := by
  obtain ⟨s, m, hm, h⟩ := h
  obtain ⟨t, m', hm', h'⟩ := h'
  refine ⟨⟨s.sig * t.sig, s.inv * t.inv, exOf_add' la la' ▸ mul_mem_secZ s.sig_mem t.sig_mem,
    by rw [exOf_add', neg_add]; exact mul_mem_secZ s.inv_mem t.inv_mem, by rw [← mul_assoc, s.idem_sig],
    by rw [← mul_assoc, s.idem_inv], by rw [mul_mul_mul_comm, s.mul_inv, t.mul_inv, idem_mul_idem],
    s.cInf * t.cInf, fun σ => mul_pos (s.cInf_pos σ) (t.cInf_pos σ), fun σ => image_eq_singleton_iff.2
      ⟨(image_eq_singleton_iff.1 (s.norm_inf σ)).1, fun z hz => ?_⟩⟩, m * m', Nat.mul_pos hm hm', fun w v hv => ?_⟩
  · rw [wtOf_add', homN_mul _ x (even_wtOf _ _) (even_wtOf _ _) _ _ _ hz.1, homN_sig s hz, homN_sig t hz]; rfl
  · have hV := isVal_valOn hv
    constructor
    · show 0 ≤ v (_ • (s.sig * t.sig))
      rw [Nat.cast_mul, ← smul_mul_smul_comm, hV.mul]
      exact add_nonneg (h w v hv).1 (h' w v hv).1
    · show 0 ≤ v (_ • (s.inv * t.inv))
      rw [Nat.cast_mul, ← smul_mul_smul_comm, hV.mul]
      exact add_nonneg (h w v hv).2 (h' w v hv).2

theorem HasBddSec.zsmul (h : HasBddSec U x Z la) (n : ℤ) : HasBddSec U x Z (n • la) := by
  induction n using Int.induction_on with
  | zero => rw [zero_smul, ← add_neg_cancel la]; exact h.add h.neg
  | succ n ih => rw [add_smul, one_smul]; exact ih.add h
  | pred n ih => rw [sub_smul, one_smul, sub_eq_add_neg]; exact ih.add h.neg

end Powers

theorem exists_nat_vAdd {K : Type} [Field K] [NumberField K] {a : K} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ Formalism.BasicNotions.vAdd w ((n : K) * a) := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ K
  obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_integral_multiple
  have hn : IsIntegral ℤ ((y.natAbs : K) * a) := by
    rw [zsmul_eq_mul] at hy
    rcases Int.natAbs_eq y with e | e
    · rw [e, Int.cast_natCast] at hy; exact hy
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at hy; simpa using hy.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun w => ?_⟩
  exact Formalism.L2.Pj.vAdd_int_nonneg w (a := (⟨_, hn⟩ : 𝓞 K))
    (mul_ne_zero (Nat.cast_ne_zero.2 (Int.natAbs_pos.2 hy0).ne') ha)

end GlobalTheory.FlatDenom


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBimultiplicativeWeilPairingTorsionAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCommPairing

open GlobalTheory.CechPic

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  ext
  have := congrArg (fun u : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val) h
  simpa [unitOn] using this

theorem unitOn_surj {R : Type} [CommRing R] (c : (Γ(Sp R, ⊤))ˣ) : ∃ z : Rˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

theorem unitOn_mul {R : Type} [CommRing R] (a b : Rˣ) : unitOn (a * b) = unitOn a * unitOn b :=
  map_mul _ a b

theorem theta_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (k : ℕ)
    {T : Over S} (θ : Out.ThetaGrp B L (k : ℤ) T) :
    ∃ θ' : Out.ThetaGrp B (Hecke.lbPow L k) 1 T, θ'.pt = θ.pt := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  have hcls : cls _ hQ = k • cls L hL := by
    refine (cls_linComb hL (K := Fin k) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _ : (Out.thetaLB B L (k : ℤ) θ.pt).IsLB)).2 ⟨θ.φ, θ.isGen⟩
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB B (Hecke.lbPow L k) 1 θ.pt), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).1 ?_
    rw [cls_linComb hQ, Fin.sum_univ_two, hcls]
    rw [cls_linComb hL, Fin.sum_univ_two] at h0
    simp at h0 ⊢
    exact h0
  exact ⟨⟨_, u, hu⟩, rfl⟩

theorem exists_weilIs_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B) {L : LB B.left}
    (hL : L.IsLB) (k : ℕ) {T : Over S} {x y : T ⟶ B} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs B L (k : ℤ) x y c) :
    ∃ c' : Γ(T.left, ⊤)ˣ, Out.WeilIs B (Hecke.lbPow L k) 1 x y c' := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  refine CommutatorPairing.exists_weilIs GlobalTheory.globalFns_holds hB hQ (fun p => ?_) (fun p => ?_)
  · obtain ⟨V, hV, ⟨θx, -, hx, -⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θx
    exact ⟨V, hV, θ, hθ.trans hx⟩
  · obtain ⟨V, hV, ⟨-, θy, -, hy⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θy
    exact ⟨V, hV, θ, hθ.trans hy⟩

theorem lift_mul_lift {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]

theorem lift_pow {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x : T ⟶ A) (y : T ⟶ B) (m : ℕ) :
    lift x y ^ m = lift (x ^ m) (y ^ m) := by
  ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]

theorem lift_one_one {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] :
    (1 : T ⟶ A ⊗ B) = lift (1 : T ⟶ A) (1 : T ⟶ B) := by
  ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]

theorem exists_pairing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (c : ℕ), (c : κ) ≠ 0 → ∃ e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ, (∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') u ↔ u = unitOn (e g g')) ∧ (∀ g₁ g₂ g' : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧ (∀ g g₁ g₂ : Over.mk x ⟶ A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) := by
  intro S A _ _ P hA hP κ _ _ x c hc
  classical
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hQ : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => hc (by rw [h, Nat.cast_zero])
  have ex : ∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 →
      ∃ z : κˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn z) := by
    intro g g' hg hg'
    have hx : (lift g 1 : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg, one_pow, lift_one_one]
    have hy : (lift 1 g' : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg', one_pow, lift_one_one]
    obtain ⟨u, hu⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ x c hc0 hc _ _ hx hy
    obtain ⟨u', hu'⟩ := exists_weilIs_lbPow hAA hP c hu
    obtain ⟨z, rfl⟩ := unitOn_surj u'
    exact ⟨z, hu'⟩
  let e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ := fun g g' =>
    if h : g ^ c = 1 ∧ g' ^ c = 1 then (ex g g' h.1 h.2).choose else 1
  have he : ∀ g g' : Over.mk x ⟶ A, ∀ hg : g ^ c = 1, ∀ hg' : g' ^ c = 1,
      Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn (e g g')) := by
    intro g g' hg hg'
    simp only [e, dif_pos (And.intro hg hg')]
    exact (ex g g' hg hg').choose_spec
  have hmulc : ∀ g₁ g₂ : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → (g₁ * g₂) ^ c = 1 := by
    intro g₁ g₂ h₁ h₂
    rw [mul_pow, h₁, h₂, _root_.one_mul]
  refine ⟨e, fun g g' hg hg' u => ⟨fun h => CommutatorPairing.weilIs_unique hG hAA hQ h (he g g' hg hg'),
    fun h => h ▸ he g g' hg hg'⟩, ?_, ?_⟩
  · intro g₁ g₂ g' h₁ h₂ h'
    have hm := DiagPairing.weilIs_mul_left hG hAA hQ (he g₁ g' h₁ h') (he g₂ g' h₂ h')
    rw [lift_mul_lift, _root_.mul_one] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ (hmulc g₁ g₂ h₁ h₂) h') hm
  · intro g g₁ g₂ hg h₁ h₂
    have hm := CommPairing.weilIs_symm hQ (DiagPairing.weilIs_mul_left hG hAA hQ
      (CommPairing.weilIs_symm hQ (he g g₁ hg h₁)) (CommPairing.weilIs_symm hQ (he g g₂ hg h₂)))
    rw [lift_mul_lift, _root_.mul_one, mul_inv, inv_inv, inv_inv] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ hg (hmulc g₁ g₂ h₁ h₂)) hm

end GlobalTheory.TorsionCommPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem exists_isPer_of_quasiPeriodic : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ U, DifferentiableOn ℂ (k U) (pre u.ex U.1)) → (∀ U V : A.left.affineOpens, V ≤ U → IsReg u.ex V.1 (k V - k U)) → (∀ U a, IsReg u.ex U.1 fun z => fderiv ℂ (k U) z (Pi.single a 1)) → (∀ U (l : u.Λ), ∀ z ∈ pre u.ex U.1, k U (z + l) = k U z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  intro A _ g L u hA k q hk hreg hder hper
  obtain ⟨hopen, hdiff, -, -, -, hmono, -, -, hres, hev, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have hf : ∀ (U V : A.left.affineOpens) (_ : Opposite.op U ⟶ Opposite.op V), ∃ b : Sec (str A) V.1,
      ∀ z ∈ pre u.ex V.1, (k V - k U) z = val u.ex V.1 b z :=
    fun U V a => hreg U V (leOfHom a.unop)
  choose f hf using hf
  have hω : ∀ U : A.left.affineOpens, ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧
      ∀ z ∈ pre u.ex U.1, fderiv ℂ (k U) z = evForm u.ex U.1 z ξ :=
    fun U => GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised A g L u hA U (k U) (hk U) (hder U)
  choose ω hωc hωe using hω
  have hsub : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_sub e b b').trans (congrArg₂ (· - ·) (he b).symm (he b').symm))
  have hadd : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_add e b b').trans (congrArg₂ (· + ·) (he b).symm (he b').symm))
  have hfun : ∀ (U V W : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V) (ψ : Opposite.op V ⟶ Opposite.op W),
      f U W (φ ≫ ψ) = Sec.res (str A) (show W.1 ≤ V.1 from leOfHom ψ.unop) (f U V φ) + f V W ψ := by
    intro U V W φ ψ
    have hle : W.1 ≤ V.1 := leOfHom ψ.unop
    refine sub_eq_zero.1 (_root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA W.1
      (f U W (φ ≫ ψ) - (Sec.res (str A) hle (f U V φ) + f V W ψ) : Sec (str A) W.1) fun z hz => ?_)
    have e1 := hsub W.1 (f U W (φ ≫ ψ)) (Sec.res (str A) hle (f U V φ) + f V W ψ) z hz
    have e2 := hadd W.1 (Sec.res (str A) hle (f U V φ)) (f V W ψ) z hz
    have e3 := hres V.1 W.1 hle (f U V φ) z hz
    have e4 := hf U W (φ ≫ ψ) z hz
    have e5 := hf U V φ z (hmono _ _ hle hz)
    have e6 := hf V W ψ z hz
    simp only [Pi.sub_apply] at e4 e5 e6
    linear_combination e1 - e2 - e3 - e4 + e5 + e6
  have hform : ∀ (U V : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V),
      ω V = p1 (OAff (str A)) φ (ω U) + KaehlerDifferential.D ℂ (Sec (str A) V.1) (f U V φ) := by
    intro U V φ
    refine sub_eq_zero.1 (_root_.GlobalTheory.form_eq_zero_of_evForm_eq_zero A g L u hA V _ fun z hz => ?_)
    have hle : V.1 ≤ U.1 := leOfHom φ.unop
    have hz' : z ∈ pre u.ex U.1 := hmono _ _ hle hz
    have e1 := _root_.GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq A g L u U V φ (ω U) z hz
    have e2 := (_root_.GlobalTheory.CechPer.evForm_rules A g L u V.1 z hz).2.2 (f U V φ)
    have heq : k V =ᶠ[nhds z] k U + val u.ex V.1 (f U V φ) := by
      filter_upwards [(hopen _).mem_nhds hz] with w hw
      have := hf U V φ w hw
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply]
      linear_combination this
    have e3 : fderiv ℂ (k V) z = fderiv ℂ (k U) z + fderiv ℂ (val u.ex V.1 (f U V φ)) z :=
      heq.fderiv_eq.trans (fderiv_add ((hk _).differentiableAt ((hopen _).mem_nhds hz'))
        ((hdiff _ _).differentiableAt ((hopen _).mem_nhds hz)))
    refine (map_sub (evForm u.ex V.1 z) _ _).trans (sub_eq_zero.2 ?_)
    refine Eq.trans ?_ (map_add (evForm u.ex V.1 z) _ _).symm
    exact (hωe V z hz).symm.trans (e3.trans (congrArg₂ (· + ·) ((hωe U z hz').trans e1.symm) e2.symm))
  let c0 : Tot1 (OAff (str A)) := (fun U V a => f U.unop V.unop a, fun U => ω U.unop)
  have hc : c0 ∈ cechDeRhamTotalCocyclesOne (OAff (str A)) :=
    mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨fun T T' T'' φ ψ => hfun T.unop T'.unop T''.unop φ ψ, fun T T' φ => hform T.unop T'.unop φ,
      fun T => hωc T.unop⟩
  refine ⟨Hyp1.mk _ ⟨c0, hc⟩, ⟨c0, hc⟩, k, rfl, ⟨hk, fun U V a z hz => ?_, fun U z hz => hωe U z hz⟩, hper⟩
  have := hf U V a z hz
  simp only [Pi.sub_apply] at this
  change k V z = k U z + val u.ex V.1 (f U V a) z
  linear_combination this

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_even_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  intro R _ _ _ hR G _ _ hG P A gen hgen hL
  obtain ⟨R', _, _, _, ρ, hR', hρ, hall⟩ := _root_.GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat R hR G hG A gen hgen
  obtain ⟨G₁, _, _, β, β₂, P₁, A₁, gen₁, hG₁, hpb, hsq, hgen₁, hL₁, hLam₁⟩ :=
    _root_.GlobalTheory.Mum.exists_baseChange_semiAbelian_data R hR G hG P A gen hgen hL R' ρ hR' hρ
  obtain ⟨hsp, htw⟩ := hall G₁ β hpb
  obtain ⟨P₂, A₂, gen₂, hgen₂, hL₂, hLam₂, hev⟩ := _root_.GlobalTheory.Mum.exists_even_translate_split R' hR' G₁ hG₁ hsp htw P₁ A₁ gen₁ hgen₁ hL₁
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, G₁, inferInstance, inferInstance, β, β₂, P₂, A₂, gen₂,
    hR', hρ, hpb, hsq, hgen₂, hL₂, ?_, hev⟩
  exact LBIso.trans (LB.isLB_linComb P₂.L.isLB _ _) (LB.isLB_linComb P₁.L.isLB _ _)
    (pull_isLB (LB.isLB_linComb P.L.isLB _ _) _) hLam₂ hLam₁

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpreadStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ Z : Comp Xo c, ∃ t : TwSec U x Z (wtOf Dw 0 1), IntOff (badPrimes H l) t.hi ∧ ∀ w, t.hi w - t.lo w ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := by
  first | exact @GlobalTheory.KeyRootSpread.exists_twSec_keyRoot_spread | exact GlobalTheory.KeyRootSpread.exists_twSec_keyRoot_spread | (intros; apply GlobalTheory.KeyRootSpread.exists_twSec_keyRoot_spread <;> assumption)
end

