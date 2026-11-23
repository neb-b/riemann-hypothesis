module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigLineBundleKodairaLemma
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KodairaLemma

theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty (k : Type) [Field k] {Z : Scheme.{0}} [Algebra k Γ(Z, ⊤)] [IsEmpty Z]
    (L : LB Z) : lbH0 k L = 0 := by
  have e : (⊤ : Z.Opens) = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  have : Subsingleton Γ(Z, ⊤) := by rw [e]; infer_instance
  have : Subsingleton L.Sec := Module.subsingleton Γ(Z, ⊤) _
  have : Subsingleton (coh (twist (structureModule Z) L) 0) := (cohZeroTwistEquiv L).toEquiv.subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem isEmpty_zeroScheme {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) {L : LB X}
    (hL : L.IsLB) (t : L.Sec) (ht : genericPoint X ∈ nonzeroLocus t) :
    IsEmpty (GlobalTheory.ThickeningDetermines.secIdeal hL t).subscheme := by
  refine ⟨fun z => ?_⟩
  have hx : (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z ∈
      ((GlobalTheory.ThickeningDetermines.secIdeal hL t).support : Set X) := by
    rw [← (GlobalTheory.ThickeningDetermines.secIdeal hL t).range_subschemeι]; exact ⟨z, rfl⟩
  rw [coe_support_secIdeal] at hx
  set x := (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
    (show Order.krullDim (IrreducibleCloseds X) ≤ 0 from hd)
  have hst : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let A : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds X := ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
  have hBA : B ≤ A := hmax A hAB
  have hts : x ⤳ genericPoint X := specializes_iff_closure_subset.2 hBA
  exact hx (hts.mem_open (nonzeroLocus t).isOpen ht)

open GlobalTheory.ThickeningDetermines (secIdeal)
open GlobalTheory.QuotSep

theorem exists_nsmul_cls_eq_add_toPic_of_isBig : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsProjOver p → ∀ (M A : LB X) (hM : letI := algebraΓOfHom p; IsBig k M) (hA : IsAmpleLB A), ∃ (a : ℕ) (D : CartierDiv X), 0 < a ∧ D.Eff ∧ a • cls M (letI := algebraΓOfHom p; hM.isLB) = cls A hA.isLB + toPic D := by
  intro k _ _ X _ p hp M A hM hA
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have := isNoetherian_of_isProjOver hp'
  suffices h : ∃ a : ℕ, 0 < a ∧ ∃ (N : LB X) (hN : N.IsLB),
      cls N hN = a • cls M hM.isLB - cls A hA.isLB ∧ HasNonzeroSec N by
    obtain ⟨a, ha, N, hN, e, hs⟩ := h
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨a, divOfSec hN s hs, ha, GlobalTheory.PairStep.eff_divOfSec_of_sec hN s hs, ?_⟩
    rw [(presents_divOfRatSec hN (isRatSec_ratOfSec s hs)).toPic_eq, e]
    abel
  obtain ⟨q, hq, hq'⟩ := hA.exists_hasNonzeroSec (LB.isLB_triv X)
  have hAq : IsAmpleLB (lbPow A q) := (isAmpleLB_pow_iff hA.isLB hq).2 hA
  obtain ⟨r, -, hr'⟩ := hAq.exists_hasNonzeroSec (isLB_dual hA.isLB)
  have hP : (lbPow (lbPow A q) r).IsLB := isLB_lbPow hAq.isLB r
  have hPs : HasNonzeroSec (lbPow (lbPow A q) r) :=
    (hq' _ hAq.isLB (by rw [cls_triv, zero_add, cls_lbPow hA.isLB])).pow hAq.isLB r
  have hE := isLB_tens (isLB_dual hA.isLB) hP
  have hEs : HasNonzeroSec (tens (dual A) (lbPow (lbPow A q) r)) :=
    hr' _ hE (by rw [cls_tens (isLB_dual hA.isLB) hP, cls_lbPow hAq.isLB])
  obtain ⟨t, ht⟩ := hasNonzeroSec_iff.1 hPs
  have ht0 : t ≠ 0 := sec_ne_zero_of_mem ht
  letI := algebraΓAlong k (secIdeal hP t).subschemeι
  obtain ⟨m, hm, hlt⟩ : ∃ m : ℕ, 0 < m ∧
      lbH0 k ((lbPow M m).pull (secIdeal hP t).subschemeι) < lbH0 k (lbPow M m) := by
    obtain ⟨D, hD, c, hc, hfreq⟩ := hM.growth
    rcases D with _ | d
    · have hd0 : topologicalKrullDim X ≤ 0 := by rw [hD]; rfl
      haveI := isEmpty_zeroScheme hd0 hP t ht
      obtain ⟨m, hcm, hm⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
      refine ⟨m, hm, ?_⟩
      rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]
      have h0 : (0 : ℝ) < lbH0 k (lbPow M m) := hc.trans_le (by simpa using hcm)
      exact_mod_cast h0
    · set ι := (secIdeal hP t).subschemeι
      have hMι := LB.isLB_pull hM.isLB ι
      obtain ⟨C, hC⟩ := GlobalTheory.exists_hdim_twist_lbPow_zero_le k _ (isProjOver_along hp' ι) d (M.pull ι) hMι
        (structureModule _) (by rw [QCoh.suppDim_structureModule]; exact dim_zeroScheme_le hP ht0 hD.le)
      have hev : ∀ᶠ m : ℕ in atTop, (C : ℝ) * 2 ^ d < c * m :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc).eventually_gt_atTop _
      obtain ⟨m, h₁, h₂, h₃⟩ := (hfreq.and_eventually (hev.and (eventually_ge_atTop 1))).exists
      refine ⟨m, h₃, ?_⟩
      have e₂ : lbH0 k ((lbPow M m).pull ι) = lbH0 k (lbPow (M.pull ι) m) :=
        lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull (isLB_lbPow hM.isLB m) ι) (isLB_lbPow hMι m)
          ((cls_eq_iff _ _).2 (lbIso_lbPow_pull hM.isLB ι m)).symm
      rw [e₂]
      by_contra hle
      push_neg at hle
      have hb : (lbH0 k (lbPow (M.pull ι) m) : ℝ) ≤ C * ((m : ℝ) + 1) ^ d := by exact_mod_cast hC m
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h₃
      have hm2 : ((m : ℝ) + 1) ^ d ≤ 2 ^ d * (m : ℝ) ^ d := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
      have hle' : (lbH0 k (lbPow M m) : ℝ) ≤ lbH0 k (lbPow (M.pull ι) m) := by exact_mod_cast hle
      have hmd : (0 : ℝ) < (m : ℝ) ^ d := pow_pos (by linarith) d
      have h₄ := mul_lt_mul_of_pos_right h₂ hmd
      have h₅ := mul_le_mul_of_nonneg_left hm2 (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
      push_cast at h₁
      rw [pow_succ] at h₁
      nlinarith
  have hB := isLB_lbPow hM.isLB m
  have e₁ := globalSections_dim_le_div_add_restriction hp' hP hB ht0
  have hpos : 0 < lbH0 k (LB.div (lbPow M m) (lbPow (lbPow A q) r)) := by omega
  have hD := LB.isLB_div hB hP
  refine ⟨m, hm, _, isLB_tens hD hE, ?_, (lineBundleHasNonzeroSection_of_globalSectionsDim_pos hpos).tens hEs hD hE⟩
  rw [cls_tens hD hE, cls_div hB hP, cls_lbPow hM.isLB, cls_tens (isLB_dual hA.isLB) hP,
    cls_dual hA.isLB, cls_lbPow hAq.isLB, cls_lbPow hA.isLB]
  abel

end GlobalTheory.KodairaLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlowupChartIdealSheafEqSpanMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SgZero

theorem exists_nat_evalZ (φ : InvFun ℤ) (g : ℕ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ)
    (δ ga : Fin m → LinearMap.BilinForm ℤ X) (M d : ℕ) (hpf : IsPolFan id g φ) (hrk : Module.finrank ℤ X ≤ g)
    (hc : IsCone id φ ga) (hδ : ∀ k, δ k = (M : ℤ) • ga k) : ∃ b : Fin m → ℕ, ∀ k, (b k : ℝ) = d * φ.evalZ (δ k) := by
  have hP := hpf X hrk
  have key : ∀ k, ∃ n : ℕ, φ.evalZ (ga k) = n := by
    intro k
    obtain ⟨z, hz⟩ := hP.integral (ga k) (hc.mem k) (hc.nonneg k)
    by_cases h0 : ga k = 0
    · refine ⟨0, ?_⟩
      have := hc.evalZ_smul 0 k
      simp only [Nat.cast_zero, zero_smul, zero_mul] at this
      rw [h0]; simpa [h0] using this
    · have hp := hP.pos (ga k) (hc.mem k) (hc.nonneg k) h0
      refine ⟨z.toNat, ?_⟩
      rw [hz] at hp ⊢
      have : (0 : ℤ) ≤ z := by exact_mod_cast hp.le
      rw [show ((z.toNat : ℕ) : ℝ) = ((z.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg this]
  choose n hn using key
  refine ⟨fun k => d * (M * n k), fun k => ?_⟩
  rw [hδ, hc.evalZ_smul, hn]
  push_cast; ring

theorem dvd_of_map_dvd_of_finite (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    (ρ : A →+* B) (hρ : Function.Injective ρ) (hf : ρ.Finite) (a c : A) (ha : a ≠ 0) (h : ρ a ∣ ρ c) : a ∣ c := by

  letI : Algebra A B := ρ.toAlgebra
  haveI : Module.Finite A B := hf
  obtain ⟨x, hx⟩ := h
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) x
  let K := FractionRing A
  let L := FractionRing B
  let gL : A →+* L := (algebraMap B L).comp ρ
  have hgL : Function.Injective gL := (IsFractionRing.injective B L).comp hρ
  let iK : K →+* L := IsFractionRing.lift hgL
  have hιK : ∀ r : A, iK (algebraMap A K r) = gL r := IsFractionRing.lift_algebraMap hgL
  have hA : algebraMap A K a ≠ 0 := fun e => ha (IsFractionRing.injective A K (e.trans (map_zero _).symm))
  have hρa : algebraMap B L (ρ a) ≠ 0 := fun e => hA (by
    have := hgL (show gL a = gL 0 by simpa [gL] using e)
    rw [this, map_zero])
  set y : K := algebraMap A K c / algebraMap A K a with hy
  have hιKy : iK y = algebraMap B L x := by
    rw [hy, map_div₀, hιK, hιK]
    simp only [gL, RingHom.comp_apply, hx, map_mul]
    exact mul_div_cancel_left₀ _ hρa
  have hint : IsIntegral A y := by
    refine ⟨p, hpm, ?_⟩
    apply iK.injective
    rw [map_zero, Polynomial.hom_eval₂, hιKy]
    have e1 : iK.comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) := by
      ext r; exact hιK r
    rw [e1, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hint
  refine ⟨z, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hz, hy, mul_div_cancel₀ _ hA]

theorem idlAlong_eq_span_monomial : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∃ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) ∧ idlAlong (J.comap π) ξ = Ideal.span {∏ k, t k ^ b k} := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W φ d J S π j hJ hval hbl hji hpf V _ _ _ Q m t δ hrk ht hsym hnn hdef
    hmono ga M hcone hδ ξ hU
  obtain ⟨b, hb⟩ := exists_nat_evalZ φ g Q.X m δ ga M d hpf hrk hcone hδ
  refine ⟨b, hb, ?_⟩
  have hCN : IsCN V := hU.1
  obtain ⟨R', _, _, _, ρ, r, D, e, hCN', hρi, hρf, hρl, hr, hrefn, hmon⟩ :=
    _root_.GlobalTheory.PolDeg.refine_monomial_of_polarised V Q m t δ hCN hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hdef
  obtain ⟨g₀, hg₀⟩ := _root_.GlobalTheory.NormBlPrincipal.idlAlong_comap_principal π J hbl V ξ
  rw [hg₀]
  have key : ∀ (Wr : Type) [CommRing Wr] [IsDomain Wr] [IsDiscreteValuationRing Wr], IsAdicComplete (maximalIdeal Wr) Wr →
      ∀ κ : R' →+* Wr, Function.Injective κ → IsLocalHom κ →
        Ideal.span {κ (ρ g₀)} = Ideal.span {κ (ρ (∏ k, t k ^ b k))} := by
    intro Wr _ _ _ hc κ hκi hκl
    obtain ⟨T, σ, c, e', hσ, hy, hc', hβ⟩ := _root_.GlobalTheory.Poinc.ChartTraitForm.exists_trait F S j V Q ξ hU m t δ R' ρ r D e hCN' hρi hρf hρl hr
      (fun k => (ht k).2) hsym hrefn hmon Wr hc κ hκi hκl
    have hy' : jK T.V ≫ spMap σ ≫ (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = T.y ≫ i := by
      rw [← hji]
      simpa only [Category.assoc] using congrArg (· ≫ π) hy
    have h1 := _root_.GlobalTheory.Poinc.Arith.idlAlong_monomial F Z i φ J d hval Q.X m ga δ M hcone hδ b hb T Wr σ c e' (spMap κ ≫ spMap ρ ≫ ξ ≫ π)
      (fun k => κ (ρ (t k))) hσ hy' hc' hβ
    have h2 : idlAlong J (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = Ideal.span {κ (ρ g₀)} := by
      rw [GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp, ← GlobalTheory.PullAlong.idlAlong_comap_eq, hg₀,
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rw [← h2, h1, map_prod, map_prod]
    simp only [map_pow]
  obtain ⟨hN', hI', -, hZ'⟩ := hCN'
  obtain ⟨-, hIV, -, -⟩ := hCN
  set f := ∏ k, t k ^ b k with hfdef
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k).2
  have hρf0 : ρ f ≠ 0 := fun h => hf0 (hρi (h.trans (map_zero ρ).symm))
  have hκ0 : ∀ (Wr : Type) [CommRing Wr] (κ : R' →+* Wr), Function.Injective κ → κ (ρ f) ≠ 0 :=
    fun Wr _ κ hκ h => hρf0 (hκ (h.trans (map_zero κ).symm))
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨Wr, _, _, _, κ, ⟨hdvr, hc, -⟩, hκi, hcm⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
    have hκl : IsLocalHom κ := ⟨fun a ha => by
      by_contra hna
      have : a ∈ (maximalIdeal Wr).comap κ := by rw [hcm]; exact hna
      exact (mem_maximalIdeal _).1 this ha⟩
    have := key Wr hc κ hκi hκl
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hκ0 Wr κ hκi this
  have hρg0 : ρ g₀ ≠ 0 := fun h => hg0 (hρi (h.trans (map_zero ρ).symm))
  have d1 : ρ f ∣ ρ g₀ := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ g₀) (ρ f) hρf0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).symm.dvd
  have d2 : ρ g₀ ∣ ρ f := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ f) (ρ g₀) hρg0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).dvd
  exact Ideal.span_singleton_eq_span_singleton.2
    (associated_of_dvd_dvd (dvd_of_map_dvd_of_finite V R' ρ hρi hρf g₀ f hg0 d2) (dvd_of_map_dvd_of_finite V R' ρ hρi hρf f g₀ hf0 d1))

end GlobalTheory.SgZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplitStatement
section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  intro K _ A _ hA L hL T x y m n a b
  have : IsCommMonObj A := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have lam_zpow_left (x z : T ⟶ A) (n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ n) z =
        n • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x z := by
    open GlobalTheory.CechPic in
    cases n with
    | ofNat k =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
      exact lam_pow_left hL hΘ x z k
    | negSucc k =>
      have h := lam_mul_left hL hΘ (x ^ (k + 1)) (x ^ (k + 1))⁻¹ z
      rw [mul_inv_cancel, lam_one_left, lam_pow_left hL hΘ] at h
      rw [zpow_negSucc, negSucc_zsmul]
      exact eq_neg_of_add_eq_zero_right h.symm
  have lam_zpow_zpow (x y : T ⟶ A) (m n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ m) (y ^ n) =
        (m * n) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
    rw [lam_zpow_left, GlobalTheory.CechPic.lam_comm, lam_zpow_left,
      GlobalTheory.CechPic.lam_comm, smul_smul]
  have pull_one_eq_zero (c : GlobalTheory.CechPic.Pic A.left) :
      GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 := by
    change GlobalTheory.CechPic.pull ((toUnit T).left ≫ (η : 𝟙_ (Over (Sp K)) ⟶ A).left) c = 0
    rw [GlobalTheory.CechPic.pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) _ c, map_zero]
  have key : ∀ (c : GlobalTheory.CechPic.Pic A.left) (u v : T ⟶ A),
      GlobalTheory.CechPic.pull (u * v).left c = GlobalTheory.CechPic.pull u.left c +
        GlobalTheory.CechPic.pull v.left c + GlobalTheory.CechPic.lam c u v := by
    intro c u v
    unfold GlobalTheory.CechPic.lam
    rw [pull_one_eq_zero]
    abel
  rw [mul_inv, key, key, ← zpow_neg, ← zpow_neg, lam_zpow_zpow, lam_zpow_zpow, neg_mul_neg]
  module
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeight
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.PDivGroup.DimSum

theorem baseChange_bijective_of_ker {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (k : Type) [CommRing k] [Algebra O k] (a : O)
    (ha : algebraMap O k a = 0) (f : M →ₗ[O] N) (hf : Function.Surjective f)
    (hfa : ∀ v, f (a • v) = 0) (hk : ∀ w, f w = 0 → ∃ v, w = a • v) :
    Function.Bijective (f.baseChange k) := by
  rw [LinearMap.baseChange_eq_ltensor]
  refine ⟨?_, LinearMap.lTensor_surjective k hf⟩
  have hex : Function.Exact (a • LinearMap.id : M →ₗ[O] M) f := by
    intro w
    constructor
    · intro hw
      obtain ⟨v, rfl⟩ := hk w hw
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact hfa v
  have hex' := lTensor_exact k hex hf
  have hz : LinearMap.lTensor k (a • LinearMap.id : M →ₗ[O] M) = 0 := by
    refine TensorProduct.ext' fun c m => ?_
    rw [LinearMap.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, ha, zero_mul, TensorProduct.zero_tmul, LinearMap.zero_apply]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex' x).1 hx
  rw [hz, LinearMap.zero_apply]

open GlobalTheory.PDiv Module

theorem finrank_cot_baseChange_one {p : ℕ} {O : Type} [CommRing O] (H : PDivGroup p O) (k : Type)
    [Field k] [Algebra O k] (hp : algebraMap O k p = 0) :
    finrank k (Cot k (k ⊗[O] H.A 1)) = finrank k (k ⊗[O] H.omega) := by
  have h1 : Function.Bijective ((H.omegaLevel 1).baseChange k) :=
    baseChange_bijective_of_ker k (p : O) hp (H.omegaLevel 1) (H.omegaLevel_surjective 1)
      (fun v => by
        have := H.pow_smul_cot 1 (v.1 1)
        rw [pow_one] at this
        exact this)
      (fun w hw => by
        obtain ⟨v, hv⟩ := (H.omega_val_eq_zero_iff 1 w).1 hw
        exact ⟨v, by rw [hv, pow_one]⟩)
  let e1 := LinearEquiv.ofBijective _ h1
  let e2 := LinearEquiv.ofBijective _ (liftSemi_toBaseChange_cot_bijective O k (H.A 1))
  exact (e1.trans e2).finrank_eq.symm

theorem finrank_cot_congr {k X Y : Type} [Field k] [CommRing X] [CommRing Y] [Bialgebra k X]
    [Bialgebra k Y] (e : X ≃ₐc[k] Y) : finrank k (Cot k X) = finrank k (Cot k Y) := by
  have h1 : (e.symm : Y →ₐc[k] X).comp (e : X →ₐc[k] Y) = BialgHom.id k X :=
    BialgHom.ext fun x => e.symm_apply_apply x
  have h2 : (e : X →ₐc[k] Y).comp (e.symm : Y →ₐc[k] X) = BialgHom.id k Y :=
    BialgHom.ext fun x => e.apply_symm_apply x
  refine (LinearEquiv.ofLinear (cotMap (e : X →ₐc[k] Y)) (cotMap (e.symm : Y →ₐc[k] X)) ?_ ?_).finrank_eq
  · rw [← cotMap_comp, h2, cotMap_id]
  · rw [← cotMap_comp, h1, cotMap_id]

end GlobalTheory.PDivGroup.DimSum


open Module PDiv in
theorem GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
      d + Module.finrank O G.dual.Lie = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let k := IsLocalRing.ResidueField O
  have hpk : algebraMap O k p = 0 := by
    change IsLocalRing.residue O p = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Fact.out : ¬IsUnit (p : O))
  have hpk' : ((p : ℕ) : k) = 0 := by rw [← map_natCast (algebraMap O k), hpk]
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let eG : (Fin d → O) ≃ₗ[O] G.omega := LinearEquiv.ofBijective _ hbij
  haveI : Module.Free O G.omega := Module.Free.of_equiv eG
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  have hd : finrank O G.omega = d := by rw [← eG.finrank_eq, Module.finrank_fin_fun]
  have hLie : finrank O G.dual.Lie = finrank O G.dual.omega := by
    let b := Module.Free.chooseBasis O G.dual.omega
    rw [finrank_eq_card_basis b.dualBasis, finrank_eq_card_basis b]
  obtain ⟨-, -, -, hsum⟩ := finrank_rigExt_omega p k hpk' (G.baseChange k)
  have hA : finrank k (G.baseChange k).omega = finrank O G.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).omegaLevel_one_bijective hpk')).finrank_eq]
    exact (DimSum.finrank_cot_baseChange_one G k hpk).trans (Module.finrank_baseChange)
  have hB : finrank k (G.baseChange k).dual.omega = finrank O G.dual.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).dual.omegaLevel_one_bijective hpk')).finrank_eq]
    refine (DimSum.finrank_cot_congr (CartierDual.baseChange O k (G.A 1))).symm.trans ?_
    exact (DimSum.finrank_cot_baseChange_one G.dual k hpk).trans (Module.finrank_baseChange)
  rw [hLie, ← hd, ← hA, ← hB]
  exact hsum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionOfGenerated
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem chernInt_eq_topSelf_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ n u hu
  have hL : L.IsLB := φ.isLB
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.GenCut.exists_generating_sections_of_dim_le ℂ Y.X Y.str L hL Y.dim (Var.topologicalKrullDim_eq Y).le n u hu
  have hπ : ProjSpace.toProj Y.str s hs ≫ PSpace.str ℂ Y.dim = Y.str := ProjSpace.toProj_str Y.str s hs
  have e := GlobalTheory.ProjSpace.lbIso_pull_O1_toProj_of_isLB ℂ Y.dim Y.X L hL Y.str s hs
  have h1 := _root_.GlobalTheory.chernInt_indep_of_iso Y _ L (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull _ hπ) φ e
    (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)).pull _ hπ) hφ
  rw [← h1, _root_.GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree Y _ hπ,
    topSelf_congr ℂ (LB.isLB_pull (ProjSpace.O1_isLB ℂ Y.dim) (ProjSpace.toProj Y.str s hs)) hL e]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiffStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, dbarAt (fun x => transAt G G' x k) v = (powAt G v k : Alt n) - powAt G' v k := by
  first | exact @GlobalTheory.ChernCalc.dbarAt_transAt | exact GlobalTheory.ChernCalc.dbarAt_transAt | (intros; apply GlobalTheory.ChernCalc.dbarAt_transAt <;> assumption)
end

