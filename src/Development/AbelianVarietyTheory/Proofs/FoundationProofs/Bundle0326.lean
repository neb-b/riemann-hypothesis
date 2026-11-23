module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmNormalizedThetaJetsIntegral
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaJets

theorem jetsPh_all : ∀ D : D7, GL3Theta.jetsPh D := fun D =>
  Formalism.MainNotions.Ext.CutA.jetsPh_of' Formalism.MainNotions.Ext.CutA.jetsHigh_holds Formalism.MainNotions.Ext.CutA.jetsOne_holds
    Formalism.MainNotions.Ext.CutA.jetsTwo_holds D (_root_.GlobalTheory.ThetaCube.cube_addInt_beBiadd D).1 (_root_.GlobalTheory.CMEndo.endo_all D).2.1 (_root_.GlobalTheory.CMEndo.endo_all D).2.2

end GlobalTheory.ThetaJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaValuesVanishAtOddSplitPrime
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSplit

theorem exists_sqrt_padic {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) {a : ℤ} (h : jacobiSym a p = 1) :
    ∃ z : ℤ_[p], z ^ 2 = (a : ℤ_[p]) ∧ IsUnit (2 * z) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have ha : (a : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p a).2 h0] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p ha).1 h
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  have hr0 : (r : ZMod p) ≠ 0 := fun h0 => ha (by rw [hr, h0, mul_zero])
  have h20 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have : p ∣ 2 := by exact_mod_cast hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hn : ‖((2 * r : ℤ) : ℤ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hlt
    push_cast at hlt h20
    exact mul_ne_zero h20 hr0 hlt
  have hlt : ‖((r ^ 2 - a : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hr]; ring
  have e1 : ∀ z : ℤ_[p], Polynomial.aeval z (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ) = z ^ 2 - a := by
    intro z; simp
  have e2 : ∀ z : ℤ_[p], Polynomial.aeval z
      (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ)) = 2 * z := by
    intro z; simp [map_ofNat]
  obtain ⟨z, hz, -, hz', -⟩ := hensels_lemma (p := p) (F := (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ))
    (a := (r : ℤ_[p])) (by
      rw [e1, e2]
      push_cast at hn hlt
      rw [hn]; simpa using hlt)
  rw [e1] at hz
  rw [e2, e2] at hz'
  push_cast at hn
  exact ⟨z, sub_eq_zero.1 hz, PadicInt.isUnit_iff.2 (hz'.trans hn)⟩

theorem exists_emb (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    ∃ ψ : D.host.E →+* ℂ_[p], ∀ x, lamC lam (D.host.φ₀ x) = ψ x := by
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  refine ⟨lam.comp (D.host.φ₀.codRestrict Qbar hm), fun x => ?_⟩
  simp only [lamC, dif_pos (hm x)]
  rfl

theorem exists_sqrt_host (D : D7) : ∃ b : 𝓞 D.host.K, ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E) ∧
    D.host.conj ((b : D.host.K) : D.host.E) = -((b : D.host.K) : D.host.E) := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hK : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hi : IsIntegral ℤ (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) := by
    refine IsIntegral.of_pow two_pos ?_
    have : (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) ^ 2 = algebraMap ℤ D.host.K (-(D.host.d : ℤ)) := by
      apply Subtype.ext
      simpa using hb
    rw [this]; exact isIntegral_algebraMap
  exact ⟨⟨_, hi⟩, hb, D.host.conj_sqd⟩

theorem idem_mem (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (h2 : p ≠ 2)
    (hs : GL3Theta.SplitK D p) : ((1, 0) : ℂ_[p] × ℂ_[p]) ∈ GL3Theta.OKp D lam := by
  obtain ⟨ψ, hψ⟩ := exists_emb D lam
  obtain ⟨b, hb, hc⟩ := exists_sqrt_host D
  let ι : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hι : Continuous ι := (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val
  set s := ψ ((b : D.host.K) : D.host.E) with hsdef
  have hs2 : s ^ 2 = -(D.host.d : ℂ_[p]) := by rw [hsdef, ← map_pow, hb]; simp
  obtain ⟨z, hz, hu⟩ : ∃ z : ℤ_[p], ι z = s ∧ IsUnit (2 * z) := by
    obtain ⟨z, hz, hu⟩ := exists_sqrt_padic h2 hs
    have : ι z ^ 2 = s ^ 2 := by rw [← map_pow, hz, hs2]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · exact ⟨z, h, hu⟩
    · exact ⟨-z, by rw [map_neg, h, neg_neg], by simpa using hu.neg⟩
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  let f : ℤ_[p] × ℤ_[p] → ℂ_[p] × ℂ_[p] := fun x => (ι x.1 + ι x.2 * s, ι x.1 - ι x.2 * s)
  have hf : Continuous f := by fun_prop
  have hd : DenseRange (Prod.map (Int.cast : ℤ → ℤ_[p]) (Int.cast : ℤ → ℤ_[p])) :=
    PadicInt.denseRange_intCast.prodMap PadicInt.denseRange_intCast
  have hw' : 2 * s * ι w = 1 := by
    have := congrArg ι hw
    rwa [map_mul, map_mul, map_ofNat, hz, map_one] at this
  have h1 : f (z * w, w) = (1, 0) := by
    simp only [f, map_mul, hz]
    ext
    · linear_combination hw'
    · simp only; ring
  rw [← h1]
  refine map_mem_closure hf (hd (z * w, w)) ?_
  rintro _ ⟨⟨m, n⟩, rfl⟩
  refine ⟨(m : 𝓞 D.host.K) + n * b, ?_⟩
  simp only [GL3Theta.tauK, GL3Theta.tauKc, hψ, f, Prod.map]
  simp [hc, hsdef, sub_eq_add_neg]

section Series
variable {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem const_ph : PowerSeries.constantCoeff g.ph = 0 := by
  simp only [GL3Theta.G1.ph, map_neg, neg_eq_zero]
  show GL3Theta.logMv _ 0 = 0
  simp [GL3Theta.logMv]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem be_zero (h : g.Ok) (i : σ) : g.be (GL3Theta.Xv i) 0 = 0 := by
  have h1 : g.lg (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_l g)
  have h2 : g.phAt (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_ph g)
  rw [GL3Theta.G1.be, GL3Theta.G1.add, h1, add_zero, pt_lg g h (MvPowerSeries.constantCoeff_X i), h2]
  simp

end Series

theorem splitZero : ∀ D : D7, GL3Theta.splitZero D := by
  intro D p _ cc δ g hg h2 hs
  obtain ⟨-, hN, hC⟩ := _root_.GlobalTheory.CMEndo.endo_all D
  have hα := idem_mem D g.lam h2 hs
  have hok : g.Ok := hg.2.2.2.2
  have h1 := hC p cc δ g hg h2 _ hα
  have h3 := hN p cc δ g hg h2 _ hα
  simp only [mulBy_one g hok, mulBy_zero g hok, be_zero g hok, mul_zero, map_zero, zero_mul] at h1 h3
  exact ⟨h1, h3⟩

end GlobalTheory.ThetaSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToK
section
noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4.TopEta

open GlobalTheory.KZ GlobalTheory.NeedB GlobalTheory.KEdge

section General

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def toK : geo F K Ω →* (Ω ≃ₐ[K] Ω) :=
  MonoidHom.mk' (fun g => { (g : Ω ≃ₐ[F] Ω).toRingEquiv with commutes' := (TopW.mem_geo _).1 g.2 })
    (fun _ _ => AlgEquiv.ext fun _ => rfl)

theorem continuous_toK [Algebra.IsAlgebraic F Ω] : Continuous (toK : geo F K Ω →* (Ω ≃ₐ[K] Ω)) := by
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hsub⟩ := hs
  let b := Module.finBasis K E
  have hop : IsOpen (⋂ i, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) (b i : Ω) : Set (Ω ≃ₐ[F] Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := F) (b i : Ω)
  refine Filter.mem_map.2 (Filter.mem_of_superset ((hop.preimage continuous_subtype_val).mem_nhds ?_) ?_)
  · simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    exact fun i => Subgroup.one_mem _
  · intro g hg
    simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hg
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hlin : (((toK g).toLinearMap).comp E.val.toLinearMap) = E.val.toLinearMap :=
      b.ext fun i => hg i
    exact LinearMap.congr_fun hlin ⟨z, hz⟩

theorem exists_extend [Algebra.IsAlgebraic F Ω] {N : ℕ} {ζ α β : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)}
    (hx : ∀ g, (x g).toAdd = kum (K := F) (N := N) ζ α g) (hy : ∀ g, (y g).toAdd = kum (K := F) (N := N) ζ β g)
    (R : Subring K) (η : (Ω ≃ₐ[K] Ω) → ZMod N) (h1 : IsLocallyConstant η)
    (h2 : ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g)
    (h3 : ∀ B : ValuationSubring Ω, Over R B → ∀ g, Inert B g → η g = 0) :
    ∃ η' : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η' ∧ IsLocallyConstant (fun g : geo F K Ω => η' g) ∧
      ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over R B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η' g = 0 := by
  classical
  refine ⟨fun g => if h : g ∈ geo F K Ω then η (toK ⟨g, h⟩) else 0, fun g hg h hh => ?_, ?_, fun B g hB hi hg => ?_⟩
  · simp only [dif_pos hg, dif_pos hh, dif_pos (mul_mem hg hh)]
    rw [hx, hy]
    have e : toK (⟨g * h, mul_mem hg hh⟩ : geo F K Ω) = toK ⟨g, hg⟩ * toK ⟨h, hh⟩ := map_mul toK ⟨g, hg⟩ ⟨h, hh⟩
    rw [e]
    exact h2 (toK ⟨g, hg⟩) (toK ⟨h, hh⟩)
  · have e : (fun g : geo F K Ω => if h : (g : Ω ≃ₐ[F] Ω) ∈ geo F K Ω then η (toK ⟨(g : Ω ≃ₐ[F] Ω), h⟩) else 0) = η ∘ toK :=
      funext fun g => by rw [dif_pos g.2]; rfl
    rw [e]
    exact h1.comp_continuous continuous_toK
  · simp only [dif_pos hg]
    exact h3 B hB _ hi

end General

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem fixMu_eq {M : ℕ} (hM : M ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) :
    fixMu Ω M = (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup := by
  haveI : NeZero M := ⟨hM⟩
  unfold fixMu
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.subset_adjoin ℚ {ζ} rfl) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

attribute [local instance] algMdl

theorem normal_top [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) : Normal (topF X M) (topL X M) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have h := LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) (isPrimitiveRoot_eOm ε hM) le_rfl
  rw [← fixMu_eq hM (isPrimitiveRoot_eOm ε hM)] at h
  exact h

theorem over_iff (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M)) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    Over (FunctionField.ringOfIntegers Ω (topL X M)).toSubring B ↔
      ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) →
        algebraMap (topL X M) (topBar X M) f ∈ B := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  constructor
  · intro h f hf
    apply h
    have : ∃ P : Polynomial Ω, algebraMap (Polynomial Ω) (topL X M) P = f := by
      rcases hf with hf | ⟨c, hc⟩
      · exact ⟨Polynomial.X, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_X, hf]))⟩
      · exact ⟨C c, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_C, hc]))⟩
    obtain ⟨P, rfl⟩ := this
    exact Subalgebra.algebraMap_mem _ P
  · intro h f hf
    have hP : ∀ P : Polynomial Ω,
        ((algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M))) P ∈ B := by
      intro P
      induction P using Polynomial.induction_on with
      | C c => exact h _ (Or.inr ⟨c, ((coe_jPoly X _ _).trans (by rw [aeval_C])).symm⟩)
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | monomial k c hk =>
        rw [pow_succ, ← mul_assoc, map_mul]
        exact mul_mem hk (h _ (Or.inl ((coe_jPoly X _ _).trans (by rw [aeval_X]))))
    obtain ⟨q, hq, h0⟩ : IsIntegral (Polynomial Ω) f := hf
    let φ : Polynomial Ω →+* B := RingHom.codRestrict _ B hP
    have hi : IsIntegral B (algebraMap (topL X M) (topBar X M) f) := by
      refine ⟨q.map φ, hq.map φ, ?_⟩
      rw [eval₂_map]
      have := congrArg (algebraMap (topL X M) (topBar X M)) h0
      rw [hom_eval₂, map_zero] at this
      exact this
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hy]
    exact y.2

theorem spec_of_units [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M l n : ℕ} (hM : M ≠ 0) (hl : l ≠ 0) (hlM : l ^ n ∣ M) {u v : X.K}
    (hu : TopUnits.IsTopUnit X M u) (hv : TopUnits.IsTopUnit X M v) :
    (∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η) ∧
      ∀ φ : topGal X M, IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) φ
        (topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
          (topEta X M (topChar X M l n u) (topChar X M l n v)) φ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero Ω := algebraRat.charZero Ω
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  letI := algRat X (CongruenceSubgroup.Gamma M)
  haveI := isScalarTower_poly_rat X (CongruenceSubgroup.Gamma M)
  haveI : FiniteDimensional (RatFunc Ω) (topL X M) := GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X _ M (Nat.pos_of_ne_zero hM) le_rfl
  haveI := normal_top X hM
  haveI : Algebra.IsAlgebraic (topF X M) (topBar X M) := Algebra.IsAlgebraic.trans _ (topL X M) _
  obtain ⟨hu0, huF, huL, hu1, hu2⟩ := hu
  obtain ⟨hv0, hvF, hvL, hv1, hv2⟩ := hv
  have hN : 0 < l ^ n := Nat.pos_of_ne_zero (pow_ne_zero n hl)
  have hζ := isPrimitiveRoot_topZeta X M hl n
  have hα := topRoot_pow X M hN.ne' huL
  have hβ := topRoot_pow X M hN.ne' hvL
  have hx := topChar_apply X hl hlM huF hu0
  have hy := topChar_apply X hl hlM hvF hv0
  have ha : ∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η := by
    obtain ⟨-, -, -, -, η, h1, h2, h3⟩ := _root_.GlobalTheory.KummerCob.thmA Ω (topL X M) (topBar X M) (l ^ n) _ hN hζ ⟨u, huL⟩ ⟨v, hvL⟩ _ _
      (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 hα hβ
    obtain ⟨η', g1, g2, g3⟩ := exists_extend hx hy _ η h1 h2 h3
    exact ⟨η', g1, g2, fun B g hB => g3 B g ((over_iff X M B).2 hB)⟩
  refine ⟨ha, fun φ => ?_⟩
  obtain ⟨g1, g2, g3⟩ := isTopEta_topEta X M ha
  refine isTopW_topW Ω (topL X M) (topBar X M) (topF X M) (l ^ n) _ hN hζ (topGal_topZeta X hl hlM)
    (map_mem_ringOfIntegers_of_fix_mdl Ω ε X _ _) ⟨u, huF⟩ ⟨v, hvF⟩ (topRoot X M (l ^ n) u) (topRoot X M (l ^ n) v)
    (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 ?_ ?_ _ _ hx hy _ g1 g2
    (fun B g hB => g3 B g ((over_iff X M B).1 hB)) φ
  · rw [hα, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl
  · rw [hβ, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl

end GlobalTheory.K4.TopEta

namespace GlobalTheory.K4

open GlobalTheory.KZ

attribute [local instance] algMdl

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFiStatement
section
open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field : ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
  (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K, τ x ∈ FunctionField.ringOfIntegers k K) →
  ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K → (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    algebraMap F K b ∈ FunctionField.ringOfIntegers k K → (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
  ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)), (∀ g, (x g).toAdd = kum (N := N) ζ α g) → (∀ g, (y g).toAdd = kum (N := N) ζ β g) →
  ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η →
    IsLocallyConstant (fun g : geo F K Ω => η g) →
    (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over (FunctionField.ringOfIntegers k K).toSubring B →
      (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η g = 0) →
  ∀ σ : Ω ≃ₐ[F] Ω, IsTopW (K := K) ζ x y η σ (topW (K := K) ζ x y η σ) := by
  first | exact @GlobalTheory.K4.isTopW_topW | exact GlobalTheory.K4.isTopW_topW | (intros; apply GlobalTheory.K4.isTopW_topW <;> assumption)
end

