module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaTuplesLeastOrdersUnitary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_uLocTuples_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → X₁.Ω₁), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe M T ξ (t k j) a) ∧ ∃ j, UOrdEq M T ξ (t k j) a := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁
  have hNodd : Odd X₁.S.N := by rw [X₁.ρ.N_eq]; exact (X₁.ρ.n_odd.pow).pow
  have hN2 := X₁.S.N_ge
  have hN3 : 3 ≤ X₁.S.N := by obtain ⟨j, hj⟩ := hNodd; omega
  haveI hN0 : NeZero X₁.S.N := ⟨by omega⟩
  obtain ⟨m₁, m₂, hm₁, hm₂, hX⟩ := _root_.GlobalTheory.unitaryStepA_at_point E H Dw hpq l Xo c C X₁
  obtain ⟨B, ι₀, 𝓛, hι₀, hT⟩ := _root_.GlobalTheory.UPoinc.finite_types_unitary E H (min Dw.p Dw.q) φ hφ X₁.S.N hN3 hNodd
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((X₁.S.r * X₁.S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup X₁.S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup X₁.S.Gam => (H : Set X₁.S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup X₁.S.Gam, Finite (T₀ →+ ZMod X₁.S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod X₁.S.N => (f : T₀ → ZMod X₁.S.N)) DFunLike.coe_injective
  let Dt := Σ T₀ : AddSubgroup X₁.S.Gam, (T₀ →+ ZMod X₁.S.N) × (X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) × X₁.S.Gam
  haveI : Finite Dt := inferInstance
  let Es : Set X₁.Ω₁ := {v | v ≠ 0} ∩ Set.range (fun d : Dt => X₁.S.FF d.1 d.2.1 d.2.2.1 / X₁.S.th d.2.2.2)
  have hEs : Es.Finite := (Set.finite_range _).inter_of_right _
  letI : Fintype Es := hEs.fintype
  let K := Σ n : Fin B, Σ _ : {L // L ∈ 𝓛 n.1}, ((Fin n.1 → ZMod X₁.S.N) → Es)
  let Jk : K → Type := fun k => {ν // ν ∈ k.2.1.1}
  let t : ∀ k, Jk k → X₁.Ω₁ := fun k j => ∏ cl, ((k.2.2 cl : Es) : X₁.Ω₁) ^ ((m₁ : ℤ) * j.1 cl)
  refine ⟨m₂ * ι₀, K, inferInstance, Jk, fun k => inferInstance, t, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  · intro k j
    exact Finset.prod_ne_zero_iff.2 fun cl _ => zpow_ne_zero _ (k.2.2 cl).2.1
  intro M U₀ EE out hAdm hEE x
  obtain ⟨X, _, _, _, _, n, eb, b₀, μ, e, hrank, hbal, hpos, hμ, hmin, he, htr⟩ := hX M U₀ EE out hAdm hEE x
  obtain ⟨hnB, hL⟩ := hT n X hrank eb
  obtain ⟨L, hLmem, hLprop⟩ := hL b₀ hbal hpos μ hμ hmin
  have heE : ∀ cl, e cl ∈ Es := fun cl => by
    obtain ⟨hne, T₀, c', κ, x₀, _, hc⟩ := he cl
    exact ⟨hne, ⟨⟨T₀, c', κ, x₀⟩, hc.symm⟩⟩
  refine ⟨⟨⟨n, hnB⟩, ⟨L, hLmem⟩, fun cl => ⟨e cl, heE cl⟩⟩, ?_⟩
  intro T ξ hthr hspec
  obtain ⟨π, hπs, hπmin, hq⟩ := htr T ξ hthr hspec
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  set b' : LinearMap.BilinForm ℤ X := pull π T.be with hb'
  have hbeBal : T.be ∈ balForms H.bar T.P.D.toPre.X := by rw [balForms_eq_levelForms]; exact T.lev
  have hb'bal : b' ∈ balForms H.bar X := pull_mem π hbeBal
  have hμ0 : μ 0 = 0 := by
    by_contra h0
    have h1 := hmin 0 0 (fun i => by simp)
    have h2 := hpos _ h0
    simp at h1
    omega
  have hb'psd : ∀ y, 0 ≤ b' y y := by
    intro y
    have h1 := hπmin 0 ((X₁.S.N : ℤ) • y) (fun i => by simp)
    have hNpos : (0 : ℤ) < X₁.S.N := by exact_mod_cast (show 0 < X₁.S.N by omega)
    have h2 : (0 : ℤ) ≤ (X₁.S.N : ℤ) * ((X₁.S.N : ℤ) * T.be (π y) (π y)) := by
      simpa [hμ0, map_zsmul, LinearMap.smul_apply, smul_eq_mul] using h1
    show 0 ≤ T.be (π y) (π y)
    exact (mul_nonneg_iff_of_pos_left hNpos).1 ((mul_nonneg_iff_of_pos_left hNpos).1 h2)
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLprop b' hb'bal hb'psd hπmin
  have hφeq : φ.evalZ b' = φ.evalZ T.be := evalZ_pull φ hπs T.be
  have hφ0 : 0 ≤ φ.evalZ b' := (hφ X hrank).evalZ_nonneg hb'bal hb'psd
  set y : Sp (FractionRing T.V) ⟶ M.Z := jK T.V ≫ ξ with hy
  set z₀ := y (IsLocalRing.closedPoint (FractionRing T.V)) with hz₀
  have hsp : ∀ w, y w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hz₀U : z₀ ∈ U₀ := by
    obtain ⟨ξ₀, hξ₀, -⟩ := hthr
    have hz : z₀ = (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) := by rw [hξ₀]
    rw [hz]
    have hm : (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) ∈ Set.range U₀.ι := by
      exact ⟨ξ₀ (IsLocalRing.closedPoint (FractionRing T.V)), rfl⟩
    rw [U₀.range_ι] at hm; exact hm
  have hO : M.ringOn U₀ ≤ M.O z₀ := RatModel.ringOn_le_O (M := M) hz₀U
  have hOv := hAdm.1
  have hFFR : ∀ (T₀ : AddSubgroup X₁.S.Gam) c' κ, X₁.S.FF T₀ c' κ ∈ X₁.S.R := by
    intro T₀ c' κ
    haveI : Fintype T₀ := Fintype.ofFinite _
    unfold ThetaSys.FF
    rw [finsum_eq_sum_of_fintype]
    exact Subalgebra.sum_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (X₁.S.ev_mem _ _))
  have hunit : ∀ cl, e cl ≠ 0 ∧ e cl ∈ M.O z₀ ∧ (e cl)⁻¹ ∈ M.O z₀ := by
    intro cl
    obtain ⟨hne, T₀, c', κ, x₀, hiso, hc⟩ := he cl
    rw [hc] at hne ⊢
    have hF : X₁.S.FF T₀ c' κ ≠ 0 := (div_ne_zero_iff.1 hne).1
    have hth : X₁.S.th x₀ ≠ 0 := (div_ne_zero_iff.1 hne).2
    refine ⟨hne, hO ?_, hO ?_⟩
    · rw [div_eq_mul_inv]; exact Subalgebra.mul_mem _ (hOv.le (hFFR T₀ c' κ)) (hOv.th_unit x₀ hth)
    · rw [inv_div, div_eq_mul_inv]
      exact Subalgebra.mul_mem _ (hOv.le (X₁.S.th_mem x₀)) (hOv.FF_unit T₀ c' κ hiso hF)
  have hvne : ∀ cl, M.val y (e cl) ≠ 0 := by
    intro cl
    have h1 := RatModel.val_mul (M := M) hsp (hunit cl).2.1 (hunit cl).2.2
    rw [mul_inv_cancel₀ (hunit cl).1, RatModel.val_one] at h1
    exact left_ne_zero_of_mul_eq_one h1.symm
  have hpow : ∀ cl, M.val y (e cl ^ m₁) = M.val y (e cl) ^ m₁ := by
    intro cl
    have := _root_.GlobalTheory.Poinc.RatModel.val_prod_zpow M y z₀ hsp (Finset.univ : Finset Unit) (fun _ => e cl) (fun _ => (m₁ : ℤ)) fun _ => hunit cl
    simpa using this
  choose v w hvw using fun cl => _root_.GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit T.irr (M.val y (e cl)) (hvne cl)
  have hϖ0 : algebraMap T.V (FractionRing T.V) T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 T.irr.ne_zero
  have hunitK : ∀ (a : T.Vˣ) (k : ℤ), algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
      (algebraMap T.V (FractionRing T.V) (a : T.V)) ^ k := by
    intro a k
    have h1 : algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom (a ^ k) : (FractionRing T.V)ˣ) : FractionRing T.V) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have hNv : ∀ cl, (m₁ : ℤ) * v cl = (m₂ : ℤ) * b' (μ cl) (μ cl) := by
    intro cl
    obtain ⟨w', hw'⟩ := hq cl
    have hq0 : 0 ≤ (m₂ : ℤ) * b' (μ cl) (μ cl) := mul_nonneg (by positivity) (hb'psd _)
    rw [hpow] at hw'
    have h2 : algebraMap T.V (FractionRing T.V) T.ϖ ^ ((m₁ : ℤ) * v cl) *
        algebraMap T.V (FractionRing T.V) ((w cl ^ (m₁ : ℤ) : T.Vˣ) : T.V) =
        algebraMap T.V (FractionRing T.V) T.ϖ ^ ((((m₂ : ℤ) * b' (μ cl) (μ cl)).toNat : ℕ) : ℤ) *
        algebraMap T.V (FractionRing T.V) (w' : T.V) := by
      rw [hunitK, mul_comm (m₁ : ℤ) (v cl), zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← hvw cl]
      rw [show (((m₂ : ℤ) * b' (μ cl) (μ cl)).toNat) = (((m₂ : ℤ) * T.be (π (μ cl)) (π (μ cl))).toNat) from rfl]
      rw [hw', map_mul, map_pow, zpow_natCast]
    have := GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique T.irr _ _ _ _ h2
    rw [this, Int.toNat_of_nonneg hq0]
  let Ev : ((Fin n → ZMod X₁.S.N) → ℤ) → ℤ := fun ν => ∑ cl, v cl * ((m₁ : ℤ) * ν cl)
  have hE : ∀ ν, (Ev ν : ℝ) = (m₂ : ℝ) * ∑ cl, (ν cl : ℝ) * (b' (μ cl) (μ cl) : ℝ) := by
    intro ν
    have h1 : Ev ν = (m₂ : ℤ) * ∑ cl, ν cl * b' (μ cl) (μ cl) := by
      simp only [Ev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun cl _ => ?_
      have := hNv cl
      linear_combination (ν cl) * this
    rw [h1]; push_cast; ring
  have hzs : ∀ (f : (Fin n → ZMod X₁.S.N) → ℤ) (s : Finset (Fin n → ZMod X₁.S.N)),
      ∏ cl ∈ s, algebraMap T.V (FractionRing T.V) T.ϖ ^ f cl = algebraMap T.V (FractionRing T.V) T.ϖ ^ ∑ cl ∈ s, f cl := by
    intro f s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hϖ0]
  have hval : ∀ ν, M.val y (∏ cl, e cl ^ ((m₁ : ℤ) * ν cl)) = algebraMap T.V (FractionRing T.V) T.ϖ ^ Ev ν *
      algebraMap T.V (FractionRing T.V) ((∏ cl, w cl ^ ((m₁ : ℤ) * ν cl) : T.Vˣ) : T.V) := by
    intro ν
    rw [_root_.GlobalTheory.Poinc.RatModel.val_prod_zpow M y z₀ hsp _ _ _ fun cl => hunit cl]
    simp only [hvw, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul, ← hunitK]
    rw [hzs, Units.coe_prod, map_prod]
  have hprodO : ∀ ν : (Fin n → ZMod X₁.S.N) → ℤ, (∏ cl, e cl ^ ((m₁ : ℤ) * ν cl)) ∈ M.O z₀ := by
    intro ν
    refine Subalgebra.prod_mem _ fun cl _ => ?_
    rcases Int.eq_nat_or_neg ((m₁ : ℤ) * ν cl) with ⟨k, hk | hk⟩ <;> rw [hk]
    · rw [zpow_natCast]; exact Subalgebra.pow_mem _ (hunit cl).2.1 k
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subalgebra.pow_mem _ (hunit cl).2.2 k
  have hge : ∀ ν ∈ L, ((m₂ * ι₀ : ℕ) : ℝ) * φ.evalZ T.be ≤ Ev ν := by
    intro ν hν
    have h1 := mul_le_mul_of_nonneg_left (hle ν hν) (Nat.cast_nonneg (α := ℝ) m₂)
    rw [hE ν, ← hφeq]; push_cast
    nlinarith
  have hE0 : ((Ev ν₀ : ℤ) : ℝ) = ((m₂ * ι₀ : ℕ) : ℝ) * φ.evalZ T.be := by
    rw [hE ν₀, ← heq, ← hφeq]; push_cast; ring
  have hEnn : 0 ≤ Ev ν₀ := by
    have : (0 : ℝ) ≤ (Ev ν₀ : ℝ) := by
      rw [hE0]; exact mul_nonneg (Nat.cast_nonneg _) (hφeq ▸ hφ0)
    exact_mod_cast this
  refine ⟨(Ev ν₀).toNat, ?_, ?_, ?_⟩
  · rw [← hE0]; exact_mod_cast Int.toNat_of_nonneg hEnn
  · intro j
    show UOrdGe M T ξ (∏ cl, e cl ^ ((m₁ : ℤ) * j.1 cl)) _
    have hle' : Ev ν₀ ≤ Ev j.1 := by
      have := hge j.1 j.2; rw [← hE0] at this; exact_mod_cast this
    obtain ⟨d, hd⟩ : ∃ d : ℕ, Ev j.1 = ((Ev ν₀).toNat : ℤ) + d := ⟨(Ev j.1 - Ev ν₀).toNat, by omega⟩
    refine ⟨hprodO j.1, T.ϖ ^ d * ((∏ cl, w cl ^ ((m₁ : ℤ) * j.1 cl) : T.Vˣ) : T.V), ?_⟩
    rw [hval, hd, map_mul, map_mul, map_pow, map_pow, zpow_add₀ hϖ0, zpow_natCast, zpow_natCast, mul_assoc]
  · refine ⟨⟨ν₀, hν₀⟩, ?_⟩
    show UOrdEq M T ξ (∏ cl, e cl ^ ((m₁ : ℤ) * ν₀ cl)) _
    refine ⟨∏ cl, w cl ^ ((m₁ : ℤ) * ν₀ cl), ?_⟩
    rw [hval, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hEnn]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.Periods

theorem inv_eq_unit_mul {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (g : D.X → (FractionRing R)ˣ) {y : D.X} {r : R} (hr : Formalism.L2.Pj.PsiCoord D y r)
    (hU : PsiUnitOn (GlobalTheory.PolDeg.rescale D g) y Set.univ) :
    ∃ u : Rˣ, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ u * algebraMap R _ r := by
  have hex : ∃ v : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.TauTwist.rescale D g) y v := by
    let D' := GlobalTheory.TauTwist.rescale D g
    obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D' y
    have hh := GlobalTheory.PsiCoordLocal.generic_le D' y j hj
    obtain ⟨s, hs, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
    obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 s
    have hu : IsUnit r := (MulEquiv.isUnit_map
      (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤) GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 hs
    exact ⟨hu.unit, j, hj, hh, e⟩
  obtain ⟨v, hv⟩ := hex
  obtain ⟨x, ⟨j, h, hj, rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y r).1 hr
  obtain ⟨x', hx', e'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D g) y _).1 hv
  have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord (GlobalTheory.TauTwist.rescale D g) y (g y * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi y) j h) := by
    refine ⟨j, h, hj, ?_⟩
    dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
    rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
    congr 1
    ext
    show (g y : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (g y : FractionRing R)))
    rw [CategoryTheory.Functor.map_id]
    exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
  obtain ⟨u, hu⟩ := h₁.unique hx'
  have k := congrArg Units.val hu
  rw [Units.val_mul, Units.val_mul, e, e'] at k
  have k' : (g y : FractionRing R) * algebraMap R _ r = algebraMap R _ ((u * v : Rˣ) : R) := by
    rw [k, Units.val_mul, map_mul]; rfl
  refine ⟨(u * v)⁻¹, ?_⟩
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [mul_left_comm, k', ← map_mul, Units.inv_mul, map_one]

theorem exists_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (β : C.P.D.toPre.P.A.left ⟶ L.D.P.A.left), IsGrpPullback C.P.D.toPre.P.A L.D.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (C.P.oD.onB.act a).left ≫ β = β ≫ (L.oa.onB.act a).left) → LBIso C.P.D.toPre.P.L (L.D.P.L.pull β) → (∀ y, (C.P.D.toPre.c y).left ≫ β = spMap θ₀ ≫ (L.D.c (l.M' • e y)).left) → ∀ (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)), (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) → ∃ s : Fin C.m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C D' L θ₀ e β hβ hact hL hc N ε hε
  letI := H.starRing
  obtain ⟨-, hbm, hgen, o₀, ho₀, hw₀⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  letI : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨g, hD, q, hxe, hpr, hU, qs, qa, qb, hg⟩ := GlobalTheory.T.degData_differ_by_symmBalancedForm_of_psi_tau (H := H) θ₀ (mulDeg L.D l.M') o₀ C.P.D.toPre C.P.oD e β
    hbm hgen hw₀ C.P.D.tau_bimult C.P.w0 hβ (fun a => by rw [ho₀]; exact hact a) hL hc
  have hM : IsUnit ((l.M' : ℕ) : V) := by
    have h1 : IsUnit ((l.M' : ℕ) : c.F) := (Nat.cast_ne_zero.2 (level_pos l).ne').isUnit
    simpa using h1.map C.b
  obtain ⟨s, hs₁, hs₂, hs⟩ := _root_.GlobalTheory.UnitForm.exists_unit_coords H L.D.X V hV.1.2.2.2 hk l.M' hM C.m N ε C.s C.s_ne_zero
    (fun a b => q (e.symm a) (e.symm b)) (fun a b => qs _ _) (fun a a' b => by simp only [map_add (f := _), qa])
    (fun x a b => by simp only [map_smul, qb]) (fun y => by
      obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨u, n, hn, hco⟩ := C.mono y
      obtain ⟨v, hv⟩ := inv_eq_unit_mul _ g hco (hU y)
      refine ⟨v * u, ?_⟩
      rw [map_smul, e.symm_apply_apply, ← hg, hv, Units.val_mul, map_mul, map_mul, map_prod, _root_.mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, ← zpow_natCast]
      congr 1
      have h1 := apply_self_eq_two_mul ((balForms_eq_levelForms H L.D.X).le (ε (.inl i)).2) (e y)
      have h2 := hn i
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hε, pull_apply, LinearEquiv.coe_coe, h1, smul_eq_mul] at h2
      linarith)
  refine ⟨s, hs₁, hs₂, g, hD, fun y => ?_, hxe, fun x => ?_⟩
  · rw [hg, ← hs, map_smul, e.symm_apply_apply]
  · have := hact x
    rw [← hpr] at this
    exact this.trans (Category.assoc _ _ _)

end GlobalTheory.UCanon.Periods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsPrescribedReductionFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.SecsAsm

theorem gs_scal_one {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Y ⟶ Sp R) (p : Z ⟶ Y) (z : Z) :
    gs p z ⊤ (scal q 1) = 1 := by
  unfold scal
  rw [map_one, map_one, gs_eq p z ⊤ trivial, map_one, map_one]

theorem closed_pt (R : Type) [CommRing R] [IsLocalRing R] :
    spMap (residue R) (closedPoint (ResidueField R)) = closedPoint R :=
  IsLocalRing.comap_closedPoint (residue R)

theorem secs_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) : Nonempty (Secs C.toModif C.G C.P.L.L C.α) := by
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨hsm, -, -, -, -⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨S, k₁, himm⟩ := _root_.GlobalTheory.Mum.ThetaImm.exists_immersion R hB D Y
  obtain ⟨hth, hth0⟩ := _root_.GlobalTheory.ThFam.exists_intFam_lead R hB D
  choose k₀ hk₀ using hth
  obtain ⟨⟨j₀, hdesc⟩, hdescθ⟩ := GlobalTheory.Mum.exists_secs_of_intFam R hB D C
  have hk : k₁ + ∑ a ∈ S, k₀ a ≤ C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) :=
    (le_max_right _ _).trans (Nat.lt_pow_self C.n_prime.one_lt).le
  obtain ⟨Φ, hΦ⟩ := hdesc (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) (le_max_left _ _)
  obtain ⟨N, α, b, τ, hτ, hατ, hI⟩ := himm _ ((Nat.le_add_right _ _).trans hk)
  have hF : ∀ i, ∃ F : IntFam (maximalIdeal R) D.toPre (C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a))), F.Lead (α i) (b i) :=
    fun i => hk₀ (α i) _ (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hατ i).1).trans
      (Nat.le_add_left _ _)).trans hk) (b i)
  choose F hFl using hF
  obtain ⟨bθ, τθ, y₀, hθt, hy₀c, hy₀⟩ := GlobalTheory.Mum.exists_term_nonzero_closed R hB D Y
  obtain ⟨F₁, hF₁⟩ := hth0 1 le_rfl bθ
  obtain ⟨θ, hθ⟩ := hdescθ F₁
  have hsm0 : Smooth ((Over.pullback (spMap (residue R))).obj Y.H).hom :=
    inferInstanceAs (Smooth (pullback.snd Y.H.hom (spMap (residue R))))
  have himm0 : IsImmersion (pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
    have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
    have : IsClosedImmersion (pullback.fst Y.H.hom (spMap (residue R))) := inferInstance
    infer_instance
  refine ⟨{ N := N, k := _, s := fun i => Φ (F i), θ := θ, Y := (Over.pullback (spMap (residue R))).obj Y.H
            smooth := hsm0
            j := pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
            j_over := ?_
            imm := himm0
            O := pullback.fst Y.H.hom (spMap (residue R)) ⁻¹ᵁ nonzeroLocus τθ
            O_ne := ?_
            trait := ?_ }⟩
  · rw [Category.assoc, GlobalTheory.ProjSpace.toProj_str, pullback.condition]; rfl
  · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.H.hom) (g := spMap (residue R)) y₀
      (closedPoint _) (hy₀c.trans (closed_pt R).symm)
    exact ⟨z, show pullback.fst Y.H.hom (spMap (residue R)) z ∈ nonzeroLocus τθ by rw [hz]; exact hy₀⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, T, hio, hfin, hTφ, hTξ⟩ := C.exists_trait W hW φ ξ hφ hloc hξ
  obtain ⟨u, hu⟩ := hΦ W' T
  obtain ⟨uθ, huθ⟩ := hθ W' T
  choose σ hσE hσA using fun i => hu (F i)
  obtain ⟨θ', hθE, hθA⟩ := huθ
  obtain ⟨κ, e, hκ, he, hred⟩ := GlobalTheory.Mum.trait_lead_value R hB D C Y W' T
  have hκ' : κ.comp (residue R) = (residue W').comp (io.comp φ) := by rw [hκ, hTφ]
  refine ⟨W', _, inferInstance, inferInstance, io, T.G, inferInstance, T.β, σ, θ', κ, e, T.cdvr, hio, hfin,
    by rw [← hTξ]; exact T.cart, hκ', he, fun i Z p p' hpp z J hJ => ?_, fun Z p p' hpp z J hJ => ?_, ?_⟩
  · rw [hσA i Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  · rw [hθA Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  intro Ω _ p p' y hp hy
  have hval := hred (Sp Ω) p p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) hp
    (by rw [hy]; simp only [Category.assoc])
  have e1 : spMap (residue W') ≫ spMap (io.comp φ) = spMap κ ≫ spMap (residue R) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ']
  have hw := Over.w e.hom
  have hbase : p' ≫ T.G.hom ≫ spMap (io.comp φ) = (y ≫ pullback.fst Y.H.hom (spMap (residue R))) ≫ Y.H.hom := by
    rw [hp]
    simp only [Category.assoc]
    rw [pullback.condition_assoc, e1, pullback.condition]
    rw [hy]
    simp only [Category.assoc]
    erw [pullback.condition_assoc]
    rw [← Category.assoc e.hom.left]
    erw [hw]
    rfl
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨-, hs, hP⟩ := GlobalTheory.Mum.toProj_secPull_of_sval R Ω C.G.left D.toPre.P.A.left T.G.left Y.H.left C.P.L.L D.toPre.P.L
      T.β Y.q.left _ N σ τ Y.H.hom hτ p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) C.P.L.isLB D.toPre.P.isLB
      (fun z J J' hJ hJ' => by
        obtain ⟨c, hc⟩ := hval _ u z J J' hJ hJ'
        exact ⟨c, fun i => hc (α i) (b i) (τ i) (F i) (σ i) (hατ i).2 (hFl i) (hσE i)⟩)
    rw [hbase]
    exact ⟨hs, hP.trans (by simp only [Category.assoc])⟩
  · choose J hJ using fun χ : Sp Ω ⟶ C.G.left => exists_chart C.P.L.isLB (χ x)
    choose J' hJ' using fun χ : Sp Ω ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ x)
    obtain ⟨c, hc⟩ := hval 1 uθ x J J' hJ hJ'
    have h1 := hc 0 bθ τθ F₁ θ' hθt hF₁ hθE
    have hx' : (y ≫ pullback.fst Y.H.hom (spMap (residue R))) x ∈ nonzeroLocus τθ := hx
    have hu1 := (GlobalTheory.mem_nonzeroLocus_iff_pull τθ _ x (Good.mem hJ' _ _)).1 hx'
    refine (GlobalTheory.mem_nonzeroLocus_iff_pull θ' p' x (Good.mem hJ _ _)).2 ?_
    change IsUnit (sval θ' p' x J)
    rw [h1]
    exact c.isUnit.mul hu1

end GlobalTheory.Mum.SecsAsm

theorem GlobalTheory.Mum.exists_secs_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (C₁ : LabCover D₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ Nonempty (Secs C₁.toModif C₁.G C₁.P.L.L C₁.α) := by
  intro R _ _ _ hB D C
  obtain ⟨h, -, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D, C,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, ⟨h⟩, GlobalTheory.Mum.SecsAsm.secs_exists R hB D C⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMemberInjectiveEvaluation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem zhAbove_surjective {X₁ : GSet} {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} (h : ZHAbove X₁ Y πY) :
    Function.Surjective πY := by
  obtain ⟨-, -, -, -, -, hH, hP⟩ := h
  haveI := hP
  have hc : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
  have hg : genericPoint X₁.M.Z ∈ Set.range πY := by
    refine ⟨Y.pt (IsLocalRing.closedPoint X₁.Ω₁), ?_⟩
    have e := congrArg (fun f : Sp X₁.Ω₁ ⟶ X₁.M.Z => f (IsLocalRing.closedPoint X₁.Ω₁)) hH
    simp only [Scheme.Hom.comp_apply] at e
    exact e.trans (X₁.M.pt_apply _)
  intro z
  have : z ∈ closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) := by
    rw [genericPoint_spec X₁.M.Z |>.def]; trivial
  exact (closure_minimal (Set.singleton_subset_iff.2 hg) hc) this

theorem exists_gMem_injective : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Function.Injective ev ∧ Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  intro I X₁ z₁ act hact
  obtain ⟨Y, πY, hY⟩ := _root_.GlobalTheory.GSep.exists_zhAbove X₁
  obtain ⟨y, hy⟩ := zhAbove_surjective hY z₁
  obtain ⟨V, i1, i2, i3, -, ev, X, i4, t, δ, 𝔫, -, -, -, hinj⟩ := _root_.GlobalTheory.GSep.Thru.exists_gMem_thru I X₁ z₁ act hact Y πY hY y hy
  exact ⟨V, i1, i2, i3, ev, X, i4, t, δ, hinj, ⟨𝔫⟩⟩

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (L.actG g v) (L.actG g w) = (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) v w := by
  first | (exact @GlobalTheory.LKGeo.actG_form_eq_sim) | (exact GlobalTheory.LKGeo.actG_form_eq_sim) | (intros; apply GlobalTheory.LKGeo.actG_form_eq_sim  <;> assumption)
end

