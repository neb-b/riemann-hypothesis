module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvLevCoreOfParts
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0036

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IsUnitOfMk
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03 PowerSeries

section Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem isUnit_of_mk {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : x * y' - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot I h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem aeval_X_coe {R : Type} [CommRing R] (r : Polynomial R) :
    Polynomial.aeval (PowerSeries.X : PowerSeries R) r = (r : PowerSeries R) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), hp, hq, Polynomial.coe_add]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.coe_monomial, PowerSeries.monomial_eq_mk]
    ext m
    simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, eq_comm]

theorem map_aeval {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : PowerSeries R) (P : Polynomial R) :
    PowerSeries.map f (Polynomial.aeval x P) = Polynomial.aeval (PowerSeries.map f x) (P.map f) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext c : 1
  simp [PowerSeries.algebraMap_eq]

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem wdiv_ps (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (f : PowerSeries O) :
    ∃ (H : PowerSeries O) (r : Polynomial O), r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) ∧
      f = ps W s a * H + (r : PowerSeries O) := by
  set I : Ideal O := Ideal.span {((PD.p : ℕ) : O)} with hIdef
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hIdef, Ideal.span_singleton_eq_top]; exact hpu)
  set N : ℕ := (PD.p - 1) * PD.p ^ s with hN
  set D : PowerSeries O := ps W s a with hDdef
  obtain ⟨u, P, hu, hPm, hPd, hPc, hps⟩ := hT.2.1 s
  obtain ⟨w, hw, hπw⟩ := ToolsR.π₀_comp hR
  have hD : D = u a * Polynomial.aeval W.π₀₁ P := by
    have h1 := congrFun hps a
    rw [Pi.mul_apply] at h1
    rw [hDdef, show ps W s = Formalism.MainNotions.WachCoordinates.pS W s from rfl, h1]
    congr 1
    exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) a) W.π₀ P).symm
  have hPmap : P.map (Ideal.Quotient.mk I) = Polynomial.X ^ (PD.p ^ s) := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    rcases lt_trichotomy k (PD.p ^ s) with hk | rfl | hk
    · rw [if_neg hk.ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.2 (hPc k hk)
    · rw [if_pos rfl, ← hPd, hPm.coeff_natDegree, map_one]
    · rw [if_neg hk.ne', Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  set V : PowerSeries (O ⧸ I) := PowerSeries.map (Ideal.Quotient.mk I) (u a) *
    PowerSeries.map (Ideal.Quotient.mk I) w ^ (PD.p ^ s) with hV
  have hmapD : PowerSeries.map (Ideal.Quotient.mk I) D = V * PowerSeries.X ^ N := by
    rw [hD, map_mul, map_aeval, hPmap, Polynomial.aeval_X_pow, hπw, map_mul, map_pow, PowerSeries.map_X, hV, hN,
      mul_pow, ← pow_mul, mul_comm (PD.p - 1) (PD.p ^ s)]
    ring
  have huV : IsUnit (PowerSeries.constantCoeff V) := by
    rw [hV, map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · have := ((hu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)).map
        (PowerSeries.map (Ideal.Quotient.mk I))).map PowerSeries.constantCoeff
      simpa using this
    · exact (hw.map (PowerSeries.map (Ideal.Quotient.mk I))).map PowerSeries.constantCoeff
  have hcN : PowerSeries.coeff N (PowerSeries.map (Ideal.Quotient.mk I) D) = PowerSeries.constantCoeff V := by
    rw [hmapD, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff]
  have hord : (PowerSeries.map (Ideal.Quotient.mk I) D).order.toNat = N := by
    have : (PowerSeries.map (Ideal.Quotient.mk I) D).order = N := by
      refine PowerSeries.order_eq_nat.2 ⟨by rw [hcN]; exact huV.ne_zero, fun i hi => ?_⟩
      rw [hmapD, PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
    rw [this, ENat.toNat_natCast]
  have hdiv : D.IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord]
    refine isUnit_of_mk I ?_
    rw [← PowerSeries.coeff_map, hcN]
    exact huV
  have HD := hdiv.isWeierstrassDivisionAt_div_mod f
  refine ⟨hdiv.div f, hdiv.mod f, ?_, HD.eq_mul_add⟩
  have := HD.degree_lt
  rwa [hord] at this

theorem ev_aeval {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) (ζ : Rs hB.F PD.p s)
    (r : Polynomial O) : hB.ev ζ (Polynomial.aeval (letπ : LetA O n) r) = Polynomial.aeval ((ζ : hB.F) - 1) r := by
  let evA : LetA O n →ₐ[O] hB.F := { hB.ev ζ with commutes' := hB.ev_O ζ }
  rw [← hB.ev_π ζ]
  exact (Polynomial.aeval_algHom_apply evA letπ r).symm

theorem card_Rs {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) :
    Fintype.card (Rs hB.F PD.p s) = (PD.p - 1) * PD.p ^ s := by
  obtain ⟨ζ₀, hζ₀⟩ := hB.root
  rw [Fintype.card_coe, hζ₀.card_primitiveRoots, Nat.totient_prime_pow_succ PD.hp, mul_comm]

theorem poly_eq_zero {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) (r : Polynomial hB.F)
    (hdeg : r.natDegree < (PD.p - 1) * PD.p ^ s) (h : ∀ ζ : Rs hB.F PD.p s, Polynomial.eval ((ζ : hB.F) - 1) r = 0) :
    r = 0 :=
  Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun ζ : Rs hB.F PD.p s => (ζ : hB.F) - 1)
    (fun x y hxy => Subtype.ext (sub_left_injective hxy)) h (by rw [card_Rs hB]; exact hdeg)

theorem levDiv_of (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) : LevDiv W a s hB.F hB.ev := by
  intro g hg hev
  have hNpos : 0 < (PD.p - 1) * PD.p ^ s := Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
  obtain ⟨H, r, hdeg, heq⟩ := wdiv_ps W hR hT hpu a s (g a)
  set wH : LetA O n := Pi.single a H with hwH
  have hRr : (fun _ : ZMod n => (r : PowerSeries O)) = Polynomial.aeval (letπ : LetA O n) r := by
    funext i
    show (r : PowerSeries O) = Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i (Polynomial.aeval letπ r)
    rw [← Polynomial.aeval_algHom_apply]
    exact (aeval_X_coe r).symm
  have key : (letE a : LetA O n) * g = ps W s * wH + letE a * Polynomial.aeval (letπ : LetA O n) r := by
    rw [← hRr]
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_same, one_mul, heq]
    · simp [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_of_ne hi]
  have hroots : ∀ ζ : Rs hB.F PD.p s, Polynomial.eval ((ζ : hB.F) - 1) (r.map (algebraMap O hB.F)) = 0 := by
    intro ζ
    have h1 := congrArg (hB.ev ζ) key
    rw [map_mul, hB.ev_letE, one_mul, hev ζ, map_add (f := _), map_mul, hB.ev_ps, zero_mul, zero_add, map_mul,
      hB.ev_letE, one_mul, ev_aeval hB] at h1
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact h1.symm
  have hr0 : r.map (algebraMap O hB.F) = 0 := by
    refine poly_eq_zero hB _ (lt_of_le_of_lt Polynomial.natDegree_map_le ?_) hroots
    by_cases hr : r = 0
    · rw [hr, Polynomial.natDegree_zero]; exact hNpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hr).2 hdeg
  have hr : r = 0 := Polynomial.map_injective _ hB.inj (by rw [hr0, Polynomial.map_zero])
  rw [hr, map_zero, mul_zero, add_zero] at key
  have hpsΔ : ps W s ∈ W.AΔ := RatW.ps_mem W hR.1 s
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hB.hp
    rw [← map_natCast (algebraMap O hB.F), h, map_zero]
  have hps0 : ∀ i, ps W s i ≠ 0 := by
    intro i h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hT.2.2.1 s)
    have h1 := congrFun hc i
    have h2 := congrArg PowerSeries.constantCoeff h1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.natCast_apply, map_mul, map_sub, map_natCast, LocWach.π₀,
      ToolsR.π₀₁_cc hR, mul_zero] at h2
    rw [show Formalism.MainNotions.WachCoordinates.pS W s i = ps W s i from rfl, h, map_zero, zero_sub, eq_comm, neg_eq_zero] at h2
    exact hp0 h2
  refine ⟨0, wH, ToolsR.cancel_AΔ hpsΔ hps0 ?_, by rw [pow_zero, one_mul, key]⟩
  rw [← key]
  exact W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hg

end Div

end Formalism.MainNotions.UnusedSlot80.InvW
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LamZero
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem γA_apply (g : W.Gam) (a : LetA O n) (i : ZMod n) : W.γA g a i = W.γ₀ g (a i) := rfl

theorem q_unit (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) :
    ∃ w : LetA O n, W.q = w * ps W 0 ∧ ∃ w' : LetA O n, w * w' = 1 ∧
      ∀ i, PowerSeries.constantCoeff (w' i) = 1 := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Formalism.MainNotions.UnusedSlot80.SatW.Eat_π₀] at hw
  have hq : (W.π₀ + ((PD.p : ℕ) : LetA O n)) = ps W 0 := by rw [ps_zero]; rfl
  rw [hq] at hw
  refine ⟨w, hw, ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.mul_inv w, fun i => ?_⟩
  have h1 : PowerSeries.constantCoeff (W.q i) =
      PowerSeries.constantCoeff ((w : LetA O n) i) * PowerSeries.constantCoeff (ps W 0 i) := by
    rw [hw, Pi.mul_apply, map_mul]
  rw [show W.q i = W.q₀ from rfl, Formalism.MainNotions.UnusedSlot80.ArcF.constantCoeff_q_zero_eq_p] at h1
  have h2 : PowerSeries.constantCoeff (ps W 0 i) = ((PD.p : ℕ) : O) := by
    rw [ps_zero]
    simp [LocWach.π₀, lA, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR]
  rw [h2] at h1
  have hw1 : PowerSeries.constantCoeff ((w : LetA O n) i) = 1 := by
    have : ((PD.p : ℕ) : O) * (PowerSeries.constantCoeff ((w : LetA O n) i) - 1) = 0 := by
      linear_combination -h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp0
    · exact sub_eq_zero.1 h
  have h3 : PowerSeries.constantCoeff ((w : LetA O n) i) *
      PowerSeries.constantCoeff (((w⁻¹ : (LetA O n)ˣ) : LetA O n) i) = 1 := by
    rw [← map_mul, ← Pi.mul_apply, Units.mul_inv]
    simp
  rwa [hw1, one_mul] at h3

theorem lam_zero (A : ArcP n) (a : ZMod n) : abelian₂ W A a 0 = 1 := by simp [abelian₂]

theorem cmpD_lam (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (hT : Win W A T) :
    ∀ e : ℕ, ∃ t : ℕ, ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T c' y →
      cmpD W T (abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y) =
        ((PD.p : LL) ^ t) • ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ e) (cmpD W T y) := by
  intro e
  induction e with
  | zero => exact ⟨0, fun y _ => by simp [lam_zero]⟩
  | succ e ih =>
    obtain ⟨t, ht⟩ := ih
    set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
    refine ⟨H + t, fun y hy => ?_⟩
    set z : W.DD T := abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y with hzdef
    obtain ⟨z', hz'N, hz'l, hzz'⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _
      (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e hy)
    rw [one_smul] at hzz'
    have hzN : z ∈ W.N T := by rw [hzdef, hzz']; exact hz'N.1
    have hzl : (letE (c' + (e : ZMod n)) : LetA O n) • z = z := by rw [hzdef, hzz']; exact hz'l
    have h5T := h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
    have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
    set i : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with hidef
    have hzNl : z ∈ W.Nl T (i - 1) := by
      rw [show i - 1 = c' + (e : ZMod n) by rw [hidef]; push_cast; ring]
      exact ⟨z, hzN, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hzl⟩
    have hM := h5T.1 i z hzNl
    rw [hQ] at hM
    have hMH : Mw A.G₀ A.S A.η (A.ty i) ≤ H := by
      have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
      rwa [Nat.sub_self] at this
    have hqN : W.q ^ H • W.φD T z ∈ W.N T := by
      obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hMH
      rw [hdd, pow_add, mul_comm, mul_smul]
      exact (W.N T).smul_mem _ hM
    have hφl : (letE i : LetA O n) • W.φD T z = W.φD T z := by
      have := φD_pow_letter W T (c' + (e : ZMod n)) z hzl 1
      rw [pow_one] at this
      rwa [show c' + (e : ZMod n) + ((1 : ℕ) : ZMod n) = i by rw [hidef]; push_cast; ring] at this
    have hql : (letE i : LetA O n) • (W.q ^ H • W.φD T z) = W.q ^ H • W.φD T z := by
      rw [smul_comm, hφl]
    obtain ⟨w, hw, w', hww, hw'⟩ := q_unit W hR hp0
    have hp0w : ps W 0 = w' * W.q := by
      rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
    have e1 : abelian₂ W A i (e + 1) • ((W.φD T) ^ (e + 1)) y = w' ^ H • (W.q ^ H • W.φD T z) := by
      rw [hidef, lam_succ, pow_apply_succ, smul_smul, hzdef, φD_smulA, smul_smul, hp0w]
      unfold LamUp
      congr 1; ring
    have hk : W.Q ^ H • W.φD T ((⟨z, hzN⟩ : ↥(W.N T)) : W.DD T) ∈ W.N T := by rw [hQ]; exact hqN
    have e2 := h3.2.2 ⟨z, hzN⟩ H hk
    have e3 : (⟨W.Q ^ H • W.φD T z, hk⟩ : ↥(W.N T)) = ⟨W.q ^ H • W.φD T z, hqN⟩ := Subtype.ext (by show W.Q ^ H • W.φD T z = W.q ^ H • W.φD T z; rw [hQ])
    rw [e3] at e2
    rw [e1, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem _ hqN),
      Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i _ _ hqN hql, e2, Pi.pow_apply, map_pow, hw', one_pow, map_one,
      one_smul, ← Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hzN, hzdef, ht y hy, map_smul, smul_smul, ← pow_add, pow_succ' _ e,
      Module.End.mul_apply]

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

