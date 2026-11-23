module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvAtApply
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Con

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F]

theorem rs_root (s : ℕ) (ζ : Rs F PD.p s) :
    Polynomial.aeval ((ζ : F) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
  root_Zp PD.p (s + 1) (by rw [add_sub_cancel]; exact rs_pow_N F PD.p s ζ)

def evAt (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) : LetA O n →+* F :=
  (evR PD.p (s + 1) hlm (rs_root F s ζ)).toRingHom.comp
    (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)

theorem evAt_apply (a : ZMod n) (s : ℕ) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ x = evR PD.p (s + 1) hlm (rs_root F s ζ) (x a) := rfl

theorem ev_qp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (s : ℕ) {y : F}
    (hy : Polynomial.aeval y (Zp (O := O) PD.p (s + 1)) = 0) :
    (evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) = 0) ↔
      (y ≠ 0 ∧ (1 + y) ^ PD.p = 1) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Formalism.MainNotions.N.Pv.LocalLengthBound.eat_qp] at hw
  have hq0 : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    have := congrFun hw 0
    simpa [LocWach.q, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀] using this
  have hwu : evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) ≠ 0 := by
    have hu : IsUnit ((w : LetA O n) 0) := (w.isUnit.map (Pi.evalMonoidHom (fun _ => PowerSeries O) 0))
    exact (hu.map (evR PD.p (s + 1) hlm hy)).ne_zero

  have hXq : PowerSeries.X * W.q₀ = (1 + PowerSeries.X) ^ PD.p - 1 := by
    rw [← W.φ₀_X, Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W]
  have hev : y * evR PD.p (s + 1) hlm hy W.q₀ = (1 + y) ^ PD.p - 1 := by
    have := congrArg (evR PD.p (s + 1) hlm hy) hXq
    rwa [map_mul, evR_X, map_sub, evR_onePow, map_one] at this
  have hsplit : evR PD.p (s + 1) hlm hy W.q₀ = evR PD.p (s + 1) hlm hy ((w : LetA O n) 0) *
      evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    rw [hq0, map_mul]
  constructor
  · intro h0
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by rw [hsplit, h0, mul_zero]
    refine ⟨fun hy0 => ?_, ?_⟩
    ·
      have hcc := evR_eq_cc PD.p (s + 1) hlm hy hy0 W.q₀
      have hc : PowerSeries.constantCoeff W.q₀ = ((PD.p : ℕ) : O) := by
        have := congrArg (PowerSeries.coeff 1) hXq
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
        rw [this]
        have e : ((1 + PowerSeries.X) ^ PD.p - 1 : PowerSeries O) =
            (((1 + Polynomial.X) ^ PD.p - 1 : Polynomial O) : PowerSeries O) := by
          simp [Polynomial.coe_pow]
        rw [e, Polynomial.coeff_coe, Polynomial.coeff_sub, Polynomial.coeff_one, add_comm,
          Polynomial.coeff_X_add_one_pow]
        simp
      rw [hq, hc, map_natCast] at hcc
      exact (Nat.cast_ne_zero.2 (hpF.out.ne_zero)) hcc.symm
    · have := hev
      rw [hq, mul_zero] at this
      exact (sub_eq_zero.1 this.symm)
  · rintro ⟨hy0, hyp⟩
    have hq : evR PD.p (s + 1) hlm hy W.q₀ = 0 := by
      have := hev
      rw [hyp, sub_self] at this
      exact (mul_eq_zero.1 this).resolve_left hy0
    rw [hsplit] at hq
    exact (mul_eq_zero.1 hq).resolve_left hwu

end Con

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevNOsmul
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Fam

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem levN_osmul (c : ZMod n) (ζ : LL) (o : O) (x : ↥(W.N T)) :
    W.levN T c ζ (o • x) = algebraMap O LL o • W.levN T c ζ x := by
  obtain ⟨m, hm⟩ := W.levN_supp T c ζ x
  have e : (o • x : ↥(W.N T)) = (algebraMap O (LetA O n) o) • x := by
    ext; simp [algebraMap_smul]
  rw [e]
  have := funext fun k => W.levN_smul T c ζ (algebraMap O (LetA O n) o) x k
  rw [this]
  change smulS _ _ = _
  have hC : (algebraMap O (PowerSeries LL) o) = PowerSeries.C (algebraMap O LL o) := by
    first
    | exact PowerSeries.algebraMap_apply' o
    | exact PowerSeries.algebraMap_apply o
    | simp [PowerSeries.algebraMap_apply']
    | simp [PowerSeries.algebraMap_apply]
  rw [AlgHom.commutes, hC, smulS_C hm]

theorem fam_exp [IsDomain O] {A : Type} [AddCommGroup A] [Module O A] (hs : W.s = 1)
    (c : ZMod n) (ζ₀ : LL)
    (hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ₀ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-k))
    (χ : LL) (hχ0 : χ ≠ 0) (hχ : ∀ i : ℤ, i ≠ 0 → χ ^ i ≠ 1)
    (hγN : ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
      W.levN T c ζ₀ ⟨W.γ T x, hγx⟩ k = χ ^ k • W.levN T c ζ₀ ⟨x, hx⟩ k)
    (hγA : ∀ f : LetA O n, W.lev c ζ₀ (W.γA W.gam f) = PowerSeries.rescale χ (W.lev c ζ₀ f))
    (u₀ : PowerSeries LL) (hu₀ : W.lev c ζ₀ W.q = X * u₀) (hu0 : constantCoeff u₀ ≠ 0)
    (K : ℕ) (w : A →ₗ[O] W.DD T) (hK : ∀ f, W.Q ^ K • w f ∈ W.N T)
    (hγw : ∀ f, W.γ T (w f) - w f ∈ W.N T) :
    ∃ dd : A → ℤ → T.V ⊗[Qp] BdR, (∀ f, ∃ m, LB m (dd f)) ∧
      (∀ f, W.levN T c ζ₀ ⟨W.Q ^ K • w f, hK f⟩ = smulS ((X * u₀) ^ K) (dd f)) ∧
      (∀ f (i : ℤ), i ≠ 0 → dd f i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i)) ∧
      (∀ f g, dd (f + g) = dd f + dd g) ∧ (∀ (o : O) f, dd (o • f) = algebraMap O LL o • dd f) := by
  have ex : ∀ f, ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m, LB m d) ∧
      W.levN T c ζ₀ ⟨W.Q ^ K • w f, hK f⟩ = smulS ((X * u₀) ^ K) d ∧
      ∀ i : ℤ, (χ ^ i - 1) • d i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i) :=
    fun f => gamma_levels_expansion W T hs c ζ₀ hLv χ hχ0 hγN hγA u₀ hu₀ hu0 (hK f) (hγw f)
  choose dd hdLB hde hdγ using ex
  have hanti := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0
  refine ⟨dd, hdLB, hde, fun f i hi => ?_, fun f g => ?_, fun o f => ?_⟩
  · have h := Formalism.KernelCokernelLengths.exists_fixed_add_of_sub_mem LL (T.V ⊗[Qp] BdR) (fun a => Formalism.MainNotions.WachCoordinates.FilLev W T c 0 a)
      hanti χ hχ 0 0 (dd f) (fun j h1 h2 => by omega) (hdγ f)
    exact h.1 i hi
  · obtain ⟨m1, h1⟩ := hdLB (f + g)
    obtain ⟨m2, h2⟩ := hdLB f
    obtain ⟨m3, h3⟩ := hdLB g
    have e1 : (⟨W.Q ^ K • w (f + g), hK (f + g)⟩ : ↥(W.N T)) =
        ⟨W.Q ^ K • w f, hK f⟩ + ⟨W.Q ^ K • w g, hK g⟩ := Subtype.ext (by simp [smul_add])
    have e2 := hde (f + g)
    rw [e1, map_add (f := _), hde f, hde g, ← smulS_add (LB_mono h2 (min_le_left m2 m3))
      (LB_mono h3 (min_le_right m2 m3))] at e2
    exact div_unique (m := min m1 (min m2 m3)) (LB_mono h1 (min_le_left _ _))
      (LB_mono (LB_add (LB_mono h2 (min_le_left m2 m3)) (LB_mono h3 (min_le_right m2 m3)))
        (min_le_right _ _)) u₀ hu0 K e2.symm
  · obtain ⟨m1, h1⟩ := hdLB (o • f)
    obtain ⟨m2, h2⟩ := hdLB f
    have e1 : (⟨W.Q ^ K • w (o • f), hK (o • f)⟩ : ↥(W.N T)) = o • ⟨W.Q ^ K • w f, hK f⟩ :=
      Subtype.ext (by simp [osmul_comm W T])
    have e2 := hde (o • f)
    rw [e1, levN_osmul W T c ζ₀ o, hde f, ← smulS_smul h2] at e2
    exact div_unique (m := min m1 m2) (LB_mono h1 (min_le_left _ _))
      (LB_mono (LB_smul h2 _) (min_le_right _ _)) u₀ hu0 K e2.symm

end Fam

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PhiExp
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Phi

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem phi_exp (hs : W.s = 1) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p)
    (y : W.DD T) (hy : y ∈ W.N T) (hyl : (letE (i - 1) : LetA O n) • y = y) :
    ∃ d : ℤ → T.V ⊗[Qp] BdR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (W.φD T y) d ∧ (∀ k : ℤ, k < 0 → d k = 0) ∧
      d 0 = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨y, hy⟩)) := by
  have hp := p_ne_zero_LL W
  obtain ⟨u, hu0, hq⟩ := MC.lev_q_eq W i hζ hp
  have hQ : W.lev i ζ W.Q = PowerSeries.X * u := by rw [MC.Q_eq_q W hs]; exact hq
  obtain ⟨m, hm⟩ := W.N_φ T y hy
  have hm' : W.Q ^ m • W.φD T y ∈ W.N T := hm
  set y' : ↥(W.N T) := ⟨y, hy⟩ with hy'

  have hcX : PowerSeries.constantCoeff (W.lev (i - 1) 1 W.X) = 0 := by
    have e : W.X = letπ := by simp [LocWach.X, hs]
    rw [e, MC.cc_lev_pi W (i - 1) 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩, sub_self]
  have hneg : ∀ k : ℤ, k < 0 → C.levB T (i - 1) 1 y' k = 0 := by
    intro k hk
    have h0 := (((h4W T hT).1 (i - 1) 1 ⟨0, by simp⟩ hcX).1 y' k).2 hk
    rw [C.levN_eq] at h0
    exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (V := T.V) (h0.trans (map_zero _).symm)
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hφrule : ∀ k : ℤ, W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ k =
      ιV PD (LL := LL) (V := T.V) (∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ))))) := by
    intro k
    rw [C.levN_eq, C.levB_φ T hT i ζ ⟨1, by rwa [pow_one]⟩ y' m hm' k, hζp]
  have hcoef : ∀ j : ℕ, j < m → PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0 := by
    intro j hj
    rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hterm0 : ∀ (k : ℤ) (j : ℕ), (j < m ∨ k < (j : ℤ)) →
      PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) • (((PD.p : LL) ^ (k - (j : ℤ))) •
        φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ)))) = 0 := by
    intro k j h
    rcases h with h | h
    · rw [hcoef j h, zero_smul]
    · rw [hneg _ (by omega), map_zero, smul_zero, smul_zero]
  set e : ℤ → T.V ⊗[Qp] BdR := W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ with he
  have he_low : ∀ k : ℤ, k < m → e k = 0 := by
    intro k hk
    rw [hφrule, finsum_eq_zero_of_forall_eq_zero, map_zero]
    intro j
    by_cases hj : j < m
    · exact hterm0 k j (Or.inl hj)
    · exact hterm0 k j (Or.inr (by omega))
  have he_m : e m = (PowerSeries.constantCoeff u) ^ m •
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' 0)) := by
    rw [hφrule, finsum_eq_single _ m (fun j hj => ?_)]
    · rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, sub_self, zpow_zero, one_smul,
        map_smul]
    · rcases Nat.lt_or_gt_of_ne hj with h | h
      · exact hterm0 _ j (Or.inl h)
      · exact hterm0 _ j (Or.inr (by exact_mod_cast h))

  set e' : ℤ → T.V ⊗[Qp] BdR := fun k => e (k + m) with he'
  have hLBe' : LB 0 e' := fun k hk => he_low _ (by omega)
  have huK : PowerSeries.constantCoeff (u ^ m) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu0
  set d : ℤ → T.V ⊗[Qp] BdR := smulS (u ^ m)⁻¹ e' with hd
  have hLBd : LB 0 d := LB_smulS hLBe' _
  have hde : smulS ((PowerSeries.X * u) ^ m) d = e := by
    rw [mul_pow, smulS_mul hLBd, hd, ← smulS_mul hLBe', PowerSeries.mul_inv_cancel _ huK,
      smulS_one hLBe', smulS_X_pow hLBe']
    funext k
    simp [he']
  refine ⟨d, ⟨⟨0, hLBd⟩, W.Q ^ m, hm', ?_, fun k => ?_⟩, fun k hk => hLBd k hk, ?_⟩
  · rw [map_pow, hQ]
    exact pow_ne_zero _ (mul_ne_zero PowerSeries.X_ne_zero
      (fun h0 => hu0 (by rw [h0, map_zero])))
  · rw [map_pow, hQ, conv_eq, hde]
  ·
    have h1 : d 0 = PowerSeries.constantCoeff ((u ^ m)⁻¹) • e' 0 := by
      rw [hd, smulS_eq_sum hLBe' _ 0 1 (by norm_num)]
      simp
    rw [h1]
    simp only [he']
    rw [zero_add, he_m, smul_smul, PowerSeries.constantCoeff_inv, map_pow, inv_mul_cancel₀
      (pow_ne_zero _ hu0), one_smul]
    congr 2
    rw [← C.cmp_eq T hT (i - 1) y']
    congr 1
    exact Subtype.ext hyl

end Phi

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PtTransRec
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc


set_option maxHeartbeats 800000 in
theorem ptTrans_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => PtTrans ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL hA hl5
  set W := (HW l).W K 1 LL hA.2.2 with hW
  intro ζ ζ' hζ hζ'
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hpl] at hζ hζ'
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA
  have hv : (D.loc l).v LL ((l : ℕ) : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hvO := (D.loc l).v_O LL
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h; rw [h, AddValuation.map_zero] at hv; exact WithTop.top_ne_coe hv

  have hcong : ∀ δ : ↥W.DelF, ∃ a : ℕ,
      ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL
        (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (a : ↥LL.1)) := by
    intro δ
    obtain ⟨g, hg⟩ := W.resΓ_onto δ
    obtain ⟨a, ha, -⟩ := (D.loc l).χQ_cyc (g : GQ l) 1 ((D.loc l).ζQ 1)
      (by rw [pow_one]; exact (Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l).pow_eq_one)
    refine ⟨a, ?_⟩
    have hres := W.χΓ_res g
    have hPD := (D.loc l).PD_χ K g
    rw [← hg, hres, hPD]
    set t : ℚ_[l] := ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ℚ_[l]) with ht
    have hlQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    have e : algebraMap ℚ_[l] ↥LL.1 ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ↥LL.1) =
        ((l : ℕ) : ↥LL.1) * algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) := by
      rw [map_div₀, map_natCast, mul_div_cancel₀ _ hl0, ht, map_sub, map_natCast]
    rw [e, AddValuation.map_mul, hv]
    have hz : ‖t / (l : ℚ_[l])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one (by positivity)]
      have := ha
      simpa [zpow_neg, zpow_one] using this
    have hint : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) ∈ OL LL := by
      have e2 : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) =
          algebraMap ℤ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l]) :=
        (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).symm
      rw [e2]
      exact (algebraMap ℤ_[l] ↥(OL LL) (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).2
    exact le_add_of_nonneg_right ((hvO _).2 hint)
  choose aδ haδ using hcong

  have hvunit : ∀ w : (↥(OL LL))ˣ, (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0 := by
    intro w
    have h1 := (hvO (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))).2 (w : ↥(OL LL)).2
    have h2 := (hvO (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)))).2
      ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2
    have h3 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact le_antisymm (le_trans (le_add_of_nonneg_right h2) h3.le) h1
  have hne : ∀ δ, ((aδ δ : ℕ) : ZMod l) ≠ 0 := by
    intro δ h
    rw [ZMod.natCast_eq_zero_iff] at h
    obtain ⟨c, hc⟩ := h
    have hva : (1 : WithTop ℚ) ≤ (D.loc l).v LL ((aδ δ : ℕ) : ↥LL.1) := by
      rw [hc, Nat.cast_mul, AddValuation.map_mul, hv]
      exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
    have hsum := AddValuation.map_add ((D.loc l).v LL)
      (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (aδ δ : ↥LL.1))
      ((aδ δ : ℕ) : ↥LL.1)
    rw [sub_add_cancel, hvunit] at hsum
    have h1 := haδ δ
    rw [Nat.cast_one] at h1
    exact absurd hsum (not_le.2 (lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_min h1 hva)))
  let U : ↥W.DelF → (ZMod l)ˣ := fun δ => Units.mk0 _ (hne δ)
  have hUinj : Function.Injective U := by
    intro δ δ' h
    have h1 : ((aδ δ : ℕ) : ZMod l) = ((aδ δ' : ℕ) : ZMod l) := congrArg Units.val h
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    set χd := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL))
    set χd' := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ' : ↥(OL LL))

    have hdiff : (1 : WithTop ℚ) ≤ (D.loc l).v LL (χd - χd') := by
      have e : χd - χd' = (χd - (aδ δ : ↥LL.1)) - (χd' - (aδ δ' : ↥LL.1)) +
          ((aδ δ : ↥LL.1) - (aδ δ' : ↥LL.1)) := by ring
      rw [e]
      have hA1 := haδ δ
      have hA2 := haδ δ'
      rw [Nat.cast_one] at hA1 hA2
      refine le_trans (le_min (le_trans (le_min hA1 hA2) (AddValuation.map_sub ((D.loc l).v LL) _ _)) ?_)
        (AddValuation.map_add ((D.loc l).v LL) _ _)

      rcases le_total (aδ δ') (aδ δ) with hle | hle
      · have hd : l ∣ aδ δ - aδ δ' := (Nat.modEq_iff_dvd' hle).1 h1.symm
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = ((aδ δ - aδ δ' : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]
        rw [e2, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
      · have hd : l ∣ aδ δ' - aδ δ := (Nat.modEq_iff_dvd' hle).1 h1
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = -((aδ δ' - aδ δ : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]; ring
        rw [e2, AddValuation.map_neg, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)

    set g := (δ : W.Gam) * (δ' : W.Gam)⁻¹
    have hξ : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = χd * χd'⁻¹ := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      rw [eq_mul_inv_iff_mul_eq₀ hχ'0]
      simp only [χd, χd', g, ← map_mul, ← Units.val_mul, ← map_mul (W.χΓ), inv_mul_cancel_right]
    have hξ1 : (1 : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      have e : χd * χd'⁻¹ - 1 = (χd - χd') * χd'⁻¹ := by field_simp
      rw [hξ, e, AddValuation.map_mul]
      have hinv : (D.loc l).v LL χd'⁻¹ = 0 := by
        have := hvunit (W.χΓ δ')⁻¹
        simpa [χd', map_inv₀] using this
      rw [hinv, add_zero]
      exact hdiff

    obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 δ.2
    obtain ⟨k', hk', hδk'⟩ := (W.DelF_def δ').1 δ'.2
    have hgk : g ^ (k * k') = 1 := by
      simp only [g, mul_pow, inv_pow]
      rw [pow_mul, hδk, one_pow, one_mul, mul_comm k k', pow_mul, hδk', one_pow, inv_one]
    have hξk : (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) ^ (k * k') = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hgk, map_one, Units.val_one, map_one]
    have hl3 : 3 ≤ l := by omega
    have hξeq : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = 1 := by
      by_contra hne1
      exact Formalism.MainNotions.N.Pv.LocalLengthBound.Val.pow_ne_one_of_close ((D.loc l).v LL) (Fact.out : l.Prime) hv hl3
        (k * k') _ (Nat.mul_pos hk hk') hξ1 hne1 hξk
    have hg1 : g = 1 := by
      apply W.χΓ_inj
      rw [map_one]
      apply Units.ext
      apply Subtype.val_injective
      simpa using hξeq
    exact Subtype.ext (mul_inv_eq_one.1 hg1)
  have hUbij : Function.Bijective U := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hUinj, by rw [Fintype.card_coe, hcard, ZMod.card_units]⟩

  obtain ⟨b, hb, hζb⟩ := hζ.eq_pow_of_pow_eq_one hζ'.pow_eq_one
  have hb0 : ((b : ℕ) : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : b = 0 := Nat.eq_zero_of_dvd_of_lt hd hb
    subst this
    rw [pow_zero] at hζb
    exact hζ'.ne_one (Fact.out : l.Prime).one_lt hζb.symm
  obtain ⟨δ, hδ⟩ := hUbij.2 (Units.mk0 _ hb0)
  have h1 : ((aδ δ : ℕ) : ZMod l) = ((b : ℕ) : ZMod l) := congrArg Units.val hδ
  rw [ZMod.natCast_eq_natCast_iff] at h1
  have hpowmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % l) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m l, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  refine ⟨δ, δ.2, aδ δ, ?_, haδ δ⟩
  rw [hpowmod, h1, ← hpowmod, hζb]

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

