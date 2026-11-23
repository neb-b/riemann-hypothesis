module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalThetaCorrespondenceInertPlaceOfHowe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.CorrInert

variable {D : D7}

theorem exists_idem_of_conj_eq (P : Pl D.host.E) (hP : conjPl P = P) : ∃ e, IsPrimeIdem P e e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hc : P = GlobalTheory.IdemSupport.cP P := by
    refine (GlobalTheory.IdemSupport.isConjPl_iff P P).1 fun c hc => ⟨GlobalTheory.IdemSupport.cO D c, ?_, rfl⟩
    have h1 : GlobalTheory.IdemSupport.cO D c ∈ (conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  rcases h with ⟨h, -⟩ | h
  · exfalso
    have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h
    have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
    rw [← hc] at hd'
    have h2 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
    rw [h.1.2.1, GlobalTheory.IdemSupport.ev_zero, hd.2.1, hd'.2.1, one_mul] at h2
    exact zero_ne_one h2
  · obtain ⟨rfl, h⟩ := h
    exact ⟨f, Or.inr ⟨rfl, h⟩⟩

theorem suppF_of_mem_rep (V : HSp D) {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f) {d : List ℤ}
    {γ : GA D V} (h : γ ∈ rep V P d) : SuppF V f γ := by
  unfold rep at h
  split_ifs at h with hl
  · obtain ⟨e', f', -, -, -, he', -, -, -, -, -, -, -, hs, -⟩ := hl.choose_spec
    obtain ⟨-, rfl⟩ :=
      ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f he).2.2.2.1 e' f' he'
    exact hs γ h
  · exact absurd h (Finset.notMem_empty _)

theorem exists_pullback {V : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (π : GA D V →* Module.End ℂ W) {H : Type} (ι : H → GA D V)
    (hι : ∀ g, SuppF V f g → ∃ h, ι h = g) (c : List ℤ →₀ ℂ) :
    ∃ b : H →₀ ℂ, ∀ u, (b.sum fun h z => z • π (ι h) u) = opOf π P c u := by
  have hm : opOf π P c ∈ Submodule.span ℂ (Set.range fun h => π (ι h)) := by
    refine Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => ?_)
    obtain ⟨h, rfl⟩ := hι γ (suppF_of_mem_rep V he hγ)
    exact Submodule.subset_span ⟨h, rfl⟩
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
  refine ⟨b, fun u => ?_⟩
  rw [← hb]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

theorem half {S T : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (πS : GA D S →* Module.End ℂ W) (πT : GA D T →* Module.End ℂ W)
    (comm : ∀ g h u, πS g (πT h u) = πT h (πS g u)) (Vac : W → Prop)
    (fixS : ∀ u, Vac u → ∀ k ∈ hyp S P, πS k u = u) (fixT : ∀ u, Vac u → ∀ k ∈ hyp T P, πT k u = u)
    {GS GT : Type} (ιS : GS → GA D S) (ιT : GT → GA D T) (hS : ∀ g, SuppF S f (ιS g))
    (hT : ∀ g, SuppF T f g → ∃ h, ιT h = g)
    (howe : ∀ bT : GT →₀ ℂ, (∀ u, Vac u → ∀ k ∈ hyp T P,
        πT k (bT.sum fun h z => z • πT (ιT h) u) = bT.sum fun h z => z • πT (ιT h) u) →
      ∃ bS : GS →₀ ℂ, ∀ u, Vac u → (bT.sum fun h z => z • πT (ιT h) u) = bS.sum fun g z => z • πS (ιS g) u)
    (cT : List ℤ →₀ ℂ) : ∃ cS, ∀ u, Vac u → opOf πS P cS u = opOf πT P cT u := by
  classical
  obtain ⟨bT, hb⟩ := exists_pullback he πT ιT hT cT
  obtain ⟨bS, hbS⟩ := howe bT fun u hu k hk => by
    rw [hb]
    exact (_root_.GlobalTheory.SphLabelOps.label_operators T P).2.1 cT W πT u (fixT u hu) k hk
  obtain ⟨cS, hc⟩ := _root_.GlobalTheory.SphAvg.fixed_comb_eq_opOf S P e f he (Finsupp.mapDomain ιS bS) fun g hg => by
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact hS g'
  refine ⟨cS, fun u hu => ?_⟩
  have e1 : ((Finsupp.mapDomain ιS bS).sum fun g z => z • πS g u) = bT.sum fun h z => z • πT (ιT h) u := by
    rw [hbS u hu]
    exact Finsupp.sum_mapDomain_index (h := fun g (z : ℂ) => z • πS g u) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)
  rw [← hc W πS u (fixS u hu) fun k hk => ?_, e1, hb]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, comm, fixS u hu k hk]

theorem coe_sum_smul {W : Type} [AddCommGroup W] [Module ℂ W] {M : Submodule ℂ W} {H : Type} (b : H →₀ ℂ) (v : H → M) :
    ((b.sum fun h z => z • v h : M) : W) = b.sum fun h z => z • (v h : W) := by
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]

theorem sphCorr_of_inert : HoweUnram → ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P = P → VacFix ψ om P → SphCorr ψ om P := by
  intro hH D ψ S T χS χT om P hW hP hV
  obtain ⟨e, he⟩ := exists_idem_of_conj_eq P hP
  obtain ⟨ϖ, σ, q, δ, JS, JT, ψ', M, ρ, ω, ιS, ιT, hL, rS, rT, kS, kT, hω, hM, hvac⟩ :=
    _root_.GlobalTheory.InertLoc.exists_locPair ψ S T χS χT om P hW hP hV e he
  haveI : CharZero (P.adicCompletion D.host.E) := algebraRat.charZero _
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Hk3.howe_all_vacua hH _ ϖ σ q δ _ _ JS JT ψ' M ρ ω hL
  have oneS : (1 : GA D S) ∈ hyp S P := by
    rw [← map_one ιS, kS]; exact one_mem _
  have oneT : (1 : GA D T) ∈ hyp T P := by
    rw [← map_one ιT, kT]; exact one_mem _
  have comm : ∀ g h u, (om.comp (MonoidHom.inl _ _)) g ((om.comp (MonoidHom.inr _ _)) h u) =
      (om.comp (MonoidHom.inr _ _)) h ((om.comp (MonoidHom.inl _ _)) g u) := by
    intro g h u
    change (om (g, 1) * om (1, h)) u = (om (1, h) * om (g, 1)) u
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]
  have fixS : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp S P, (om.comp (MonoidHom.inl _ _)) k u = u :=
    fun u hu k hk => hV u hu k hk 1 oneT
  have fixT : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp T P, (om.comp (MonoidHom.inr _ _)) k u = u :=
    fun u hu k hk => hV u hu 1 oneS k hk
  have ωS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inl _ _)) (ιS g) m := by
    intro g m
    rw [hω, map_one]; rfl
  have ωT : ∀ h (m : M), ((ω (1, h) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inr _ _)) (ιT h) m := by
    intro g m
    rw [hω, map_one]; rfl
  refine ⟨hV, fun cT => ?_, fun cS => ?_⟩
  · refine half he _ _ comm (IsVacAt ψ S T P) fixS fixT ιS ιT (fun g => (rS _).1 ⟨g, rfl⟩)
      (fun g hg => (rT g).2 hg) (fun bT hb => ?_) cT
    obtain ⟨bS, hbS⟩ := h1 bT fun s hs k hk => by
      apply Subtype.ext
      rw [ωT, coe_sum_smul]
      simp only [ωT]
      exact hb s ((hvac s).1 hs) _ ((kT k).2 hk)
    refine ⟨bS, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbS ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this
  · suffices h : ∃ cT, ∀ u, IsVacAt ψ S T P u →
        opOf (om.comp (MonoidHom.inr _ _)) P cT u = opOf (om.comp (MonoidHom.inl _ _)) P cS u from
      h.imp fun cT h u hu => (h u hu).symm
    refine half he _ _ (fun g h u => (comm h g u).symm) (IsVacAt ψ S T P) fixT fixS ιT ιS (fun g => (rT _).1 ⟨g, rfl⟩)
      (fun g hg => (rS g).2 hg) (fun bS hb => ?_) cS
    obtain ⟨bT, hbT⟩ := h2 bS fun s hs k hk => by
      apply Subtype.ext
      rw [ωS, coe_sum_smul]
      simp only [ωS]
      exact hb s ((hvac s).1 hs) _ ((kS k).2 hk)
    refine ⟨bT, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbT ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this

end GlobalTheory.Hk3.CorrInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegral
section
noncomputable section

namespace GlobalTheory.ShortModelTheta

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso epOf)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.L2.KerInert.BeCob (eLT vLT ThetaTie ShortIso)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

section IntPS

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_ps' {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem ips' {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) (k : ℕ) :
    ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

theorem ips_add' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f + g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (ips' hg k))

theorem ips_sub' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f - g : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ips' hf k) (by rw [norm_neg]; exact ips' hg k))

theorem ips_Cmul' {c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K)) :
    Integral ((PowerSeries.C c * f : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (ips' hf k)

theorem ips_X' : Integral ((PowerSeries.X : PowerSeries K) : MvPowerSeries Unit K) := by
  apply integral_ps'; intro k
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem ips_mul' {f g : PowerSeries K} (hf : Integral (f : MvPowerSeries Unit K))
    (hg : Integral (g : MvPowerSeries Unit K)) : Integral ((f * g : PowerSeries K) : MvPowerSeries Unit K) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hf hg

end IntPS

theorem shortIso_holds : ShortIso := by
  intro K _ _ _ h2 h3 W hW
  obtain ⟨hxI, hx1, hA, -⟩ := Formalism.L2.Th1.A.bridgeCurve K W hW
  obtain ⟨hB, -⟩ := Formalism.L2.Th1.A.bridgeCurve3 K W hW
  obtain ⟨hnum, hden⟩ := Formalism.L2.Th1.A.wpNumEq K W
  rw [← Formalism.L2.Th1.A.uSerEq K _ _]
  obtain ⟨hl0, hl1, -, -⟩ := Formalism.L2.Th1.A.logSpec K W
  have hlS : PowerSeries.HasSubst (Formalism.L2.Th1.A.logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hl_ne : Formalism.L2.Th1.A.logSer W ≠ 0 := by
    intro h; rw [h, map_zero] at hl1; exact zero_ne_one hl1
  set lW := Formalism.L2.Th1.A.logSer W with hlW
  set P := Formalism.L2.Th1.A.wpReg W with hP
  set xs := Formalism.L2.Th1.A.xS W with hxs
  set N : PowerSeries K := xs + PowerSeries.C (W.b₂ / 12) * PowerSeries.X ^ 2 with hN
  set D : PowerSeries K := xs - PowerSeries.C (W.a₁ / 2) * PowerSeries.X * xs -
    PowerSeries.C (W.a₃ / 2) * PowerSeries.X ^ 3 with hD
  have hD1 : PowerSeries.constantCoeff D = 1 := by
    rw [hD]; simp [hx1]
  have hden1 : PowerSeries.constantCoeff (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) ≠ 0 := by
    rw [hden]; simp
  have hsn : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 + lW ^ 2 * PowerSeries.subst lW P := by
    rw [hnum, PowerSeries.subst_add hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_pow hlS,
      PowerSeries.subst_X hlS, ← PowerSeries.coe_substAlgHom hlS, map_one]
  have hsd : PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative (R := K) P) := by
    rw [hden, PowerSeries.subst_sub hlS, PowerSeries.subst_mul hlS, PowerSeries.subst_mul hlS,
      PowerSeries.subst_pow hlS, PowerSeries.subst_X hlS, PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom hlS,
      map_one]
    rfl
  set I := PowerSeries.subst lW (Formalism.L2.Th1.CM.uSer (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) with hI
  have hIB : I * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpDen (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) =
      lW * PowerSeries.subst lW (Formalism.L2.Th1.CM.wpNum (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W)) := by
    rw [hI, ← PowerSeries.subst_mul hlS]
    unfold Formalism.L2.Th1.CM.uSer
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hden1, mul_one, PowerSeries.subst_mul hlS, PowerSeries.subst_X hlS]
  rw [hsn, hsd] at hIB
  have hID : I * D = PowerSeries.X * N := by
    have h3ne : lW ^ 3 ≠ 0 := pow_ne_zero 3 hl_ne
    apply mul_left_cancel₀ h3ne
    have e2 : (2 : K) ≠ 0 := two_ne_zero
    have hB' : PowerSeries.X ^ 3 * (1 - PowerSeries.C (1 / 2 : K) * lW ^ 3 * PowerSeries.subst lW (PowerSeries.derivative (R := K) P)) =
        lW ^ 3 * D := by
      have hh : (PowerSeries.C (1 / 2 : K) : PowerSeries K) * (2 : PowerSeries K) = 1 := by
        rw [show (2 : PowerSeries K) = PowerSeries.C (2 : K) from (map_ofNat _ 2).symm, ← map_mul]; norm_num
      rw [hD]
      have ha1 : (PowerSeries.C (W.a₁ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₁ := by
        rw [← map_mul]; ring_nf
      have ha3 : (PowerSeries.C (W.a₃ / 2) : PowerSeries K) = PowerSeries.C (1 / 2 : K) * PowerSeries.C W.a₃ := by
        rw [← map_mul]; ring_nf
      rw [ha1, ha3]
      linear_combination (-(PowerSeries.C (1 / 2 : K) : PowerSeries K)) * hB -
        (PowerSeries.X ^ 3 - lW ^ 3 * xs) * hh
    linear_combination PowerSeries.X ^ 3 * hIB - I * hB' + lW * PowerSeries.X * hA
  have hDinv : D⁻¹ * D = 1 := PowerSeries.inv_mul_cancel _ (by rw [hD1]; exact one_ne_zero)
  have hIe : I = PowerSeries.X * N * D⁻¹ := by
    calc I = I * D * D⁻¹ := by rw [mul_assoc, mul_comm D, hDinv, mul_one]
      _ = _ := by rw [hID]
  rw [hIe]
  have h12 : ‖(12 : K)‖ = 1 := by
    rw [show (12 : K) = 2 * 2 * 3 by norm_num, norm_mul, norm_mul, h2, h3]; norm_num
  have hi1 : ‖W.a₁‖ ≤ 1 := hW.1
  have hi2 : ‖W.a₂‖ ≤ 1 := hW.2.1
  have hi3 : ‖W.a₃‖ ≤ 1 := hW.2.2.1
  have hb2 : ‖W.b₂ / 12‖ ≤ 1 := by
    rw [norm_div, h12, div_one, WeierstrassCurve.b₂]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi1
    · rw [norm_mul]
      refine mul_le_one₀ ?_ (norm_nonneg _) hi2
      rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have ha12 : ‖W.a₁ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi1
  have ha32 : ‖W.a₃ / 2‖ ≤ 1 := by rw [norm_div, h2, div_one]; exact hi3
  have hX2 : Integral (((PowerSeries.X : PowerSeries K) ^ 2 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_two]; exact ips_mul' ips_X' ips_X'
  have hX3 : Integral (((PowerSeries.X : PowerSeries K) ^ 3 : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [pow_succ]; exact ips_mul' hX2 ips_X'
  have hNI : Integral ((N : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hN]; exact ips_add' hxI (ips_Cmul' hb2 hX2)
  have hDI : Integral ((D : PowerSeries K) : MvPowerSeries Unit K) := by
    rw [hD]
    exact ips_sub' (ips_sub' hxI (ips_mul' (ips_Cmul' ha12 ips_X') hxI)) (ips_Cmul' ha32 hX3)
  have hDiI : Integral ((D⁻¹ : PowerSeries K) : MvPowerSeries Unit K) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hDI hD1 hDinv
  exact ips_mul' (ips_mul' ips_X' hNI) hDiI

theorem exists_witt_series_inverse_formalGroup_iso_short {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral' {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso_short hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem norm_nat_one' {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (m : ℕ) (hm1 : 0 < m) (hm : m < 5) :
    ‖(m : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  refine Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) ?_
  intro h
  have := Nat.le_of_dvd hm1 h
  omega

theorem thetaTie_holds : ThetaTie := by
  intro l _ h5 g hLT hOk n
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst (vLT hLT) := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  have hgl : g.l = Formalism.L2.Th1.A.logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer g.W) = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hvl : PowerSeries.subst (vLT hLT) (Formalism.L2.Th1.A.logSer g.W) = PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 2 (by norm_num) (by norm_num)
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by exact_mod_cast norm_nat_one' h5 3 (by norm_num) (by norm_num)
  have hiso := shortIso_holds ℂ_[l] h2 h3 g.W (Formalism.L2.KerInert.Dict.intModel_of_ok hOk)
  have hθ : thetaS l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) (eLT hLT)⁻¹ =
      MvPowerSeries.subst (fun _ => vLT hLT) (PowerSeries.subst (Formalism.L2.Th1.A.logSer g.W)
        (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)))) := by
    unfold thetaS
    rw [Formalism.L2.Th1.A.uSerEq ℂ_[l] _ _, ← PowerSeries.subst_def,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
  rw [hθ]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun _ => hvcc) (fun _ => integral_ps' (v_integral' hOk hLT)) hiso
    (Finsupp.single () n)

end GlobalTheory.ShortModelTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets

def SplitSet {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AA ≠ ⊥ ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧ IsCoprime ϖ (X.conjO ϖ) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P ∈ S

def TranslateInt {X : Fields} (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (π : X.E) (κ : ℂ) (e : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ (s : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * π) • s ∈ per A N N' →
    GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (κ * jetC A.cD (Wx A s (A.e a b N N')) e)

def PlaceAbove : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)),
    (p : 𝓞 K) ∈ w.asIdeal →
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k : K, GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (σ k) ↔ w.valuation K k ≤ 1

def TypePrimeBadPrimesLevelsHypotheses : Prop :=
  ∀ (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ)
    (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), HostTie EX → IsSel (recFields D) sel →
    ∀ (i : Fin 2) (u : (recPrimes EX).Word) (mu : Tup (recFields D).F (recFields D).E (recFields D).K (badS D))
      (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel mu)), cst.Ok →
    ∀ a b : ℕ, (ambOf (recSeam D) B χ cD).LaHyp a b ∅ → (ambOf (recSeam D) B χ cD).ESmooth a b →
      SplitSet (ambOf (recSeam D) B χ cD) a b (Sall sel mu u) ((recFields D).conjO ((recPrimes EX).piG i))
        ((recPrimes EX).g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ (recPrimes EX).g i ∣ cBof sel mu cst u

end GlobalTheory.DatumJets
end
end

