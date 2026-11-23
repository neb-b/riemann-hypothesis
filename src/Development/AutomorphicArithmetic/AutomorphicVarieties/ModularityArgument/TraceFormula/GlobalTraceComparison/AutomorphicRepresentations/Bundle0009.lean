module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0003
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0002
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
public import GroundTheory.AutomorphicForms.AdelicGLn

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDetZero
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem zero_of_powers_compact {G : Type*} [Monoid G] [TopologicalSpace G] (f : G → ℝ) (hf : Continuous f)
    (hm : ∀ x y, f (x * y) = f x + f y) (S : Set G) (hS : IsCompact S) (k : G) (hk : ∀ m : ℕ, k ^ m ∈ S) : f k = 0 := by
  obtain ⟨C, hC⟩ := (hS.image hf).isBounded.exists_norm_le
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ m : ℕ, f (k ^ m) = m * f k := by
    intro m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih]; push_cast; ring
  by_contra hne
  have hpos : 0 < |f k| := abs_pos.2 hne
  obtain ⟨m, hmC⟩ := exists_nat_gt (C / |f k|)
  have hb := hC _ ⟨k ^ m, hk m, rfl⟩
  rw [hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at hb
  rw [div_lt_iff₀ hpos] at hmC
  linarith

private theorem continuous_kI (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (kI E n) := by
  have hu : Continuous (Unitary.toUnits : Kinf E n → _) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  exact GlobalTheory.CuspQuot.continuous_infGL.comp hu

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.detZero_pf :
    DetZero := by
  intro E _ _ _ n
  have hc := DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)
  have hm := DiscreteGroups.T1.G.Dcy.logAbs_det_mul' (E := E) (n := n)
  refine ⟨fun k => ?_, fun K hK k hk => ?_⟩
  · haveI : CompactSpace (Kinf E n) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
    exact zero_of_powers_compact _ hc hm (Set.range (kI E n)) (isCompact_range (continuous_kI E n)) _
      fun m => ⟨k ^ m, map_pow _ _ _⟩
  · exact zero_of_powers_compact _ hc hm (finGL E n '' (K : Set _))
      (hK.image GlobalTheory.BCT.GlobLev.continuous_finGL_ad) _ fun m => ⟨k ^ m, K.pow_mem hk m, map_pow _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFormEx
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

private theorem weight_ex : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
    (∀ s ∈ Set.Ioo (-1 : ℝ) 1, w s ≠ 0) ∧ ∫ s, w s = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.continuous_normed, b.hasCompactSupport_normed, b.nonneg_normed, ?_,
    b.integral_normed⟩
  intro s hs
  have h : s ∈ Function.support (b.normed volume) := by
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.2 hs
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def slabSp (D : Dom E n 0) : Submodule ℂ (GA E n → ℂ) where
  carrier := {f | Slab D f}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl, fun u _ _ => by
    simp only [Pi.zero_apply, zero_mul]
    exact MemLp.zero⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.add_apply, a2, b2]
    · simp only [Pi.add_apply, a3, b3]
    · have h := (a4 u hu hc).add (b4 u hu hc)
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, a4⟩
    refine ⟨a1.const_smul c, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.smul_apply, a2]
    · simp only [Pi.smul_apply, a3]
    · have h := (a4 u hu hc).const_smul c
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem zero_of_ae (hB : Basic) (hA : AeEq) (hn : 1 ≤ n) (D : Dom E n 0) {f : GA E n → ℂ} (hf : Slab D f)
    (h : ∀ᵐ x ∂D.ν, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0) : f = 0 := by
  obtain ⟨hl, hm, -⟩ := hB E n hn
  have hinv : Inv (fun x : H E n 0 => f x.1) := by
    rintro ⟨_, ⟨p, q⟩, rfl⟩ x
    exact hf.2.1 p x.1
  have key := hA E n D (fun x => f x.1) (fun _ => 0) _ (hf.1.comp continuous_fst) continuous_const hinv
    (fun _ _ => rfl) isOpen_Ioo h
  funext g
  have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [hm, hl, neg_add_cancel]
    constructor <;> norm_num
  exact (hf.2.2.1 _ g).symm.trans (key _ h0)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.formEx_pf :
    Basic → AeEq → WtInd → FormEx := by
  intro hB hA hW E _ _ _ n hn D
  obtain ⟨w, wc, ws, w0, wp, w1⟩ := weight_ex
  have uc : Continuous fun s => (w s : ℂ) := Complex.continuous_ofReal.comp wc
  have us : HasCompactSupport fun s => (w s : ℂ) := ws.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have u1 : ∫ s, (w s : ℂ) = 1 := by rw [integral_complex_ofReal, w1, Complex.ofReal_one]
  have hI : ∀ a b : slabSp D, Integrable
      (fun x : H E n 0 => starRingEnd ℂ (a.1 x.1) * b.1 x.1 * (w (ldet x) : ℂ)) D.ν :=
    fun a b => (hW E n hn D a.1 b.1 a.2 b.2 _ uc us).1
  let B : slabSp D →ₗ⋆[ℂ] slabSp D →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun a b => prW D (fun s => (w s : ℂ)) a.1 b.1)
      (fun a a' b => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a' b)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        ring)
      (fun a b b' => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a b')]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring)
  have hBv : ∀ a b, B a b = prW D (fun s => (w s : ℂ)) a.1 b.1 := fun _ _ => rfl
  refine ⟨slabSp D, B, fun _ => Iff.rfl, fun a b => ?_, fun a ha => ?_, fun a b u hu hc => ?_, fun g hg a => ⟨?_, ?_⟩⟩
  · rw [hBv, hBv, prW, prW, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have he : ∀ x : H E n 0, starRingEnd ℂ (a.1 x.1) * a.1 x.1 * (w (ldet x) : ℂ) =
        ((Complex.normSq (a.1 x.1) * w (ldet x) : ℝ) : ℂ) := fun x => by
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    have hi : Integrable (fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x)) D.ν := by
      have h := (hI a a).re
      simp only [he, RCLike.re_to_complex, Complex.ofReal_re] at h
      exact h
    have hnn : 0 ≤ fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x) :=
      fun x => mul_nonneg (Complex.normSq_nonneg _) (w0 _)
    rw [hBv, prW]
    simp only [he]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ha (Subtype.ext ?_)
    refine zero_of_ae hB hA hn D a.2 ?_
    filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hi).1 h0.symm] with x hx hI'
    exact Complex.normSq_eq_zero.1 ((mul_eq_zero.1 hx).resolve_right (wp _ hI'))
  · exact (hW E n hn D a.1 b.1 a.2 b.2 u hu hc).2.1 _ uc us u1
  · exact ((hW E n hn D a.1 a.1 a.2 a.2 _ uc us).2.2 g hg).1
  · intro a' b b' h1 h2
    rw [hBv, hBv, funext h1, funext h2]
    exact ((hW E n hn D a.1 b.1 a.2 b.2 _ uc us).2.2 g hg).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPositionFacts
section
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem cc (w : Pl E) : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) = w := GlobalTheory.EulerTwU.cPl_cPl w

private theorem cont_thF : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

private theorem twist_int (v : Pl E) (x : GL (Fin n) (Af E))
    (h : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x ∈ KGL (GlobalTheory.EulerTw.cPl E v) (n := n)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) ∈ KGL v (n := n) := by
  rw [GlobalTheory.EulerTwU.pc_thF]
  exact GlobalTheory.EulerTwSplit.theta_mem _ (conjLoc_spec _ v).2.2 h

private theorem twist_int_iff (v : Pl E) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) ∈ KGL v (n := n) ↔
      GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x ∈ KGL (GlobalTheory.EulerTw.cPl E v) (n := n) := by
  refine ⟨fun h => ?_, twist_int v x⟩
  have h1 : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v))) (thF E n x) ∈
      KGL (GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v)) (n := n) := by
    rw [cc]; exact h
  have h2 := twist_int (GlobalTheory.EulerTw.cPl E v) (thF E n x) h1
  rwa [GlobalTheory.EulerTwU.thF_thF] at h2

private theorem twist_away {u v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ u) (a : GLw n u) :
    GeneralLinearGroup.map (pLoc E v) (thF E n (locGL E n u a)) = 1 := by
  have e : GeneralLinearGroup.map (n := Fin n) (conjLoc (IsCMField.complexConj E).toRingEquiv v) 1 = 1 := map_one _
  rw [GlobalTheory.EulerTwU.pc_thF, pLoc_locGL_of_ne h]
  exact (congrArg (thetaGL n (RingHom.id _)) e).trans (map_one _)

private theorem bad_finite (g : GL (Fin n) (Af E)) :
    {v : Pl E | GeneralLinearGroup.map (pLoc E v) g ∉ KGL v (n := n)}.Finite := by
  have h1 : ∀ x : Af E, ∀ᶠ v : Pl E in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E :=
    fun x => x.2.mono fun _ h => h
  have h2 := eventually_all.2 fun i => eventually_all.2 fun j => h1 (g.1 i j)
  have h3 := eventually_all.2 fun i => eventually_all.2 fun j => h1 ((g⁻¹).1 i j)
  have h4 : ∀ᶠ v : Pl E in cofinite, GeneralLinearGroup.map (pLoc E v) g ∈ KGL v (n := n) := by
    filter_upwards [h2, h3] with v a b
    rw [GlobalTheory.EulerTwRestr.mem_KGL_iff]
    exact ⟨fun i j => a i j, fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact b i j⟩
  exact eventually_cofinite.1 h4

private theorem comm_loc (w : Pl E) (a : GLw n w) (c : GL (Fin n) (Af E))
    (h : GeneralLinearGroup.map (pLoc E w) c = 1) : Commute (locGL E n w a) c := by
  show locGL E n w a * c = c * locGL E n w a
  refine GlobalTheory.EulerTwU.gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

private theorem qj (w : Pl E) (b : Bool) (a : GLw n w) : qw n w b (jw n w b a) = a := by
  cases b
  · exact pLoc_locGL _ _
  · show GeneralLinearGroup.map (pLoc E w) (thF E n (thF E n (locGL E n w a))) = a
    rw [GlobalTheory.EulerTwU.thF_thF]
    exact pLoc_locGL _ _

private theorem comm_mapFactor_of_absIrr (w : Pl E) (b : Bool) (a : GLw n w) (c : GL (Fin n) (Af E))
    (h : qw n w b c = 1) : Commute (jw n w b a) c := by
  cases b
  · exact comm_loc w a c h
  · have h1 := (comm_loc w a (thF E n c) h).map (thF E n)
    rwa [GlobalTheory.EulerTwU.thF_thF] at h1

private theorem cont_j (w : Pl E) (b : Bool) : Continuous (jw n w b) := by
  cases b
  · exact GlobalTheory.CuspRep.CuspSub.continuous_locGL w
  · exact cont_thF.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

private theorem cont_q (w : Pl E) (b : Bool) : Continuous (qw (E := E) n w b) := by
  cases b
  · exact GlobalTheory.BCT.LocCpt.continuous_mapLoc w
  · exact (GlobalTheory.BCT.LocCpt.continuous_mapLoc w).comp cont_thF

end SlopeTestRemainingChoices

theorem slotFacts_pf : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → SlotBasic := by
  intro hP E _ _ _ n S hS
  obtain ⟨-, hc, -, hs⟩ := hP E
  have hsplit : ∀ w : Pl E, IsSplitAt w ↔ GlobalTheory.EulerTw.cPl E w ≠ w := fun w => (hc w).2
  have hsec : ∀ w : Pl E, w ∈ S → GlobalTheory.EulerTw.cPl E w ∈ S → GlobalTheory.EulerTw.cPl E w = w :=
    fun w => (hs S hS w).2
  have hor : ∀ w : Pl E, w ∈ S ∨ GlobalTheory.EulerTw.cPl E w ∈ S := fun w => (hs S hS w).1
  refine ⟨GlobalTheory.EulerTwU.thF_thF, cont_thF, fun w b => ⟨cont_j w b, cont_q w b, qj w b, comm_mapFactor_of_absIrr w b⟩,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, bi⟩ ⟨k, bk⟩ ⟨hi, hi'⟩ ⟨hk, hk'⟩ hne a
    have hik : bi = bk → i ≠ k := fun e e' => hne (by rw [e, e'])
    cases bi <;> cases bk
    · exact pLoc_locGL_of_ne (hik rfl).symm a
    · refine twist_away (fun e => ?_) a
      have e0 : GlobalTheory.EulerTw.cPl E k = i := e
      have hi0 : i ∈ S := hi
      have hk0 : k ∈ S := hk
      exact (hsplit k).1 (hk' rfl) (hsec k hk0 (e0 ▸ hi0))
    · refine twist_away (fun e => ?_) a
      have e0 : GlobalTheory.EulerTw.cPl E k = i := e
      have hi0 : i ∈ S := hi
      have hk0 : k ∈ S := hk
      have e' : GlobalTheory.EulerTw.cPl E i = k := by rw [← e0, cc]
      exact (hsplit i).1 (hi' rfl) (hsec i hi0 (e' ▸ hk0))
    · show GeneralLinearGroup.map (pLoc E k) (thF E n (thF E n (locGL E n i a))) = 1
      rw [GlobalTheory.EulerTwU.thF_thF]
      exact pLoc_locGL_of_ne (hik rfl).symm a
  · intro g
    refine (((bad_finite g).prod (Set.finite_singleton false)).union
      ((bad_finite (thF E n g)).prod (Set.finite_singleton true))).subset ?_
    rintro ⟨w, b⟩ h
    cases b
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩
  · intro w hw g
    have hcw : GlobalTheory.EulerTw.cPl E w = w := by
      by_contra h
      exact hw ((hsplit w).2 h)
    have h1 := twist_int_iff w g
    rw [hcw] at h1
    exact h1
  · intro g
    have hL : g ∈ Lev S (fun w : Pl E => KGL w (n := n)) ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 g ∈ KGL i.1 (n := n) := by
      simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
    have hK : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ KGL w (n := n) := by
      simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
    rw [hL, hK]
    constructor
    · intro h w
      by_cases hw : w ∈ S
      · exact h (w, false) ⟨hw, by simp⟩
      · have hw' : GlobalTheory.EulerTw.cPl E w ∈ S := (hor w).resolve_left hw
        have hne : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) ≠ GlobalTheory.EulerTw.cPl E w := by
          rw [cc]
          exact fun e => hw (e ▸ hw')
        have h1 := (twist_int_iff (n := n) (GlobalTheory.EulerTw.cPl E w) g).1
          (h (GlobalTheory.EulerTw.cPl E w, true) ⟨hw', fun _ => (hsplit _).2 hne⟩)
        rwa [cc] at h1
    · rintro h ⟨w, b⟩ -
      cases b
      · exact h w
      · exact twist_int w g (h _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTensType
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open PositivityTheory.Rg.BcB.CG.prime_not_mem_section_base_place
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem uAt_mul' (v : InfinitePlace E) (k k' : Kinf E n) : uAt v (k * k') = uAt v k * uAt v k' := by
  apply Subtype.ext
  show ((k * k' : Kinf E n) : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) =
    (k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) * (k' : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v)
  rw [← Matrix.map_mul]
  rfl

private theorem coef_mul' (M : Mods E n) (I L : IxA M) (x k : Kinf E n) :
    coef M I L (x * k) = ∑ m : IxA M, coef M I m k * coef M m L x := by
  have h1 : ∀ v, ent (M v) ((M v).ρ (uAt v (x * k)⁻¹)) (I v) (L v) =
      ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) := by
    intro v
    rw [_root_.mul_inv_rev, uAt_mul', map_mul, PMul.ent_mul]
  calc coef M I L (x * k)
      = ∏ v, ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) :=
        Finset.prod_congr rfl fun v _ => h1 v
    _ = ∑ m ∈ Fintype.piFinset fun _ => Finset.univ,
          ∏ v, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) (m v) * ent (M v) ((M v).ρ (uAt v x⁻¹)) (m v) (L v) :=
        Finset.prod_univ_sum _ _
    _ = ∑ m : IxA M, coef M I m k * coef M m L x := by
        simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, coef]

private theorem rinv_Wsp (M : Mods E n) : RInv (Wsp M) := by
  intro f hf k
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨p, rfl⟩ := h
    have e : (fun x => coef M p.1 p.2 (x * k)) = ∑ m : IxA M, coef M p.1 m k • coef M m p.2 := by
      funext x
      simp only [coef_mul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show (fun x => coef M p.1 p.2 (x * k)) ∈ Wsp M
    rw [e]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m, p.2), rfl⟩)
  | zero => exact (Wsp M).zero_mem
  | add a b _ _ ha hb => exact (Wsp M).add_mem ha hb
  | smul c a _ ha => exact (Wsp M).smul_mem c ha

private theorem level_open_compact {b : ℕ} (U : Subgroup (Hf E n b)) (hU : IsOpen (U : Set (Hf E n b))) :
    IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) ∧
      IsCompact ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) := by
  have h1 : IsOpen ((U.comap (MonoidHom.inl _ _) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    hU.preimage (Continuous.prodMk_left 1)
  have h2 : IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    h1.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  exact ⟨h2, (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h2) Set.inter_subset_right⟩

end SlopeTestRemainingChoices

theorem tensType_pf : TensType := by
  intro E _ _ _ n μa μb _ _ Ma Mb κ ka kb va vb R ψ U ha hb hψ hU hlev i j
  obtain ⟨hKo, hKc⟩ := level_open_compact U hU
  refine ⟨tens_cs ha hb hψ i j, _, Wsp Ma, hKo, hKc, fd_Wsp Ma, rinv_Wsp Ma, fun u hu y => ?_, fun y => ?_⟩
  · have e1 : entA ka i.1.1 j.1.1 (finGL E n u * y.1) = entA ka i.1.1 j.1.1 y.1 := by
      have h := entA_fin ka i.1.1 j.1.1 u⁻¹ y.1
      rwa [map_inv, inv_inv] at h
    have e2 : hFin ((finGL E n u, 1) * y) = ((u, 1) : Hf E n 0) * hFin y := by
      show (gFin (finGL E n u * y.1), gFin (1 * y.2)) = (u * gFin y.1, 1 * gFin y.2)
      rw [map_mul, gFin_finGL, one_mul, one_mul]
    show entA ka i.1.1 j.1.1 (finGL E n u * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
        ψ i.2 j.2 (hFin ((finGL E n u, 1) * y)) = entA ka i.1.1 j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)
    rw [e1, one_mul, e2, hlev i.2 j.2 (u, 1) hu.1 (hFin y)]
  · have e : (fun k : Kinf E n => tens ka kb ψ i j (((kI E n k)⁻¹, 1) * y)) =
        ∑ L : IxA Ma, (entA ka L j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)) • coef Ma i.1.1 L := by
      funext k
      have e2 : hFin (((kI E n k)⁻¹, 1) * y) = hFin y := by
        have h1 : gFin (infGL E n (Unitary.toUnits k)) = 1 := pFin_infGL _
        show (gFin ((infGL E n (Unitary.toUnits k))⁻¹ * y.1), gFin (1 * y.2)) = (gFin y.1, gFin y.2)
        rw [map_mul, map_inv, h1, inv_one, one_mul, one_mul]
      show entA ka i.1.1 j.1.1 ((infGL E n (Unitary.toUnits k))⁻¹ * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
          ψ i.2 j.2 (hFin (((kI E n k)⁻¹, 1) * y)) = _
      rw [entA_inf ha, one_mul, e2, Finset.sum_mul, Finset.sum_mul]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun L _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun L _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i.1.1, L), rfl⟩)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

