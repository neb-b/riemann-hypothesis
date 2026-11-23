module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.MemIntAdelesAndIdealIffSplitEmbeddings
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cpt_incl {D : D7} (Q : Pl D.host.E) (x : D.host.E) :
    cpt (D := D) Q (x ⊗ₜ[D.host.F] 1) = algebraMap D.host.E (Q.adicCompletion D.host.E) x := by
  show (toAd D (x ⊗ₜ[D.host.F] 1)) Q = _
  rw [GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D)]
  rfl

private theorem val_oToS {D : D7} (Q : Pl D.host.E) (a : 𝓞 D.host.E) :
    Valued.v (cpt (D := D) Q (oToS D.host.F D.host.E a : Lev.EAf D)) = Q.intValuation a := by
  have h : (oToS D.host.F D.host.E a : Lev.EAf D) = (a : D.host.E) ⊗ₜ[D.host.F] 1 := rfl
  rw [h, cpt_incl, Formalism.UG.P.levelaf_valued_algebraMap]
  exact Q.valuation_of_algebraMap a

private theorem exists_exact {R : Type} [CommRing R] [IsDedekindDomain R] (Pw : Finset (HeightOneSpectrum R))
    (c : HeightOneSpectrum R → ℕ) :
    ∃ a ∈ ∏ w ∈ Pw, w.asIdeal ^ c w, ∀ w ∈ Pw, w.intValuation a = WithZero.exp (-(c w : ℤ)) := by
  choose x hx hx' using fun w : HeightOneSpectrum R =>
    Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top (c w)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Pw) (fun w => w.asIdeal) (fun w => c w + 1)
    (fun w _ => w.prime) (fun i _ j _ h e => h (HeightOneSpectrum.ext e)) (fun w => x w.1)
  have h1 : ∀ w ∈ Pw, y ∈ w.asIdeal ^ c w := fun w hw => by
    have := add_mem (Ideal.pow_le_pow_right (Nat.le_succ _) (hy w hw)) (hx w)
    rwa [sub_add_cancel] at this
  have h2 : ∀ w ∈ Pw, y ∉ w.asIdeal ^ (c w + 1) := fun w hw h => hx' w (by
    have := sub_mem h (hy w hw)
    rwa [sub_sub_cancel] at this)
  refine ⟨y, ?_, fun w hw => le_antisymm ((w.intValuation_le_pow_iff_mem _ _).2 (h1 w hw)) ?_⟩
  · rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp only [Ideal.mem_iInf]
      exact h1
    · intro P _ Q _ hPQ
      exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ).pow
  · have h3 := h2 w hw
    rw [← w.intValuation_le_pow_iff_mem, not_le] at h3
    have h0 : w.intValuation y ≠ 0 := (lt_of_le_of_lt zero_le h3).ne'
    rw [← WithZero.exp_log h0] at h3 ⊢
    rw [WithZero.exp_lt_exp] at h3
    rw [WithZero.exp_le_exp]
    push_cast at h3
    omega

private theorem le_of_mem_map {O S K Γ : Type} [CommRing O] [CommRing S] [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (f : O →+* S) (φ : S →+* K) (v : Valuation K Γ) (I : Ideal O) (γ : Γ) (h1 : ∀ s, v (φ s) ≤ 1)
    (h2 : ∀ a ∈ I, v (φ (f a)) ≤ γ) : ∀ s ∈ I.map f, v (φ s) ≤ γ := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha, rfl⟩ := hs
    exact h2 a ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' (h1 a) hx).trans_eq (one_mul _)

private theorem val_le_one {D : D7} (w : Pl D.host.E) (s : OA D) : Valued.v (cpt (D := D) w s.1) ≤ 1 := by
  obtain ⟨s, hs⟩ := s
  have := (mem_OA_iff s).1 hs w
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem val_le_of_mem {D : D7} (w : Pl D.host.E) (I : Ideal (𝓞 D.host.E)) (γ : WithZero (Multiplicative ℤ))
    (h2 : ∀ a ∈ I, w.intValuation a ≤ γ) (z : Lev.EAf D) (h : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hI : (⟨z, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I) : Valued.v (cpt (D := D) w z) ≤ γ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* w.adicCompletion D.host.E,
      ∀ s, φ s = cpt (D := D) w s.1 := ⟨(cpt (D := D) w).comp (OA D).subtype, fun _ => rfl⟩
  have := le_of_mem_map (oToS D.host.F D.host.E) φ Valued.v I γ
    (fun s => by rw [hφ]; exact val_le_one w s) (fun a ha => by rw [hφ, val_oToS]; exact h2 a ha) ⟨z, h⟩ hI
  rwa [hφ] at this

private theorem inId_iff {D : D7} (Pw : Finset (Pl D.host.E)) (c : Pl D.host.E → ℕ) (z : Lev.EAf D)
    (hz : ∀ Q, Q ∉ Pw → cpt (D := D) Q z = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) z ↔
      ∀ w ∈ Pw, Valued.v (cpt (D := D) w z) ≤ WithZero.exp (-(c w : ℤ)) := by
  constructor
  · rintro ⟨h, hI⟩ w hw
    refine val_le_of_mem w _ _ (fun a ha => ?_) z h hI
    rw [w.intValuation_le_pow_iff_mem]
    exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ c w) hw) ha
  · intro h
    obtain ⟨a, ha, hv⟩ := exists_exact Pw c
    have hy : ((a : D.host.E)⁻¹ ⊗ₜ[D.host.F] 1 : Lev.EAf D) * z ∈ OA D := (mem_OA_iff _).2 fun Q => by
      rw [RingHom.map_mul]
      by_cases hQ : Q ∈ Pw
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, cpt_incl,
          Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀]
        have : Q.valuation D.host.E (a : D.host.E) = WithZero.exp (-(c Q : ℤ)) :=
          (Q.valuation_of_algebraMap a).trans (hv Q hQ)
        rw [this, inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)]
        exact h Q hQ
      · rw [hz Q hQ, mul_zero]
        exact zero_mem _
    have e : z = ((oToS D.host.F D.host.E a * ⟨_, hy⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
      refine cpt_ext fun Q => ?_
      have h : (oToS D.host.F D.host.E a : Lev.EAf D) = (a : D.host.E) ⊗ₜ[D.host.F] 1 := rfl
      rw [Subring.coe_mul, h, RingHom.map_mul, RingHom.map_mul, cpt_incl, cpt_incl]
      by_cases hQ : Q ∈ Pw
      · have h0 : (a : D.host.E) ≠ 0 := by
          intro h0
          have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
          have := hv Q hQ
          rw [h1, map_zero] at this
          exact WithZero.exp_ne_zero this.symm
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
      · rw [hz Q hQ, mul_zero, mul_zero]
    rw [e]
    exact ⟨Subtype.property _, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)⟩

private theorem val_unifAt {F : Type} [Field F] [NumberField F] (v : Pl F) :
    Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have e := GlobalTheory.FlipMatch.isEquiv_Fv v
  have h : valuation (Fv F v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  refine le_antisymm ?_ ?_
  · have h1 : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) < 1 := e.lt_one_iff_lt_one.1 (h ▸ uniformizer_lt_one)
    rw [← WithZero.exp_zero] at h1
    exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at hπ
    rw [← hπ, ← e, h]
    exact le_uniformizer_iff.2 (e.lt_one_iff_lt_one.2 (by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))

private theorem val_evW {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    Valued.v (GlobalTheory.BotMatch.evW τ z) = Valued.v (cpt (D := D) (splitPrime τ) z) :=
  GlobalTheory.FlipMatch.valued_complEquiv_symm τ _

theorem UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (c : Pl D.host.E → ℕ) (z : Lev.EAf D), toEAf D ε * z = z →
          (z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ 𝒪[Fv D.host.F (pl i)]) ∧
          (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) z ↔
            ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i) ^ c (splitPrime (τ i)))) := by
  intro D ε Pw hε ι _ pl τ hP _ c z hz
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hε
  have h0 : ∀ Q, Q ∉ Pw → cpt (D := D) Q z = 0 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hz, RingHom.map_mul, map_sum, map_sum, Finset.sum_eq_zero, zero_mul]
    intro P hP
    exact (cpt_of_isIdemAt (hes P hP)).2 Q fun e => hQ (e ▸ hP)
  constructor
  · have h1 : ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ 𝒪[Fv D.host.F (pl i)] ↔
        cpt (D := D) (splitPrime (τ i)) z ∈ (splitPrime (τ i)).adicCompletionIntegers D.host.E := fun i => by
      rw [Valuation.mem_integer_iff, (GlobalTheory.FlipMatch.isEquiv_Fv _).le_one_iff_le_one, val_evW,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    refine (mem_OA_iff z).trans ⟨fun h i => (h1 i).2 (h _), fun h Q => ?_⟩
    by_cases hQ : Q ∈ Pw
    · obtain ⟨i, rfl⟩ := (hP Q).1 hQ
      exact (h1 i).1 (h i)
    · rw [h0 Q hQ]
      exact zero_mem _
  · have h1 : ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈
        GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i) ^ c (splitPrime (τ i))) ↔
        Valued.v (cpt (D := D) (splitPrime (τ i)) z) ≤ WithZero.exp (-(c (splitPrime (τ i)) : ℤ)) := fun i => by
      refine (GlobalTheory.FlipMatch.isEquiv_Fv (pl i) _ _).trans ?_
      rw [val_evW, Units.val_pow_eq_pow_val, map_pow, val_unifAt, ← WithZero.exp_nsmul]
      simp
    refine (inId_iff Pw c z h0).trans ⟨fun h i => (h1 i).2 (h _ ((hP _).2 ⟨i, rfl⟩)), fun h Q hQ => ?_⟩
    obtain ⟨i, rfl⟩ := (hP Q).1 hQ
    exact (h1 i).1 (h i)
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ShellSumEqConstOfTwistEqIndicatorDoubleCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.shellSum_eq_const_of_twist_eq_indicator_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
        ∀ (a : ℕ) (ν : kˣ →* ℂˣ) (z C : ℂ) (φ : Matrix (Fin a) (Fin a) k → ℂ) (g₀ g₁ : GL (Fin a) k),
        (∀ g : GL (Fin a) k, φ g.1 * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) z =
          {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}.indicator (fun _ => C) g) →
        GlobalTheory.SplitFlip.shellSum (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ = C := by
  intro k _ _ _ _ _ _ ϖ hϖ a ν z C φ g₀ g₁ hφ
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := GlobalTheory.SplitFlip.borel_GL
  have hSm : MeasurableSet {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)} :=
    (GlobalTheory.PureMatch.ShellVolume.isOpen_translate g₀ g₁).measurableSet
  have hvol := GlobalTheory.PureMatch.ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁ hϖ
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m},
      GlobalTheory.SplitFlip.shell (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ m.1 =
      (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))).real (GlobalTheory.SplitFlip.shellSet ϖ m.1 ∩
        {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}) • C := by
    intro m
    rw [GlobalTheory.SplitFlip.shell]
    simp_rw [hφ]
    have e1 := MeasureTheory.setIntegral_indicator (μ := GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))
      (s := GlobalTheory.SplitFlip.shellSet ϖ m.1) (f := fun _ => C) hSm
    rw [e1, MeasureTheory.setIntegral_const]
  rw [GlobalTheory.SplitFlip.shellSum]
  simp_rw [hshell]
  rw [← finsum_smul, hvol, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.StdAStdBMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices
open Filter Topology ValuativeRel GlobalTheory.StdPairSB GlobalTheory.StdPairCone

private theorem gfun_lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ν : kˣ →* ℂˣ} {ϖ : kˣ} {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  have h0 : ∀ e : ℕ, ∀ i j, (0 : Matrix (Fin m) (Fin r) k) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ e) := by
    intro e i j
    rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
    simp
  have hfac : ∀ (A : Matrix (Fin m) (Fin m) k) (B : Matrix (Fin m) (Fin r) k),
      gfun ν ϖ c A B = if (∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) then
        gfun ν ϖ n A (0 : Matrix (Fin m) (Fin r) k) else 0 := by
    intro A B
    by_cases hB : ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
    · rw [if_pos hB]
      unfold gfun
      by_cases hA : A.det ≠ 0 ∧ IsGLO A
      · rw [dite_eq_left ⟨hA.1, hA.2, hB⟩, dite_eq_left ⟨hA.1, hA.2, h0 n⟩]
      · rw [dite_eq_right fun h => hA ⟨h.1, h.2.1⟩, dite_eq_right fun h => hA ⟨h.1, h.2.1⟩]
    · rw [if_neg hB]
      unfold gfun
      rw [dite_eq_right fun h => hB h.2.2]
  have h1 : IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
        gfun ν ϖ n q.1 (0 : Matrix (Fin m) (Fin r) k)) :=
    (isLocallyConstant_gfun hϖ hν m r).comp_continuous
      (f := fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
        (q.1, (0 : Matrix (Fin m) (Fin r) k))) (continuous_fst.prodMk continuous_const)
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  rintro ⟨A, B⟩
  have hnh : ∀ x : k, ∀ᶠ y in 𝓝 x, valuation k (y - x) ≤ valuation k ((ϖ ^ c : kˣ) : k) := by
    intro x
    have ht : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds (ϖ ^ c))
  have hev : ∀ᶠ q in 𝓝 (A, B),
      ∀ i j, valuation k ((q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k).2 i j - B i j) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    exact ((continuous_snd.matrix_elem i j).tendsto (A, B)).eventually (hnh (B i j))
  filter_upwards [hev, h1 (A, B)] with q hq hq1
  have hiff : (∀ i j, q.2 i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ↔
      ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    constructor
    · intro h i j
      rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_sub_cancel (q.2 i j) (B i j)]
      exact Valuation.map_sub_le _ (h i j) (hq i j)
    · intro h i j
      rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_add_cancel (q.2 i j) (B i j)]
      exact Valuation.map_add_le _ (hq i j) (h i j)
  show gfun ν ϖ c q.1 q.2 = gfun ν ϖ c A B
  rw [hfac, hfac]
  exact if_congr hiff hq1 rfl

private theorem finiteRing_sq_sub_mul_sq_eq_of_card {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) {n : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (c a a' : ℕ) :
    stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
      stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (gfun_lc hϖ hν c a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j

end SlopeTestRemainingChoices

theorem UpperTheory.stdA_stdB_mem_schwartzBruhat :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∃ m, GlobalTheory.SplitFlip.CondLE ϖ m ν) → ∀ c a a' : ℕ,
        GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ hϖ hν c a a'
  obtain ⟨n, hn⟩ := hν
  exact finiteRing_sq_sub_mul_sq_eq_of_card ν ϖ hϖ hn c a a'
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ThetaOperatorIntertwinesHeisenberg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ v (GlobalTheory.WeilM.schr ψ w Φ) =
      ψ (⅟(2 : R) * (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2)) • GlobalTheory.WeilM.schr ψ (v + w) Φ := by
  funext z
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add,
    Prod.snd_add, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(v.1 ⬝ᵥ w.2)) * invOf_mul_self (2 : R)

private theorem thetaSum_rho_rho' {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U]
    {B : U → U → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Φ : (κ → AF F) → ℂ) (x y : U) :
    GlobalTheory.WeilM.thetaSum F (co.rho ψ x (co.rho ψ y Φ)) =
      ψ (⅟(2 : AF F) * B x y) * GlobalTheory.WeilM.thetaSum F (co.rho ψ (x + y) Φ) := by
  simp only [GlobalTheory.WeilM.Darboux.rho, schr_schr', GlobalTheory.WeilM.thetaSum, map_add (f := _), Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    co.form]

private theorem exists_co' {D : D7} {ε : Bool} {S X : HSp D} {d : ℕ} (e : Fin d ≃ Fin X.rank)
    {Vs : Spc D.host.F D.host.E S.rank} {Ws : Spc D.host.F D.host.E d} (M : Model D.sp.cm.sig Vs Ws)
    (hX : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) 1 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))) (Fin S.rank × Fin d),
      ∀ x, co.e x = M.co.e (ptO (sgn ε S).gram e x) := by
  have hdet : IsUnit (sgn ε S).gram.det := (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hG : ((sgn ε S).gram.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = ((sgn ε S).gram.map (incA D))ᵀ := by
    ext i j
    show cA D (incA D ((sgn ε S).gram i j)) = incA D ((sgn ε S).gram j i)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  have hVJ : Vs.J = -(sgn ε S).gram := by
    rw [hX]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  obtain ⟨G, hGd⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G = (sgn ε S).gram := ⟨_, rfl⟩
  rw [← hGd] at hdet hG hVJ ⊢
  have h1 : G.map (incA D) * (G⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (G⁻¹).map (incA D) * G.map (incA D) = 1 := mul_eq_one_comm.1 h1
  have hp : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), ptO G e x = ((x * (G⁻¹).map (incA D))ᵀ).submatrix id e :=
    fun _ => rfl
  have hr : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), (ptO G e x)ᵀ.submatrix e.symm id * G.map (incA D) = x := fun x => by
    have e1 : (ptO G e x)ᵀ.submatrix e.symm id = x * (G⁻¹).map (incA D) := by
      rw [hp]
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [e1, Matrix.mul_assoc, h2, Matrix.mul_one]
  let T : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ Matrix (Fin X.rank) (Fin S.rank) (AE D) :=
    { toFun := fun u => uᵀ.submatrix e.symm id * G.map (incA D)
      invFun := ptO G e
      left_inv := fun u => by
        rw [hp, Matrix.mul_assoc, h1, Matrix.mul_one]
        ext i j
        simp only [submatrix_apply, transpose_apply, id, Equiv.symm_apply_apply]
      right_inv := hr
      map_add' := fun u v => by rw [← Matrix.add_mul]; rfl }
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
    (X.gram.map (incA D)) (incA D D.host.xi0) h2 hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • G⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _)
    (by rw [hW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co T (fun _ => rfl)
  exact ⟨co, fun x => (congrArg co.e (hr x)).symm.trans (hco _)⟩

theorem UpperTheory.thetaOperator_intertwines_heisenberg :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M →
        (∀ x y : WO (sgn ε S) X, GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (ptO (sgn ε S).gram e x) (ptO (sgn ε S).gram e y) =
          symplO (sgn ε S) X x y) ∧
        (∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (y : WO (sgn ε S) X),
          thO M ψ (sgn ε S).gram e (M.co.rho ψ (ptO (sgn ε S).gram e y) Φ) = heisO ψ (sgn ε S) X y (thO M ψ (sgn ε S).gram e Φ)) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e (Φ + Φ') = thO M ψ (sgn ε S).gram e Φ + thO M ψ (sgn ε S).gram e Φ') ∧
        (∀ (c : ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), thO M ψ (sgn ε S).gram e (c • Φ) = c • thO M ψ (sgn ε S).gram e Φ) ∧
        (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d),
          thO M ψ (sgn ε S).gram e Φ = thO M ψ (sgn ε S).gram e Φ' → Φ = Φ') ∧
        ∀ f : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f ↔
          ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d), thO M ψ (sgn ε S).gram e Φ = f := by
  intro D ψ ε S X d e Bs Vs Ws M hP
  have hψ : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hP.psi ▸ hP.base.std)
  obtain ⟨co, hco⟩ := exists_co' e M hP.JV hP.JW
  have hr : ∀ x, co.rho ψ x = M.co.rho ψ (ptO (sgn ε S).gram e x) := fun x => by
    simp only [GlobalTheory.WeilM.Darboux.rho, hco]
  have hth : ∀ Φ, thO M ψ (sgn ε S).gram e Φ = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := fun Φ => by
    funext x
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, hr]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε S) (T := X) co hψ rfl (one_smul _ _) (fun x => by
    obtain ⟨y, z, h⟩ := hP.good.rat (((x * (sgn ε S).gram⁻¹)ᵀ).submatrix id e)
    refine ⟨y, z, Eq.trans ?_ h⟩
    rw [hco]
    congr 1
    exact (congrArg (fun m => (transpose m).submatrix id e) (Matrix.map_mul (f := incA D))).symm)
  have hs := GlobalTheory.ThetaTransform.symplO_eq_symp (S := sgn ε S) (T := X) (ξ := 1) rfl (one_smul _ _)
  simp only [hth]
  refine ⟨fun x y => ?_, fun Φ y => ?_, h1, GlobalTheory.ThetaTransform.thetaTr_smul co, h2, h3⟩
  · rw [hs, co.form, M.co.form, hco, hco]
  · funext x
    rw [← hr]
    show GlobalTheory.WeilM.thetaSum D.host.F (co.rho ψ x (co.rho ψ y Φ)) = _
    rw [thetaSum_rho_rho', ← hs, GlobalTheory.ThetaTransform.invOf_two_eq]
    rfl
end

