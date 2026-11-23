module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Step1KillXList
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0028
public import Formalism.SharpRestriction.LevelLetterCocycles.PullbackLevelTwoToOne
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CoprimeFrobeniusUniformizerPowers
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

open Formalism.MainNotions.ArcLiftingSetup in
theorem ps_zero : ps W 0 = W.π₀ + lA W := by
  simp [ps, qA]

open Formalism.MainNotions.ArcLiftingSetup in
theorem ps_succ (s : ℕ) : ps W (s + 1) = W.φA (ps W s) := by
  simp only [ps, pow_succ', AlgHom.mul_apply]

theorem hs_succ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (a : ZMod n) (e s : ℕ) :
    A.Hs a (e + 1) (s + 1) = A.Hs (a - 1) e s := by
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
  rw [show a - ((s + 1 : ℕ) : ZMod n) = a - 1 - (s : ZMod n) by push_cast; ring,
    show e + 1 - (s + 1) = e - s by omega]

def LamUp (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) : LetA O n :=
  W.φA (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + (e : ZMod n)) e)

theorem lam_succ (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e : ℕ) :
    Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) =
      Formalism.MainNotions.ArcLiftingSetup.ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 * LamUp W A c' e := by
  unfold LamUp
  conv_lhs => unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, ← ps_succ, hs_succ]
  congr 2
  push_cast; ring

def Cop (x z : LetA O n) : Prop :=
  ∃ m : ℕ, ∃ r ∈ W.AΔ, ∃ s ∈ W.AΔ, Formalism.MainNotions.ArcLiftingSetup.lA W ^ m = r * x + s * z

theorem lA_mem (m : ℕ) : Formalism.MainNotions.ArcLiftingSetup.lA W ^ m ∈ W.AΔ :=
  W.AΔ.pow_mem (W.AΔ.natCast_mem _) m

theorem cop_symm {x z : LetA O n} (h : Cop W x z) : Cop W z x := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, s, hs, r, hr, by rw [e]; ring⟩

theorem cop_mul {x y z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ)
    (h1 : Cop W x z) (h2 : Cop W y z) : Cop W (x * y) z := by
  obtain ⟨a, r, hr, s, hs, e1⟩ := h1
  obtain ⟨b, r', hr', s', hs', e2⟩ := h2
  refine ⟨a + b, r * r', W.AΔ.mul_mem hr hr', r * x * s' + s * r' * y + s * s' * z, ?_, ?_⟩
  · have hy : r' * y ∈ W.AΔ := by
      have : r' * y = Formalism.MainNotions.ArcLiftingSetup.lA W ^ b - s' * z := by rw [e2]; ring
      rw [this]; exact W.AΔ.sub_mem (lA_mem W b) (W.AΔ.mul_mem hs' hz)
    refine W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hr hx) hs') ?_)
      (W.AΔ.mul_mem (W.AΔ.mul_mem hs hs') hz)
    rw [mul_assoc]; exact W.AΔ.mul_mem hs hy
  · rw [pow_add, e1, e2]; ring

theorem cop_pow {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : Cop W x z) :
    ∀ N : ℕ, Cop W (x ^ N) z := by
  intro N
  induction N with
  | zero => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | succ N ih => rw [pow_succ]; exact cop_mul W (W.AΔ.pow_mem hx N) hz ih h

theorem cop_prod {ι : Type} (s : Finset ι) (x : ι → LetA O n) {z : LetA O n}
    (hx : ∀ i, x i ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : ∀ i ∈ s, Cop W (x i) z) :
    Cop W (∏ i ∈ s, x i) z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, W.AΔ.zero_mem, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    exact cop_mul W (W.AΔ.prod_mem fun i _ => hx i) hz (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      (h a (Finset.mem_insert_self a s))

theorem crt {x z : LetA O n} (hx : x ∈ W.AΔ) (hz : z ∈ W.AΔ) (h : Cop W x z) :
    ∃ m : ℕ, ∃ u₀ ∈ W.AΔ, ∃ u₁ ∈ W.AΔ, Formalism.MainNotions.ArcLiftingSetup.lA W ^ m = u₀ + u₁ ∧
      (∃ r ∈ W.AΔ, u₀ = x * r) ∧ ∃ s ∈ W.AΔ, u₁ = z * s := by
  obtain ⟨m, r, hr, s, hs, e⟩ := h
  exact ⟨m, r * x, W.AΔ.mul_mem hr hx, s * z, W.AΔ.mul_mem hs hz, e, ⟨r, hr, mul_comm _ _⟩,
    ⟨s, hs, mul_comm _ _⟩⟩

theorem coprime_uniformizer_first_factor : Cop W W.π₀ (Formalism.MainNotions.ArcLiftingSetup.ps W 0) :=
  ⟨1, -1, W.AΔ.neg_mem W.AΔ.one_mem, 1, W.AΔ.one_mem, by rw [ps_zero]; ring⟩

variable [IsDomain O]

theorem coprime_frobenius_uniformizer_powers (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) (s : ℕ) (hs : 1 ≤ s) :
    Cop W (Formalism.MainNotions.ArcLiftingSetup.ps W s) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) := by
  obtain ⟨a, ha⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_qP hR s hs
  have hq : Formalism.MainNotions.WachCoordinates.qP W = Formalism.MainNotions.ArcLiftingSetup.ps W 0 := by
    rw [ps_zero]; rfl
  have haΔ : a ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)
      (Formalism.MainNotions.UnusedSlot80.ToolsR.q_component_ne_zero' hR hp0) ?_
    rw [← ha]; exact Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ s hR.1
  have e1 : Formalism.MainNotions.ArcLiftingSetup.ps W s - Formalism.MainNotions.ArcLiftingSetup.lA W = (W.φA ^ s) W.π₀ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub s
  refine ⟨1, 1, W.AΔ.one_mem, -a, W.AΔ.neg_mem haΔ, ?_⟩
  rw [hq] at ha
  linear_combination (-1 : LetA O n) * e1 - ha

theorem cop_lamUp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c' : ZMod n) (e N : ℕ) :
    Cop W (W.π₀ * LamUp W A c' e ^ 2) (Formalism.MainNotions.ArcLiftingSetup.ps W 0 ^ N) := by
  have hp0Δ : Formalism.MainNotions.ArcLiftingSetup.ps W 0 ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1 0
  have hps : ∀ s, Formalism.MainNotions.ArcLiftingSetup.ps W s ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1
  have hU : Cop W (LamUp W A c' e) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) := by
    unfold LamUp Formalism.MainNotions.ArcLiftingSetup.abelian₂
    rw [map_prod]
    refine cop_prod W _ _ (fun s => ?_) hp0Δ fun s _ => ?_
    · rw [map_pow, ← ps_succ]; exact W.AΔ.pow_mem (hps _) _
    · rw [map_pow, ← ps_succ]
      exact cop_pow W (hps _) hp0Δ (coprime_frobenius_uniformizer_powers W hR hp0 (s + 1) (by omega)) _
  have hUΔ : LamUp W A c' e ∈ W.AΔ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W hR.1 A _ e)
  have h1 : Cop W (W.π₀ * LamUp W A c' e ^ 2) (Formalism.MainNotions.ArcLiftingSetup.ps W 0) :=
    cop_mul W hR.1 hp0Δ (coprime_uniformizer_first_factor W) (cop_pow W hUΔ hp0Δ hU 2)
  have hxΔ : W.π₀ * LamUp W A c' e ^ 2 ∈ W.AΔ := W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem hUΔ 2)
  exact cop_symm W (cop_pow W hp0Δ hxΔ (cop_symm W h1) N)

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentSmul
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section SlopeTestRemainingChoices

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gammaD_smul_letA' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem idempotent_mul_self'' (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem invariantLetter_sub {c : ZMod n} {x y : W.DD T} (hx : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x)
    (hy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (x - y) := by
  rw [sub_eq_add_neg, ← neg_one_smul O y]
  exact dl_add W T hx (dl_smul W T (-1) hy)

theorem invariant_letter_idempotent_smul {c : ZMod n} {z : W.DD T} (hz : ∀ δ ∈ W.DelF, W.γD T δ z = z) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ((letE c : LetA O n) • z) :=
  ⟨by rw [smul_smul, idempotent_mul_self''], fun δ hδ => by rw [gammaD_smul_letA', gammaA_idempotent, hz δ hδ]⟩

theorem uniformizer_smul_inverse_smul (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    W.π₀ • (uniformizerInverse W • x) = x := by
  rw [← algebraMap_smul W.EE W.π₀, smul_smul, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem smul_comm_O_EE (r : O) (e : W.EE) (x : W.DD T) : r • (e • x) = e • (r • x) := by
  rw [← algebraMap_smul (LetA O n) r (e • x), ← algebraMap_smul (LetA O n) r x, smul_comm_letA_EE]

theorem q_pow_smul_inverse_pow_smul (hU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (a : ℕ) (x : W.DD T) :
    Formalism.MainNotions.LiftingTheory.qp W ^ a • (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • x) = x := by
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ a), smul_smul, map_pow, ← mul_pow,
    Ring.mul_inverse_cancel _ hU, one_pow, one_smul]

theorem delta_fixes_cocycle_second (x : ↥(W.wachCocyclesDelta T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (x : W.DD T × W.DD T).2 = (x : W.DD T × W.DD T).2 := by
  have h : (x : W.DD T × W.DD T) ∈ W.wachCocyclesDelta T := x.2
  simp only [LocWach.wachCocyclesDelta, herrZ1Δ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.prodMap_apply, LinearMap.id_apply, sub_eq_zero] at h
  exact congrArg Prod.snd (h.2 δ hδ)

theorem mem_of_natCast_pow_smul_mem [NeZero n] (hB : Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ)
    (c : ZMod n) {w : W.DD T} (k : ℕ) (hw : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w)
    (hN : ((PD.p : ℕ) : O) ^ k • w ∈ W.N T) : w ∈ W.N T := by
  obtain ⟨e, he⟩ := (hB hA T hT c).1
  have hmem : ((PD.p : ℕ) : O) ^ k • w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 0 :=
    Submodule.subset_span ⟨_, ⟨hN, dl_smul W T _ hw⟩, by simp⟩
  have h := ((hB hA T hT c).2 _ e he 0).2 w k hmem
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  simpa using hx

theorem exists_embedding_over_letter [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c := by
  let e := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
  refine ⟨(W.emb c).comp e.symm.toAlgHom, ?_⟩
  ext x
  show (W.emb c) (e.symm (algebraMap K₀ K x)) = W.emb c x
  congr 1
  exact e.symm_apply_apply x

theorem lam_nonneg_of_one_lt (l H : ℕ) (hl : 1 < l) : 0 ≤ lam l H := by
  unfold lam
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg (b := (l : ℝ)) (by exact_mod_cast hl) this
    linarith

end SlopeTestRemainingChoices

section Core

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def liftingSection (R : Polynomial O) (a : ℕ) (ν zc : W.DD T) : W.DD T :=
  Polynomial.aeval (derivationOnWachModule W T) R
      (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • ν) +
    Polynomial.aeval (derivationOnWachModule W T) (Polynomial.divX R) (uniformizerInverse W • zc)

theorem lift_of_killing_polynomial [NeZero n] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hDS : DerivationPreservesQLattice W)
    (hB : Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (c : ZMod n) (a N s₁ : ℕ)
    (R : Polynomial O) (hR0 : R.coeff 0 = ((PD.p : ℕ) : O) ^ s₁)
    (hkill : ∀ y₀, QLattice W T c a y₀ → Polynomial.aeval (derivationOnWachModule W T) (X * R) y₀ ∈ W.N T)
    (zc μ ν : W.DD T) (hzc : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c zc) (hμ : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c μ)
    (hν : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ν)
    (h3 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (((PD.p : ℕ) : O) ^ N • zc + (W.γ T μ - μ)))
    (h6 : ((PD.p : ℕ) : O) ^ N • ν - Formalism.MainNotions.LiftingTheory.qp W ^ a • μ ∈ W.N T) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (liftingSection W T R a ν zc) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (((PD.p : ℕ) : O) ^ s₁ • zc +
      (W.γ T (liftingSection W T R a ν zc) - liftingSection W T R a ν zc)) ∧
    QLattice W T c a (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (W.γ T (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ) -
        (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ)) := by
  have hU := hR.πU
  have hπΔ := hR.πΔ
  have hqU := hR.qU
  have hqΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπΔ
  set d := derivationOnWachModule W T with hd
  set pp : O := ((PD.p : ℕ) : O) with hpp
  have ciFix : ∀ δ ∈ W.DelF, W.γE δ (uniformizerInverse W) = uniformizerInverse W :=
    fun δ hδ => delta_fixes_inverse W _ hπΔ hU δ hδ
  have qiFix : ∀ δ ∈ W.DelF, W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a) =
      Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a := by
    intro δ hδ
    rw [map_pow, delta_fixes_inverse W _ hqΔ hqU δ hδ]
  set R1 := Polynomial.divX R with hR1
  have hsplit : R = R1 * X + C (pp ^ s₁) := by
    rw [← hR0, mul_comm]
    exact (Polynomial.X_mul_divX_add R).symm
  set m₀ := Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • ν with hm₀def
  set dz := uniformizerInverse W • zc with hdzdef
  have hm₀ : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c m₀ := invariantLetter_fixed_smul W T _ qiFix hν
  have hdz : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c dz := invariantLetter_fixed_smul W T _ ciFix hzc
  obtain ⟨y, hyN, hyΔ, hye⟩ := h3
  have he₁ : uniformizerInverse W • (pp ^ N • zc + (W.γ T μ - μ)) = y := by
    rw [hye, pow_one, inverse_smul_uniformizer_smul W T hU]
  have hy_eq : y = pp ^ N • dz + d μ := by
    rw [← he₁, smul_add, hd, derivation_on_wach_module_apply, hdzdef, smul_comm_O_EE]
  have hyDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y := by
    rw [← he₁]
    exact invariantLetter_fixed_smul W T _ ciFix (dl_add W T (dl_smul W T _ hzc) (invariantLetter_gamma_sub W T hμ))
  have hyQ : QLattice W T c 0 y := ⟨hyDL, by simpa using hyN⟩
  set u₀ := pp ^ N • m₀ - μ with hu₀def
  have hu₀ : QLattice W T c a u₀ := by
    refine ⟨invariantLetter_sub W T (dl_smul W T _ hm₀) hμ, ?_⟩
    rw [hu₀def, smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ a) (pp ^ N) m₀, hm₀def, q_pow_smul_inverse_pow_smul W T hqU]
    exact h6
  have hms : liftingSection W T R a ν zc = Polynomial.aeval d R m₀ + Polynomial.aeval d R1 dz := rfl
  have key : Polynomial.aeval d R μ = pp ^ s₁ • μ + Polynomial.aeval d R1 (d μ) := by
    conv_lhs => rw [hsplit]
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, add_comm]
  set u := pp ^ N • liftingSection W T R a ν zc - pp ^ s₁ • μ with hudef
  have e1 : Polynomial.aeval d R u₀ = pp ^ N • Polynomial.aeval d R m₀ - Polynomial.aeval d R μ := by
    rw [hu₀def, (Polynomial.aeval d R).map_sub, (Polynomial.aeval d R).map_smul]
  have e2 : Polynomial.aeval d R1 y = pp ^ N • Polynomial.aeval d R1 dz + Polynomial.aeval d R1 (d μ) := by
    rw [hy_eq, (Polynomial.aeval d R1).map_add, (Polynomial.aeval d R1).map_smul]
  have hu_eq : u = Polynomial.aeval d R u₀ + Polynomial.aeval d R1 y := by
    rw [hudef, hms, e1, e2, key, smul_add]
    abel
  have hXP : ∀ (Q : Polynomial O) (x : W.DD T),
      d (Polynomial.aeval d Q x) = Polynomial.aeval d (X * Q) x := by
    intro Q x
    rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  have hDLms : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (liftingSection W T R a ν zc) := by
    rw [hms]
    exact dl_add W T (invariantLetter_polynomial_derivation W T hπΔ hU R hm₀) (invariantLetter_polynomial_derivation W T hπΔ hU R1 hdz)
  have hQu : QLattice W T c a u := by
    rw [hu_eq]
    exact qLattice_add W T (qLattice_polynomial_derivation W T hDS hA hT c a R hu₀)
      (qLattice_mono W T (Nat.zero_le a) (qLattice_polynomial_derivation W T hDS hA hT c 0 R1 hyQ))
  have hdu : d u = Polynomial.aeval d (X * R) u₀ + Polynomial.aeval d (X * R1) y := by
    rw [hu_eq, map_add (f := _), hXP, hXP]
  have hduN : d u ∈ W.N T := by
    rw [hdu]
    refine (W.N T).add_mem (hkill u₀ hu₀) ?_
    have h := (qLattice_polynomial_derivation W T hDS hA hT c 0 (X * R1) hyQ).2
    rw [pow_zero, one_smul] at h
    exact h
  have hduDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (d u) := invariantLetter_derivation W T hπΔ hU hQu.1

  set w := pp ^ s₁ • dz + d (liftingSection W T R a ν zc) with hwdef
  have hexpr : pp ^ s₁ • zc + (W.γ T (liftingSection W T R a ν zc) - liftingSection W T R a ν zc) = W.π₀ • w := by
    rw [hwdef, smul_add, smul_comm W.π₀ (pp ^ s₁) dz, hdzdef, uniformizer_smul_inverse_smul W T hU, hd,
      uniformizer_smul_derivation W T hU]
  have hpw : pp ^ N • w = pp ^ s₁ • y + d u := by
    have h1 : pp ^ N • dz = y - d μ := by rw [hy_eq]; abel
    have h2 : pp ^ N • liftingSection W T R a ν zc = u + pp ^ s₁ • μ := by rw [hudef]; abel
    rw [hwdef, smul_add, smul_comm (pp ^ N) (pp ^ s₁) dz, h1, ← d.map_smul (pp ^ N), h2,
      d.map_add, d.map_smul, smul_sub]
    abel
  have hwDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w :=
    dl_add W T (dl_smul W T _ hdz) (invariantLetter_derivation W T hπΔ hU hDLms)
  have hwN : w ∈ W.N T := by
    refine mem_of_natCast_pow_smul_mem W T hB hA hT c N hwDL ?_
    rw [hpw]
    exact (W.N T).add_mem ((W.N T).smul_of_tower_mem _ hyN) hduN
  refine ⟨hDLms, ⟨w, hwN, hwDL.2, by rw [pow_one, hexpr]⟩, hQu, ⟨d u, hduN, hduDL.2, ?_⟩⟩
  rw [pow_one, hd, uniformizer_smul_derivation W T hU]

end Core

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LiftRingOfUniformizerClause
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section JumpsT2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem jumps_in_letter_of_crystalline [NeZero n] (W : LocWach PD LL O v n) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) :
    ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η) :=
  fun _ _ _ _ _ _ _ _ hS => Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumpsLet₂ W hE hC hQ hS

theorem liftRing_of_uniformizer_clause (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) :
    Formalism.MainNotions.LiftingTheory.lifta_Ring W :=
  Formalism.MainNotions.LiftingTheory.lifta_ring_of W (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hA T hT).1

theorem lemGA_la_of_adm [NeZero n] (W : LocWach PD LL O v n) (hT2 : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : LemGA_la W := by
  intro d T₁ T₂ F b S η m hS
  exact lemGA_la_of W hT2 h9 h5
    (liftRing_of_uniformizer_clause W h9 hS.1 T₂ hS.2.2.2.2.2.1.2.1) (jumps_in_letter_of_crystalline W hE hC hQ)
    d T₁ T₂ F b S η m hS

end JumpsT2

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfGammaLemmas
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

theorem lemmaGD_cc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
    (hg : Good K 1 LL) :
    ∃ cc : ℤ → ↥(OL LL), ∀ x : ℤ, (-(((P.PD K).p : ℕ) : ↥(OL LL))) * cc x =
      ((((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL)) - 1 := by
  obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (H := H) hg
  have hne : (z : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  let I : Ideal ℤ_[l] := Ideal.span {((l : ℕ) : ℤ_[l])}
  have hI : (z : ℤ_[l]) - 1 ∈ I := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by omega)
    simpa using this
  have hz1 : Units.map (Ideal.Quotient.mk I).toMonoidHom z = 1 := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_one]
    exact (Ideal.Quotient.eq.2 hI).trans (map_one _)
  have hw : ∀ x : ℤ, ∃ w : ℤ_[l], -((l : ℕ) : ℤ_[l]) * w = ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
    intro x
    have h1 : (Ideal.Quotient.mk I) ((z ^ (-x) : ℤ_[l]ˣ) : ℤ_[l]) = (Ideal.Quotient.mk I) 1 := by
      have := congrArg Units.val
        (show Units.map (Ideal.Quotient.mk I).toMonoidHom (z ^ (-x)) = 1 by
          rw [map_zpow, hz1, one_zpow])
      rw [Units.coe_map, Units.val_one] at this
      exact this.trans (map_one _).symm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    exact ⟨-w, by rw [← hw]; ring⟩
  choose w hw using hw
  refine ⟨fun x => algebraMap ℤ_[l] ↥(OL LL) (w x), fun x => ?_⟩
  have e := congrArg (algebraMap ℤ_[l] ↥(OL LL)) (hw x)
  rw [map_mul, map_neg, map_natCast, map_sub, map_one] at e
  rw [P.PD_p K, e]
  congr 1
  have hzu : Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom z =
      (H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam := Units.ext hz
  rw [← hzu, ← map_zpow]
  rfl

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RealisedOfCoordArc
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

def CoordSteps (hR : Ring9 W) (e : W.DD W.one) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ (C₁ : Coord W (baseIdOf hR) T₁) (C₂ : Coord W (baseIdOf hR) T₂) (C₀ : Coord W (baseIdOf hR) W.one)
      (_h : CoordHom C₁ C₂ F) (e₀ : C₀.V), ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e

end Formalism.MainNotions.N.Ln03
end
end

