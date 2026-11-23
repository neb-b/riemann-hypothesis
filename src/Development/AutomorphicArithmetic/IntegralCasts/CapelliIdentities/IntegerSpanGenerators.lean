module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014

@[expose] public section


open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.CrystallineLiftingInputs in
noncomputable def UpperTheory.Reformulated.B.IntegerSpanGenerators.Zspan
    {G : Type} [Group G] [TopologicalSpace G]
    {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ) :
    Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n)
    {z | ∃ w, w ∈ W.N T ∧ InI W T i w ∧ IsTrunc W T i j M X σ w z}

section SlopeTestRemainingChoices

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.CrystallineLiftingInputs Formalism.MainNotions.LiftingTheory

private theorem unit_of_val {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    (v : AddValuation LL (WithTop ℚ)) (hinj : Function.Injective (algebraMap O LL))
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (x y : O) (k : ℕ)
    (hx : v (algebraMap O LL x) = (k : WithTop ℚ)) (hy : v (algebraMap O LL y) = (k : WithTop ℚ)) :
    ∃ u : Oˣ, x = (u : O) * y := by
  have hk : (k : WithTop ℚ) ≠ ⊤ := WithTop.natCast_ne_top k
  have key : ∀ a b : O, v (algebraMap O LL a) = (k : WithTop ℚ) →
      v (algebraMap O LL b) = (k : WithTop ℚ) → b ≠ 0 ∧ ∃ o : O, a = o * b := by
    intro a b ha hb
    have hb0 : algebraMap O LL b ≠ 0 := by
      intro h
      rw [h, v.map_zero] at hb
      exact hk hb.symm
    have h1 : algebraMap O LL a = algebraMap O LL a / algebraMap O LL b * algebraMap O LL b :=
      (div_mul_cancel₀ _ hb0).symm
    have h2 : v (algebraMap O LL a / algebraMap O LL b) = 0 := by
      have h3 := congrArg v h1
      rw [v.map_mul, ha, hb] at h3
      exact (WithTop.add_right_cancel hk ((zero_add _).trans h3)).symm
    obtain ⟨o, ho⟩ := hO _ h2.ge
    refine ⟨fun h => hb0 (by rw [h, map_zero]), o, hinj ?_⟩
    rw [map_mul, ho]
    exact h1
  obtain ⟨hy0, o, ho⟩ := key x y hx hy
  obtain ⟨-, o', ho'⟩ := key y x hy hx
  have h1 : o * o' = 1 := by
    apply hinj
    have hy1 : algebraMap O LL y ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))
    apply mul_right_cancel₀ hy1
    rw [← map_mul, map_one, one_mul]
    congr 1
    calc o * o' * y = o' * (o * y) := by ring
      _ = y := by rw [← ho, ← ho']
  exact ⟨Units.mkOfMulEqOne o o' h1, ho⟩

private theorem val_succ (p : ℕ) (hp : p.Prime) (r : ℕ) :
    (r + 1) + padicValNat p (r + 1).factorial =
      (r + padicValNat p r.factorial) + (1 + padicValNat p (r + 1)) := by
  have := Fact.mk hp
  rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.add_one_ne_zero r) (Nat.factorial_ne_zero r)]
  omega

private theorem val_add (p : ℕ) (hp : p.Prime) (a b : ℕ) :
    (a + padicValNat p a.factorial) + (b + padicValNat p b.factorial) ≤
      (a + b) + padicValNat p (a + b).factorial := by
  have := Fact.mk hp
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  have h0 : (a + b).choose b ≠ 0 := (Nat.choose_pos (Nat.le_add_left b a)).ne'
  rw [← h, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (mul_ne_zero h0 (Nat.factorial_ne_zero a)) (Nat.factorial_ne_zero b),
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h0 (Nat.factorial_ne_zero a)]
  omega

private theorem eY_mono (p : ℕ) (hp : p.Prime) : Monotone (eY p) := by
  intro a b hab
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (a : ℝ) ≤ b := by exact_mod_cast hab
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact mul_le_mul_of_nonneg_right h3 (by linarith)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private noncomputable def N0 (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) :
    Submodule O (W.DD T) :=
  W.NΔ T ⊓ (W.Nl T i).restrictScalars O

private theorem mem_wachFiltration_iff (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    x ∈ N0 W T i ↔ x ∈ W.N T ∧ DL W T i x := by
  constructor
  · rintro ⟨⟨h1, h2⟩, y, -, hy⟩
    refine ⟨h1, ?_, h2⟩
    have hy' : (letE i : LetA O n) • y = x := hy
    have he : (letE i : LetA O n) * letE i = letE i := by
      funext k
      by_cases h : k = i <;> simp [letE, h]
    rw [← hy', smul_smul, he]
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, x, h1, h2⟩

private theorem smul_mem_wachFiltration (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (a : LetA O n) (ha : a ∈ W.AΔ) (x : W.DD T) (hx : x ∈ N0 W T i) : a • x ∈ N0 W T i := by
  refine ⟨⟨(W.N T).smul_mem a hx.1.1, fun δ hδ => ?_⟩, (W.Nl T i).smul_mem a hx.2⟩
  have h := W.γD_smul T δ (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul, hx.1.2 δ hδ] at h
  rw [h]
  exact congrArg (· • x) (ha δ hδ)

private theorem sat (W : LocWach PD LL O v n) [IsDomain O] (f : LetA O n)
    (hf : IsUnit (algebraMap (LetA O n) W.EE f)) (a : LetA O n)
    (h : f ∣ ((PD.p : ℕ) : LetA O n) * a) : f ∣ a := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨u, hu⟩ := hf
  have hl : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0
    have h1 : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h0, map_zero]
    have h2 := W.v_l
    rw [h1, v.map_zero] at h2
    exact WithTop.one_ne_top h2.symm
  have hl' : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h0
    apply hl
    have := congrArg PowerSeries.constantCoeff h0
    rwa [map_natCast, map_zero] at this
  obtain ⟨b, hb⟩ := W.EE_sat g 1 (by
    rw [Ideal.mem_span_singleton', pow_one]
    refine ⟨algebraMap (LetA O n) W.EE a * (u⁻¹ : W.EEˣ), ?_⟩
    have h1 := congrArg (algebraMap (LetA O n) W.EE) hg
    rw [map_mul, map_mul, map_natCast, ← hu] at h1
    calc algebraMap (LetA O n) W.EE a * (u⁻¹ : W.EEˣ) * ((PD.p : ℕ) : W.EE)
        = (u⁻¹ : W.EEˣ) * (((PD.p : ℕ) : W.EE) * algebraMap (LetA O n) W.EE a) := by ring
      _ = algebraMap (LetA O n) W.EE g := by rw [h1, Units.inv_mul_cancel_left])
  refine ⟨b, funext fun k => mul_left_cancel₀ hl' ?_⟩
  have h1 : ((PD.p : ℕ) : LetA O n) * a = ((PD.p : ℕ) : LetA O n) * (f * b) := by
    rw [hg, hb]; ring
  exact congrFun h1 k

private theorem aux (W : LocWach PD LL O v n) [IsDomain O]
    (hinj : Function.Injective (algebraMap O LL))
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hH : coreH W) (hR : lifta_Ring W) (hA : CaseA W)
    (hφ : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    (r s : ℕ → LetA O n)
    (hrs : ∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y)
    (p : W.DD T) (hp : p ∈ pullJ W T i j) :
    ∃ p' ∈ pullJ W T i j, ((PD.p : ℕ) : O) ^ (2 * σ) • p - fMX W M X • p' ∈
      UpperTheory.Reformulated.B.IntegerSpanGenerators.Zspan W T i j M X σ := by
  obtain ⟨h1, h2, -, h4, -⟩ := hH hA T hT i
  have hpr : PD.p.Prime := PD.hp
  have hcast : ∀ (k : ℕ) (x : W.DD T),
      ((PD.p : ℕ) : LetA O n) ^ k • x = ((PD.p : ℕ) : O) ^ k • x := by
    intro k x
    rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ k) x, map_pow, map_natCast]
  have hEe : ∀ y : ℕ, y + padicValNat PD.p y.factorial ≤ eY PD.p y := by
    intro y
    have h := (Rat.cast_le (K := ℝ)).2 (h4 y)
    have h' : ((y + padicValNat PD.p y.factorial : ℕ) : ℝ) ≤ (y : ℝ) * PD.p / ((PD.p : ℝ) - 1) := by
      simpa using h
    exact (Nat.cast_le (α := ℝ)).1 (h'.trans (Nat.le_ceil _))
  have hlam : ∀ k : ℕ, ∃ u : Oˣ, u₁ W ^ (k + 1) - 1 = (u : O) * ((PD.p : ℕ) : O) ^
      (((k + 1) + padicValNat PD.p (k + 1).factorial) - (k + padicValNat PD.p k.factorial)) := by
    intro k
    rw [val_succ PD.p hpr k, Nat.add_sub_cancel_left]
    refine unit_of_val v hinj hO _ _ _ (h2 (k + 1) (by omega)) ?_
    rw [map_pow, map_natCast, v.map_pow, W.v_l, nsmul_one]
  have hser := UpperTheory.filtration_exponent_bound (N0 W T i) (W.γ T) W.π₀ ((PD.p : ℕ) : O)
    (fun y => y + padicValNat PD.p y.factorial) (eY PD.p) (fun k => u₁ W ^ k - 1)
    (monotone_nat_of_le_succ fun k => by have := val_succ PD.p hpr k; omega)
    (eY_mono PD.p hpr) hEe hlam (by simp) (smul_mem_wachFiltration W T i _ hR.πΔ) (fun k x hx => h1 k x hx)
  rw [← hcast]
  refine UpperTheory.divisibility_filtration ((PD.p : ℕ) : LetA O n) (fMX W M X) ((W.φA ^ j) W.π₀) σ (max M X)
    (fun y => y + padicValNat PD.p y.factorial) (eY PD.p) r s _ _ (sat W _ ?_)
    (val_add PD.p hpr) hEe (by simp [eY]) (fun y => (hrs y).1.2) (fun y => (hrs y).2) ?_ ?_ p hp
  · rw [fMX, map_mul, map_pow, map_pow]
    exact (hR.πU.pow _).mul (hR.qU.pow _)
  · intro y hy
    obtain ⟨u, -, -, -, -, hu⟩ := hφ j y
    rw [hu, fMX]
    have hM : M ≤ y := by omega
    have hX : X ≤ (PD.p - 1) * y := by
      have h := hpr.two_le
      have h' : 1 * y ≤ (PD.p - 1) * y := Nat.mul_le_mul_right y (by omega)
      omega
    refine mul_dvd_mul ((pow_dvd_pow _ hM).mul_left u) ((pow_dvd_pow (qp W) hX).trans ?_)
    exact Finset.dvd_prod_of_mem (fun k => pk W k ^ ((PD.p - 1) * y))
      (Finset.mem_range.2 (show 0 < j by omega))
  · rintro _ ⟨w, hw, rfl⟩
    have hw0 : w ∈ N0 W T i := (mem_wachFiltration_iff W T i w).2 hw
    obtain ⟨c, hc0, hc, hK⟩ := hser w hw0
    refine ⟨fun y => ((W.φD T) ^ j) (c y), by simp [hc0],
      fun y => ⟨c y, (mem_wachFiltration_iff W T i _).1 (hc y), rfl⟩, Submodule.subset_span ?_⟩
    refine ⟨w, hw.1, ⟨hw.2, ⟨0, 0, by simpa using hw.1⟩, ?_⟩,
      fun y => ((PD.p : ℕ) : O) ^ (eY PD.p y - (y + padicValNat PD.p y.factorial)) • c y, r, s,
      ⟨by simp [hc0], fun y => ?_, fun k => ?_⟩, hrs, ?_⟩
    · obtain ⟨x', hx', he⟩ := h1 0 w hw0
      exact ⟨x', hx'.1.1, hx'.1.2, by simpa using he⟩
    · exact ((mem_wachFiltration_iff W T i _).1 ((N0 W T i).smul_mem _ (hc y))).symm
    · obtain ⟨t, ht, he⟩ := hK k
      exact ⟨0, t, ht.1.1, ht.1.2, by rw [pow_zero, one_smul]; exact he⟩
    · rw [hcast]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_smul, hcast, map_smul]

end SlopeTestRemainingChoices

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.CrystallineLiftingInputs
  Formalism.MainNotions.DeltaInvariantLattices Formalism.MainNotions.LiftingTheory Formalism.MainNotions.ArcLiftingSetup in
theorem UpperTheory.Reformulated.B.IntegerSpanGenerators.span_gen
    {G : Type} [Group G] [TopologicalSpace G]
    {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) [NeZero n] [IsDomain O]
    (hinj : Function.Injective (algebraMap O LL))
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (_h9 : P9W W) (hH : coreH W) (hR : lifta_Ring W) (_hsp : SATPcore W) (hA : CaseA W)
    (hφ : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    (r s : ℕ → LetA O n)
    (hrs : ∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y)
    (p : W.DD T) (hp : p ∈ pullJ W T i j) :
    ∃ p' ∈ pullJ W T i j, ((PD.p : ℕ) : O) ^ (2 * σ) • p - fMX W M X • p' ∈
      UpperTheory.Reformulated.B.IntegerSpanGenerators.Zspan W T i j M X σ :=
  aux W hinj hO hH hR hA hφ T hT i hj r s hrs p hp
