module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open TensorProduct

namespace GlobalTheory.SubSumJumps

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_mem_DdRE (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR)
    (hx : x ∈ DdRE PD ρ τ) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ DdRE PD ρ' τ := by
  have h1 : ∀ (g : G) (y : V ⊗[Qp] BdR),
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, hf]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have h2 : ∀ (c : K) (y : V ⊗[Qp] BdR),
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c
        (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y)
        = AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)
          (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y) := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  simp only [DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  refine ⟨fun g => ?_, fun c => ?_⟩
  · rw [h1, hx.1 g]
  · rw [h2, hx.2 c, map_smul]

theorem FilV_anti (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

end

theorem jumpsInV_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (τ : K →ₐ[Qp] LL) (J : Set ℤ), IsSubOfSums ρ (fun x g => Ms x g) → (∀ x, JumpsInV PD (matRep (Ms x)) τ J) → JumpsInV PD ρ τ J := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ ι k Ms τ J
    hsub hJ a ha
  by_contra haJ
  apply ha
  obtain ⟨m, xs, j, hj, hje⟩ := hsub
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hj)
  have hrv : ∀ v, r (j v) = v := fun v => LinearMap.congr_fun hr v
  apply le_antisymm
  · exact inf_le_inf_left _ (FilV_anti PD a)
  intro x hx
  refine ⟨hx.1, ?_⟩
  let p : Fin m → (V →ₗ[LL] (Fin k → LL)) := fun b => (LinearMap.proj b).comp j
  let s : Fin m → ((Fin k → LL) →ₗ[LL] V) := fun b =>
    r.comp (LinearMap.single LL (fun _ : Fin m => Fin k → LL) b)
  have hdec : ∀ y : V ⊗[Qp] BdR, y = ∑ b, AlgebraTensorModule.map (s b)
      (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.sum_tmul]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [s, p, LinearMap.comp_apply, ← map_sum]
      conv_lhs => rw [← hrv v]
      congr 1
      exact (Finset.univ_sum_single (j v)).symm
    | add y z hy hz =>
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← hy, ← hz]
  rw [hdec x]
  refine Submodule.sum_mem _ fun b _ => map_mem_FilV PD (s b) (a + 1) _ ?_
  have heq : FildR PD (matRep (Ms (xs b))) τ (a + 1) = FildR PD (matRep (Ms (xs b))) τ a := by
    by_contra h
    exact haJ (hJ (xs b) a h)
  have hm : AlgebraTensorModule.map (p b) (LinearMap.id : BdR →ₗ[Qp] BdR) x
      ∈ FildR PD (matRep (Ms (xs b))) τ a := by
    refine ⟨map_mem_DdRE PD ρ _ (p b) (fun g v => ?_) τ x hx.1, map_mem_FilV PD (p b) a x hx.2⟩
    simp [p, hje, matRep, Matrix.toLinAlgEquiv'_apply]
  rw [← heq] at hm
  exact hm.2

end GlobalTheory.SubSumJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_add_etaHat_add_sHat_le_hPage {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  have ht : 5 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hη : 0 < L.etaSz := L.etaSz_pos
  have hS : 0 < L.Sc := L.Sc_pos
  obtain ⟨hC, hw1, hw2, hwb, -, hb⟩ := h
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hb' : (100 : ℝ) ≤ L.sc.b' := hw1.trans hwb
  have hfac : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbig : 100 * L.sc.b' ≤ L.sc.b := by
    have := mul_le_mul_of_nonneg_right hfac (by linarith : (0 : ℝ) ≤ L.sc.b')
    linarith
  have htR : ((D.R.t : ℕ) : ℝ) ≤ L.sc.b := by nlinarith
  have hb0 : 0 ≤ L.sc.b := by linarith
  set c := (D.R.t + 1) / 2 with hcdef
  have hc3 : 3 ≤ c := by omega
  have hct : c ≤ D.R.t := by omega
  have htc : D.R.t ≤ ⌈L.sc.b⌉₊ := by exact_mod_cast htR.trans (Nat.le_ceil _)
  have hcle : c ≤ ⌈L.sc.b⌉₊ := hct.trans htc
  have h1 : (⌈L.sc.b⌉₊ : ℝ) < L.sc.b + 1 := Nat.ceil_lt_add_one hb0
  have h2 : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le hη.le
  have h3 : (⌊L.Sc⌋₊ : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have hc3R : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc3
  unfold bHat etaHat sHat hPage
  rw [← hcdef, Nat.cast_sub hcle]
  push_cast
  linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatio
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem scale_log_mul_b'_le_b : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  intro eps C A heps hC hA
  have hK : 0 ≤ C * (A + 1) := by positivity
  have hev : ∀ᶠ t in Filter.atTop, t ^ ⌈6 / eps⌉₊ * Real.exp (-t) ≤ 1 / (C * (A + 1) + 1) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈6 / eps⌉₊).eventually
      (ge_mem_nhds (by positivity))
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max T0 1 ^ (3 / eps), fun s hse hx => ?_⟩
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 ≤ s.x := by linarith
  have hT1 : 0 ≤ max T0 1 := le_trans zero_le_one (le_max_right _ _)
  have ht : max T0 1 ≤ s.x ^ (eps / 3) := by
    calc max T0 1 = (max T0 1 ^ (3 / eps)) ^ (eps / 3) := by
          rw [← Real.rpow_mul hT1]
          rw [show 3 / eps * (eps / 3) = 1 by field_simp, Real.rpow_one]
      _ ≤ s.x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hx (by positivity)
  have ht1 : 1 ≤ s.x ^ (eps / 3) := le_trans (le_max_right _ _) ht
  have hxsq : s.x ^ 2 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by
    have e : s.x ^ 2 = (s.x ^ (eps / 3)) ^ (6 / eps) := by
      rw [← Real.rpow_mul hx0, show eps / 3 * (6 / eps) = ((2 : ℕ) : ℝ) by field_simp; norm_num,
        Real.rpow_natCast]
    rw [e, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil _)
  have hu := hT0 _ (le_trans (le_max_left _ _) ht)
  rw [le_div_iff₀ (by positivity)] at hu
  have hu0 : 0 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) := by positivity
  have he := Real.exp_pos (s.x ^ (eps / 3))
  have e1 : (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ =
      (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) * Real.exp (s.x ^ (eps / 3)) := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hlog : A * Real.log s.x + 1 ≤ (A + 1) * s.x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < s.x)
    nlinarith
  have main : C * (A * Real.log s.x + 1) * s.x ≤ Real.exp (s.x ^ (eps / 3)) := by
    calc C * (A * Real.log s.x + 1) * s.x ≤ C * ((A + 1) * s.x) * s.x := by gcongr
      _ = C * (A + 1) * s.x ^ 2 := by ring
      _ ≤ C * (A + 1) * (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by gcongr
      _ ≤ Real.exp (s.x ^ (eps / 3)) := by
          rw [e1]
          nlinarith [mul_le_mul_of_nonneg_right hu he.le, mul_nonneg hu0 he.le]
  have hb : 0 ≤ s.b := (Real.exp_pos _).le
  have hb' : s.b' = s.x * s.b / Real.exp (s.x ^ (eps / 3)) := by
    simp only [Scale.b', Scale.a, Scale.X', hse]
  rw [hb']
  calc C * (A * Real.log s.x + 1) * (s.x * s.b / Real.exp (s.x ^ (eps / 3)))
      = C * (A * Real.log s.x + 1) * s.x / Real.exp (s.x ^ (eps / 3)) * s.b := by ring
    _ ≤ 1 * s.b := by
        gcongr
        rw [div_le_one he]
        exact main
    _ = s.b := one_mul _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem splits_of_conjugates_mem :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l),
      (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) →
      ∀ _ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        Formalism.WeaklyAdmissibleFiltrations.Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 := by
  intro l _ K LL h ft
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  refine ⟨LL.2, ?_⟩
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Loc.Om l), ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun σ => LL.1.val.comp σ
      invFun := fun τ => τ.codRestrict LL.1.toSubalgebra (h τ)
      left_inv := fun σ => ?_
      right_inv := fun τ => ?_ }
  · ext x; rfl
  · ext x; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScale
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem thinSize_dominates : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  intro eps _
  refine ⟨10000, fun D L P _ hx => ?_⟩
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m; exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := div_le_self hb'.le hxn
  have hte := P.t_le_eta
  have h1 := P.teta
  rw [le_div_iff₀ hx0] at h1
  have hS := L.Sc_pos
  have hsq : (100 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hlog : (1 : ℝ) ≤ Real.log L.sc.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hk : (200 : ℝ) ≤ D.R.k := by
    refine le_trans ?_ P.k_ge_mx
    have a : (200 : ℝ) ≤ (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) := by nlinarith
    nlinarith
  have h2 : 200 * L.Sc ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul_of_nonneg_right hk hS.le) P.kS_le
  have h3 : 7 * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := mul_le_mul_of_nonneg_right ht (by linarith)
  have h4 : 7 * L.etaSz * 10000 ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul h3 hx (by norm_num) (by linarith)) h1
  exact ⟨by linarith, by linarith, hw1⟩

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScale
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.Ggeo

theorem bT_add_div_le_three_halves : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x →
    ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  intro D L P hx t
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Formalism.BasicNotions.Scale.b' Formalism.BasicNotions.Scale.a Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.X'
    positivity
  have hbT := P.bT_le t
  have hrho := P.rho_le
  unfold Formalism.BasicNotions.LevelStarExponents.rhoP at hrho
  have hLaG : 0 < L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    by_contra hneg
    have hneg' : L.LaG ≤ 0 := le_of_not_gt hneg
    have h3 : L.LaG * L.sc.b' / (D.R.k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg' hb'.le) (Nat.cast_nonneg _)
    linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / (D.R.k : ℝ) := by
    have := P.Crho_pos
    positivity
  set T := Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hT
  have hT4 : 4 * T ≤ L.sc.x ^ (-2 : ℝ) := by
    have h4 : 4 * Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * T := by
      rw [hT]
      ring
    linarith
  have hbT' : (L.bT t : ℝ) ≤ L.sc.b' + T * L.sc.b' := by
    have h5 : Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = T * L.sc.b' := by
      rw [hT]
      ring
    linarith
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 16 := by
    calc L.sc.x ^ (-2 : ℝ) = (L.sc.x ^ 2)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_two]
      _ ≤ (16 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
      _ = 1 / 16 := by norm_num
  have hTb : T * L.sc.b' ≤ L.sc.b' / 64 := by
    have h6 : T ≤ 1 / 64 := by linarith
    nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  linarith

end GlobalTheory.Ggeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindows
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem jT1_mem_window_of_bounded_v : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ),
    (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) →
    (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s,
    (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ)
      else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨
    |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  intro R P j s S η hv hb u hu
  obtain ⟨c, hc⟩ := R.t_odd
  have ht1 : ((R.t : ℤ) - 1) / 2 = c := by rw [hc]; push_cast; omega
  have ht2 : ((R.t : ℤ) + 1) / 2 = c + 1 := by rw [hc]; push_cast; omega
  have htc : (R.t : ℤ) = 2 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨E, hE⟩ := P.e_int j
  have hEf : ⌊P.e j⌋ = E := by rw [hE]; simp
  have hV : ∀ i, 0 ≤ ⌊P.v i⌋ ∧ ⌊P.v i⌋ ≤ ((⌊S⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨V, hVi⟩ := P.v_int i
    obtain ⟨h0, h1⟩ := hv i
    rw [hVi] at h0 h1 ⊢
    simp only [Int.floor_intCast]
    push_cast at h0 h1
    have h0' : (0:ℤ) ≤ V := by exact_mod_cast h0
    refine ⟨h0', ?_⟩
    have h2 : ((V.toNat : ℕ) : ℝ) ≤ S := by
      have : ((V.toNat : ℕ) : ℝ) = (V : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0'
      rw [this]; exact h1
    have := Nat.le_floor h2
    omega
  have hB : ∀ i, -((⌊η⌋₊ : ℕ) : ℤ) ≤ ⌊P.b i⌋ - E ∧ ⌊P.b i⌋ - E ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨B, hBi⟩ := P.b_int i
    have h1 := hb i
    rw [hBi, hE] at h1
    rw [hBi]
    simp only [Int.floor_intCast]
    have h2 : (((B - E).natAbs : ℕ) : ℝ) ≤ η := by
      rw [Nat.cast_natAbs]; push_cast at h1 ⊢; exact h1
    have h3 := Nat.le_floor h2
    have h4 : |B - E| ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    exact abs_le.mp h4
  simp only [jT1, jR, jW, cloud, lows, block, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
    Finset.mem_univ, true_and, Multiset.mem_range] at hu
  cases s with
  | true =>
    simp only [szT, if_true, Bool.not_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [if_true, Multiset.mem_map, Multiset.mem_add, Finset.mem_val, Finset.mem_univ,
      true_and] at hu
    obtain ⟨x, (hx | hx) | hx, rfl⟩ := hu
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hV i
      left; rw [hEf, ht1]; constructor <;> omega
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hB i
      right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega
  | false =>
    simp only [szT, Bool.not_false, if_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [Bool.false_eq_true, if_false, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
      Finset.mem_univ, true_and] at hu
    obtain ⟨x, hx | hx, rfl⟩ := hu
    · obtain ⟨y, hy | hy, rfl⟩ := hx
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hV i
        left; rw [hEf, ht1]; constructor <;> omega
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hB i
        right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega

end GlobalTheory
end

