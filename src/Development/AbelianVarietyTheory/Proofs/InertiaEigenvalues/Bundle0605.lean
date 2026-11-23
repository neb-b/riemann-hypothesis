module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.SmoothDesignExistence.ContinuousHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0596
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionsLowAndPullback
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.LowLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem mem_latSpan {ι : Type} (e : ι → ℤ → M) (x : ι) : e x ∈ latSpan (LL := LL) e :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

theorem neg_eq_zero {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e))
    (x : ι) (k : ℤ) (hk : k < 0) : e x k = 0 :=
  ((h _).1 (mem_latSpan e x)).2 k hk

theorem span_const {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e)) :
    Submodule.span LL (Set.range fun x => e x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan e x)).1 0
  · intro d hd
    have key : ∀ f ∈ latSpan (LL := LL) e, f 0 ∈ Submodule.span LL (Set.range fun x => e x 0) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨a, x, rfl⟩ := hf
        unfold conv
        rw [finsum_eq_single _ 0]
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_⟩)
          simp
        · intro j hj
          rw [neg_eq_zero h x _ (by omega), smul_zero]
      | zero => exact Submodule.zero_mem _
      | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
      | smul c f _ hf => exact Submodule.smul_mem _ c hf
    have hmem : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) e := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk
        simpa using hd
      · rw [Pi.single_eq_of_ne hk]
        exact D.zero_mem
    simpa using key _ hmem

theorem span_const_map {M' ι : Type} [AddCommGroup M'] [Module LL M'] {e : ι → ℤ → M}
    {D : Submodule LL M} (h : Std D (latSpan e)) (L : M →ₗ[LL] M') (g : ι → M')
    (hg : ∀ x, g x = L (e x 0)) : Submodule.span LL (Set.range g) = D.map L := by
  rw [← span_const h, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext x
  exact hg x

theorem conv_low (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) (j : ℤ)
    (hj : j < k) : conv ((PowerSeries.X * w) ^ k) f j = 0 := by
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m < k
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
  · rw [hf _ (by omega), smul_zero]

theorem conv_lead (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) :
    conv ((PowerSeries.X * w) ^ k) f k = PowerSeries.constantCoeff w ^ k • f 0 := by
  unfold conv
  rw [finsum_eq_single _ k]
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl]
    simp
  · intro m hmk
    by_cases hm : m < k
    · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem pullback_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] {P : ι → ℕ → Prop}
    (y : ∀ x k, P x k → ι) (lN : ι → ℤ → M') (e e' : ι → ℤ → M) {D D' : Submodule LL M}
    (L : M →ₗ[LL] M') (φ : M →ₗ[LL] M) (c : LL) (q : PowerSeries LL)
    (hq : ∃ w, IsUnit w ∧ q = PowerSeries.X * w)
    (hN : ∀ x k, lN x k = L (e x k)) (hmem : ∀ x k, e x k ∈ D) (hS : Std D' (latSpan e'))
    (hφ : ∀ x k hk j, e (y x k hk) j = conv (q ^ k) (fun j => c ^ j • φ (e' x j)) j)
    (hsurj : Set.SurjOn φ D' D) (hex : ∀ x, ∃ k, P x k) :
    (∀ x k hk (j : ℤ), lN (y x k hk) j ∈ D.map L ∧ (j < k → lN (y x k hk) j = 0)) ∧
      Submodule.span LL {z | ∃ x k hk, z = lN (y x k hk) (k : ℕ)} = D.map L := by
  obtain ⟨w, hw, rfl⟩ := hq
  have hm : ∀ x k, lN x k ∈ D.map L := fun x k => by
    rw [hN]
    exact Submodule.mem_map_of_mem (hmem x k)
  have hg0 : ∀ x, ∀ j < (0 : ℤ), c ^ j • φ (e' x j) = 0 := by
    intro x j hj
    rw [neg_eq_zero hS x j hj, map_zero, smul_zero]
  have hc : PowerSeries.constantCoeff w ≠ 0 := (hw.map PowerSeries.constantCoeff).ne_zero
  refine ⟨fun x k hk j => ⟨hm _ _, fun hj => ?_⟩, le_antisymm ?_ ?_⟩
  · rw [hN, hφ, conv_low w k _ (hg0 x) j hj, map_zero]
  · rw [Submodule.span_le]
    rintro _ ⟨x, k, hk, rfl⟩
    exact hm _ _
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd', rfl⟩ := hsurj hd
    have hd'' : d' ∈ Submodule.span LL (Set.range fun x => e' x 0) := by
      rw [span_const hS]
      exact hd'
    clear hd hd'
    induction hd'' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hex x
      have h2 : L (φ (e' x 0)) = (PowerSeries.constantCoeff w ^ k)⁻¹ • lN (y x k hk) k := by
        rw [hN, hφ, conv_lead w k _ (hg0 x), map_smul, inv_smul_smul₀ (pow_ne_zero _ hc)]
        simp only [zpow_zero, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, k, hk, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha

theorem low_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] (a : ι → ι) (lN : ι → ℤ → M')
    (e : ι → ℤ → M) {D : Submodule LL M} (L : M →ₗ[LL] M') (q : PowerSeries LL) (hq : q = 1)
    (ha : ∀ x k, lN (a x) k = conv q (lN x) k)
    (hN : ∀ x k, lN x k = L (e x k)) (hS : Std D (latSpan e)) :
    (∀ x (k : ℤ), lN (a x) k ∈ D.map L ∧ (k < 0 → lN x k = 0)) ∧
      Submodule.span LL (Set.range fun x => lN (a x) 0) = D.map L := by
  subst hq
  simp only [conv_one] at ha
  refine ⟨fun x k => ⟨?_, fun hk => ?_⟩, span_const_map hS L _ fun x => by rw [ha, hN]⟩
  · rw [hN]
    exact Submodule.mem_map_of_mem (((hS _).1 (mem_latSpan e _)).1 k)
  · rw [hN, neg_eq_zero hS x k hk, map_zero]

end Series

theorem exists_primitive {L : Type} [Field L] {l : ℕ} (hl : l.Prime) {ζ : L} {m : ℕ}
    (h : ζ ^ (l ^ m) = 1) : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩

theorem pow_pow_pred {L : Type} [Field L] {l s : ℕ} (hs : 1 ≤ s) {ζ : L}
    (h : IsPrimitiveRoot ζ (l ^ s)) : (ζ ^ l) ^ (l ^ (s - 1)) = 1 := by
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  exact h.pow_eq_one


set_option maxHeartbeats 1000000 in
theorem expansions_low_and_pullback : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW F Cm l _ K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hstd : ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (latSpan (ex C h T i ζ)) := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT
  refine ⟨fun i ζ hζ hX => ?_, fun i ζ τ hτ => ?_⟩
  · have hm : ζ ^ (l ^ hζ.choose) = 1 := by
      have := hζ.choose_spec
      rwa [show ((D.loc l).PD K).p ^ hζ.choose = l ^ hζ.choose from congrArg (· ^ _) hp] at this
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ (exists_primitive Fact.out hm)
    exact low_span (fun x => (letE i : AA K LL) • x) (W.levN T i ζ) (ex C h T i ζ) _
      (W.lev i ζ (letE i)) hl.2.1 (W.levN_smul T i ζ (letE i))
      ((C.C K s LL h).tie.levN_eq T i ζ) (hstd i ζ (hl.2.2.2.2.1.1 hX))
  · have hprim : IsPrimitiveRoot ζ (l ^ s) :=
      ((GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hτ).1
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩
    have hφ : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        ex C h T i ζ ⟨_, hk⟩ j = conv ((W.lev i ζ W.Q) ^ k) (fun j => (l : ↥LL.1) ^ j •
          φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x j)) j := by
      intro x k hk j
      have h1 := (C.C K s LL h).tie.levB_φ T hT i ζ ⟨s, by rw [hp]; exact hprim⟩ x k hk j
      rw [map_pow, hp] at h1
      exact h1
    exact pullback_span (P := fun (x : ↥(W.N T)) k => W.Q ^ k • W.φD T x ∈ W.N T)
      (fun _ _ hk => ⟨_, hk⟩) (W.levN T i ζ) (ex C h T i ζ) (ex C h T (i - 1) (ζ ^ l)) _ _ _ _
      (hl.2.2.2.1 hprim).1 ((C.C K s LL h).tie.levN_eq T i ζ) ((C.C K s LL h).tie.levB_mem T i ζ)
      (hstd (i - 1) (ζ ^ l) (pow_pow_pred h.1 hprim)) hφ
      ((GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i).surjOn (fun x => W.N_φ T x x.2)

end GlobalTheory.NL.LowLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdm

theorem fontaineProperties_all_places : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i :=
  fun D i => Formalism.MainNotions.Pk.font_of_all_places (fun l _ K LL => GlobalTheory.FontaineAll.fontaineAt_all D l K LL) i

end GlobalTheory.FontaineAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorusStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  first | exact @GlobalTheory.JR.LinDesc.fubini_cutoff | exact GlobalTheory.JR.LinDesc.fubini_cutoff | (intros; apply GlobalTheory.JR.LinDesc.fubini_cutoff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.MonZero

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem galOB_mul (g h : GQ l) (r : OB l O) :
    galOB O (g * h) r = galOB O g (galOB O h r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o w =>
    simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact congrArg (fun z => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 g h w)

theorem actB_mul (T : LocLat (Gl l) ℚ_[l] K O) (g h : Gl l) (x : TW (OB l O) T) :
    actB (sQ l) T (g * h) x = actB (sQ l) T g (actB (sQ l) T h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r t =>
    have ht : T.actT (g * h) t = T.actT g (T.actT h t) :=
      Subtype.ext (show T.ρ (g * h) t = T.ρ g (T.ρ h t) by simp)
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_mul, galOB_mul, ht]

theorem actB_one_tmul (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (t : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l O) ⊗ₜ[O] t) = (1 : OB l O) ⊗ₜ[O] T.actT g t := by
  simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem step_mul {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b) (g h k : Gl l)
    (hg : g = h * k) (hh : sQ l h ∈ GK (ϖ.field a)) (hk : sQ l k ∈ ϖ.GKinf) :
    ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  obtain ⟨xk, hxk⟩ := _root_.GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf l a e O K t ϖ ι η H D T R y hy b hb k hk
  obtain ⟨xh, hxh⟩ := _root_.GlobalTheory.BKGal.potential_cocycle_mem_lpow l a e O K t ϖ ι η H D T R hηH hlH y hy c hc b hb h hh
    (_root_.GlobalTheory.BKGal.coboundary_mem_lattice_of_mon_eq_zero hF l a e O K t ϖ hl2 ι η H D T R y hy hM b hb h hh)
  refine ⟨(l : O) ^ c • T.actT h xk + xh, ?_⟩
  have e1 : actB (sQ l) T g b - b = actB (sQ l) T h (actB (sQ l) T k b - b) + (actB (sQ l) T h b - b) := by
    rw [hg, actB_mul, map_sub]; abel
  rw [e1, hxk, actB_one_tmul, smul_add, hxh, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]

theorem cob_of (T : LocLat (Gl l) ℚ_[l] K O) (b : TW (OB l O) T) (c : ℕ) (X : Gl l → ↥T.L.T)
    (hX : ∀ g, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] X g) :
    IsCobOf (sQ l) T b (fun g => ((l : K) ^ c)⁻¹ • (X g : T.V)) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  intro g n x hx
  apply smul_cancel T c
  rw [smul_comm ((l : O) ^ c) ((l : O) ^ n), hX g, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  rw [← algebraMap_smul K ((l : O) ^ c), ← algebraMap_smul K ((l : O) ^ n), map_pow, map_pow, map_natCast, hx,
    smul_comm ((l : K) ^ n), smul_smul ((l : K) ^ c), mul_inv_cancel₀ hne, one_smul]

theorem exists_cob {a e : ℕ} [NeZero a] [NeZero e] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (hF : GlobalTheory.Published.FontaineBcris) (hl2 : l ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T)
    (hηH : η < H) (hlH : 8 * H + 1 < l) (y : Vec K a ι) (hy : y ∈ D.Y) (hM : D.Mon y = 0) (c : ℕ)
    (hc : (l : K) ^ c • D.zeta y ∈ D.MM) (b : TW (OB l O) T) (hb : R.IsPotential y b)
    (hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf) :
    ∃ κ : Gl l → T.V, IsCobOf (sQ l) T b κ ∧ ∀ g, (l : K) ^ c • κ g ∈ T.L.T := by
  have hX : ∀ g : Gl l, ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
    intro g
    obtain ⟨h, k, hg, hh, hk⟩ := hdec g
    exact step_mul t ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb g h k hg hh hk
  choose X hX using hX
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hne : (l : K) ^ c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine ⟨_, cob_of T b c X hX, fun g => ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  exact (X g).2

end GlobalTheory.BKGal.MonZero

theorem GlobalTheory.BKGal.classOf_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  intro hF l _ a e _ _ ϖ LL _ _ ι _ _ η H D T R Pl AI hstd hηH hlH y hy hM c hc
  have hl2 : l ≠ 2 := by omega
  obtain ⟨b, hb⟩ := (_root_.GlobalTheory.GalPot.potential_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).1 y hy
  have hdec : ∀ g : Gl l, ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ sQ l k ∈ ϖ.GKinf := by
    intro g
    obtain ⟨h, hh, k, hk, hgk⟩ := (_root_.GlobalTheory.TameCover.main l a e ϖ LL).1 (sQ l g)
    let hG : Gl l := ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
    refine ⟨hG, hG⁻¹ * g, (mul_inv_cancel_left hG g).symm, hh, ?_⟩
    have e1 : sQ l (hG⁻¹ * g) = k := by
      rw [map_mul, map_inv, show sQ l g = h * k from hgk]
      show h⁻¹ * (h * k) = k
      group
    rw [e1]; exact hk
  obtain ⟨κ, hcob, hT⟩ := GlobalTheory.BKGal.MonZero.exists_cob (thetaW a LL) ϖ hF hl2 D T R hηH hlH y hy hM c hc b hb hdec
  have hcl : R.ClassOf y κ := ⟨b, hb, hcob⟩
  have hZ1c : κ ∈ continuousCocycles T.ρ := _root_.GlobalTheory.CobCont.main l hl2 LL T b κ hcob
  obtain ⟨β, -, -, -, hf⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hstd
  have hZ1f : κ ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := (hf κ hZ1c).2 ⟨b, hcob⟩
  refine ⟨(l : ↥LL.1) ^ c • κ, ?_, (_root_.GlobalTheory.GalPot.potential_class l a e _ _ (thetaW a LL) ϖ ι η H D T R).2.2.1 y κ c hcl⟩
  refine ⟨⟨(continuousCocycles T.ρ).smul_mem _ hZ1c, ?_⟩, (finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ).smul_mem _ hZ1f⟩
  intro g _
  exact hT g
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseField
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.TransitionThirdCase


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jD_Qpow (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (m : ℕ)
    (x : ((HW l).W K s LL h).DD T) :
    ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).Q ^ m • x) =
      (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m • ((F l).E K s LL h).tie.jD T x := by
  have hQ := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  rw [← algebraMap_smul ((HW l).W K s LL h).EE (((HW l).W K s LL h).Q ^ m) x,
    ((F l).E K s LL h).tie.jD_smul, ((F l).E K s LL h).tie.ioE_ext, map_pow, hQ, map_pow]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT m y' hy'
  have hB := GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0
  have hB3 := hB.2.2 T (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl (↥(OL LL)) ↥T.L.T)
    (fun g t => rfl)
  have hid : (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap) = LinearMap.id := TensorProduct.map_id
  have hR := hB3.1
  have hN := hB3.2 hT (restrict_crys D hle T hT)
  have hy1 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') ∈
      Set.range (((F l).E K s LL h).tie.jD T) := hR ▸ ⟨_, ⟨y', rfl⟩, rfl⟩
  have hy2 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y')) ∈
      ((F l).E K s LL h).tie.jD T '' (((HW l).W K s LL h).N T : Set (((HW l).W K s LL h).DD T)) :=
    hN ▸ ⟨_, ⟨_, hy', rfl⟩, rfl⟩
  have hm1 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  have hm2 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y'))
  refine hy1.elim fun y hy => hy2.elim fun z hz => ⟨y, ?_, hy.trans hm1⟩
  show ((HW l).W K s LL h).Q ^ m • y ∈ ((HW l).W K s LL h).N T
  have e : z = ((HW l).W K s LL h).Q ^ m • y := by
    apply ((F l).E K s LL h).tie.jD_inj T
    rw [hz.2, hm2, jD_Qpow, jD_Qpow, hy, hm1]
    rfl
  exact e ▸ hz.1

end GlobalTheory.NL.TransitionThirdCase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantEtaleBasisChangeByOEUnitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  first | (exact @GlobalTheory.ChangeEtaleBasis.main) | (exact GlobalTheory.ChangeEtaleBasis.main) | (intros; apply GlobalTheory.ChangeEtaleBasis.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def lfac {a b : ℕ} (σ : CG E a) (σ' : CG E b) (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  locL (Ideal.absNorm w.asIdeal) (sat σ w) ((sat σ' w).map (Units.map (starRingEnd ℂ).toMonoidHom)) s

def IsGood (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) ∧
    ∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w

def dcoef {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ :=
  ‖(((sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))).map (· ^ (r + 1))).sum‖ ^ 2 /
    ((r : ℝ) + 1)

def dexp (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ := ((r : ℝ) + 1) * Real.log (Ideal.absNorm w.asIdeal)

theorem dcoef_nonneg {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    0 ≤ dcoef σ σ' w r := div_nonneg (sq_nonneg _) (by positivity)

theorem dexp_nonneg (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : 0 ≤ dexp w r :=
  mul_nonneg (by positivity) (Real.log_nonneg (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    exact_mod_cast this.le))

end GlobalTheory.RSNonvan
end
end

