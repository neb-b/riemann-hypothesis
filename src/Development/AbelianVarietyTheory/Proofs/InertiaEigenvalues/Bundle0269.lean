module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEllStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_unramified_away_from_ell : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  first | exact @GlobalTheory.CycUnram.main | exact GlobalTheory.CycUnram.main | (intros; apply GlobalTheory.CycUnram.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelIntegersMemClosureLevels
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.LevelGen

theorem chain_pow {l : ℕ} {M : Type} [Monoid M] (ζ : ℕ → M) (h : ∀ j, ζ (j + 1) ^ l = ζ j)
    (j k : ℕ) : ζ (j + k) ^ (l ^ k) = ζ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc ζ (j + (k + 1)) ^ (l ^ (k + 1)) = (ζ (j + k + 1) ^ l) ^ (l ^ k) := by
          rw [pow_succ', pow_mul, ← add_assoc]
      _ = ζ j := by rw [h, ih]

theorem chain_primitive {l : ℕ} [Fact l.Prime] {M : Type} [CommMonoid M] (ζ : ℕ → M)
    (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (j : ℕ) :
    IsPrimitiveRoot (ζ (j + 1)) (l ^ (j + 1)) := by
  have hfin : ζ (j + 1) ^ l ^ (j + 1) = 1 := by
    have := chain_pow ζ h 0 (j + 1)
    rw [zero_add] at this
    rw [this, h0]
  have hnot : ¬ ζ (j + 1) ^ l ^ j = 1 := by
    have := chain_pow ζ h 1 j
    rw [add_comm 1 j] at this
    rw [this]
    exact h1
  rw [← orderOf_eq_prime_pow hnot hfin]
  exact IsPrimitiveRoot.orderOf _

theorem mem_closure_all (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l) (h0 : ζ 0 = 1)
    (h1 : ζ 1 ≠ 1) (h : ∀ j, ζ (j + 1) ^ l = ζ j) (s : ℕ) :
    ∀ α : Om l, α ∈ Ks K (s + 1) → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} := by
  induction s with
  | zero =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (0 + 1)) l := by
      simpa using chain_primitive ζ h0 h1 h 0
    obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow l K (ζ (0 + 1)) hp α hα hn
    refine AddSubgroup.sum_mem _ (fun a _ => AddSubgroup.subset_closure ?_)
    exact ⟨a, y a, (hy a).1, (hy a).2, mul_comm _ _⟩
  | succ s ih =>
    intro α hα hn
    have hp : IsPrimitiveRoot (ζ (s + 1 + 1)) (l ^ (s + 1 + 1)) := chain_primitive ζ h0 h1 h (s + 1)
    have hα' : α ∈ Ks K (s + 1 + 1) := hα
    obtain ⟨y, hy, rfl⟩ := (GlobalTheory.Cyc.integers_eq_sum_zeta_pow l K (s + 1 + 1) (by omega)
      (ζ (s + 1 + 1)) hp).1 α hα' hn
    refine AddSubgroup.sum_mem _ (fun a _ => ?_)
    have hya : y a ∈ Ks K (s + 1) := by simpa using (hy a).1
    have hmem := ih (y a) hya (hy a).2
    have hle : AddSubgroup.closure
        {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1) ^ n} ≤
        (AddSubgroup.closure
          {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (s + 1 + 1) ^ n}).comap
          (AddMonoidHom.mulLeft (ζ (s + 1 + 1) ^ (a : ℕ))) := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨n, c, hc, hcn, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨(a : ℕ) + l * n, c, hc, hcn, ?_⟩
      simp only [AddMonoidHom.coe_mulLeft]
      rw [← h (s + 1), pow_add, pow_mul]
      ring
    exact hle hmem

end GlobalTheory.Cyc.LevelGen


open GlobalTheory.Cyc.LevelGen in
theorem GlobalTheory.Cyc.integers_mem_closure_levels : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s : ℕ, 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ j ^ n} := by
  intro l _ K ζ h0 h1 h s hs α hα hn
  set S : AddSubgroup (Om l) := AddSubgroup.closure
    {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧
      x = c * ζ j ^ n} with hS
  have hl : 1 < l := (Fact.out : l.Prime).one_lt

  have hconst : ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → c ∈ S := by
    intro c hc hcn
    have hp : IsPrimitiveRoot (ζ 1) l := by simpa using chain_primitive ζ h0 h1 h 0
    have hsum := hp.geom_sum_eq_zero hl
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hr : Finset.range l = Finset.range (m + 1) := by rw [hm]
    rw [hr, Finset.sum_range_succ', pow_zero] at hsum
    have hc' : c = ∑ i ∈ Finset.range m, (-c) * ζ 1 ^ (i + 1) := by
      rw [← Finset.mul_sum, eq_neg_of_add_eq_zero_left hsum]
      ring
    rw [hc']
    refine AddSubgroup.sum_mem _ (fun i hi => AddSubgroup.subset_closure ?_)
    have hi' := Finset.mem_range.1 hi
    refine ⟨1, i + 1, -c, le_rfl, hs, ?_, neg_mem hc, by rwa [norm_neg], rfl⟩
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hlev : ∀ j, j ≤ s → ∀ (n : ℕ) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → c * ζ j ^ n ∈ S := by
    intro j
    induction j with
    | zero =>
      intro _ n c hc hcn
      rw [h0, one_pow, mul_one]
      exact hconst c hc hcn
    | succ j ih =>
      intro hj n c hc hcn
      by_cases hd : l ∣ n
      · obtain ⟨m, rfl⟩ := hd
        rw [pow_mul, h j]
        exact ih (by omega) m c hc hcn
      · exact AddSubgroup.subset_closure ⟨j + 1, n, c, by omega, hj, hd, hc, hcn, rfl⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hmem := mem_closure_all l K ζ h0 h1 h t α hα hn
  have hle : AddSubgroup.closure
      {x : Om l | ∃ (n : ℕ) (c : Om l), c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ (t + 1) ^ n} ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro x ⟨n, c, hc, hcn, rfl⟩
    exact hlev (t + 1) le_rfl n c hc hcn
  exact hle hmem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZeta
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.LevExp

theorem eq_exp {F : Type} [Field F] [CharZero F] [Algebra ℚ F] (E : PowerSeries F)
    (h0 : PowerSeries.constantCoeff E = 1) (h1 : PowerSeries.derivative (R := F) E = E) :
    E = PowerSeries.exp F := by
  exact PowerSeries.exp_unique_of_derivative_eq_self h1 h0

theorem map_poly {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {n : ℕ} (f : LetA O n →ₐ[O] A)
    (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) = Polynomial.aeval (f letπ) (p i) := by
  have hfam : f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      f (fun _ => ((p i : Polynomial O) : PowerSeries O)) := by
    have h := hf ((fun j => ((p j : Polynomial O) : PowerSeries O)) -
      (fun _ => ((p i : Polynomial O) : PowerSeries O))) (by simp)
    rwa [map_sub, sub_eq_zero] at h
  rw [hfam]
  have hg : f.comp ((Pi.constAlgHom O (ZMod n) (PowerSeries O)).comp
      (Polynomial.coeToPowerSeries.algHom O)) = Polynomial.aeval (f letπ) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.coeToPowerSeries.algHom_apply,
      Polynomial.coe_X, Algebra.algebraMap_self, PowerSeries.map_id]
    rfl
  have h2 := congrArg (fun φ => φ (p i)) hg
  simp only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
    PowerSeries.map_id] at h2
  exact h2

theorem map_poly_series {O L : Type} [CommRing O] [CommRing L] [Algebra O L] {n : ℕ}
    (f : LetA O n →ₐ[O] PowerSeries L) (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      Polynomial.aeval (f letπ) ((p i).map (algebraMap O L)) := by
  rw [map_poly f i hf p, Polynomial.aeval_map_algebraMap]

theorem lev_isExp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  intro l _ P K s LL Γ R i ζ hζ a
  have hπ : R.lev i ζ letπ = PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1 := by
    obtain ⟨E, hE0, hE1, hE⟩ := R.lev_π i ζ (by rw [P.PD_p K]; exact hζ)
    rw [eq_exp E hE0 hE1] at hE
    rw [← hE]
    ring
  have htr : ∀ m : ℕ, Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1)
      (PowerSeries.trunc m (toLL a i)) =
      R.lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial ↥(OL LL)) : PowerSeries ↥(OL LL))) := by
    intro m
    rw [map_poly_series (R.lev i ζ) i (R.lev_letter i ζ) (fun j => PowerSeries.trunc m (a j)), hπ]
    simp only [toLL, PowerSeries.trunc_map]
  intro k
  simp only [htr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (l : ℝ) ^ (-(r : ℝ)) < ε := by
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
    refine ⟨r, ?_⟩
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
    exact hr
  obtain ⟨m₀, hm₀⟩ := R.lev_cont i ζ a k r
  refine ⟨m₀, fun m hm => ?_⟩
  have hv := hm₀ m hm
  rw [← WithTop.coe_natCast] at hv
  have hn := ((NormVal.locPrime_v_normalised l P LL).2.1 _ (r : ℚ)).1 hv
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  calc _ = _ := by push_cast; rfl
    _ ≤ _ := hn
    _ = (l : ℝ) ^ (-(r : ℝ)) := by push_cast; rfl
    _ < ε := hr

end GlobalTheory.HWL.LevExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivial
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem resΓ_eq_one_of_chi {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) (h1 : P.χQ g = 1) : W.resΓ g = 1 := by
  apply W.χΓ_inj
  rw [map_one W.χΓ]
  apply Units.ext
  apply Subtype.ext
  have h3 := W.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at h3
  exact h3

theorem hinf_fixes_εroot_and_resΓ_eq_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l),
    (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧
    ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K,
      ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  intro l _ P AI K
  have hχ : ∀ g ∈ Hinf K, P.χQ g = 1 := fun g hg =>
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g
      (IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Kinf K from le_sup_left) hg)).2.1 hg
  refine ⟨fun g hg j => ?_, fun s LL hG W g hg => ?_⟩
  · have := GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g 1 (by simp [hχ g hg]) j
    rwa [pow_one] at this
  · have h1 : Ks K s ≤ Kinf K := by
      apply sup_le_sup_left _ _
      apply IntermediateField.adjoin.mono
      intro x hx
      exact ⟨s, hx⟩
    have h2 : K.1 ≤ Ks K s := hG.2.2.1
    have hgK : g ∈ GK K := IntermediateField.fixingSubgroup_antitone (h2.trans h1) hg
    exact ⟨hgK, resΓ_eq_one_of_chi P W ⟨g, hgK⟩ (hχ g hg)⟩

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisFiniteOfIsDR
section
noncomputable section

namespace GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  have h : Function.Injective
      (LinearMap.lTensor V (PD.ι.toLinearMap.restrictScalars Qp)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ PD.ι_inj
  exact h

theorem ιV_actVB (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_Dcris_le (ρ : Representation LL G V) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) ≤ DdR PD ρ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe] at hx
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hx ⊢
  intro g
  rw [← ιV_actVB, hx g]

theorem DdR_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(DdR PD ρ) := by
  by_cases hV : finrank LL V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
    have h0 : ∀ x : V ⊗[Qp] BdR, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
      | add a c ha hc => rw [ha, hc, add_zero]
    haveI : Subsingleton ↥(DdR PD ρ) :=
      ⟨fun x y => Subtype.ext ((h0 x).trans (h0 y).symm)⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

theorem Dcris_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := DdR_finite PD ρ h
  haveI : FiniteDimensional LL ↥((Dcris PD ρ).map (ιV PD (LL := LL) (V := V))) :=
    Submodule.finiteDimensional_of_le (map_Dcris_le PD ρ)
  exact Module.Finite.equiv
    (Submodule.equivMapOfInjective _ (ιV_injective PD) (Dcris PD ρ)).symm

end Generic

end GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.DcrisFin.dcris_finite_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsDR (P.PD K) ρ → Module.Finite ℚ_[l] ↥(Dcris (P.PD K) ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI := (P.PD K).finK
  exact GlobalTheory.DcrisFin.Dcris_finite (P.PD K) ρ h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel
section
noncomputable section

namespace GlobalTheory.GLq.LabelDet

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Formalism.CyclotomicNorms Polynomial
open scoped Classical ComplexOrder

variable {g : ℕ} [hg : Fact g.Prime]


open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.isIrr_hom {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ) :
    _root_.GlobalTheory.GLq.IsIrr (fun x : G => ((φ x : ℂˣ) : ℂ)) := by
  have hchar : ∀ x : G, (FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ)).character x = φ x := by
    intro x
    have : _root_.GlobalTheory.GLp.Model.chRep φ x = (φ x : ℂ) • LinearMap.id := by
      ext; simp [_root_.GlobalTheory.GLp.Model.chRep_apply]
    simp [FDRep.character, FDRep.of_ρ, this]
  refine ⟨FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ), ?_, hchar⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp [hchar, Nat.card_eq_fintype_card]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.theta_gen_pow (L : _root_.GlobalTheory.GLq.LabelDatum g) {x : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hx : x ^ (g ^ 1 - 1) = 1) (n : ℕ) :
    _root_.GlobalTheory.GLq.thetaOf L 1 x (L.gen 1 ^ n) =
      L.teich x ^ n :=
  _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos hx n


open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.gen_one_mem (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 := by
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.GLp.Model.exists_gen L
  exact ⟨u, hu⟩


open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_inPar (a b : ℕ) (M : _root_.GlobalTheory.GLq.Mt g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a M) :
    M.det = (_root_.GlobalTheory.GLq.tl a M).det * (_root_.GlobalTheory.GLq.br a b M).det := by
  have key : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks (_root_.GlobalTheory.GLq.tl a M)
      (M.submatrix (Fin.castAdd b) (Fin.natAdd a)) 0 (_root_.GlobalTheory.GLq.br a b M) := by
    ext (i | i) (j | j)
    · show M (Fin.castAdd b i) (Fin.castAdd b j) = _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j
      have hi := i.isLt
      have hj := j.isLt
      unfold _root_.Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dite_eq_left ⟨by omega, by omega⟩]
      rfl
    · simp
    · exact h _ _ (by simp) (by simp)
    · simp [_root_.GlobalTheory.GLq.br, _root_.Formalism.MainNotions.ArithmeticCylinders.entN, Fin.natAdd]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, key, Matrix.det_fromBlocks_zero₂₁]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_toG {n : ℕ} (M : _root_.GlobalTheory.GLq.Mt g n) (h : M.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG M) : (ZMod g)ˣ) : ZMod g) = M.det := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dite_eq_left ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h))]
  simp [Matrix.GeneralLinearGroup.val_det_apply]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.det_par (a b : ℕ) (p : _root_.GlobalTheory.GLq.Gn g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a (p : _root_.GlobalTheory.GLq.Mt g (a + b))) :
    Matrix.GeneralLinearGroup.det p =
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.tl a
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) *
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.br a b
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) := by
  have hdet := _root_.GlobalTheory.GLq.LabelDet.det_inPar a b _ h
  have hp := (Matrix.GeneralLinearGroup.det p).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hp
  rw [hdet] at hp
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp
  apply Units.ext
  rw [Units.val_mul, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h1, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h2,
    Matrix.GeneralLinearGroup.val_det_apply, ← hdet]

open Polynomial in
open scoped Classical ComplexOrder in
variable {g : ℕ} [hg : Fact g.Prime] in
theorem _root_.GlobalTheory.GLq.LabelDet.toG_one {n : ℕ} : _root_.GlobalTheory.GLq.toG (1 : _root_.GlobalTheory.GLq.Mt g n) = 1 := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dite_eq_left isUnit_one]
  exact Units.ext (by simp)

end GlobalTheory.GLq.LabelDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixedLiftOfFixedModPrimeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_fixed_lift_of_fixed_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)) (x : RW LL), (∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) → ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | exact GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | (intros; apply GlobalTheory.Decompl.exists_fix_lift_of_fix_mod <;> assumption)
end

