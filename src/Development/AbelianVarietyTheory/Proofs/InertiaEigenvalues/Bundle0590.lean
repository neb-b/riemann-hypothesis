module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitive
section
open Matrix GlobalTheory.ExportSeries

namespace GlobalTheory.ExportSeries

theorem sum_univCoef_eq_prim : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n →
    ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  intro k C _ _ _ _ r n hrn β κ y
  classical
  letI := Fintype.ofFinite (Planes k r n)

  have hterm : ∀ U : Planes k r n, ∑ c, (univTerm β κ y U).coeff c = if Compl U.1 y then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases h : Compl U.1 y
    · rw [dite_eq_left h, if_pos h]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · rw [dite_eq_right h, if_neg h]
      simp
  have hsum : ∑ c, univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      (Nat.card {U : Planes k r n // Compl U.1 y} : ℚ) := by
    simp only [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun U _ => hterm U, Finset.sum_boole]
    congr 2
    rw [Nat.card_eq_fintype_card (α := {U : Planes k r n // Compl U.1 y}), Fintype.card_subtype]
  rw [hsum]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have ht : r + t - r = t := by omega
  rw [ht]
  set R := Submodule.span k (Set.range y.row) with hR
  have hRle : Module.finrank k R ≤ r := by
    have := finrank_range_le_card (R := k) y.row
    rw [Fintype.card_fin] at this
    exact this
  have hcard : Nat.card {U : Planes k r (r + t) // Compl U.1 y} =
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} := by
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ (fun U => Compl U y)).trans
      (Equiv.subtypeEquivRight fun U => ?_))
    simp only [Compl, hR]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hcard, GlobalTheory.card_subspaces_sup_eq_top k r t R hRle]
  have hq : ((Nat.card k : ℚ) ^ (r * t)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne')
  have hli : LinearIndependent k y.row ↔ Module.finrank k R = r := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, eq_comm]
  unfold prim
  by_cases h : Module.finrank k R = r
  · rw [if_pos h, if_pos (hli.2 h)]
    push_cast
    exact inv_mul_cancel₀ hq
  · rw [if_neg h, if_neg (fun h' => h (hli.1 h'))]
    simp

end GlobalTheory.ExportSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundSeq

theorem tensor_fundamental_sequence :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  intro l _ P AI hT K LL _ _ V _ _ _ _
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT
  have hA : ∀ u : V ⊗[ℚ_[l]] P.R.B, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      x - φVB (P.PD K) (LL := LL) (V := V) x = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx⟩ := h1 b
      refine ⟨v ⊗ₜ x, ?_⟩
      have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
      rw [this, P.PD_φ, ← TensorProduct.tmul_sub, hx]
    | add u u' hu hu' =>
      obtain ⟨x, hx⟩ := hu
      obtain ⟨x', hx'⟩ := hu'
      refine ⟨x + x', ?_⟩
      rw [map_add (f := _), ← hx, ← hx']
      abel
  have hB : ∀ w : V ⊗[ℚ_[l]] P.R.BdR, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      φVB (P.PD K) (LL := LL) (V := V) x = x ∧
        ιV (P.PD K) (LL := LL) (V := V) x - w ∈ FilV (P.PD K) (LL := LL) (V := V) 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx, hx'⟩ := h2 K b
      refine ⟨v ⊗ₜ x, ?_, ?_⟩
      · have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
        rw [this, P.PD_φ, hx]
      · have : ιV (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).ι x := rfl
        rw [this, P.PD_ι, ← TensorProduct.tmul_sub]
        exact ⟨v ⊗ₜ ⟨P.ιB x - b, hx'⟩, rfl⟩
    | add w w' hw hw' =>
      obtain ⟨x, hx, hy⟩ := hw
      obtain ⟨x', hx', hy'⟩ := hw'
      refine ⟨x + x', by rw [map_add (f := _), hx, hx'], ?_⟩
      have := Submodule.add_mem _ hy hy'
      rw [map_add (f := _)]
      convert this using 1
      abel
  refine ⟨fun u w => ?_, fun x hx hF =>
    GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) x hx hF⟩
  obtain ⟨x₀, hx₀⟩ := hA u
  obtain ⟨x₁, hx₁, hy⟩ := hB (w - ιV (P.PD K) (LL := LL) (V := V) x₀)
  refine ⟨x₀ + x₁, _, hy, ?_, ?_⟩
  · rw [map_add (f := _), hx₁, ← hx₀]
    abel
  · rw [map_add (f := _)]
    abel

end GlobalTheory.FundSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevel
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL GlobalTheory.NL.Model

noncomputable section

namespace GlobalTheory.NL.LatLow

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_sum (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    conv e u k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • u (k - (j : ℤ)) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
  apply hj
  have : k - (j : ℤ) < m := by omega
  simp [hm _ this]

theorem conv_van (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    ∀ k < m, conv e u k = 0 := by
  intro k hk
  rw [conv_eq_sum e hm k 0 (by omega)]
  simp

theorem conv_mul (a b : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    conv (a * b) u = conv a (conv b u) := by
  funext k
  set N := (k - m).toNat + 1 with hN
  rw [conv_eq_sum _ hm k N (by omega), conv_eq_sum _ (conv_van b hm) k N (by omega)]
  have h1 : ∀ i ∈ Finset.range N, PowerSeries.coeff i a • conv b u (k - (i : ℤ)) =
      ∑ j ∈ Finset.range (N - i), (PowerSeries.coeff i a * PowerSeries.coeff j b) •
        u (k - ((i + j : ℕ) : ℤ)) := by
    intro i hi
    have := Finset.mem_range.1 hi
    rw [conv_eq_sum _ hm _ (N - i) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_range_diag_flip N (fun i j =>
    (PowerSeries.coeff i a * PowerSeries.coeff j b) • u (k - ((i + j : ℕ) : ℤ)))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have h2 : i + (n - i) = n := by omega
  rw [h2]

def tw (c : L) (Φ : M →ₗ[L] M) : (ℤ → M) →ₗ[L] (ℤ → M) where
  toFun f := fun k => c ^ k • Φ (f k)
  map_add' f g := by funext k; simp
  map_smul' a f := by funext k; simp [smul_comm a]

theorem tw_apply (c : L) (Φ : M →ₗ[L] M) (f : ℤ → M) (k : ℤ) : tw c Φ f k = c ^ k • Φ (f k) := rfl

theorem tw_van (c : L) (Φ : M →ₗ[L] M) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    ∀ k < m, tw c Φ u k = 0 := fun k hk => by simp [tw_apply, hm k hk]

theorem tw_conv {c : L} (hc : c ≠ 0) (Φ : M →ₗ[L] M) (a : PowerSeries L) {u : ℤ → M} {m : ℤ}
    (hm : ∀ k < m, u k = 0) :
    tw c Φ (conv a u) = conv (PowerSeries.rescale c a) (tw c Φ u) := by
  funext k
  set N := (k - m).toNat + 1 with hN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tw_apply, conv_eq_sum _ hm k N (by omega), conv_eq_sum _ (tw_van c Φ hm) k N (by omega),
    map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tw_apply, map_smul, smul_smul, smul_smul, PowerSeries.coeff_rescale, zpow_sub₀ hc, zpow_natCast]
  congr 1
  field_simp

theorem std_step {A DD : Type} [CommRing A] [AddCommGroup DD] [Module A DD] (N : Submodule A DD)
    (φ : DD → DD) (Q : A) (lev : A →* PowerSeries L) (hQ : IsUnit (lev Q))
    (e e' : ↥N →+ (ℤ → M)) (D D' : Submodule L M) (c : L) (hc : c ≠ 0) (Φ : M →ₗ[L] M)
    (hΦ : Set.BijOn Φ D' D)
    (hD : ∀ x k, e x k ∈ D) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, e x k = 0)
    (hsm : ∀ (a : A) (x : ↥N), e (a • x) = conv (lev a) (e x))
    (hφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hφinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set DD)))
    (heφ : ∀ (x : ↥N) (m : ℕ) (hx : Q ^ m • φ x ∈ N),
      e ⟨Q ^ m • φ x, hx⟩ = conv (lev (Q ^ m)) (tw c Φ (e' x)))
    (h' : Std D' (latSpan (LL := L) e')) : Std D (latSpan (LL := L) e) := by
  have hv' : ∀ x, ∀ k < (0 : ℤ), e' x k = 0 := fun x => ((h' _).1 (mem_latSpan _ x)).2
  have hinv : ∀ m : ℕ, ∃ w : PowerSeries L, w * lev (Q ^ m) = 1 := fun m => by
    rw [map_pow]
    exact (hQ.pow m).exists_left_inv
  have hspan : ∀ z ∈ Submodule.span A (φ '' (N : Set DD)), ∃ (m : ℕ) (hz : Q ^ m • z ∈ N),
      ∀ k < (0 : ℤ), e ⟨Q ^ m • z, hz⟩ k = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨m, hm⟩ := hφ x hx
      refine ⟨m, hm, ?_⟩
      rw [heφ ⟨x, hx⟩ m hm]
      exact conv_van _ (tw_van c Φ (hv' _))
    | zero =>
      refine ⟨0, by simp, fun k _ => ?_⟩
      have : (⟨Q ^ 0 • (0 : DD), by simp⟩ : ↥N) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]; rfl
    | add z z' _ _ hz hz' =>
      obtain ⟨m, hm, hz⟩ := hz
      obtain ⟨m', hm', hz'⟩ := hz'
      have key : Q ^ (m + m') • (z + z') =
          ((Q ^ m' • (⟨_, hm⟩ : ↥N) + Q ^ m • (⟨_, hm'⟩ : ↥N) : ↥N) : DD) := by
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, smul_smul, ← pow_add, add_comm m' m]
      refine ⟨m + m', key ▸ Subtype.mem _, fun k hk => ?_⟩
      have : (⟨Q ^ (m + m') • (z + z'), key ▸ Subtype.mem _⟩ : ↥N) =
          Q ^ m' • (⟨_, hm⟩ : ↥N) + Q ^ m • (⟨_, hm'⟩ : ↥N) := Subtype.ext key
      rw [this, map_add (f := _), hsm, hsm, Pi.add_apply, conv_van _ hz k hk, conv_van _ hz' k hk, add_zero]
    | smul a z _ hz =>
      obtain ⟨m, hm, hz⟩ := hz
      have key : Q ^ m • (a • z) = ((a • (⟨_, hm⟩ : ↥N) : ↥N) : DD) := by
        simp only [Submodule.coe_smul, smul_smul, mul_comm]
      refine ⟨m, key ▸ Subtype.mem _, fun k hk => ?_⟩
      have : (⟨Q ^ m • (a • z), key ▸ Subtype.mem _⟩ : ↥N) = a • (⟨_, hm⟩ : ↥N) := Subtype.ext key
      rw [this, hsm, conv_van _ hz k hk]
  have hv : ∀ x, ∀ k < (0 : ℤ), e x k = 0 := by
    intro y
    obtain ⟨j, hj⟩ := hφinv y y.2
    obtain ⟨m, hm, hz⟩ := hspan _ hj
    have : (⟨Q ^ m • Q ^ j • (y : DD), hm⟩ : ↥N) = Q ^ (m + j) • y :=
      Subtype.ext (by simp only [Submodule.coe_smul, smul_smul, pow_add])
    rw [this, hsm] at hz
    obtain ⟨w, hw⟩ := hinv (m + j)
    obtain ⟨b, hb⟩ := hs y
    have h2 := conv_van w hz
    rwa [← conv_mul _ _ hb, hw, conv_one] at h2
  have hmap : ∀ g ∈ latSpan (LL := L) e', tw c Φ g ∈ latSpan (LL := L) e := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, x, rfl⟩ := hg
      obtain ⟨m, hm⟩ := hφ x x.2
      obtain ⟨w, hw⟩ := hinv m
      refine Submodule.subset_span ⟨PowerSeries.rescale c a * w, ⟨_, hm⟩, ?_⟩
      rw [heφ x m hm, ← conv_mul _ _ (tw_van c Φ (hv' x)), mul_assoc, hw, mul_one,
        tw_conv hc Φ a (hv' x)]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add f g _ _ hf hg => rw [map_add (f := _)]; exact Submodule.add_mem _ hf hg
    | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ a hf
  intro f
  constructor
  · intro hf
    refine ⟨(latSpan_coeff _ D hD hs f hf).1, ?_⟩
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, x, rfl⟩ := hf
      exact conv_van a (hv x)
    | zero => exact fun _ _ => rfl
    | add f g _ _ hf hg => intro k hk; simp [hf k hk, hg k hk]
    | smul a f _ hf => intro k hk; simp [hf k hk]
  · rintro ⟨h1, h2⟩
    have : ∀ k, ∃ d ∈ D', Φ d = f k ∧ (k < 0 → d = 0) := by
      intro k
      by_cases hk : k < 0
      · exact ⟨0, D'.zero_mem, by rw [map_zero, h2 k hk], fun _ => rfl⟩
      · obtain ⟨d, hd, hd'⟩ := hΦ.surjOn (h1 k)
        exact ⟨d, hd, hd', fun h => absurd h hk⟩
    choose d hd hd1 hd2 using this
    have hg : (fun k => (c ^ k)⁻¹ • d k) ∈ latSpan (LL := L) e' :=
      (h' _).2 ⟨fun k => D'.smul_mem _ (hd k), fun k hk => by simp [hd2 k hk]⟩
    have h3 := hmap _ hg
    have : tw c Φ (fun k => (c ^ k)⁻¹ • d k) = f := by
      funext k
      rw [tw_apply, map_smul, smul_smul, mul_inv_cancel₀ (zpow_ne_zero k hc), one_smul, hd1]
    rwa [this] at h3

end Series


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem lat_low : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (Lat C h T i ζ) := by
  intro D HW F Cm l hl K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have main : ∀ (j : ℕ) (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (Lat C h T i ζ) := by
    intro j
    induction j with
    | zero =>
      intro i ζ h1 _
      obtain rfl : ζ = 1 := by simpa using h1
      exact GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero D HW F Cm l K s LL h T hT i
    | succ j ih =>
      intro i ζ h1 h2
      have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
        obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)
        exact ⟨r, hr ▸ IsPrimitiveRoot.orderOf ζ⟩
      have ih' := ih (i - 1) (ζ ^ l) (by rw [← pow_mul, ← pow_succ', h1])
        (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])
      have hQ : IsUnit (W.lev i ζ W.Q) :=
        ((GlobalTheory.T.wachLevel_expansion_at_root_of_unity D HW l K s LL h i ζ hprim).2.2.1 h2).2
      have hΦ := (GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i
      have hc : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
      refine std_step (W.N T) (W.φD T) W.Q (MonoidHomClass.toMonoidHom (W.lev i ζ)) hQ
        ((C.C K s LL h).tie.levB T i ζ) ((C.C K s LL h).tie.levB T (i - 1) (ζ ^ l))
        (Di (HW l) h T i) (Di (HW l) h T (i - 1)) (l : ↥LL.1) hc _ hΦ
        ((C.C K s LL h).tie.levB_mem T i ζ) ((C.C K s LL h).tie.levB_supp T i ζ)
        (ex_smul C h T i ζ) (W.N_φ T) (W.N_φinv T) ?_ ih'
      intro x m hx
      funext k
      have := (C.C K s LL h).tie.levB_φ T hT i ζ (by rw [hp]; exact hprim) x m hx k
      rw [hp] at this
      exact this
  intro i ζ hζ
  exact main (s - 1) i ζ hζ hζ

end GlobalTheory.NL.LatLow
end
end

