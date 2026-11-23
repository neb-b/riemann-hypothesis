module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
section
noncomputable section
namespace GlobalTheory.PhiGam.Window
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem bij_of_gmult_zero {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] (x : k) (h : gmult T P Q x = 0) :
    (∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q) ∧ ∀ y ∈ P, ∃ p ∈ P, y - (T p - x • p) ∈ Q := by
  have hinj : ∀ p ∈ P, T p - x • p ∈ Q → p ∈ Q := by
    intro p hp hq
    unfold gmult at h
    set P' := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hP'
    have hker : LinearMap.ker (Q.mkQ ∘ₗ P'.subtype) = Q.submoduleOf P' := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
    have hle : LinearMap.range (Q.mkQ ∘ₗ P'.subtype) ≤ P.map Q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact Submodule.map_mono inf_le_left
    haveI : FiniteDimensional k (LinearMap.range (Q.mkQ ∘ₗ P'.subtype)) :=
      Submodule.finiteDimensional_of_le hle
    haveI : FiniteDimensional k (↥P' ⧸ Q.submoduleOf P') := by
      rw [← hker]
      exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm
    have hsub : Subsingleton (↥P' ⧸ Q.submoduleOf P') := Module.finrank_zero_iff.mp h
    have hmem : p ∈ P' := by
      refine ⟨hp, ?_⟩
      refine Submodule.mem_iSup_of_mem 1 ?_
      simpa [Module.algebraMap_end_apply] using hq
    have : (Submodule.Quotient.mk (⟨p, hmem⟩ : P') : ↥P' ⧸ Q.submoduleOf P') = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero (Q.submoduleOf P')).mp this
  refine ⟨hinj, ?_⟩
  let S : U →ₗ[k] U := T - x • LinearMap.id
  have hS : ∀ p, S p = T p - x • p := fun p => rfl
  have hSQ : Q ≤ Q.comap S := fun p hp => by
    rw [Submodule.mem_comap, hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, P.sub_mem (hP p hp) (P.smul_mem _ hp), rfl⟩
  have hi : Function.Injective (Sq.restrict hSq) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, p, hp, rfl⟩ hz
    have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
    have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
  have hs := LinearMap.injective_iff_surjective.mp hi
  intro y hy
  obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
  have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
  exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩

variable {k : Type} [Field k]

theorem vv_coe : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by
  simp [vv]

theorem vv_ne_zero : vv k ≠ 0 := by
  simp [vv]

theorem gam_zpow {l : ℕ} (R : RingPG k l) (b : ℤ) :
    ∃ c : k⟦X⟧, R.γ (vv k ^ b) = vv k ^ b * (1 - (b : k⸨X⸩) * vv k + (c : k⸨X⸩) * vv k ^ 2) := by
  obtain ⟨κ, hκ, hγ⟩ := R.γ_v
  obtain ⟨c0, hc0⟩ : (PowerSeries.X : k⟦X⟧) ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ]
  have hκ' : κ = 1 + PowerSeries.X * c0 := by rw [← hc0]; ring
  have hu : IsUnit (1 - κ * PowerSeries.X : k⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  obtain ⟨w', hw'⟩ := hu.exists_right_inv
  let ι : k⟦X⟧ →+* k⸨X⸩ := HahnSeries.ofPowerSeries ℤ k
  have hι : ∀ c : k⟦X⟧, (c : k⸨X⸩) = ι c := fun _ => rfl
  have hv : vv k = ι PowerSeries.X := vv_coe
  set w : k⸨X⸩ := 1 - (κ : k⸨X⸩) * vv k with hw
  have hw1 : w = 1 - vv k - ι c0 * vv k ^ 2 := by
    rw [hw, hι, hκ', hv]; simp only [map_add (f := _), map_mul, map_one]; ring
  have hww : w * ι w' = 1 := by
    have := congrArg ι hw'
    simp only [map_mul, map_sub, map_one] at this
    rw [hw, hv, hι]; exact this
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  have hinv : w⁻¹ = ι w' := (eq_inv_of_mul_eq_one_right hww).symm
  have key : ∃ c : k⟦X⟧, w ^ b = 1 - (b : k⸨X⸩) * vv k + ι c * vv k ^ 2 := by
    induction b using Int.induction_on with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(n : k⟦X⟧) - c0 + (n : k⟦X⟧) * c0 * PowerSeries.X + c * (1 - PowerSeries.X - c0 * PowerSeries.X ^ 2), ?_⟩
      rw [zpow_add_one₀ hw0, hc, hw1]
      simp only [map_add (f := _), map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      ring
    | pred n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨w' * (c + ((n : k⟦X⟧) + 1) + c0 + ((n : k⟦X⟧) + 1) * c0 * PowerSeries.X), ?_⟩
      rw [zpow_sub_one₀ hw0, hc, hinv]
      simp only [map_add (f := _), map_sub, map_mul, map_one, map_pow, map_natCast, ← hv]
      push_cast
      rw [hw1] at hww
      linear_combination (1 + ((n : k⸨X⸩) + 1) * vv k) * hww
  obtain ⟨c, hc⟩ := key
  exact ⟨c, by rw [map_zpow₀, hγ, mul_zpow, hc]⟩

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem mem_sh_iff {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ ∃ n ∈ N, vv k ^ a • n = x := Iff.rfl

theorem coe_smul_eq (c : k⟦X⟧) (x : V) : (c : k⸨X⸩) • x = c • x :=
  algebraMap_smul k⸨X⸩ c x

theorem v_smul_mem {N : Submodule k⟦X⟧ V} {n : V} (hn : n ∈ N) : vv k • n ∈ N := by
  rw [vv_coe, coe_smul_eq]; exact N.smul_mem _ hn

theorem sh_succ_le (a : ℤ) (N : Submodule k⟦X⟧ V) : sh (a + 1) N ≤ sh a N := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_sh_iff.mpr ⟨vv k • n, v_smul_mem hn, ?_⟩
  show _ = vv k ^ (a + 1) • n
  rw [smul_smul, zpow_add_one₀ vv_ne_zero]

theorem sh_add_le (a : ℤ) (m : ℕ) (N : Submodule k⟦X⟧ V) : sh (a + m) N ≤ sh a N := by
  induction m with
  | zero => simp
  | succ m ih =>
    refine le_trans ?_ ih
    rw [Nat.cast_succ, ← add_assoc]; exact sh_succ_le _ _

theorem nab_eq (g : V →ₗ[k] V) (x : V) : nab g x = (vv k)⁻¹ • (g x - x) := rfl

theorem nab_mem {g : V →ₗ[k] V} {N : Submodule k⟦X⟧ V} (hC : CondC g N) {n : V} (hn : n ∈ N) :
    nab g n ∈ N := by
  obtain ⟨n', hn', h⟩ := mem_sh_iff.mp (hC n hn)
  rw [nab_eq, ← h, smul_smul, zpow_one, inv_mul_cancel₀ vv_ne_zero, one_smul]; exact hn'

theorem shift_identity {K W : Type} [Field K] [AddCommGroup W] [Module K W] {v : K} (hv : v ≠ 0)
    (u b c : K) (n t : W) :
    v⁻¹ • ((u * (1 - b * v + c * v ^ 2)) • (n + v • t) - u • n) =
      u • (t - b • n + v • (c • (n + v • t) - b • t)) := by
  match_scalars <;> field_simp <;> ring

theorem nab_shift {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {n : V} (hn : n ∈ N) :
    ∃ n' ∈ N, nab g (vv k ^ b • n) = vv k ^ b • (nab g n - (b : k) • n + vv k • n') := by
  obtain ⟨c, hc⟩ := gam_zpow R b
  have hv : vv k ≠ 0 := vv_ne_zero
  have hgn : g n = n + vv k • nab g n := by
    rw [nab_eq, smul_smul, mul_inv_cancel₀ hv, one_smul]; abel
  have hm := nab_mem hC hn
  refine ⟨c • (n + vv k • nab g n) - b • nab g n,
    N.sub_mem (N.smul_mem _ (N.add_mem hn (v_smul_mem hm))) (zsmul_mem hm _), ?_⟩
  rw [nab_eq g (vv k ^ b • n), hg, hc, hgn, Int.cast_smul_eq_zsmul, ← coe_smul_eq,
    ← Int.cast_smul_eq_zsmul k⸨X⸩ b n, ← Int.cast_smul_eq_zsmul k⸨X⸩ b (nab g n)]
  exact shift_identity hv _ _ _ _ _

theorem nab_mem_sh {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hC : CondC g N) (b : ℤ) {x : V} (hx : x ∈ sh b N) : nab g x ∈ sh b N := by
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
  obtain ⟨n', hn', h⟩ := nab_shift R hg hC b hn
  refine mem_sh_iff.mpr ⟨_, ?_, h.symm⟩
  exact N.add_mem (N.sub_mem (nab_mem hC hn) ((N.restrictScalars k).smul_mem _ hn)) (v_smul_mem hn')

theorem finite_quot {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    FiniteDimensional k ((N.restrictScalars k).map ((sh 1 N).restrictScalars k).mkQ) := by
  obtain ⟨s, hs⟩ := hN
  set Q := (sh 1 N).restrictScalars k with hQ
  have hle : (N.restrictScalars k).map Q.mkQ ≤ Submodule.span k (Q.mkQ '' (s : Set V)) := by
    rintro _ ⟨n, hn, rfl⟩
    have hn' : n ∈ Submodule.span k⟦X⟧ (s : Set V) := by rw [hs]; exact hn
    clear hn
    induction hn' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x hx ih =>
      have hxN : x ∈ N := by rw [← hs]; exact hx
      obtain ⟨c', hc'⟩ : (PowerSeries.X : k⟦X⟧) ∣ c - algebraMap k k⟦X⟧ (PowerSeries.constantCoeff c) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have : Q.mkQ (c • x) = PowerSeries.constantCoeff c • Q.mkQ x := by
        rw [← map_smul]
        refine (Submodule.Quotient.eq _).mpr ?_
        refine mem_sh_iff.mpr ⟨c' • x, N.smul_mem _ hxN, ?_⟩
        rw [zpow_one, vv_coe, coe_smul_eq, smul_smul, ← hc', sub_smul, algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ ih
  haveI : FiniteDimensional k (Submodule.span k (Q.mkQ '' (s : Set V))) :=
    FiniteDimensional.span_of_finite k (s.finite_toSet.image _)
  exact Submodule.finiteDimensional_of_le hle

theorem graded {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (h : sen g N (b : k) = 0) :
    (∀ x ∈ sh b N, nab g x ∈ sh (b + 1) N → x ∈ sh (b + 1) N) ∧
      ∀ y ∈ sh b N, ∃ x ∈ sh b N, y - nab g x ∈ sh (b + 1) N := by
  haveI := finite_quot hN
  obtain ⟨h1, h2⟩ := bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => nab_mem hC hp) (fun p hp => nab_mem_sh R hg hC 1 hp) (b : k) h
  have hv : vv k ≠ 0 := vv_ne_zero
  constructor
  · intro x hx hx'
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hx
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hn
    obtain ⟨t, ht, e'⟩ := mem_sh_iff.mp hx'
    rw [e, zpow_add_one₀ hv, mul_smul] at e'
    have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
    have : n ∈ sh 1 N := h1 n hn (mem_sh_iff.mpr ⟨t - n', N.sub_mem ht hn', by
      rw [zpow_one, smul_sub, e2]; abel⟩)
    obtain ⟨r, hr, rfl⟩ := mem_sh_iff.mp this
    exact mem_sh_iff.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := mem_sh_iff.mp hy
    obtain ⟨p, hp, hq⟩ := h2 n hn
    obtain ⟨r, hr, e'⟩ := mem_sh_iff.mp hq
    obtain ⟨n', hn', e⟩ := nab_shift R hg hC b hp
    refine ⟨vv k ^ b • p, mem_sh_iff.mpr ⟨p, hp, rfl⟩, mem_sh_iff.mpr ⟨r - n', N.sub_mem hr hn', ?_⟩⟩
    rw [zpow_one] at e'
    rw [e, zpow_add_one₀ hv, mul_smul, ← smul_sub, smul_sub (vv k), e']
    congr 1; abel

theorem nab_bijective_window : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ), (∀ j : ℕ, j < m → sen g N ((a + j : ℤ) : k) = 0) → (∀ x ∈ sh a N, nab g x ∈ sh (a + m) N → x ∈ sh (a + m) N) ∧ ∀ y ∈ sh a N, ∃ x ∈ sh a N, y - nab g x ∈ sh (a + m) N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m
  induction m with
  | zero =>
    intro _
    refine ⟨fun x hx _ => by simpa using hx, fun y hy => ⟨0, Submodule.zero_mem _, by simpa using hy⟩⟩
  | succ m ih =>
    intro h
    obtain ⟨i1, i2⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    obtain ⟨g1, g2⟩ := graded R hg hN.1 hC (a + m) (h m (Nat.lt_succ_self m))
    rw [Nat.cast_succ, ← add_assoc]
    refine ⟨fun x hx hx' => g1 x (i1 x hx (sh_succ_le _ _ hx')) hx', fun y hy => ?_⟩
    obtain ⟨x, hx, hx'⟩ := i2 y hy
    obtain ⟨z, hz, hz'⟩ := g2 _ hx'
    refine ⟨x + z, Submodule.add_mem _ hx (sh_add_le a m N hz), ?_⟩
    rw [map_add (f := _), ← sub_sub]; exact hz'

end GlobalTheory.PhiGam.Window
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyJacquetRallisHaarMeasuresForallSize
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.HaarExist

variable (r : ℕ)

theorem entryBall_compact_open (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ∧
      IsOpen {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have e : {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} =
      Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : K) 1 := by
    ext A
    exact ⟨fun h i _ j _ => mem_closedBall_zero_iff.2 (h i j),
      fun h i j => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))⟩
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero⟩

theorem norm_one_entry_le (K : Type) [NormedField K] (i j : Fin r) :
    ‖(1 : Matrix (Fin r) (Fin r) K) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem glO_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact (glO r K) ∧ IsOpen (glO r K) ∧ (glO r K).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r K
  have e : glO r K = Units.embedProduct _ ⁻¹' ({A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1})) := by
    ext g
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  refine ⟨?_, ?_, 1, fun i j => ⟨norm_one_entry_le r K i j, by rw [inv_one]; exact norm_one_entry_le r K i j⟩⟩
  · rw [e]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hc.prod (MulOpposite.opHomeomorph.symm.isClosedEmbedding.isCompact_preimage hc))
  · rw [e]
    exact (ho.prod (ho.preimage MulOpposite.continuous_unop)).preimage Units.continuous_embedProduct

theorem continuousStar_of_norm_star (E : Type) [NormedField E] [StarRing E] (h : ∀ y : E, ‖star y‖ = ‖y‖) :
    ContinuousStar E :=
  ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) h).continuous⟩

theorem uO_isCompact_isOpen (E : Type) [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [ContinuousStar E] :
    IsCompact (uO r E) ∧ IsOpen (uO r E) ∧ (uO r E).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r E
  have hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  exact ⟨hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc, ho.preimage continuous_subtype_val,
    1, fun i j => norm_one_entry_le r E i j⟩

def positiveCompactsOf {X : Type} [TopologicalSpace X] (s : Set X) (h : IsCompact s ∧ IsOpen s ∧ s.Nonempty) :
    TopologicalSpace.PositiveCompacts X :=
  ⟨⟨s, h.1⟩, by simpa [h.2.1.interior_eq] using h.2.2⟩

theorem unitBall_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] :
    IsCompact (Metric.closedBall (0 : K) 1) ∧ IsOpen (Metric.closedBall (0 : K) 1) ∧
      (Metric.closedBall (0 : K) 1).Nonempty := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact ⟨isCompact_closedBall _ _, IsUltrametricDist.isOpen_closedBall _ one_ne_zero, 0, by simp⟩

theorem meas_nonempty : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  intro F E _ _ _ _ h r
  haveI := h.ultraF; haveI := h.ultraE; haveI := h.lcF; haveI := h.lcE
  haveI := continuousStar_of_norm_star E h.norm_star
  letI : MeasurableSpace (GL (Fin r) F) := borel _
  haveI : BorelSpace (GL (Fin r) F) := ⟨rfl⟩
  letI : MeasurableSpace (Matrix.unitaryGroup (Fin r) E) := borel _
  haveI : BorelSpace (Matrix.unitaryGroup (Fin r) E) := ⟨rfl⟩
  letI : MeasurableSpace F := borel _
  haveI : BorelSpace F := ⟨rfl⟩
  letI : MeasurableSpace E := borel _
  haveI : BorelSpace E := ⟨rfl⟩
  exact ⟨{ μG := Measure.haarMeasure (positiveCompactsOf _ (glO_isCompact_isOpen r F))
           μU := Measure.haarMeasure (positiveCompactsOf _ (uO_isCompact_isOpen r E))
           μF := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen F))
           μE := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen E))
           haarG := inferInstance, haarU := inferInstance, haarF := inferInstance, haarE := inferInstance
           volG := Measure.haarMeasure_self, volU := Measure.haarMeasure_self
           volF := Measure.addHaarMeasure_self, volE := Measure.addHaarMeasure_self }⟩

end GlobalTheory.JR.HaarExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLeMaxUltra
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.LatL

theorem norm_sub_le_max_ultra' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem exists_glO_pair {F : Type} [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (v w : Fin (r + 1) → F) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) (hwv : w ⬝ᵥ v = 1) :
    ∃ k ∈ glO (r + 1) F, (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧
      w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => ‖w i‖)
  have hw0 : w i₀ ≠ 0 := by
    intro h
    have : w = 0 := funext fun i => norm_le_zero_iff.mp (by simpa [h] using hi₀ i)
    simp [this] at hwv
  have hratio : ∀ i, ‖w i / w i₀‖ ≤ 1 := fun i => by
    rw [norm_div]; exact div_le_one_of_le₀ (hi₀ i) (norm_nonneg _)
  let s : Fin r → Fin (r + 1) := i₀.succAbove
  have hs : ∀ c, s c ≠ i₀ := fun c => Fin.succAbove_ne i₀ c
  let u : Fin r → Fin (r + 1) → F := fun c =>
    Pi.single (s c) 1 - (w (s c) / w i₀) • Pi.single i₀ 1
  let ρ : Fin r → Fin (r + 1) → F := fun c => Pi.single (s c) 1 - v (s c) • w
  let col : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases v u
  let row : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases w ρ
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => col b a
  let L : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => row a b
  have hwu : ∀ c, w ⬝ᵥ u c = 0 := by
    intro c
    simp only [u, dotProduct_sub, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
    field_simp; ring
  have hdot : ∀ a b, row a ⬝ᵥ col b = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b := by
    intro a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [row, col, hwv]
      | cast c => simp [row, col, hwu, Matrix.one_apply, (Fin.castSucc_lt_last c).ne']
    | cast c =>
      induction b using Fin.lastCases with
      | last =>
        simp [row, col, ρ, sub_dotProduct, smul_dotProduct, single_dotProduct, hwv,
          Matrix.one_apply, (Fin.castSucc_lt_last c).ne]
      | cast c' =>
        simp only [row, col, Fin.lastCases_castSucc, ρ, sub_dotProduct, smul_dotProduct,
          single_dotProduct, hwu, smul_eq_mul, mul_zero, sub_zero, one_mul, u, Pi.sub_apply,
          Pi.smul_apply, Pi.single_apply, hs c, if_false, mul_zero, sub_zero, Matrix.one_apply,
          Fin.castSucc_inj]
        by_cases h : c = c'
        · subst h; simp
        · have : s c ≠ s c' := fun e => h (Fin.succAbove_right_injective e)
          simp [this, h]
  have hLK : L * K = 1 := by
    ext a b
    rw [← hdot a b]
    simp [L, K, Matrix.mul_apply, dotProduct]
  have hKL : K * L = 1 := mul_eq_one_comm.mp hLK
  let k : GL (Fin (r + 1)) F := ⟨K, L, hKL, hLK⟩
  have hsingle : ∀ i j : Fin (r + 1), ‖(Pi.single i (1 : F) : Fin (r + 1) → F) j‖ ≤ 1 := by
    intro i j; by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : ∀ b a, ‖col b a‖ ≤ 1 := by
    intro b a
    induction b using Fin.lastCases with
    | last => simpa [col] using hv a
    | cast c =>
      simp only [col, Fin.lastCases_castSucc, u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hratio _) (norm_nonneg _) (hsingle _ _)
  have hrow : ∀ a b, ‖row a b‖ ≤ 1 := by
    intro a b
    induction a using Fin.lastCases with
    | last => simpa [row] using hw b
    | cast c =>
      simp only [row, Fin.lastCases_castSucc, ρ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hv _) (norm_nonneg _) (hw _)
  refine ⟨k, fun i j => ⟨by simpa [k, K] using hcol j i, by simpa [k, L] using hrow i j⟩, ?_, ?_⟩
  · rw [Matrix.mulVec_single_one]
    funext a
    change col (Fin.last r) a = v a
    simp [col]
  · ext b
    rw [show (w ᵥ* (k : Matrix _ _ F)) b = row (Fin.last r) ⬝ᵥ col b by
      simp [k, K, row, Matrix.vecMul, dotProduct]]
    rw [hdot, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]

theorem glO_transitive_pairs : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v w : Fin (r + 1) → F), (∀ i, ‖v i‖ ≤ 1) →
    (∀ i, ‖w i‖ ≤ 1) → w ⬝ᵥ v = 1 → ∃ k ∈ glO (r + 1) F,
      (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧ w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  intro F E _ _ _ _ hU r v w hv hw hwv
  haveI : IsUltrametricDist F := hU.ultraF
  exact exists_glO_pair r v w hv hw hwv

end GlobalTheory.LatL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeSubOneNormLe
section
namespace GlobalTheory

theorem pow_prime_sub_one_norm_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  intro l _ n _ _ X k hX i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with ht
  have t0 : 0 ≤ t := by positivity
  have tl : t ≤ (l : ℝ)⁻¹ := by
    rw [ht, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have t1 : t ≤ 1 := tl.trans (inv_le_one_of_one_le₀ hl1.le)
  have hrhs : (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = t * (l : ℝ)⁻¹ := by
    rw [ht, show -(((k + 1 : ℕ) : ℤ) + 2) = -((k : ℤ) + 2) + (-1) by push_cast; ring,
      zpow_add₀ hl0, zpow_neg_one]
  rw [hrhs]
  set Y := X - 1 with hY
  have hXY : X = 1 + Y := by rw [hY]; abel
  have hR := _root_.GlobalTheory.matrix_one_add_pow_sub_entry_le ℚ_[l] n Y t t0 t1 hX l i j
  have hsplit : (X ^ l - 1) i j = ((1 + Y) ^ l - 1 - ((l : ℕ) : ℚ_[l]) • Y) i j + (((l : ℕ) : ℚ_[l]) • Y) i j := by
    rw [hXY]; simp
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · calc _ ≤ t ^ 2 := hR
      _ = t * t := sq t
      _ ≤ t * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_left tl t0
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p, mul_comm]
    exact mul_le_mul_of_nonneg_right (hX i j) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportMatrixIdentityInjectiveRingHomStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_matrix_identity_injective_ringHom : ∀ {R L : Type} [CommRing R] [CommRing L] (ι : R →+* L), Function.Injective ι → ∀ (d N q : ℕ) (p : Fin d → ℕ) (ξ s : R) (Qm Q₁ : Matrix (Fin d) (Fin d) L) (X B c V : Matrix (Fin d) (Fin d) R), ι s ^ N • Qm = (X * B).map ι → (∀ i j, ι ξ ^ q * Q₁ i j = ι (ξ ^ p j * V i j)) → Q₁ = Qm * c.map ι → ξ ^ q • (X * B * c) = s ^ N • (V * Matrix.diagonal (fun j => ξ ^ p j)) := by
  first | (exact @GlobalTheory.transport_matrix_identity_star_alg) | (exact GlobalTheory.transport_matrix_identity_star_alg) | (intros; apply GlobalTheory.transport_matrix_identity_star_alg  <;> assumption)
end

