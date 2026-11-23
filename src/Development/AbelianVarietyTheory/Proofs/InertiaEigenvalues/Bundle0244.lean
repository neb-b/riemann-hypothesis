module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelSenWeightCount
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.ModelCount

theorem telescope (S S₀ m : ℤ → ℕ) (h : ∀ y, S y + m (y + 1) = S₀ y + m y) (a : ℤ) (L : ℕ) :
    ∑ j ∈ Finset.range L, S (a + j) + m (a + L) = ∑ j ∈ Finset.range L, S₀ (a + j) + m a := by
  induction L with
  | zero => simp
  | succ L ih =>
    have step := h (a + L)
    have e : a + ((L + 1 : ℕ) : ℤ) = a + L + 1 := by push_cast; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, e]
    omega

theorem eq_of_cast_eq {k : Type} [Field k] (l : ℕ) [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ y - u := ((CharP.intCast_eq_intCast k l).mp h).dvd
  have hz : y - u = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

theorem sum_resCount {k : Type} [Field k] (U : Multiset ℤ) (w a : ℤ) (L : ℕ) (p : ℤ → Prop) [DecidablePred p]
    (h : ∀ u ∈ U, (p u → a ≤ u ∧ u < a + L) ∧
      ∀ y : ℤ, a ≤ y → y < a + L → (u : k) = (y : k) → u = y ∧ p u) :
    ∑ j ∈ Finset.range L, resCount U w ((a + j - w : ℤ) : k) = Multiset.card (U.filter p) := by
  classical
  induction U using Multiset.induction_on with
  | empty => simp [resCount]
  | cons u U ih =>
    have hU := ih (fun v hv => h v (Multiset.mem_cons_of_mem hv))
    have hu := h u (Multiset.mem_cons_self u U)
    have split : ∀ x : k, resCount (u ::ₘ U) w x =
        (if ((u - w : ℤ) : k) = x then 1 else 0) + resCount U w x := by
      intro x
      unfold resCount
      rw [Multiset.filter_cons, Multiset.card_add]
      split_ifs <;> simp
    simp only [split]
    rw [Finset.sum_add_distrib, hU, Multiset.filter_cons, Multiset.card_add]
    congr 1
    have tr : ∀ j : ℕ, (((u - w : ℤ) : k) = ((a + j - w : ℤ) : k)) ↔ ((u : k) = ((a + j : ℤ) : k)) := by
      intro j
      push_cast
      exact sub_left_inj
    by_cases hp : p u
    · rw [if_pos hp, Multiset.card_singleton]
      obtain ⟨ha, hb⟩ := hu.1 hp
      rw [Finset.sum_eq_single (u - a).toNat]
      · rw [if_pos]
        rw [tr]
        congr 1
        omega
      · intro j _ hj
        rw [if_neg]
        intro hc
        have := (hu.2 (a + j) (by omega) (by have := Finset.mem_range.mp ‹j ∈ Finset.range L›; omega) ((tr j).mp hc)).1
        omega
      · intro hn
        exfalso
        exact hn (Finset.mem_range.mpr (by omega))
    · rw [if_neg hp, Multiset.card_zero]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro hc
      have hj' := Finset.mem_range.mp hj
      exact hp (hu.2 (a + j) (by omega) (by omega) ((tr j).mp hc)).2

theorem exists_of_resCount_ne {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k} (h : resCount U w x ≠ 0) :
    ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero h)
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

theorem count : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ N : Lats k n M.T.m, M.Model M.T N → (∀ i, M.Nstd i ≤ N i) → ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen ((F.D M.T).γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) = r) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 N hN hle i
  have hNabc := (_root_.GlobalTheory.Models.model_obj_and_abc F M M.T N hN).2
  have hSabc := (_root_.GlobalTheory.Models.model_obj_and_abc F M M.T M.Nstd M.std_model).2
  have hs : Dt.sg l i = GlobalTheory.PhiGam.sg l Dt.h i := rfl
  have hsh := _root_.GlobalTheory.PhiGam.CloseTw.main (F.D M.T) Dt.h Dt.w N M.Nstd hNabc.1 hSabc.1 hNabc.2.1 hSabc.2.1 i
  rw [← hs] at hsh
  have hP : N i ≤ sh (-(Dt.sg l i : ℤ)) (M.Nstd i) := by
    have h' := sh_le_sh (-(Dt.sg l i : ℤ)) hsh
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  have tel := fun y : ℤ => _root_.GlobalTheory.PhiGam.Count.sen_count R ((F.D M.T).γ i) ((F.D M.T).γ_semi i) (N i) (M.Nstd i)
    (hNabc.1 i) (hSabc.1 i) (hle i) (hNabc.2.2 i) (hSabc.2.2 i) (Dt.sg l i) hP (y : k)
  have rel : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((y + 1 : ℤ) : k) =
      sen ((F.D M.T).γ i) (M.Nstd i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) := by
    intro y
    rw [Int.cast_add, Int.cast_one]
    exact (tel y).1
  have mz : ∀ y : ℤ, qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) ≠ 0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ Dt.sg l i ∧ ∃ u ∈ Dt.U i, (u : k) = ((y - j + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨j, hj1, hj2, hj⟩ := (tel y).2 hy
    rw [M.std_sen] at hj
    obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne hj
    refine ⟨j, hj1, hj2, u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  have sz : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) ≠ 0 → ∃ u ∈ Dt.U i, (u : k) = ((y + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨u, hu, hux⟩ := _root_.GlobalTheory.Models.ModTh.sen_model_subquot_mem_U F M h1 h2 h3 M.T M.T LinearMap.id LinearMap.id N (fun _ _ => rfl)
      (fun _ _ hab => hab) (fun _ _ => rfl) (fun b => ⟨b, rfl⟩) hN i (y : k) hy
    refine ⟨u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  obtain ⟨-, hwin, hG, hB⟩ := _root_.GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
  have hT1 := h1 i
  have ht := Dt.one_le_letterBlockLength
  have e1 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((0 : ℤ) : k) = 0 := by
    by_contra hne
    obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz 0 hne
    exact hwin u hu _ (by omega) (by omega) hux
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_contra hne
    obtain ⟨u, hu, hux⟩ := sz a (by simpa using hne)
    exact hwin u hu _ (by omega) (by omega) hux
  · intro hG'
    obtain ⟨hGU, hGc, hw1, hwt⟩ := hG hG'
    have hL : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel (-Dt.w i) (Dt.w i).toNat
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i + ((Dt.w i).toNat : ℤ) : ℤ) : k) = 0 := by
      rw [hL, neg_add_cancel]
      exact e1
    have e2 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz (-Dt.w i) hne
      exact hGU u hu _ (by omega) (by omega) hux
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) 0 (Dt.w i).toNat (· < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by omega⟩, fun y hy0 hyL hc => ?_⟩
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowG i hG' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · exact absurd hc (hGc u hcl y hy0 (by omega)))
    have e3 : ∀ j : ℕ, ((0 : ℤ) + (j : ℤ) - Dt.w i) = -Dt.w i + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (M.Nstd i) ((-Dt.w i + j : ℤ) : k) = Dt.d i := by
      change _ = Multiset.card ((Dt.U i).filter (· < Dt.w i))
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [e0, e2, hsum'] at tl
    omega
  · intro hB'
    obtain ⟨hBU, hBc, htw, hwη⟩ := hB hB'
    have hwst : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    have hL : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel 0 ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i)
        (((0 : ℤ) + (((Dt.wst i).toNat + 1 + (Dt.sg l i + 1) : ℕ) : ℤ) : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [e0, e1, Finset.sum_range_add] at tl
    have hz : ∑ j ∈ Finset.range (Dt.sg l i + 1),
        sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + (((Dt.wst i).toNat + 1 + j : ℕ) : ℤ) : ℤ) : k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_contra hne
      obtain ⟨u, hu, hux⟩ := sz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [hz] at tl
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) (Dt.w i) ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
      (fun u => ¬ u < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by push_cast; omega⟩, fun y hy0 hyL hc => ?_⟩
      push_cast at hyL
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowBd i hB' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · by_cases hyh : y ≤ (Dt.h i : ℤ)
        · exact absurd hc (hBc u hcl y (by omega) hyh)
        · exact absurd hc (hBU u (Multiset.mem_add.mpr (Or.inr hcl)) y (by omega) (by omega)))
    have e3 : ∀ j : ℕ, (Dt.w i + (j : ℤ) - Dt.w i) = 0 + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1)),
        sen ((F.D M.T).γ i) (M.Nstd i) (((0 : ℤ) + j : ℤ) : k) = Multiset.card ((Dt.U i).filter (fun u => ¬ u < Dt.w i)) := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [hsum'] at tl
    have hfirst : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + j : ℤ) : k) =
        ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp
    have hsplit := congrArg Multiset.card (Multiset.filter_add_not (· < Dt.w i) (Dt.U i))
    rw [Multiset.card_add] at hsplit
    have hU : Multiset.card (Dt.U i) = r := Dt.card_eq i
    have hd : Dt.d i = Multiset.card ((Dt.U i).filter (· < Dt.w i)) := rfl
    rw [hfirst] at tl
    omega

end GlobalTheory.ModelCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeExceedsConstant
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem typePrime_real_bound {C F N k b : ℝ} (hF0 : 0 ≤ F) (hN0 : 0 ≤ N)
    (hC : C ≤ b) (hF : F ≤ 5 * b) (hN : N ≤ 3 * (k * b)) (hk : 5 ≤ k) (hb : 1 ≤ b) :
    C * (F * N ^ 2 + N ^ 3) < (k * b) ^ 8 := by
  set y := k * b with hy
  have hby : 5 * b ≤ y := by rw [hy]; nlinarith
  have hy5 : 5 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : F * N ^ 2 + N ^ 3 ≤ y * (3 * y) ^ 2 + (3 * y) ^ 3 := by
    have hFy : F ≤ y := by linarith
    gcongr
  have h0 : 0 ≤ F * N ^ 2 + N ^ 3 := by positivity
  have h2 : C * (F * N ^ 2 + N ^ 3) ≤ y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) :=
    mul_le_mul (by linarith) h1 h0 hy0.le
  have h3 : y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) = 36 * y ^ 4 := by ring
  have h4 : (5 : ℝ) ^ 4 ≤ y ^ 4 := by gcongr
  have h5 : 0 < y ^ 4 := by positivity
  have h6 : y ^ 8 = y ^ 4 * y ^ 4 := by ring
  rw [h6]
  nlinarith

theorem typePrime_exceeds_constant :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → L.etaSz + D.R.t + L.Sc ≤ L.sc.b → 1 ≤ L.sc.b → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (⌊L.etaSz⌋₊ + D.R.t + 1 < ⌊3 * L.sc.b⌋₊ + 2) ∧ ((⌊L.etaSz⌋₊ : ℝ) ≤ 2 * L.etaSz) ∧ ∀ k : Fin 2, CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k := by
  intro D L P hsum hb CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hfl : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le heta.le
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨?_, by linarith, fun i => ?_⟩
  · have : ⌊L.etaSz⌋₊ + D.R.t ≤ ⌊3 * L.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hgi := (hg i).1
    have hm := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
    have hnV : D.R.nV + 1 ≤ 2 * D.R.k + D.R.t := by
      unfold Ranks.nV Ranks.r
      omega
    have hnVR : (D.R.nV : ℝ) + 1 ≤ 2 * D.R.k + D.R.t := by exact_mod_cast hnV
    have hfl3 : (⌊3 * L.sc.b⌋₊ : ℝ) ≤ 3 * L.sc.b := Nat.floor_le (by linarith)
    have hN : (D.R.nV : ℝ) + 1 ≤ 3 * ((D.R.k : ℝ) * L.sc.b) := by nlinarith
    have key := typePrime_real_bound (C := (CT : ℝ)) (F := (⌊3 * L.sc.b⌋₊ : ℝ) + 2)
      (N := (D.R.nV : ℝ) + 1) (by positivity) (by positivity) hCT (by linarith) hN hk5 hb
    have : ((CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) : ℕ) : ℝ) <
        (D.host.g i : ℝ) := by
      push_cast
      simp only [add_zero]
      linarith
    exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XXPowMemOfQQPowMulMemMapPhi
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.FrobIdeal

theorem exists_coords_mem {R ι : Type} [CommRing R] [Fintype ι] (f : R →+* R) (e : ι → R)
    (hspan : ∀ y : R, ∃ z : ι → R, y = ∑ j, e j * f (z j)) (𝔟 : Ideal R) {x : R} (hx : x ∈ 𝔟.map f) :
    ∃ w : ι → R, (∀ j, w j ∈ 𝔟) ∧ x = ∑ j, e j * f (w j) := by
  have key : ∀ a : R, ∃ w : ι → R, (∀ j, w j ∈ 𝔟) ∧ a * x = ∑ j, e j * f (w j) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      intro a
      obtain ⟨z, rfl⟩ := hspan a
      refine ⟨fun j => z j * t, fun j => 𝔟.mul_mem_left _ ht, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc]
    | zero => exact fun a => ⟨0, fun _ => 𝔟.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      intro a
      obtain ⟨u, hu, h1⟩ := hx a
      obtain ⟨v, hv, h2⟩ := hy a
      refine ⟨u + v, fun j => 𝔟.add_mem (hu j) (hv j), ?_⟩
      rw [mul_add, h1, h2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, map_add (f := _), mul_add]
    | smul c x _ hx =>
      intro a
      obtain ⟨u, hu, h1⟩ := hx (a * c)
      exact ⟨u, hu, by rw [← h1, smul_eq_mul, mul_assoc]⟩
  simpa using key 1

theorem colon_le_map {R ι : Type} [CommRing R] [Fintype ι] (f : R →+* R) (e : ι → R)
    (hfree : ∀ y : R, ∃! z : ι → R, y = ∑ j, e j * f (z j)) (𝔞 𝔟 : Ideal R) (x q : R)
    (hx : f x = x * q) (hq : ∀ g ∈ 𝔞, q * g ∈ 𝔟.map f) {y : R} (hy : x * y ∈ 𝔞) :
    ∃ z : ι → R, (∀ j, x * z j ∈ 𝔟) ∧ y = ∑ j, e j * f (z j) := by
  obtain ⟨z, hz, -⟩ := hfree y
  refine ⟨z, ?_, hz⟩
  obtain ⟨w, hw, h⟩ := exists_coords_mem f e (fun y => (hfree y).exists) 𝔟 (hq _ hy)
  have h2 : q * (x * y) = ∑ j, e j * f (x * z j) := by
    conv_lhs => rw [hz]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hx]; ring
  have h3 : (fun j => x * z j) = w := (hfree _).unique h2 h
  intro j
  have : x * z j = w j := congrFun h3 j
  rw [this]; exact hw j

theorem phi_mem_span (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ϖ : O)
    (hϖ : ϖ ∣ (l : O)) (N : ℕ) (hN : 1 ≤ N) {y : PowerSeries O}
    (hy : y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ N}) :
    phi l O y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ (N + 1)} := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hy
  obtain ⟨r, hr⟩ := Series.phi_X_mod l O
  obtain ⟨t, ht⟩ := hϖ
  have hC : phi l O (PowerSeries.C ϖ) = PowerSeries.C ϖ := (phi l O).commutes ϖ
  have hl : (l : PowerSeries O) = PowerSeries.C ϖ * PowerSeries.C t := by
    rw [← map_mul, ← ht, map_natCast]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (phi l O PowerSeries.X) (PowerSeries.X ^ l) N
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨m, hm⟩ : ∃ m, l * N = m + (N + 1) := ⟨l * N - (N + 1), by
    have : 2 * N ≤ l * N := Nat.mul_le_mul_right N h2
    omega⟩
  rw [← pow_mul, hm, pow_add] at hd
  nth_rewrite 2 [hr] at hd
  rw [hl] at hd
  refine Ideal.mem_span_pair.2 ⟨phi l O a + phi l O b * PowerSeries.C t * r * d,
    phi l O b * PowerSeries.X ^ m, ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_pow, hC]
  linear_combination (-(phi l O b)) * hd

end GlobalTheory.Cyc.FrobIdeal

namespace GlobalTheory.Cyc

open FrobIdeal

theorem XX_pow_mem_of_QQ_pow_mul_mem_map_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (s n H c : ℕ) [NeZero n], 1 ≤ s → ∀ 𝔞 : ZMod n → Ideal (PowerSeries O), (∀ i, PowerSeries.X ^ c ∈ 𝔞 i) → (∀ i, ∀ g ∈ 𝔞 i, QQ l O s ^ H * g ∈ (𝔞 (i - 1)).map (phi l O)) → ∀ i, XX l O s ^ H ∈ 𝔞 i := by
  intro l _ O _ _ _ _ _ hl0 hlu s n H c _ _ 𝔞 hc hK i
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ∀ a : O, ¬ IsUnit a → ϖ ∣ a := fun a ha => by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact ha
  by_contra hi
  have main : ∀ (m : ℕ) (y : PowerSeries O), XX l O s ^ H * y ∈ 𝔞 (i + m) →
      y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ (m + 1)} := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [Nat.cast_zero, add_zero] at hy
      have hu : ¬ IsUnit y := fun hu => hi ((Ideal.mul_unit_mem_iff_mem _ hu).1 hy)
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu
      obtain ⟨t, ht⟩ := hdvd _ hu
      refine Ideal.mem_span_pair.2 ⟨PowerSeries.C t, PowerSeries.mk fun p => PowerSeries.coeff (p + 1) y, ?_⟩
      conv_rhs => rw [PowerSeries.eq_shift_mul_X_add_const y]
      rw [ht, map_mul]; ring
    | succ m ih =>
      intro y hy
      obtain ⟨z, hz, rfl⟩ := colon_le_map (phi l O : PowerSeries O →+* PowerSeries O)
        (fun j : Fin l => (1 + PowerSeries.X) ^ (j : ℕ)) (_root_.GlobalTheory.Cyc.phi_free l O hl0 hlu)
        (𝔞 (i + (m + 1 : ℕ))) (𝔞 (i + m)) (XX l O s ^ H) (QQ l O s ^ H)
        (by rw [map_pow, ← mul_pow]; exact congrArg (· ^ H) (Series.phi_XX l O s))
        (fun g hg => by
          have h := hK _ g hg
          rw [Nat.cast_succ, ← add_assoc, add_sub_cancel_right] at h
          exact h) hy
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _
        (phi_mem_span l O ϖ (hdvd _ hlu) (m + 1) (Nat.le_add_left 1 m) (ih _ (hz j)))
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (main c _ (Ideal.mul_mem_left _ _ (hc _)))
  have h := congrArg (PowerSeries.coeff c) hab
  rw [map_add (f := _), PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', if_neg (by omega),
    PowerSeries.coeff_X_pow, if_pos rfl, add_zero] at h
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one_right _ h)

end GlobalTheory.Cyc
end

