module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinJumpsSubsetOfSplitMono
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0171
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.WindowArith

theorem sg_ineq (l n : ℕ) [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    h i + sg l h i + 1 ≤ l * (sg l h (i - 1) + 1) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hshift : ∀ j : ℕ, (h (i - 1 + ((j + 1 + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1 + 1)
      = (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) / l := by
    intro j
    have e : i - 1 + ((j + 1 + 1 : ℕ) : ZMod n) = i + ((j + 1 : ℕ) : ZMod n) := by
      push_cast; ring
    rw [e, pow_succ, div_div]
  have e0 : i - 1 + ((0 + 1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hrec : (l : ℝ) * (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
      = h i + ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
    rw [(summable_sg hl h (i - 1)).tsum_eq_zero_add, e0]
    simp only [hshift, tsum_div_const]
    field_simp
    ring
  have hS0 : 0 ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  have h1 := Nat.floor_le hS0
  have h2 := Nat.lt_floor_add_one
    (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
  have h3 := mul_lt_mul_of_pos_left h2 hl0
  have key : (h i : ℝ) + (⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ)
      < (l : ℝ) * ((⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ) + 1) := by
    linarith
  have key' : h i + ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊
      < l * (⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ + 1) := by
    exact_mod_cast key
  simp only [sg]
  omega

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ u - y := ((CharP.intCast_eq_intCast k l).mp h).symm.dvd
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by linarith, h1⟩)
  linarith

private theorem cast_ne_of_mem_cloud_of_typeG {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hG : Dt.ty i = LType.G) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ y) (hy2 : y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) :
    (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu y hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hG]
  exact hm

private theorem natCast_ne_of_mem_cloud_of_bd_of_mem_range {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hB : Dt.ty i = LType.Bd) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ (Dt.h i : ℤ) - y)
    (hy2 : (Dt.h i : ℤ) - y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) : (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu ((Dt.h i : ℤ) - y) hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hB]
  exact Int.ModEq.sub (Int.ModEq.refl _) hm

theorem windows : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  intro k _ l n r _ _ _ Dt hT1 hT2 hT3 i
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hT1i := hT1 i
  have ht := Dt.one_le_letterBlockLength
  have hwB : Dt.w i ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩))
  have heB : Dt.w i + Dt.t - 1 ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩))
  have factsG : Dt.ty i = LType.G → (∀ u ∈ Dt.lows i, 1 ≤ u ∧ u ≤ (Dt.η i : ℤ)) ∧
      1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i := fun hG =>
    ⟨fun u hu => Dt.lowG i hG u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowG i hG _ hwB).1,
      (Dt.lowG i hG _ heB).2⟩
  have factsBd : Dt.ty i = LType.Bd → (∀ u ∈ Dt.lows i, (Dt.h i : ℤ) - Dt.η i ≤ u ∧ u ≤ (Dt.h i : ℤ) - 1) ∧
      (Dt.h i : ℤ) - Dt.η i ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ (Dt.h i : ℤ) - 1 := fun hB =>
    ⟨fun u hu => Dt.lowBd i hB u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowBd i hB _ hwB).1,
      (Dt.lowBd i hB _ heB).2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsg := sg_ineq l n hl2 Dt.h i
    have e1 : Dt.sg l i = sg l Dt.h i := rfl
    have e2 : Dt.sg l (i - 1) = sg l Dt.h (i - 1) := rfl
    rw [e1, e2]
    zify at hsg
    linarith
  · intro u hu y hy1 hy2 he
    rcases Multiset.mem_add.1 hu with hu | hu
    · have huy : u = y := by
        cases hty : Dt.ty i
        · obtain ⟨hL, hw1, hw2⟩ := factsG hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
        · obtain ⟨hL, hw1, hw2⟩ := factsBd hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
      have key : ∃ β ∈ Dt.B i, |u - β| ≤ (Dt.sg l i : ℤ) + 2 := by
        by_cases hyw : y < Dt.w i
        · exact ⟨Dt.w i, mem_block.2 ⟨le_rfl, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        by_cases hye : Dt.w i + Dt.t - 1 < y
        · exact ⟨Dt.w i + Dt.t - 1, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        · exact ⟨y, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
      obtain ⟨β, hβ, hb⟩ := key
      have := hT2 i u hu β hβ
      linarith
    · cases hty : Dt.ty i
      · obtain ⟨-, hw1, hw2⟩ := factsG hty
        exact cast_ne_of_mem_cloud_of_typeG hT3 hty hu y (by omega) (by omega) he
      · obtain ⟨-, hw1, hw2⟩ := factsBd hty
        exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hty hu y (by omega) (by omega) he
  · intro hG
    obtain ⟨hL, hw1, hw2⟩ := factsG hG
    refine ⟨?_, ?_, hw1, hw2⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
  · intro hB
    obtain ⟨hL, hw1, hw2⟩ := factsBd hB
    have ew : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    refine ⟨?_, ?_, by rw [ew]; omega, by rw [ew]; omega⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he

end GlobalTheory.WindowArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatedTraceSystemLocallyCauchy
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

theorem polyApprox_trc_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  intro l _ Γ _ _ _ _ a J x θ C hC hA ε hε g
  obtain ⟨s, c, hs, hP⟩ := hA (ε / 2) (by linarith)
  have hmem : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! R hRC hRη using hmem
  set F : Γ → PadicAlgCl l := fun h => ∑ η ∈ s, c η * trc (R η) h with hF
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun η hη => continuous_const.mul ?_
    exact (Units.continuous_val.comp (hC _ (hRC η hη))).matrix_trace
  refine ⟨F ⁻¹' Metric.ball (F g) (ε / 4), hFc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith)), ?_⟩
  intro i j hi hj
  have key := hP (MvPolynomial.X i - MvPolynomial.X j)
  simp only [map_sub, MvPolynomial.aeval_X] at key
  have hsum : ∑ η ∈ s, c η * (η i - η j) = F (x i) - F (x j) := by
    rw [hF]; simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun η hη => ?_
    have hi2 : η i = trc (R η) (x i) := (congrFun (hRη η hη) i).symm
    have hj2 : η j = trc (R η) (x j) := (congrFun (hRη η hη) j).symm
    rw [hi2, hj2]; ring
  rw [hsum] at key
  have hi' : ‖F (x i) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hi
  have hj' : ‖F (x j) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hj
  have hd : ‖F (x i) - F (x j)‖ ≤ ε / 2 := by
    have e : F (x i) - F (x j) = (F (x i) - F g) - (F (x j) - F g) := by ring
    rw [e]; linarith [norm_sub_le (F (x i) - F g) (F (x j) - F g)]
  have e2 : θ i - θ j = (θ i - θ j - (F (x i) - F (x j))) + (F (x i) - F (x j)) := by ring
  rw [e2]; linarith [norm_add_le (θ i - θ j - (F (x i) - F (x j))) (F (x i) - F (x j))]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExactTripleJumpsCharactersLift
section
noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.ExactTripleBK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem smul_eq_of_retr {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) {n : ℕ}
    {τ : ZMod a} {Λ : Matrix ι κ K⟦X⟧} (h : Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧))
    (v : Vec K a ι) : (l : K) ^ n • v τ = Λ *ᵥ F.app v τ := by
  rw [Hom.app_apply, Matrix.mulVec_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem onPol_injective {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : GlobalTheory.BK.Hom P Q) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) :
    Function.Injective F.onPol := by
  refine (injective_iff_map_eq_zero F.onPol).2 fun w hw => ?_
  obtain ⟨v, rfl⟩ := P.Man.mkQ_surjective w
  have hv : F.app v ∈ Q.Man := Q.cls_eq_zero_iff.1 hw
  change P.cls v = 0
  rw [PhiMod.cls_eq_zero_iff]
  have h1 : (l : K) ^ n • v ∈ P.Man := by
    refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
    obtain ⟨Λ, hΛA, hΛF⟩ := hΛ τ
    have hFv := mem_tot.1 (Q.mem_Man.1 hv) τ
    have h2 : ((l : K) ^ n • v) τ = Λ *ᵥ F.app v τ := by
      rw [Pi.smul_apply]
      exact smul_eq_of_retr F hΛF v
    rw [h2]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (A_le_Rpi l e (hΛA i k)) (hFv k)
  have h3 := P.Man.smul_mem ((l : K) ^ n)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (l_ne_zero l)), one_smul] at h3


omit [CompleteSpace K] in
theorem onD_actD {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (g : TameGal K l e a) (d : P.D) :
    F.onD (Δ₁.actD g d) = Δ₂.actD g (F.onD d) := by
  have h1 : Δ₁.actD g d = red (Δ₁.act g (cst d)) := rfl
  rw [h1, ← Hom.red_app, F.app_act, Δ₂.red_act, Hom.red_app, red_cst]

theorem map_constantCoeff_smul_one (c : K) :
    (c • (1 : Matrix ι ι K⟦X⟧)).map constantCoeff = c • (1 : Matrix ι ι K) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_smul]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem chars_subset {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    (F : BKHom D₀ D₁) (n : ℕ)
    (hΛ : ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧
      Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧)) (τ : ZMod a) :
    D₀.desc.chars τ ⊆ D₁.desc.chars τ := by
  rintro c ⟨d, hd, hc⟩
  refine ⟨F.onD d, fun h0 => hd ?_, fun ζ => ?_⟩
  · obtain ⟨Λ, -, hΛF⟩ := hΛ τ
    have h1 : Λ.map constantCoeff *ᵥ F.onD d τ = (l : K) ^ n • d τ := by
      rw [show F.onD d τ = (F.mat τ).map constantCoeff *ᵥ d τ from rfl, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, hΛF, map_constantCoeff_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ (l_ne_zero l))
  · rw [← onD_actD]
    change (F.mat τ).map constantCoeff *ᵥ _ = _ • ((F.mat τ).map constantCoeff *ᵥ d τ)
    rw [hc ζ, Matrix.mulVec_smul]

theorem exists_Z_of_onPol_eq_zero {μ : Type} [Fintype μ] [DecidableEq μ] {η H : ℕ}
    {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H} {D₂ : BKDat O K l e a μ η H}
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    (hinj : Function.Injective F.onPol) (n : ℕ)
    (hn : ∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) {w : D₁.Pol} (hw : w ∈ D₁.Z)
    (hG : G.onPol w = 0) : ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w := by
  obtain ⟨⟨y, hy, rfl⟩, hinv⟩ := D₁.desc.mem_Z.1 hw
  have hGy : G.app y ∈ D₂.M :=
    D₂.mem_M_of_mem_Man (G.app_mem_EM hy) (D₂.cls_eq_zero_iff.1 hG)
  obtain ⟨x, hx, hxy⟩ := hn _ hGy
  have hGz : G.app ((l : K) ^ n • y - x) = 0 := by
    rw [map_sub, LinearMap.map_smul_of_tower, hxy, sub_self]
  have hlM : ∀ {m : Vec K a κ}, m ∈ D₁.M → (l : K) ^ n • m ∈ D₁.M := fun hm => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hm _
  have hEz : E K l e ^ η • ((l : K) ^ n • y - x) ∈ D₁.M := by
    rw [smul_sub, smul_comm]
    refine sub_mem (hlM hy) ?_
    exact D₁.M.smul_mem (⟨E K l e ^ η, pow_mem (E_mem l e _) η⟩ : A O K) hx
  have hker : G.app (E K l e ^ η • ((l : K) ^ n • y - x)) = 0 := by rw [map_smul, hGz, smul_zero]
  obtain ⟨m₀, hm₀, hFm⟩ := Submodule.mem_map.1 ((hex.exact _ hEz).1 hker)
  have hFm' : F.app m₀ = E K l e ^ η • ((l : K) ^ n • y - x) := hFm
  have hFy : F.app (Ezpow K l e (-η) • m₀) = (l : K) ^ n • y - x := by
    rw [map_smul, hFm', smul_smul, mul_comm, E_pow_mul_Ezpow_neg, one_smul]
  have hy₀M : Ezpow K l e (-η) • m₀ ∈ D₀.EM η := by
    show E K l e ^ η • (Ezpow K l e (-η) • m₀) ∈ D₀.M
    rw [smul_smul, E_pow_mul_Ezpow_neg, one_smul]
    exact hm₀
  have hF : F.onPol (D₀.cls (Ezpow K l e (-η) • m₀)) = (l : K) ^ n • D₁.cls y := by
    rw [BK.Hom.onPol_cls, hFy, map_sub, map_smul, D₁.cls_eq_zero_iff.2 (D₁.M_le_Man hx), sub_zero]
  refine ⟨D₀.cls (Ezpow K l e (-η) • m₀), D₀.desc.mem_Z.2 ⟨⟨_, hy₀M, rfl⟩, fun g => hinj ?_⟩, hF⟩
  rw [F.onPol_act, hF, map_smul, hinv g]

end GlobalTheory.ExactTripleBK


open GlobalTheory.ExactTripleBK in
theorem GlobalTheory.exactTriple_jumps_chars_lift : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (D₂ : BKDat O K l e a μ η H) (F : BKHom D₀ D₁) (G : BKHom D₁ D₂), IsExactTriple F.toHom G.toHom → D₀.jumps ⊆ D₁.jumps ∧ (∀ τ, D₀.desc.chars τ ⊆ D₁.desc.chars τ) ∧ Function.Injective F.onPol ∧ (∀ n : ℕ, (∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) → ∀ w ∈ D₁.Z, G.onPol w = 0 → ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ μ _ _ _ _ η H D₀ D₁ D₂ F G hex
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker O K l e a κ μ D₁.toPhiMod D₂.toPhiMod G.toHom hex.finiteLength
  have hΛ := _root_.GlobalTheory.BK.exists_integral_leftInverse_of_exactTriple O K l e a ι κ μ D₀.toPhiMod D₁.toPhiMod D₂.toPhiMod F.toHom G.toHom hex n hn
  have hinj := onPol_injective F.toHom n hΛ
  exact ⟨_root_.GlobalTheory.BK.jumps_subset_of_split_mono O K l e a ι κ η H D₀ D₁ F.toHom n hΛ, fun τ => chars_subset F n hΛ τ, hinj,
    fun m hm w hw hG => exists_Z_of_onPol_eq_zero F G hex hinj m hm hw hG⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputation
section
open PowerSeries GlobalTheory.BK Matrix

noncomputable section

namespace GlobalTheory.IntegralityComp

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem S_eq_A_add_Fil {j : ℕ} (hj : j < l) {f : K⟦X⟧} (hf : f ∈ S O K e) :
    ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := _root_.GlobalTheory.BK.SDec.S_eq_A_add_Fil O K l e j hj f hf

theorem Fil_le_E_pow (j : ℕ) {φ : S O K e} (hφ : φ ∈ Fil O K l e j) :
    ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc O K l e j φ hφ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def colVec (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : Vec K a ι := Pi.single τ ((P.mx τ).col i)

theorem colVec_mem_MM (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : colVec P τ i ∈ P.MM := by
  refine mem_tot.2 fun σ => ?_
  by_cases h : σ = τ
  · subst h
    simp only [colVec, Pi.single_eq_same]
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp only [colVec, Pi.single_eq_of_ne h]
    exact zero_mem _

theorem sum_colVec (P : PhiMod O K l e a ι) (c : ZMod a → ι → K⟦X⟧) :
    (∑ τ, ∑ i, c τ i • colVec P τ i) = fun τ => P.mx τ *ᵥ c τ := by
  ext τ k
  simp only [Finset.sum_apply, Pi.smul_apply, colVec, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single τ]
  · simp [Matrix.mulVec, dotProduct, mul_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem MM_eq_L_add_FilMM (P : PhiMod O K l e a ι) {j : ℕ} (hj : j < l) {m : Vec K a ι}
    (hm : m ∈ P.MM) : ∃ p ∈ P.L, ∃ f ∈ P.FilMM j, m = p + f := by
  have hs (τ : ZMod a) (i : ι) : (P.mxInv τ *ᵥ m τ) i ∈ S O K e :=
    P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  choose g hg φ hφ hgφ using fun τ i => S_eq_A_add_Fil (O := O) (l := l) hj (hs τ i)
  have hm' (τ : ZMod a) : m τ = P.mx τ *ᵥ (P.mxInv τ *ᵥ m τ) := by
    rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]
  refine ⟨fun τ => P.mx τ *ᵥ g τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨g τ, fun i => hg τ i, rfl⟩,
    ∑ τ, ∑ i, φ τ i • colVec P τ i, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hφ τ i) (colVec_mem_MM P τ i)
  · have : (∑ τ, ∑ i, φ τ i • colVec P τ i) = ∑ τ, ∑ i, (φ τ i : K⟦X⟧) • colVec P τ i := rfl
    rw [this, sum_colVec]
    ext1 τ
    rw [Pi.add_apply, ← Matrix.mulVec_add, hm' τ]
    congr 1
    ext1 i
    exact hgφ τ i

section Dat

variable [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem Ezpow_smul_FilMM_mem (hηH : η < H) {f : Vec K a ι} (hf : f ∈ D.FilMM (10 * H)) :
    Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man := by
  refine Submodule.smul_induction_on hf (fun φ hφ m hm => ?_) (fun x y hx hy => ?_)
  · obtain ⟨q, hq, hφq⟩ := Fil_le_E_pow (O := O) (10 * H) hφ
    have hEm := D.smul_mem_Mext (A_le_S l e) hm
    have key : Ezpow K l e (-(2 * H : ℤ)) • φ • m =
        (E K l e ^ (8 * H - η) * q) • (E K l e ^ η • m) := by
      have h1 : Ezpow K l e (-(2 * H : ℤ)) * E K l e ^ (10 * H) = E K l e ^ (8 * H - η) * E K l e ^ η := by
        rw [← pow_add, show 8 * H - η + η = 8 * H by omega, ← Ezpow_natCast, ← Ezpow_natCast,
          ← Ezpow_add]
        congr 1
        push_cast
        ring
      rw [show φ • m = (φ : K⟦X⟧) • m from rfl, hφq, smul_smul, smul_smul, ← mul_assoc, h1]
      congr 1
      ring
    rw [key]
    exact D.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) _) hq)
      (D.Mext_mono (S_le_R l e) hEm)
  · rw [smul_add]
    exact add_mem hx hy

theorem E_pow_smul_EN_mem (hηH : η < H) (hl : 10 * H + 2 ≤ l) {y : Vec K a ι} (hy : y ∈ D.EM η) :
    ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), E K l e ^ (2 * H) • D.EN y = p + f := by
  have hl0 : E K l e ^ (H + η) • y ∈ D.L := by
    rw [pow_add, mul_smul]
    exact D.lower _ hy
  have hMM : E K l e ^ (H + η) • y ∈ D.MM := D.ext_mono (A_le_S l e) hl0
  have hc : D.conn (E K l e ^ (H + η) • y) ∈ D.MM := D.conn_mem_MM hMM
  have hA : E K l e ^ (H - η) * E K l e ∈ S O K e := mul_mem (pow_mem (E_mem l e _) _) (E_mem l e _)
  obtain ⟨p, hp, f, hf, hpf⟩ := MM_eq_L_add_FilMM D.toPhiMod (j := 10 * H) (by omega)
    (D.MM.smul_mem ⟨_, hA⟩ hc)
  have hB : E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e)) ∈ A O K :=
    mul_mem (pow_mem (E_mem l e _) _) (mul_mem (natCast_mem _ _) (by
      rw [N_E]; exact mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _)))
  refine ⟨p - (E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e))) • (E K l e ^ (H + η) • y),
    sub_mem hp (D.L.smul_mem ⟨_, hB⟩ hl0), f, hf, ?_⟩
  have h1 : E K l e ^ (2 * H) • D.EN y = E K l e ^ (H - η) • (E K l e ^ (H + η) • D.EN y) := by
    rw [smul_smul, ← pow_add, show H - η + (H + η) = 2 * H by omega]
  rw [h1, PhiMod.E_pow_smul_EN, PhiMod.EN_apply, smul_sub, smul_smul, smul_smul]
  have h2 : (E K l e ^ (H - η) * E K l e) • D.conn (E K l e ^ (H + η) • y) = p + f := hpf
  rw [h2]
  abel

end Dat

end GlobalTheory.IntegralityComp

theorem GlobalTheory.IntegralityComp.integralityComputation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralityComputation D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hηH hl
  exact ⟨fun m hm => GlobalTheory.IntegralityComp.MM_eq_L_add_FilMM D.toPhiMod (by omega) hm,
    fun f hf => GlobalTheory.IntegralityComp.Ezpow_smul_FilMM_mem D hηH hf,
    fun y hy => GlobalTheory.IntegralityComp.E_pow_smul_EN_mem D hηH hl hy⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.TrFormNd

theorem eq_zero_of_trace_mul_eq_zero : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  intro k Γ _ _ _ a r hr M hM hg
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ a r hr
  refine hnd M ((GlobalTheory.SSCont.mem_imAlg_iff r M).2 hM) fun y hy => ?_
  have hy' := (GlobalTheory.SSCont.mem_imAlg_iff r y).1 hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact hg g
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]

end GlobalTheory.TrFormNd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gauss_norm_extension_acris : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), (l : ℝ)⁻¹ ≤ r → r < 1 → ∃ N : Per.Acris l → ℝ, (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧ ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
  first | exact @GlobalTheory.GaussExt.exists_gauss_acris | exact GlobalTheory.GaussExt.exists_gauss_acris | (intros; apply GlobalTheory.GaussExt.exists_gauss_acris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicitStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicProjector_mem_isotypicPart_explicit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c := by
  first | exact @GlobalTheory.CokerL.isoProj_mem_isotypic' | exact GlobalTheory.CokerL.isoProj_mem_isotypic' | (intros; apply GlobalTheory.CokerL.isoProj_mem_isotypic' <;> assumption)
end

