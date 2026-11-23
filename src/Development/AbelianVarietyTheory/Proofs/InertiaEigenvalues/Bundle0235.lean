module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0221
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Matrix

noncomputable section

namespace GlobalTheory.TauFrame

theorem exists_sub_basis {C : Type} [Field C] {d r : ℕ} (f : Fin d → Fin r → C)
    (hf : Submodule.span C (Set.range f) = ⊤) :
    ∃ κ : Fin r → Fin d, LinearIndependent C (fun k => f (κ k)) := by
  obtain ⟨ι, a, ha, hsp, hli⟩ := exists_linearIndependent' C f
  haveI : Finite ι := Finite.of_injective a ha
  haveI := Fintype.ofFinite ι
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp, hf]))
  rw [Module.finrank_fin_fun] at hb
  let e : Fin r ≃ ι := (Fintype.equivFinOfCardEq hb.symm).symm
  exact ⟨a ∘ e, hli.comp e e.injective⟩

section Norm

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_sum_le {n : ℕ} (f : Fin n → C) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖f i‖ ≤ c) :
    ‖∑ i, f i‖ ≤ c :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun i _ => h i)

theorem norm_mul_le {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C) (B : Matrix (Fin b) (Fin c) C)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : ∀ i j, ‖A i j‖ ≤ x) (hB : ∀ i j, ‖B i j‖ ≤ y) (i j) :
    ‖(A * B) i j‖ ≤ x * y := by
  rw [Matrix.mul_apply]
  refine norm_sum_le _ (mul_nonneg hx hy) fun k => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hx

theorem norm_mulVec_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) C) (v : Fin b → C)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (i) : ‖A.mulVec v i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine norm_sum_le _ zero_le_one fun k => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _ _) (norm_nonneg _) (hv _)

theorem exists_bound_lt {a : ℕ} (A : Matrix (Fin a) (Fin a) C) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ i j, ‖A i j‖ < ρ) : ∃ x, 0 ≤ x ∧ x < ρ ∧ ∀ i j, ‖A i j‖ ≤ x := by
  refine ⟨‖fun p : Fin a × Fin a => A p.1 p.2‖, norm_nonneg _, ?_, fun i j => ?_⟩
  · exact (pi_norm_lt_iff hρ).2 fun p => h _ _
  · exact norm_le_pi_norm (fun p : Fin a × Fin a => A p.1 p.2) (i, j)

end Norm

theorem mem_mul {C : Type} [Field C] (F : Subfield C) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C)
    (B : Matrix (Fin b) (Fin c) C) (hA : ∀ i j, A i j ∈ F) (hB : ∀ i j, B i j ∈ F) (i j) :
    (A * B) i j ∈ F := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA _ _) (hB _ _)

variable {l : ℕ} [Fact l.Prime]

def subC (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) :=
  F.toSubfield.map (algebraMap (Om l) (PadicComplex l))

theorem mem_subC {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ subC F ↔ y ∈ inC F := Iff.rfl

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ subC F) : act σ y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 := ha.1 σ x
  have h2 : σ x = x := hσ ⟨x, hx⟩
  rw [h2] at h1
  exact h1

theorem map_mul' {a b c : ℕ} (f : PadicComplex l ≃+* PadicComplex l)
    (A : Matrix (Fin a) (Fin b) (PadicComplex l)) (B : Matrix (Fin b) (Fin c) (PadicComplex l)) :
    (A * B).map f = A.map f * B.map f := by
  ext i j
  simp [Matrix.mul_apply]

theorem frame_of_idem (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (ha : IsActC act) (K : FinExt l) (m d r : ℕ)
    (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (Dm E : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (hD : IsDec act χ K m M Dm U g)
    (hEM : ∀ σ ∈ Gj K m, E * M σ = M σ * E) (hEσ : ∀ σ ∈ Gj K m, E.map (act σ) = E)
    (hEF : ∀ i j, (Dm⁻¹ * E * Dm) i j ∈ subC (Ks K m))
    (R : Matrix (Fin r) (Fin d) (PadicComplex l)) (S : Matrix (Fin d) (Fin r) (PadicComplex l))
    (hR : ∀ i j, R i j ∈ subC (Ks K m) ∧ ‖R i j‖ ≤ 1)
    (hS : ∀ i j, S i j ∈ subC (Ks K m) ∧ ‖S i j‖ ≤ 1)
    (hRS : R * S = 1) (hRe : R * (Dm⁻¹ * E * Dm) = R) (heSR : (Dm⁻¹ * E * Dm) * S * R = Dm⁻¹ * E * Dm)
    (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ) (hli : LinearIndependent (PadicComplex l) e)
    (hfix : ∀ σ ∈ Gj K m, ∀ k, twAct act χ (u k) M σ (e k) = e k) (J : Set ℤ)
    (hJ : ∀ k, E.mulVec (e k) ≠ 0 → u k ∈ J) :
    Frame χ K m (fun σ => R * U σ * S) g ∧ HTBasis act χ (Gj K m) (fun σ => R * U σ * S) J ∧
    (∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ)) ∧
    ball l r ⊆ (R * Dm⁻¹).mulVec '' ball l d ∧
    (∀ x ∈ ball l d, (l : PadicComplex l) • (R * Dm⁻¹).mulVec x ∈ ball l r) ∧
    ∃ Q : Matrix (Fin d) (Fin r) (PadicComplex l), Q * (R * Dm⁻¹) = E := by
  obtain ⟨hdet, hDi, hDl, ⟨hgen, hcont, hint, hmul, hH, hg⟩, hrel⟩ := hD
  set e' := Dm⁻¹ * E * Dm with he'
  have h1 : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : Dm⁻¹ * Dm = 1 := Matrix.nonsing_inv_mul _ hdet
  have hDe : Dm * e' = E * Dm := by
    rw [he', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hfixm : ∀ σ ∈ Gj K m, ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (PadicComplex l)),
      (∀ i j, X i j ∈ subC (Ks K m)) → X.map (act σ) = X := by
    intro σ hσ a b X hX
    ext i j
    exact act_fix ha hσ (hX i j)
  have hcomm : ∀ σ ∈ Gj K m, e' * U σ = U σ * e' := by
    intro σ hσ
    have : Dm * (e' * U σ) = Dm * (U σ * e') := by
      rw [← Matrix.mul_assoc, hDe, Matrix.mul_assoc, hrel σ hσ, ← Matrix.mul_assoc, hEM σ hσ,
        Matrix.mul_assoc, ← Matrix.mul_assoc Dm, hrel σ hσ, Matrix.mul_assoc]
      congr 1
      conv_lhs => rw [← hEσ σ hσ]
      conv_rhs => rw [← hfixm σ hσ e' hEF]
      rw [← map_mul', ← map_mul', hDe]
    have h3 := congrArg (fun X => Dm⁻¹ * X) this
    simpa only [← Matrix.mul_assoc, h2, Matrix.one_mul] using h3
  have hkey : ∀ σ ∈ Gj K m, R * U σ * S * R = R * U σ := by
    intro σ hσ
    have h3 : R * U σ = R * U σ * e' := by
      rw [Matrix.mul_assoc, ← hcomm σ hσ, ← Matrix.mul_assoc, hRe]
    calc R * U σ * S * R = R * U σ * (e' * S * R) := by
          conv_lhs => rw [h3]
          simp only [Matrix.mul_assoc]
      _ = R * U σ := by rw [heSR, ← h3]
  have heq : ∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ) := by
    intro σ hσ
    have h3 : Dm.map (act σ) * Dm⁻¹.map (act σ) = 1 := by
      rw [← map_mul', h1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have h4 : Dm⁻¹ * M σ = U σ * Dm⁻¹.map (act σ) := by
      calc Dm⁻¹ * M σ = Dm⁻¹ * (M σ * Dm.map (act σ)) * Dm⁻¹.map (act σ) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
        _ = _ := by rw [← hrel σ hσ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [map_mul', hfixm σ hσ R (fun i j => (hR i j).1), ← Matrix.mul_assoc, hkey σ hσ,
      Matrix.mul_assoc, h4, Matrix.mul_assoc]
  have hsec : R * Dm⁻¹ * (Dm * S) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Dm⁻¹, h2, Matrix.one_mul, hRS]
  refine ⟨⟨hgen, ?_, ?_, ?_, ?_, ?_⟩, ?_, heq, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.mul_apply]
    refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
    exact continuousOn_finsetSum _ fun j _ => ContinuousOn.mul continuousOn_const (hcont _ _)
  · intro σ hσ a b
    refine ⟨mem_subC.1 (mem_mul _ _ _ (mem_mul _ _ _ (fun i j => (hR i j).1)
      (fun i j => mem_subC.2 (hint σ hσ i j).1)) (fun i j => (hS i j).1) a b), ?_⟩
    have := norm_mul_le (R * U σ) S (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (norm_mul_le R (U σ) zero_le_one zero_le_one (fun i j => (hR i j).2)
        (fun i j => (hint σ hσ i j).2)) (fun i j => (hS i j).2) a b
    simpa using this
  · intro σ hσ τ hτ
    simp only
    rw [hmul σ hσ τ hτ, ← Matrix.mul_assoc (R * U σ * S), ← Matrix.mul_assoc (R * U σ * S),
      hkey σ hσ]
    simp only [Matrix.mul_assoc]
  · intro σ hσ
    simp only
    rw [hH σ hσ, Matrix.mul_one, hRS]
  · intro a b
    have hrho : 0 < rho1 l :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
    obtain ⟨x, hx0, hx, hxb⟩ := exists_bound_lt (U g - 1) hrho hg
    have h3 : R * U g * S - 1 = R * (U g - 1) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRS]
    simp only
    rw [h3]
    have := norm_mul_le (R * (U g - 1)) S (mul_nonneg zero_le_one hx0) zero_le_one
      (norm_mul_le R (U g - 1) zero_le_one hx0 (fun i j => (hR i j).2) hxb)
      (fun i j => (hS i j).2) a b
    exact lt_of_le_of_lt (by simpa using this) hx
  · set Pm := R * Dm⁻¹ with hPm
    have hsp : Submodule.span (PadicComplex l) (Set.range fun k => Pm.mulVec (e k)) = ⊤ := by
      have h3 : Submodule.span (PadicComplex l) (Set.range e) = ⊤ :=
        hli.span_eq_top_of_card_eq_finrank' (by simp)
      have h4 : (Set.range fun k => Pm.mulVec (e k)) = Pm.mulVecLin '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [h4, ← Submodule.map_span, h3, Submodule.map_top, LinearMap.range_eq_top]
      intro y
      refine ⟨(Dm * S).mulVec y, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hsec, Matrix.one_mulVec]
    obtain ⟨κ, hκ⟩ := exists_sub_basis _ hsp
    refine ⟨fun k => Pm.mulVec (e (κ k)), fun k => u (κ k), hκ, fun k => hJ _ fun h0 => ?_, ?_⟩
    · apply hκ.ne_zero k
      have h3 : Pm * E = Pm := by
        calc Pm * E = R * e' * Dm⁻¹ := by
              rw [hPm, he']; simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          _ = Pm := by rw [hRe]
      show Pm.mulVec (e (κ k)) = 0
      rw [← h3, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    · intro σ hσ k
      have h3 := hfix σ hσ (κ k)
      unfold twAct at h3 ⊢
      have hmap : (fun a => act σ (Pm.mulVec (e (κ k)) a)) =
          (Pm.map (act σ)).mulVec (fun a => act σ (e (κ k) a)) := by
        funext a
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      simp only
      rw [hmap, Matrix.mulVec_mulVec, ← heq σ hσ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, h3]
  · intro y hy
    refine ⟨Dm.mulVec (S.mulVec y), norm_mulVec_le _ _ hDi
      (norm_mulVec_le _ _ (fun i j => (hS i j).2) hy), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hsec, Matrix.one_mulVec]
  · intro x hx
    have h3 : (l : PadicComplex l) • (R * Dm⁻¹).mulVec x =
        R.mulVec (((l : PadicComplex l) • Dm⁻¹).mulVec x) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    rw [h3]
    exact norm_mulVec_le _ _ (fun i j => (hR i j).2) (norm_mulVec_le _ _ (fun i j => hDl i j) hx)
  · refine ⟨Dm * e' * S, ?_⟩
    calc Dm * e' * S * (R * Dm⁻¹) = Dm * (e' * S * R) * Dm⁻¹ := by simp only [Matrix.mul_assoc]
      _ = E := by rw [heSR, hDe, Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.TauFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc

namespace ParamRing

variable {R : Type} [CommRing R] {σ : R⟦X⟧ →ₐ[R] R⟦X⟧} {w : R⟦X⟧} {s : ℕ}

theorem X_pow_dvd_map (h : σ X = w * X ^ s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    X ^ (s * j) ∣ σ G := by
  obtain ⟨H, rfl⟩ := hG
  exact ⟨w ^ j * σ H, by rw [map_mul, map_pow, h, pow_mul]; ring⟩

theorem coeff_map_lead (h : σ X = w * X ^ s) (hs : 0 < s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    coeff (s * j) (σ G) = constantCoeff w ^ j * coeff j G := by
  obtain ⟨H, rfl⟩ := hG
  have h0 : constantCoeff (σ H) = constantCoeff H := by
    conv_lhs => rw [eq_X_mul_shift_add_const H]
    rw [map_add (f := _), map_mul, h, show σ (C (constantCoeff H)) = C (constantCoeff H) from σ.commutes _]
    simp [hs.ne']
  have h1 : σ (X ^ j * H) = X ^ (s * j) * (w ^ j * σ H) := by
    rw [map_mul, map_pow, h, pow_mul]; ring
  have h2 := coeff_X_pow_mul (w ^ j * σ H) (s * j) 0
  have h3 := coeff_X_pow_mul H j 0
  rw [zero_add] at h2 h3
  rw [h1, h2, h3]
  simp [h0]

theorem lead_sum (h : σ X = w * X ^ s) (hs : 0 < s) (G : Fin s → R⟦X⟧) (n : ℕ)
    (hG : ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0) :
    X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) ∧
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) =
        constantCoeff w ^ (n / s) * coeff (n / s) (G ⟨n % s, Nat.mod_lt _ hs⟩) := by
  have hn := Nat.mod_add_div n s
  have key : ∀ k : Fin s, (k : ℕ) ≠ n % s → X ^ (n + 1) ∣ X ^ (k : ℕ) * σ (G k) := by
    intro k hk
    have hk' := k.2
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h1 : X ^ (n / s + 1) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.lt_succ_iff.1 hm)
        omega)
      refine (pow_dvd_pow X ?_).trans ((X_pow_dvd_map h h1).mul_left _)
      have := Nat.mod_lt n hs
      rw [mul_add]; omega
    · have h1 : X ^ (n / s) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hm)
        rw [Nat.mul_succ] at this
        omega)
      refine (pow_dvd_pow X (show n + 1 ≤ k + s * (n / s) by omega)).trans ?_
      rw [pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
  have h1 : X ^ (n / s) ∣ G ⟨n % s, Nat.mod_lt _ hs⟩ := X_pow_dvd_iff.2 fun m hm => hG _ m (by
    have := Nat.mul_lt_mul_of_pos_left hm hs
    simp only
    omega)
  constructor
  · refine Finset.dvd_sum fun k _ => ?_
    by_cases hk : (k : ℕ) = n % s
    · obtain rfl : k = ⟨n % s, Nat.mod_lt _ hs⟩ := Fin.ext hk
      conv_lhs => rw [← hn, pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
    · exact (pow_dvd_pow X n.le_succ).trans (key k hk)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single ⟨n % s, Nat.mod_lt _ hs⟩]
    · rw [← coeff_map_lead h hs h1, ← coeff_X_pow_mul (σ _) (n % s) (s * (n / s)), add_comm, hn]
    · intro k _ hk
      exact X_pow_dvd_iff.1 (key k fun e => hk (Fin.ext e)) n n.lt_succ_self
    · simp

theorem eq_zero_of_lead (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (G : Fin s → R⟦X⟧)
    (hG : ∀ n, X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) →
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) = 0 ∨ G ⟨n % s, Nat.mod_lt _ hs⟩ = 0) : G = 0 := by
  have key : ∀ n, ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0 := by
    intro n
    induction n with
    | zero => intro k j hj; omega
    | succ n ih =>
      intro k j hj
      rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | hj
      · exact ih k j hj
      obtain ⟨h1, h2⟩ := lead_sum h hs G n ih
      have e1 : n % s = k := by rw [← hj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.2]
      have e2 : n / s = j := by rw [← hj, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt k.2, zero_add]
      have e3 : (⟨n % s, Nat.mod_lt _ hs⟩ : Fin s) = k := Fin.ext e1
      have h3 := hG n h1
      rw [h2, e3, e2] at h3
      rcases h3 with h3 | h3
      · exact ((hw.map constantCoeff).pow j).mul_right_eq_zero.1 h3
      · rw [h3, map_zero]
  ext k j
  exact key _ k j (Nat.lt_succ_self _)

theorem exists_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃ G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  let T : R⟦X⟧ → R⟦X⟧ := fun b => v * mk fun i => coeff (i + s) b
  let G : R⟦X⟧ → Fin s → R⟦X⟧ := fun b k => mk fun j => coeff k (T^[j] b)
  have hT : ∀ b : R⟦X⟧, b = σ X * T b + ∑ k : Fin s, X ^ (k : ℕ) * C (coeff k b) := by
    intro b
    have h1 : σ X * T b = X ^ s * mk fun i => coeff (i + s) b := by
      simp only [h, T]
      linear_combination (X ^ s * mk fun i => coeff (i + s) b) * hv
    rw [h1]
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), coeff_X_pow_mul', map_sum]
    simp only [coeff_mul_C, coeff_X_pow, coeff_mk]
    split_ifs with hn
    · rw [Nat.sub_add_cancel hn, Finset.sum_eq_zero, add_zero]
      intro k _
      have := k.2
      rw [if_neg (by omega), zero_mul]
    · rw [zero_add, Finset.sum_eq_single ⟨n, by omega⟩]
      · simp
      · intro k _ hk
        rw [if_neg (fun e => hk (Fin.ext e.symm)), zero_mul]
      · simp
  have hG : ∀ b k, σ (G b k) = σ X * σ (G (T b) k) + C (coeff k b) := by
    intro b k
    have : G b k = X * G (T b) k + C (coeff k b) := by
      conv_lhs => rw [eq_X_mul_shift_add_const (G b k)]
      simp [G]
    rw [this, map_add (f := _), map_mul]
    congr 1
    exact σ.commutes _
  have key : ∀ n, ∀ b : R⟦X⟧, X ^ n ∣ b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro b
      have : b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) =
          σ X * (T b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G (T b) k)) := by
        have h1 := hT b
        simp only [hG b, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum, mul_left_comm (σ X)]
        linear_combination h1
      rw [this, pow_succ']
      refine mul_dvd_mul ?_ (ih _)
      rw [h]
      exact (dvd_pow_self X hs.ne').mul_left w
  refine ⟨G b, sub_eq_zero.1 ?_⟩
  ext n
  exact X_pow_dvd_iff.1 (key (n + 1) b) n n.lt_succ_self

theorem existsUnique_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃! G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨G, hG⟩ := exists_sum h hs hw b
  refine ⟨G, hG, fun G' hG' => sub_eq_zero.1 (eq_zero_of_lead h hs hw _ fun n _ => Or.inl ?_)⟩
  simp only [Pi.sub_apply, map_sub σ, mul_sub, Finset.sum_sub_distrib, ← hG, ← hG', sub_self, map_zero]

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [Algebra ℤ_[l] O] (hl : (l : O) ≠ 0) : Function.Injective (algebraMap ℤ_[l] O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl) hx

end ParamRing

open ParamRing

theorem invariants_param : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (Δ : Subgroup ℤ_[l]ˣ) [Fintype ↥Δ] (π' w : PowerSeries O), IsUnit w → π' = w * PowerSeries.X ^ Fintype.card ↥Δ → (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) π' = π') → (∀ b : PowerSeries O, ∃! G : Fin (Fintype.card ↥Δ) → PowerSeries O, b = ∑ k : Fin (Fintype.card ↥Δ), PowerSeries.X ^ (k : ℕ) * PowerSeries.subst π' (G k)) ∧ ∀ b : PowerSeries O, (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) b = b) ↔ ∃ g : PowerSeries O, b = PowerSeries.subst π' g := by
  intro l _ O _ _ _ _ _ hl _ Δ _ π' w hw hπ hinv
  have hs : 0 < Fintype.card ↥Δ := Fintype.card_pos
  have hsub : HasSubst π' := HasSubst.of_constantCoeff_zero' (by simp [hπ, hs.ne'])
  set σ : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hsub with hσ
  have hσa : ∀ g, subst π' g = σ g := fun g => (congrFun (coe_substAlgHom hsub) g).symm
  have hσX : σ X = w * X ^ Fintype.card ↥Δ := (substAlgHom_X hsub).trans hπ
  have hfix : ∀ (d : ↥Δ) (g : O⟦X⟧), act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) (σ g) = σ g := by
    intro d g
    have := hinv d
    rw [act_apply] at this
    rw [← hσa, act_apply, subst_comp_subst_apply hsub
      (HasSubst.of_constantCoeff_zero' (cyc_const l O _)), this]
  simp only [hσa]
  refine ⟨existsUnique_sum hσX hs hw, fun b => ⟨fun hb => ?_, ?_⟩⟩
  swap
  · rintro ⟨g, rfl⟩ d
    exact hfix d g
  obtain ⟨G, hG⟩ := exists_sum hσX hs hw b
  refine ⟨G ⟨0, hs⟩, ?_⟩
  have hG' : b - σ (G ⟨0, hs⟩) =
      ∑ k : Fin (Fintype.card ↥Δ), X ^ (k : ℕ) * σ (Function.update G ⟨0, hs⟩ 0 k) := by
    rw [hG, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩)]
    simp only [pow_zero, one_mul, Function.update_self, map_zero, zero_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have h0 : Function.update G ⟨0, hs⟩ 0 = 0 := by
    refine eq_zero_of_lead hσX hs hw _ fun n hn => ?_
    rw [← hG'] at hn ⊢
    by_cases hd : Fintype.card ↥Δ ∣ n
    · right
      have : (⟨n % _, Nat.mod_lt _ hs⟩ : Fin (Fintype.card ↥Δ)) = ⟨0, hs⟩ :=
        Fin.ext (Nat.mod_eq_zero_of_dvd hd)
      rw [this, Function.update_self]
    left
    by_contra hc
    apply hd
    haveI : IsCyclic ↥Δ := isCyclic_of_injective_ringHom ((Units.coeHom ℤ_[l]).comp Δ.subtype)
      (Units.val_injective.comp Subtype.val_injective)
    obtain ⟨d, hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Δ)
    rw [← Nat.card_eq_fintype_card, ← hd, orderOf_dvd_iff_pow_eq_one]
    obtain ⟨u, hu⟩ : (X : O⟦X⟧) ∣ cyc l O ((d : ℤ_[l]ˣ) : ℤ_[l]) := X_dvd_iff.2 (cyc_const l O _)
    have hu0 : constantCoeff u = algebraMap ℤ_[l] O ((d : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [← coeff_one_cyc, hu, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]
    have h1 := coeff_map_lead (σ := act l O ((d : ℤ_[l]ˣ) : ℤ_[l])) (w := u) (s := 1)
      (by rw [act_X, hu, pow_one, mul_comm]) one_pos hn
    rw [map_sub (act l O _), hb, hfix, one_mul, hu0, ← map_pow, eq_comm, mul_eq_right₀ hc,
      ← map_one (algebraMap ℤ_[l] O)] at h1
    have h2 := algebraMap_injective l O hl h1
    apply Subtype.ext
    apply Units.ext
    simpa using h2
  rw [← sub_eq_zero, hG', h0]
  simp

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltrationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_inf_filtration_ne_succ : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W), Module.Finite E ↥D → (∀ a, F (a + 1) ≤ F a) → {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  first | exact @GlobalTheory.finite_jumps_inf_filtration | exact GlobalTheory.finite_jumps_inf_filtration | (intros; apply GlobalTheory.finite_jumps_inf_filtration <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChangeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_periodFunctor_coeff_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  first | exact @GlobalTheory.CoeffBC.finrank_baseChange | exact GlobalTheory.CoeffBC.finrank_baseChange | (intros; apply GlobalTheory.CoeffBC.finrank_baseChange <;> assumption)
end

