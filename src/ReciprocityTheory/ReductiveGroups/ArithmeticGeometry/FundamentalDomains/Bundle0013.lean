module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.DetToMatrixSq

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientMatrices
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Fam

variable {ι : Type} [Fintype ι]

def kap (b : ι → Fin 2 → Fin 2 → ℂ) : ι → Fin 2 → Fin 2 → ℝ :=
  fun τ i k => if (i : ℕ) ≤ k then (b τ i k).re else (b τ k i).im

def th (y : ι → Fin 2 → Fin 2 → ℝ) : ι → Fin 2 → Fin 2 → ℂ :=
  fun τ i k => if i = k then (y τ i k : ℂ) else if (i : ℕ) < k then (y τ i k : ℂ) + I * y τ k i
    else (y τ k i : ℂ) - I * y τ i k

def kapL : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℝ) where
  toFun := kap
  map_add' b c := by
    funext τ i k; simp only [kap, Pi.add_apply]; split_ifs <;> simp
  map_smul' s b := by
    funext τ i k; simp only [kap, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def thL : (ι → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℂ) where
  toFun := th
  map_add' y z := by
    funext τ i k; simp only [th, Pi.add_apply]; split_ifs <;> push_cast <;> ring
  map_smul' s y := by
    funext τ i k; simp only [th, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Complex.real_smul]
    split_ifs <;> push_cast <;> ring

lemma th_herm (y : ι → Fin 2 → Fin 2 → ℝ) : IsHermFam (th y) := by
  intro τ i k
  fin_cases i <;> fin_cases k <;> simp [th] <;> ring

lemma kap_th (y : ι → Fin 2 → Fin 2 → ℝ) : kap (th y) = y := by
  funext τ i k
  fin_cases i <;> fin_cases k <;> simp [kap, th]

lemma th_kap {b : ι → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) : th (kap b) = b := by
  funext τ i k
  have h00 := hb τ 0 0
  have h11 := hb τ 1 1
  have h01 := hb τ 0 1
  rw [Complex.ext_iff] at h00 h11 h01
  simp at h00 h11 h01
  fin_cases i <;> fin_cases k <;> apply Complex.ext <;> simp [th, kap] <;> linarith

lemma th_zero : th (0 : ι → Fin 2 → Fin 2 → ℝ) = 0 := by
  funext τ i k
  simp [th]

lemma conj_herm {χ : ι → Fin 2 → Fin 2 → ℂ} (h : IsHermFam χ) :
    IsHermFam (fun τ i k => conj (χ τ i k)) := by
  intro τ i k
  show conj (χ τ k i) = conj (conj (χ τ i k))
  rw [h τ i k]

def pr (χ b : ι → Fin 2 → Fin 2 → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re

lemma pr_add_right (χ b c : ι → Fin 2 → Fin 2 → ℂ) : pr χ (b + c) = pr χ b + pr χ c := by
  simp only [pr, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

lemma pr_add_left (χ ψ b : ι → Fin 2 → Fin 2 → ℂ) : pr (χ + ψ) b = pr χ b + pr ψ b := by
  simp only [pr, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re]

lemma pr_smul_right (χ b : ι → Fin 2 → Fin 2 → ℂ) (s : ℝ) : pr χ ((s : ℂ) • b) = s * pr χ b := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_left_comm _ (s : ℂ), ← Finset.mul_sum, Complex.re_ofReal_mul]

lemma pr_smul_left (χ b : ι → Fin 2 → Fin 2 → ℂ) (s : ℝ) : pr ((s : ℂ) • χ) b = s * pr χ b := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

def prL (χ : ι → Fin 2 → Fin 2 → ℂ) : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] ℝ where
  toFun := pr χ
  map_add' := pr_add_right χ
  map_smul' s b := by rw [← Complex.coe_smul, pr_smul_right]; rfl

def prR (b : ι → Fin 2 → Fin 2 → ℂ) : (ι → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] ℝ where
  toFun χ := pr χ b
  map_add' χ ψ := pr_add_left χ ψ b
  map_smul' s χ := by simp only [RingHom.id_apply, smul_eq_mul]; rw [← Complex.coe_smul, pr_smul_left]

lemma pr_sum {N : ℕ} (χ : ι → Fin 2 → Fin 2 → ℂ) (c : Fin N → ℝ) (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ) :
    pr χ (∑ j, (c j : ℂ) • ω j) = ∑ j, c j * pr χ (ω j) := by
  show prL χ (∑ j, (c j : ℂ) • ω j) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pr_smul_right χ (ω j) (c j)

lemma eq_zero_of_pr_conj {χ : ι → Fin 2 → Fin 2 → ℂ}
    (h : pr χ (fun τ i k => conj (χ τ i k)) = 0) : χ = 0 := by
  simp only [pr, Complex.mul_conj] at h
  simp only [← Complex.ofReal_sum, Complex.ofReal_re] at h
  funext τ i k
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)] at h
  have h2 := h τ (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ =>
    Complex.normSq_nonneg _)] at h2
  have h3 := h2 i (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)] at h3
  exact Complex.normSq_eq_zero.mp (h3 k (Finset.mem_univ _))

lemma finrank_rfam : Module.finrank ℝ (ι → Fin 2 → Fin 2 → ℝ) = 4 * Fintype.card ι := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_pi_fintype, mul_comm]

end Fam

section Basis

variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)

lemma kap_li (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) :
    LinearIndependent ℝ (fun j => kap (ω j)) := by
  rw [linearIndependent_iff'] at hli ⊢
  intro s g hg i hi
  refine hli s g ?_ i hi
  have h := congrArg thL hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  exact congrArg _ (th_kap (hω j)).symm

def basR (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι) :
    Module.Basis (Fin N) ℝ (ι → Fin 2 → Fin 2 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (kap_li ω hω hli) (by rw [Fintype.card_fin, finrank_rfam, hN])

lemma herm_eq_sum (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) {b : ι → Fin 2 → Fin 2 → ℂ} (hb : IsHermFam b) :
    ∃ s : Fin N → ℝ, b = ∑ j, (s j : ℂ) • ω j := by
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin N) ℝ (ι → Fin 2 → Fin 2 → ℝ), ⇑B = fun j => kap (ω j) :=
    ⟨basR ω hω hli hN, by unfold basR; exact coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  refine ⟨B.repr (kap b), ?_⟩
  have hsum := B.sum_repr (kap b)
  simp only [hB] at hsum
  calc b = thL (kap b) := (th_kap hb).symm
    _ = thL (∑ j, B.repr (kap b) j • kap (ω j)) := by rw [hsum]
    _ = ∑ j, (B.repr (kap b) j : ℂ) • ω j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Complex.coe_smul]
        exact congrArg _ (th_kap (hω j))

def phiL : (ι → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  LinearMap.pi fun j => (2 : ℝ) • ((prR (ω j)).comp thL)

lemma phiL_apply (z : ι → Fin 2 → Fin 2 → ℝ) (j : Fin N) : phiL ω z j = 2 * pr (th z) (ω j) := rfl

lemma phiL_inj (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) : Function.Injective (phiL ω) := by
  refine (injective_iff_map_eq_zero (phiL ω)).mpr fun z hz => ?_
  have hp : ∀ j, pr (th z) (ω j) = 0 := fun j => by
    have h := congrFun hz j
    rw [phiL_apply] at h
    simpa using h
  obtain ⟨s, hs⟩ := herm_eq_sum ω hω hli hN (conj_herm (th_herm z))
  have h0 : pr (th z) (fun τ i k => conj (th z τ i k)) = 0 := by
    rw [hs, pr_sum]
    simp [hp]
  have hz0 := eq_zero_of_pr_conj h0
  rw [← kap_th z, hz0]
  funext τ i k
  simp [kap]

lemma phiL_surj (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) : Function.Surjective (phiL ω) := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_rfam, Module.finrank_fin_fun, hN])).mp (phiL_inj ω hω hli hN)

def chiOf (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω)
    (hN : N = 4 * Fintype.card ι) (m : Fin N → ℝ) : ι → Fin 2 → Fin 2 → ℂ :=
  th ((LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩).symm m)

variable (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι)

lemma chiOf_herm (m : Fin N → ℝ) : IsHermFam (chiOf ω hω hli hN m) := th_herm _

lemma chiOf_pair (m : Fin N → ℝ) (j : Fin N) : 2 * pr (chiOf ω hω hli hN m) (ω j) = m j := by
  unfold chiOf
  exact congrFun (LinearEquiv.apply_symm_apply
    (LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩) m) j

lemma chiOf_eq {χ : ι → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) {m : Fin N → ℝ}
    (hm : ∀ j, 2 * pr χ (ω j) = m j) : χ = chiOf ω hω hli hN m := by
  unfold chiOf
  have he : phiL ω (kap χ) = m := funext fun j => by rw [phiL_apply, th_kap hχ, hm j]
  rw [← th_kap hχ]
  congr 1
  rw [← he]
  exact ((LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩).symm_apply_apply
    (kap χ)).symm

lemma chiOf_inj : Function.Injective (chiOf ω hω hli hN) := by
  intro m m' h
  funext j
  rw [← chiOf_pair ω hω hli hN m j, ← chiOf_pair ω hω hli hN m' j, h]

end Basis

section ZbFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

lemma mat_Zb (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl

lemma zmat_zero (τ : X.Ψ) : X.zmat u 0 τ = 1 := by
  ext a j
  simp [Data.zmat, Matrix.one_apply]

lemma Zb_zero (x : Frame X.Ψ r) : X.Zb u 0 x = x := by
  funext τ
  show X.zmat u 0 τ * mat x τ = x τ
  rw [zmat_zero, one_mul]
  rfl

def fac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

lemma pnorm_eq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * fac X la x := rfl

lemma fac_nonneg (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ fac X la x := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

end ZbFacts

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace QuadraticLatticeForms

open Matrix NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  unfold Data.c
  exact mul_pos two_pos (norm_pos_iff.mpr h)

noncomputable def ip (u w : X.Ψ → Fin r → ℂ) : ℝ := ∑ τ, X.c τ * (∑ a, u τ a * conj (w τ a)).re

theorem ip_add_left (u u' w : X.Ψ → Fin r → ℂ) : ip X (u + u') w = ip X u w + ip X u' w := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re, mul_add]

theorem ip_add_right (u w w' : X.Ψ → Fin r → ℂ) : ip X u (w + w') = ip X u w + ip X u w' := by
  simp only [ip, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem ip_smul_left (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X (k • u) w = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, (k • u) τ a * conj (w τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

theorem ip_smul_right (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X u (k • w) = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, u τ a * conj ((k • w) τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

noncomputable def ipB : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (ip X) (ip_add_left X) (ip_smul_left X) (ip_add_right X) (ip_smul_right X)

theorem ipB_apply (u w : X.Ψ → Fin r → ℂ) : ipB X u w = ip X u w := rfl

theorem ip_comm (u w : X.Ψ → Fin r → ℂ) : ip X u w = ip X w u := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem ip_self (u : X.Ψ → Fin r → ℂ) : ip X u u = ∑ τ, X.c τ * ∑ a, ‖u τ a‖ ^ 2 := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem ip_pos {u : X.Ψ → Fin r → ℂ} (hu : u ≠ 0) : 0 < ip X u u := by
  rw [ip_self]
  obtain ⟨τ, hτ⟩ : ∃ τ, u τ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ : ∃ a, u τ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hτ (funext h)
  apply Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X i).le
    (Finset.sum_nonneg fun b _ => sq_nonneg _))
  refine ⟨τ, Finset.mem_univ _, mul_pos (c_pos X τ) ?_⟩
  apply Finset.sum_pos' (fun b _ => sq_nonneg _)
  exact ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩

noncomputable def Ly (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) :
    (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ := (y τ)⁻¹ *ᵥ u τ
  map_add' u w := by funext τ; simp [Matrix.mulVec_add]
  map_smul' k u := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, Complex.real_smul]

noncomputable def Sg : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ a := ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a
  map_add' u w := by funext τ a; simp [mul_add]
  map_smul' k u := by funext τ a; simp [Complex.real_smul]; ring

noncomputable def Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) : ℝ :=
  ∑ τ, X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 v) a‖ ^ 2

theorem ip_Ly_self (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ip X (Ly X y (X.embV v)) (Ly X y (X.embV v)) = Qy X y v := by
  rw [ip_self]
  rfl

theorem Qy_nonneg (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) : 0 ≤ Qy X y v := by
  unfold Qy
  exact Finset.sum_nonneg fun τ _ => mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => sq_nonneg _)

theorem embV_sum {ι : Type} (s : Finset ι) (w : ι → Fin r → E) :
    X.embV (∑ i ∈ s, w i) = ∑ i ∈ s, X.embV (w i) := by
  funext τ a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Data.embV, Data.emb, Finset.sum_apply, map_sum]

theorem embV_zsmul (n : ℤ) (w : Fin r → E) : X.embV (n • w) = (n : ℝ) • X.embV w := by
  funext τ a
  simp only [Data.embV, Data.emb, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast,
    Complex.real_smul, Complex.ofReal_intCast]

theorem Ly_injective (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) :
    Function.Injective (Ly X y) := by
  intro u u' h
  funext τ
  have h1 : (y τ)⁻¹ *ᵥ u τ = (y τ)⁻¹ *ᵥ u' τ := congrFun h τ
  have hu : IsUnit (y τ).det := isUnit_iff_ne_zero.mpr (hy τ)
  have h2 := congrArg (fun v => y τ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2
  exact h2

theorem Ly_surjective (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) :
    Function.Surjective (Ly X y) := by
  intro v
  refine ⟨fun τ => y τ *ᵥ v τ, ?_⟩
  funext τ
  change (y τ)⁻¹ *ᵥ (y τ *ᵥ v τ) = v τ
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hy τ)), Matrix.one_mulVec]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def Am (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ip X (Ly X y (X.embV (g i : Fin r → E))) (Ly X y (X.embV (g j : Fin r → E)))

noncomputable def Bm (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ τ, X.c τ * (τ.1 (herm X.Gm (g i : Fin r → E) (g j : Fin r → E))).re

theorem quad_eq (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℝ) :
    x ⬝ᵥ (Am X y g *ᵥ x) = ip X (Ly X y (∑ i, x i • X.embV (g i : Fin r → E)))
      (Ly X y (∑ i, x i • X.embV (g i : Fin r → E))) := by
  have hL : Ly X y (∑ i, x i • X.embV (g i : Fin r → E)) =
      ∑ i, x i • Ly X y (X.embV (g i : Fin r → E)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [hL, ← ipB_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ipB_apply]
  simp only [dotProduct, Matrix.mulVec, Am, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ip_comm X (Ly X y (X.embV (g j : Fin r → E)))]
  ring

theorem quad_int (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℤ) :
    (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) =
      Qy X y (∑ i, x i • (g i : Fin r → E)) := by
  rw [quad_eq, ← ip_Ly_self, embV_sum]
  simp only [embV_zsmul]

theorem Am_posDef (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0)
    (g : Basis ι ℤ X.Λ) : (Am X y g).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp only [conjTranspose_apply, star_trivial, Am, of_apply]
    exact ip_comm X _ _
  · rw [star_trivial, quad_eq]
    refine ip_pos X fun h0 => hx ?_
    have h1 : ∑ i, x i • X.embV (g i : Fin r → E) = 0 := Ly_injective X y hy (by rw [h0, map_zero])
    exact funext (Fintype.linearIndependent_iff.mp (RealPlaceEmbeddings.linIndR X g) x h1)

end QuadraticLatticeForms

end ReciprocityTheory.ChartRestriction.G.FD
end

