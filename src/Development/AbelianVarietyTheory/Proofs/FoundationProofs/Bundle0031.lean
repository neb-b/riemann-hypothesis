module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicit
section
noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold Real

namespace GlobalTheory.Hk

private theorem im_div_pos' {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) (b : ℕ) :
    0 < ((z + b) / (p : ℂ)).im := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

private theorem sum_root' {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ∑ b ∈ Finset.range p, (Complex.exp (2 * π * Complex.I / p) ^ b) ^ m =
      if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp.ne'
  set ζ := Complex.exp (2 * π * Complex.I / p)
  simp_rw [← pow_mul, fun b => mul_comm b m, pow_mul]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have h1 : ζ ^ m ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd m).1 e)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]; simp

theorem hasSum_uOp (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq0 : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (uOp q f τ) := by
  have hp0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hinj : Function.Injective fun m : ℕ => q * m := mul_right_injective₀ hq0.ne'
  have hrange : ∀ n, n ∉ Set.range (fun m : ℕ => q * m) → ¬ q ∣ n :=
    fun n hn ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
  set Q := Function.Periodic.qParam 1 τ with hQ
  set x := Complex.exp (2 * π * Complex.I * τ / q) with hx
  have hxq : x ^ q = Q := by
    rw [hx, ← Complex.exp_nat_mul, hQ, Function.Periodic.qParam]; congr 1; push_cast; field_simp
  have hB : ∀ b : ℕ, HasSum (fun m => a m * x ^ m * (Complex.exp (2 * π * Complex.I / q) ^ b) ^ m)
      (f (ofComplex (((τ : ℂ) + b) / q))) := fun b => by
    have h := hf (ofComplex (((τ : ℂ) + b) / q))
    rw [ofComplex_apply_of_im_pos (im_div_pos' hq0 τ.2 b)] at h ⊢
    convert h using 2 with m
    have e : Function.Periodic.qParam 1 (((τ : ℂ) + b) / q) =
        x * Complex.exp (2 * π * Complex.I / q) ^ b := by
      rw [hx, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp [e, mul_pow, mul_assoc]
  have hC := hasSum_sum (s := Finset.range q) fun b _ => hB b
  simp_rw [← Finset.mul_sum, sum_root' hq0] at hC
  rw [← hinj.hasSum_iff fun n hn => by simp [hrange n hn]] at hC
  have hD := hC.mul_left (q : ℂ)⁻¹
  refine cast (congrArg (HasSum · (uOp q f τ)) (funext fun n => ?_)) hD
  simp only [Function.comp, dvd_mul_right, if_true, pow_mul, hxq, smul_eq_mul]
  field_simp

end GlobalTheory.Hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section
namespace GlobalTheory.SlashUpperTriangularMatrices

theorem toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL; rw [dite_eq_right h]; rfl

theorem slash_upper (k : ℤ) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL !![a, b; 0, d]) τ =
      f (ofComplex (((a : ℂ) * τ + b) / d)) * ((a : ℂ) * d) ^ (k - 1) * (d : ℂ) ^ (-k) := by
  have hdet : (!![a, b; 0, d]).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [ha.ne', hd.ne']
  have hv := toGL_val _ hdet
  set G := toGL !![a, b; 0, d]
  have e00 : G 0 0 = a := by simp [G, hv]
  have e01 : G 0 1 = b := by simp [G, hv]
  have e10 : G 1 0 = 0 := by simp [G, hv]
  have e11 : G 1 1 = d := by simp [G, hv]
  have hG : G.det.val = (a : ℝ) * d := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e00, e01, e10, e11]; ring
  have hpos : 0 < G.det.val := by rw [hG]; positivity
  have hsm : G • τ = ofComplex (((a : ℂ) * τ + b) / d) := by
    rw [← ofComplex_apply (G • τ), coe_smul_of_det_pos hpos]
    simp [num, denom, e00, e01, e10, e11]
  rw [ModularForm.slash_apply, hsm, σ, if_pos hpos, hG]
  have hden : denom G τ = d := by simp [denom, e10, e11]
  rw [hden, abs_of_pos (by positivity)]
  simp

theorem pow_pair (x : ℂ) (hx : x ≠ 0) (k : ℤ) : x ^ (k - 1) * x ^ (-k) = x⁻¹ := by
  rw [← zpow_add₀ hx]; ring_nf; simp

theorem toGL_SL (σ : SL(2, ℤ)) : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
  have h : (mat σ).det ≠ 0 := by simp [mat]
  ext i j
  rw [toGL_val _ h]
  simp [mat]

theorem ul_eq (k : ℤ) (l : ℕ) (f : ℍ → ℂ) (hl : 0 < l) : UlF k l f = GlobalTheory.Hk.uOp l f := by
  funext τ
  simp only [UlF, hkF, Finset.sum_apply, ulFam]
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  simp only [fun j : Fin l => slash_upper k 1 (j : ℤ) l one_pos hl' f τ]
  rw [GlobalTheory.Hk.uOp, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => f (ofComplex (((((1 : ℤ)) : ℂ) * τ + ((j : ℤ) : ℂ)) / ((l : ℤ) : ℂ))) *
      (((1 : ℤ) : ℂ) * ((l : ℤ) : ℂ)) ^ (k - 1) * ((l : ℤ) : ℂ) ^ (-k)) l]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : ((l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  rw [one_mul, one_mul, mul_assoc, pow_pair _ hx, mul_comm]

theorem dd_eq (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : DdF k σ f = GlobalTheory.Hk.dia k σ f := by
  simp [DdF, hkF, GlobalTheory.Hk.dia, toGL_SL, ModularForm.SL_slash]

theorem toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hg hh
  ext i j
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh, RingHom.map_mul]

theorem tq_eq (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) (hq : 0 < q) :
    TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f := by
  have hsplit : TqF k q σ f = UlF k q f + f ∣[k] toGL (mat σ * dg q 1) := by
    have e : ∀ i : Fin q, tqFam q σ i.castSucc = ulFam q i := fun i => by
      rw [tqFam, if_pos (by simp)]; rfl
    have e2 : tqFam q σ (Fin.last q) = mat σ * dg q 1 := by
      rw [tqFam, if_neg (by simp)]
    simp only [TqF, UlF, hkF]
    rw [Fin.sum_univ_castSucc, e2]
    simp only [e]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hdg : (dg q 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of, hq.ne']
  have hσ : (mat σ).det ≠ 0 := by simp [mat]
  rw [hsplit, ul_eq k q f hq, toGL_mul _ _ hσ hdg, SlashAction.slash_mul, toGL_SL, ← ModularForm.SL_slash,
    GlobalTheory.Hk.heckeT]
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [dg, slash_upper k q 0 1 hq' one_pos, GlobalTheory.Hk.vOp]
  push_cast
  simp [mul_comm]

theorem dia_iff (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ := by
  simp [IsDiam, GlobalTheory.Hk.IsDia, CongruenceSubgroup.Gamma0_mem, mat]

end GlobalTheory.SlashUpperTriangularMatrices

namespace GlobalTheory.SlashUpperTriangularMatrices

theorem bridge : (∀ (k : ℤ) (l : ℕ) (f : ℍ → ℂ), 0 < l → UlF k l f = GlobalTheory.Hk.uOp l f) ∧
  (∀ (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), DdF k σ f = GlobalTheory.Hk.dia k σ f) ∧
  (∀ (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f) ∧
  (∀ (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)), IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ) ∧
  ∀ N l : ℕ, Lev N l = GlobalTheory.Hk.lev N l :=
  ⟨fun k l f hl => ul_eq k l f hl, dd_eq, fun k q σ f hq => tq_eq k q σ f hq, dia_iff, fun _ _ => rfl⟩

end GlobalTheory.SlashUpperTriangularMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesCosetsDistinct
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory

theorem tqFam_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime →
    tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  intro q σ g i i' hq h
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have hdet : (mat g).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (· 0 0) h
  have e01 := congrArg (· 0 1) h
  have e10 := congrArg (· 1 0) h
  have e11 := congrArg (· 1 1) h
  simp only [tqFam] at e00 e01 e10 e11
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases h1 : (i : ℕ) < q <;> by_cases h2 : (i' : ℕ) < q <;>
    simp only [h1, h2, if_true, if_false, dg, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e00 e01 e10 e11
  ·
    apply Fin.ext
    have hg00 : (mat g) 0 0 = 1 := by linarith
    rw [hg00] at e01
    have hii : (0:ℤ) ≤ (i : ℕ) := by positivity
    have hii' : (0:ℤ) ≤ (i' : ℕ) := by positivity
    have hlt : ((i : ℕ) : ℤ) < q := by exact_mod_cast h1
    have hlt' : ((i' : ℕ) : ℤ) < q := by exact_mod_cast h2
    rcases lt_trichotomy ((mat g) 0 1) 0 with hn | hz | hp
    · exfalso; nlinarith
    · rw [hz] at e01; exact_mod_cast (by linarith : ((i : ℕ) : ℤ) = (i' : ℕ))
    · exfalso; nlinarith
  · exfalso
    have hd : (q : ℤ) ∣ 1 := ⟨mat g 0 0 * mat σ 0 0 + mat g 0 1 * mat σ 1 0, by linear_combination e00⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · exfalso
    have hd : (q : ℤ) ∣ 1 := by
      rw [← hdet]
      exact Dvd.dvd.sub (Dvd.dvd.mul_right ⟨mat σ 0 0, by linear_combination -e00⟩ _)
        (Dvd.dvd.mul_left ⟨mat σ 1 0, by linear_combination -e10⟩ _)
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · apply Fin.ext; omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesRightMulPermutesCosets
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.TqPerm

theorem sl_det (g : SL(2, ℤ)) : mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0 = 1 := by
  have h := g.det_coe
  rw [Matrix.det_fin_two] at h
  exact h

theorem mem_lev (N l : ℕ) (g : SL(2, ℤ)) :
    g ∈ Lev N l ↔ (N : ℤ) ∣ mat g 0 0 - 1 ∧ (N : ℤ) ∣ mat g 1 0 ∧ (l : ℤ) ∣ mat g 1 0 := by
  have hd := sl_det g
  simp only [Lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  constructor
  · rintro ⟨⟨h1, _, h3⟩, h4⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    refine ⟨⟨h1, ?_, h3⟩, h4⟩
    have h := congrArg (Int.cast : ℤ → ZMod N) hd
    push_cast at h
    rw [h1, h3] at h
    simpa using h

theorem diam_facts {N l q : ℕ} {σ : SL(2, ℤ)} (h : IsDiam N l (q : ZMod N) σ) :
    (N : ℤ) ∣ mat σ 1 0 ∧ (l : ℤ) ∣ mat σ 1 0 ∧ (N : ℤ) ∣ mat σ 1 1 - q := by
  obtain ⟨h1, h2⟩ := h
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  refine ⟨(dvd_mul_right _ _).trans h1, (dvd_mul_left _ _).trans h1, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h2, sub_self]

def InDelta (N l q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 = q ∧ (N : ℤ) ∣ M 0 0 - 1 ∧ (N : ℤ) ∣ M 1 0 ∧ (l : ℤ) ∣ M 1 0

theorem tqFam_inDelta {N l q : ℕ} {σ : SL(2, ℤ)} (h : IsDiam N l (q : ZMod N) σ) (i : Fin (q + 1)) :
    InDelta N l q (tqFam q σ i) := by
  obtain ⟨⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩⟩ := diam_facts h
  have hd := sl_det σ
  unfold tqFam InDelta
  split_ifs with hi
  · simp
  · simp only [dg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨by linear_combination (q : ℤ) * hd, ⟨mat σ 0 1 * c1 - mat σ 0 0 * c3, ?_⟩, ⟨c1 * q, ?_⟩, ⟨c2 * q, ?_⟩⟩
    · linear_combination hd + mat σ 0 1 * h1 - mat σ 0 0 * h3
    · linear_combination (q : ℤ) * h1
    · linear_combination (q : ℤ) * h2

theorem InDelta.mul {N l q : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : InDelta N l q M) {g : SL(2, ℤ)}
    (hg : g ∈ Lev N l) : InDelta N l q (M * mat g) := by
  obtain ⟨h0, h1, h2, h3⟩ := hM
  obtain ⟨g1, g2, g3⟩ := (mem_lev N l g).1 hg
  have hd := sl_det g
  unfold InDelta
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨by linear_combination (mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0) * h0 + (q : ℤ) * hd, ?_, ?_, ?_⟩
  · have : M 0 0 * mat g 0 0 + M 0 1 * mat g 1 0 - 1
        = (M 0 0 - 1) * mat g 0 0 + (mat g 0 0 - 1) + M 0 1 * mat g 1 0 := by ring
    rw [this]
    exact dvd_add (dvd_add (h1.mul_right _) g1) (g2.mul_left _)
  · exact dvd_add (h2.mul_right _) (g2.mul_left _)
  · exact dvd_add (h3.mul_right _) (g3.mul_left _)

theorem exists_res {q : ℕ} (hq : q.Prime) {x : ℤ} (hx : ¬ (q : ℤ) ∣ x) (y : ℤ) :
    ∃ j : ℕ, j < q ∧ (q : ℤ) ∣ y - j * x := by
  haveI := Fact.mk hq
  have hx' : (x : ZMod q) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((y : ZMod q) / x).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hx', sub_self]

theorem exists_upper {N l q : ℕ} (hq : q.Prime) (σ : SL(2, ℤ)) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : InDelta N l q M) {j : ℕ} (hj : j < q) (ha : (q : ℤ) ∣ M 0 1 - j * M 0 0)
    (hb : (q : ℤ) ∣ M 1 1 - j * M 1 0) :
    ∃ (k : Fin (q + 1)) (g : Lev N l), M = mat g * tqFam q σ k := by
  obtain ⟨h0, h1, h2, h3⟩ := hM
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdet : (!![M 0 0, u; M 1 0, v] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    apply mul_left_cancel₀ hq0
    linear_combination h0 - M 0 0 * hv + M 1 0 * hu
  refine ⟨⟨j, by omega⟩, ⟨⟨_, hdet⟩, (mem_lev N l _).2 ⟨h1, h2, h3⟩⟩, ?_⟩
  show M = !![M 0 0, u; M 1 0, v] * _
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tqFam, hj, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hu
  · linear_combination hv

theorem exists_rep {N l q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * l) {σ : SL(2, ℤ)}
    (hσ : IsDiam N l (q : ZMod N) σ) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : InDelta N l q M) :
    ∃ (k : Fin (q + 1)) (g : Lev N l), M = mat g * tqFam q σ k := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have h0 := hM.1
  by_cases hα : (q : ℤ) ∣ M 0 0
  · by_cases hγ : (q : ℤ) ∣ M 1 0
    · obtain ⟨-, h1, h2, h3⟩ := hM
      obtain ⟨u, hu⟩ := hα
      obtain ⟨v, hv⟩ := hγ
      obtain ⟨s1, s2, s3⟩ := diam_facts hσ
      have hd := sl_det σ
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hcN : IsCoprime (N : ℤ) q := Nat.isCoprime_iff_coprime.2
        ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right _)).symm
      have hcl : IsCoprime (l : ℤ) q := Nat.isCoprime_iff_coprime.2
        ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_left _)).symm
      have hNv : (N : ℤ) ∣ v := hcN.dvd_of_dvd_mul_left (hv ▸ h2)
      have hlv : (l : ℤ) ∣ v := hcl.dvd_of_dvd_mul_left (hv ▸ h3)
      have hd' : u * M 1 1 - M 0 1 * v = 1 := by
        apply mul_left_cancel₀ hq0
        linear_combination h0 - M 1 1 * hu + M 0 1 * hv
      have hdet : (!![u * mat σ 1 1 - M 0 1 * mat σ 1 0, -u * mat σ 0 1 + M 0 1 * mat σ 0 0;
          v * mat σ 1 1 - M 1 1 * mat σ 1 0, -v * mat σ 0 1 + M 1 1 * mat σ 0 0] :
          Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination (u * M 1 1 - M 0 1 * v) * hd + hd'
      refine ⟨Fin.last q, ⟨⟨_, hdet⟩, (mem_lev N l _).2 ⟨?_, ?_, ?_⟩⟩, ?_⟩
      · show (N : ℤ) ∣ u * mat σ 1 1 - M 0 1 * mat σ 1 0 - 1
        have : u * mat σ 1 1 - M 0 1 * mat σ 1 0 - 1
            = u * (mat σ 1 1 - q) - M 0 1 * mat σ 1 0 + (M 0 0 - 1) := by rw [hu]; ring
        rw [this]
        exact dvd_add (dvd_sub (s3.mul_left _) (s1.mul_left _)) h1
      · exact dvd_sub (hNv.mul_right _) (s1.mul_left _)
      · exact dvd_sub (hlv.mul_right _) (s2.mul_left _)
      · show M = !![u * mat σ 1 1 - M 0 1 * mat σ 1 0, -u * mat σ 0 1 + M 0 1 * mat σ 0 0;
          v * mat σ 1 1 - M 1 1 * mat σ 1 0, -v * mat σ 0 1 + M 1 1 * mat σ 0 0] * _
        ext a b
        fin_cases a <;> fin_cases b <;> simp [tqFam, dg, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination hu - q * u * hd
        · linear_combination (-M 0 1) * hd
        · linear_combination hv - q * v * hd
        · linear_combination (-M 1 1) * hd
    · obtain ⟨j, hj, hb⟩ := exists_res hq hγ (M 1 1)
      refine exists_upper hq σ hM hj ?_ hb
      have : (q : ℤ) ∣ M 1 0 * (M 0 1 - j * M 0 0) := by
        have e : M 1 0 * (M 0 1 - j * M 0 0) = M 0 0 * (M 1 1 - j * M 1 0) - q := by linear_combination -h0
        rw [e]
        exact dvd_sub (hb.mul_left _) dvd_rfl
      exact (hp.dvd_or_dvd this).resolve_left hγ
  · obtain ⟨j, hj, ha⟩ := exists_res hq hα (M 0 1)
    refine exists_upper hq σ hM hj ha ?_
    have : (q : ℤ) ∣ M 0 0 * (M 1 1 - j * M 1 0) := by
      have e : M 0 0 * (M 1 1 - j * M 1 0) = M 1 0 * (M 0 1 - j * M 0 0) + q := by linear_combination h0
      rw [e]
      exact dvd_add (ha.mul_left _) dvd_rfl
    exact (hp.dvd_or_dvd this).resolve_left hα

theorem tqFam_inj {q : ℕ} (hq : q.Prime) (σ h : SL(2, ℤ)) {i k : Fin (q + 1)}
    (e : tqFam q σ i = mat h * tqFam q σ k) : i = k := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hd := sl_det h
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have hi := i.2
  have hk := k.2
  by_cases a : (i : ℕ) < q <;> by_cases b : (k : ℕ) < q
  · simp [tqFam, a, b, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    have hdv : (q : ℤ) ∣ ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) := ⟨mat h 0 1, by linear_combination e01 - ((k : ℕ) : ℤ) * e00⟩
    have := Int.eq_zero_of_abs_lt_dvd hdv (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  · exfalso
    simp [tqFam, a, b, dg, Matrix.mul_apply, Fin.sum_univ_two] at e00
    exact hp.not_dvd_one ⟨mat h 0 0 * mat σ 0 0 + mat h 0 1 * mat σ 1 0, by linear_combination e00⟩
  · exfalso
    simp [tqFam, a, b, dg, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
    exact hp.not_dvd_one ⟨mat σ 0 0 * mat h 1 1 - mat h 0 1 * mat σ 1 0,
      by linear_combination -hd - mat h 1 1 * e00 + mat h 0 1 * e10⟩
  · exact Fin.ext (by omega)

theorem tqFam_perm : ∀ (N l q : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → q.Prime → ¬ q ∣ N * l → ∀ σ : SL(2, ℤ),
    IsDiam N l (q : ZMod N) σ → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' : Lev N l,
      tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  intro N l q _ _ _ hq hqN σ hσ γ
  choose f g hf using fun i => exists_rep hq hqN hσ ((tqFam_inDelta hσ i).mul γ.2)
  have hinj : Function.Injective f := by
    intro i k hik
    refine tqFam_inj hq σ ((g i : SL(2, ℤ)) * (g k : SL(2, ℤ))⁻¹) ?_
    have h1 : mat γ * mat (γ : SL(2, ℤ))⁻¹ = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : mat (g k : SL(2, ℤ))⁻¹ * mat (g k) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc tqFam q σ i = tqFam q σ i * mat γ * mat (γ : SL(2, ℤ))⁻¹ := by rw [mul_assoc, h1, mul_one]
      _ = mat (g i) * (mat (g k : SL(2, ℤ))⁻¹ * mat (g k)) * tqFam q σ (f k) * mat (γ : SL(2, ℤ))⁻¹ := by
          rw [hf i, hik, h2, mul_one]
      _ = mat (g i) * mat (g k : SL(2, ℤ))⁻¹ * (mat (g k) * tqFam q σ (f k)) * mat (γ : SL(2, ℤ))⁻¹ := by
          simp only [mul_assoc]
      _ = mat (g i) * mat (g k : SL(2, ℤ))⁻¹ * tqFam q σ k := by
          rw [← hf k, mul_assoc, mul_assoc (tqFam q σ k), h1, mul_one]
      _ = _ := by rw [← Matrix.SpecialLinearGroup.coe_mul]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => ⟨g i, hf i⟩⟩

end GlobalTheory.TqPerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjMulExpEqConjQExpansionCoeff
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Qc

lemma exp_eq_conj_qParam (T : ℝ) (n : ℕ) (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) =
      (starRingEnd ℂ) (1 / Function.Periodic.qParam T ((x : ℂ) + (y : ℂ) * Complex.I) ^ n) *
        (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, one_div, ← Complex.exp_neg, ← Complex.exp_conj,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, map_div₀, map_add (f := _), Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  push_cast
  linear_combination (4 * (Real.pi : ℂ) * n * y / T) * Complex.I_sq

theorem conj_integral (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ) (hT : 0 < T) (hy : 0 < y)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (hper : Function.Periodic (h ∘ ofComplex) T)
    (hbdd : IsBoundedAtImInfty h) :
    (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
        Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) =
      T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  have hc : ∀ f : ℝ → ℂ, (starRingEnd ℂ) (∫ u in (0 : ℝ)..T, f u) = ∫ u in (0 : ℝ)..T, (starRingEnd ℂ) (f u) := by
    intro f
    rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le, integral_conj]
  rw [qExpansion_coeff_eq_intervalIntegral hT hper hhol hbdd n hy, map_mul, hc]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [show (starRingEnd ℂ) (1 / (T : ℂ)) = 1 / (T : ℂ) by simp [Complex.conj_ofReal],
    ← mul_assoc, mul_one_div_cancel hT', one_mul, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  simp only [ofComplex_apply_of_im_pos him]
  rw [exp_eq_conj_qParam, map_mul, ← mul_assoc, mul_comm ((starRingEnd ℂ) (h _))]
  rfl

end GlobalTheory.HeckeFamilyMatrices.Qc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixInvEntriesBoundedStatement
section
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_inv_entries_of_bounded_entries : ∀ (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ), Continuous G → (∀ c, G c ≠ 0 → IsUnit c) → ∀ B ε : ℝ, 0 < ε → ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by
  first | exact @GlobalTheory.matrix_inv_entries_bounded | exact GlobalTheory.matrix_inv_entries_bounded | (intros; apply GlobalTheory.matrix_inv_entries_bounded <;> assumption)
end

