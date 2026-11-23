module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelations
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0184

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.Glue.DlPow


open scoped MatrixGroups in
theorem _root_.GlobalTheory.Glue.DlPow.isAlgebraic_of_tower {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    Algebra.IsAlgebraic ℚ Ω := by
  refine ⟨fun c => ?_⟩
  obtain ⟨D, hD, hint⟩ := X.bdd (algebraMap Ω X.K c)
  obtain ⟨k, hk⟩ := hint 0
  have hc : (algebraMap Ω (HahnSeries ℚ Ω) c).coeff 0 = c := by
    rw [HahnSeries.algebraMap_apply']
    simp
  rw [AlgHom.commutes, hc] at hk
  have h1 : IsAlgebraic ℚ ((D : Ω) ^ k * c) := (hk.tower_top (A := ℚ)).isAlgebraic
  have hD' : ((D : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD.ne')
  have hc' : c = algebraMap ℚ Ω (((D : ℚ) ^ k)⁻¹) * ((D : Ω) ^ k * c) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℚ Ω), ← map_pow, ← map_mul, inv_mul_cancel₀ hD',
      map_one, one_mul]
  rw [hc']
  exact (isAlgebraic_algebraMap _).mul h1

open scoped MatrixGroups in
private lemma prim_pow_succ {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {P : HahnSeries ℚ Ω} (hP : _root_.GlobalTheory.Glue.Prim A P) (k : ℕ) :
    _root_.GlobalTheory.Glue.Prim A (P ^ (k + 1)) := by
  induction k with
  | zero => rwa [zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ]
    exact _root_.GlobalTheory.Glue.Prim.mul A _ _ ih hP

open scoped MatrixGroups in
private lemma theta_pow_succ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ)
    (P : HahnSeries ℚ Ω) (k : ℕ) :
    _root_.GlobalTheory.Glue.theta s (P ^ (k + 1)) =
      HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta s P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, (_root_.GlobalTheory.Glue.theta_leibniz_add_const s _ _).1, ih]
    push_cast
    simp only [map_add (f := _), map_natCast, map_one]
    ring

open scoped MatrixGroups in
private lemma theta_one_coeff_mem_of_integral_den_one {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) {P : HahnSeries ℚ Ω} (hP : ∀ r, P.coeff r ∈ A)
    (hden : ∀ r, P.coeff r ≠ 0 → r.den = 1) (r : ℚ) :
    (_root_.GlobalTheory.Glue.theta 1 P).coeff r ∈ A := by
  show algebraMap ℚ Ω (1 * r) * P.coeff r ∈ A
  by_cases h : P.coeff r = 0
  · rw [h, mul_zero]
    exact zero_mem A
  · refine mul_mem ?_ (hP r)
    rw [one_mul, ← Rat.coe_int_num_of_den_eq_one (hden r h), map_intCast]
    exact intCast_mem A _

open scoped MatrixGroups in
private lemma hahnSeries_coeff_mul_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) :
    (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hx _) (hy _)

open scoped MatrixGroups in
private lemma hahnSeries_coeff_pow_mem_valuationSubring {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (k : ℕ) (r : ℚ) : (x ^ k).coeff r ∈ A := by
  induction k generalizing r with
  | zero =>
    rw [pow_zero, HahnSeries.coeff_one]
    split_ifs
    · exact one_mem A
    · exact zero_mem A
  | succ k ih =>
    rw [pow_succ]
    exact hahnSeries_coeff_mul_mem_valuationSubring A ih hx r


open scoped MatrixGroups in
theorem _root_.GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits →
    ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 →
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) u = u →
      ∀ φ φ' : HahnSeries ℚ Ω, _root_.GlobalTheory.Glue.IsDl X A l n 1 f φ →
        _root_.GlobalTheory.Glue.IsDl X A l n 1 (f * u ^ (l ^ n)) φ' →
          ∀ r, _root_.GlobalTheory.Glue.CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A l _ hl n f u hf hu hT φ φ' hφ hφ' r
  have hj : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g _root_.GlobalTheory.KZ.Hs ∧
      X.an X.jK = ↑g := by
    obtain ⟨g, h1, h2⟩ := X.j_hol
    exact ⟨g, h2, h1⟩
  have hden : ∀ x : X.K,
      X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) x = x →
        ∀ s, (X.exp x).coeff s ≠ 0 → s.den = 1 := by
    intro x hx s hs
    have hmem : x ∈ _root_.GlobalTheory.Glue.KT X 1 := by
      rw [_root_.GlobalTheory.Glue.KT.mem_def, pow_one]
      exact hx
    simpa using (_root_.GlobalTheory.Glue.KTExp.mem_KT_iff ε X 1 one_pos x).1 hmem s hs
  have hu0 : _root_.GlobalTheory.Glue.IsDl X A l n 1 (u ^ (l ^ n)) 0 := by
    obtain ⟨a, b, κ, S, hκ, hab, hPa, hPb, hb, -⟩ :=
      _root_.GlobalTheory.exists_prim_frac_level_one ε X hj l A hl u hu
    have hbT := hb ModularGroup.T
    have haT : X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T) a = a := by
      have h1 := congrArg (X.sl (_root_.GlobalTheory.KZ.ofSL ModularGroup.T)) hab
      rw [map_mul, map_mul, hT, hbT, AlgEquiv.commutes, hab] at h1
      exact (mul_left_cancel₀ ((map_ne_zero _).2 hκ) h1).symm
    obtain ⟨k, hk⟩ : ∃ k, l ^ n = k + 1 :=
      ⟨l ^ n - 1, (Nat.succ_pred_eq_of_pos (pow_pos (Fact.out : l.Prime).pos n)).symm⟩
    have hl' : (l : Ω) ^ n = ((k + 1 : ℕ) : Ω) := by rw [← Nat.cast_pow, hk]
    have hPaA := hPa.1
    have hPbA := hPb.1
    unfold _root_.GlobalTheory.Glue.IsDl
    refine ⟨fun s => by simpa using zero_mem A, a ^ (l ^ n), b ^ (l ^ n), κ ^ (l ^ n),
      pow_ne_zero _ hκ, by rw [map_pow, ← mul_pow, ← mul_pow, hab], ?_, ?_, fun s => ?_⟩
    · rw [map_pow, hk]
      exact prim_pow_succ hPa k
    · rw [map_pow, hk]
      exact prim_pow_succ hPb k
    · rw [map_pow, map_pow, hk, theta_pow_succ, theta_pow_succ]
      set P := X.exp a
      set Q := X.exp b
      set W := P ^ k * Q ^ k *
        (_root_.GlobalTheory.Glue.theta 1 P * Q - P * _root_.GlobalTheory.Glue.theta 1 Q)
      have hW : W.coeff s ∈ A := by
        have hθP := theta_one_coeff_mem_of_integral_den_one A hPaA (hden a haT)
        have hθQ := theta_one_coeff_mem_of_integral_den_one A hPbA (hden b hbT)
        refine hahnSeries_coeff_mul_mem_valuationSubring A
          (hahnSeries_coeff_mul_mem_valuationSubring A (hahnSeries_coeff_pow_mem_valuationSubring A hPaA k)
            (hahnSeries_coeff_pow_mem_valuationSubring A hPbA k)) (fun t => ?_) s
        rw [HahnSeries.coeff_sub]
        exact sub_mem (hahnSeries_coeff_mul_mem_valuationSubring A hθP hPbA t)
          (hahnSeries_coeff_mul_mem_valuationSubring A hPaA hθQ t)
      have hexp : HahnSeries.C ((k + 1 : ℕ) : Ω) * P ^ k * _root_.GlobalTheory.Glue.theta 1 P *
          Q ^ (k + 1) -
          P ^ (k + 1) * (HahnSeries.C ((k + 1 : ℕ) : Ω) * Q ^ k * _root_.GlobalTheory.Glue.theta 1 Q) =
          HahnSeries.C ((k + 1 : ℕ) : Ω) * W := by
        simp only [W]
        ring
      unfold _root_.GlobalTheory.Glue.CgA
      refine ⟨-W.coeff s, neg_mem hW, ?_⟩
      rw [hexp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, zero_mul, zero_mul,
        HahnSeries.coeff_zero, hl', smul_eq_mul]
      ring
  have h := (_root_.GlobalTheory.Glue.isDl_calc ε X hj l A hl n 1 f (u ^ (l ^ n)) φ 0).1
    hφ hu0
  simpa using _root_.GlobalTheory.Glue.isDl_unique ε X hj l A hl n 1 _ _ _ h hφ' r

end GlobalTheory.Glue.DlPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinValuesAtZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RankinZero

lemma ch_bdd {M : ℕ} (ξ : DirichletCharacter ℂ M) : ∃ C : ℝ, ∀ x, ‖ch ξ x‖ ≤ C :=
  ⟨1, fun x => DirichletCharacter.norm_le_one ξ _⟩

lemma lseries_Vo (l : ℕ) (hl : 0 < l) (t : ℂ) (h b : ℕ → ℂ) (hb : ∀ n, n ≠ 0 → b (l * n) = t * b n)
    (W : ℂ) :
    LSeries (fun n => conj (Vo l h n) * b n) W = t / (l : ℂ) ^ W * LSeries (fun n => conj (h n) * b n) W := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun a c hac => Nat.eq_of_mul_eq_mul_left hl hac
  have hsupp : Function.support (LSeries.term (fun n => conj (Vo l h n) * b n) W) ⊆ Set.range (fun m : ℕ => l * m) := by
    intro n hn
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      exact ⟨m, rfl⟩
    · exfalso
      apply hn
      simp [LSeries.term, Vo, hd]
  unfold LSeries
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  congr 1
  funext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [LSeries.term]
  · have hm0 : m ≠ 0 := hm.ne'
    have hlm : l * m ≠ 0 := Nat.mul_ne_zero hl.ne' hm0
    rw [LSeries.term_of_ne_zero hlm, LSeries.term_of_ne_zero hm0]
    have hV : Vo l h (l * m) = h m := by
      simp [Vo, Nat.mul_div_cancel_left m hl]
    rw [hV, hb m hm0]
    push_cast
    rw [natCast_mul_natCast_cpow]
    ring

end GlobalTheory.EisM.RankinZero

namespace GlobalTheory.EisM

theorem rankin_values_at_zero : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (c₀ : ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ g → Wt (N * l) ρ → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → φ ≠ 1 → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → ∃ P : ℂ, P ≠ 0 ∧ pet (2 * e + 1) ρ (qs fun n => conj (g n)) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = P ∧ pet (2 * e + 1) ρ (qs (Vo l fun n => conj (g n))) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = θ l / (l : ℂ) ^ (2 * e) * P := by
  intro e N l χ θ ψ φ g ρ c₀ he hN hl hlN hg hρ hφ hφ1 hb
  haveI : Fact l.Prime := ⟨hl⟩
  have hLpos : 0 < N * l := Nat.mul_pos hN hl.pos
  have hNL : N ∣ N * l := dvd_mul_right N l
  set b := eis e c₀ (ch ψ) (ch θ) with hbdef
  set h : ℕ → ℂ := fun n => conj (g n) with hhdef
  set Φ := latF (N * l) (fun _ => 1) φ with hΦdef
  have hCFg : CF (2 * e + 1) N (ch χ) g := hg.cf
  have hCFh0 : CF (2 * e + 1) N (ch χ⁻¹) h := (_root_.GlobalTheory.EisM.ConjForm.conj_form (2 * e + 1) N χ g).1 hCFg
  have hCFh : CF (2 * e + 1) (N * l) (ch χ⁻¹) h :=
    (_root_.GlobalTheory.EisM.mf_linear (2 * e + 1) N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hNL hCFh0
  have hCFVh : CF (2 * e + 1) (N * l) (ch χ⁻¹) (Vo l h) :=
    (_root_.GlobalTheory.Vo_level (2 * e + 1) N l (ch χ⁻¹) h hl.pos).2 hCFh0
  obtain ⟨hPolyb, hbbd, -⟩ := _root_.GlobalTheory.EisM.eis_qseries e c₀ (ch ψ) (ch θ) (RankinZero.ch_bdd ψ) (RankinZero.ch_bdd θ)
  have hΦbd : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
    refine ⟨1, fun x => ?_⟩
    simp only [hΦdef, latF]
    split_ifs
    · simpa using DirichletCharacter.norm_le_one φ _
    · simp

  have hmult : ∀ d : ℤ, IsCoprime d ((N * l : ℕ) : ℤ) →
      (fun d => ch ψ d * ch θ d) d = ch φ d * ch χ⁻¹ d := by
    intro d hd
    have hd' : IsCoprime d ((N : ℤ) * l) := by push_cast at hd; exact hd
    have hdN : IsCoprime d (N : ℤ) := hd'.of_mul_right_left
    obtain ⟨u, v, huv⟩ := hdN
    have hunit : IsUnit (d : ZMod N) := by
      have h1 := congrArg (Int.cast : ℤ → ZMod N) huv
      push_cast at h1
      rw [ZMod.natCast_self, mul_zero, add_zero] at h1
      exact ⟨⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    have hχ : χ (d : ZMod N) ≠ 0 := (hunit.map χ).ne_zero
    show ch ψ d * ch θ d = ch φ d * ch χ⁻¹ d
    rw [hφ d]
    simp only [ch, MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    field_simp

  have hLφ : (fun n : ℕ => φ n) = fun n : ℕ => χ n * ψ n * θ n := by
    funext n
    have := hφ (n : ℤ)
    simp only [ch, Int.cast_natCast, MulChar.mul_apply] at this
    rw [this]
    ring
  have hψmul : ∀ m n : ℕ, ψ ((m * n : ℕ) : ZMod l) = ψ (m : ZMod l) * ψ (n : ZMod l) := by
    intro m n; push_cast; exact map_mul ψ _ _
  have hθmul : ∀ m n : ℕ, θ ((m * n : ℕ) : ZMod N) = θ (m : ZMod N) * θ (n : ZMod N) := by
    intro m n; push_cast; exact map_mul θ _ _
  have hnorm : ∀ n : ℕ, ‖χ (n : ZMod N)‖ ≤ 1 ∧ ‖ψ (n : ZMod l)‖ ≤ 1 ∧ ‖θ (n : ZMod N)‖ ≤ 1 :=
    fun n => ⟨DirichletCharacter.norm_le_one χ _, DirichletCharacter.norm_le_one ψ _,
      DirichletCharacter.norm_le_one θ _⟩
  have hhecke : ∀ m n : ℕ, 0 < m → 0 < n → g m * g n =
      ∑ δ ∈ (Nat.gcd m n).divisors, χ (δ : ZMod N) * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2) := by
    have := (_root_.GlobalTheory.EisM.hecke_relations (2 * e + 1) N χ g (by omega) hN hg).2.2
    simpa using this
  have hsum : ∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t) :=
    fun t ht => (_root_.GlobalTheory.rankin_mean_square (2 * e + 1) N (ch χ) g (by omega) hCFg).2.2.1 t ht
  have hbform : ∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal,
      ψ (p.1 : ZMod l) * (p.1 : ℂ) ^ (e - 1) * θ (p.2 : ZMod N) := by
    intro n hn
    simp [hbdef, eis, ch, hn]

  have hbl : ∀ n, n ≠ 0 → b (l * n) = θ (l : ZMod N) * b n := by
    have hψ0 : ∀ x : ℤ, (l : ℤ) ∣ x → ch ψ x = 0 := by
      intro x hx
      simp only [ch]
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd x l).mpr hx]
      exact MulChar.map_zero ψ
    have hθl : ∀ y : ℤ, ch θ ((l : ℤ) * y) = ch θ (l : ℤ) * ch θ y := by
      intro y; simp only [ch]; push_cast; exact map_mul θ _ _
    intro n hn
    have := (_root_.GlobalTheory.eis_U_V e l c₀ (ch θ (l : ℤ)) (ch ψ) (ch θ) hl).1 hψ0 hθl n hn
    simpa [ch] using this

  have hI : ∀ s : ℝ, 0 < s →
      pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) =
        ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) *
          (LSeries (fun n => ψ (n : ZMod l) * g n) ((e + 1 : ℝ) + s : ℝ) *
            LSeries (fun n => θ (n : ZMod N) * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
    intro s hs
    rw [_root_.GlobalTheory.EisM.rankin_unfold e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h b s he hs hLpos hNL hρ hφ1 hCFh hb hmult hbbd]
    have hd := _root_.GlobalTheory.EisM.rankin_dirichlet_identity e (fun n => χ (n : ZMod N)) (fun n => ψ (n : ZMod l)) (fun n => θ (n : ZMod N)) g s he hs
      hψmul hθmul hnorm hhecke hsum b hbform
    have hgb : (fun n => conj (h n) * b n) = fun n => g n * b n := by
      funext n; simp [hhdef]
    rw [hgb, hLφ, ← hd.2]
    ring

  have hI' : ∀ s : ℝ, 0 < s →
      pet (2 * e + 1) ρ (qs (Vo l h)) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) =
        θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) *
          pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) := by
    intro s hs
    rw [_root_.GlobalTheory.EisM.rankin_unfold e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ (Vo l h) b s he hs hLpos hNL hρ hφ1 hCFVh hb hmult hbbd,
      _root_.GlobalTheory.EisM.rankin_unfold e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h b s he hs hLpos hNL hρ hφ1 hCFh hb hmult hbbd,
      RankinZero.lseries_Vo l hl.pos _ h b hbl]
    ring

  have hlim := _root_.GlobalTheory.EisM.rankin_tendsto (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ h b (by omega) (by omega) hLpos hLpos hNL
    hρ hCFh hPolyb hΦbd
  have hlim' := _root_.GlobalTheory.EisM.rankin_tendsto (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ (Vo l h) b (by omega) (by omega) hLpos hLpos
    hNL hρ hCFVh hPolyb hΦbd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  obtain ⟨-, v₁, hv₁, hL₁⟩ := _root_.GlobalTheory.EisM.twisted_lvalue_ne_zero_edge (2 * e + 1) N l χ ψ g ((e : ℝ) + 1) (odd_two_mul_add_one e) hN hl.pos hg
    (by push_cast; linarith)
  obtain ⟨-, v₂, hv₂, hL₂⟩ := _root_.GlobalTheory.EisM.twisted_lvalue_ne_zero_edge (2 * e + 1) N N χ θ g (2 * (e : ℝ)) (odd_two_mul_add_one e) hN hN hg
    (by push_cast; linarith)
  have hΓ : Tendsto (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) 0 := by
      apply Complex.continuous_ofReal.continuousAt.comp
      apply ContinuousAt.div
      · apply ContinuousAt.comp (g := Real.Gamma) _ (continuous_const.add continuous_id).continuousAt
        refine (Real.differentiableAt_Gamma fun m hm => ?_).continuousAt
        have := m.cast_nonneg (α := ℝ)
        have hm' : 2 * (e : ℝ) + 0 = -(m : ℝ) := hm
        linarith
      · exact (Real.continuousAt_const_rpow (by positivity)).comp (continuous_const.add continuous_id).continuousAt
      · positivity
    simpa using hc.tendsto
  set P : ℂ := ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ) * (v₁ * v₂) with hPdef
  have hprod : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h)
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P) := by
    refine (hΓ.mul (hL₁.mul hL₂)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hI s hs).symm
  have hP0 := tendsto_nhds_unique hlim hprod
  have hPne : P ≠ 0 := by
    have hΓpos : 0 < Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) :=
      div_pos (Real.Gamma_pos_of_pos (by linarith)) (by positivity)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hΓpos.ne') (mul_ne_zero hv₁ hv₂)
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hcp : Tendsto (fun s : ℝ => θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝[>] 0)
      (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).const_cpow (Or.inl hl0)
    have h0 : (l : ℂ) ^ (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = (l : ℂ) ^ (2 * e) := by
      rw [show (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = ((2 * e : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
    have h1 : Tendsto (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝 0) (𝓝 ((l : ℂ) ^ (2 * e))) := by
      rw [← h0]; exact hc.tendsto 0
    exact tendsto_const_nhds.div h1 (pow_ne_zero _ hl0)
  have hlimP : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h)
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P) := hprod
  have hprod' : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs (Vo l h))
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e) * P)) := by
    refine (hcp.mul hlimP).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hI' s hs).symm
  exact ⟨P, hPne, hP0, tendsto_nhds_unique hlim' hprod'⟩

end GlobalTheory.EisM
end

