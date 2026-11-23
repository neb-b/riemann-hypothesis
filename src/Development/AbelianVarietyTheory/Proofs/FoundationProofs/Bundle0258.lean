module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateLevelFour
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.OddThetaTranslate

theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_nsmul (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (n : ℕ) (z : VC D N N') : coordB D T b k (n • z) = n * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, nsmul_eq_mul, mul_assoc, Finset.mul_sum]

theorem U_pullB (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ)
    (hP : ∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) =
      ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) (x z : VC D N N') :
    U D T x (pullB D T b g) z = ∏ k, U1 T.abelian₂ (coordB D T b k x) g (coordB D T b k z) := by
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  simp only [coordB_add]
  congr 2
  rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem half_not_mem {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  rw [AddSubgroup.mem_closure_pair]
  rintro ⟨m, n, hmn⟩
  have h0 := (LinearIndependent.pair_iff.1 h) (2 * (m : ℝ) - 1) (2 * (n : ℝ)) (by
    simp only [zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * hmn)
  have h1 : (2 * m - 1 : ℤ) = 0 := by exact_mod_cast h0.1
  omega

theorem exp_neg_pi_I_even (m : ℤ) (a : ℝ) (ha : a = 2 * m) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (a : ℂ)) = 1 := by
  rw [ha, ← Complex.exp_int_mul_two_pi_mul_I (-m)]
  congr 1
  push_cast
  ring

theorem translate_level_four : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → Differentiable ℂ (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∧ ∃ t : VC D N N', 2 • t ∈ LaB D (tor0 D cc δ) b ∧ U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) 0 ≠ 0 ∧ ∀ ω ∈ LaB D (tor0 D cc δ) b, U D (tor0 D cc δ) (4 • ω) (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) = U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) := by
  intro D hG cc δ hC N N' r b hb
  obtain ⟨w₁, w₂, hli, hΛ⟩ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
    obtain ⟨L, hL⟩ := _root_.GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hC
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul]
  obtain ⟨-, -, hP, hL, hbij⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  obtain ⟨⟨hd, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws (lamOf D cc δ) ⟨w₁, w₂, hli, hΛ⟩
  obtain ⟨-, -, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (LaB D (tor0 D cc δ) b)
    (Or.inl ⟨r, b, hb, rfl⟩)
  have hw : w₁ ∈ lamOf D cc δ := by rw [hΛ]; exact AddSubgroup.subset_closure (by simp)
  have hw2 : w₁ / 2 ∉ lamOf D cc δ := by rw [hΛ]; exact half_not_mem hli
  obtain ⟨t, ht⟩ := hbij.2 (fun _ => w₁ / 2)
  have ht' : ∀ k, coordB D (tor0 D cc δ) b k t = w₁ / 2 := fun k => congrFun ht k
  have h2t : 2 • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [coordB_nsmul, ht']
    have : ((2 : ℕ) : ℂ) * (w₁ / 2) = w₁ := by push_cast; ring
    rw [this]; exact hw
  refine ⟨?_, t, h2t, ?_, ?_⟩
  · have hc : ∀ k, Differentiable ℂ (coordB D (tor0 D cc δ) b k) := by
      intro k
      unfold coordB
      fun_prop
    unfold pullB
    fun_prop
  · simp only [U, zero_add, pullB, ht']
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ?_) (Complex.exp_ne_zero _)
    exact fun h => hw2 ((hz _).1 h)
  · intro ω hω
    have hfix : U D (tor0 D cc δ) (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) =
        pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)) := by
      funext z
      rw [U_pullB D _ b _ hP]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hk := (hL ω).1 hω k
      have h4 : coordB D (tor0 D cc δ) b k (4 • ω) ∈ lamOf D cc δ :=
        (hL _).1 (AddSubgroup.nsmul_mem _ hω 4) k
      have h2 : coordB D (tor0 D cc δ) b k (4 • ω) / 2 ∈ lamOf D cc δ := by
        have : coordB D (tor0 D cc δ) b k (4 • ω) / 2 =
            coordB D (tor0 D cc δ) b k ω + coordB D (tor0 D cc δ) b k ω := by
          rw [coordB_nsmul]; push_cast; ring
        rw [this]; exact add_mem hk hk
      have := hU _ h4 (coordB D (tor0 D cc δ) b k z)
      rw [if_pos h2, one_mul] at this
      exact this
    obtain ⟨m, hm⟩ := hint ω hω _ h2t
    have ha : (Hf D (tor0 D cc δ) (4 • ω) t).im = 2 * m := by
      rw [Hf_nsmul_right] at hm
      rw [Hf_nsmul_left, ← hm]
      simp
      ring
    have hb' : (Hf D (tor0 D cc δ) t (4 • ω)).im = 2 * ((-m : ℤ) : ℝ) := by
      rw [Hf_im_swap, ha]; push_cast; ring
    funext z
    have e := U_U D (tor0 D cc δ) t (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
    rw [hfix, exp_neg_pi_I_even _ _ hb', one_mul] at e
    rw [U_U, exp_neg_pi_I_even _ _ ha, one_mul, e, add_comm]

end GlobalTheory.OddThetaTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroup
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TrivSubgroup

variable {D : D7} {q : ℕ}

theorem zeroAt_zero : ZeroAt D q 0 := fun k =>
  ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem zeroAt_add {x y : AE D} (hx : ZeroAt D q x) (hy : ZeroAt D q y) : ZeroAt D q (x + y) := by
  intro k
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx k
  obtain ⟨m', hm', hmq', s', hs', h'⟩ := hy k
  refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hmq hmq', (m' : AE D) * s + (m : AE D) * s',
    add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
  push_cast
  linear_combination (m' : AE D) * h + (m : AE D) * h'

theorem zeroAt_mul_left (hq : q.Prime) (y : AE D) {x : AE D} (hx : ZeroAt D q x) :
    ZeroAt D q (y * x) := by
  intro k
  obtain ⟨n, hn, hy⟩ := GlobalTheory.AdelicApprox.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx (k + a)
  refine ⟨m * n', Nat.mul_pos hm (Nat.pos_of_ne_zero (by rintro rfl; simp at hn')),
    Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, _, mul_mem hs hy, ?_⟩
  push_cast
  linear_combination (n' : AE D) * y * h

def zeroIdeal (D : D7) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  add_mem' := zeroAt_add
  zero_mem' := zeroAt_zero
  smul_mem' := fun c _ hx => zeroAt_mul_left hq c hx

theorem entry_mul_mem {R : Type} [CommRing R] (I : Ideal R) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hB : ∀ i j, B i j ∈ I) (i j : Fin n) : (A * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hB k j)

theorem trivAt_subgroup : ∀ (D : D7) (n q : ℕ), q.Prime → TrivAt D q (1 : GL (Fin n) (AE D)) ∧
    (∀ g h : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q h → TrivAt D q (g * h)) ∧
    ∀ g : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q g⁻¹ := by
  intro D n q hq
  refine ⟨fun i j => ?_, fun g h hg hh i j => ?_, fun g hg i j => ?_⟩
  · rw [Units.val_one, sub_self]; exact zeroAt_zero
  · have e : ((g * h : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (g : Matrix (Fin n) (Fin n) (AE D)) * ((h : Matrix (Fin n) (Fin n) (AE D)) - 1) +
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact zeroAt_add (entry_mul_mem (zeroIdeal D hq) _ _ hh i j) (hg i j)
  · have e : ((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (-((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) *
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [neg_mul, mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [← Matrix.sub_apply, e]
    exact entry_mul_mem (zeroIdeal D hq) _ _ hg i j

end GlobalTheory.TrivSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrime
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.UnitaryTransvection

def tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  1 + μ • Matrix.vecMulVec w (fun i => D.host.conj (w i))

theorem tv_mulVec (D : D7) {n : ℕ} (μ : D.host.E) (w v : Fin n → D.host.E) :
    (tv D μ w).mulVec v = v + (μ * hE D v w) • w := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, hE,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cT_tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) :
    cT D (tv D μ w) = tv D (D.host.conj μ) w := by
  ext i j
  simp only [cT, tv, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_add, map_mul, conj_conj, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp only [if_true, map_one]; ring
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]; ring

theorem tv_unitary (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E)
    (h : μ + D.host.conj μ + μ * D.host.conj μ * hE D w w = 0) : tv D μ w * cT D (tv D μ w) = 1 := by
  rw [cT_tv]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, Matrix.one_mulVec,
    hE_add_left, hE_smul_left, add_assoc, ← add_smul]
  have : D.host.conj μ * hE D v w + μ * (hE D v w + D.host.conj μ * hE D v w * hE D w w) = 0 := by
    linear_combination hE D v w * h
  rw [this, zero_smul, add_zero]

theorem smul_mem_int {D : D7} {n : ℕ} (N : Lat D n) {c : D.host.E} (hc : IntE D c) {v : Fin n → D.host.E}
    (hv : v ∈ N) : c • v ∈ N := by
  obtain ⟨a, rfl⟩ := hc
  rw [algebraMap_smul]
  exact N.smul_mem a hv

theorem intE_nat (D : D7) (m : ℕ) : IntE D (m : D.host.E) := ⟨m, map_natCast _ m⟩

theorem gen {D : D7} {n : ℕ} (s : Matrix (Fin n) (Fin n) D.host.E) (c : D.host.E) (M N : Lat D n)
    (z : Fin n → D.host.E) (hM : ∀ y ∈ M, c • s.mulVec y ∈ N) (hz : c • s.mulVec z ∈ N) :
    ∀ v ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z}, c • s.mulVec v ∈ N := by
  intro v hv
  obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ht
  rw [Matrix.mulVec_add, smul_add]
  refine N.add_mem (hM y hy) ?_
  rw [← algebraMap_smul D.host.E a z, Matrix.mulVec_smul, smul_comm]
  exact smul_mem_int N ⟨a, rfl⟩ hz

theorem step {D : D7} {n : ℕ} (M N : Lat D n) (hMN : M ≤ N) (w y : Fin n → D.host.E) (μ : D.host.E) (m : ℕ)
    (hw : ((m : D.host.E) * μ) • w ∈ M) (hy : y ∈ N) (hi : IntE D (hE D y w)) :
    ((m * m : ℕ) : D.host.E) • (tv D μ w).mulVec y ∈ N := by
  rw [tv_mulVec, smul_add, smul_smul]
  refine N.add_mem (smul_mem_int N (intE_nat D _) hy) ?_
  have : ((m * m : ℕ) : D.host.E) * (μ * hE D y w) = ((m : D.host.E) * hE D y w) * ((m : D.host.E) * μ) := by
    push_cast; ring
  rw [this, mul_smul]
  exact smul_mem_int N (mul_mem (intE_nat D m) hi) (hMN hw)

theorem transvection : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  intro D n q P hP M b x lam m hbx hM hww hl hmq ⟨p, hp, hpl⟩ ⟨p', hp', hpl'⟩
  have hPw : ∀ a ∈ P, (a : D.host.E) • (b + x) ∈ M := by
    intro a ha
    have : a • (b + x) ∈ M := by
      rw [smul_add]; exact M.add_mem (hbx a ha).1 (hbx a ha).2
    rw [← algebraMap_smul D.host.E a (b + x)] at this
    exact this
  have hcl : (m : D.host.E) * D.host.conj lam = ((sgO D p : 𝓞 D.host.E) : D.host.E) := by
    rw [sgO_coe, ← hpl, map_mul, map_natCast]
  have h1 : ((m : D.host.E) * lam) • (b + x) ∈ M := by rw [hpl]; exact hPw p hp
  have h2 : ((m : D.host.E) * D.host.conj lam) • (b + x) ∈ M := by rw [hcl]; exact hPw _ (hP p hp)
  have h3 : ((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x) ∈ M := by rw [hpl']; exact hPw p' hp'
  have hmem : ∀ z : Fin n → D.host.E, z ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z} := fun z =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have hco : Nat.Coprime (m * m) q := Nat.Coprime.mul_left hmq hmq
  refine ⟨tv D lam (b + x), tv_unitary D lam _ hl, ⟨m * m, hco, ?_, ?_⟩, ⟨m * m, hco, ?_, ?_⟩⟩
  · exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h1 (hmem _) hww)
  · rw [cT_tv]
    exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h2 (hmem _) hww)
  · refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have : ((m * m : ℕ) : D.host.E) • (b + (lam * hE D b (b + x)) • (b + x)) =
        (m : D.host.E) • (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • x := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      push_cast; ring
    rw [this]
    exact Submodule.sub_mem _ (smul_mem_int _ (intE_nat D m) (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem x))
  · rw [cT_tv]
    refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have hx : hE D x (b + x) = hE D (b + x) (b + x) - hE D b (b + x) := by
      rw [hE_add_left]; ring
    have : ((m * m : ℕ) : D.host.E) • (x + (D.host.conj lam * hE D x (b + x)) • (b + x)) =
        ((m : D.host.E) + ((m : D.host.E) * D.host.conj lam) * hE D (b + x) (b + x)) •
          (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • b := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [hx]
      push_cast
      linear_combination (-((m : D.host.E) * m * hE D b (b + x) * (b i + x i))) * hl
    rw [this]
    refine Submodule.sub_mem _ (smul_mem_int _ ?_ (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem b))
    rw [hcl]
    exact add_mem (intE_nat D m) (mul_mem ⟨sgO D p, rfl⟩ hww)

end GlobalTheory.UnitaryTransvection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorConjHeisenbergMovedLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.WeilEquiv

theorem exists_common_den {R : Type} [CommRing R] (O : Subring R)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : R) * A i j ∈ O := by
  choose f hf hfO using hO
  refine ⟨∏ p : Fin a × Fin b, f (A p.1 p.2), Finset.prod_pos fun p _ => hf _, fun i j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
  exact O.mul_mem (natCast_mem O _) (hfO _)

theorem exists_close {R E : Type} [CommRing R] (ι : E → R) (O : Subring R) (I : AddSubgroup R)
    (hA : ∀ (y : R) (m : ℕ), 0 < m → ∃ e : E, ∃ t ∈ I, ι e - y = (m : R) * t)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) (hI : ∀ s ∈ O, ∀ t ∈ I, s * t ∈ I)
    {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (Q : Matrix (Fin b) (Fin b) R)
    (hX : ∀ i j, (P * X * Q) i j ∈ I) (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) E, (∀ i j, ∃ y ∈ I, (z.map ι - X) i j = (m : R) * y) ∧
      ∀ i j, (P * z.map ι * Q) i j ∈ I := by
  obtain ⟨n, hn, hP⟩ := exists_common_den O hO P
  obtain ⟨n', hn', hQ⟩ := exists_common_den O hO Q
  choose e t ht he using fun i j => hA (X i j) (m * n * n') (by positivity)
  refine ⟨Matrix.of e, fun i j => ⟨((n * n' : ℕ) : R) * t i j, hI _ (natCast_mem O _) _ (ht i j), ?_⟩, fun i j => ?_⟩
  · simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, he]
    push_cast; ring
  · have h1 : (Matrix.of e).map ι = X + Matrix.of fun i j => ((m * n * n' : ℕ) : R) * t i j := by
      ext i j
      simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, ← he]
      ring
    rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    refine I.add_mem (hX i j) ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    refine sum_mem fun l _ => sum_mem fun r _ => ?_
    have : P i r * (((m * n * n' : ℕ) : R) * t r l) * Q l j =
        ((m : R) * ((n : R) * P i r) * ((n' : R) * Q l j)) * t r l := by
      push_cast; ring
    rw [this]
    exact hI _ (O.mul_mem (O.mul_mem (natCast_mem O _) (hP i r)) (hQ l j)) _ (ht r l)

theorem om_wd_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (k : GL (Fin N) (AE D)) L₁ → Moves D (k' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ x' ∈ La D (tor0 D cc δ) L₂ L₂', W.Om h h' (Wd D (tor0 D cc δ) x F) = Wd D (tor0 D cc δ) x' (W.Om h h' F) := by
  intro D hD cc δ hcc N N' e0 W h k h' k' L₁ L₂ L₁' L₂' h1 h1' h2 h2' x hx F hF
  obtain ⟨z, rfl, hz⟩ := _root_.GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' k k' L₁ L₁' h1 h1' x hx
  obtain ⟨m, hm, hl⟩ := W.lift h h' z F hF
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  obtain ⟨z', hc, hz'⟩ := exists_close (inc D) (OhE D) (IhE D cc) hA hO hI
    (((h' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (((h : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
    (((((h' * k' : GA D N') : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)))
    (((h * k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    (by
      intro i j
      refine Set.mem_of_eq_of_mem (congrFun (congrFun ?_ i) j) (hz i j)
      simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((h' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)),
        ← Matrix.mul_assoc (((h : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)),
        Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.one_mul]) m hm
  exact ⟨_, _root_.GlobalTheory.NormSum.pt_mem_La_of_adelic D hD cc δ hcc N N' (h * k) (h' * k') L₂ L₂' h2 h2' z' hz', hl z' hc⟩

end GlobalTheory.WeilEquiv
end

