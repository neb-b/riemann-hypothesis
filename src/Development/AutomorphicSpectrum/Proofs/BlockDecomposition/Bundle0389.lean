module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
public import Formalism.GelfandTransference.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieAction

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfIsIntegralMulOfSmall
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.SmallIntegral

theorem eq_zero_of_isIntegral_mul_of_small :
    ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (y : E), 0 < d →
      IsIntegral ℤ ((d : E) * y) → ∀ ε : ℝ, (∀ φ : E →+* ℂ, ‖φ y‖ ≤ ε) →
      ((d : ℝ) * ε) ^ Module.finrank ℚ E < 1 → y = 0 := by
  intro E _ _ d y hd hint ε hε hlt
  by_contra hy
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hz : (d : E) * y ≠ 0 := mul_ne_zero hd' hy

  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm ℚ hint : IsIntegral ℤ (Algebra.norm ℚ ((d : E) * y)))
  have hnorm0 : Algebra.norm ℚ ((d : E) * y) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hz
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hnorm0 (by simpa using hn.symm)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0

  have hprod : ((Algebra.norm ℚ ((d : E) * y) : ℚ) : ℂ) = ∏ φ : E →+* ℂ, φ ((d : E) * y) := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ ((d : E) * y)
    have h2 : ∏ σ : E →ₐ[ℚ] ℂ, σ ((d : E) * y) = ∏ φ : E →+* ℂ, φ ((d : E) * y) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
    rw [← h2, ← h]
    simp
  have hnC : ((n : ℂ)) = ∏ φ : E →+* ℂ, φ ((d : E) * y) := by
    rw [← hprod, ← hn]
    simp
  have habs : |(n : ℝ)| = ∏ φ : E →+* ℂ, ‖φ ((d : E) * y)‖ := by
    have := congrArg norm hnC
    rw [norm_prod] at this
    simpa using this
  have hbound : ∏ φ : E →+* ℂ, ‖φ ((d : E) * y)‖ ≤ ((d : ℝ) * ε) ^ Module.finrank ℚ E := by
    have hle : ∀ φ ∈ (Finset.univ : Finset (E →+* ℂ)), ‖φ ((d : E) * y)‖ ≤ (d : ℝ) * ε := by
      intro φ _
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hε φ) (Nat.cast_nonneg d)
    calc ∏ φ : E →+* ℂ, ‖φ ((d : E) * y)‖ ≤ ∏ _φ : E →+* ℂ, (d : ℝ) * ε :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hle
      _ = ((d : ℝ) * ε) ^ Module.finrank ℚ E := by
          rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card E ℂ]
  linarith

end GlobalTheory.CompanionTheory.SmallIntegral
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimir
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.NormIneq

variable {n : ℕ}

theorem casC_eq_sum (σ : Fin n → ℂ) :
    casC σ = ∑ a, σ a ^ 2 + ∑ a, σ a * ((n : ℂ) - 1 - 2 * ((a : ℕ) : ℂ)) :=
  _root_.UpperTheory.Reformulated.B.CasimirElement.main σ

theorem sum_wt_mul (m : Fin n × Fin n →₀ ℕ) (f : Fin n → ℤ) :
    ∑ k, wt m k * f k = m.sum fun a c => (c : ℤ) * (f a.1 - f a.2) := by
  simp only [wt, Finsupp.sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [rootAt, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lt_of_step {f : Fin n → ℤ} (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i) :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d + 1 → f j < f i := by
  intro d
  induction d with
  | zero => intro i j hij; exact h i j (by simpa using hij)
  | succ d ih =>
    intro i j hij
    have hk : (i : ℕ) + d + 1 < n := by have := j.2; omega
    have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
    have h2 := h ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
    exact h2.trans h1

theorem eq_zero_of_casC_eq {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (hm : LowExp m)
    (hp : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ))
    (hc : casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n)) : m = 0 := by
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℤ, ∀ k, f k = 2 * ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) + wt m k :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i := by
    intro i j hij
    obtain ⟨p, hp⟩ := hp i j hij
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
    have hij' : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1 := by exact_mod_cast hij
    rw [hf, hf, hij']
    linarith
  have hneg : ∑ k, wt m k * f k < 0 := by
    rw [sum_wt_mul]
    refine Finset.sum_neg (fun a ha => ?_) (Finsupp.support_nonempty_iff.2 hne)
    have hlow : (a.2 : ℕ) < a.1 := hm a ha
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (a.1 : ℕ) = a.2 + d + 1 := ⟨(a.1 : ℕ) - a.2 - 1, by omega⟩
    have hlt := lt_of_step hstep d a.2 a.1 hd
    have hpos : (0 : ℤ) < (m a : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ha)
    exact mul_neg_of_pos_of_neg hpos (by linarith)
  have key : ((∑ k, wt m k * f k : ℤ) : ℂ) =
      casC (fun k => rhoVec n k + (wt m k : ℂ)) - casC (rhoVec n) := by
    rw [casC_eq_sum, casC_eq_sum, add_sub_add_comm, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    push_cast
    simp only [rhoVec]
    ring
  rw [hc, sub_self] at key
  have : ∑ k, wt m k * f k = 0 := by exact_mod_cast key
  omega

end GlobalTheory.CompanionTheory.PresRho.NormIneq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuOfDifferentiableAt
section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.RmHol.GelCoef

variable {n : ℕ}

theorem Eu_of_differentiableAt {f : Mat n → ℂ} {z : Mat n} (hf : DifferentiableAt ℂ f z) (a b : Fin n) :
    Eu true a b f z = fderiv ℂ f z (z * Matrix.single a b 1) ∧ Eu false a b f z = 0 := by
  have hR : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
    (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  have hI : z * Matrix.single a b Complex.I = Complex.I • (z * Matrix.single a b (1 : ℂ)) := by
    rw [← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, if_true, hR,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination (-(1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, hR, Bool.false_eq_true, if_false,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination ((1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII

theorem Eu_congr_germ {f h : Mat n → ℂ} {g : Mat n} (e : f =ᶠ[𝓝 g] h) (s : Bool) (a b : Fin n) :
    Eu s a b f g = Eu s a b h g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, e.fderiv_eq]

end GlobalTheory.CompanionTheory.RmHol.GelCoef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdFamL
section
open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult

variable {n : ℕ}

def AdFamL (lev : Fin n → ℕ) {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n))
    (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ c d, lev c = lev d → ∀ i, (X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d) =
      ∑ j, M c d j i • evB lev X1 X2 (w j)

theorem ad_letter {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {X1 X2 : Fin n → Fin n → Module.End ℂ W}
    (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (s : Bool) (a b : Fin n) :
    (X1 c d + X2 c d) * evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) -
        evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) * (X1 c d + X2 c d) =
      (if d = a then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, c, b)) else 0) -
        (if b = c then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, d)) else 0) := by
  obtain ⟨h1, h2, h3⟩ := hX
  simp only [evB, FreeAlgebra.lift_ι_apply]
  by_cases hab : lev a = lev b
  · have e1 : d = a → lev c = lev b := fun h => by rw [hcd, h, hab]
    have e2 : b = c → lev a = lev d := fun h => by rw [hab, h, hcd]
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) =
        if d = a then (if s = true then X1 c b else X2 c b) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e1 h) h'
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) =
        if b = c then (if s = true then X1 a d else X2 a d) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e2 h) h'
    rw [k1, k2, if_pos hab]
    cases s
    · have e := h2 c d a b hcd hab
      have k := (h3 c d a b hcd hab).eq
      simp only [Bool.false_eq_true, if_false, add_mul, mul_add]
      rw [k, ← e]
      abel
    · have e := h1 c d a b hcd hab
      have k := (h3 a b c d hab hcd).eq
      simp only [if_true, add_mul, mul_add]
      rw [k, ← e]
      abel
  · have e1 : d = a → ¬ lev c = lev b := fun h => by rw [hcd, h]; exact hab
    have e2 : b = c → ¬ lev a = lev d := fun h => by rw [← hcd, ← h]; exact hab
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e1 h)
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e2 h)
    rw [k1, k2, if_neg hab]
    simp

theorem exists_adFamL (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFamL lev w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro W _ _ X1 X2 _ c d _ i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Bool × Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.2.1 ∧ j = (i.1, c, i.2.2) then 1 else 0) -
        (if i.2.2 = c ∧ j = (i.1, i.2.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨s, i1, i2⟩ ⟨t, j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h2.symm, h3.symm, h1⟩
    · rintro W _ _ X1 X2 hX c d hcd ⟨s, a, b⟩
      have h := ad_letter hX hcd s a b
      simp only [Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a <;> simp [h1]
      · by_cases h1 : b = c <;> simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro W _ _ X1 X2 hX c d hcd ⟨i, i'⟩
      have e1 := h2 W X1 X2 hX c d hcd i
      have e2 := h2' W X1 X2 hX c d hcd i'
      have : (X1 c d + X2 c d) * evB lev X1 X2 (w i * w' i') - evB lev X1 X2 (w i * w' i') * (X1 c d + X2 c d) =
          ((X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d)) * evB lev X1 X2 (w' i') +
            evB lev X1 X2 (w i) *
              ((X1 c d + X2 c d) * evB lev X1 X2 (w' i') - evB lev X1 X2 (w' i') * (X1 c d + X2 c d)) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro W _ _ X1 X2 hX c d hcd (i | i)
      · simp [Fintype.sum_sum_type, h2 W X1 X2 hX c d hcd]
      · simp [Fintype.sum_sum_type, h2' W X1 X2 hX c d hcd]
    · simp [Fintype.sum_sum_type]

theorem AdFamL.comm {lev : Fin n → ℕ} {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFamL lev w M) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (t : ι → ℂ) :
    (X1 c d + X2 c d) * evB lev X1 X2 (∑ i, t i • w i) - evB lev X1 X2 (∑ i, t i • w i) * (X1 c d + X2 c d) =
      evB lev X1 X2 (∑ j, (M c d *ᵥ t) j • w j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, h.2 W X1 X2 hX c d hcd, Finset.smul_sum, Matrix.mulVec, dotProduct,
    Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem invL : InvL := by
  classical
  intro n lev V _ _ X1 X2 L a hX hL ha
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFamL lev a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, lev c = lev d → ∀ x ∈ N, D c d x ∈ N := by
    intro c d hcd x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]
  have ht : ∀ c d, lev c = lev d → D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d hcd
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, lev c = lev d → D c d t' = 0 := by
    intro c d hcd
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d hcd) (hDN c d hcd k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ Y1 Y2 hY c d hcd
    have := hM.comm hY hcd t'.ofLp
    rw [← hD, h0 c d hcd] at this
    have h2 : evB lev Y1 Y2 (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, this, zero_add]

end GlobalTheory.CompanionTheory.PairMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlocksOfUpper
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaBlock

theorem exists_blocks_of_upper {K : Type} [Field K] {n a b : ℕ} (h : a + b = n) (p : GL (Fin n) K)
    (hp : p.1.BlockTriangular id) :
    ∃ (m₁ : GL (Fin a) K) (m₂ : GL (Fin b) K) (Y : Matrix (Fin a) (Fin b) K),
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m₁.val (m₁.val * Y) 0 m₂.val) = p.val := by
  set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := p.val.submatrix e e with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    refine Matrix.ext fun i j => hp ?_
    change (e (Sum.inl j) : ℕ) < e (Sum.inr i)
    simp [he]
    omega
  have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21]; exact (Matrix.fromBlocks_toBlocks M).symm
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact Matrix.GeneralLinearGroup.det_ne_zero p
  have hprod : M.toBlocks₁₁.det * M.toBlocks₂₂.det ≠ 0 := by
    rw [hMb, Matrix.det_fromBlocks_zero₂₁] at hdet
    simpa using hdet
  have hA : IsUnit M.toBlocks₁₁ :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hprod))
  have hD : IsUnit M.toBlocks₂₂ :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hprod))
  refine ⟨hA.unit, hD.unit, (hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂, ?_⟩
  have hAB : hA.unit.val * ((hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂) = M.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [hAB]
  change Matrix.reindex e e (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂) = p.val
  rw [← hMb, hM]
  ext i j
  simp

theorem iwasawa_parabolic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (g : GLw n w), ∃ (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = blk h w m Y * k := by
  intro E _ _ _ n a b h w g
  obtain ⟨k, c, hc, hg⟩ := GlobalTheory.ValIwasawa.iwasawa (w.adicCompletionIntegers E) (w.adicCompletion E) n g⁻¹
  have hk : Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) k ∈
      GlobalTheory.LFun.KGL w (n := n) := ⟨k, rfl⟩
  have hc' : (c⁻¹).1.BlockTriangular id := by
    haveI : Invertible c.1 := Units.invertible c
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hc
  obtain ⟨m₁, m₂, Y, hY⟩ := exists_blocks_of_upper h c⁻¹ hc'
  have hblk : blk h w (m₁, m₂) Y = c⁻¹ := by
    have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m₁.val (m₁.val * Y) 0 m₂.val)) := by
      rw [hY]; exact (c⁻¹).isUnit
    apply Units.ext
    simp only [blk]
    rw [dite_eq_left hU, IsUnit.unit_spec]
    exact hY
  refine ⟨(m₁, m₂), Y, _, inv_mem hk, ?_⟩
  rw [hblk, ← inv_inv g, hg, _root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.IwaBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamily
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem dualFam_exists : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  intro n E
  obtain ⟨e, ρ', hc, hiso, hint⟩ := _root_.GlobalTheory.CompanionTheory.RealCount.dualRep_exists E
  obtain ⟨F, hgl, -, hder⟩ := _root_.GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep _ ρ' hc hiso
  refine ⟨fun a b => e.symm.toLinearMap ∘ₗ F a b ∘ₗ e.toLinearMap, ?_, ?_⟩
  · intro a b c d
    ext1 ξ
    have h := LinearMap.congr_fun (hgl a b c d) (e ξ)
    apply e.injective
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_sub] at h ⊢
    rw [h]
    split_ifs <;> simp
  · intro X γ hX hγ ξ
    let eL : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] (E.V →L[ℂ] ℂ) :=
      LinearMap.toContinuousLinearMap e.symm.toLinearMap
    have heL : ∀ w, eL w = e.symm w := fun _ => rfl
    have h := (eL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder X γ hX hγ (e ξ))
    have hf : (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) = (eL.restrictScalars ℝ) ∘ fun t : ℝ => ρ' (γ t) (e ξ) := by
      funext t
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', heL, ← hint,
        LinearEquiv.symm_apply_apply]
    rw [hf]
    refine h.congr_deriv ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.coe_restrictScalars', map_sum, map_smul, heL, LinearMap.comp_apply,
      LinearEquiv.coe_coe]

end GlobalTheory.CompanionTheory.RealCountG
end
end

