module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralCompAut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousDualG

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.OneAddPow
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition

section

variable {R : Type} [CommRing R] {n : ℕ}

abbrev aC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1)).submatrix finSumFinEquiv.symm id

theorem CC_add : dC R n * (dC R n)ᵀ + aC R n * (aC R n)ᵀ = (2 : R) • 1 := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [diagCols, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, id, Matrix.smul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply] <;> split_ifs <;>
    first | (simp_all; done) | (simp_all; norm_num; done) | norm_num

theorem C_D (J : Matrix (Fin n) (Fin n) R) :
    (dC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (aC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_D (J : Matrix (Fin n) (Fin n) R) :
    (aC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (dC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_C : (aC R n)ᵀ * dC R n = 0 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, diagCols, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp

theorem C_A : (dC R n)ᵀ * aC R n = 0 := by
  have := congrArg Matrix.transpose (A_C (R := R) (n := n))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this

theorem ring_facts {A : Type} [Ring A] [Algebra R A] {Q Q' D N : A} {x y : R} (hxy : x * y = 1) (h1 : Q + Q' = 1)
    (hQ : Q * Q' = 0) (hQ' : Q' * Q = 0) :
    (x • Q + y • Q') * (y • Q + x • Q') = 1 ∧
    (Q * D * Q = 0 → Q' * D * Q' = 0 → (x • Q + y • Q') * D * (x • Q + y • Q') = D) ∧
    (N * Q = 0 → Q' * N = 0 → N * N = 0 ∧ (x • Q + y • Q') * N * (y • Q + x • Q') = (x * x) • N) := by
  have e1 : Q * Q = Q := by
    have := congrArg (Q * ·) h1
    simpa only [mul_add, hQ, add_zero, mul_one] using this
  have e2 : Q' * Q' = Q' := by
    have := congrArg (Q' * ·) h1
    simpa only [mul_add, hQ', zero_add, mul_one] using this
  have hyx : y * x = 1 := by rw [mul_comm, hxy]
  refine ⟨?_, fun a b => ?_, fun a b => ?_⟩
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, e1, e2, hQ, hQ', smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul, h1]
  · have hD : D = (Q + Q') * D * (Q + Q') := by rw [h1, one_mul, mul_one]
    conv_rhs => rw [hD]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, a, b, smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul]
  · have c1 : Q * N = N := by
      have := congrArg (· * N) h1
      simpa only [add_mul, b, add_zero, one_mul] using this
    have c2 : N * Q' = N := by
      have := congrArg (N * ·) h1
      simpa only [mul_add, a, zero_add, mul_one] using this
    refine ⟨by rw [← c2, mul_assoc, ← mul_assoc Q', b, zero_mul, mul_zero], ?_⟩
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, c1, b, smul_zero, add_zero, mul_add, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, a, c2, smul_zero, smul_zero, zero_add, smul_smul]

theorem one_add_pow {A : Type} [Ring A] {N : A} (h : N * N = 0) (m : ℕ) : (1 + N) ^ m = 1 + m • N := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc m N N, h, succ_nsmul]; simp [add_assoc, add_comm N]

end

theorem conj_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT → ∀ k : ℕ, 0 < k →
    ∃ (M : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
      mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) M * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 ∧
      ∀ n : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) n * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT →
        M * n * M⁻¹ = n ^ (k * k) := by
  intro F E _ _ _ _ _ σ n J hJ k hk
  let R := AF F ⊗[F] E
  let q : ℚ →+* R := (incAF F E).comp (algebraMap ℚ E)
  have hq : ∀ r, cAF σ (q r) = q r := fun r =>
    congrArg (incAF F E) (show σ (algebraMap ℚ E r) = algebraMap ℚ E r by simp)
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hxy : q k * q (k : ℚ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hk', map_one]
  have hyx : q (k : ℚ)⁻¹ * q k = 1 := by rw [mul_comm, hxy]
  have h2 : q (1 / 2) * 2 = 1 := by rw [← map_ofNat q 2, ← map_mul]; norm_num
  let Q : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (dC R n * (dC R n)ᵀ)
  let Q' : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (aC R n * (aC R n)ᵀ)
  let J' := J.map (incAF F E)
  let D : Matrix (Fin (n + n)) (Fin (n + n)) R := (dbl J').submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have hD : JR (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) = D := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective j
    simp only [JR, D, J', GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Matrix.map_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases p with p | p <;> rcases r with r | r <;> simp
  have h1 : Q + Q' = 1 := by rw [← smul_add, CC_add, smul_smul, h2, one_smul]
  have hQ : Q * Q' = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ' : Q' * Q = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD : Q * D * Q = 0 := by
    simp only [Q, Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (dC R n), C_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD' : Q' * D * Q' = 0 := by
    simp only [Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (aC R n), A_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ'C : Q' * dC R n = 0 := by
    simp only [Q', Matrix.smul_mul]
    rw [Matrix.mul_assoc, A_C]; simp
  have hQC : Q * dC R n = dC R n := by
    have := congrArg (· * dC R n) h1
    simpa only [Matrix.add_mul, hQ'C, add_zero, Matrix.one_mul] using this
  have f1 := fun N => ring_facts (D := D) (N := N) hxy h1 hQ hQ'
  have f2 := ring_facts (D := D) (N := 0) hyx h1 hQ hQ'
  let M : GL (Fin (n + n)) R := ⟨q k • Q + q (k : ℚ)⁻¹ • Q', q (k : ℚ)⁻¹ • Q + q k • Q', (f1 0).1, f2.1⟩
  have haC : (aC R n).map (cAF σ) = aC R n := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    rcases p with p | p <;> simp [Matrix.one_apply, apply_ite (cAF σ)]
  have hsm : ∀ (r : ℚ) (X : Matrix (Fin (n + n)) (Fin (n + n)) R), (q r • X).map (cAF σ) = q r • X.map (cAF σ) :=
    fun r X => by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hq]
  have hM : (M.1.map (cAF σ))ᵀ = M.1 := by
    show ((q k • Q + q (k : ℚ)⁻¹ • Q').map (cAF σ))ᵀ = q k • Q + q (k : ℚ)⁻¹ • Q'
    rw [Matrix.map_add _ (map_add _), hsm, hsm, hsm, hsm, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      Matrix.transpose_map, dC_map, haC]
    simp only [Q, Q', Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hmem : M ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) := by
    show (M.1.map (cAF σ))ᵀ * JR (AF F) _ * M.1 = JR (AF F) _
    rw [hM, hD]
    exact (f1 0).2.1 hQD hQD'
  let t : GL (Fin n) R := ⟨q k • 1, q (k : ℚ)⁻¹ • 1, by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hxy, one_smul],
    by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hyx, one_smul]⟩
  refine ⟨(⟨M, hmem⟩ : HR (AF F) σ _), t, ?_, fun g hg => ?_⟩
  · show (q k • Q + q (k : ℚ)⁻¹ • Q') * dC R n = dC R n * (q k • 1)
    rw [Matrix.add_mul, Matrix.smul_mul _ Q, Matrix.smul_mul _ Q', hQC, hQ'C, smul_zero, add_zero, Matrix.mul_smul,
      Matrix.mul_one]
  · set G := mtF σ _ g with hG
    have hu : (G.map (cAF σ))ᵀ * JR (AF F) _ * G = JR (AF F) _ := g.2
    rw [hD] at hu
    have hJu : IsUnit J'.det := by
      have := (Ne.isUnit hJ.2).map (incAF F E)
      rwa [RingHom.map_det] at this
    have a1 : (G - 1) * Q = 0 := by
      simp only [Q, Matrix.mul_smul]
      rw [← Matrix.mul_assoc, Matrix.sub_mul, hg, Matrix.one_mul, sub_self, Matrix.zero_mul, smul_zero]
    have a2 : (aC R n)ᵀ * (G - 1) = 0 := by
      have b1 : (dC R n)ᵀ * (G.map (cAF σ))ᵀ = (dC R n)ᵀ := by
        rw [← Matrix.transpose_mul, ← dC_map (cAF σ) n, ← Matrix.map_mul, hg]
      have b2 : (dC R n)ᵀ * D * G = (dC R n)ᵀ * D := by
        conv_rhs => rw [← hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, b1]
      rw [C_D] at b2
      have b3 : J' * ((aC R n)ᵀ * (G - 1)) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, b2, sub_self]
      rw [← Matrix.one_mul (_ * _), ← Matrix.nonsing_inv_mul _ hJu, Matrix.mul_assoc, b3, Matrix.mul_zero]
    have a3 : Q' * (G - 1) = 0 := by
      simp only [Q', Matrix.smul_mul]
      rw [Matrix.mul_assoc, a2, Matrix.mul_zero, smul_zero]
    obtain ⟨n1, n2⟩ := (f1 (G - 1)).2.2 a1 a3
    refine Subtype.ext (Units.ext ?_)
    have e : mtF σ _ (g ^ (k * k)) = G ^ (k * k) := by
      rw [hG, mtF, mtF, map_pow, Units.val_pow_eq_pow_val]
    refine Eq.trans ?_ e.symm
    show (q k • Q + q (k : ℚ)⁻¹ • Q') * G * (q (k : ℚ)⁻¹ • Q + q k • Q') = _
    rw [← add_sub_cancel 1 G, one_add_pow n1, mul_add _ 1 (G - 1), mul_one, add_mul (q k • Q + q (k : ℚ)⁻¹ • Q'),
      (f1 0).1, n2, map_natCast, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Periodic
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition

theorem periodic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ}
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ f) :
    ∀ γ ∈ ratLF F E nS nT, ∀ v : WOF F E nS nT,
      f (dC (AF F ⊗[F] E) nT * (γ + v)) = f (dC (AF F ⊗[F] E) nT * v) := by
  rintro _ ⟨γ, rfl⟩ v
  show f (GlobalTheory.SplitLagrF.dC F E nT * ((ratWF γ : WOF F E nS nT) + v)) = f (GlobalTheory.SplitLagrF.dC F E nT * v)
  have hq := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (GlobalTheory.SplitLagrF.dC F E nT * v)
  rw [← GlobalTheory.SplitLagrF.dC_mul_ratWF, GlobalTheory.SplitLagrF.symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
  rw [Matrix.mul_add, hq]

theorem integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ f →
      Integrable (fun u : WOF F E nS nT => f (dC (AF F ⊗[F] E) nT * u)) (ν.restrict 𝓕) := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ ν 𝓕 hν h𝓕 f hf
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕⟩
  have hcont : Continuous fun u : WOF F E nS nT => f (dC (AF F ⊗[F] E) nT * u) :=
    hf.cont.comp (continuous_const.matrix_mul continuous_id)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← periodic hf γ hγ w]
  exact hC _ h

theorem rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ γ ∈ GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) γ * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, γ) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 χS ωd hω γ hγ t ht f hf
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h0 : ∀ y : WOF F E nS (nT + nT), symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ 0 y = 0 := fun y => by
    simp [symplOHF, symplOF, hOF]
  have h1 : ∀ w : WOF F E nS nT, ωd (1, γ) f (dC (AF F ⊗[F] E) nT * w) = f (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) := by
    intro w
    have hact : actOF σ JS _ 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) = dC (AF F ⊗[F] E) nT * w := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc, ht, Matrix.mul_assoc,
        ← Matrix.mul_assoc t.1, Units.mul_inv, Matrix.one_mul]
    have h2 := congrFun (hω.om_heis 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) f hf) 0
    rw [hω.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ _ f hf), hact] at h2
    simp only [heisOF, h0, AddChar.map_zero_eq_one, one_mul, zero_add] at h2
    exact h2.symm
  obtain ⟨g₀, -, hg⟩ := hγ
  have hg' : mtF σ _ γ = g₀.1.map (incAF F E) := (congrArg Units.val hg).symm
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Matrix (Fin nT) (Fin nT) E, t.1 = incM F s₀ := by
    refine ⟨(g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).submatrix (fun p => finSumFinEquiv (Sum.inl p)) id, ?_⟩
    have e : (g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).map (incAF F E) = dC (AF F ⊗[F] E) nT * t.1 := by
      rw [Matrix.map_mul, ← hg', ← ht]
      congr 1
      have := GlobalTheory.LagrThetaInv.dC_mul_rat (F := F) (1 : Matrix (Fin nT) (Fin nT) E)
      rw [Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
      exact this.symm
    ext i j
    rw [← GlobalTheory.LagrThetaInv.dC_mul_inl t.1, ← e]
    rfl
  have hd := GlobalTheory.DiagThetaRatF.det_ne_zero_of_unit t s₀ hs₀
  have hs₁ : (t⁻¹).1 = incM F s₀⁻¹ := by
    rw [Matrix.coe_units_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [hs₀]
    show s₀.map (inclR (F := F) (AF F)) * s₀⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hm : ∀ (s : Matrix (Fin nT) (Fin nT) E) (x : WOF F E nS nT), x ∈ ratLF F E nS nT →
      (incM F s * x : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) ∈ ratLF F E nS nT := by
    rintro s _ ⟨y, rfl⟩
    refine ⟨s * y, ?_⟩
    show (s * y).map (incAF F E) = s.map (incAF F E) * y.map (incAF F E)
    exact Matrix.map_mul
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => (t⁻¹).1 * w
      invFun := fun w => t.1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  unfold GlobalTheory.LagrTheta.lagrInt
  simp only [h1]
  exact GlobalTheory.DiagThetaRatF.setIntegral_comp_aut (ratLF F E nS nT) hK hKc ν h𝓕 e
    (continuous_const.matrix_mul continuous_id) (continuous_const.matrix_mul continuous_id)
    (fun x hx => by
      show (t⁻¹).1 * x ∈ _
      rw [hs₁]
      exact hm _ x hx)
    (fun x hx => by
      show t.1 * x ∈ _
      rw [hs₀]
      exact hm _ x hx)
    (fun w => f (dC (AF F ⊗[F] E) nT * w)) (periodic hf)

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.TargetDoubling
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW

def TargetDoubling : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JB) (dbl (incM F JA))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JA)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JB) (incM F JA) (GlobalTheory.WeilSchrodinger.transD (cA σ) co) dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (dbl (incM F JA)) dd χS (diagCols (Fin nT)) omd ∧
                ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (dbl (incM F JA))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂

def SourceDoubling : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JA) (incM F JB) co dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JA) (dbl (incM F JB)) dd χT (diagCols (Fin nS)) omd ∧
                ∀ (g : UG (cA σ) (incM F JB)) (gd : UG (cA σ) (dbl (incM F JB))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem invT_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) : (J⁻¹ᵀ)ᵀ * J = 1 := by
  rw [Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ (Ne.isUnit h.2)]

omit [NumberField F] [NumberField E] in
theorem isHermND_invT {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) : IsHermND σ J⁻¹ᵀ := by
  have hu : IsUnit J.det := Ne.isUnit h.2
  have e1 : J.map (σ : E →+* E) = Jᵀ := by
    ext i j
    exact h.1 j i
  have e2 : (Jᵀ)⁻¹ = J⁻¹.map (σ : E →+* E) := Matrix.inv_eq_left_inv (by
    rw [← e1, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨fun i j => ?_, ?_⟩
  · have := congrFun (congrFun e2 i) j
    rw [← Matrix.transpose_nonsing_inv] at this
    exact this.symm
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero

theorem LatH.swap {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    (hS : IsHermND σ JS) (hT : IsHermND σ JT) (h : LatH σ JS JT ξ₀) : LatH σ JT⁻¹ᵀ JS⁻¹ᵀ ξ₀ :=
  Sw.latH_swap σ (invT_mul hS) (invT_mul hT) ξ₀ h

theorem isDblCoord_cast₂ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Invertible (2 : R)] {ξ ξ' : A} {J J' : Matrix β β A} (h : ξ • J = ξ' • J')
    {K : Matrix α α A} {κ : Type} [Fintype κ] (d : Darboux (symp c ξ K J) κ) {dd : Darboux (symp c ξ' K (dbl J')) (κ ⊕ κ)}
    (H : IsDblCoord c ξ' K J' (GlobalTheory.WeilSchrodinger.transD c (Sw.castD c h (GlobalTheory.WeilSchrodinger.transD c d))) dd) :
    IsDblCoord c ξ K J d (Sw.castD₂ c (Sw.smul_dbl h) dd) := fun w₁ w₂ => H w₁ w₂

theorem swapHom_fst {A α G M : Type} [CommRing A] [Fintype α] [DecidableEq α] [Group G] [Monoid M]
    {H K : Subgroup (GL α A)} (hle : H ≤ K) (hge : K ≤ H) (om : G × K →* M) (g : K) :
    Sw.swapHom hle om (Subgroup.inclusion hge g, 1) = om (1, g) := rfl

open Formalism.IndefR.DatumF Sw in
set_option maxHeartbeats 400000 in
theorem dblS_of_dblT (H : TargetDoubling) : SourceDoubling := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ hL χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have lS := invT_mul hS
  have lT := invT_mul hT
  have hsm : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) E), incM F (ξ₀ • M) = incAF F E ξ₀ • incM F M := fun M => by
    ext i j
    exact map_mul (incAF F E) _ _
  have hB' : ξ • incM F JB = incAF F E ξ₀ • incM F JS⁻¹ := hBm.trans (hsm _)
  have hx : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 _ hξ).map _
  have hd : IsUnit (incM F JS⁻¹).det := by
    have h1 : IsUnit (JS⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)
    have h2 : (incM F JS⁻¹).det = incAF F E (JS⁻¹).det := (RingHom.map_det (incAF F E) _).symm
    rw [h2]
    exact h1.map _
  have hle := ug_le (cA σ) hB' hx hd
  have hge := ug_ge (cA σ) hB' hx
  have hD := smul_dbl hB'
  have hge' := ug_ge (cA σ) hD hx
  have htr := swap_transport σ lS lT B.ψ hle co _ (castD_transD_rho _ hB' co B.ψ) hom _ (swapHom_apply hle om)
  have hrat' : ∀ x : Matrix (Fin nS) (Fin nT) E, ∃ y z : κ → F,
      (castD _ hB' (GlobalTheory.WeilSchrodinger.transD (cA σ) co)).e (incM F x) =
        (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    obtain ⟨y, z, h⟩ := hrat xᵀ
    exact ⟨y, z, (castD_transD_e _ hB' co _).trans h⟩
  have g1 : JS⁻¹ = (JS⁻¹ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
  have g2 : incAF F E ξ₀ • incM F JA = incM F (ξ₀ • (JT⁻¹ᵀ)⁻¹) := by
    rw [(dual_inv lT).2, hsm, hA]
  obtain ⟨dd, omd, k1, k2, k3⟩ := H F E σ B hB nT nS JT⁻¹ᵀ JS⁻¹ᵀ (isHermND_invT hT) (isHermND_invT hS) ξ₀ hξ hσξ
    (LatH.swap hS hT hL) χT χS cT cS rT rS _ (swap_datum σ lS lT ξ₀ B.ψ hω) JS⁻¹ JA (incAF F E ξ₀) g1 g2 κ _ hrat' _ htr
  refine ⟨castD₂ _ hD dd, omd.comp (Subgroup.inclusion hge'), isDblCoord_cast₂ _ hB' co k1,
    isUWeilSplit_cast₂ _ hD hge' (isLagr_diagCols _ _) k2, fun g gd hgd φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
  have k4 := k3 (Subgroup.inclusion hge g) (Subgroup.inclusion hge' gd) hgd φ₁ hφ₁ φ₂ hφ₂
  rw [swapHom_fst] at k4
  rw [MonoidHom.comp_apply]
  exact k4

end PositivityTheory.ThKW

end
end

