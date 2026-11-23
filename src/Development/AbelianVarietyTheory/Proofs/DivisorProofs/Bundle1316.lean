module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeSmoothVariationAlongBoundedUnipotent
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapVari

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem nilM_smul {r : ℕ} (τ : ℝ) (x : BlockIx a r → Cinf E) :
    (nilM (τ • x) : Matrix (Fin a) (Fin a) (Cinf E)) = τ • nilM x := by
  ext i j
  simp only [nilM, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

theorem norm_toL_nilM_le {r : ℕ} (x : BlockIx a r → Cinf E) :
    ‖toL (nilM x : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  change ‖(nilM x : Matrix (Fin a) (Fin a) (Cinf E)) i j‖ ≤ ‖x‖
  simp only [nilM, Matrix.of_apply]
  split_ifs with h
  · exact norm_le_pi_norm x _
  · simp

theorem continuous_unip_inf {r : ℕ} :
    Continuous (fun x : BlockIx a r → Cinf E => (unip x : GL (Fin a) (Cinf E))) := by
  have hN : Continuous (fun x : BlockIx a r → Cinf E => (nilM x : Matrix (Fin a) (Fin a) (Cinf E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hN, continuous_const.sub hN⟩

theorem exists_bound_compact {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ Ω, ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A ∧
      ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A := by
  have h1 : Continuous (fun c : GL (Fin a) (Cinf E) => toL (c : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  have h2 : Continuous (fun c : GL (Fin a) (Cinf E) =>
      toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  obtain ⟨A1, hA1⟩ := hΩ.exists_bound_of_continuousOn h1.continuousOn
  obtain ⟨A2, hA2⟩ := hΩ.exists_bound_of_continuousOn h2.continuousOn
  exact ⟨max (max A1 A2) 0, le_max_right _ _, fun c hc =>
    ⟨(hA1 c hc).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hA2 c hc).trans ((le_max_right _ _).trans (le_max_left _ _))⟩⟩

theorem norm_conj_le (A : ℝ) (c : GL (Fin a) (Cinf E)) (N : Matrix (Fin a) (Fin a) (Cinf E))
    (h1 : ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A)
    (h2 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A) :
    ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N * c.val)‖ ≤ a * a * A * A * ‖toL N‖ := by
  have hA : 0 ≤ A := (norm_nonneg _).trans h1
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have p1 := norm_toL_mul_le ((c⁻¹ : GL (Fin a) (Cinf E)).val * N) c.val
  have p2 := norm_toL_mul_le (c⁻¹ : GL (Fin a) (Cinf E)).val N
  have p2' : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ ≤ a * (A * ‖toL N‖) :=
    p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) ha)
  have p3 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ * ‖toL c.val‖ ≤ (a * (A * ‖toL N‖)) * A :=
    mul_le_mul p2' h1 (norm_nonneg _) (mul_nonneg ha (mul_nonneg hA (norm_nonneg _)))
  exact (p1.trans (mul_le_mul_of_nonneg_left p3 ha)).trans (le_of_eq (by ring))

end GlobalTheory.RapVari


open GlobalTheory.RapVari in
theorem GlobalTheory.rap_vari : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t →
    ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ R : ℝ, 0 ≤ R →
    ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧
    ∀ ψ : Sm E a, ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
    (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
    ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω,
    ∀ z : BlockIx a j → Cinf E, ‖z‖ ≤ R →
    ‖ψ.1 (infGL E a (unip z * (d * c))) - ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a t ht i j hij Ω hΩ R hR
  obtain ⟨C0, hC0, hconj⟩ := _root_.GlobalTheory.unip_mul_diag_cone E a t ht i j hij
  obtain ⟨B, Cb, hCb, hbasis⟩ := _root_.GlobalTheory.CuspRapid.lieD_le_of_basis E a
  obtain ⟨A, hA, hAc⟩ := exists_bound_compact hΩ
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have haA : (0 : ℝ) ≤ a * a * A * A := mul_nonneg (mul_nonneg (mul_nonneg ha ha) hA) hA
  refine ⟨(fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
      (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω), B, Cb * (a * a * A * A) * (C0 * R), ?_, ?_, ?_⟩
  · exact ((isCompact_closedBall 0 (C0 * C0 * R)).prod hΩ).image
      ((continuous_unip_inf.comp continuous_fst).mul continuous_snd)
  · exact mul_nonneg (mul_nonneg hCb haA) (mul_nonneg hC0 hR)
  intro ψ r d hr hrat hd M hM hB c hc z hz
  obtain ⟨hq, hz'⟩ := hconj r d hr hrat hd
  obtain ⟨z', hz'n, hcomm⟩ := hz' z
  have hq0 : 0 ≤ r j / r i := div_nonneg (hr j).le (hr i).le
  have hz'R : ‖z'‖ ≤ C0 * (r j / r i) * R := hz'n.trans (mul_le_mul_of_nonneg_left hz (mul_nonneg hC0 hq0))
  have hz'R' : ‖z'‖ ≤ C0 * C0 * R :=
    hz'R.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC0) hR)
  have hu : ∀ τ : ℝ, ((c⁻¹ * unip (τ • z') * c : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      1 + τ • ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) := by
    intro τ
    rw [Units.val_mul, Units.val_mul]
    change (c⁻¹ : GL (Fin a) (Cinf E)).val * (1 + nilM (τ • z')) * c.val = _
    rw [nilM_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hNN : ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) *
      ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) = 0 := by
    calc _ = (c⁻¹ : GL (Fin a) (Cinf E)).val *
          (nilM z' * (c.val * (c⁻¹ : GL (Fin a) (Cinf E)).val) * nilM z') * c.val := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Units.mul_inv, Matrix.mul_one, nilM_mul, Matrix.mul_zero, Matrix.zero_mul]
  have hNnorm : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val)‖ ≤
      a * a * A * A * (C0 * (r j / r i) * R) :=
    (norm_conj_le A c _ (hAc c hc).1 (hAc c hc).2).trans
      (mul_le_mul_of_nonneg_left ((norm_toL_nilM_le z').trans hz'R) haA)
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, unip (τ • z') * c ∈
      (fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
        (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω) := by
    intro τ hτ
    refine ⟨(τ • z', c), ⟨?_, hc⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hτ.2).trans hz'R'
  have key := GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment E a ψ (infGL E a (d * c)) _ (fun τ => c⁻¹ * unip (τ • z') * c)
    (Cb * (a * a * A * A * (C0 * (r j / r i) * R)) * M) hNN hu (by
      intro τ hτ
      have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip (τ • z') * c) =
          infGL E a (d * (unip (τ • z') * c)) := by
        rw [← map_mul]; congr 1; group
      rw [e]
      refine (hbasis ψ.1 _ _ M (fun Y hY => hB Y hY _ (hmem τ hτ)) hM).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNnorm hCb) hM)
  have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip ((1 : ℝ) • z') * c) = infGL E a (unip z * (d * c)) := by
    rw [← map_mul]; congr 1
    have h1 := hcomm 1
    rw [one_smul, one_smul] at h1
    rw [one_smul, ← mul_assoc (unip z) d c, h1]
    group
  rw [e] at key
  exact key.trans (le_of_eq (by ring))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TorusHeight

open scoped Matrix.Norms.L2Operator

theorem opNorm_le_of_shape {n q : ℕ} (X Y' : Matrix (Fin n) (Fin q) ℂ) (Y X' : Matrix (Fin q) (Fin n) ℂ)
    (d d' : Fin q → ℂ) {s : ℝ} (hs : 0 ≤ s) (hd : ∀ i, ‖d i‖ ≤ s) (hd' : ∀ i, ‖d' i‖ ≤ s) :
    (opNorm (1 + X * Matrix.diagonal d * Y + Y' * Matrix.diagonal d' * X') : ℝ) ≤
      1 + (‖X‖ * ‖Y‖ + ‖Y'‖ * ‖X'‖) * s := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, (opNorm M : ℝ) = ‖M‖ := fun M => by
    rw [opNorm, coe_nnNorm]; exact (Matrix.l2_opNorm_def M).symm
  rw [e]
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hD : ‖Matrix.diagonal d‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd
  have hD' : ‖Matrix.diagonal d'‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd'
  have h2 : ‖X * Matrix.diagonal d * Y‖ ≤ ‖X‖ * s * ‖Y‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg _))) (norm_nonneg _))
  have h3 : ‖Y' * Matrix.diagonal d' * X'‖ ≤ ‖Y'‖ * s * ‖X'‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD' (norm_nonneg _))) (norm_nonneg _))
  calc _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖X * Matrix.diagonal d * Y‖ + ‖Y' * Matrix.diagonal d' * X'‖ :=
        norm_add₃_le
    _ ≤ 1 + ‖X‖ * s * ‖Y‖ + ‖Y'‖ * s * ‖X'‖ := by linarith
    _ = _ := by ring

theorem le_prod_of_forall_le {q : ℕ} {c : ℝ} (hc : 0 < c) (t : Fin q → ℝ) (ht : ∀ i, c ≤ t i) (k : Fin q) :
    t k * (min 1 c) ^ (q - 1) ≤ ∏ i, t i := by
  have hm : 0 < min 1 c := lt_min one_pos hc
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ k)]
  have hk : 0 ≤ t k := hc.le.trans (ht k)
  refine mul_le_mul_of_nonneg_left ?_ hk
  have := Finset.prod_le_prod₀ (s := Finset.univ.erase k) (f := fun _ => min 1 c) (g := t) (fun _ _ => hm.le)
    (fun i _ => (min_le_right _ _).trans (ht i))
  simpa [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin] using this

theorem norm_ofReal_sub_one (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_ofReal_inv_sub_one (x : ℝ) : ‖(x : ℂ)⁻¹ - 1‖ = |x⁻¹ - 1| := by
  rw [← Complex.ofReal_inv, norm_ofReal_sub_one]

theorem height_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (c : ℝ), 0 < c →
    ∃ (C : ℝ) (A : ℕ), ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ a : GAd σ J, a ∈ infPts σ J →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w),
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1)) →
      (height σ J a : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  intro F E _ _ _ _ _ σ hcm n J q Xf Yf c hc
  classical
  have hm : 0 < min 1 c := lt_min one_pos hc
  set c0 : ℝ := ((min 1 c) ^ (q - 1))⁻¹ + c⁻¹ + 1 with hc0
  have hc0' : 1 ≤ c0 := by
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    linarith
  let τ0 : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  let K : InfinitePlace F → ℝ := fun w =>
    ‖(Xf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Yf * J).map (τ0 w).1‖ +
      ‖(Yf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Xf * J).map (τ0 w).1‖
  have hK : ∀ w, 0 ≤ K w := fun w => by positivity
  refine ⟨∏ w, (1 + K w * c0), Fintype.card (InfinitePlace F), fun t ht a ha hA => ?_⟩
  set P := ∏ i, t i with hP'
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => hc.le.trans (ht i)
  have hs : 0 ≤ c0 * (1 + P) := by positivity
  have hs1 : ∀ k, |t k - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 ≤ t k := hc.le.trans (ht k)
    have h1 := le_prod_of_forall_le hc t ht k
    have hpow : 0 < (min 1 c) ^ (q - 1) := pow_pos hm _
    have h2 : t k ≤ ((min 1 c) ^ (q - 1))⁻¹ * P := by
      rw [← div_eq_inv_mul, le_div_iff₀ hpow]; exact h1
    have h3 : |t k - 1| ≤ t k + 1 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : ((min 1 c) ^ (q - 1))⁻¹ * P ≤ c0 * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      linarith
    nlinarith
  have hs2 : ∀ k, |(t k)⁻¹ - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 < t k := hc.trans_le (ht k)
    have h1 : (t k)⁻¹ ≤ c⁻¹ := inv_anti₀ hc (ht k)
    have h0 : 0 ≤ (t k)⁻¹ := inv_nonneg.2 htk.le
    have h3 : |(t k)⁻¹ - 1| ≤ (t k)⁻¹ + 1 := by
      rw [abs_le]; constructor <;> linarith
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    nlinarith

  have hfin : ∀ v, htFin F v (matHom _ σ J (proj σ J v a)) = 1 := fun v => by
    rw [mem_infPts_iff_forall.1 ha v, map_one]
    exact htOf_eq_one.2 ⟨by simpa using normFin_one_le (E := E) F v, by simpa using normFin_one_le (E := E) F v⟩

  have hinf : ∀ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
    intro w
    obtain ⟨h1, h2⟩ := hA w (τ0 w)
    have e1 : normInf F w ((matHom _ σ J (projArch σ J w a) : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) = opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) :=
      normInf_eq_opNorm hcm (τ0 w) _
    have e2 : normInf F w (((matHom _ σ J (projArch σ J w a))⁻¹ : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) =
        opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) := by
      rw [← map_inv, ← map_inv]; exact normInf_eq_opNorm hcm (τ0 w) _
    have B1 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h1]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs1 i
      · rw [norm_ofReal_inv_sub_one]; exact hs2 i
    have B2 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h2]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs2 i
      · rw [norm_ofReal_inv_sub_one, inv_inv]; exact hs1 i
    have hfin' : (1 + K w * (c0 * (1 + P))) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    have hone : (1 : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    simp only [htInf, htOf, NNReal.coe_max, NNReal.coe_one]
    rw [e1, e2]
    exact max_le hone (max_le (B1.trans hfin') (B2.trans hfin'))
  have hh : (height σ J a : ℝ) = ∏ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) := by
    rw [height_eq]
    simp only [hfin, finprod_one, mul_one, NNReal.coe_prod]
  rw [hh]
  calc _ ≤ ∏ w, ((1 + K w * c0) * (1 + P)) :=
        Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) (fun w _ => hinf w)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end GlobalTheory.TorusHeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArc
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem exists_mat_at {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mat_eq_zero {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (D : Matrix m k (AE F E)) (hD : At (evI F) D) (h0 : ∀ w, D.map (piInf (τ w)) = 0) : D = 0 := by
  ext i j
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm τ (D i j) (fun u hu => ?_) (fun w => ?_)
  · have := congrFun (congrFun (hD u hu) i) j
    simpa using this
  · have := congrFun (congrFun (h0 w) i) j
    simpa using this

theorem at_add {m k : Type} {D D' : Matrix m k (AE F E)} (hD : At (evI F) D) (hD' : At (evI F) D') :
    At (evI F) (D + D') := by
  intro u hu; rw [smul_add, hD u hu, hD' u hu, add_zero]

theorem at_mul_left {m k l : Type} [Fintype k] {D : Matrix m k (AE F E)} (hD : At (evI F) D) (N : Matrix k l (AE F E)) :
    At (evI F) (D * N) := by
  intro u hu; rw [← Matrix.smul_mul, hD u hu, Matrix.zero_mul]

theorem at_mul_right {m k l : Type} [Fintype k] {D : Matrix k l (AE F E)} (hD : At (evI F) D) (N : Matrix m k (AE F E)) :
    At (evI F) (N * D) := by
  intro u hu; rw [← Matrix.mul_smul, hD u hu, Matrix.mul_zero]

theorem at_transpose {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) : At (evI F) Dᵀ := by
  intro u hu; rw [← Matrix.transpose_smul, hD u hu, Matrix.transpose_zero]

theorem at_map_cA (σ : E →ₐ[F] E) {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) :
    At (evI F) (D.map (cA σ)) := by
  intro u hu
  ext i j
  have := congrFun (congrFun (hD u hu) i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, Matrix.map_apply] at this ⊢
  rw [← map_smul, this, map_zero]

theorem map_cA_piInf {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {m k : Type}
    (D : Matrix m k (AE F E)) : (D.map (cA σ)).map (piInf τ) = (D.map (piInf τ)).map star := by
  ext i j
  simp [GlobalTheory.RealLift.KLineProof.piInf_cA hcm]

theorem cartan_conj {n r s : ℕ} (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ) (hs : HasSig M r s) (h₁ : IsCartan M θ₁)
    (h₂ : IsCartan M θ₂) :
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  obtain ⟨A₁, hF₁, hA₁⟩ := _root_.GlobalTheory.RealLift.frameEx_holds n r s M θ₁ hs h₁
  obtain ⟨A₂, hF₂, hA₂⟩ := _root_.GlobalTheory.RealLift.frameEx_holds n r s M θ₂ hs h₂
  obtain ⟨A₁', h11, h12⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₁
  obtain ⟨A₂', h21, h22⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₂
  refine ⟨A₂ * A₁', A₁ * A₂', ?_, ?_, ?_⟩
  · calc A₂ * A₁' * (A₁ * A₂') = A₂ * (A₁' * A₁) * A₂' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h12, Matrix.mul_one, h21]
  · have e1 := hF₁.1
    have e2 := hF₂.1
    rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]
    calc A₁'ᵀ * A₂ᵀ * M * (A₂.map star * A₁'.map star)
        = A₁'ᵀ * (A₂ᵀ * M * A₂.map star) * A₁'.map star := by simp only [Matrix.mul_assoc]
      _ = A₁'ᵀ * (A₁ᵀ * M * A₁.map star) * A₁'.map star := by rw [e2, e1]
      _ = (A₁ * A₁')ᵀ * M * (A₁ * A₁').map star := by
          rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]; simp only [Matrix.mul_assoc]
      _ = M := by
          rw [h11, Matrix.transpose_one, Matrix.map_one _ (star_zero _) (star_one _), Matrix.one_mul, Matrix.mul_one]
  · have k1 : A₁' * θ₁ = Formalism.BasicNotions.TH.Jm r s * A₁' := by
      calc A₁' * θ₁ = A₁' * θ₁ * (A₁ * A₁') := by rw [h11, Matrix.mul_one]
        _ = A₁' * (θ₁ * A₁) * A₁' := by simp only [Matrix.mul_assoc]
        _ = (A₁' * A₁) * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [hA₁]; simp only [Matrix.mul_assoc]
        _ = Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [h12, Matrix.one_mul]
    calc A₂ * A₁' * θ₁ = A₂ * (A₁' * θ₁) := Matrix.mul_assoc _ _ _
      _ = A₂ * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [k1, Matrix.mul_assoc]
      _ = θ₂ * (A₂ * A₁') := by rw [← hA₂, Matrix.mul_assoc]

end GlobalTheory.CartanConjSkew

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

theorem conj_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have hcm := hB.cm
  have key : ∀ w, ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧
      uᵀ * X.J.map (B.emb w).1 * u.map star = X.J.map (B.emb w).1 ∧ u * X.θ w = Y.θ w * u := by
    intro w
    obtain ⟨u, v, huv, hu, hθ⟩ := cartan_conj (Complex.I • X.J.map (B.emb w).1) (X.θ w) (Y.θ w) (hX.sig w)
      (hX.cartan w) (hY.cartan w)
    refine ⟨u, v, huv, ?_, hθ⟩
    rw [Matrix.mul_smul, Matrix.smul_mul] at hu
    exact smul_right_injective _ Complex.I_ne_zero hu
  choose u v huv hu hθ using key
  obtain ⟨G, hGat, hG⟩ := exists_mat_at hcm B.emb (fun w => u w - 1)
  obtain ⟨H, hHat, hH⟩ := exists_mat_at hcm B.emb (fun w => v w - 1)
  have hmap1 : ∀ w, (1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (B.emb w)) = 1 :=
    fun w => Matrix.map_one _ (map_zero _) (map_one _)
  have hgmap : ∀ w, (1 + G).map (piInf (B.emb w)) = u w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hG]; abel
  have hhmap : ∀ w, (1 + H).map (piInf (B.emb w)) = v w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hH]; abel
  have hgh : (1 + G) * (1 + H) = 1 := by
    have h0 : (1 + G) * (1 + H) - 1 = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G) * (1 + H) - 1 = G + H + G * H := by noncomm_ring
        rw [e]; exact at_add (at_add hGat hHat) (at_mul_left hGat H)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, hgmap, hhmap, hmap1, huv, sub_self]
    exact sub_eq_zero.1 h0
  have hhg : (1 + H) * (1 + G) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hgh
  let g0 : GL (Fin n) (AE F E) := ⟨1 + G, 1 + H, hgh, hhg⟩
  have hmem : g0 ∈ UG (cA σ) (incM F X.J) := by
    show (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) = incM F X.J
    have h0 : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J =
            Gᵀ * incM F X.J + incM F X.J * G.map (cA σ) + Gᵀ * incM F X.J * G.map (cA σ) := by
          rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
        rw [e]
        exact at_add (at_add (at_mul_left (at_transpose hGat) _) (at_mul_right (at_map_cA σ hGat) _))
          (at_mul_right (at_map_cA σ hGat) _)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_cA_piInf hcm, hgmap,
          incM_map_piInf, hu, sub_self]
    exact sub_eq_zero.1 h0
  refine ⟨⟨g0, hmem⟩, ?_, fun w => ?_⟩
  · show At (evI F) ((1 + G) - 1)
    rw [add_sub_cancel_left]; exact hGat
  · show (1 + G).map (piInf (B.emb w)) * X.θ w = Y.θ w * (1 + G).map (piInf (B.emb w))
    rw [hgmap]; exact hθ w

end GlobalTheory.CartanConjSkew
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d m : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    GlobalTheory.InertVacLag.IsLagrAt σ W v C → ∀ (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    u ∈ GlobalTheory.InertVacLag.lagAt v C → u' ∈ GlobalTheory.InertVacLag.lagAt v C →
    symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) u u' = 0 := by
  first | exact @GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt | exact GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt | (intros; apply GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt <;> assumption)
end

