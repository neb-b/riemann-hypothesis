module

public import Mathlib
public import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
public import Development.WeilBound.ThetaLifts.FrameEstimates.RankIffRight
public import Development.WeilBound.ThetaLifts.FrameEstimates.UFinMulRId
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0002
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.HermitianFormDetNeZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace PositivityTheory.ThKEst

namespace W

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (a : AF F) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hn a)]

theorem coef_eigen {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure]
    (Φ : (κ → AF F) → ℂ) (u w : (κ → AF F) × (κ → AF F)) (a : AF F) (h : schr ψ u Φ = ψ a • Φ) :
    coef F ψ μ Φ (fun x => Φ (-x)) w = ψ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 + (a + a)) * coef F ψ μ Φ (fun x => Φ (-x)) w := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have key : ∀ y, Φ (y + u.1) = ψ (a - (y ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2))) * Φ y := fun y => by
    have := congrFun h y
    simp only [schr, Pi.smul_apply, smul_eq_mul] at this
    rw [sub_eq_neg_add, AddChar.map_add_eq_mul, mul_assoc, ← this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have key' : ∀ x, Φ (-(x + u.1)) = ψ (-(a - ((-(x + u.1)) ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)))) * Φ (-x) := fun x => by
    have := key (-(x + u.1))
    rw [show -(x + u.1) + u.1 = -x by abel] at this
    rw [this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  unfold coef
  rw [← integral_const_mul, ← integral_add_right_eq_self _ u.1]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [schr]
  rw [add_right_comm x u.1 w.1, key, key', map_mul, conj_psi hn]
  have e : ∀ p q s t t' : AF F, ∀ A B : ℂ, p + q + s = t + t' → ψ p * (ψ q * A) * (ψ s * B) = ψ t * (ψ t' * A * B) := by
    intro p q s t t' A B e
    have := congrArg ψ e
    simp only [AddChar.map_add_eq_mul] at this
    linear_combination A * B * this
  refine e _ _ _ _ _ _ _ ?_
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  simp only [add_dotProduct, neg_dotProduct]
  linear_combination (-(u.1 ⬝ᵥ u.2)) * h2

variable {v : Pl (F := F)}

theorem indep_of_rest {φ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ} (h : Rest (evFin F v) φ r) : Indep v r :=
  fun x t => h.1 x _ ((at_iff _).2 (funext fun i => (ep_mul _).trans (by rw [evFin_atPlace])))

theorem acts_schr (ψ : AddChar (AF F) ℂ) {w : (κ → AF F) × (κ → AF F)} (hw : ep v • w = w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (schr (psv v ψ) (evP v w) φ) := fun r hr => by
  rw [schr_tens ψ w _ (indep_of_rest hr), offP_eq, sub_smul, hw, one_smul, sub_self, schr_zero]

end W

open W

theorem det_X {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact hasSig_det (h.sig w) (by
    rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero])

theorem hermitian_form_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact hasSig_det (h.sig w) (by
    rw [det_smul, show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero,
      mul_zero])

theorem soCut_of : SoCut := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ
  classical
  obtain ⟨hφ, ι, hι, hz⟩ := hφ
  have h := hP.base.cm
  haveI := h.1
  have hψ := isCharAF hP.base.std
  generalize B.τ₁ = t at *
  generalize B.v₁ = v at *
  generalize B.ψ = ψ at *
  have hc : Continuous (psv v ψ) := hψ.1.comp cont_at
  obtain ⟨b, hb⟩ := (GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).1 v
  haveI := nonarch_field (Fv F v)
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  obtain ⟨m, g, hsum, hg⟩ := exists_cut (v.adicCompletionIntegers F)
    (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v))
    (fun U hU => by
      obtain ⟨a, ha⟩ := GlobalTheory.SplitWeil.exists_cball_subset hU
      exact ⟨a, a.ne_zero, ha (by simp [GlobalTheory.SplitWeil.cball])⟩)
    (psv v ψ) (isLocallyConstant_addChar _ hc) (b := b) hb (hι.bij.mapsTo hφ) hz
  choose χ hχ hχg using fun i => hι.bij.surjOn (hg i).1
  have hu : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), J.det ≠ 0 → ∃ P : GL (Fin m) (Fv F v), P.1 = J.map t := fun J hJ =>
    ⟨GeneralLinearGroup.mkOfDetNeZero (J.map t) (by
      rw [show (J.map t).det = t J.det from ((t : E →+* Fv F v).map_det J).symm]
      exact (map_ne_zero t).2 hJ), rfl⟩
  obtain ⟨P, hP'⟩ := hu _ (det_X hP.herm)
  obtain ⟨Q, hQ⟩ := hu _ (hermitian_form_det_ne_zero hP.skew)
  have hco : ∀ u, coB σ X W t u = -(P.1 * u.map (piW (t.comp σ)) * Q.1ᵀ) := fun u => by rw [coB, hP', hQ]
  have QQ : (Q⁻¹).1ᵀ * Q.1ᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have coU : ∀ A Y, coB σ X W t (spM h t A (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) = Y := fun A Y => by
    rw [hco, spM_snd, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc, QQ, Matrix.mul_one]
  have epU : ∀ A A' : Matrix (Fin n) (Fin d) (Fv F v), ep v • spM h t A A' = spM h t A A' := fun A A' => by
    have := spM_off h t A A'
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e1 : ∀ u : Matrix (Fin n) (Fin d) (AE F E), -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) *
      (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = coB σ X W t u := fun u => by simp [coB]
  have sy : ∀ (U : Matrix (Fin n) (Fin d) (Fv F v)) z, symp (cA σ) (-1) (incM F X.J) (incM F W.J) z
      (spM h t (-U) 0) = atPlace v (trace (coB σ X W t z * Uᵀ)) := fun U z => by
    have := ev_symp h t hP.herm.herm hP.skew.skew z (spM h t (-U) 0)
    rw [spM_fst, neg_neg, hco (spM h t (-U) 0), spM_snd] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, trace_zero, sub_zero] at this
    rw [← this, ← ep_mul, M.co.form]
    conv_lhs => rw [← epU, map_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]
  refine ⟨m, χ, hι.bij.injOn hφ (Submodule.sum_mem _ fun i _ => hχ i) ?_, fun i => ⟨⟨hχ i, ι, hι, fun Y hY => ?_⟩, ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, hsum]
      exact Finset.sum_congr rfl fun i _ => (hχg i).symm
  · rw [hχg]
    exact (hg i).2.1 Y (hz Y hY)
  intro r hr μ hμ z hzr
  obtain ⟨Y₀, hY₀⟩ := (hg i).2.2
  obtain ⟨U, hU, hU'⟩ := hY₀ (coB σ X W t z) fun h' => hzr (rank_of_mul _ _ _ (rank_neg_full h'))
  have hw : ep v • M.co.e (spM h t (-U) 0) = M.co.e (spM h t (-U) 0) := by rw [← map_smul, epU]
  have ha := acts_schr ψ hw (χ i)
  have hs := schr_mem_SB hc (evP v (M.co.e (spM h t (-U) 0))) (hχ i)
  have eig : schr (psv v ψ) (evP v (M.co.e (spM h t (-U) 0))) (χ i) = psv v ψ (trace (Y₀ * Uᵀ)) • χ i := by
    refine hι.bij.injOn hs (Submodule.smul_mem _ _ (hχ i)) (funext fun Y => ?_)
    have := hι.mult _ ((at_iff _).2 (epU _ _)) (spM_snd h t _ _) _ (hχ i) _ hs ha
      (spM h t 0 (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) ((at_iff _).2 (epU _ _)) (spM_fst h t _ _)
    simp only [e1] at this
    rw [sy, coU, ← psv_apply] at this
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, hχg]
    by_cases h0 : g i Y = 0
    · simp [h0]
    · rw [hU Y h0]
  have hΦ := ha r hr
  rw [eig] at hΦ
  have := coef_eigen hψ.2.1 μ (tens (evFin F v) (χ i) r) _ (M.co.e z) (atPlace v (trace (Y₀ * Uᵀ)))
    (hΦ.trans (funext fun x => mul_assoc _ _ _))
  rw [← neg_sub, ← M.co.form, sy, ← map_add (f := _), ← map_neg, ← map_add (f := _), ← psv_apply] at this
  by_contra h0
  apply hU'
  have h1 := (mul_eq_right₀ h0).1 this.symm
  rw [← inv_eq_one, ← AddChar.map_neg_eq_inv, ← h1]
  congr 1
  rw [Matrix.sub_mul, Matrix.add_mul, trace_sub, trace_add]
  ring

end PositivityTheory.ThKEst
end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.IntMvPolynomialCoeffAbsSumMulLe
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_lam {n r : ℕ} {lam : Fin n → (Fin r → ℝ) →ₗ[ℝ] ℝ} {ix iy : Fin r ↪ Fin n} (h1 : ∀ i j, ix i ≠ iy j)
    (h2 : ∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) (h3 : ∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0)
    (f : ℝ → ℝ) (t : Fin r → ℝ) :
    ∑ k, f (lam k t) = ∑ i, f (t i) + ∑ i, f (-t i) + ((n : ℝ) - 2 * r) * f 0 := by
  have hinj : Function.Injective (Sum.elim ix iy) :=
    Function.Injective.sumElim ix.injective iy.injective h1
  have := Fintype.sum_of_injective _ hinj (fun i => f (lam (Sum.elim ix iy i) t) - f 0) (fun k => f (lam k t) - f 0)
    (fun k hk => by
      rw [h3 k fun i => ⟨fun h => hk ⟨.inl i, h⟩, fun h => hk ⟨.inr i, h⟩⟩]
      simp) (fun _ => rfl)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h2, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add] at this
  linarith

def l1 {a b : Type} [Fintype a] [Fintype b] (A : Matrix a b ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

theorem weightAbsEntrySum_nonneg {a b : Type} [Fintype a] [Fintype b] (A : Matrix a b ℂ) : 0 ≤ l1 A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem intMvPolynomialCoeffAbsSum_mul_le {a b c : Type} [Fintype a] [Fintype b] [Fintype c] (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    l1 (A * B) ≤ l1 A * l1 B := by
  unfold l1
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(A * B) i j‖ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ :=
        Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul_le _ _))
    _ = ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ k, ‖A i k‖ * ∑ k, ∑ j, ‖B k j‖ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem sz_nonneg {n d : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : Ten F E n d) : 0 ≤ sz τ z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sz_mul_le {n d : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w) (P : Ten F E n n) (Q : Ten F E d d) (z : Ten F E n d) :
    sz τ (P * z * Q) ≤ sz τ P * sz τ Q * sz τ z := by
  have e : ∀ {a b : ℕ} (y : Ten F E a b), sz τ y = ∑ w, l1 (y.map (piInf (τ w))) := fun _ => rfl
  have le : ∀ {a b : ℕ} (y : Ten F E a b) w, l1 (y.map (piInf (τ w))) ≤ sz τ y := fun y w =>
    Finset.single_le_sum (f := fun w => l1 (y.map (piInf (τ w)))) (fun _ _ => weightAbsEntrySum_nonneg _) (Finset.mem_univ w)
  rw [e (P * z * Q), e z, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Matrix.map_mul, Matrix.map_mul]
  refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ?_
  have h1 := intMvPolynomialCoeffAbsSum_mul_le (P.map (piInf (τ w))) (z.map (piInf (τ w)))
  calc _ ≤ sz τ P * l1 (z.map (piInf (τ w))) * sz τ Q :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le P w) (weightAbsEntrySum_nonneg _))) (le Q w) (weightAbsEntrySum_nonneg _)
          (mul_nonneg (sz_nonneg _ _) (weightAbsEntrySum_nonneg _))
    _ = _ := by ring

omit [NumberField E] in
theorem incM_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

omit [NumberField E] in
theorem incM_one {a : ℕ} : incM F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

omit [NumberField E] in
theorem inv_mul_tor {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {fr : Frame σ J} (hfr : fr.IsGood) {b : GL (Fin n) E}
    {lam : Fin n → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ}
    (hb : ∀ t, mat (fr.a t) * incM F b.1 =
      incM F b.1 * Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t))) (s : Fin fr.r → ℝ) :
    incM F (b⁻¹).1 * mat (fr.a s)⁻¹ =
      (Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (-lam k s))) * incM F (b⁻¹).1 := by
  have h0 : fr.a 0 = 1 := by
    have := hfr.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h1 : (fr.a s)⁻¹ = fr.a (-s) := by
    rw [inv_eq_iff_mul_eq_one, ← hfr.add, add_neg_cancel, h0]
  have h2 := hb (-s)
  simp only [map_neg] at h2
  have h3 : incM F b.1 * incM F (b⁻¹).1 = 1 := by rw [← incM_mul, Units.mul_inv, incM_one]
  have h4 : incM F (b⁻¹).1 * incM F b.1 = 1 := by rw [← incM_mul, Units.inv_mul, incM_one]
  rw [h1]
  calc _ = incM F (b⁻¹).1 * (mat (fr.a (-s)) * incM F b.1) * incM F (b⁻¹).1 := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
    _ = _ := by rw [h2, ← Matrix.mul_assoc, h4, Matrix.one_mul]

theorem diag_coords (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {J' : Matrix (Fin d) (Fin d) E} {fr : Frame σ J} {fr' : Frame σ J'} (hfr : fr.IsGood) (hfr' : fr'.IsGood)
    {b : GL (Fin n) E} {lam : Fin n → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ}
    (hb : ∀ t, mat (fr.a t) * incM F b.1 =
      incM F b.1 * Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t)))
    {b' : GL (Fin d) E} {lam' : Fin d → (Fin fr'.r → ℝ) →ₗ[ℝ] ℝ}
    (hb' : ∀ t, mat (fr'.a t) * incM F b'.1 =
      incM F b'.1 * Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam' k t)))
    {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∃ (m : ℕ) (K : ℝ), 0 < m ∧ 1 ≤ K ∧ ∀ s t (x : Matrix (Fin n) (Fin d) E),
      ((∃ y ∈ C, At (evI F) (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ - y)) →
        ∀ k l, IsIntegral ℤ ((m : E) * ((b⁻¹).1 * x * (b'⁻¹).1ᵀ) k l)) ∧
      ∑ w, ∑ k, ∑ l, Real.exp (-(lam k s + lam' l t)) * ‖(τ w).1 (((b⁻¹).1 * x * (b'⁻¹).1ᵀ) k l)‖ ≤
        K * sz τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P := incM F (b⁻¹).1 with hP
  set Q := (incM F (b'⁻¹).1)ᵀ with hQ
  have hc : ∀ k l, Continuous fun y : Ten F E n d => (P * y * Q) k l := fun k l =>
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem k l
  obtain ⟨m, hm, h⟩ := denom_AE (isCompact_iUnion fun k => isCompact_iUnion fun l => hC.image (hc k l))
  refine ⟨m, max 1 (sz τ P * sz τ Q), hm, le_max_left _ _, fun s t x => ?_⟩
  set z := mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ with hz
  set ξ := (b⁻¹).1 * x * (b'⁻¹).1ᵀ with hξ
  have key : ∀ k l, (P * z * Q) k l = algebraMap (AF F) (AE F E) (rId F (-lam k s)) * inclR (F := F) (AF F) (ξ k l) *
      algebraMap (AF F) (AE F E) (rId F (-lam' l t)) := by
    intro k l
    have e1 : P * z * Q = (P * mat (fr.a s)⁻¹) * incM F x * (incM F (b'⁻¹).1 * mat (fr'.a t)⁻¹)ᵀ := by
      simp only [hz, hQ, Matrix.transpose_mul, Matrix.mul_assoc]
    have e2 : incM F ξ = P * incM F x * Q := by
      rw [hξ, incM_mul, incM_mul]; rfl
    rw [e1, hP, inv_mul_tor hfr hb, inv_mul_tor hfr' hb', Matrix.transpose_mul, Matrix.diagonal_transpose, ← hP, ← hQ,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ P, Matrix.mul_assoc _ (P * _), ← e2, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    rfl
  constructor
  · rintro ⟨y, hy, hzy⟩ k l
    refine h _ ⟨(P * y * Q) k l, Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨l, y, hy, rfl⟩⟩, ?_⟩
    have h1 : uFin F • z = uFin F • y := by
      rw [← sub_eq_zero, ← smul_sub]
      exact hzy _ evI_uFin
    have h2 : uFin F • (P * z * Q) = uFin F • (P * y * Q) := by
      have e : ∀ u : Ten F E n d, uFin F • (P * u * Q) = P * (uFin F • u) * Q := fun u => by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [e, e, h1]
    have h3 := congrFun (congrFun h2 k) l
    rw [Matrix.smul_apply, Matrix.smul_apply, key, mul_comm, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, smul_smul,
      uFin_mul_rId, uFin_mul_rId] at h3
    exact h3
  · refine le_trans (le_of_eq ?_) ((sz_mul_le τ P Q z).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sz_nonneg _ _)))
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [key, map_mul, map_mul, piInf_rId, piInf_rId, piInf_inclR, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le, neg_add,
      Real.exp_add]
    ring

theorem norm_emb (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (φ : E →+* ℂ) :
    ∃ w, ∀ x, ‖φ x‖ = ‖(τ w).1 x‖ := by
  have := h.1
  let w : InfinitePlace F := InfinitePlace.mk (φ.comp (algebraMap F E))
  have hw : φ.comp (algebraMap F E) = w.embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal w))).symm
  refine ⟨w, fun x => ?_⟩
  have e : ∀ t : EmbOver E w, t.1 x = infEmb t (1 ⊗ₜ x) := fun t => by rw [infEmb_tmul, map_one, one_mul]
  rw [e (τ w), show φ x = infEmb (⟨φ, hw⟩ : EmbOver E w) (1 ⊗ₜ x) from e ⟨φ, hw⟩]
  rcases infEmb_eq_or_conj h (τ w) ⟨φ, hw⟩ with h1 | h1 <;> rw [h1]
  exact RCLike.norm_conj _

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LatSumRedH
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ht_mul_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : ht (g * h) ≤ ht g * ht h :=
  heightGL_mul_le F g.1 h.1

theorem ht_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ht g⁻¹ = ht g := heightGL_inv F g.1

theorem one_le_ht {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : 1 ≤ ht g := one_le_heightGL F g.1

theorem exp_le_ht (hT : GrpTop) (hc : IsCMExt F E σ) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J)
    {fr : Frame σ J} (h2 : TorHt fr) {Ω : Set (UA σ J)} (hΩ : IsCompact Ω) :
    ∃ (A : ℝ) (k : ℕ), 0 ≤ A ∧ ∀ h : UA σ J, ∀ δ ∈ ratU σ J, ∀ t ∈ Cone fr.r, ∀ κ ∈ Ω, δ * h = fr.a t * κ →
      Real.exp (∑ i, t i) ≤ A * (ht h : ℝ) ^ k := by
  obtain ⟨C, k, hC⟩ := h2
  obtain ⟨B, hB⟩ := (hT F E σ hc d J hJ).2.2.2.2.2.2.2 Ω hΩ
  refine ⟨max C 0 * (B : ℝ) ^ k, k, by positivity, fun h δ hδ t ht' κ hκ e => ?_⟩
  have e2 : δ⁻¹ * fr.a t = h * κ⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, e, mul_inv_cancel_right]
  have h3 := (hC t ht').2 δ⁻¹ (inv_mem hδ)
  rw [e2] at h3
  have h4 : (ht (h * κ⁻¹) : ℝ) ≤ B * ht h := by
    have hb : ht κ⁻¹ ≤ B := by rw [ht_inv]; exact hB κ hκ
    have := (ht_mul_le h κ⁻¹).trans (mul_le_mul_right hb _)
    rw [mul_comm] at this
    exact_mod_cast this
  calc _ ≤ C * (ht (h * κ⁻¹) : ℝ) ^ k := h3
    _ ≤ max C 0 * ((B : ℝ) * ht h) ^ k := by gcongr; exact le_max_left _ _
    _ = _ := by rw [mul_pow, mul_assoc]

theorem latSum_redH (hT : GrpTop) (hS : SiegelAll) (hI : LatInv) (hK : LatCpt) (hA : LatArch) (hc : IsCMExt F E σ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    (hJ : EpsHerm σ J) (hJ' : EpsHerm σ J') (N : ℕ) :
    ∃ k : ℕ, ∀ C, IsCompact C → ∃ (C' : Set (Ten F E n d)) (K : ℝ), IsCompact C' ∧ 0 ≤ K ∧ ∀ (g : UA σ J) (h : UA σ J'),
      latSum τ C N Set.univ g h ≤ ENNReal.ofReal ((K * (ht h : ℝ) ^ k) ^ 2) * latSum τ C' N Set.univ g (1 : UA σ J') := by
  obtain ⟨fr, hg, -, ⟨Ω, hΩ, hcov⟩, -, hht⟩ := hS F E σ hc d J' hJ'
  obtain ⟨A, k, hA0, hAk⟩ := exp_le_ht hT hc hJ' hht hΩ
  refine ⟨k * N, fun C hC => ?_⟩
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc τ n d J J' hJ hJ' {1} Ω isCompact_singleton hΩ C N hC
  obtain ⟨C₂, K₂, hC₂, h₂⟩ := hA F E σ hc τ n d J J' hJ hJ' fr hg C₁ N hC₁
  refine ⟨C₂, K₁ * K₂ * A ^ N + 1, hC₂, by positivity, fun g h => ?_⟩
  obtain ⟨δ, hδ, t, ht', κ, hκ, e⟩ := hcov h
  have e1 := hI F E σ hc τ n d J J' hJ hJ' C N Set.univ (by simp) 1 (one_mem _) δ hδ g h
  rw [← e1, e, one_mul]
  have e2 := h₁ Set.univ g (fr.a t) 1 rfl κ hκ
  rw [mul_one] at e2
  refine e2.trans ((mul_le_mul_right (h₂ Set.univ g t ht') _).trans ?_)
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (1 : ℝ) ≤ (ht h : ℝ) ^ (k * N) := one_le_pow₀ (by exact_mod_cast one_le_ht h)
  have h3 : Real.exp (N * ∑ j, t j) ≤ A ^ N * (ht h : ℝ) ^ (k * N) := by
    rw [Real.exp_nat_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hAk h δ hδ t ht' κ hκ e) _
  have h4 : (0 : ℝ) ≤ K₁ * K₂ * A ^ N := by positivity
  have h5 : (1 : ℝ) ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
  calc (K₁ : ℝ) * K₂ * Real.exp (N * ∑ j, t j) ≤ K₁ * K₂ * (A ^ N * (ht h : ℝ) ^ (k * N)) := by gcongr
    _ ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
    _ ≤ _ := by nlinarith

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {d : ℕ} {W : Spc F E d}

def IsLie (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w, (Y w)ᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * (Y w).map star = 0

def Gen (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (γ : Multiplicative ℝ →* UA σ W.J)
    (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w (t : ℝ), (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w)


variable (W) in
def UMG (f : UA σ W.J → ℂ) : Prop :=
  ∃ (k : ℕ) (S : Set (UA σ W.J → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧ (∃ C : ℝ, ∀ h, ‖f₁ h‖ ≤ C * (ht h : ℝ) ^ k) ∧
    ∀ γ ∈ Lines σ W, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f₁ (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0


variable (W) in
def SmoothFin (τ : ∀ w : InfinitePlace F, EmbOver E w) (f : UA σ W.J → ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (τ w)) = 1) → ∀ h, f (h * u) = f h

def LeftInv {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ γ ∈ ratU σ J, ∀ h, f (γ * h) = f h

def Rapid {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C

end

def LineGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ γ ∈ Lines σ W, ∃ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y ∧ Gen τ W γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y → ∃ γ ∈ Lines σ W, Gen τ W γ Y ∧ ∀ γ' ∈ Lines σ W, Gen τ W γ' Y → γ' = γ

def LinDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∃ (m : ℕ) (β : Fin m → (Multiplicative ℝ →* UA σ W.J)) (c : Fin m → (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ), (∀ i, β i ∈ Lines σ W) ∧ ∀ (f : UA σ W.J → ℂ) (f' : Fin m → UA σ W.J → ℂ), (∀ i, Continuous (f' i) ∧ ∀ h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0) → ∀ γ ∈ Lines σ W, ∀ Y, Gen τ W γ Y → ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ i, (c i Y : ℂ) * f' i h) 0

def UMGSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, UMG W f → ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* UA σ W.J)), (∀ i, γ i ∈ Lines σ W) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod)

def UMGLin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f f' : UA σ W.J → ℂ, UMG W f → UMG W f' → ∀ a b : ℂ, UMG W (a • f + b • f')

def CuspRapid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, LeftInv f → UMG W f → SmoothFin W τ f → PositivityTheory.ThKEnd.IsCusp W f → Rapid f

def Level : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = pureA F f φ

def IDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, (∀ γ ∈ Lines σ W, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ h, HasDerivAt (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) (M.I om (pureA F f₁ φ) h) 0) ∧ ∀ γ ∈ Lines σ X, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ ∧ M.I om (pureA F f₁ φ) = 0

def IInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), LeftInv (M.I om Φ) ∧ (∀ g, M.I om (om (g, 1) Φ) = M.I om Φ) ∧ ∀ h h', M.I om (om (1, h') Φ) h = M.I om Φ (h * h')

def IUMG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, UMG W (M.I om (pureA F f φ)) ∧ SmoothFin W B.emb (M.I om (pureA F f φ))

end PositivityTheory.ThKEst

end
end

