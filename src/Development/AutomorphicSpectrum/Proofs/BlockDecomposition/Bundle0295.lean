module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBound
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeSubmod

theorem exists_leftInv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ K) (h : LinearIndependent K Mᵀ) : ∃ Y : Matrix κ ι K, Y * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := by
    have : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
    exact this
  obtain ⟨g, hg⟩ := M.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 : LinearMap.toMatrix' (g ∘ₗ M.mulVecLin) = LinearMap.toMatrix' g * M := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← h2, hg]
  simp

theorem map_fromCols {R S ι κ κ' : Type} (f : R → S) (P : Matrix ι κ R) (Q : Matrix ι κ' R) :
    (fromCols P Q).map f = fromCols (P.map f) (Q.map f) := by
  ext i (j | j) <;> rfl

theorem log_ineq {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (N : Fam K ι) (hN : IsWedge N) (hS : WedgeSub)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix ι κ₀ K) (A : Matrix ι κ₁ K) (C : Matrix ι κ₂ K)
    (h0 : N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C)) ≠ 0) (h1 : N κ₀ B ≠ 0)
    (h2 : N (κ₀ ⊕ κ₁) (fromCols B A) ≠ 0) (h3 : N (κ₀ ⊕ κ₂) (fromCols B C) ≠ 0) :
    Real.log (N (κ₀ ⊕ (κ₁ ⊕ κ₂)) (fromCols B (fromCols A C))) + Real.log (N κ₀ B) ≤
      Real.log (N (κ₀ ⊕ κ₁) (fromCols B A)) + Real.log (N (κ₀ ⊕ κ₂) (fromCols B C)) := by
  have p0 := lt_of_le_of_ne (hN.nonneg _ (fromCols B (fromCols A C))) h0.symm
  have p1 := lt_of_le_of_ne (hN.nonneg _ B) h1.symm
  rw [← Real.log_mul h0 h1, ← Real.log_mul h2 h3]
  exact Real.log_le_log (mul_pos p0 p1) (hS K ι N hN _ _ _ B A C)

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem frame_leftInv {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (M : Matrix (Fin n) κ E)
    (h : LinearIndependent E Mᵀ) :
    ∃ Y : Matrix κ (Fin n) (Ad E), Y * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) = 1 := by
  obtain ⟨Y, hY⟩ := exists_leftInv M h
  refine ⟨Y.map (algebraMap E (Ad E)) * x.val, ?_⟩
  have hx : x.val * (x⁻¹ : GA E n).val = 1 := Units.mul_inv x
  have hm : Y.map (algebraMap E (Ad E)) * M.map (algebraMap E (Ad E)) = 1 := by
    rw [← Matrix.map_mul, hY, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Y.map (algebraMap E (Ad E)) * x.val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)))
      = Y.map (algebraMap E (Ad E)) * (x.val * (x⁻¹ : GA E n).val) * M.map (algebraMap E (Ad E)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hx, Matrix.mul_one, hm]

theorem frame_fromCols {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : GA E n) (P : Matrix (Fin n) κ E)
    (Q : Matrix (Fin n) κ' E) :
    (x⁻¹ : GA E n).val * (fromCols P Q).map (algebraMap E (Ad E)) =
      fromCols ((x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E))) ((x⁻¹ : GA E n).val * Q.map (algebraMap E (Ad E))) := by
  rw [map_fromCols, Matrix.mul_fromCols]

theorem sum_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (P : Matrix (Fin n) κ₀ (Ad E)) (Q : Matrix (Fin n) κ₁ (Ad E)) (R : Matrix (Fin n) κ₂ (Ad E))
    {Y₀ : Matrix (κ₀ ⊕ (κ₁ ⊕ κ₂)) (Fin n) (Ad E)} (h₀ : Y₀ * fromCols P (fromCols Q R) = 1)
    {Y₁ : Matrix κ₀ (Fin n) (Ad E)} (h₁ : Y₁ * P = 1)
    {Y₂ : Matrix (κ₀ ⊕ κ₁) (Fin n) (Ad E)} (h₂ : Y₂ * fromCols P Q = 1)
    {Y₃ : Matrix (κ₀ ⊕ κ₂) (Fin n) (Ad E)} (h₃ : Y₃ * fromCols P R = 1) :
    (∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) +
        ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w)))) +
      (∑ v, Real.log (nI (P.map (cV v))) + ∑ᶠ w, Real.log (nF (P.map (cW w)))) ≤
    (∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w)))) +
      (∑ v, Real.log (nI ((fromCols P R).map (cV v))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w)))) := by
  obtain ⟨i₀, f₀, s₀⟩ := hFS E _ _ _ Y₀ h₀
  obtain ⟨i₁, f₁, s₁⟩ := hFS E _ _ _ Y₁ h₁
  obtain ⟨i₂, f₂, s₂⟩ := hFS E _ _ _ Y₂ h₂
  obtain ⟨i₃, f₃, s₃⟩ := hFS E _ _ _ Y₃ h₃
  have fin : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (T : Matrix (Fin n) κ (Ad E)),
      {w | nF (T.map (cW w)) ≠ 1}.Finite →
      (Function.support fun w => Real.log (nF (T.map (cW w)))).Finite := by
    intro κ _ _ T hT
    refine hT.subset fun w hw h1 => hw ?_
    simp only [Function.mem_support] at hw
    exact absurd (by rw [h1, Real.log_one]) hw
  have inf : ∑ v, Real.log (nI ((fromCols P (fromCols Q R)).map (cV v))) + ∑ v, Real.log (nI (P.map (cV v))) ≤
      ∑ v, Real.log (nI ((fromCols P Q).map (cV v))) + ∑ v, Real.log (nI ((fromCols P R).map (cV v))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have a₀ := i₀ v
    have a₂ := i₂ v
    have a₃ := i₃ v
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nI A) (hI _) hS _ _ _ a₀ (i₁ v) a₂ a₃
  have finp : ∑ᶠ w, Real.log (nF ((fromCols P (fromCols Q R)).map (cW w))) + ∑ᶠ w, Real.log (nF (P.map (cW w))) ≤
      ∑ᶠ w, Real.log (nF ((fromCols P Q).map (cW w))) + ∑ᶠ w, Real.log (nF ((fromCols P R).map (cW w))) := by
    rw [← finsum_add_distrib (fin _ s₀) (fin _ s₁), ← finsum_add_distrib (fin _ s₂) (fin _ s₃)]
    refine finsum_le_finsum' ((fin _ s₀).union (fin _ s₁) |>.subset (Function.support_add _ _))
      ((fin _ s₂).union (fin _ s₃) |>.subset (Function.support_add _ _)) fun w => ?_
    have a₀ := f₀ w
    have a₂ := f₂ w
    have a₃ := f₃ w
    rw [map_fromCols] at a₂ a₃
    rw [map_fromCols, map_fromCols] at a₀
    simp only [Pi.add_apply]
    rw [map_fromCols, map_fromCols, map_fromCols, map_fromCols]
    exact log_ineq (fun _ _ _ A => nF A) (hF _ _) hS _ _ _ a₀ (f₁ w) a₂ a₃
  linarith

theorem degG_ineq (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (x : GA E n)
    {κ₀ κ₁ κ₂ : Type} [Fintype κ₀] [DecidableEq κ₀] [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (B : Matrix (Fin n) κ₀ E) (A : Matrix (Fin n) κ₁ E) (C : Matrix (Fin n) κ₂ E)
    (l₀ : LinearIndependent E (fromCols B (fromCols A C))ᵀ) (l₁ : LinearIndependent E Bᵀ)
    (l₂ : LinearIndependent E (fromCols B A)ᵀ) (l₃ : LinearIndependent E (fromCols B C)ᵀ) :
    degG x (fromCols B A) + degG x (fromCols B C) ≤ degG x B + degG x (fromCols B (fromCols A C)) := by
  obtain ⟨Y₀, h₀⟩ := frame_leftInv x _ l₀
  obtain ⟨Y₁, h₁⟩ := frame_leftInv x _ l₁
  obtain ⟨Y₂, h₂⟩ := frame_leftInv x _ l₂
  obtain ⟨Y₃, h₃⟩ := frame_leftInv x _ l₃
  rw [frame_fromCols, frame_fromCols] at h₀
  rw [frame_fromCols] at h₂ h₃
  have key := sum_ineq hF hI hS hFS _ _ _ h₀ h₁ h₂ h₃
  simp only [degG, frame_fromCols]
  linarith

theorem degSubmod_of (hF : WedgeF) (hI : WedgeI) (hS : WedgeSub) (hFS : FinSupp) (hB : DegBasisG) (hT : TwoBases) :
    DegSubmod := by
  intro E _ _ _ n x W W'
  obtain ⟨a, b, c, B, A, C, l₀, e₁, e₂, e₃, e₄⟩ := hT E n W W'
  have l₂ : LinearIndependent E (fromCols B A)ᵀ := by
    have : (fromCols B A)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inl := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)
  have l₃ : LinearIndependent E (fromCols B C)ᵀ := by
    have : (fromCols B C)ᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.map id Sum.inr := by
      funext j; rcases j with j | j <;> rfl
    rw [this]
    exact l₀.comp _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩)
  have l₁ : LinearIndependent E Bᵀ := by
    have : Bᵀ = (fromCols B (fromCols A C))ᵀ ∘ Sum.inl := by
      funext j; rfl
    rw [this]
    exact l₀.comp _ Sum.inl_injective
  have d₀ := hB E n _ x _ l₀
  have d₁ := hB E n _ x _ l₁
  have d₂ := hB E n _ x _ l₂
  have d₃ := hB E n _ x _ l₃
  rw [e₄] at d₀
  rw [e₁] at d₁
  rw [e₂] at d₂
  rw [e₃] at d₃
  rw [← d₀, ← d₁, ← d₂, ← d₃]
  exact degG_ineq hF hI hS hFS x B A C l₀ l₁ l₂ l₃

end GlobalTheory.CompanionTheory.DegreeSubmod

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegMoveProof

theorem log_step {a b c : ℝ} {k n : ℕ} (hkn : k ≤ n) (ha : 0 < a) (hb : 0 < b) (h : a ≤ c ^ k * b) :
    Real.log a ≤ n * Real.posLog c + Real.log b := by
  have hp : 0 < c ^ k * b := lt_of_lt_of_le ha h
  have hck : c ^ k ≠ 0 := fun h0 => by simp [h0] at hp
  have h1 : Real.log a ≤ Real.log (c ^ k * b) := Real.log_le_log ha h
  rw [Real.log_mul hck hb.ne', Real.log_pow] at h1
  have h2 : Real.log c ≤ Real.posLog c := le_max_right 0 (Real.log c)
  have h3 : (0 : ℝ) ≤ Real.posLog c := Real.posLog_nonneg
  have h4 : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h5 : (k : ℝ) * Real.log c ≤ n * Real.posLog c :=
    (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)).trans (mul_le_mul_of_nonneg_right h4 h3)
  linarith

theorem finsum_bound {α : Type} {f g s : α → ℝ} {c : ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (hs : (Function.support s).Finite) (h : ∀ a, f a ≤ c * s a + g a) :
    ∑ᶠ a, f a ≤ c * ∑ᶠ a, s a + ∑ᶠ a, g a := by
  classical
  let T : Finset α := hf.toFinset ∪ hg.toFinset ∪ hs.toFinset
  rw [finsum_eq_sum_of_support_subset f (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset g (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset s (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => h a

theorem sz_sq_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : sz g ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖g p.1 p.2‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n × Fin n) with he | hne
  · simp [sz, Real.iSup_of_isEmpty]
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖)
    rw [sz, ← hp]
    exact le_ciSup (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖ ^ 2) (Set.finite_range _).bddAbove p

theorem nI_nonneg {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  open ComplexOrder in
  have h : 0 ≤ (Aᴴ * A).det := (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg
  exact (Complex.le_def.1 h).1

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem exists_left_inv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ N : Matrix (Fin k) (Fin n) K, N * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_iff.2 h
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h1 : LinearMap.toMatrix' (f ∘ₗ M.mulVecLin) = 1 := by rw [hf]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n k : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem inf_step (hI : MulI) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (v : InfinitePlace E) (h0 : nI ((h * A).map (cV v)) ≠ 0) (h1 : nI (A.map (cV v)) ≠ 0) :
    Real.log (nI ((h * A).map (cV v))) ≤
      n * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2)) +
        Real.log (nI (A.map (cV v))) := by
  have hm : (h * A).map (cV v) = h.map (cV v) * A.map (cV v) := Matrix.map_mul
  have hle := (hI (Fin n) (Fin n) (Fin k) (A.map (cV v))).1 (h.map (cV v))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  have hs := log_step hkn (lt_of_le_of_ne (nI_nonneg _) h0.symm) (lt_of_le_of_ne (nI_nonneg _) h1.symm) hle
  refine hs.trans ?_
  have h2 : Real.posLog ((n : ℝ) * n * sz (h.map (cV v)) ^ 2) ≤
      Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2) :=
    Real.posLog_mul.trans (add_le_add le_rfl (Real.posLog_le_posLog (by nlinarith [sq_nonneg (sz (h.map (cV v)))]) (sz_sq_le _)))
  have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem fin_step (hF : MulF) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (w : HeightOneSpectrum (𝓞 E)) (h0 : nF ((h * A).map (cW w)) ≠ 0) (h1 : nF (A.map (cW w)) ≠ 0) :
    Real.log (nF ((h * A).map (cW w))) ≤
      n * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h p.1 p.2)‖) + Real.log (nF (A.map (cW w))) := by
  haveI := ultra w
  have hm : (h * A).map (cW w) = h.map (cW w) * A.map (cW w) := Matrix.map_mul
  have hle := (hF (w.adicCompletion E) (Fin n) (Fin n) (Fin k) (A.map (cW w))).1 (h.map (cW w))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  exact log_step hkn (lt_of_le_of_ne (nF_nonneg _) h0.symm) (lt_of_le_of_ne (nF_nonneg _) h1.symm) hle

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem frame_move (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) :
    (x⁻¹ * ratGL E n g * x : GA E n).val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) =
      (x⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) := by
  have h1 : (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := rfl
  rw [Matrix.map_mul, ← h1, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem core (hF : MulF) (hI : MulI) (hSz : SzFin) (hFS : FinSupp) (hkn : k ≤ n) (h : GA E n)
    (A : Matrix (Fin n) (Fin k) (Ad E)) (Y : Matrix (Fin k) (Fin n) (Ad E)) (hY : Y * A = 1) :
    ∑ v, Real.log (nI ((h.val * A).map (cV v))) + ∑ᶠ w, Real.log (nF ((h.val * A).map (cW w))) ≤
      (∑ v, Real.log (nI (A.map (cV v))) + ∑ᶠ w, Real.log (nF (A.map (cW w)))) +
        n * ((Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)) + n * logSizeM h.val := by
  have hY' : (Y * (h⁻¹ : GA E n).val) * (h.val * A) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹ : GA E n).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, hY]
  obtain ⟨a1, a2, a3⟩ := hFS E (Fin n) (Fin k) A Y hY
  obtain ⟨b1, b2, b3⟩ := hFS E (Fin n) (Fin k) (h.val * A) _ hY'
  have hinf := Finset.sum_le_sum (s := Finset.univ) fun v (_ : v ∈ Finset.univ) =>
    inf_step (E := E) hI hkn h.val A v (b1 v) (a1 v)
  have hfin := finsum_bound (c := (n : ℝ))
    (f := fun w => Real.log (nF ((h.val * A).map (cW w))))
    (g := fun w => Real.log (nF (A.map (cW w))))
    (s := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖))
    (b3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    (a3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    ((hSz E (Fin n) (Fin n) h.val).subset fun w hw => by
      by_contra hc
      apply hw
      exact max_eq_left (Real.log_nonpos (Real.iSup_nonneg fun _ => norm_nonneg _) (not_lt.1 hc)))
    fun w => fin_step hF hkn h.val A w (b2 w) (a2 w)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hinf
  have hS : logSizeM h.val = ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h.val p.1 p.2)‖ ^ 2) +
      ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖) := rfl
  rw [hS]
  nlinarith [hinf, hfin]

theorem lin_basisMat (W : Submodule E (Fin n → E)) : LinearIndependent E (basisMat W)ᵀ ∧
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  have hM : (basisMat W)ᵀ = W.subtype ∘ (Module.finBasis E W) := by
    funext j i
    rfl
  rw [hM]
  refine ⟨(Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem linearIndependent_image_span (g : GL (Fin n) E) (f : Fin k → Fin n → E) (hf : LinearIndependent E f) :
    LinearIndependent E (Matrix.toLin' g.val ∘ f) ∧
      Submodule.span E (Set.range (Matrix.toLin' g.val ∘ f)) = img g (Submodule.span E (Set.range f)) := by
  have inj : Function.Injective (Matrix.toLin' g.val) := fun a b hab => by
    have h1 := congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  refine ⟨hf.map' _ (LinearMap.ker_eq_bot.2 inj), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span]
  rfl

theorem lin_moved (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) (hM : LinearIndependent E Mᵀ) :
    LinearIndependent E (g.val * M)ᵀ ∧
      Submodule.span E (Set.range (g.val * M)ᵀ) = img g (Submodule.span E (Set.range Mᵀ)) := by
  have hG : (Matrix.toLin' g.val ∘ (Mᵀ : Fin k → Fin n → E)) = ((g.val * M)ᵀ : Fin k → Fin n → E) := by
    funext j i
    change (Matrix.toLin' g.val (fun i' => M i' j)) i = (g.val * M) i j
    rw [Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h1 := linearIndependent_image_span g Mᵀ hM
  rw [hG] at h1
  exact h1

theorem degMove_of : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  intro hF hI hSz hFS hB E _ _ _ n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), fun x g W => ?_⟩
  obtain ⟨hLI, hspan⟩ := lin_basisMat W
  obtain ⟨hLI', hspan'⟩ := lin_moved g (basisMat W) hLI
  rw [hspan] at hspan'
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have e1 : deg x (img g W) = degG x (g.val * basisMat W) := by rw [hB E n _ x _ hLI', hspan']
  have e2 : deg x W = degG x (basisMat W) := rfl
  have hY : (N.map (algebraMap E (Ad E)) * x.val) * ((x⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn (x⁻¹ * ratGL E n g * x) _ _ hY
  rw [frame_move] at hc
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg (x⁻¹ * ratGL E n g * x : GA E n).val
  have hS' := logSizeM_nonneg ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val
  have hL : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hsz : logSize (x⁻¹ * ratGL E n g * x) = logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val +
    logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val = S at *
  generalize logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 ≤ (n : ℝ) * (1 + S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegMoveProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomology
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.DsumCoh

variable {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K)

def inj (i : I) : Cx.Hom (E i) (Dsum E) (RingHom.id K) where
  f n := DirectSum.lof K I (fun i => (E i).X n) i
  comm n x := by
    change DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x) = _
    rw [DirectSum.lmap_lof]
    rfl

def prj (i : I) : Cx.Hom (Dsum E) (E i) (RingHom.id K) where
  f n := DirectSum.component K I (fun i => (E i).X n) i
  comm n x := by
    change (E i).d n (DirectSum.component K I (fun i => (E i).X n) i x) =
      DirectSum.component K I (fun i => (E i).X (n + 1)) i (DirectSum.lmap (fun i => (E i).d n) x)
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
      by_cases h : j = i
      · subst h
        simp only [DirectSum.component.lof_self]
      · rw [DirectSum.component.of, DirectSum.component.of, dite_eq_right h, dite_eq_right h, map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

def toH (n : ℕ) : (⨁ i, (E i).H n) →ₗ[K] (Dsum E).H n :=
  DirectSum.toModule K I _ fun i => (inj E i).mapH n

theorem prj_toH (n : ℕ) (i : I) (y : ⨁ i, (E i).H n) :
    (prj E i).mapH n (toH E n y) = DirectSum.component K I (fun i => (E i).H n) i y := by
  have hcl : ∀ (x y : (E i).X n) (hx : (E i).d n x = 0) (hy : (E i).d n y = 0), x = y →
      (E i).cls x hx = (E i).cls y hy := by
    rintro x _ _ _ rfl
    rfl
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j z =>
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
    have h1 : (Dsum E).d n ((inj E j).f n a) = 0 := CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E j) a ha
    rw [← DirectSum.lof_eq_of K, toH, DirectSum.toModule_lof, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E j) a ha h1,
      CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (prj E i) _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) _ h1)]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.component.lof_self]
      exact hcl _ _ _ _ (DirectSum.component.lof_self K _ _)
    · rw [DirectSum.component.of, dite_eq_right hji]
      rw [← CrystallineSemistableComparison.CechClassBoundaries.cls_zero' (K := E i) (n := n) (map_zero _)]
      refine hcl _ _ _ _ ?_
      show DirectSum.component K I (fun i ↦ (E i).X n) i (DirectSum.lof K I (fun i ↦ (E i).X n) j a) = 0
      rw [DirectSum.component.of, dite_eq_right hji]
  | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]

theorem toH_injective (n : ℕ) : Function.Injective (toH E n) := by
  refine (injective_iff_map_eq_zero (toH E n)).2 fun y hy ↦ ?_
  refine DirectSum.ext fun i ↦ ?_
  have h := prj_toH E n i y
  rw [hy, map_zero] at h
  rw [DirectSum.apply_eq_component K, ← h]
  rfl

theorem toH_surjective (n : ℕ) : Function.Surjective (toH E n) := by
  classical
  intro z
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj z
  have hc : ∀ i, (E i).d n ((prj E i).f n x) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (prj E i) x hx
  have hci : ∀ i, (Dsum E).d n ((inj E i).f n ((prj E i).f n x)) = 0 := fun i ↦ CrystallineSemistableComparison.CechClassBoundaries.cyc (inj E i) _ (hc i)
  have hsum : ∀ S : Finset I, ∀ h : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0,
      (Dsum E).cls (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) h =
        ∑ i ∈ S, (Dsum E).cls ((inj E i).f n ((prj E i).f n x)) (hci i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact CrystallineSemistableComparison.CechClassBoundaries.cls_zero' h
    | insert j S hj ih =>
      intro h
      have hS : (Dsum E).d n (∑ i ∈ S, (inj E i).f n ((prj E i).f n x)) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_eq_zero fun i _ ↦ hci i
      simp only [Finset.sum_insert hj]
      rw [CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ (hci j) hS, ih hS]
  have hx_eq : ∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x) = x := by
    conv_rhs => rw [← DirectSum.sum_support_of x]
    rfl
  refine ⟨∑ i ∈ DFinsupp.support x, DirectSum.lof K I (fun i ↦ (E i).H n) i ((E i).cls _ (hc i)), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [toH, DirectSum.toModule_lof]
  have hx' : (Dsum E).d n (∑ i ∈ DFinsupp.support x, (inj E i).f n ((prj E i).f n x)) = 0 := by
    rw [hx_eq]
    exact hx
  rw [Finset.sum_congr rfl fun i _ ↦ CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (inj E i) _ (hc i) (hci i), ← hsum _ hx']
  exact (CrystallineSemistableComparison.CechClassBoundaries.cls_eq _ _ _ _).2 (by rw [hx_eq, sub_self]; exact zero_mem _)

end GlobalTheory.CompanionTheory.KunGlue.DsumCoh

theorem GlobalTheory.CompanionTheory.KunGlue.dsum_coh : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ),
    ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0)
      (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0),
      e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) =
        (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  intro K _ I _ E n
  refine ⟨LinearEquiv.ofBijective (DsumCoh.toH E n) ⟨DsumCoh.toH_injective E n, DsumCoh.toH_surjective E n⟩,
    fun i x hx hx' ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, DsumCoh.toH, DirectSum.toModule_lof]
  exact CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' (DsumCoh.inj E i) x hx hx'
end
end

