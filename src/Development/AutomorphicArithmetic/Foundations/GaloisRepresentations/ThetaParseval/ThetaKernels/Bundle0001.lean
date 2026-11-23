module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0006
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefinite

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ActOFIotaVFK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
namespace GlobalTheory.RealWeilF
theorem actOF_iotaVF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ θ _ ι hι g h v
  have hfin : ∀ u : IxF F nS nT → ℂ, (iotaVF ι u).map (finPartF F E) = 0 := fun u => real_iotaVF hι u
  have hL : (actOF σ JS JT g h (iotaVF ι v)).map (finPartF F E) = 0 := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hfin, Matrix.mul_zero, Matrix.zero_mul]
  have hcpt : ∀ (u : IxF F nS nT → ℂ) w, compAtF θ w (iotaVF ι u) = GlobalTheory.RealWeil.cpt u w := by
    intro u w
    ext i j
    exact hι.comp _ w
  have hC : ∀ w, compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
      compAtF θ w (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v)) := by
    intro w
    have e : compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
        compAtF θ w (mtF σ JT h) * compAtF θ w (iotaVF ι v) * compAtF θ w (mtF σ JS g⁻¹) := by
      unfold actOF compAtF
      rw [Matrix.map_mul, Matrix.map_mul]
    rw [e, hcpt, hcpt, mMF_apply, GlobalTheory.RealWeil.cpt_blk]
  ext i j
  rw [← sub_eq_zero]
  refine hι.ext _ ?_ fun w => ?_
  · have h1 : finPartF F E (actOF σ JS JT g h (iotaVF ι v) i j) = 0 := congrFun (congrFun hL i) j
    have h2 : finPartF F E (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) i j) = 0 := congrFun (congrFun (hfin _) i) j
    rw [RingHom.map_sub, h1, h2, sub_zero]
  · have h3 := congrFun (congrFun (hC w) i) j
    simp only [compAtF, Matrix.map_apply, RingHom.comp_apply] at h3
    rw [RingHom.map_sub, RingHom.map_sub, h3, sub_self]
end GlobalTheory.RealWeilF
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheorems
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def SWAniso_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ
def EisContinues_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ b : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ b →
    ∀ K a, IsStab2 (σ := σ) (Y := Y) B K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ U Ê, IsEisCont (flat a f s₁) U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsS
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def SiegelWeilStd_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n → min r s = 0 →
    (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def SWAnisoX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) (((d : ℂ) - n) / 2)
        fun x => (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ChangeK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}
end
theorem change_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContDiffDerivHeisOFLineK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.ThetaLineSmoothF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Form
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E)
end Form
theorem contDiff_deriv_heisOF_line_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 k L' hL' hL0' w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hi : Continuous (fun v : Fin (k + 1) → ℝ => Fin.init v) := continuous_pi fun i => continuous_apply _
  let M : (Fin (k + 1) → ℝ) →+ WOF F E nS nT :=
    { toFun := fun v => L' (Fin.init v) + L (v (Fin.last k))
      map_zero' := by
        show L' (Fin.init (0 : Fin (k + 1) → ℝ)) + L ((0 : Fin (k + 1) → ℝ) (Fin.last k)) = 0
        rw [show Fin.init (0 : Fin (k + 1) → ℝ) = (0 : Fin k → ℝ) from rfl, Pi.zero_apply, map_zero, map_zero, add_zero]
      map_add' := fun u v => by
        show L' (Fin.init (u + v)) + L (u (Fin.last k) + v (Fin.last k)) = _
        rw [show Fin.init (u + v) = Fin.init u + Fin.init v from rfl, map_add (f := _), map_add (f := _)]
        abel }
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have hM : Continuous M := (hL'.comp hi).add (hL.comp (continuous_apply _))
  have hM0 : ∀ v, (M v).map (finPartF F E) = 0 := fun v => by
    show (L' (Fin.init v) + L (v (Fin.last k))).map (finPartF F E) = 0
    rw [Matrix.map_add _ (map_add _), hL0', hL0, add_zero]
  have hg : ContDiff ℝ ∞ fun v => f (w + M v) := hf.smooth (k + 1) M hM hM0 w
  have hsnoc : ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact contDiff_snd
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_fst
  let h : (Fin k → ℝ) × ℝ → ℂ := fun p => f (w + M (Fin.snoc (α := fun _ => ℝ) p.1 p.2))
  have hh : ContDiff ℝ ∞ h := hg.comp hsnoc
  have hfe : ∀ x t, f (w + L' x + L t) = h (x, t) := by
    intro x t
    show _ = f (w + (L' (Fin.init (Fin.snoc (α := fun _ => ℝ) x t)) + L (Fin.snoc (α := fun _ => ℝ) x t (Fin.last k))))
    rw [Fin.init_snoc, Fin.snoc_last, add_assoc]
  have hpsi : ∀ y (t : ℝ), B.ψ (symplOHF σ JS JT ξ₀ y (L t)) =
      Complex.exp (t * lam (symplOHF σ JS JT ξ₀ y (L 1))) := by
    intro y t
    rw [hlam _ (snd_symplOHF σ JS JT ξ₀ y _ (hL0 t))]
    congr 1
    let φ : ℝ →+ ℂ :=
      { toFun := fun t => lam (symplOHF σ JS JT ξ₀ y (L t))
        map_zero' := by rw [map_zero L, symplOHF_zero_right, map_zero]
        map_add' := fun a b => by rw [map_add L, symplOHF_add_right, map_add (f := _)] }
    have hφ : Continuous φ := hl.comp (continuous_symplOHF σ JS JT ξ₀ continuous_const hL)
    have := (φ.toRealLinearMap hφ).map_smul t 1
    rw [smul_eq_mul, mul_one, Complex.real_smul] at this
    exact this
  have hd : ∀ x, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x))
      (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1)) 0 := by
    intro x
    have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) = fun t : ℝ =>
        Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t) := by
      funext t
      show B.ψ (symplOHF σ JS JT ξ₀ (w + L' x) (L t)) * f (w + L' x + L t) = _
      rw [hpsi, hfe]
    rw [e]
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) 0 := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
    have hp : HasDerivAt (fun t : ℝ => (x, t)) ((0 : Fin k → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
    have h2 : HasDerivAt (fun t : ℝ => h (x, t)) (fderiv ℝ h (x, 0) (0, 1)) 0 :=
      ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hp
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t))
        (Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) *
          lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) +
          Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * fderiv ℝ h (x, 0) (0, 1)) 0 :=
      h0.cexp.mul h2
    refine h3.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  let φ' : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun x => lam (symplOHF σ JS JT ξ₀ (L' x) (L 1))
      map_zero' := by rw [map_zero L', symplOHF_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L', symplOHF_add_left, map_add (f := _)] }
  have hφ' : ContDiff ℝ ∞ φ' :=
    (φ'.toRealLinearMap (hl.comp (continuous_symplOHF σ JS JT ξ₀ hL' continuous_const))).contDiff
  have e : (fun x => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0) = fun x =>
      (lam (symplOHF σ JS JT ξ₀ w (L 1)) + φ' x) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1) := by
    funext x
    rw [(hd x).deriv, symplOHF_add_left, map_add (f := _)]
    rfl
  rw [e]
  have hin : ContDiff ℝ ∞ (fun x : Fin k → ℝ => (x, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  exact ((contDiff_const.add hφ').mul (hh.comp hin)).add
    (((hh.fderiv_right (m := ∞) (by simp)).comp hin).clm_apply contDiff_const)
end GlobalTheory.ThetaLineSmoothF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousMMFK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.RealWeilF.MCont
theorem continuous_mMF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT θ hθ
  have hc : ∀ (w : InfinitePlace F) (m n : ℕ), Continuous fun x : Matrix (Fin m) (Fin n) (AEF F E) => compAtF θ w x :=
    fun w m n => continuous_id.matrix_map (continuous_comp_infPartF (hθ w))
  have h1 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JT p.2 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd
  have h2 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JS p.1⁻¹ := by
    have : (fun g : GAF σ JS => mtF σ JS g⁻¹) =
        fun g => (((Subtype.val (show HR (AF F) σ JS from g))⁻¹ : GL (Fin nS) (AF F ⊗[F] E)) : Matrix _ _ _) := rfl
    have hi : Continuous fun g : GAF σ JS => mtF σ JS g⁻¹ := by
      rw [this]; exact Units.continuous_coe_inv.comp continuous_subtype_val
    exact hi.comp continuous_fst
  have e : (mMF σ JS JT θ : GAF σ JS × GAF σ JT → _) = fun p =>
      GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT p.2)) fun w => compAtF θ w (mtF σ JS p.1⁻¹) := funext fun p => rfl
  rw [e]
  exact GlobalTheory.RealWeil.continuous_blk (fun w => (hc w _ _).comp h1) fun w => (hc w _ _).comp h2
end GlobalTheory.RealWeilF.MCont
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousOfLevelRealK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.WeilContF
end
noncomputable section
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
open scoped Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
attribute [local instance] finiteFE modTop topRing
theorem continuous_of_level_real_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hstd g hU hsm
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  haveI : IsTopologicalAddGroup (AEF F E) := IsTopologicalRing.to_topologicalAddGroup
  obtain ⟨U, hUo, hUf⟩ := hU
  let φ := (Module.finBasis ℝ (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFunL
  let L : (Fin _ → ℝ) →+ WOF F E nS nT := (realCh F E nS nT).comp φ.symm.toLinearEquiv.toAddMonoidHom
  have hLc : Continuous L := (continuous_realCh nS nT).comp φ.symm.continuous
  have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => by
    funext i j
    exact realCh_fin nS nT _ i j
  have hLφ : ∀ v, L (φ v) = realCh F E nS nT v := fun v => by
    show realCh F E nS nT (φ.symm (φ v)) = _
    rw [φ.symm_apply_apply]
  refine continuous_iff_continuousAt.2 fun w => ?_
  let a : WOF F E nS nT → WOF F E nS nT := fun w' => w + eInf F • (w' - w)
  let u : WOF F E nS nT → WOF F E nS nT := fun w' => w' - a w'
  have hsmc : Continuous fun y : WOF F E nS nT => eInf F • y := continuous_const_smul _
  have ha : Continuous a := continuous_const.add (hsmc.comp (continuous_sub_right w))
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + eInf F • (w - w)) = 0
    rw [sub_self, smul_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPartF F E) = 0 := by
    intro w'
    have e : u w' = (w' - w) - eInf F • (w' - w) := sub_add_eq_sub_sub _ _ _
    funext i j
    show infPartF F E (u w' i j) = 0
    rw [e]
    exact infPartF_sub_eInf_smul _
  have hga : Continuous fun w' => g (a w') := by
    have h1 := (hsm _ L hLc hL0 w).continuous.comp
      (φ.continuous.comp ((continuous_realCo nS nT).comp (hsmc.comp (continuous_sub_right w))))
    refine h1.congr fun w' => ?_
    show g (w + L (φ (realCo F E nS nT (eInf F • (w' - w))))) = g (w + eInf F • (w' - w))
    rw [hLφ, realCh_realCo]
  have hg : Continuous fun w' => B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') :=
    (hstd.1.1.comp (continuous_symplOHF σ JS JT ξ₀ ha hu).neg).mul hga
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hUf _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') = g w'
  rw [← e]
  show _ * (B.ψ (symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
end GlobalTheory.WeilContF
end
end
end

