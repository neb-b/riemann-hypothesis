module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegreeStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_coneIdeal_eq_field_degree : ∀ (K : Type) [Field K] (N : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 → GlobalTheory.idealHilbertPoly (coneIdeal K y) = Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  first | exact @GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | exact GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | (intros; apply GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastSide
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.PolyShapeFinite

theorem main : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), IsBiFinite (KG ε) (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) := by
  intro n ε F P
  let r : UJ ε → ℝ := fun g => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2
  let ev : UJ ε → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ := fun g =>
    Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))
  let L : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ →ₗ[ℂ] (UJ ε → ℂ) :=
    { toFun := fun Q g => ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q
      map_add' := fun Q Q' => by funext g; simp [mul_add]
      map_smul' := fun c Q => by funext g; simp [MvPolynomial.smul_eq_C_mul, mul_left_comm] }
  unfold IsBiFinite
  have hle : Submodule.span ℂ {φ : UJ ε → ℂ | ∃ k ∈ KG ε, ∃ k' ∈ KG ε, φ = fun g =>
      ((F (r (k * g * k')) : ℝ) : ℂ) * MvPolynomial.eval (ev (k * g * k')) P} ≤
      (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map L := by
    rw [Submodule.span_le]
    rintro φ ⟨k, hk, k', hk', rfl⟩
    obtain ⟨Q, hQ, hQe⟩ := _root_.GlobalTheory.PolyEntryMul.main n (toM k) (toM k') P
    refine ⟨Q, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hQ, ?_⟩
    funext g
    have h1 : r (k * g * k') = r g := (_root_.GlobalTheory.offDiagBlockNorm_cont_inv n ε).2 ⟨k, hk⟩ ⟨k', hk'⟩ g
    have h2 : toM (k * g * k') = toM k * toM g * toM k' := rfl
    have h3 : MvPolynomial.eval (ev (k * g * k')) P = MvPolynomial.eval (ev g) Q := by
      simp only [ev, h2]; exact hQe (toM g)
    show ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q = _
    rw [h1, h3]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.PolyShapeFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
section
noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

namespace GlobalTheory.KSplit

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSmU (χ : kˣ →* ℂˣ) : Prop := IsOpen (χ.ker : Set kˣ) ∧ ∀ x, ‖(χ x : ℂ)‖ = 1


variable (k) in
def intM (m n : Type) : Set (Matrix m n k) := {X | ∀ i j, X i j ∈ 𝒪[k]}

def IsEqv {n : ℕ} (ν : kˣ →* ℂˣ) (z : ℂ) (l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ) : Prop :=
  (∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∀ φ' ∈ SB (Matrix (Fin n) (Fin n) k), l (φ + φ') = l φ + l φ') ∧
  (∀ c : ℂ, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), l (c • φ) = c * l φ) ∧
  ∀ g₁ g₂ : GL (Fin n) k, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k),
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z * l (fun X => φ (g₁.val * X * g₂.val)) = l φ

def indSp (a a' : ℕ) (α β : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin (a + a')) k → ℂ) where
  carrier := {f | (∀ (b : GL (Fin (a + a')) k) (A : GL (Fin a) k) (D : GL (Fin a') k) (N : Matrix (Fin a) (Fin a') k),
      b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks A.val N 0 D.val → ∀ h, f (b * h) =
        (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * f h) ∧
    ∀ᶠ u in 𝓝 (1 : GL (Fin (a + a')) k), ∀ h, f (h * u) = f h}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun b A D N hb h => ?_, (h2.and h2').mono fun u hu h => ?_⟩
    · simp only [Pi.add_apply, h1 b A D N hb, h1' b A D N hb, mul_add]
    · simp only [Pi.add_apply, hu.1, hu.2]
  zero_mem' := ⟨fun _ _ _ _ _ _ => by simp, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun b A D N hb h => ?_, h2.mono fun u hu h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1 b A D N hb]; ring
    · simp only [Pi.smul_apply, hu]

def mapA {a : ℕ} (a' : ℕ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omA ν β 1 h Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

section Frames

variable {R S D : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem restrict_mem_SB {P : Matrix R D k} {P' : Matrix D R k} (hP : P * P' = 1) {Φ : Matrix R D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R D k)) : (fun g : Matrix R R k => Φ (g * P)) ∈ SB (Matrix R R k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun g : Matrix R R k => g * P := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * P' := continuous_id.matrix_mul continuous_const
  have e : IsClosedEmbedding fun g : Matrix R R k => g * P :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : Matrix R D k => X * P')
      (fun g => by simp only [Matrix.mul_assoc, hP, Matrix.mul_one]) c2 c1
  exact ⟨hΦ.1.comp_continuous c1, hΦ.2.comp_isClosedEmbedding e⟩


omit [DecidableEq R] [DecidableEq D] in
theorem indicator_intM_mem_SB : (intM k R D).indicator (1 : Matrix R D k → ℂ) ∈ SB (Matrix R D k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact (intM k R D) := isCompact_intMatrix
  have hK : IsClopen (intM k R D) := ⟨hc.isClosed, isOpen_intMatrix⟩
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

theorem exists_extend_SB {P : Matrix R D k} {Q : Matrix S D k} (hP : P * Pᵀ = 1) (hQ : P * Qᵀ = 0)
    (hPQ : Pᵀ * P + Qᵀ * Q = 1) {φ : Matrix R R k → ℂ} (hφ : φ ∈ SB (Matrix R R k)) :
    ∃ Φ ∈ SB (Matrix R D k), ∀ g, Φ (g * P) = φ g := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hI := indicator_intM_mem_SB (k := k) (R := R) (D := S)
  have c1 : Continuous fun X : Matrix R D k => X * Pᵀ := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * Qᵀ := continuous_id.matrix_mul continuous_const
  have c3 : Continuous fun x : Matrix R R k × Matrix R S k => x.1 * P + x.2 * Q :=
    (continuous_fst.matrix_mul continuous_const).add (continuous_snd.matrix_mul continuous_const)
  refine ⟨fun X => φ (X * Pᵀ) * (intM k R S).indicator 1 (X * Qᵀ),
    ⟨(hφ.1.comp_continuous c1).mul (hI.1.comp_continuous c2), ?_⟩, fun g => ?_⟩
  · refine HasCompactSupport.intro ((hφ.2.isCompact.prod hI.2.isCompact).image c3) fun X hX => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    refine hX ⟨(X * Pᵀ, X * Qᵀ), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [Matrix.mul_assoc, ← Matrix.mul_add, hPQ, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, hP, hQ, Matrix.mul_one, Matrix.mul_zero]
    rw [Set.indicator_of_mem (show (0 : Matrix R S k) ∈ intM k R S from fun _ _ => zero_mem _)]
    simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_rel (σ : R ⊕ S ≃ D) : X0 k σ * (X0 k σ)ᵀ = 1 ∧ Y0 k σ * (Y0 k σ)ᵀ = 1 ∧ X0 k σ * (Y0 k σ)ᵀ = 0 ∧
    Y0 k σ * (X0 k σ)ᵀ = 0 ∧ (X0 k σ)ᵀ * X0 k σ + (Y0 k σ)ᵀ * Y0 k σ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; rw [frameMatrixFirstColumnBlock_mul_apply]; simp [X0, Matrix.one_apply, eq_comm]
  · ext i j; rw [frameMatrixSecondColumnBlock_mul_apply]; simp [Y0, Matrix.one_apply, eq_comm]
  · ext i j; simp [frameMatrixFirstColumnBlock_mul_apply, Y0]
  · ext i j; simp [frameMatrixSecondColumnBlock_mul_apply, X0]
  · ext i j
    obtain ⟨i | i, rfl⟩ := σ.surjective i <;> obtain ⟨j | j, rfl⟩ := σ.surjective j <;>
      simp [X0, Y0, Matrix.mul_apply, Matrix.one_apply, Function.swap, eq_comm]

end Frames

variable {a a' : ℕ} {z : ℂ} {ν α β : kˣ →* ℂˣ}

theorem restrict_X0 {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (hΦ : Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k)) :
    (fun g : Matrix (Fin a) (Fin a) k => Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
  restrict_mem_SB (frame_rel _).1 hΦ

theorem mapA_omA_right (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ)
    (x h : GL (Fin (a + a')) k) : mapA a' l ν β (omA ν β 1 x Φ) h = mapA a' l ν β Φ (h * x) := by
  unfold mapA
  rw [← omA_mul, one_mul]

end Local

section Adelic

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def locMat {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v)) :
    UA σ J →* GL (Fin n) (Fv F v) where
  toFun g := b⁻¹ * Matrix.GeneralLinearGroup.map (piW t) g.1 * b
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem locMat_val {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v))
    (g : UA σ J) : (locMat t b g).val = (b⁻¹).val * (mat g).map (piW t) * b.val := rfl

end Adelic

end GlobalTheory.KSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory

namespace GlobalTheory.WeilPartsF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def GfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (infPartF F E)).comp (matHomF σ J)).ker

def GinfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (finPartF F E)).comp (matHomF σ J)).ker

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

structure IsUnitaryOnThetaF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f → IsThetaFunOF σ JS JT xi0 ψ (om p f)
  cont : ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ∀ w, Continuous fun p : GAF σ JS × GAF σ JT => om p f w
  unit : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ) (χS χT : (AEF F E)ˣ →* Circle)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ x y,
    IsDetAtF σ e JS g x → IsDetAtF σ e JT h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT xi0 ψ f →
        ℓ (heisOF σ JS JT xi0 ψ u f) = ℓ f) →
      ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacOF χS χT x y : ℂ) * ℓ f

structure IsInfWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)

section Lemmas

variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E} {ψ : AddChar (AF F) ℂ}

theorem heisOF_add (w : WOF F E nS nT) (f g : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (f + g) = heisOF σ JS JT xi0 ψ w f + heisOF σ JS JT xi0 ψ w g := by
  funext x
  simp only [heisOF, Pi.add_apply, mul_add]

theorem heisOF_smul (c : ℂ) (w : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (c • f) = c • heisOF σ JS JT xi0 ψ w f := by
  funext x
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_add {f g : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    IsThetaFunOF σ JS JT xi0 ψ (f + g) := {
  quasi γ w := by
    simp only [Pi.add_apply]
    rw [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    obtain ⟨V, hV, hV'⟩ := hg.level
    exact ⟨U ⊓ V, hU.inter hV, fun u hu h0 => by rw [heisOF_add, hU' u hu.1 h0, hV' u hu.2 h0]⟩
  cont := hf.cont.add hg.cont
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w) }

theorem theta_zero : IsThetaFunOF σ JS JT xi0 ψ (0 : WOF F E nS nT → ℂ) := {
  quasi γ w := by simp
  level := ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext x; simp [heisOF]⟩
  cont := continuous_const
  smooth k L hL h0 w := contDiff_const }

theorem theta_smul (c : ℂ) {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) :
    IsThetaFunOF σ JS JT xi0 ψ (c • f) := {
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisOF_smul, hU' u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c }


variable (σ JS JT xi0 ψ) in
def thetaSubF : Submodule ℂ (WOF F E nS nT → ℂ) where
  carrier := {f | IsThetaFunOF σ JS JT xi0 ψ f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : GAF σ J) : mtF σ J (g * g') = mtF σ J g * mtF σ J g' := by
  unfold mtF
  rw [map_mul]
  rfl

theorem actOF_mul (g g' : GAF σ JS) (h h' : GAF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT (g * g') (h * h') u = actOF σ JS JT g h (actOF σ JS JT g' h' u) := by
  unfold actOF
  rw [_root_.mul_inv_rev, mtF_mul, mtF_mul]
  simp only [Matrix.mul_assoc]

theorem mem_GfCF_of_supp {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : AEF F E} (ha : infPartF F E a = 0) {g : GAF σ J}
    (hg : ∀ i j, a * (mtF σ J g - 1) i j = (mtF σ J g - 1) i j) : g ∈ GfCF σ J := by
  rw [GfCF, MonoidHom.mem_ker, MonoidHom.comp_apply]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPartF F E ((mtF σ J g - 1) i j) = 0 := by rw [← hg i j, map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  show infPartF F E (mtF σ J g i j) = ((1 : GL (Fin n) (Ainf F ⊗[F] E)) : Matrix _ _ _) i j
  rw [h, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem infPartF_placeIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdemF F v ε) :
    infPartF F E (algebraMap (AF F) (AEF F E) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfCF_of_suppAt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} (he : IsSplitIdemF σ e) {g : GAF σ J}
    (hg : SuppAtF σ e J g) : g ∈ GfCF σ J := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfCF_of_supp (h2 ▸ infPartF_placeIdem h1) hg

theorem isHeckeCharF_pow {η : (AEF F E)ˣ →* Circle} (h : IsHeckeCharF η) (n : ℕ) : IsHeckeCharF (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEtaF_pow {η : (AEF F E)ˣ →* Circle} (h : ResEtaF η 1) (n : ℕ) : ResEtaF (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

end Lemmas

end GlobalTheory.WeilPartsF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {M W' ι : Type} [AddCommGroup M] [Module K M]
  [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Fintype ι]


omit [NumberField K] in
theorem inner_coef_of_rat (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W') (pr : M →ₗ⋆[K] M →ₗ[K] K)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a'))) (u v : M) (hu : ∀ a, b.repr u a ∈ cmMax K) :
    inner ℂ (c₁ u) (c₁ v) = σ (pr u v) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply (b.repr u a'), hu a' σ]

theorem inner_eq_csumAt (S : CSD K) (hb : S.HasRatBasis) (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (pr : M →ₗ⋆[K] M →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (e : S.V ≃ₗ[K] M) (hr : ∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) (he : ∀ x x', pr (e x) (e x') = S.pair x x')
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : S.Forms →ₛₗ[σ] H)
    (hj : ∀ x y : S.Forms, inner ℂ (j x) (j y) =
      ∑ c, ((S.wt c : ℂ))⁻¹ * inner ℂ (c₁ (e ((x : S.Cl → S.V) c))) (c₁ (e ((y : S.Cl → S.V) c)))) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  have hrat : ∀ k c a, b.repr (e ((S.basis k : S.Cl → S.V) c)) a ∈ cmMax K := by
    intro k c a
    rw [← S.bV.sum_repr ((S.basis k : S.Cl → S.V) c)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (S.basis_rat hb k c i) (hr i a)
  have hH : ∀ k l, inner ℂ (j (S.basis k)) (j (S.basis l)) = σ (S.H k l) := by
    intro k l
    rw [hj]
    unfold CSD.H CSD.csum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_coef_of_rat b σ c₁ pr hp _ _ (hrat k c), he, map_mul, map_inv₀, map_natCast]
  conv_lhs => rw [← S.basis.sum_repr x, ← S.basis.sum_repr y]
  unfold csumAt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hH,
    dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply]
  ring

theorem inner_eq_csumAt_of_pres {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ι₀ : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι₀ S σ₀ ρ J χ) (b : Module.Basis ι K M) (c₀ : M →ₛₗ[σ₀] W) (pr : M →ₗ⋆[K] M →ₗ[K] K)
    {Q : (S.V ≃ₗ[K] M) → Prop}
    (hP : ∃ e : S.V ≃ₗ[K] M, (∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) ∧ (∀ x, P.coef x = c₀ (e x)) ∧
      (∀ x x', pr (e x) (e x') = S.pair x x') ∧ Q e)
    (hb : S.HasRatBasis) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H)
    (hH : ∀ x y : H.H, inner ℂ x y = Bridge.adInner ι₀ J P.y (H.e x) (H.e y))
    (hj : ∀ (x : S.Forms) h, ∃ v, P.ext (x : S.Cl → S.V) h = c₀ v ∧ H.e (j x) h = c₁ v) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  obtain ⟨e, hr, he, hpair, -⟩ := hP
  have hval : ∀ (z : S.Forms) cl, H.e (j z) (P.y cl) = c₁ (e (z.1 cl)) := by
    intro z cl
    obtain ⟨v, h0, h1⟩ := hj z (P.y cl)
    have h3 : P.coef (z.1 cl) = P.coef (e.symm v) := by
      rw [← GlobalTheory.PresBasic.ext_y P z cl, h0, he, e.apply_symm_apply]
    rw [h1, GlobalTheory.PresBasic.coef_injective _ h3, e.apply_symm_apply]
  refine inner_eq_csumAt S hb _ σ c₁ _ hp e hr hpair j (fun z w => ?_) x y
  rw [hH]
  unfold Bridge.adInner
  refine Finset.sum_congr rfl fun cl _ => ?_
  rw [hval, hval, CSD.wt, ← Nat.card_eq_fintype_card, Nat.card_congr (P.stabI cl).toEquiv]

end Generic

theorem inner_conjForms_eq_csumAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ x y, ⟪j x, j y⟫_ℂ = csumAt (A.MtCSD i A.μ0) σ x y := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC x y
  have hb : (A.MtCSD i A.μ0).HasRatBasis :=
    (GlobalTheory.HeckeRational.dcOp_matrix_mem_cmMax (Vc D i) (R.cV i).coef (R.βV i) (R.datVt i A.μ0) (R.B.L i A.μ0).pres
      (hT.coefL i A.μ0) (hT.mapL i)
      (fun g a k => (coefAction_repr_mem_subfield (labLL D) _ _ GlobalTheory.HeckeRational.labLL_mem_cmMax g a k).2) {1} 1
      (fun f => by funext h; simp [Bridge.dcOp])).1
  have h1 := hC.model.choose_spec.2.2.2
  have h2 : ∀ (z : A.fam.amb.FL i A.μ0) h, ∃ v, (R.B.L i A.μ0).pres.ext z.1 h = c0L i v ∧ H.e (j z) h = c₁ v :=
    fun z h => (hC.base z h).imp fun v hv => ⟨(congrFun (hjV i A.μ0 z) h).symm.trans hv.1, hv.2⟩
  exact inner_eq_csumAt_of_pres (R.B.L i A.μ0).pres _ (c0L i) _ (hT.coefL i A.μ0) hb σ c₁ hC.pair H j h1 h2 x y

end GlobalTheory.LiftLower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLocalCenterFiniteMaximalIdealsStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralLocalCenter_finite_maximal_ideals : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1) (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)), Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  first | (exact @GlobalTheory.OrbFinAf.intF_finite_maximal) | (exact GlobalTheory.OrbFinAf.intF_finite_maximal) | (intros; apply GlobalTheory.OrbFinAf.intF_finite_maximal  <;> assumption)
end

