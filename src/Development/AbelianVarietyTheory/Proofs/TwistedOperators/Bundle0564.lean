module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.KStableSums

def pureL {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' a f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) {Ψ : (Fin n × Fin d → AF F) → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb) ∧ (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  choose f φ hf hSB hev he using fun i => (g i).2
  refine ⟨m, fun i => a i • f i, φ, fun i => (M.Pol ψ emb).smul_mem _ (hf i), fun i => ⟨hSB i, hev i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i]
  exact ((pureL (φ i)).map_smul (a i) (f i)).symm

def piEnd {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) : Module.End ℂ (Fin m → V) :=
  LinearMap.pi fun i => L ∘ₗ LinearMap.proj i

theorem piEnd_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (y : Fin m → V)
    (i : Fin m) : piEnd m L y i = L (y i) := rfl

theorem piEnd_pow_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (k : ℕ)
    (y : Fin m → V) (i : Fin m) : (piEnd m L ^ k) y i = (L ^ k) (y i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, piEnd_apply, ih, pow_succ', Module.End.mul_apply]

theorem isExp_piEnd {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : IsExp L U) (m : ℕ) :
    IsExp (piEnd m L) (piEnd m U) := by
  intro y l
  have hl : ∀ z : Fin m → V, l z = ∑ i, (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) (z i) := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have key : (fun k : ℕ => ((k.factorial : ℂ))⁻¹ * l ((piEnd m L ^ k) y)) =
      fun k => ∑ i, ((k.factorial : ℂ))⁻¹ * (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) ((L ^ k) (y i)) := by
    funext k
    rw [hl, Finset.mul_sum]
    simp only [piEnd_pow_apply]
  rw [key, hl]
  exact hasSum_sum fun i _ => h (y i) _

theorem exp_conj_rect {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (C : Matrix β ι ℂ) (A' : Matrix ι β ℂ) (hCA : C * A' = 1) (hAC : A' * C = 1) (Y : Matrix ι ι ℂ) :
    NormedSpace.exp (C * Y * A') = C * NormedSpace.exp Y * A' := by
  let f : Matrix ι ι ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C * X * A'
      map_one' := by simp [hCA]
      map_mul' := fun X Z => by
        calc C * (X * Z) * A' = C * X * (A' * C) * Z * A' := by rw [hAC, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]
      map_zero' := by simp
      map_add' := fun X Z => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  open scoped Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem atPl_zero {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) : atPl (V := V) w 0 = 0 := by
  unfold atPl
  exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] {κ : Type}
    [Fintype κ] (act : Matrix κ κ ℂ →ₗ[ℂ] Module.End ℂ V) (c : ι → ℂ) (w : ι) (Y : Matrix κ κ ℂ) :
    sumPl (V := fun _ : ι => V) (fun w' => act ((Pi.single w Y : ι → Matrix κ κ ℂ) w') +
        (c w' * ((Pi.single w Y : ι → Matrix κ κ ℂ) w').trace) • 1) =
      atPl (V := fun _ : ι => V) w (act Y + (c w * Y.trace) • 1) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp only [Pi.single_eq_of_ne hw', map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero]
    exact atPl_zero w'
  · intro h; exact absurd (Finset.mem_univ w) h

theorem exists_line_upq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {β : Type} [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (J : Matrix β β (AE F E)) (b : ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ)
    (hCM : IsCMExt F E σ) (hfr : ∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) (hθ : ∀ w, θ w * C w = C w * Jm R S)
    (k : UG (cA σ) J) (hk : At (evI F) ((k.1 : Matrix β β (AE F E)) - 1))
    (hkθ : ∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) :
    ∃ γ ∈ RLines (σ := σ) J, ∃ Y : InfinitePlace F → Matrix (Ix R S) (Ix R S) ℂ, IsGen τ C γ Y ∧ (∀ w, Y w ∈ upq R S) ∧
      (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k := by
  open GlobalTheory.RealLift.KLineProof in
  have hu : (k.1 : Matrix β β (AE F E))ᵀ * J * (k.1 : Matrix β β (AE F E)).map (cA σ) = J := k.2
  have hloc : ∀ w, ∃ Y : Matrix (Ix R S) (Ix R S) ℂ, Y ∈ upq R S ∧ IsKC Y ∧
      C w * NormedSpace.exp Y = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w := by
    intro w
    obtain ⟨A', hCA, hAC⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    refine GlobalTheory.RealLift.KLineProof.exists_gen_at (C w) A' hCA hAC (J.map (piInf (τ w))) b (hfr w).1 _ (θ w) ?_
      (hθ w) (hkθ w)
    have := congrArg (fun X => X.map (piInf (τ w))) hu
    simp only [Matrix.map_mul, GlobalTheory.RealLift.KLineProof.map_cA_map hCM, Matrix.transpose_map] at this
    exact this
  choose Y hY using hloc
  obtain ⟨γ, hγ, hgen⟩ := _root_.GlobalTheory.RealLift.exists_line_of_upq F E σ β R S τ J b C hCM hfr Y (fun w => (hY w).1)
  refine ⟨γ, hγ, Y, hgen, fun w => (hY w).1, fun w => (hY w).2.1, ?_⟩
  have hw : ∀ w, ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) := by
    intro w
    obtain ⟨A', hCA, -⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    have h1 := hgen 1 w
    rw [one_smul, (hY w).2.2] at h1
    calc _ = ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w * A' := by
          rw [Matrix.mul_assoc, hCA, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hA1 := hγ.2 (Multiplicative.ofAdd 1)
  have hmat : ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)) = k.1 := by
    ext i j
    rw [← sub_eq_zero]
    refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ _ ?_ ?_
    · intro u hu0
      have e1 := congrFun (congrFun (hA1 u hu0) i) j
      have e2 := congrFun (congrFun (hk u hu0) i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_sub] at e1 e2 ⊢
      rw [← sub_sub_sub_cancel_right _ _ (u • (1 : Matrix β β (AE F E)) i j), e1, e2, sub_zero]
    · intro w
      have := congrFun (congrFun (hw w) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this, sub_self]
  exact Subtype.ext (Units.ext hmat)


end GlobalTheory.KStableSums
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
noncomputable section

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mulL {d : ℕ} (c : E) : (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun z := fun j => inclR (F := F) (AF F) c * z j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma mulL_apply {d : ℕ} (c : E) (z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (j : Fin d) :
    mulL (F := F) c z j = inclR (F := F) (AF F) c * z j := rfl

lemma mulL_int_mem {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (o : 𝓞 E)
    {z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : mulL (F := F) (o : E) z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    simp only [mulL_apply, Pi.smul_apply]
    rw [Algebra.smul_def (A := E) o (y j), map_mul, mul_smul_comm]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rowL {n d : ℕ} (i₀ : Fin n) (c : E) :
    Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun Γ := fun j => inclR (F := F) (AF F) c * Γ i₀ j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma rowL_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (i₀ : Fin n) (c : E)
    (hc : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀)
    {Γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hΓ : Γ ∈ latAtV X W v) :
    rowL (F := F) i₀ c Γ ∈ GlobalTheory.InertSph.latAt W v := by
  induction hΓ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨o, ho⟩ := hc x hx
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    show inclR (F := F) (AF F) c * (a • incM F (Matrix.vecMulVec x y)) i₀ j = _
    simp only [Matrix.smul_apply, Pi.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [Algebra.smul_def (A := E) o (y j), mul_smul_comm, ← map_mul, ← mul_assoc]
    congr 2
    rw [← ho]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

lemma rowL_vecMulVec {n d : ℕ} (i₀ : Fin n) (c : E) (x : Fin n → E) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    rowL (F := F) i₀ c (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) = mulL (F := F) (c * x i₀) q := by
  ext j
  simp only [rowL, mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, map_mul, mul_assoc]

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coefSub {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    Submodule (𝓞 E) E where
  carrier := {c | mulL (F := F) c q ∈ GlobalTheory.InertSph.latAt W v}
  zero_mem' := by
    change mulL (F := F) (0 : E) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (0 : E) q = 0 := by ext j; simp [mulL_apply]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).zero_mem
  add_mem' {a b} ha hb := by
    change mulL (F := F) (a + b) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (a + b) q = mulL (F := F) a q + mulL (F := F) b q := by
      ext j; simp [mulL_apply, add_mul]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).add_mem ha hb
  smul_mem' o c hc := by
    change mulL (F := F) (o • c) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (o • c) q = mulL (F := F) (o : E) (mulL (F := F) c q) := by
      ext j; simp only [mulL_apply, Algebra.smul_def, map_mul, mul_assoc]
    rw [this]; exact mulL_int_mem W v o hc

theorem extract (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hn : 0 < n) (hL : X.L.IsFullLattice E)
    (h : ∀ x ∈ X.L, Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v) :
    q ∈ GlobalTheory.InertSph.latAt W v := by
  set i₀ : Fin n := ⟨0, hn⟩
  let b₀ : Submodule (𝓞 E) E := X.L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i₀)
  have hfg : b₀.FG := hL.fg.map _
  let 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨b₀, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ b, b ∈ 𝔟 ↔ ∃ x ∈ X.L, x i₀ = b := fun b => by
    rw [← FractionalIdeal.mem_coe]; exact Submodule.mem_map
  have hne : 𝔟 ≠ 0 := by
    intro h0
    have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) i₀) := by
      rw [Submodule.span_le]
      intro x hx
      have : x i₀ ∈ 𝔟 := (hmem _).2 ⟨x, hx, rfl⟩
      rw [h0, FractionalIdeal.mem_zero_iff] at this
      simpa using this
    rw [Submodule.IsFullLattice.span_eq_top (self := hL)] at hle
    have := hle (Submodule.mem_top (x := Pi.single i₀ (1 : E)))
    simp at this
  have hone : (1 : E) ∈ ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
    rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_coe]; exact FractionalIdeal.one_mem_one _
  have hle : ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ coefSub W v q := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro c hc b hb
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hc
    rw [FractionalIdeal.mem_coe, hmem] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hc' : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀ := by
      intro x hx
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hc _ ((hmem _).2 ⟨x, hx, rfl⟩))
      exact ⟨o, ho⟩
    change mulL (F := F) (c * x i₀) q ∈ GlobalTheory.InertSph.latAt W v
    rw [← rowL_vecMulVec]
    exact rowL_mem X W v i₀ c hc' (h x hx)
  have h1 : mulL (F := F) (1 : E) q ∈ GlobalTheory.InertSph.latAt W v := hle hone
  have : mulL (F := F) (1 : E) q = q := by ext j; simp [mulL_apply]
  rwa [this] at h1

end GlobalTheory.LatExtract

theorem GlobalTheory.LatExtract.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), 0 < n → X.L.IsFullLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := fun F E _ _ _ _ _ n d X W v q hn hL h =>
  GlobalTheory.LatExtract.extract n d X W v q hn hL h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaLiftTypeX

theorem goodAt_of_node {D : D7} (N : GlobalTheory.Grid.Node D) (hV : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) :=
  ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ),
    GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hV (tauE D τ))⟩

end GlobalTheory.ThetaLiftTypeX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchDer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.LieEq

theorem exists_op {S S' Pi : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Pi] [Module ℂ Pi]
    (N : Submodule ℂ S) (N' : Submodule ℂ S') (p : S →ₗ[ℂ] Pi) (p' : S' →ₗ[ℂ] Pi) (δ : S →ₗ[ℂ] S) (δ' : S' →ₗ[ℂ] S')
    (h : ∀ f ∈ N, ∀ f' ∈ N', p f = p' f' → p (δ f) = p' (δ' f')) :
    ∃ A : Pi →ₗ[ℂ] Pi, (∀ f ∈ N, A (p f) = p (δ f)) ∧ ∀ f' ∈ N', A (p' f') = p' (δ' f') := by
  let L : (N × N') →ₗ[ℂ] Pi := p ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  let L₁ : (N × N') →ₗ[ℂ] Pi := p ∘ₗ δ ∘ₗ N.subtype ∘ₗ LinearMap.fst ℂ N N' + p' ∘ₗ δ' ∘ₗ N'.subtype ∘ₗ LinearMap.snd ℂ N N'
  have hk : LinearMap.ker L ≤ LinearMap.ker L₁ := by
    intro x hx
    simp only [LinearMap.mem_ker, L, L₁, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.coe_subtype] at hx ⊢
    have e : p (x.1 : S) = p' (-(x.2 : S')) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left hx
    have := h _ x.1.2 _ (N'.neg_mem x.2.2) e
    rw [this, map_neg, map_neg, neg_add_cancel]
  let A₀ : LinearMap.range L →ₗ[ℂ] Pi := (LinearMap.ker L).liftQ L₁ hk ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hA₀ : ∀ x, A₀ ⟨L x, LinearMap.mem_range_self L x⟩ = L₁ x := by
    intro x
    simp only [A₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨A, hA⟩ := LinearMap.exists_extend A₀
  have hA' : ∀ x, A (L x) = L₁ x := fun x => by
    rw [← hA₀ x, ← hA]; rfl
  refine ⟨A, fun f hf => ?_, fun f' hf' => ?_⟩
  · have := hA' (⟨f, hf⟩, 0)
    simpa [L, L₁] using this
  · have := hA' (0, ⟨f', hf'⟩)
    simpa [L, L₁] using this

end GlobalTheory.SquareAgree.LieEq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LineKillV

theorem isDatum_list_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd}
    {ψ : AddChar (AF F) ℂ} {Z : Type} {crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z}
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {ι : Type} (l : List ι) (Ψ : ι → (Fin n × Fin d → AF F) → ℂ) (f : ι → Z → ℂ)
    (h : ∀ i, IsDatum M ψ crd (Ψ i) (f i)) : IsDatum M ψ crd (l.map Ψ).sum (l.map f).sum := by
  induction l with
  | nil => simpa using (GlobalTheory.SquareAgree.CoinvPass.isDatum_zero (M := M) (ψ := ψ) (crd := crd))
  | cons a l ih => simpa [List.map_cons, List.sum_cons] using GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ (h a) ih

end GlobalTheory.LineKillV

end
end

