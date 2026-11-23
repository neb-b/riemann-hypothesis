module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientMeasureBesselModelOfLocalQuotient
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotTransport

lemma jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

lemma exists_unit {n m : ℕ} (ε : Fin n → Bool) (H : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (Qi : Matrix (Fin m) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (h3 : Qᴴ * Formalism.REAL.Jm ε * Q = H)
    (y : Matrix (Fin m) (Fin m) ℂ) (hy : yᴴ * H * y = H) :
    ∃ g : Formalism.REAL.UJ ε, ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Q * y⁻¹ * Qi := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := jm_mul_self ε
  have hHi : (Qi * Formalism.REAL.Jm ε * Qiᴴ) * H = 1 := by
    have : H * (Qi * Formalism.REAL.Jm ε * Qiᴴ) = 1 := by
      rw [← h3]
      calc Qᴴ * Formalism.REAL.Jm ε * Q * (Qi * Formalism.REAL.Jm ε * Qiᴴ)
          = Qᴴ * Formalism.REAL.Jm ε * (Q * Qi) * Formalism.REAL.Jm ε * Qiᴴ := by simp only [Matrix.mul_assoc]
        _ = Qᴴ * Qiᴴ := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc Qᴴ (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJ, Matrix.mul_one]
        _ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    exact mul_eq_one_comm.mp this
  have hl : (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = 1 := by
    calc (Qi * Formalism.REAL.Jm ε * Qiᴴ * yᴴ * H) * y = (Qi * Formalism.REAL.Jm ε * Qiᴴ) * (yᴴ * H * y) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, hHi]
  have hdet : IsUnit y.det := Matrix.isUnit_det_of_left_inverse hl
  have hyr : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y hdet
  have hyl : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hdet
  have hy' : (y⁻¹)ᴴ * H * y⁻¹ = H := by
    calc (y⁻¹)ᴴ * H * y⁻¹ = (y⁻¹)ᴴ * (yᴴ * H * y) * y⁻¹ := by rw [hy]
      _ = (y * y⁻¹)ᴴ * H * (y * y⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hyr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    ⟨Q * y⁻¹ * Qi, Q * y * Qi, by
      calc Q * y⁻¹ * Qi * (Q * y * Qi) = Q * (y⁻¹ * (Qi * Q) * y) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyl, Matrix.mul_one, h2],
     by
      calc Q * y * Qi * (Q * y⁻¹ * Qi) = Q * (y * (Qi * Q) * y⁻¹) * Qi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hyr, Matrix.mul_one, h2]⟩
  have hu : u ∈ Formalism.REAL.UJ ε := by
    show Formalism.REAL.inUJ ε (Q * y⁻¹ * Qi)
    unfold Formalism.REAL.inUJ
    calc (Q * y⁻¹ * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * y⁻¹ * Qi)
        = Qiᴴ * ((y⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * y⁻¹) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [h3, hy']
      _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  exact ⟨⟨u, hu⟩, rfl⟩

end GlobalTheory.QuotTransport

namespace GlobalTheory


open GlobalTheory.QuotTransport in
theorem quotMeas_besselModel_of_quotLoc : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)))) (ν.map (fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹))) := by
  intro D X θ C τ γ μ ν hμ hq f hf
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  obtain ⟨g, hg⟩ := exists_unit _ _ (C.Q τ) (C.Qi τ) h1 h2 h3 (C.y τ) (C.y_mem τ)
  have h2' : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M := by
    intro M; rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hγ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      ((γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        ((((γ⁻¹ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.one_mul]
  have hc : Continuous (fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => uMat w) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcM : ∀ {h : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}, Continuous h →
      ∀ (A : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ)
        (B : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ),
      Continuous (fun w => (Matrix.of.symm (A * uMat (h w) * B) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    fun hh A B => (continuous_const.matrix_mul (hc.comp hh)).matrix_mul continuous_const
  have hcβ : Continuous (fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (hcM (continuous_const_mul γ⁻¹) (C.Qi τ) (C.Q τ)).matrix_mul (continuous_const (y := (C.y τ)⁻¹))
  set φ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun w => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) w) with hφ
  set α : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ⁻¹ * y * γ)) with hα
  set β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun z => Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) with hβ
  have hφm : Measurable φ := (hcM continuous_id _ _).measurable
  have hαm : Measurable α := (hcM ((continuous_const.mul continuous_id).mul continuous_const) _ _).measurable
  have hβm : Measurable β := hcβ.measurable
  have hpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))) :=
    Continuous.matrix_mul continuous_snd continuous_fst
  have hj : Measurable (fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j)) :=
    hf.comp hpc.measurable
  have hA : ∀ w, φ (w * g) = β (γ * w) := by
    intro w
    show Matrix.of.symm (C.Qi τ * uMat (w * g) * C.Q τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ⁻¹ * (γ * w)) * C.Q τ * (C.y τ)⁻¹)
    rw [inv_mul_cancel_left]
    congr 1
    simp only [uMat, Subgroup.coe_mul, Units.val_mul, hg, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hB : ∀ y z, β (y * z) = fun i j => (Matrix.of (α y) * Matrix.of (β z)) i j := by
    intro y z
    simp only [hα, hβ, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply, uMat, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc, h2', hγ]
    rfl
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ) = ∫⁻ x, ∫⁻ s,
    f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(μ.map α) ∂(ν.map β)
  rw [lintegral_map (hj.lintegral_prod_right' (ν := μ.map α)) hβm]
  calc ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map φ)
      = ∫⁻ w, f (φ w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_map hf hφm
    _ = ∫⁻ w, f (φ (w * g)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        (lintegral_mul_right_eq_self (fun w => f (φ w)) g).symm
    _ = ∫⁻ w, f (β (γ * w)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by simp only [hA]
    _ = ∫⁻ w, f (β w) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_mul_left_eq_self (fun w => f (β w)) γ
    _ = ∫⁻ z, ∫⁻ y, f (β (y * z)) ∂μ ∂ν := hq _ (hf.comp hβm)
    _ = ∫⁻ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (β z)) i j) ∂(μ.map α) ∂ν := by
        refine lintegral_congr fun z => ?_
        have hmz : Measurable (fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
            f (fun i j => (Matrix.of s * Matrix.of (β z)) i j)) := hj.comp measurable_prodMk_left
        rw [lintegral_map hmz hαm]
        simp only [hB]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
section
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open Matrix Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RatDiscrete

theorem finite_bounded {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) (B : ℝ) :
    {x : n → E | x ∈ Λ ∧ ∀ (τ : E →+* ℂ) i, ‖τ (x i)‖ ≤ B}.Finite := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hm' : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm0
  have h1 := (NumberField.Embeddings.finite_of_norm_le E ℂ (‖(m : ℂ)‖ * B)).preimage
    (f := fun a : E => (m : E) * a) (mul_right_injective₀ hm').injOn
  refine (Set.Finite.pi' fun _ : n => h1).subset fun x hx i => ⟨hΛ x hx.1 i, fun τ => ?_⟩
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left (hx.2 τ i) (norm_nonneg _)

variable (I : AutInst)

theorem exists_place (τ : I.E →+* ℂ) : ∃ v, ∀ a, ‖τ a‖ = ‖I.φ v a‖ := by
  haveI := I.cm.totReal
  let ψ : I.F →+* ℂ := τ.comp (algebraMap I.F I.E)
  have hψ : ComplexEmbedding.IsReal ψ :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk ψ))
  refine ⟨InfinitePlace.mk ψ, fun a => ?_⟩
  obtain ⟨b, hb⟩ := (I.cm.fixed (a * star a)).1 (by rw [star_mul, star_star])
  have h1 : τ (a * star a) = I.φ (InfinitePlace.mk ψ) (a * star a) := by
    rw [← hb, I.φ_over, InfinitePlace.embedding_mk_eq_of_isReal hψ]
    rfl
  have h2 := congrArg norm h1
  simp only [map_mul, I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj] at h2
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h2

def IsImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) (x : I.GA) : Prop :=
  (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v) ∧
    I.fmat x.2 = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))

theorem subsingleton_isImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) :
    {x | IsImage I γ x}.Subsingleton := fun _ hx _ hy =>
  Prod.ext (funext fun v => Subtype.ext (Units.ext ((hx.1 v).trans (hy.1 v).symm)))
    (Subtype.ext (Units.ext (hx.2.trans hy.2.symm)))

theorem P_det (v) : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)

theorem isImage_one : IsImage I 1 1 := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (P_det I v)]
    rfl
  · rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem isImage_mul {γ δ x y} (hx : IsImage I γ x) (hy : IsImage I δ y) :
    IsImage I (γ * δ) (x * y) := by
  refine ⟨fun v => ?_, ?_⟩
  · have : uMat ((x * y).1 v) = uMat (x.1 v) * uMat (y.1 v) := rfl
    rw [this, hx.1, hy.1, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
  · have : I.fmat (x * y).2 = I.fmat x.2 * I.fmat y.2 := rfl
    rw [this, hx.2, hy.2, Matrix.map_mul]

theorem isImage_inv {γ : GL (Fin I.n) I.E} {x} (hx : IsImage I γ x) :
    IsImage I (γ⁻¹ : GL (Fin I.n) I.E) x⁻¹ := by
  refine ⟨fun v => ?_, ?_⟩
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.1 v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) ?_
    have := hx.1 v
    unfold uMat at this
    rw [this]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
    rw [← Matrix.mul_assoc (Matrix.map _ _), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.nonsing_inv_mul _ (P_det I v)]
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) ?_
    have := hx.2
    unfold AutInst.fmat at this
    rw [this, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

def ratSub : Subgroup I.GA where
  carrier := I.GFset
  one_mem' := ⟨1, one_mem _, isImage_one I⟩
  mul_mem' := fun ⟨γ, hγ, hx⟩ ⟨δ, hδ, hy⟩ => ⟨γ * δ, mul_mem hγ hδ, isImage_mul I hx hy⟩
  inv_mem' := fun ⟨γ, hγ, hx⟩ => ⟨γ⁻¹, inv_mem hγ, isImage_inv I hx⟩

theorem countable_GFset : I.GFset.Countable := by
  haveI : Countable I.E := Countable.of_equiv _ (Module.finBasis ℚ I.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin I.n) (Fin I.n) I.E) :=
    inferInstanceAs (Countable (Fin I.n → Fin I.n → I.E))
  refine (Set.countable_iUnion fun γ => (subsingleton_isImage I γ).countable).mono ?_
  rintro x ⟨γ, -, hx⟩
  exact Set.mem_iUnion.2 ⟨γ, hx⟩

theorem exists_bound {C : Set I.GA} (hC : IsCompact C) : ∃ B : ℝ, ∀ x ∈ C, ∀ v i j,
    ‖(I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j‖ ≤ B := by
  have hc : Continuous fun x : I.GA => fun v i j => (I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j := by
    refine continuous_pi fun v => ?_
    exact (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp
      ((continuous_apply v).comp continuous_fst)))).matrix_mul continuous_const
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨B, fun x hx v i j => (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
    ((norm_le_pi_norm _ v).trans (hB x hx)))⟩

theorem finite_coset (g : I.Gf) (B : ℝ) :
    {γ : Matrix (Fin I.n) (Fin I.n) I.E | (∀ v i j, ‖I.φ v (γ i j)‖ ≤ B) ∧
      ∃ y : I.Gf, g⁻¹ * y ∈ I.Kset ∧ I.fmat y = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))}.Finite := by
  classical
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  obtain ⟨c, hc0, hlow⟩ := Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨d, hd0, hup⟩ := Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
  rw [← hL] at hlow hup
  set G : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := g.1 with hGdef
  obtain ⟨e, he, s, hs, hsg, -⟩ := Formalism.UG.P.levelaf_exists_denom (E := I.E) G
  have hfin := Formalism.UG.P.adelstab_finite G I.Lf d e hd0 he hup (Formalism.UG.P.adelstab_entries G e s hs hsg)
  set u : I.E := algebraMap (𝓞 I.F) I.E c with hu
  have hu0 : u ≠ 0 := Formalism.UG.P.adelstab_algebraMap_ne_zero c hc0
  obtain ⟨Bu, hBu⟩ : ∃ Bu : ℝ, ∀ τ : I.E →+* ℂ, ‖τ u‖ ≤ Bu :=
    ⟨_, fun τ => Finite.le_ciSup (fun τ : I.E →+* ℂ => ‖τ u‖) τ⟩
  have h1 := (Set.Finite.pi' fun _ : Fin I.n => finite_bounded _ hfin (Bu * B)).preimage
    (f := fun (γ : Matrix (Fin I.n) (Fin I.n) I.E) j i => u * γ i j) (by
      intro a _ b _ h
      ext i j
      exact mul_left_cancel₀ hu0 (congrFun (congrFun h j) i))
  refine h1.subset ?_
  rintro γ ⟨hb, y, hy, hγ⟩ j
  refine ⟨?_, fun τ i => ?_⟩
  · have hs : (Pi.single j (Formalism.UG.P.levelafC I.E c) : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ I.Lf := by
      convert hlow (Pi.single j 1) fun i => ?_ using 1
      · funext i
        by_cases h : i = j <;> simp [h]
      · rw [Pi.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
    have h2 := (hy _).1 hs
    rw [Formalism.UG.P.adelstab_mem_iff]
    convert h2 using 1
    change _ = (((G⁻¹ : GL _ _) : Matrix _ _ _) * I.fmat y) *ᵥ _
    rw [← Matrix.mulVec_mulVec, hγ]
    congr 1
    funext i
    simp [hu, Formalism.UG.P.adelstab_incl_C, mul_comm]
  · obtain ⟨v, hv⟩ := exists_place I τ
    simp only [map_mul, norm_mul]
    rw [hv (γ i j)]
    exact mul_le_mul (hBu τ) (hb v i j) (norm_nonneg _) ((norm_nonneg _).trans (hBu τ))

theorem finite_inter {C : Set I.GA} (hC : IsCompact C) : (C ∩ I.GFset).Finite := by
  obtain ⟨-, -, -, -, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨B, hB⟩ := exists_bound I hC
  obtain ⟨t, -, ht⟩ := (hC.image continuous_snd).elim_nhds_subcover
    (fun g => {y | g⁻¹ * y ∈ I.Kset}) fun g _ =>
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by
        show g⁻¹ * g ∈ I.Kset
        rw [inv_mul_cancel, ← hK]
        exact K.one_mem)
  refine ((t.finite_toSet.biUnion fun g _ => finite_coset I g B).biUnion
    fun γ _ => (subsingleton_isImage I γ).finite).subset ?_
  rintro x ⟨hx, γ, -, hγ⟩
  obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 (ht ⟨x, hx, rfl⟩)
  refine Set.mem_iUnion₂.2 ⟨γ, Set.mem_iUnion₂.2 ⟨g, hg, fun v i j => ?_, x.2, hgx, hγ.2⟩, hγ⟩
  have := hB x hx v i j
  rw [hγ.1 v] at this
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v),
    Matrix.mul_nonsing_inv _ (P_det I v), Matrix.mul_one, Matrix.map_apply] using this

theorem isFundamentalDomain (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) : IsFundamentalDomain (ratSub I) fund (I.muA μf) := by
  refine IsFundamentalDomain.mk'' h.1.nullMeasurableSet (ae_of_all _ fun y => ?_) (fun γ hγ => ?_)
    fun γ => ((measurePreserving_mul_left (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) (γ : I.GA).1).prod
      (measurePreserving_mul_left μf (γ : I.GA).2)).quasiMeasurePreserving
  · obtain ⟨γ, hγ, hy⟩ := h.2.1 y
    exact ⟨⟨γ, hγ⟩, hy⟩
  · exact h.2.2 γ γ.2 fun e => hγ (Subtype.ext e)

theorem rational_points : ∀ I : AutInst, ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ Countable Γ ∧ (∀ C : Set I.GA, IsCompact C → (C ∩ I.GFset).Finite) ∧ ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → IsFundamentalDomain Γ fund (I.muA μf) :=
  fun I => ⟨ratSub I, rfl, (countable_GFset I).to_subtype, fun _ hC => finite_inter I hC,
    fun μf _ _ fund h => isFundamentalDomain I μf fund h⟩

end GlobalTheory.RatDiscrete
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentOrbitCover
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepCover

theorem isIsot_span (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (h : R ≤ perpIn I x R) : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  have hspan : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
      Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)) :=
    Submodule.span_mono h

  have h1 : ∀ s ∈ R, ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 :=
    fun s hs y hy => GlobalTheory.FlagIso.hform_span I x R (hspan hy) hs

  have h2 : ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      ∀ z ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
        Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    have hker : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
        LinearMap.ker (GlobalTheory.FlagIso.hR I.J y) := by
      rw [Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply,
        ← GlobalTheory.FlagIso.hform_star I.J I.J_herm s y, h1 s hs y hy, star_zero]
    have hz' := hker hz
    rwa [LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply] at hz'
  refine ⟨?_, h2⟩
  intro hbot
  apply h0
  rw [eq_bot_iff]
  intro r hr
  have hr' : r ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [hbot] at hr'
  exact (Submodule.mem_bot _).2 ((Submodule.mem_bot _).1 hr')

theorem unipotent_orbit_cover : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W : Submodule I.E (Fin I.n → I.E), I.IsIsot W ∧ ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA W → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ y ∈ omega I x W ((I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4), ((ν, 1) : I.GA) * x = γ * y * (1, k) := by
  intro I x g q hg hn hq hlt

  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  obtain ⟨hpieces, hzero⟩ := hspec a S τ hF
  obtain ⟨ha0, hτ0⟩ := hzero hn
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hlt)
    · exact h
  obtain ⟨hall, -, -, hstep⟩ := _root_.GlobalTheory.FlagPieces.flag_pieces I x a S τ hF
  obtain ⟨-, -, hSlast, hτmono, hτ, -⟩ := hF

  obtain ⟨τ', hτ'⟩ : ∃ f : ℕ → ℝ, f = fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 := ⟨_, rfl⟩
  have hτ'lt : ∀ i (h : i < a), τ' i = τ ⟨i, h⟩ := by
    intro i h; rw [hτ']; exact dif_pos h
  have hτ'ge : ∀ i, a ≤ i → τ' i = 1 / 2 := by
    intro i h; rw [hτ']; exact dif_neg (not_lt.2 h)
  have hpos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    rcases lt_or_ge i a with h | h
    · rw [hτ'lt i h]; exact (hτ ⟨i, h⟩).1
    · rw [hτ'ge i h]; norm_num
  have hinc : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    rw [hτ'lt i hi]
    rcases lt_or_ge (i + 1) a with h | h
    · rw [hτ'lt (i + 1) h]
      exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · rw [hτ'ge (i + 1) h]; exact (hτ ⟨i, hi⟩).2.1
  have hlast : τ' a = 1 / 2 := hτ'ge a le_rfl

  have hrk : ∀ i (hi : i ≤ a), i ≤ rkK (S ⟨i, Nat.lt_succ_of_le hi⟩) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 : rkK (S (Fin.castSucc ⟨k, hk⟩)) < rkK (S (Fin.succ ⟨k, hk⟩)) :=
        ((hpieces ⟨k, hk⟩).2.1)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt h1 h2)
  obtain ⟨-, hrkR, -⟩ := GlobalTheory.FlagIso.flag_isotropic I x
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 : a ≤ rkK (S (Fin.last a)) := hrk a le_rfl
    rw [hSlast] at h1
    exact h1.trans ((hrkR v).trans (hq v))

  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hpos hinc hlast
  rw [hτ'lt 0 ha, hτ0 ha, hτ'lt b hb] at hratio hsq
  have hi_pos : 0 < τ ⟨b, hb⟩ := (hτ ⟨b, hb⟩).1
  have hlo_pos : 0 < τ' (b + 1) := hpos (b + 1) hb
  obtain ⟨-, -, -, hne, hlarge, hgeL⟩ := hstep ⟨b, hb⟩
  have hRperp : S (Fin.succ ⟨b, hb⟩) ≤ perpIn I x (S (Fin.succ ⟨b, hb⟩)) :=
    le_trans (hall _).2.2.1 (hall _).2.2.2.1
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S (Fin.succ ⟨b, hb⟩)) :=
    (hall _).1
  have hlo : ∀ N, S (Fin.succ ⟨b, hb⟩) < N → N ≤ lamX I x →
      τ' (b + 1) ≤ sizeQ (bas I) (frm I x) N (S (Fin.succ ⟨b, hb⟩)) := by
    rw [hτ']; exact hgeL
  refine ⟨Submodule.span I.E (S (Fin.succ ⟨b, hb⟩) : Set (Fin I.n → I.E)),
    isIsot_span I x _ hne hRperp, ?_⟩
  intro ν hν
  obtain ⟨γ, ⟨hγF, -⟩, hk, A, Z, hAZ, heq, hbound, hst⟩ :=
    _root_.GlobalTheory.SmallFund.small_fundamental_set I x g (S (Fin.succ ⟨b, hb⟩)) (τ' (b + 1)) (τ ⟨b, hb⟩)
      ((2 * least I x) ^ ((1 : ℝ) / q)) hg hsat hne hRperp hi_pos hlarge hlo
      ((div_le_iff₀ hlo_pos).1 hratio) hsq ν hν

  obtain ⟨m, -, hm⟩ := hst 1 1
  have hm' : ∀ v, uMat (m v) * uMat (x.1 v) =
      uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
    intro v; simpa only [Complex.ofReal_one, one_smul] using hm v

  obtain ⟨-, -, -, -, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨-, ⟨K, hK⟩, -⟩ := hKg g hg
  have hkinv : ((x⁻¹ * γ * x).2)⁻¹ ∈ I.Kg g := by
    rw [← hK] at hk ⊢
    exact K.inv_mem hk
  refine ⟨γ, hγF, ((x⁻¹ * γ * x).2)⁻¹, hkinv, ((m * x.1 : I.Ginf), x.2), ?_, ?_⟩
  · refine ⟨rfl, A, Z, hAZ, hbound, fun v => ?_, hst⟩
    show uMat (m v) * uMat (x.1 v) = _
    exact hm' v
  · have key : ∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * (uMat (m v) * uMat (x.1 v)) := by
      intro v
      rw [heq v, hm' v]
      simp only [mul_assoc]
    refine Prod.ext ?_ ?_
    · show ν * x.1 = γ.1 * (m * x.1) * 1
      rw [mul_one]
      funext v
      exact Subtype.ext (Units.ext (key v))
    · show 1 * x.2 = γ.2 * x.2 * ((x⁻¹ * γ * x).2)⁻¹
      simp only [Prod.snd_mul, Prod.snd_inv]
      group

end GlobalTheory.DeepCover
end

