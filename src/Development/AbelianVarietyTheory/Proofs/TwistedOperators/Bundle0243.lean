module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfAdelicHomDecomposeIsotropicMiddleComplement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem adj_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) (B : Matrix (Fin b) (Fin c) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) : adj D (adj D A) = A := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_one {a : ℕ} : adj D (1 : Matrix (Fin a) (Fin a) D.host.E) = 1 := by
  simp [adj, Formalism.UG.cT]

theorem adj_zero {a b : ℕ} : adj D (0 : Matrix (Fin a) (Fin b) D.host.E) = 0 := by
  simp [adj, Formalism.UG.cT]

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem exists_decomp_one (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B)
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (hKC : K * C = 1) (hKB : K * B = 0) :
    ∃ N' : Matrix (Fin V.rank) (Fin r) D.host.E,
      C * K + (B * (V'.gram⁻¹ * adj D B * V.gram) + N' * (adj D C * V.gram)) = 1 := by
  set G := V.gram
  set Pi := adj D C * G
  set Pm := V'.gram⁻¹ * adj D B * G
  set N := G⁻¹ * adj D K
  set N' := N - C * (K * N) - B * (Pm * N)
  have hG := GlobalTheory.LatVac.gram_det_isUnit V
  have hG' := GlobalTheory.LatVac.gram_det_isUnit V'
  have hPiC : Pi * C = 0 := hs.frame.2.2
  have hPiB : Pi * B = 0 := hs.orth
  have hBC : adj D B * G * C = 0 := by
    have h := congrArg (adj D) hs.orth
    rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero, ← Matrix.mul_assoc] at h
    exact h
  have hPmC : Pm * C = 0 := by
    simp only [Pm, Matrix.mul_assoc] at hBC ⊢
    rw [hBC, Matrix.mul_zero]
  have hPmB : Pm * B = 1 := by
    simp only [Pm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (adj D B), hs.isom, Matrix.nonsing_inv_mul _ hG']
  have hPiN : Pi * N = 1 := by
    simp only [Pi, N, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, ← adj_mul, hKC, adj_one]
  have hKN' : K * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hKC, hKB, Matrix.one_mul, Matrix.zero_mul, sub_self, sub_zero]
  have hPmN' : Pm * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPmC, hPmB, Matrix.one_mul, Matrix.zero_mul, sub_zero, sub_self]
  have hPiN' : Pi * N' = 1 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPiC, hPiB, Matrix.zero_mul, sub_zero]
    simpa only [Pi, N, Matrix.mul_assoc] using hPiN
  let M : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows K (Matrix.fromRows Pm Pi)
  let Q : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E :=
    Matrix.fromCols C (Matrix.fromCols B N')
  have hMQ : M * Q = 1 := by
    simp only [M, Q, Matrix.fromRows_mul, Matrix.mul_fromCols, hKC, hKB, hKN', hPmC, hPmB, hPmN', hPiC, hPiB, hPiN']
    refine Matrix.ext fun a b => ?_
    rcases a with a | a | a <;> rcases b with b | b | b <;> simp [Matrix.one_apply]
  have e : Fin r ⊕ (Fin V'.rank ⊕ Fin r) ≃ Fin V.rank :=
    Fintype.equivOfCardEq (by simp [hs.rank]; ring)
  have hQM : Q * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hMQ
  refine ⟨N', ?_⟩
  simpa only [M, Q, Matrix.fromCols_mul_fromRows] using hQM

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

theorem half_decomp : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ (a : AE D) (u : WO V W), IsHalf a u → ∃ (y : Mx D W.rank r) (x : WO V' W) (t : Mx D W.rank r), IsHalf a y ∧ IsHalf a x ∧ IsHalf a t ∧ u = isoPart V W C y + midPart V V' W B x + restEmb V W K t := by
  intro D V V' W r C B hs K hKC hKB a u hu
  obtain ⟨N', hN'⟩ := exists_decomp_one V V' C B hs K hKC hKB
  refine ⟨HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (N'.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (B.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (C.map (incA D)),
    isHalf_mul hu _, isHalf_mul hu _, isHalf_mul hu _, ?_⟩
  have h1 := congrArg (fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (incA D)) hN'
  simp only [Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [isoPart, midPart, restEmb, Matrix.map_mul, Matrix.mul_assoc]
  conv_lhs => rw [← Matrix.mul_one u, ← h1]
  simp only [Matrix.map_add _ (map_add (incA D)), Matrix.map_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

end GlobalTheory.HalfDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

variable {D : D7}

def halfPair (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AE D :=
  ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j

def halfSympl (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * halfPair W a t)

theorem halfSympl_add_right (W : HSp D) {r : ℕ} (a t t' : Mx D W.rank r) :
    halfSympl W a (t + t') = halfSympl W a t + halfSympl W a t' := by
  simp only [halfSympl, halfPair]
  rw [← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_add]

theorem halfSympl_add_left (W : HSp D) {r : ℕ} (a a' t : Mx D W.rank r) :
    halfSympl W (a + a') t = halfSympl W a t + halfSympl W a' t := by
  simp only [halfSympl, halfPair]
  rw [← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [add_mul]

theorem halfSympl_zero_right (W : HSp D) {r : ℕ} (a : Mx D W.rank r) : halfSympl W a 0 = 0 := by
  simp [halfSympl, halfPair]

theorem halfSympl_zero_left (W : HSp D) {r : ℕ} (t : Mx D W.rank r) : halfSympl W 0 t = 0 := by
  simp [halfSympl, halfPair]

end GlobalTheory.HalfAverage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelUnramifiedUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaAbsU

theorem hasSum_norm_kerU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α ∧ HasSum (fun a : GU σ r ⧸ KU σ r => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹)) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hK
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : q ≠ 0 := by omega
  obtain ⟨-, -, hS⟩ := GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivial_hyp hU hq0 r
  obtain ⟨x, hx⟩ := hS.exists_vec
  have bound : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r (GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0) := by
    intro i
    have hi := i.2
    have h2 : 2 * i.val + 2 ≤ r := by omega
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hn : ‖(GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0 i : ℂ)‖ = (q : ℝ) ^ ((r : ℝ) - 1 - 2 * (i.val : ℝ)) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam, Units.val_zpow_eq_zpow_val, norm_zpow, Units.val_mk0, Complex.norm_natCast,
        ← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    have hlow : ((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)) = (q : ℝ) ^ (-((r : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
      congr 1
      push_cast
      ring
    rw [hn, hlow, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq]
    have h2' : 2 * (i.val : ℝ) + 2 ≤ r := by exact_mod_cast h2
    have h0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> linarith
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0, bound, ?_⟩
  have hKψ : KerU ϖ q (r + t) 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
    intro d g hg k₁ hk₁ k₂ hk₂
    simp only
    rw [hK d g hg k₁ hk₁ k₂ hk₂]
    simp [norm_zpow, hz]
  have h := _root_.GlobalTheory.ZetaSumU.hasSum_zetaSum_inert L ϖ σ q r t hU hrt 1 _ (by simp) hKψ ℂ (GlobalTheory.LGrp.charRep 1) x _ hx bound LinearMap.id
    ⟨‖x‖, fun g => by simp⟩
  have hx0 : x ≠ 0 := hx.1
  have h' := h.mul_right x⁻¹
  simpa [mul_assoc, mul_inv_cancel₀ hx0] using h'

end GlobalTheory.ZetaAbsU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionFinitePlaceLatticeVacuaScal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCompress

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_half_idem (v : FinPl D) (h : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ b : AE D, finPart D b ∈ intAE D ∧ b + b = idem D (.inl v) := by
  have h2 : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
    GlobalTheory.LatVac.half_mem_adicCompletionIntegers D.host.F v h
  have hsum : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ +
      algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ = 1 := by
    rw [← map_add (f := _), ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v
      (algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹)), ?_, ?_⟩
  · unfold intAE finPart
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v ⟨_, h2⟩, 1, ?_⟩
    simp [GlobalTheory.SplitIdem.placeHom, Algebra.TensorProduct.algebraMap_apply] <;> rfl
  · rw [← map_add (f := _), ← map_add (f := _), hsum]
    rfl

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem exists_char_act (v : FinPl D) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v)
    (hi : idem D (.inl v) • u = u) :
    ∃ y : AF D.host.F, ∀ f, IsLatVac (heisO ψ S T) (latO S T LS LT fun w => w = v) f →
      heisO ψ S T u f = ψ y • f := by
  classical
  have hidem := (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.2.2.1 v
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · obtain ⟨e, hee, hec, hsum, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    have hsum' : e + cA D e = idem D (.inl v) := by rw [hsum]; rfl
    have hsp : IsSplitIdem D e := by
      unfold IsSplitIdem
      exact ⟨hee, hec, v, _, hidem.2.2, hsum⟩
    have hsp' : IsSplitIdem D (cA D e) := isSplitIdem_conj hsp
    have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
    have hint : finPart D e ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])
    have hint' : finPart D (cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
    have hm1 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e hint u hu
    have hm2 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ (cA D e) hint' u hu
    have hh1 : IsHalf e (e • u) := (isHalf_iff e (e • u)).2 (by rw [smul_smul, hee])
    have hh2 : IsHalf (cA D e) (cA D e • u) := (isHalf_iff (cA D e) (cA D e • u)).2 (by rw [smul_smul, hcc])
    have hsplit : e • u + cA D e • u = u := by rw [← add_smul, hsum', hi]
    refine ⟨-symplOH S T (e • u) (cA D e • u), fun f hf => ?_⟩
    unfold IsLatVac at hf
    have k1 := hf.2 e hsp _ hm1 hh1
    have k2 := hf.2 _ hsp' _ hm2 hh2
    have key := heisO_heisO ψ S T (e • u) (cA D e • u) f
    rw [k2, k1, hsplit] at key
    conv_rhs => rw [key]
    rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]
  · obtain ⟨b, hb, hbb⟩ := exists_half_idem v h2
    refine ⟨0, fun f hf => ?_⟩
    unfold IsLatVac at hf
    have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ b hb u hu
    have h2u : 2 • (b • u) = u := by rw [two_nsmul, ← add_smul, hbb, hi]
    rw [AddChar.map_zero_eq_one, one_smul, ← h2u]
    exact hf.1 _ hm

private theorem ipO_smul_smul' {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ)
    (f g : Mx D m n → ℂ) : ipO μ 𝓕 (a • f) (b • g) = (a * starRingEnd ℂ b) * ipO μ 𝓕 f g := by
  unfold ipO
  rw [← integral_const_mul]
  congr 1
  ext t
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem compress_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (w : WO S T), ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inl v) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ S T ΛS ΛT μ 𝓕 hψ hS hT hμ v w
  classical
  have hn : ∀ a, ‖ψ a‖ = 1 := by
    have h := hψ
    unfold IsStdChar IsCharAF at h
    exact h.1.2.1
  obtain ⟨hI1, -, hI3, hI4, -⟩ := _root_.GlobalTheory.PlaceTensor.idem_spec D
  obtain ⟨ι, hι⟩ : ∃ ι, ι = idem D (.inl v) := ⟨_, rfl⟩
  have hιι : ι * ι = ι := by rw [hι]; exact hI1 _
  have hcι : cA D ι = ι := by rw [hι]; exact hI3 _
  have hinf : infPart D ι = 0 := by rw [hι]; exact (hI4 v).1
  obtain ⟨x, hx⟩ : ∃ x, x = ι • w := ⟨_, rfl⟩
  rw [wAt_eq_smul, ← hι, ← hx]
  have hιx : ι • x = x := by rw [hx, smul_smul, hιι]
  have hloc : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT (fun _ => True) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => Sum.inl.inj h'.2) h
  have hloc' : ∀ u ∈ latO S T ΛS ΛT (fun u => u = v), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((_root_.GlobalTheory.LatticeLocal.wAt_mem_latO D S T ΛS ΛT (fun u => u = v) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => h'.1) h
  have hpair : ∀ a, symplO S T (ι • a) x = symplO S T a x := by
    intro a
    rw [symplO_smul, hcι, hιx]
  by_cases hA : ∀ l ∈ latO S T ΛS ΛT (fun u => u = v), ψ (symplO S T l x) = 1
  · have hxg : x ∈ latO S T ΛS ΛT (fun _ => True) := by
      refine ((_root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 x ?_).2 ?_
      · rw [hx]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hinf]
      · intro u' hu'
        rw [symplO_skew, AddChar.map_neg_eq_inv, ← hpair, hA _ (hloc u' hu'), inv_one]
    have hxv : x ∈ latO S T ΛS ΛT (fun u => u = v) := by
      rw [← hιx]
      exact hloc x hxg
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v hxv (by rw [← hι]; exact hιx)
    refine ⟨starRingEnd ℂ (ψ y), fun f g hf hg hvf hvg => ?_⟩
    rw [hy f hvf]
    exact ((_root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f hg hf).2.2.1 (ψ y)).2
  · push_neg at hA
    obtain ⟨l, hl, hl1⟩ := hA
    have hιl : ι • (ι • l) = ι • l := by rw [smul_smul, hιι]
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v (hloc' l hl) (by rw [← hι]; exact hιl)
    refine ⟨0, fun f g hf hg hvf hvg => ?_⟩
    rw [zero_mul]
    have hxf : IsThetaFunO ψ S T (heisO ψ S T x f) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 x f hf
    have hU := ((_root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g (heisO ψ S T x f) hg hxf).2.2.2.2.2.2.1 (ι • l)).1
    rw [hy g hvg, heisO_comm, hy f hvf, heisO_smul, smul_smul, ipO_smul_smul', map_mul] at hU
    have hc : ψ y * starRingEnd ℂ (ψ y) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num
    have hs : starRingEnd ℂ (ψ (symplO S T (ι • l) x)) ≠ 1 := by
      rw [hpair]
      intro h
      exact hl1 ((starRingEnd ℂ).injective (by rw [h, map_one]))
    have h0 : (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) - 1) * ipO μ 𝓕 g (heisO ψ S T x f) = 0 := by
      linear_combination hU - (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) * ipO μ 𝓕 g (heisO ψ S T x f)) * hc
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hs)

end GlobalTheory.PlaceCompress
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableAdelicMatrixRapidDecayCompactFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicIntegrable

theorem integrable_of_rapid_decay : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  intro D a b μ hμ θ hθ f hf K hK hKf hdec
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ

  let π : Mx D a b → (Fin a → Fin b → D.what₂.Tau → ℂ) := fun y i j τ => θ τ (infPart D (y i j))
  have hπc : Continuous π := continuous_pi fun i => continuous_pi fun j => continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp (continuous_apply i))
  have hπm : Measurable π := hπc.measurable

  let s : (Fin a → Fin b → D.what₂.Tau → ℂ) → Mx D a b := fun c => Matrix.of fun i j => σ (c i j)
  have hπs : ∀ c y, π (s c + y) = c + π y := by
    intro c y; funext i j τ
    show θ τ (infPart D (σ (c i j) + y i j)) = c i j τ + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp]
  have hfs : ∀ c (y : Mx D a b), (s c + y).map (finPart D) = y.map (finPart D) := by
    intro c y; ext i j
    show finPart D (σ (c i j) + y i j) = finPart D (y i j)
    rw [RingHom.map_add (f := _), hσ.fin, zero_add]
  let S : Set (Mx D a b) := {y | y.map (finPart D) ∈ K}
  let ν : Measure (Fin a → Fin b → D.what₂.Tau → ℂ) := (μ.restrict S).map π
  have hνA : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπm hA, Measure.restrict_apply (hπm hA)]
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => Measure.ext fun A hA => ?_⟩
    rw [Measure.map_apply (measurable_const_add c) hA, hνA _ (measurable_const_add c hA), hνA _ hA]
    have e : π ⁻¹' ((fun x => c + x) ⁻¹' A) ∩ S = (fun y => s c + y) ⁻¹' (π ⁻¹' A ∩ S) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, S, Set.mem_setOf_eq, hπs, hfs]
    rw [e, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun A hA => ?_⟩
    obtain ⟨R, hR⟩ := hA.isBounded.exists_norm_le
    choose C hC hCK using fun i j => GlobalTheory.StabCompact.exists_compact_adele D θ hθ R
      ((fun M : Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) => M i j) '' K)
      (hK.image ((continuous_apply j).comp (continuous_apply i)))
    have hc : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => C i j : Set (Mx D a b)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => hC i j
    rw [hνA _ hA.isClosed.measurableSet]
    haveI : IsFiniteMeasureOnCompacts μ := hμ.toIsFiniteMeasureOnCompacts
    refine lt_of_le_of_lt (measure_mono ?_) (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := μ) hc)
    rintro y ⟨hyA, hyS⟩ i - j -
    refine hCK i j _ ⟨_, hyS, rfl⟩ fun ρ => le_trans ?_ (hR _ hyA)
    exact (norm_le_pi_norm (π y i j) ρ).trans ((norm_le_pi_norm (π y i) j).trans (norm_le_pi_norm (π y) i))
  have hνe : ν = ν.addHaarScalarFactor Measure.addHaar • (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul ν Measure.addHaar

  set N : ℕ := Module.finrank ℝ (Fin a → Fin b → D.what₂.Tau → ℂ) + 1 with hN
  obtain ⟨C, hC⟩ := hdec N
  let G : (Fin a → Fin b → D.what₂.Tau → ℂ) → ℝ := fun x => C * (1 + ‖x‖) ^ (-(N : ℝ))
  have hGv : Integrable G (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C
  have hGν : Integrable G ν := by
    rw [hνe]; exact hGv.smul_measure ENNReal.coe_ne_top
  have hGπ : Integrable (G ∘ π) (μ.restrict S) :=
    (integrable_map_measure hGν.aestronglyMeasurable hπm.aemeasurable).1 hGν
  have hbound : ∀ y, ‖f y‖ ≤ G (π y) := by
    intro y
    have hsum : ‖π y‖ ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2
        fun j => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ τ))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    have h1 : 0 < 1 + ‖π y‖ := by positivity
    have h2 : (1 + ‖π y‖) ^ N ≤ (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N :=
      pow_le_pow_left₀ h1.le (by linarith) N
    have h3 := hC y
    have h4 : (1 + ‖π y‖) ^ N * ‖f y‖ ≤ C := le_trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h3
    show ‖f y‖ ≤ C * (1 + ‖π y‖) ^ (-(N : ℝ))
    rw [Real.rpow_neg h1.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1 N), mul_comm]
    exact h4
  have hfS : IntegrableOn f S μ :=
    hGπ.mono' hf.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hbound)
  exact hfS.integrable_of_forall_notMem_eq_zero fun y hy => hKf y hy

end GlobalTheory.AdelicIntegrable

end
end

