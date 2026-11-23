module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacFlip

open GlobalTheory.DblVac

open Matrix

section Idem

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι κ : Type} [Fintype ι] [DecidableEq ι]

theorem idem_sandwich {e : R} (he : e * e = e) (N X : Matrix ι ι A) :
    ((1 - e) • (1 : Matrix ι ι A) + e • N) * X * ((1 - e) • (1 : Matrix ι ι A) + e • N) =
      (1 - e) • X + e • (N * X * N) := by
  have h11 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h10 : (1 - e) * e = 0 := by linear_combination -he
  have h01 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    h11, h10, h01, he, zero_smul, add_zero, zero_add]

end Idem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_idem_eq_zero (v : Pl (F := F)) {x : AF F} (hx : evFin F v x = 0) : x * GlobalTheory.LatVac.liftV v 1 = 0 :=
  GlobalTheory.LatVac.at_liftV v 1 x hx

theorem idem_mul_self (v : Pl (F := F)) : GlobalTheory.LatVac.liftV v 1 * GlobalTheory.LatVac.liftV v 1 = (GlobalTheory.LatVac.liftV v 1 : AF F) := by
  have h := mul_idem_eq_zero v (x := GlobalTheory.LatVac.liftV v 1 - 1)
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rwa [sub_mul, one_mul, sub_eq_zero] at h

def flipM (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := fromBlocks 1 0 0 (-1)

theorem flipM_mul_self (d : ℕ) : flipM (F := F) (E := E) d * flipM d = 1 := by
  simp [flipM, fromBlocks_multiply, ← fromBlocks_one]

theorem flipM_transpose (d : ℕ) : (flipM (F := F) (E := E) d)ᵀ = flipM d := by
  simp [flipM, fromBlocks_transpose]

theorem flipM_dbl {d : ℕ} (J : Matrix (Fin d) (Fin d) (AE F E)) : flipM d * dbl J * flipM d = dbl J := by
  simp [flipM, dbl, fromBlocks_multiply]

theorem flipM_diagCols (d : ℕ) : flipM (F := F) (E := E) d * diagCols (Fin d) = antiCols d := by
  change @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
    (flipM (F := F) (E := E) d) (diagCols (Fin d)) = antiCols d
  simp [flipM, diagCols, antiCols, Matrix.fromBlocks_mul_fromRows]

theorem flipM_antiCols (d : ℕ) : flipM (F := F) (E := E) d * antiCols d = diagCols (Fin d) := by
  change @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
    (flipM (F := F) (E := E) d) (antiCols d) = diagCols (Fin d)
  simp [flipM, antiCols, diagCols, Matrix.fromBlocks_mul_fromRows]

theorem flipM_map (σ : E →ₐ[F] E) (d : ℕ) : (flipM (F := F) (E := E) d).map (cA σ) = flipM d := by
  ext (i | i) (j | j) <;> simp [flipM, Matrix.one_apply] <;> split_ifs <;> simp

section Idem2

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem idem_conj_cols {e : R} (he : e * e = e) (N Q : Matrix ι ι A) (D Ac : Matrix ι κ A) (T : Matrix κ κ A)
    (hND : N * D = Ac) (hNA : N * Ac = D) (hQ : (1 - e) • Q = (1 - e) • (1 : Matrix ι ι A))
    (hQA : Q * Ac = Ac * T) :
    (((1 - e) • (1 : Matrix ι ι A) + e • N) * Q * ((1 - e) • (1 : Matrix ι ι A) + e • N)) * D =
      D * ((1 - e) • (1 : Matrix κ κ A) + e • T) := by
  have hQD : (1 - e) • (Q * D) = (1 - e) • D := by
    rw [← Matrix.smul_mul, hQ, Matrix.smul_mul, Matrix.one_mul]
  rw [idem_sandwich he, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hQD,
    Matrix.mul_assoc, Matrix.mul_assoc, hND, hQA, ← Matrix.mul_assoc, hNA, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one]

theorem idem_unit {e : R} (he : e * e = e) (T Ti : Matrix κ κ A) (h : T * Ti = 1) :
    ((1 - e) • (1 : Matrix κ κ A) + e • T) * ((1 - e) • (1 : Matrix κ κ A) + e • Ti) = 1 := by
  have h11 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h10 : (1 - e) * e = 0 := by linear_combination -he
  have h01 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    h11, h10, h01, he, zero_smul, add_zero, zero_add, h]
  rw [← add_smul, sub_add_cancel, one_smul]

end Idem2

def flipAt (v : Pl (F := F)) (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) +
    (GlobalTheory.LatVac.liftV v 1 : AF F) • flipM d

theorem flipAt_mul_self (v : Pl (F := F)) (d : ℕ) : flipAt (E := E) v d * flipAt v d = 1 := by
  have h := idem_sandwich (idem_mul_self v) (flipM (F := F) (E := E) d) 1
  rw [Matrix.mul_one, Matrix.mul_one, flipM_mul_self, ← add_smul, sub_add_cancel, one_smul] at h
  exact h

theorem flipAt_transpose (v : Pl (F := F)) (d : ℕ) : (flipAt (E := E) v d)ᵀ = flipAt v d := by
  simp only [flipAt, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, flipM_transpose]

theorem flipAt_map (σ : E →ₐ[F] E) (v : Pl (F := F)) (d : ℕ) : (flipAt (E := E) v d).map (cA σ) = flipAt v d := by
  ext i j
  have h1 : (cA σ) ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) i j) = (1 : Matrix _ _ (AE F E)) i j :=
    congrFun (congrFun (Matrix.map_one (cA σ) (map_zero _) (map_one _)) i) j
  have h2 : (cA σ) (flipM (F := F) (E := E) d i j) = flipM d i j := congrFun (congrFun (flipM_map σ d) i) j
  simp only [flipAt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, h1, h2]

theorem flipAt_unitary (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) :
    (flipAt (E := E) v d)ᵀ * dbl (incM F W.J) * (flipAt v d).map (cA σ) = dbl (incM F W.J) := by
  rw [flipAt_transpose, flipAt_map, flipAt, idem_sandwich (idem_mul_self v), flipM_dbl, ← add_smul, sub_add_cancel,
    one_smul]

def flipPt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : UD σ W :=
  ⟨⟨flipAt v d, flipAt v d, flipAt_mul_self v d, flipAt_mul_self v d⟩, flipAt_unitary σ W v⟩

theorem matD_flipPt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : matD (flipPt σ W v) = flipAt v d := rfl

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  exact congrArg Units.val (inv_mul_cancel (g : GL (Fin d ⊕ Fin d) (AE F E)))

theorem mul_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · have e1 : matD (g * h) - 1 = (matD g - 1) * matD h + (matD h - 1) := by
      rw [matD_mul, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e1, smul_add, ← Matrix.smul_mul, hg.1 x hx, hh.1 x hx, Matrix.zero_mul, add_zero]
  · have e2 : matD (g * h)⁻¹ = matD h⁻¹ * matD g⁻¹ := by rw [_root_.mul_inv_rev, matD_mul]
    rw [matD_mul, ← Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem inv_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · have e1 : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one, neg_sub]
    rw [e1, smul_neg, ← Matrix.mul_smul, hg.1 x hx, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]
    exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem idem_smul_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (GlobalTheory.LatVac.liftV v 1 : AF F) • y ∈ GlobalTheory.InertSph.latAt W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1 * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
      exact hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem flipAt_mulVec_inl (v : Pl (F := F)) {d : ℕ} (z : Fin d ⊕ Fin d → AE F E) (i : Fin d) :
    (flipAt v d *ᵥ z) (Sum.inl i) = z (Sum.inl i) := by
  simp [flipAt, flipM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, smul_mul_assoc, neg_mul, Finset.sum_neg_distrib]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem flipAt_mulVec_inr (v : Pl (F := F)) {d : ℕ} (z : Fin d ⊕ Fin d → AE F E) (i : Fin d) :
    (flipAt v d *ᵥ z) (Sum.inr i) =
      z (Sum.inr i) - (GlobalTheory.LatVac.liftV v 1 : AF F) • z (Sum.inr i) - (GlobalTheory.LatVac.liftV v 1 : AF F) • z (Sum.inr i) := by
  simp [flipAt, flipM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, smul_mul_assoc, neg_mul, Finset.sum_neg_distrib]
  rw [sub_smul, one_smul]; abel

theorem flipAt_mulVec_mem_latD (v : Pl (F := F)) {d : ℕ} (W : Spc F E d) {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    flipAt v d *ᵥ z ∈ latD W v := by
  have hl : (flipAt v d *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl := funext (flipAt_mulVec_inl v z)
  have hr : (flipAt v d *ᵥ z) ∘ Sum.inr = z ∘ Sum.inr - (GlobalTheory.LatVac.liftV v 1 : AF F) • (z ∘ Sum.inr) -
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (z ∘ Sum.inr) := funext fun i => by
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, flipAt_mulVec_inr]
  have h2 := idem_smul_mem_latAt W v hz.2
  refine ⟨?_, ?_⟩
  · rw [hl]; exact hz.1
  · rw [hr]; exact sub_mem (sub_mem hz.2 h2) h2

theorem flipPt_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : flipPt σ W v ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ⟨flipAt_mulVec_mem_latD v W hz, flipAt_mulVec_mem_latD v W hz⟩⟩
  have e1 : matD (flipPt σ W v) - 1 = (GlobalTheory.LatVac.liftV v 1 : AF F) • (flipM d - 1) := by
    rw [matD_flipPt, flipAt, smul_sub, sub_smul, one_smul]; abel
  rw [e1, smul_smul, mul_idem_eq_zero v hx, zero_smul]

theorem flipPt_conj_anti_diag : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl (F := F)), ∃ w₀ ∈ GlobalTheory.DblVac.KD σ W v, ∀ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W →
      w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ W v ∧ w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ W := by
  intro F E _ _ _ _ _ σ d W v
  have hw := flipPt_mem_KD σ W v
  refine ⟨flipPt σ W v, hw, fun q hq hqa => ⟨mul_mem_KD (mul_mem_KD hw hq) (inv_mem_KD hw), ?_⟩⟩
  obtain ⟨T, hT⟩ := hqa
  have he := idem_mul_self (F := F) v
  have hQ : (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • matD q =
      (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
    have h0 := hq.1 (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rwa [smul_sub, sub_eq_zero] at h0
  refine ⟨⟨(1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (T : Matrix (Fin d) (Fin d) (AE F E)),
    (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • ((T⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)),
    idem_unit he _ _ (Units.mul_inv T), idem_unit he _ _ (Units.inv_mul T)⟩, ?_⟩
  show (flipAt v d * matD q * flipAt v d) * diagCols (Fin d) = diagCols (Fin d) *
    ((1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (T : Matrix (Fin d) (Fin d) (AE F E)))
  exact idem_conj_cols he (flipM d) (matD q) _ _ _ (flipM_diagCols d) (flipM_antiCols d) hQ hT

end GlobalTheory.DblVacFlip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.CompactCharDual

theorem eq_one_of_pow_close {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitNormRealPartBound.main
  | exact _root_.GlobalTheory.UnitNormRealPartBound.main
  | (apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitNormRealPartBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitNormRealPartBound.main ..)

theorem exists_ball_ker {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K] (ψ : AddChar K ℂ)
    (hc : Continuous ψ) : ∃ δ > 0, ∀ x : K, ‖x‖ < δ → ψ x = 1 := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun x hx => eq_one_of_pow_close fun n => ?_⟩
  have := h (x := n • x) (by
    rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
  rwa [AddChar.map_zero_eq_one, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this

theorem mem_of_separates {Q : Type} [AddCommGroup Q] [Finite Q] (H : AddSubgroup (AddChar Q ℂ))
    (h : ∀ x : Q, x ≠ 0 → ∃ χ ∈ H, χ x ≠ 1) (χ : AddChar Q ℂ) : χ ∈ H := by
  by_contra hχ
  have h0 : (QuotientAddGroup.mk χ : AddChar Q ℂ ⧸ H) ≠ 0 := fun e => hχ ((QuotientAddGroup.eq_zero_iff _).1 e)
  obtain ⟨Λ, hΛ⟩ := AddChar.exists_apply_ne_zero.2 h0
  obtain ⟨x, hx⟩ := (AddChar.doubleDualEquiv (α := Q)).surjective (Λ.compAddMonoidHom (QuotientAddGroup.mk' H))
  have hev : ∀ φ : AddChar Q ℂ, φ x = Λ (QuotientAddGroup.mk φ) := fun φ => DFunLike.congr_fun hx φ
  by_cases hx0 : x = 0
  · exact hΛ (by rw [← hev, hx0, AddChar.map_zero_eq_one])
  · obtain ⟨φ, hφ, hφx⟩ := h x hx0
    exact hφx (by rw [hev, (QuotientAddGroup.eq_zero_iff _).2 hφ, AddChar.map_zero_eq_one])

theorem exists_lift {G : Type} [AddCommGroup G] (N : AddSubgroup G) (φ : AddChar G ℂ)
    (hφ : ∀ x ∈ N, φ x = 1) : ∃ Λ : AddChar (G ⧸ N) ℂ, ∀ x : G, Λ x = φ x := by
  refine ⟨⟨Quotient.lift φ fun a b hab => ?_, φ.map_zero_eq_one, ?_⟩, fun x => rfl⟩
  · have := hφ _ (QuotientAddGroup.leftRel_apply.1 hab)
    rw [← add_neg_cancel_left a b, AddChar.map_add_eq_mul, this, mul_one]
  · rintro ⟨a⟩ ⟨b⟩
    exact φ.map_add_eq_mul a b

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ]
    (ψ₀ : AddChar K ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (L : AddSubgroup (κ → K)) (hL : IsCompact (L : Set (κ → K)))
    (L' : AddSubgroup (κ → K)) (hL' : IsOpen (L' : Set (κ → K)))
    (χ : (κ → K) → ℂ) (hmul : ∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') (htriv : ∀ y ∈ L, y ∈ L' → χ y = 1) :
    ∃ x₀ : κ → K, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  classical
  obtain ⟨δ, hδ, hψδ⟩ := exists_ball_ker ψ₀ hc
  obtain ⟨r, hr, hrL'⟩ := Metric.isOpen_iff.1 hL' 0 L'.zero_mem
  obtain ⟨t₁, ht₁⟩ : ∃ t, ψ₀ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (DFunLike.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  have ht0 : 0 < ‖t₁‖ := norm_pos_iff.2 fun h => ht₁ (by rw [h, AddChar.map_zero_eq_one])
  set ρ := ‖t₁‖ / r with hρ
  have hρ0 : 0 < ρ := div_pos ht0 hr
  set η := min r (δ / ρ) with hη
  have hη0 : 0 < η := lt_min hr (div_pos hδ hρ0)

  have small : ∀ a y : κ → K, ‖a‖ ≤ ρ → ‖y‖ < η → ψ₀ (a ⬝ᵥ y) = 1 := by
    intro a y ha hy
    have key : ∀ s : Finset κ, (∀ i ∈ s, ψ₀ (a i * y i) = 1) → ψ₀ (∑ i ∈ s, a i * y i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | insert i s hi ih =>
        intro hf
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, hf i (Finset.mem_insert_self _ _),
          ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), one_mul]
    show ψ₀ (∑ i, a i * y i) = 1
    refine key Finset.univ fun i _ => hψδ _ ?_
    rw [norm_mul]
    have h1 : ‖a i‖ ≤ ρ := (norm_le_pi_norm a i).trans ha
    have h2 : ‖y i‖ < δ / ρ := ((norm_le_pi_norm y i).trans_lt hy).trans_le (min_le_right _ _)
    calc ‖a i‖ * ‖y i‖ ≤ ρ * ‖y i‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < ρ * (δ / ρ) := mul_lt_mul_of_pos_left h2 hρ0
      _ = δ := mul_div_cancel₀ _ hρ0.ne'
  let M : AddSubgroup (κ → K) :=
    { carrier := {y | ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1}
      add_mem' := fun {y y'} hy hy' a ha => by
        rw [dotProduct_add, AddChar.map_add_eq_mul, hy a ha, hy' a ha, mul_one]
      zero_mem' := fun a _ => by rw [dotProduct_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {y} hy a ha => by
        rw [dotProduct_neg, ← neg_dotProduct]
        exact hy (-a) (by rwa [norm_neg]) }
  have hMmem : ∀ y, y ∈ M ↔ ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1 := fun y => Iff.rfl

  have hML' : ∀ y ∈ M, y ∈ L' := by
    intro y hy
    refine hrL' (mem_ball_zero_iff.2 ?_)
    rw [pi_norm_lt_iff hr]
    intro k
    by_contra hk
    push_neg at hk
    have hyk : 0 < ‖y k‖ := hr.trans_le hk
    refine ht₁ ?_
    have hnorm : ‖(Pi.single k (t₁ / y k) : κ → K)‖ ≤ ρ := by
      refine (pi_norm_le_iff_of_nonneg hρ0.le).2 fun i => ?_
      by_cases hi : i = k
      · subst hi
        rw [Pi.single_eq_same, norm_div]
        exact div_le_div_of_nonneg_left ht0.le hr hk
      · rw [Pi.single_eq_of_ne hi, norm_zero]; exact hρ0.le
    have := (hMmem y).1 hy _ hnorm
    rwa [single_dotProduct, div_mul_cancel₀ _ (norm_pos_iff.1 hyk)] at this

  let U : AddSubgroup (κ → K) :=
    { carrier := Metric.ball 0 η
      add_mem' := fun {a b} ha hb => mem_ball_zero_iff.2
        ((IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt (mem_ball_zero_iff.1 ha) (mem_ball_zero_iff.1 hb)))
      zero_mem' := Metric.mem_ball_self hη0
      neg_mem' := fun {a} ha => by simpa using ha }
  have hUM : U ≤ M := fun y hy a ha => small a y ha (mem_ball_zero_iff.1 hy)
  let N : AddSubgroup L := M.addSubgroupOf L
  have hNo : IsOpen (N : Set L) := by
    refine AddSubgroup.isOpen_mono (H₁ := U.addSubgroupOf L)
      (fun y hy => AddSubgroup.mem_addSubgroupOf.2 (hUM (AddSubgroup.mem_addSubgroupOf.1 hy))) ?_
    exact (Metric.isOpen_ball (x := (0 : κ → K)) (ε := η)).preimage continuous_subtype_val
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  haveI : Finite (L ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNo

  let e : (κ → K) → AddChar L ℂ := fun a =>
    { toFun := fun y => ψ₀ (a ⬝ᵥ (y : κ → K))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun y y' => by
        rw [AddSubgroup.coe_add, dotProduct_add, AddChar.map_add_eq_mul] }
  have he : ∀ a (y : L), e a y = ψ₀ (a ⬝ᵥ (y : κ → K)) := fun _ _ => rfl
  have hχ0 : χ 0 = 1 := htriv 0 L.zero_mem L'.zero_mem
  let χL : AddChar L ℂ :=
    { toFun := fun y => χ y
      map_zero_eq_one' := hχ0
      map_add_eq_mul' := fun y y' => hmul _ y.2 _ y'.2 }
  obtain ⟨X, hX⟩ := exists_lift N χL fun y hy => htriv _ y.2 (hML' _ hy)
  let H : AddSubgroup (AddChar (L ⧸ N) ℂ) :=
    { carrier := {Λ | ∃ a : κ → K, ‖a‖ ≤ ρ ∧ ∀ y : L, Λ y = ψ₀ (a ⬝ᵥ (y : κ → K))}
      add_mem' := by
        rintro Λ Λ' ⟨a, ha, h⟩ ⟨b, hb, h'⟩
        refine ⟨a + b, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb), fun y => ?_⟩
        rw [AddChar.add_apply, h, h', add_dotProduct, AddChar.map_add_eq_mul]
      zero_mem' := ⟨0, by rw [norm_zero]; exact hρ0.le, fun y => by simp⟩
      neg_mem' := by
        rintro Λ ⟨a, ha, h⟩
        refine ⟨-a, by rwa [norm_neg], fun y => ?_⟩
        rw [AddChar.neg_apply, ← QuotientAddGroup.mk_neg, h, AddSubgroup.coe_neg, dotProduct_neg, neg_dotProduct] }
  have hsep : ∀ q : L ⧸ N, q ≠ 0 → ∃ Λ ∈ H, Λ q ≠ 1 := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hyN : (y : κ → K) ∉ M := fun h => hq ((QuotientAddGroup.eq_zero_iff _).2 h)
    rw [hMmem] at hyN
    push_neg at hyN
    obtain ⟨a, ha, hay⟩ := hyN
    obtain ⟨Λ, hΛ⟩ := exists_lift N (e a) fun z hz => hz a ha
    exact ⟨Λ, ⟨a, ha, fun z => hΛ z⟩, by rw [hΛ]; exact hay⟩
  obtain ⟨a, -, ha⟩ := mem_of_separates H hsep X
  exact ⟨a, fun y hy => (hX ⟨y, hy⟩).symm.trans (ha ⟨y, hy⟩)⟩

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq_local : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ L : AddSubgroup (κ → Fv F v), IsCompact (L : Set (κ → Fv F v)) →
    ∀ L' : AddSubgroup (κ → Fv F v), IsOpen (L' : Set (κ → Fv F v)) →
    ∀ χ : (κ → Fv F v) → ℂ, (∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') → (∀ y ∈ L, y ∈ L' → χ y = 1) →
    ∃ x₀ : κ → Fv F v, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  intro F _ _ v κ _ ψ₀ hc hne L hL L' hL' χ hmul htriv
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  exact exists_dotProduct_eq ψ₀ hc hne L hL L' hL' χ hmul htriv

end GlobalTheory.CompactCharDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreUniformisationAppellHumbertUnit
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FibreUnifComb

theorem exists_unif_isDiff_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ₀ : c.F →+* ℂ) (U : Unf Xo c σ₀ r), 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (w : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W) (ρ : E →+* ℂ) (z : FrPt Xo c (CAt σ₀)), z.x = (U.un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt σ₀), (∀ i, IsCombAt (U.un k w).x ((U.un k w).u ρ) (C i) (z.u ρ i)) → ∃ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x) (u' : HolUnif T.pol.A T.pol.L W.g) (χ' : u'.Λ → ℂ), u'.IsAH Wu.Hm χ' ∧ ∀ i, ∃ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i ∧ u'.IsDiff (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) w' := by
  intro E _ _ _ H Dw l Xo c r σ₀ U hpq k x W Wu ρ z hz C hC
  rcases z with ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩
  dsimp only at hz ztan hC ⊢
  subst hz
  obtain ⟨Φ₀⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : GlobalTheory.LamT.FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, -, hA, -, -, -, hD⟩ := GlobalTheory.OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos
    Wu.c2 Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  refine ⟨Φ.T, Φ.m, u, χ, hA, fun i => ?_⟩
  have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per (Dw.mult ρ)
    ((U.un k x).u ρ) (fun l => Pi.single (W.e.symm ⟨ρ, l⟩) 1) (W.der ρ) (fun l => toC (C i l)) (zu ρ i)).1
    (by rw [← W.pt]; exact hC i)
  exact hD _ _ (ztan ρ i) hd

end GlobalTheory.FibreUnifComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlaceStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockMap_signatures_depend_on_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  exact GlobalTheory.HoweD.exists_isFockMapD F E σ α β κ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProductStatement
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) := by
  first | exact @GlobalTheory.GoodCharProd.isProdCuspChar_good | exact GlobalTheory.GoodCharProd.isProdCuspChar_good | (intros; apply GlobalTheory.GoodCharProd.isProdCuspChar_good <;> assumption)
end

