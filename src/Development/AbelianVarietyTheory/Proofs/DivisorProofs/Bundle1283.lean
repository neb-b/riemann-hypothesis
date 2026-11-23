module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLe
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDiscDeg

variable {F : Type} [Field F] {σ : Type}

def CoeffDeg (e : ℕ) (P : Polynomial (MvPolynomial σ F)) : Prop :=
  ∀ k, (P.coeff k).totalDegree ≤ e

theorem CoeffDeg.mono {e e' : ℕ} {P : Polynomial (MvPolynomial σ F)} (h : CoeffDeg e P) (he : e ≤ e') :
    CoeffDeg e' P := fun k => (h k).trans he

theorem coeffDeg_C {e : ℕ} {a : MvPolynomial σ F} (ha : a.totalDegree ≤ e) :
    CoeffDeg e (Polynomial.C a) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · simp

theorem coeffDeg_one : CoeffDeg 0 (1 : Polynomial (MvPolynomial σ F)) := by
  rw [← Polynomial.C_1]
  exact coeffDeg_C (by simp)

theorem coeffDeg_X : CoeffDeg 0 (Polynomial.X : Polynomial (MvPolynomial σ F)) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

theorem CoeffDeg.add {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (hQ : CoeffDeg e Q) :
    CoeffDeg e (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hP k) (hQ k))

theorem CoeffDeg.mul {e e' : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e' Q) : CoeffDeg (e + e') (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact totalDegree_finsetSum_le fun x _ => (totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))

theorem coeffDeg_sum {ι : Type} (s : Finset ι) {e : ℕ} (P : ι → Polynomial (MvPolynomial σ F))
    (h : ∀ i ∈ s, CoeffDeg e (P i)) : CoeffDeg e (∑ i ∈ s, P i) := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact totalDegree_finsetSum_le fun i hi => h i hi k

theorem coeffDeg_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (P : ι → Polynomial (MvPolynomial σ F)) (h : ∀ i ∈ s, CoeffDeg (e i) (P i)) :
    CoeffDeg (∑ i ∈ s, e i) (∏ i ∈ s, P i) := by
  induction s using Finset.induction_on with
  | empty => simpa using coeffDeg_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CoeffDeg.pow {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (n : ℕ) :
    CoeffDeg (n * e) (P ^ n) := by
  induction n with
  | zero => simpa using coeffDeg_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

theorem CoeffDeg.derivative {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) :
    CoeffDeg e (Polynomial.derivative P) := by
  intro k
  rw [Polynomial.coeff_derivative]
  have h1 : ((k : MvPolynomial σ F) + 1) = C ((k : F) + 1) := by simp
  rw [h1]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  exact hP (k + 1)

theorem totalDegree_resultant_le {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e Q) (m n : ℕ) : (Polynomial.resultant P Q m n).totalDegree ≤ (m + n) * e := by
  have hH : ∀ i j, (Polynomial.sylvester P Q m n i j).totalDegree ≤ e := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simp
    | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simp
  rw [Polynomial.resultant, Matrix.det_apply]
  refine totalDegree_finsetSum_le fun s _ => ?_
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  simpa using Finset.sum_le_card_nsmul Finset.univ _ e fun i _ => hH (s i) i

theorem coeffDeg_line {D N δ : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    CoeffDeg (D * δ) (line (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f) := by
  rw [line, aeval_def, eval₂_eq']
  refine coeffDeg_sum _ _ fun d hd => ?_
  have hc : CoeffDeg 0 (algebraMap F (Polynomial (MvPolynomial (Fin D × Fin N) F)) (AddMonoidAlgebra.coeff f d)) := by
    rw [Polynomial.algebraMap_apply]
    exact coeffDeg_C (by rw [MvPolynomial.algebraMap_eq, totalDegree_C])
  have hw : ∀ p : Fin (D + 1) × Fin N, CoeffDeg (if p.1 = Fin.last D then 0 else 1)
      (join (fun i j => Polynomial.C (X (i, j) : MvPolynomial (Fin D × Fin N) F))
        (fun j => Polynomial.C (C (ξ₀ j)) + Polynomial.C (C (ξ₁ j)) * Polynomial.X) p) := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [join, Fin.lastCases_last, if_true]
      exact (coeffDeg_C (totalDegree_C _).le).add ((coeffDeg_C (e := 0) (totalDegree_C _).le).mul coeffDeg_X)
    · simp only [join, Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last i)]
      exact coeffDeg_C (totalDegree_X _).le
  refine (hc.mul (coeffDeg_prod Finset.univ _ _ fun p _ => (hw p).pow (d p))).mono (le_of_eq ?_)
  rw [zero_add, Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  have h := hf d hd
  simp [Fin.castSucc_ne_last, h]

theorem totalDegree_disc_le (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    (disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  have h := coeffDeg_line f hf ξ₀ ξ₁
  refine (totalDegree_resultant_le h h.derivative δ (δ - 1)).trans ?_
  calc (δ + (δ - 1)) * (D * δ) ≤ (2 * δ) * (D * δ) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * D * δ ^ 2 := by ring

end GlobalTheory.PencilDiscDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPiMulWeightLengthLeMaxWeightDegreeSq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

namespace GlobalTheory.TopDegLower

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem lR_last_ge (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    Tp.TO ≤ (lR Tp hK j).aP τ i + 1 := by
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  have hk := GlobalTheory.DepthBoundProbe.kappa_last Tp hK hj τ i hi
  show Tp.TO ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i + 1
  rw [ofGaps_last _ _ hn]
  unfold lGapP
  rw [if_neg hn]
  have hp : (0 : ℤ) < (WeightAlgebra.Tp D j Tp.TO : ℤ) := by unfold WeightAlgebra.Tp; push_cast; omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have h1 : ((Tp.Dp : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by exact_mod_cast Tp.TO_nW
  have h40 : 40 * ((Tp.Dp : ℤ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have : (Tp.TO : ℤ) - 1 ≤ (((kaR Tp hK j).aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn - 2 * D.R.r) /
      (WeightAlgebra.Tp D j Tp.TO : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hp]
    unfold WeightAlgebra.Tp
    rw [GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]
    push_cast
    have hD : (0 : ℤ) ≤ Tp.Dp := Int.natCast_nonneg _
    have h2 : ((Tp.TO : ℤ) - 1) * ((Tp.Dp : ℤ) + 2) ≤ ((Tp.TO : ℤ) - 1) * Tp.TO :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  omega

theorem DF_ge (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau) :
    Tp.TO ≤ WeightAlgebra.DF (lR Tp hK j) + 1 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 := lR_last_ge Tp hK hj τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine h1.trans (Nat.add_le_add_right ?_ 1)
  unfold WeightAlgebra.DF WeightAlgebra.degP
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (lR Tp hK j).aP τ i) + ∑ i, (lR Tp hK j).aM τ i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  exact le_trans (Finset.single_le_sum (f := fun i => (lR Tp hK j).aP τ i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ _)) (Nat.le_add_right _ _)

theorem two_pi_nW_le_topDeg_sq : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D),
    2 * Real.pi * (Tp.nWn : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) ^ 2 := by
  intro D L Pm Tp hK
  have hj : InR D 1 := ⟨le_rfl, by have := D.R.two_le_m; omega⟩
  obtain ⟨τ, -⟩ := GlobalTheory.FinalJoin.RecordRun.exists_thick L
  have h1 := DF_ge Tp hK hj τ
  have h2 : WeightAlgebra.DF (lR Tp hK 1) ≤ GlobalTheory.IndexAssembly.topDeg Tp hK := GlobalTheory.IndexAssembly.le_topDeg Tp hK hj
  have h3 : 2 * Tp.nWn ≤ Tp.TO := by
    have := Tp.TO_nW
    nlinarith [Nat.zero_le (Tp.Dp * Tp.nWn)]
  have h4 : 40 ≤ Tp.TO := by have := Tp.TO_40; omega
  have a : (Tp.TO : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) + 1 := by
    exact_mod_cast h1.trans (Nat.add_le_add_right h2 1)
  have b : 2 * (Tp.nWn : ℝ) ≤ Tp.TO := by exact_mod_cast h3
  have c : (40 : ℝ) ≤ Tp.TO := by exact_mod_cast h4
  have hpi := Real.pi_le_four
  have hn : (0 : ℝ) ≤ Tp.nWn := Nat.cast_nonneg _
  have d : 2 * Real.pi * (Tp.nWn : ℝ) ≤ 4 * Tp.TO := by nlinarith
  nlinarith

end GlobalTheory.TopDegLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeve
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapCover

theorem unip_eq_rat_mul_inf_mul_fin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ)
    (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E,
    ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧
    unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  intro E _ _ _ a s L hL
  have h0 : (unip (0 : BlockIx a s → Af E)) = 1 := by
    have h := unip_add (0 : BlockIx a s → Af E) 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hpre : (fun y : BlockIx a s → Af E => unip y) ⁻¹' L ∈ nhds (0 : BlockIx a s → Af E) := by
    apply JointCont.continuous_unip.continuousAt.preimage_mem_nhds
    rw [h0]; exact hL
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  have hU : (⋂ p, t p) ∈ nhds (0 : Af E) := Filter.iInter_mem.2 fun p => by simpa using ht p
  obtain ⟨R, hR, hx⟩ := _root_.GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small E (⋂ p, t p) hU
  refine ⟨R, hR, fun x => ?_⟩
  choose ξ hξ1 hξ2 using fun p => hx (x p)
  refine ⟨ξ, fun p => pInf E (x p - algebraMap E (Ad E) (ξ p)),
    unip (fun p => pFin E (x p - algebraMap E (Ad E) (ξ p))), ?_, ?_, ?_⟩
  · apply hsub
    intro p _
    exact Set.mem_iInter.1 (hξ2 p) p
  · exact (pi_norm_le_iff_of_nonneg hR).2 hξ1
  · have hsplit : x = (fun p => algebraMap E (Ad E) (ξ p)) + (fun p => x p - algebraMap E (Ad E) (ξ p)) := by
      funext p; simp
    conv_lhs => rw [hsplit, unip_add, unip_algebraMap,
      ← infGL_mul_finGL (unip (fun p => x p - algebraMap E (Ad E) (ξ p))), JointCont.map_unip, JointCont.map_unip]
    rw [mul_assoc]

end GlobalTheory.RapCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransport
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.fromBlocks_unitary_transfer : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  intro A O _ _ ι γ c n P K JL hinj hγ hP M G hM hG
  have hmul : ∀ {m : Type} [Fintype m] (X Y : Matrix m m O), (X * Y).map ι = X.map ι * Y.map ι := by
    intro m _ X Y; ext i j; simp [Matrix.mul_apply, map_sum]
  have hneg : (-JL).map ι = -(JL.map ι) := by ext i j; simp
  have hD : (Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ
      = (Matrix.fromBlocks JL 0 0 (-JL)).map ι := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hneg, ← hP]
    simp [Matrix.mul_neg, Matrix.neg_mul]
  have hc : (G.map c).map ι = (G.map ι).map γ := by
    ext i j; simp [hγ]
  apply Matrix.map_injective hinj
  show (Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c).map ι = (Matrix.fromBlocks JL 0 0 (-JL)).map ι
  rw [hmul, hmul, Matrix.transpose_map, hc]
  conv_lhs => rw [← hD]
  have hG' : (Matrix.fromBlocks P 0 0 P * G.map ι).map γ = (Matrix.fromBlocks P 0 0 P).map γ * (G.map ι).map γ := by
    rw [Matrix.map_mul]
  calc (G.map ι)ᵀ * ((Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ) * (G.map ι).map γ
      = (Matrix.fromBlocks P 0 0 P * G.map ι)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P * G.map ι).map γ := by
        rw [hG', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (M * Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (M * Matrix.fromBlocks P 0 0 P).map γ := by rw [hG]
    _ = (Matrix.fromBlocks P 0 0 P)ᵀ * (Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ) * (Matrix.fromBlocks P 0 0 P).map γ := by
        rw [Matrix.map_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hD]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

variable {D : D7}

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℂ) = -((sT τ).trace / 2 + (b τ : ℂ))) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ x₃ τ) • f := by
  intro D ψ θ S T χS χT om hW hθ _ _ sT hS hT a b ha hb x₁ x₂ x₃ h1 h2 h3 f hf hv g hg h hh hc
  obtain ⟨η, e1, e2, e3, e4⟩ := _root_.GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => hdet (hS τ)) g hg
  obtain ⟨y, hy, hyv⟩ := exists_root hθ T (fun τ => hdet (hT τ)) h hh
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (sT τ) (hT τ).1
  rw [_root_.GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) sT hS hT g hg h hh
    (fun τ => by rw [one_mul, mul_one]) hc x y hx hy f hf hv]
  congr 1
  have hb' : ∀ τ, ((-x₃ τ - p τ : ℤ) : ℚ) = b τ - T.rank / 2 := fun τ => by
    have := h3 τ
    rw [hp] at this
    apply Rat.cast_injective (α := ℂ)
    push_cast
    linear_combination -this
  rw [Circle.coe_mul, Circle.coe_inv,
    hxv _ (fun τ => -x₃ τ - p τ) (fun τ => by rw [hb']; exact hasInfExp_twist (hb τ) (e2 τ) _),
    hyv _ x₂ (fun τ => by rw [h2]; exact hasInfExp_twist (ha τ) (e2 τ) _),
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨d1, d2⟩ := hd τ (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h)) (hc τ)
  have inv : ∀ (V : HSp D) (k : GA D V),
      (compAt θ τ (Formalism.L2.Theta.mt V k)).det * (compAt θ τ (Formalism.L2.Theta.mt V k⁻¹)).det = 1 := fun V k => by
    rw [det_compAt, det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one (inv S g)
  have h0 := left_ne_zero_of_mul_eq_one (inv T h)
  rw [d2] at h0
  have h0' := left_ne_zero_of_mul h0
  have e : x₁ τ = x₂ τ + S.rank := by
    have : (x₁ τ : ℚ) = x₂ τ + S.rank := by rw [h1, h2]; ring
    exact_mod_cast this
  have alg : ∀ (A B G : ℂ) (u v : ℤ) (n k : ℕ), A ≠ 0 → G ≠ 0 →
      (G ^ (-v - k))⁻¹ * (A * B) ^ u * (A ^ n * G⁻¹ ^ k) = A ^ (u + n) * B ^ u * G ^ v := by
    intro A B G u v n k hA hG
    rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hG, _root_.zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    have := zpow_ne_zero v hG
    have := pow_ne_zero k hG
    field_simp
  rw [d1, d2, eq_inv_of_mul_eq_one_right (inv S g), e]
  exact alg _ _ _ _ _ _ _ h0' g0

end GlobalTheory.VacuumCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumExponentSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitVacSum

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem idem_trace_det (P : Matrix ι ι ℂ) (hP : P * P = P) :
    P.trace = P.rank ∧ ∀ u : ℂ, (u • P + (1 - P)).det = u ^ P.rank := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) :=
    LinearMap.IsIdempotentElem.isProj_range _ hi
  have hr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = P.rank := rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← Matrix.trace_toLin'_eq, hp.trace, hr]
  · rw [← LinearMap.det_toLin']
    have e := hp.eq_conj_prodMap
    set c := (Submodule.prodEquivOfIsCompl _ _ hp.isCompl)
    have e2 : Matrix.toLin' (u • P + (1 - P)) = c.conj (LinearMap.prodMap (u • LinearMap.id) LinearMap.id) := by
      have : LinearMap.prodMap (u • LinearMap.id) LinearMap.id =
          u • LinearMap.prodMap (LinearMap.id : LinearMap.range (Matrix.toLin' P) →ₗ[ℂ] _) (0 : LinearMap.ker (Matrix.toLin' P) →ₗ[ℂ] _)
            + (1 - LinearMap.prodMap LinearMap.id 0) := by
        refine LinearMap.ext fun x => ?_
        ext <;> simp
      rw [this, map_add (f := _), map_add (f := _), map_smul, map_smul, map_sub, map_sub, ← e, Matrix.toLin'_one]
      congr 2
      exact (LinearEquiv.conj_id c).symm
    rw [e2, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
      LinearMap.det_id, LinearMap.det_id, hr, mul_one, mul_one]

theorem half_idem {s : Matrix ι ι ℂ} (hs : s * s = 1) :
    ((1 / 2 : ℂ) • (1 + s)) * ((1 / 2 : ℂ) • (1 + s)) = (1 / 2 : ℂ) • (1 + s) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, mul_add, add_mul, hs, mul_one, one_mul]
  module

theorem le_rank_half {m : ℕ} {G s t : Matrix ι ι ℂ} (hpos : (G * s).PosDef) (ht : t = s ∨ t = -s)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) :
    m ≤ ((1 / 2 : ℂ) • (1 + t)).rank := by
  refine le_trans ?_ (Matrix.rank_mul_le_left _ B)
  have hinj : Function.Injective (((1 / 2 : ℂ) • (1 + t)) * B).mulVecLin := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : B *ᵥ a + t *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at ha
      exact (smul_eq_zero.1 ha).resolve_left (by norm_num)
    have h2 : star (B *ᵥ a) ⬝ᵥ G *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
        Matrix.zero_mulVec, dotProduct_zero]
    have h3 : star (B *ᵥ a) ⬝ᵥ (G * s) *ᵥ (B *ᵥ a) = 0 := by
      rw [← Matrix.mulVec_mulVec]
      rcases ht with rfl | rfl
      · rw [eq_neg_of_add_eq_zero_right h1, Matrix.mulVec_neg, dotProduct_neg, h2, neg_zero]
      · rw [Matrix.neg_mulVec, add_neg_eq_zero] at h1
        rw [← h1, h2]
    have h4 : B *ᵥ a = 0 := by
      by_contra h
      exact (hpos.dotProduct_mulVec_pos h).ne' h3
    rw [← Matrix.one_mulVec a, ← hC, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
  unfold Matrix.rank
  rw [LinearMap.finrank_range_of_inj hinj]
  simp

theorem trace_eq_zero {m : ℕ} {G s : Matrix ι ι ℂ} (hs : s * s = 1) (hpos : (G * s).PosDef) (hm : 2 * m = Fintype.card ι)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) : s.trace = 0 := by
  have a1 := le_rank_half hpos (Or.inl rfl) B C hC hB
  have a2 := le_rank_half hpos (Or.inr rfl) B C hC hB
  have b1 := (idem_trace_det _ (half_idem hs)).1
  have b2 := (idem_trace_det _ (half_idem (s := -s) (by rw [neg_mul_neg, hs]))).1
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, ← hm, smul_eq_mul] at b1 b2
  rw [Matrix.trace_neg] at b2
  have c : ((((1 / 2 : ℂ) • (1 + s)).rank + ((1 / 2 : ℂ) • (1 + -s)).rank : ℕ) : ℂ) = (2 * m : ℕ) := by
    rw [Nat.cast_add, ← b1, ← b2]; ring
  have c' := Nat.cast_injective c
  have d : ((1 / 2 : ℂ) • (1 + s)).rank = m := by omega
  rw [d] at b1
  push_cast at b1
  linear_combination 2 * b1

end Lin

variable {D : D7} {θ : InfFam D}

end GlobalTheory.SplitVacSum

end
end

