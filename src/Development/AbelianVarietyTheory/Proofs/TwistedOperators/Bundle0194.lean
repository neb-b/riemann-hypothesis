module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniquene
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MvPolynomial Matrix
open GlobalTheory.ArchRec GlobalTheory.FockDeg GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.ArchRec.Joint

variable {p q r s : ℕ}

theorem mem_pR_of_herm {Z : TH.Mat p q} (hZ : IsPC Z) (h : Zᴴ = Z) : Z ∈ pR p q := by
  refine ⟨?_, hZ⟩
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  show Zᴴ * TH.Jm p q + TH.Jm p q * Z = 0
  rw [h, hJ]
  ext a b
  have := hZ a b
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem exists_pR {Z : TH.Mat p q} (hZ : IsPC Z) :
    ∃ A ∈ pR p q, ∃ B ∈ pR p q, Z = (1 / 2 : ℂ) • A + (-Complex.I / 2) • B := by
  refine ⟨Z + Zᴴ, mem_pR_of_herm ?_ ?_, Complex.I • (Z - Zᴴ), mem_pR_of_herm ?_ ?_, ?_⟩
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp [← smul_neg]
  · rw [smul_smul, show -Complex.I / 2 * Complex.I = 1 / 2 by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

theorem minusPart_eq_zero_of_raise {σ : Type} (a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    {Φ : MvPolynomial σ ℂ} {d : ℕ} (hΦ : Φ.IsHomogeneous d)
    (h : ∀ Z ∈ pR p q, (a Z Φ).IsHomogeneous (d + 2)) (Z : TH.Mat p q) (hZ : IsPC Z) :
    minusPart (a Z) Φ = 0 := by
  obtain ⟨A, hA, B, hB, rfl⟩ := exists_pR hZ
  have hm : a ((1 / 2 : ℂ) • A + (-Complex.I / 2) • B) Φ ∈ homogeneousSubmodule σ ℂ (d + 2) := by
    rw [map_add (f := _), map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h A hA)) (Submodule.smul_mem _ _ (h B hB))
  rw [minusPart_eq_zero_iff]
  intro e
  rw [homogeneousComponent_of_mem (show Φ ∈ homogeneousSubmodule σ ℂ d from hΦ)]
  split_ifs with he
  · rw [homogeneousComponent_of_mem hm, if_neg (by omega)]
  · simp

theorem raise_of_minusPart {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) {Φ : Pol p q r s} {d : ℕ}
    (hΦ : Φ.IsHomogeneous d) (h : minusPart (omAct p q r s M) Φ = 0) :
    (omAct p q r s M Φ).IsHomogeneous (d + 2) := by
  rw [omAct_eq_parts hM, h, add_zero, plusPart_omAct hM]
  exact upOp_mem M d Φ hΦ

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem hc_mem_hwSub {σ : Type} {a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    (ha : ∀ Y, IsKC Y → DegZero (a Y)) {μ : Ix p q → ℚ} {Φ : MvPolynomial σ ℂ}
    (h : Φ ∈ hwSub a μ) (d : ℕ) : homogeneousComponent d Φ ∈ hwSub a μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
  refine ⟨fun c => ?_, fun c e hce => ?_⟩
  · rw [← (ha _ (isKC_Eab (by cases c <;> trivial))).comm, h.1, map_smul]
  · rw [← (ha _ (isKC_Eab ?_)).comm, h.2 c e hce, map_zero]
    rcases c with c | c <;> rcases e with e | e <;> simp_all [sameBlock, posC]

theorem hc_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (d : ℕ) :
    homogeneousComponent d Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 →
      minusPart A (homogeneousComponent d Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [hc_hc]
    split_ifs with he
    · rw [← he]; exact hA e
    · simp
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

theorem smul_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (c : ℂ) :
    c • Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 → minusPart A (c • Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [map_smul, map_smul, map_smul, hA, smul_zero]
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

theorem line (X : ProvA) {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P Φ : Pol p q r s}
    (hJ : P ∈ (X.fock p q r s).J) (h : P ∈ hwSub (fockAct1 p q r s) μ)
    (h' : P ∈ hwSub (fockAct2 p q r s) μ') (h0 : Φ ≠ 0) (gJ : Φ ∈ (X.fock p q r s).J)
    (g : Φ ∈ hwSub (fockAct1 p q r s) μ) (g' : Φ ∈ hwSub (fockAct2 p q r s) μ') :
    ∃ c : ℂ, P = c • Φ := by
  have h2 := (GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 μ μ'
  have hs : JointShape p q r s μ μ' := by
    by_contra hs
    exact h0 ((Submodule.eq_bot_iff _).1 (h2.2 hs) Φ ⟨⟨g, g'⟩, Submodule.subset_span gJ⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    ⟨Φ, ⟨g, g'⟩, Submodule.subset_span gJ⟩
    (fun e => h0 (congrArg Subtype.val e))).1 (h2.1 hs) ⟨P, ⟨h, h'⟩, Submodule.subset_span hJ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem cJoint_iff (X : ProvA) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (Φ : Pol p q r s) :
    CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ := by
  constructor
  · rintro ⟨⟨d, hd, h1, h2⟩, h3⟩
    exact ⟨⟨minusPart_eq_zero_of_raise _ hd h1, minusPart_eq_zero_of_raise _ hd h2⟩, h3⟩
  · rintro ⟨hJ, h1, h2⟩
    obtain ⟨d, hd⟩ : ∃ d, homogeneousComponent d Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1.1
      rw [← sum_homogeneousComponent Φ]
      exact Finset.sum_eq_zero fun d _ => hc d
    obtain ⟨c, hc⟩ := line X hJ h1.2 h2.2 hd (hc_mem_J X hJ d)
      (hc_mem_hwSub (fun _ => degZero_fockAct1) h1.2 d)
      (hc_mem_hwSub (fun _ => degZero_fockAct2) h2.2 d)
    have hh : Φ.IsHomogeneous d := by
      rw [hc]
      exact (homogeneousSubmodule _ ℂ d).smul_mem c (homogeneousComponent_mem d Φ)
    exact ⟨⟨d, hh, fun Z hZ => raise_of_minusPart (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ.2) hh (hJ.1 Z hZ.2),
      fun Z hZ => raise_of_minusPart (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ.2) hh (hJ.2 Z hZ.2)⟩, h1, h2⟩

theorem joint_harmonics : ∀ (X : ProvA) (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ) ∧
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      ∃ c : ℝ, 0 < c ∧ JointHW (X.fock p q r s) μ μ' ((c : ℂ) • Φ)) ∧
    ∀ Φ Φ', CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ' → ∃ c : ℂ, Φ' = c • Φ := by
  intro X p q r s μ μ'
  refine ⟨cJoint_iff X μ μ', fun Φ h => ?_, fun Φ Φ' h h' => ?_⟩
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    have hn : 0 < ‖(X.fock p q r s).ι Φ‖ :=
      norm_pos_iff.2 fun e => h1.1 ((X.fock p q r s).ι_inj (e.trans (map_zero _).symm))
    have hc : ((‖(X.fock p q r s).ι Φ‖⁻¹ : ℝ) : ℂ) • Φ ≠ 0 :=
      smul_ne_zero (Complex.ofReal_ne_zero.2 (inv_pos.2 hn).ne') h1.1
    refine ⟨‖(X.fock p q r s).ι Φ‖⁻¹, inv_pos.2 hn, smul_mem_J X hJ _,
      ⟨hc, Submodule.smul_mem _ _ h1.2⟩, ⟨hc, Submodule.smul_mem _ _ h2.2⟩, ?_⟩
    rw [map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    obtain ⟨hJ', h1', h2'⟩ := (cJoint_iff X μ μ' Φ').1 h'
    exact line X hJ' h1'.2 h2'.2 h1.1 hJ h1.2 h2.2

end GlobalTheory.ArchRec.Joint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointMapReframedHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec.FrMap

variable {D : D7}

theorem gram_reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  funext i j
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k => by
    unfold frP
    simp only [Module.Basis.toMatrix_apply]
    exact (S.frame.sum_repr (b k)).symm
  show S.hT (b i) (b j) = ∑ l, (∑ k, star (frP S b k i) * S.hT (S.frame k) (S.frame l)) * frP S b l j
  rw [hb i, hb j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem inv_eq_of_gram_conjTranspose_change {n : ℕ} {K : Type} [Field K] [StarRing K] (G G' P Q : Matrix (Fin n) (Fin n) K)
    (hG : G' = Pᴴ * G * P) (hQP : Q * P = 1) (hPQ : P * Q = 1) : G'⁻¹ = Q * G⁻¹ * Qᴴ := by
  have h1 : P⁻¹ = Q := Matrix.inv_eq_left_inv hQP
  have h2 : (Pᴴ)⁻¹ = Qᴴ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
  rw [hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, h1, h2, Matrix.mul_assoc]

theorem gram_reS_inv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (reS S b).gram⁻¹ = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ :=
  inv_eq_of_gram_conjTranspose_change (n := S.rank) S.gram (reS S b).gram (frP S b) (frPinv S b) (gram_reS S b)
    (frPinv_mul_frP S b) (frameMatrix_mul_frameMatrixInv S b)

end GlobalTheory.AdSpan.ReVec.FrMap

theorem GlobalTheory.AdSpan.ReVec.FrMap.cA_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

namespace GlobalTheory.AdSpan.ReVec.FrMap

variable {D : D7}

theorem map_eToEAf_eq (n m : ℕ) (M : Matrix (Fin n) (Fin m) D.host.E) :
    M.map (eToEAf D) = (M.map (incA D)).map (toEAf D) := by
  funext i j; rfl

theorem complex_units_mul_eq_one_of_mul_eq_one {R : Type} [Ring R] {n m : ℕ} (B Pf : Matrix (Fin n) (Fin n) R) (M' M : Matrix (Fin n) (Fin m) R)
    (C : Matrix (Fin m) (Fin m) R) (h : Pf * M' = M) : B * Pf * M' * C = B * M * C := by
  rw [Matrix.mul_assoc B, h]

theorem frP_mul_adj_finPart (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Gi : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (hGi : Gi = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ) :
    HMul.hMul ((frP S b).map (eToEAf D))
      ((HMul.hMul (HMul.hMul (Gi.map (incA D))
        (x.map (cA D)).transpose) (T.gram.map (incA D))).map (toEAf D)) =
    (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
        ((HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))).map (cA D)).transpose)
        (T.gram.map (incA D))).map (toEAf D) := by
  rw [map_eToEAf_eq, ← Matrix.map_mul]
  congr 1
  have e1 := Matrix.map_mul (L := x) (M := (frPinv S b).map (incA D)) (f := cA D)
  have e2 : (frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ).map (incA D) =
      (frPinv S b).map (incA D) * (S.gram⁻¹).map (incA D) * ((frPinv S b)ᴴ).map (incA D) := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have e4 : (((frPinv S b).map (incA D)).map (cA D))ᵀ = ((frPinv S b)ᴴ).map (incA D) := by
    funext i j
    exact cA_incA_star _
  have h5 : (frP S b).map (incA D) * (frPinv S b).map (incA D) = 1 := by
    rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e1, hGi, e2, Matrix.transpose_mul, e4]
  simp only [← Matrix.mul_assoc]
  simp only [h5, Matrix.one_mul]

theorem frMapAdj_reS (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T) :
    frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := by
  have h1 : ((frPinvGL S b * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val =
      (βS⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val * (frP S b).map (eToEAf D) := by
    rw [_root_.mul_inv_rev, Units.val_mul, frPinvGL_inv_val]
  unfold frMapAdj reW
  erw [h1]
  exact complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ _ (frP_mul_adj_finPart S T b x _ (gram_reS_inv S b))

end GlobalTheory.AdSpan.ReVec.FrMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt.GlueProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {a b : ℕ}


open Classical in
def rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ)

def ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : LPol b a →ₗ[ℂ] PolF D b a :=
  LinearMap.mulRight ℂ (rest τ P) ∘ₗ (MvPolynomial.rename (fun s => (τ, s))).toLinearMap

theorem ins_apply (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    ins τ P p = MvPolynomial.rename (fun s => (τ, s)) p * rest τ P := rfl

open Classical in
theorem glue_update (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    glue (Function.update P τ p) = ins τ P p := by
  rw [ins_apply, glue, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), rest]
  congr 1
  · rw [Function.update_self]
  · refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]

theorem glue_eq (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : glue P = ins τ P (P τ) := by
  classical
  rw [← glue_update, Function.update_eq_self]

theorem pderiv_other {τ ρ : D.what₂.Tau} (h : ρ ≠ τ) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (MvPolynomial.rename (fun s => (ρ, s)) p : PolF D b a) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p t hp =>
    rw [map_mul, Derivation.leibniz, hp, MvPolynomial.rename_X, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e
      exact h (congrArg Prod.fst e)

theorem pderiv_rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) :
    MvPolynomial.pderiv (τ, s) (rest τ P) = 0 := by
  classical
  unfold rest
  refine Finset.prod_induction _ (fun q : PolF D b a => MvPolynomial.pderiv (τ, s) q = 0) ?_ ?_ ?_
  · intro x y hx hy
    rw [Derivation.leibniz, hx, hy]; simp
  · simp
  · intro ρ hρ
    exact pderiv_other (Finset.ne_of_mem_erase hρ) s _

theorem pderiv_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (ins τ P p) = ins τ P (MvPolynomial.pderiv s p) := by
  classical
  have hinj : Function.Injective (fun s : Fin b × Fin a => (τ, s)) := fun x y e => congrArg Prod.snd e
  have := MvPolynomial.pderiv_rename hinj s p
  rw [ins_apply, ins_apply, Derivation.leibniz, pderiv_rest, ← this]
  simp [mul_comm]

theorem mul_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.X (τ, s) * ins τ P p = ins τ P (MvPolynomial.X s * p) := by
  rw [ins_apply, ins_apply, map_mul, MvPolynomial.rename_X, mul_assoc]

theorem rai_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : raiO τ ε ε' i j (ins τ P p) = ins τ P (rai ε ε' i j p) := by
  unfold raiO rai
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.neg_apply, map_smul, map_neg, Derivation.coeFn_coe]
    rw [← pderiv_ins]

theorem low_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : lowO τ ε ε' i j (ins τ P p) = ins τ P (low ε ε' i j p) := by
  unfold lowO low
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe]
    rw [← pderiv_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]

theorem fockS_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (X : Matrix (Fin a) (Fin a) ℂ) (p : LPol b a) :
    fockS τ ε ε' X (ins τ P p) = ins τ P (locS ε ε' X p) := by
  unfold fockS locS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add (f := _),
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem fockT_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin b) (Fin b) ℂ) (p : LPol b a) :
    fockT τ ε ε' Y (ins τ P p) = ins τ P (locT ε ε' Y p) := by
  unfold fockT locT
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add (f := _),
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem glue_span :
    Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | (apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue ..)

theorem glueLaw : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  intro D a b
  refine ⟨glue_span, fun τ ε ε' P => ⟨fun X => ?_, fun Y => ?_⟩⟩
  · rw [glue_update, glue_eq τ P, fockS_ins]
  · rw [glue_update, glue_eq τ P, fockT_ins]

end GlobalTheory.Chain.RealIt.GlueProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothThetaFunctionReframeFunctionOnHoms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.ThetaCarry

theorem continuous_reW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b : WO (reS S b) T → WO S T) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun x : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D)))

theorem reW_ratW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reW S T b (ratW T (reS S b) γ) = ratW T S (γ * frPinv S b) := by
  unfold reW ratW
  rw [Matrix.map_mul]
  rfl

theorem reW_map_inf {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (infPart D) = 0) : (reW S T b u).map (infPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := infPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (infPart D) = 0 from hu, Matrix.zero_mul]

theorem reW_map_fin {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (finPart D) = 0) : (reW S T b u).map (finPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := finPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (finPart D) = 0 from hu, Matrix.zero_mul]

theorem isThetaFunO_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := by
  intro D ψ S T b hs f hf
  have hsH : ∀ x y : WO (reS S b) T, symplOH (reS S b) T x y = symplOH S T (reW S T b x) (reW S T b y) := by
    intro x y
    unfold symplOH
    rw [hs]
  have hc := continuous_reW S T b
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hc, fun k L h1 h2 w => ?_⟩
  · have e := reW_ratW S T b γ
    rw [reF_apply, reF_apply, reW_add, hsH]
    erw [e]
    exact hf.quasi _ _
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap (reWHom S T b), hU.preimage hc, fun u hu h0 => ?_⟩
    rw [heisO_reF S T b ψ hs u f, h (reW S T b u) hu (reW_map_inf S T b h0)]
  · have := hf.smooth k ((reWHom S T b).comp L) (hc.comp h1) (fun t => reW_map_fin S T b (h2 t)) (reW S T b w)
    simp only [reF_apply, reW_add]
    exact this

end GlobalTheory.AdSpan.ReVec.ThetaCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.Chain.LiftConv

theorem liftInteg_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.Chain.LiftInteg D :=
  fun hP D => liftInteg_of_growth hP D (_root_.GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D)

end GlobalTheory.Chain.LiftConv
end

