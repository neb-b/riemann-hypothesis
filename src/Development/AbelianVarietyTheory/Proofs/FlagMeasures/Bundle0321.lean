module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemLatS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureGaussian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G.MHat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable {D : D7}

theorem sum_swap4 {α β γ δ R : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm

theorem sigR_inclE (I : Formalism.MainNotions.S.AutInst) (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star e) := by
  simp only [Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem hA_sum (I : Formalism.MainNotions.S.AutInst) {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → I.E ⊗[I.F] Af I.F) (v : ι → Fin I.n → I.E) (d : κ → I.E ⊗[I.F] Af I.F)
    (w : κ → Fin I.n → I.E) :
    hA I (∑ i, c i • incl I (v i)) (∑ j, d j • incl I (w j)) =
      ∑ i, ∑ j, sigA I (c i) *
        Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J (v i) (w j)) * d j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hA, Formalism.UG.hform, incl, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Matrix.map_apply, sigR_inclE, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  rw [sum_swap4, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_; intro i _
  refine Finset.sum_congr rfl ?_; intro j _
  refine Finset.sum_congr rfl ?_; intro k _
  refine Finset.sum_congr rfl ?_; intro l _
  ring

theorem hform_cols (I : Formalism.MainNotions.S.AutInst) {ι : Type} [Fintype ι] (Q : Matrix (Fin I.n) ι I.E) (a b : ι) :
    Formalism.UG.hform (starRingEnd I.E) I.J (fun k => Q k a) (fun l => Q l b) =
      ((Q.map (starRingEnd I.E))ᵀ * I.J * Q) a b := by
  simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem frame_indep (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) {R : Type} [CommRing R] (φ : X.B.I.E →+* R) (c : Fin (D.R.N 0) → R)
    (h : ∀ i, ∑ j, c j * φ (X.crd (qFr wt j) i) = 0) : c = 0 := by
  obtain ⟨Q, Qi, G', -, hQiQ, hq, -, -, -, -, -⟩ := _root_.GlobalTheory.St.qFrame_basis_gram D X u wt hW
  let v : (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) → R := Sum.elim c 0
  have h0 : (Q.map φ) *ᵥ v = 0 := by
    funext i
    simp only [v, Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    rw [← h i]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hq, mul_comm]
  have h1 : v = 0 := by
    have hone : (Qi.map φ * Q.map φ) *ᵥ v = v := by
      rw [← Matrix.map_mul, hQiQ, Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.one_mulVec]
    rw [← hone, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  funext j
  have := congrFun h1 (Sum.inl j)
  simpa [v] using this

theorem symm_inclE (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hι : IsAdeleIso X ιA)
    (c : D.host.E) :
    ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) c) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm c) := by
  rw [RingEquiv.symm_apply_eq, hι.1, RingEquiv.apply_symm_apply]

theorem embA_apply (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (i : Fin X.B.I.n) :
    embA X wt ιA x i = ∑ j, ιA.symm (x j) * Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.crd (qFr wt j) i) := by
  simp [embA, qA, incl]

theorem embA_injective (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    Function.Injective (embA X wt ιA) := by
  intro a b hab
  have h := frame_indep X u wt hW (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
    (fun j => ιA.symm (a j - b j)) (fun i => by
      have := congrFun hab i
      rw [embA_apply, embA_apply] at this
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, this, sub_self])
  funext j
  have := congrFun h j
  simpa [sub_eq_zero] using this

theorem hform_qFr (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (i j : Fin (D.R.N 0)) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd (qFr wt i)) (X.crd (qFr wt j)) =
      X.ιE.symm (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j) := by
  obtain ⟨Q, Qi, G', -, -, hq, -, -, -, -, hG⟩ := _root_.GlobalTheory.St.qFrame_basis_gram D X u wt hW
  have hc : ∀ j, X.crd (qFr wt j) = fun k => Q k (Sum.inl j) := fun j => funext fun k => (hq j k).symm
  rw [hc, hc, hform_cols, hG, Matrix.fromBlocks_apply₁₁, Matrix.map_apply]

theorem hA_embA (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hι : IsAdeleIso X ιA) (x y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    ιA (hA X.B.I (embA X wt ιA x) (embA X wt ιA y)) =
      hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) x y := by
  unfold embA qA
  rw [hA_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform_qFr X u wt hW, map_sum, map_mul, _root_.GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hι, RingEquiv.apply_symm_apply,
    hι.1]
  simp only [hR, Formalism.UG.hform, Matrix.map_apply]

theorem hA_incl_embA (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (v : Fin X.B.I.n → X.B.I.E)
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    hA X.B.I (incl X.B.I v) (embA X wt ιA x) =
      ∑ j, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
        (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J v (X.crd (qFr wt j))) * ιA.symm (x j) := by
  have h1 : incl X.B.I v = ∑ _i : Unit, (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I v := by simp
  rw [h1]
  unfold embA qA
  rw [hA_sum]
  simp

theorem hform_orth (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (j : Fin (D.R.N 0)) :
    (∀ a, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.crd (qFr wt j)) = 0) ∧
    (∀ a, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.fR a) (X.crd (qFr wt j)) = 0) ∧
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.zR u) (X.crd (qFr wt j)) = 0 := by
  obtain ⟨Q, Qi, G', -, -, hq, he, hf, hz, -, hG⟩ := _root_.GlobalTheory.St.qFrame_basis_gram D X u wt hW
  have hc : X.crd (qFr wt j) = fun k => Q k (Sum.inl j) := funext fun k => (hq j k).symm
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · have : X.eR a = fun k => Q k (Sum.inr (Sum.inl a)) := funext fun k => (he a k).symm
    rw [hc, this, hform_cols, hG, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have : X.fR a = fun k => Q k (Sum.inr (Sum.inr (Sum.inl a))) := funext fun k => (hf a k).symm
    rw [hc, this, hform_cols, hG, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have : X.zR u = fun k => Q k (Sum.inr (Sum.inr (Sum.inr ()))) := funext fun k => (hz k).symm
    rw [hc, this, hform_cols, hG, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem fmat_embA (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (h : Hfin X u)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
    (hR : RepF X wt ιA (h : X.B.I.Gf) y) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  unfold embA
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  unfold RepF at hR
  simp only [hR, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_comm]

theorem mem_hat_Mq (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hι : IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf := by
  let Q' : Matrix (Fin X.B.I.n) (Fin (D.R.N 0)) D.host.E := Matrix.of fun i j => X.bas.repr (qFr wt j) i
  have hM : Mq wt = ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))).comap (Q'.mulVecLin.restrictScalars (𝓞 D.host.E)) := by
    ext c
    simp only [Mq, Submodule.mem_comap, LinearMap.restrictScalars_apply, Fintype.linearCombination_apply,
      Matrix.mulVecLin_apply]
    have hv : ∑ i, (Q' *ᵥ c) i • X.bas i = ∑ j, c j • qFr wt j := by
      calc ∑ i, (Q' *ᵥ c) i • X.bas i = ∑ i, ∑ j, c j • (X.bas.repr (qFr wt j) i • X.bas i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Q', Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul, smul_smul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_comm]
        _ = ∑ j, c j • ∑ i, X.bas.repr (qFr wt j) i • X.bas i := by
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum]
        _ = ∑ j, c j • qFr wt j := by simp only [X.bas.sum_repr]
    rw [hv]
  have hinj : Function.Injective Q'.mulVec := by
    intro a b hab
    have h0 : Q' *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have h := frame_indep X u wt hW (RingHom.id X.B.I.E) (fun j => X.ιE.symm ((a - b) j)) (fun i => by
      have h1 := congrFun h0 i
      simp only [Q', Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
      have h2 : ∑ j, X.ιE.symm ((a - b) j) * (RingHom.id X.B.I.E) (X.crd (qFr wt j) i) =
          X.ιE.symm (∑ j, X.bas.repr (qFr wt j) i * (a - b) j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, mul_comm]
        rfl
      rw [h2, h1, map_zero])
    funext j
    have := congrFun h j
    simpa [sub_eq_zero] using this
  rw [hM, (GlobalTheory.St.G.Inter.hat_comap _ _ _ _ Q' hinj _ (_root_.GlobalTheory.St.G.coordLat_isLat D X)).2 x, _root_.GlobalTheory.St.G.latTransport D X ιA hι]
  have he : (fun i => ιA.symm ((Q'.map (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F)) *ᵥ x) i)) = embA X wt ιA x := by
    funext i
    rw [embA_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, symm_inclE X ιA hι, Q',
      Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  rw [he]

theorem mhat_coords : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf) ∧ (∀ x y, ιA (hA X.B.I (embA X wt ιA x) (embA X wt ιA y)) = hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) x y) ∧ Function.Injective (embA X wt ιA) ∧ (∀ x a, hA X.B.I (incl X.B.I (X.eR a)) (embA X wt ιA x) = 0 ∧ hA X.B.I (incl X.B.I (X.fR a)) (embA X wt ιA x) = 0) ∧ (∀ x, hA X.B.I (incl X.B.I (X.zR u)) (embA X wt ιA x) = 0) ∧ ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  intro D X u wt ιA hW hι
  refine ⟨mem_hat_Mq X u wt hW ιA hι, hA_embA X u wt hW ιA hι, embA_injective X u wt hW ιA, fun x a => ?_,
    fun x => ?_, fun h y hR x => fmat_embA X u wt ιA h y hR x⟩
  · rw [hA_incl_embA, hA_incl_embA]
    constructor
    · simp [(hform_orth X u wt hW _).1 a]
    · simp [(hform_orth X u wt hW _).2.1 a]
  · rw [hA_incl_embA]
    simp [(hform_orth X u wt hW _).2.2]

end GlobalTheory.St.G.MHat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ArchimedeanDensityProductTestFunctionAtSign
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.RealDensityCc

open GlobalTheory.GaussMean.RealDensity GlobalTheory.GaussMean.Density Filter Topology

theorem selfDual_complex_eq {ι : Type} [Fintype ι] {n : ℕ} (d : ι → Fin n → ℝ) (hd : ∀ v i, d v i ≠ 0)
    (μ : Measure (ι → Fin n → ℂ))
    (h : SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ v, ∑ i, d v i * ((x v i).re * (y v i).re + (x v i).im * (y v i).im) : ℝ) : ℂ)))) :
    μ = ENNReal.ofReal (∏ v, ∏ i, |d v i|) • (volume : Measure (ι → Fin n → ℂ)) := by
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.ReImVolume.exists_reIm_measurePreserving ι n
  have h1 := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag (ι × Fin n × Bool) (fun k => d k.1 k.2.1) (fun k => hd _ _) _
    (selfDual_map T h fun x y => by
      congr 3
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, (hT' _ _ _).1, (hT' _ _ _).2, mul_add])
  have he : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  refine he.map_injective ?_
  rw [h1, Measure.map_smul, hT.map_eq]
  congr 2
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, Real.mul_self_sqrt (abs_nonneg _)]
  exact hT.measurable.aemeasurable

theorem eq_zero_of_cubes {ι : Type} [Fintype ι] {K : (ι → ℝ) → ℂ} {U : Set (ι → ℝ)} (hK : ContinuousOn K U)
    {b : ι → ℝ} (hU : U ∈ 𝓝 b)
    (h : ∀ r : ℝ, 0 < r → Set.Icc b (fun v => b v + r) ⊆ U → ∫ x in Set.Icc b (fun v => b v + r), K x = 0) :
    K b = 0 := by
  by_contra hne
  have he : 0 < ‖K b‖ := norm_pos_iff.2 hne
  have h0 : ∀ᶠ x in 𝓝 b, x ∈ U ∧ dist (K x) (K b) < ‖K b‖ / 2 :=
    (show ∀ᶠ x in 𝓝 b, x ∈ U from hU).and
      (Metric.tendsto_nhds.1 (hK.continuousAt hU) _ (half_pos he))
  obtain ⟨d, hd, hδ⟩ := Metric.eventually_nhds_iff.1 h0
  set r := d / 2 with hr
  have hr0 : 0 < r := half_pos hd
  have hin : ∀ x ∈ Set.Icc b (fun v => b v + r), dist x b < d := fun x hx => by
    refine lt_of_le_of_lt (b := r) ?_ (half_lt_self hd)
    rw [dist_pi_le_iff hr0.le]
    intro v
    have h3 := hx.1 v
    have h4 := hx.2 v
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hsub : Set.Icc b (fun v => b v + r) ⊆ U := fun x hx => (hδ (hin x hx)).1
  have hk : 0 < r ^ Fintype.card ι := pow_pos hr0 _
  have hvol : volume.real (Set.Icc b (fun v => b v + r)) = r ^ Fintype.card ι := by
    rw [Measure.real, Real.volume_Icc_pi_toReal (fun v => by simp [hr0.le])]
    simp
  have hfin : volume (Set.Icc b (fun v => b v + r)) < ⊤ := isCompact_Icc.measure_lt_top
  have h1 : ∫ x in Set.Icc b (fun v => b v + r), (K x - K b) = - ((r ^ Fintype.card ι) • K b) := by
    rw [integral_sub (hK.mono hsub).integrableOn_Icc continuousOn_const.integrableOn_Icc,
      setIntegral_const, hvol, h r hr0 hsub, zero_sub]
  have h2 : ‖∫ x in Set.Icc b (fun v => b v + r), (K x - K b)‖ ≤ ‖K b‖ / 2 * r ^ Fintype.card ι := by
    rw [← hvol]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    rw [← dist_eq_norm]
    exact (hδ (hin x hx)).2.le
  rw [h1, norm_neg, norm_smul, Real.norm_of_nonneg hk.le] at h2
  nlinarith

theorem setIntegral_box {ι : Type} [Fintype ι] {X : Type} [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (q : ι → X → ℝ) (hq : ∀ v, Measurable (q v)) (φ : ι → X → ℝ) (a c : ι → ℝ) :
    ∫ y in (fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c, ∏ v, φ v (y v) =
      ∏ v, ∫ y in q v ⁻¹' Set.Icc (a v) (c v), φ v y := by
  have hm : MeasurableSet ((fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c) :=
    measurableSet_Icc.preimage
      (Measurable.of_eval fun v => (hq v).comp (measurable_pi_apply v))
  rw [← integral_indicator hm,
    ← Finset.prod_congr rfl fun v _ => integral_indicator (measurableSet_Icc.preimage (hq v)),
    ← integral_fintype_prod_volume_eq_prod]
  congr 1
  funext y
  by_cases hy : y ∈ (fun (y : ι → X) (v : ι) => q v (y v)) ⁻¹' Set.Icc a c
  · rw [Set.indicator_of_mem hy]
    exact Finset.prod_congr rfl fun v _ => (Set.indicator_of_mem (s := q v ⁻¹' Set.Icc (a v) (c v))
      ⟨hy.1 v, hy.2 v⟩ _).symm
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨v, hv⟩ : ∃ v, y v ∉ q v ⁻¹' Set.Icc (a v) (c v) := by
      by_contra! h
      exact hy ⟨fun v => (h v).1, fun v => (h v).2⟩
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)).symm

theorem density_eq_prod_of_isDens (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool)
    (φ : ι → (Fin n → ℂ) → ℝ) (D : ι → ℝ → ℝ) (hD : ∀ v, IsDens (ε v) (φ v) (D v)) (G : (ι → ℝ) → ℂ)
    (hG : ContinuousOn G {b | ∀ v, b v ≠ 0})
    (h : ∀ S : Set (ι → ℝ), IsCompact S → S ⊆ {b | ∀ v, b v ≠ 0} →
      ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, φ v (y v) : ℝ) : ℂ) =
        ∫ b in S, G b)
    (b : ι → ℝ) (hb : ∀ v, b v ≠ 0) : G b = ((∏ v, D v (b v) : ℝ) : ℂ) := by
  have hH : ContinuousOn (fun x : ι → ℝ => ((∏ v, D v (x v) : ℝ) : ℂ)) {b | ∀ v, b v ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_finsetProd _ fun v _ =>
      (hD v).1.comp (continuous_apply v).continuousOn fun x hx => hx v)
  have hU : {b : ι → ℝ | ∀ v, b v ≠ 0} ∈ 𝓝 b :=
    Filter.eventually_all.2 fun v => (continuous_apply v).continuousAt.eventually_ne (hb v)
  refine sub_eq_zero.1 (eq_zero_of_cubes (hG.sub hH) hU fun r hr hsub => ?_)
  simp only [Pi.sub_apply]
  rw [integral_sub (hG.mono hsub).integrableOn_Icc (hH.mono hsub).integrableOn_Icc, ← h _ isCompact_Icc hsub,
    integral_complex_ofReal, integral_complex_ofReal, sub_eq_zero,
    setIntegral_box (fun v => qEps (ε v)) (fun v => (continuous_qEps (ε v)).measurable)]
  congr 1
  refine Eq.trans ?_ (setIntegral_box (fun _ => id) (fun _ => measurable_id) D b fun v => b v + r).symm
  refine Finset.prod_congr rfl fun v _ => (hD v).2 _ isCompact_Icc fun t ht => ?_
  classical
  have := hsub (a := Function.update b v t) ⟨fun w => ?_, fun w => ?_⟩ v
  · simpa using this
  · by_cases hw : w = v
    · subst hw; simpa using ht.1
    · simp [hw]
  · by_cases hw : w = v
    · subst hw; simpa using ht.2
    · simp [hw, hr.le]

theorem density_at_sign : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ (lamv : InfinitePlace I.F → ℝ) (χ : Ainf I.F → ℂ), (∀ v, lamv v ≠ 0) → (∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) → ∀ (μi : Measure (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E)) (νi : Measure (Ainf I.F)), SelfDual μi (fun X Y => χ (BR (Ainf I.F) I.cm.sig I.J X Y)) → SelfDual νi (fun s t => χ (s * t)) → ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ), (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v) ∧ IsDens (I.ε v) (φ v) (D v)) → ∀ Fi : Ainf I.F → ℂ, IsContDensityOn μi (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) id νi {c | IsUnit c} (fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) Fi → ∀ s : Bool, Fi (sgn (Ainf I.F) s) = ((∏ v, 2 ^ I.n * |lamv v| ^ ((I.n : ℝ) - 1 / 2) * D v (sgn ℝ s) : ℝ) : ℂ) := by
  intro I θ hθ lam χ hlam hχ μ ν hμ hν φ D hφ Fi hF s
  obtain ⟨a, ha⟩ := exists_coord_base I θ hθ
  obtain ⟨T, hT⟩ := exists_coord_space I θ hθ
  have hform := fun v => trace_form I v (θ v) (hθ v)
  have h2 : Module.finrank I.F I.E = 2 := I.cm.deg2
  have : FiniteDimensional I.F I.E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  have : IsModuleTopology (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf I.F ⊗[I.F] I.E) := IsModuleTopology.isTopologicalRing (Ainf I.F) _
  have : SecondCountableTopology (Ainf I.F) := a.toHomeomorph.secondCountableTopology
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := I.F) (E := I.E) (Ainf I.F)
  have : SecondCountableTopology (Ainf I.F ⊗[I.F] I.E) := e0.secondCountableTopology
  have : BorelSpace (Ainf I.F ⊗[I.F] I.E) := ⟨rfl⟩
  have : BorelSpace (Ainf I.F) := ⟨rfl⟩
  have hmul : ∀ x y v, a (x * y) v = a x v * a y v := fun x y v => by
    have : ((a (x * y) v : ℝ) : ℂ) = (a x v : ℝ) * (a y v : ℝ) := by
      rw [← ha, ← ha, ← ha, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact_mod_cast this
  have hone : ∀ v, a 1 v = 1 := fun v => by
    have : ((a 1 v : ℝ) : ℂ) = 1 := by
      rw [← ha]; exact map_one (θ v)
    exact_mod_cast this
  have hsgn : a (sgn (Ainf I.F) s) = fun _ => sgn ℝ s := by
    funext v
    cases s <;> simp [sgn, hone]
  have hhalf : ∀ v, a (algebraMap I.F (Ainf I.F) (1 / 2)) v = 1 / 2 := fun v => by
    have h1 : algebraMap I.F (Ainf I.F) (1 / 2) + algebraMap I.F (Ainf I.F) (1 / 2) = 1 := by
      rw [← map_add (f := _), add_halves, map_one]
    have := hone v
    rw [← h1, map_add (f := _), Pi.add_apply] at this
    linarith
  have htr : ∀ (X Y : Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) v,
      a (Algebra.trace (Ainf I.F) (Ainf I.F ⊗[I.F] I.E) (hR (Ainf I.F) I.cm.sig I.J (X 0) (Y 0))) v =
        ∑ i, (if I.ε v i then 2 else -2) * ((T X v i).re * (T Y v i).re + (T X v i).im * (T Y v i).im) :=
    fun X Y v => by
      have := hform v (X 0) (Y 0)
      rw [ha] at this
      rw [hT, hT]
      exact_mod_cast this
  have hq : ∀ X, a (qR (Ainf I.F) I.cm.sig I.J (X 0)) = fun v => qEps (I.ε v) (T X v) := fun X => by
    funext v
    rw [qR, hmul, hhalf, htr, qEps, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    split_ifs <;> ring
  have hν' := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag _ lam hlam _ (selfDual_map a hν fun x y => by
    rw [hχ]; simp only [ha, Complex.ofReal_re, hmul])
  have hμ' := selfDual_complex_eq (fun v i => lam v * (if I.ε v i then 2 else -2))
    (fun v i => mul_ne_zero (hlam v) (by split_ifs <;> norm_num)) _ (selfDual_map T hμ fun x y => by
      rw [hχ]; simp only [ha, Complex.ofReal_re, BR, Fin.sum_univ_one, htr, Finset.mul_sum, mul_assoc])
  have hc : (∏ v, ∏ i, |lam v * (if I.ε v i then 2 else -2)|) = ∏ v, (2 * |lam v|) ^ I.n := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => 2 * |lam v|) fun i _ => by
      rw [abs_mul]; split_ifs <;> simp [mul_comm]]
    simp
  rw [hc] at hμ'
  set c : ℝ := ∏ v, (2 * |lam v|) ^ I.n with hcdef
  set c' : ℝ := ∏ v, √|lam v| with hc'def
  have hc0 : 0 < c := Finset.prod_pos fun v _ => pow_pos (mul_pos two_pos (abs_pos.2 (hlam v))) _
  have hc'0 : 0 < c' := Finset.prod_pos fun v _ => Real.sqrt_pos.2 (abs_pos.2 (hlam v))
  have heT : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hea : MeasurableEmbedding a := a.toHomeomorph.measurableEmbedding
  have hunit : ∀ x : Ainf I.F, (∀ v, a x v ≠ 0) → IsUnit x := fun x hx => by
    refine IsUnit.of_mul_eq_one (a.symm fun v => (a x v)⁻¹) (a.injective ?_)
    funext v
    rw [hmul, ContinuousAddEquiv.apply_symm_apply, hone, mul_inv_cancel₀ (hx v)]
  have key := density_eq_prod_of_isDens _ I.n I.ε φ D (fun v => (hφ v).2.2)
    (fun b => ((c' / c : ℝ) : ℂ) * Fi (a.symm b))
    (continuousOn_const.mul (hF.1.comp a.symm.continuous.continuousOn fun b hb =>
      hunit _ (by simpa using hb))) (fun S hS hSU => by
      have h1 := hF.2 (a ⁻¹' S) (a.toHomeomorph.isCompact_preimage.2 hS) fun x hx => hunit x (hSU hx)
      have h3 := hea.setIntegral_map (μ := ν) (fun b => Fi (a.symm b)) S
      have h4 := heT.setIntegral_map (μ := μ) (fun y => ((∏ v, φ v (y v) : ℝ) : ℂ))
        ((fun y v => qEps (I.ε v) (y v)) ⁻¹' S)
      simp only [ContinuousAddEquiv.symm_apply_apply] at h3
      have h5 : (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) ⁻¹' (id '' (a ⁻¹' S)) =
          T ⁻¹' ((fun y v => qEps (I.ε v) (y v)) ⁻¹' S) := by
        ext X
        simp only [Set.image_id, Set.mem_preimage, hq]
      rw [h5, ← h3] at h1
      simp only [← hT] at h1
      rw [← h4, hμ', hν', Measure.restrict_smul, Measure.restrict_smul, integral_smul_measure,
        integral_smul_measure, ENNReal.toReal_ofReal hc0.le, ENNReal.toReal_ofReal hc'0.le,
        Complex.real_smul, Complex.real_smul] at h1
      have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
      rw [integral_const_mul, Complex.ofReal_div, div_mul_eq_mul_div, ← h1, mul_div_cancel_left₀ _ hcc])
    (fun _ => sgn ℝ s) (fun _ => by cases s <;> simp [sgn])
  rw [← hsgn, ContinuousAddEquiv.symm_apply_apply] at key
  have hcc : ((c' / c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hc'0 hc0).ne'
  refine mul_left_cancel₀ hcc ?_
  rw [key, ← Complex.ofReal_mul, hcdef, hc'def, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  have hl : 0 < |lam v| := abs_pos.2 (hlam v)
  rw [Real.rpow_sub hl, Real.rpow_natCast, Real.sqrt_eq_rpow, mul_pow]
  have : 0 < |lam v| ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hl _
  field_simp

end GlobalTheory.GaussMean.RealDensityCc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deepRegion_kernelDiagonal_bound : GlobalTheory.FlagMeas.AbsoluteVolume → GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  first | exact @GlobalTheory.DeepRegion.deepBound | exact GlobalTheory.DeepRegion.deepBound | (intros; apply GlobalTheory.DeepRegion.deepBound <;> assumption)
end

