module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BridgeC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0018

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def reimV {V : Type} {n m : ℕ} (M : V → Matrix (Fin n) (Fin m) ℂ) : EuclideanSpace ℝ (V × Fin n × Fin m × Bool) :=
  (WithLp.equiv 2 (V × Fin n × Fin m × Bool → ℝ)).symm fun p =>
    if p.2.2.2 then (M p.1 p.2.1 p.2.2.1).re else (M p.1 p.2.1 p.2.2.1).im

def BetaIso : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ Bc : EuclideanSpace ℝ (KapI X) ≃L[ℝ]
        EuclideanSpace ℝ (InfinitePlace X.B.I.F × Fin X.B.I.n × Fin (D.R.rS + 1 + D.R.rS) × Bool),
      ∀ Y : TupI X, Bc (tupCoord X Y) = reimV (fun v => betaV X v Y)

def MuBridge : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    μinf.map (fun Y => reimV (fun v => betaV X v Y)) =
      ENNReal.ofReal (2 ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F))) • volume

def NuBridge : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ (κ : Type) (_ : Fintype κ) (Hh : EuclideanSpace ℝ κ →ₗ[ℝ]
        (InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ))
      (Tc : HmI X ≃ₜ EuclideanSpace ℝ κ),
      (∀ s v, (Hh s v)ᴴ = Hh s v) ∧ (∀ s, ∑ v, ∑ i, ∑ j, ‖Hh s v i j‖ ^ 2 = ‖s‖ ^ 2) ∧
      (∀ M : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ,
        (∀ v, (M v)ᴴ = M v) → ∃ s, Hh s = M) ∧
      (∀ S T, Tc (S + T) = Tc S + Tc T) ∧
      (∀ S v, Hh (Tc S) v = (S : Matrix _ _ _).map (PI.AprimeInfU.thetaInf X v)) ∧
      νinf.map Tc = volume

def DKForm : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L →
    ∀ x v, betaV X v ((tupCoord X).symm (fderiv ℝ (KapOrb X u' (kap0 X hb c L)) 0 x)) =
      uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')

def RowsZ : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S →
    ∀ v, ∀ i ∈ S v, ∀ b, (uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b = 0

def DetT : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ v : InfinitePlace X.B.I.F, ‖X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det‖ = Tw u'

def PlaceJacAll : Prop := ∀ (V : Type) [Fintype V] (n m : ℕ) (ε : V → Fin n → Bool) (S : V → Finset (Fin n))
    (w : V → Matrix (Fin n) (Fin m) ℂ) (c : V → Matrix (Fin n) (Fin n) ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ))
    (H : EuclideanSpace ℝ κ →ₗ[ℝ] (V → Matrix (Fin m) (Fin m) ℂ)),
    (∀ v, n = m + (S v).card) → (∀ v, ∀ i ∈ S v, ∀ b, w v i b = 0) →
    (∀ v, ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v).det ≠ 0) →
    (∀ v, (c v)ᴴ * Formalism.REAL.Jm (ε v) * c v = Formalism.REAL.Jm (ε v)) →
    (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) →
    (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) →
    (∀ M : V → Matrix (Fin n) (Fin n) ℂ, (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
      ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) → ∃ x, L x = M) →
    (∀ t v, (H t v)ᴴ = H t v) → (∀ t, ∑ v, ∑ i, ∑ j, ‖H t v i j‖ ^ 2 = ‖t‖ ^ 2) →
    (∀ M : V → Matrix (Fin m) (Fin m) ℂ, (∀ v, (M v)ᴴ = M v) → ∃ t, H t = M) →
    ∃ Fe : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) ≃L[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool),
      (∀ z, Fe z = reimV (fun v => c v * (L z.1 v * w v +
        (1 / 2 : ℂ) • (w v * ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v)⁻¹ * H z.2 v)))) ∧
      (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).map Fe =
        ENNReal.ofReal (∏ v, 2 ^ (n * m) / ‖((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v).det‖ ^ (S v).card) • volume

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MuBridgeA
section
noncomputable section

namespace PI.AprimeInfW.MuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

section Tr

variable {D : D7} (X : HidaSetting D)

theorem emb_real (v : InfinitePlace X.B.I.F) (a : X.B.I.F) : conj (v.embedding a) = v.embedding a := by
  have hv : v.IsReal := totReal_of X v
  have h := NumberField.ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hv)
  have := RingHom.congr_fun h a
  simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

theorem phi_star (v : InfinitePlace X.B.I.F) (e : X.B.I.E) : X.B.I.φ v (star e) = conj (X.B.I.φ v e) :=
  X.B.I.cm.cmUnram.2.1 _ e

theorem phi_notReal (v : InfinitePlace X.B.I.F) : ¬ ∀ e : X.B.I.E, conj (X.B.I.φ v e) = X.B.I.φ v e := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal (X.B.I.φ v) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext e
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq, h e]
  have hc := X.B.I.cm.cmUnram.1.isComplex (InfinitePlace.mk (X.B.I.φ v))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem emb_trace (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    v.embedding (Algebra.trace X.B.I.F X.B.I.E e) = X.B.I.φ v e + conj (X.B.I.φ v e) := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  let φA : X.B.I.E →ₐ[X.B.I.F] ℂ := { X.B.I.φ v with commutes' := X.B.I.φ_over v }
  let ψA : X.B.I.E →ₐ[X.B.I.F] ℂ :=
    { (starRingEnd ℂ).comp (X.B.I.φ v) with
      commutes' := fun a => by
        show conj (X.B.I.φ v (algebraMap X.B.I.F X.B.I.E a)) = v.embedding a
        rw [X.B.I.φ_over, emb_real] }
  have hne : φA ≠ ψA := by
    intro h
    apply phi_notReal X v
    intro e
    have := congrArg (fun f : X.B.I.E →ₐ[X.B.I.F] ℂ => f e) h
    exact this.symm
  have hcard : Fintype.card (X.B.I.E →ₐ[X.B.I.F] ℂ) = 2 := by
    rw [AlgHom.card X.B.I.F X.B.I.E ℂ, X.B.I.cm.deg2]
  have huniv : (Finset.univ : Finset (X.B.I.E →ₐ[X.B.I.F] ℂ)) = {φA, ψA} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have h := trace_eq_sum_embeddings (K := X.B.I.F) (L := X.B.I.E) ℂ (x := e)
  rw [huniv, Finset.sum_pair hne] at h
  exact h

theorem evInf_conj (v : InfinitePlace X.B.I.F) (a : Ainf X.B.I.F) :
    conj (PI.AprimeInfU.evInf X v a) = PI.AprimeInfU.evInf X v a := by
  have hv : v.IsReal := totReal_of X v
  show conj (InfinitePlace.Completion.extensionEmbedding v (a v)) =
    InfinitePlace.Completion.extensionEmbedding v (a v)
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem evInf_alg (v : InfinitePlace X.B.I.F) (a : X.B.I.F) :
    PI.AprimeInfU.evInf X v (algebraMap X.B.I.F (Ainf X.B.I.F) a) = v.embedding a :=
  evV_algebraMap X.B.I v a

theorem trace_one_tmul (e : X.B.I.E) :
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) =
      algebraMap X.B.I.F (Ainf X.B.I.F) (Algebra.trace X.B.I.F X.B.I.E e) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem evInf_trace (v : InfinitePlace X.B.I.F) (z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.evInf X v (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) z) =
      PI.AprimeInfU.thetaInf X v z + conj (PI.AprimeInfU.thetaInf X v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[X.B.I.F] e = a • ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, trace_one_tmul, smul_eq_mul, map_mul, evInf_alg, emb_trace, ← h1, thetaInf_tmul, map_mul,
      evInf_conj]
    ring
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]; ring

theorem theta_sigR (v : InfinitePlace X.B.I.F) (t : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig t) = conj (PI.AprimeInfU.thetaInf X v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig (a ⊗ₜ[X.B.I.F] e) = a ⊗ₜ[X.B.I.F] (star e) := rfl
    rw [h, thetaInf_tmul, thetaInf_tmul, map_mul, evInf_conj, phi_star]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem theta_hR (v : InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (hR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y) =
      ∑ i, ∑ j, conj (PI.AprimeInfU.thetaInf X v (x i)) * X.B.I.φ v (X.B.I.J i j) *
        PI.AprimeInfU.thetaInf X v (y j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, theta_sigR, JR, Matrix.map_apply, thetaInf_inclR]

end Tr

section Form

theorem form_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj (p i) * M i j * q j = star p ⬝ᵥ (M *ᵥ q) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_P {n : ℕ} (P A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj ((P *ᵥ p) i) * A i j * (P *ᵥ q) j = ∑ i, ∑ j, conj (p i) * (Pᴴ * A * P) i j * q j := by
  rw [form_dot, form_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem form_Jm {n : ℕ} (ε : Fin n → Bool) (p q : Fin n → ℂ) :
    (∑ i, ∑ j, conj (p i) * Formalism.REAL.Jm ε i j * q j).re =
      ∑ i, (if ε i then 1 else -1 : ℝ) * ((p i).re * (q i).re + (p i).im * (q i).im) := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

end Form

section Beta

variable {D : D7} (X : HidaSetting D)

theorem theta_col (v : InfinitePlace X.B.I.F) (Y : TupI X) (b : Fin (D.R.rS + 1 + D.R.rS)) :
    (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) = X.B.I.P v *ᵥ fun i => betaV X v Y i b := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have : (fun i => betaV X v Y i b) = (X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y b j) := by
    funext i
    simp [betaV]
  rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]

theorem re_evInf_BR (v : InfinitePlace X.B.I.F) (Y Z : TupI X) :
    (PI.AprimeInfU.evInf X v (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y Z)).re =
      ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v Y i b).re * (betaV X v Z i b).re + (betaV X v Y i b).im * (betaV X v Z i b).im)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [BR, map_sum, Complex.re_sum, evInf_trace, Complex.add_re, Complex.conj_re]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [theta_hR]
  have e1 := theta_col X v Y b
  have e2 := theta_col X v Z b
  have hY : ∀ i, PI.AprimeInfU.thetaInf X v (Y b i) = (X.B.I.P v *ᵥ fun i => betaV X v Y i b) i :=
    fun i => congrFun e1 i
  have hZ : ∀ i, PI.AprimeInfU.thetaInf X v (Z b i) = (X.B.I.P v *ᵥ fun i => betaV X v Z i b) i :=
    fun i => congrFun e2 i
  simp only [hY, hZ]
  have hJ : ∀ i j, X.B.I.φ v (X.B.I.J i j) = (X.B.I.J.map (X.B.I.φ v)) i j := fun _ _ => rfl
  simp only [hJ]
  rw [form_P, X.B.I.P_spec v, form_Jm, ← two_mul, Finset.mul_sum]

theorem betaI_bridge (x y : EuclideanSpace ℝ (KapI X)) :
    betaI X x y = ∑ v, ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v ((tupCoord X).symm x) i b).re * (betaV X v ((tupCoord X).symm y) i b).re +
          (betaV X v ((tupCoord X).symm x) i b).im * (betaV X v ((tupCoord X).symm y) i b).im)) := by
  simp only [betaI]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact re_evInf_BR X v _ _

end Beta

end PI.AprimeInfW.MuB
end
end

