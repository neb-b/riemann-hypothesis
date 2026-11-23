module

public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaReal

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem thetaV_eq_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.thetaV I v y = θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) y) := by
  have hb : ∀ b : Ainf I.F,
      InfinitePlace.Completion.extensionEmbedding v (b v) = θ' (b ⊗ₜ[I.F] (1 : I.E)) := by
    intro b
    have hc : Continuous fun b : Ainf I.F => InfinitePlace.Completion.extensionEmbedding v (b v) :=
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
    refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hc hθ'.2 (funext fun x => ?_)) b
    show InfinitePlace.Completion.extensionEmbedding v (algebraMap I.F (Ainf I.F) x v) =
      θ' ((algebraMap I.F (Ainf I.F) x) ⊗ₜ[I.F] (1 : I.E))
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul x, hθ'.1, I.φ_over]
    exact Formalism.L2.SG.AdBridge.evV_algebraMap I v x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul, Algebra.TensorProduct.map_tmul]
    have e : (fstA I.F a) ⊗ₜ[I.F] ((AlgHom.id I.F I.E) x) =
        ((fstA I.F a) ⊗ₜ[I.F] (1 : I.E)) * ((1 : Ainf I.F) ⊗ₜ[I.F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    rw [e, map_mul, hθ'.1, ← hb]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem map_thetaV_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (k : Formalism.L2.SG.AdBridge.HAd I) :
    (Formalism.L2.SG.AdBridge.hmat I k).map (Formalism.L2.SG.AdBridge.thetaV I v) = Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ' k := by
  ext i j
  exact thetaV_eq_gen I v θ' hθ' _

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem tauF_eq_comm (I : Formalism.MainNotions.S.AutInst) (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.tauF I y = Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E
      (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.tauF_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem ofHAFin_eq_one (I : Formalism.MainNotions.S.AutInst) (k : Formalism.L2.SG.AdBridge.HAd I)
    (h : (Formalism.L2.SG.AdBridge.hmat I k).map (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E)) = 1) :
    Formalism.L2.SG.AdBridge.ofHAFin I k = 1 := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at e
  simp only [Formalism.L2.SG.AdBridge.ofHAFin, Matrix.map_apply, tauF_eq_comm, e, Matrix.one_apply]
  split_ifs <;> simp

theorem infMat_of_mem_GfC {D : D7} (k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0))
    (θ' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram θ' k = 1 := by
  have e : (infHom (D.sp.Y 0) k).val = 1 := by
    rw [show infHom (D.sp.Y 0) k = 1 from hk]; rfl
  ext i j
  have e2 := congrFun (congrFun e i) j
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [Matrix.map_apply, Matrix.map_apply]
  refine (congrArg θ' e2).trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_GfC_of_infMat {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (k : GA D (D.sp.Y 0))
    (hk : ∀ τ, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram (θ τ) k = 1) : k ∈ GfC (D.sp.Y 0) := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  obtain ⟨h1, -⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.Y 0)).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact GlobalTheory.PointAtPlace.tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  exact h1 k fun σ => hk (r σ)

theorem conj_eq_iff {n : ℕ} (P M N : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    P⁻¹ * M * P = N ↔ M = P * N * P⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  constructor
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

theorem isAtTau_atTau {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) : IsAtTau θ (D.sp.Y 0) τ g (atTau θ (D.sp.Y 0) τ g) := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau (D.sp.Y 0) τ θ hθ g hg
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

theorem iota_real_finite_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hι : ∀ x : I.E, HEq (ιE x) x) :
    let ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (ι k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ pl.symm τ → (ι (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  intro ι
  subst h
  have hι' : ∀ x, ιE x = x := fun x => eq_of_heq (hι x)
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := by
    ext v
    have e1 : embS D (pl v) = embS D ((Formalism.L2.Host.tauPl D).symm v) := by
      ext x
      exact (congrArg (embS D (pl v)) (hι' x).symm).trans (hφ v x).symm
    exact GlobalTheory.PointAtPlace.tauE_injective e1
  subst hpl
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hPu := (Formalism.L2.SG.InstExistsPf.instOf D).P_unit

  have hd : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).1 (hPu v)
  refine ⟨fun k => ⟨fun hk => ?_, fun hk => ?_⟩, ?_, ?_⟩
  · funext v
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι k).1 v) = 1
    rw [hinf k v]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k = 1 := infMat_of_mem_GfC k hk _
    rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
  · apply mem_GfC_of_infMat θ hθ k
    intro τ
    have e := hinf k (Formalism.L2.Host.tauPl D τ)
    rw [congrFun hk (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply] at e
    have e2 := (conj_eq_iff _ _ _ (hPu _)).1 e.symm
    refine e2.trans ?_
    rw [show Formalism.MainNotions.S.uMat ((1 : (Formalism.L2.SG.InstExistsPf.instOf D).Ginf) (Formalism.L2.Host.tauPl D τ)) = 1 from rfl,
      Matrix.mul_one]
    exact Matrix.mul_nonsing_inv _ (hd _)
  · intro τ g hg
    have hat := isAtTau_atTau θ hθ τ g hg
    refine ⟨?_, fun v hv => ?_, ?_⟩
    · apply Subtype.ext
      apply Units.ext
      have e := (key (atTau θ (D.sp.Y 0) τ g)).2
      refine e.trans (ofHAFin_eq_one _ _ ?_)
      · have e3 : (finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g)).val = 1 := by
          rw [show finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) = 1 from hat.1]; rfl
        ext i j
        exact congrFun (congrFun e3 i) j
    · apply Subtype.ext
      apply Units.ext
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 v) = 1
      rw [hinf _ v]
      have hne : (Formalism.L2.Host.tauPl D).symm v ≠ τ := fun e => hv ((Equiv.symm_apply_eq _).1 e)
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ ((Formalism.L2.Host.tauPl D).symm v)) (atTau θ (D.sp.Y 0) τ g) = 1 := hat.2.2 _ hne
      rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
    · apply heq_of_eq
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (Formalism.L2.Host.tauPl D τ)) = _
      rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ τ) (atTau θ (D.sp.Y 0) τ g) = g := hat.2.1
      rw [e]
      rfl
  · intro τ y
    set P := (Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ) with hP
    have hdP : IsUnit P.det := hd _
    set H : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      gramAt D (D.sp.Y 0) τ with hH
    set Y : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      Formalism.MainNotions.S.uMat y with hY
    have hs : Pᴴ * H * P = Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := by
      have := (Formalism.L2.SG.InstExistsPf.instOf D).P_spec (Formalism.L2.Host.tauPl D τ)
      have eφ : (Formalism.L2.SG.InstExistsPf.instOf D).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
        show embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D τ)) = _
        rw [Equiv.symm_apply_apply]
        rfl
      rw [eφ] at this
      exact this
    have hy : Yᴴ * Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) * Y =
        Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := y.2
    have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdP
    have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
    have hg : (P * Y * P⁻¹)ᴴ * H * (P * Y * P⁻¹) = H := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      calc (P⁻¹)ᴴ * (Yᴴ * Pᴴ) * H * (P * Y * P⁻¹) = (P⁻¹)ᴴ * (Yᴴ * (Pᴴ * H * P) * Y) * P⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (P⁻¹)ᴴ * (Pᴴ * H * P) * P⁻¹ := by rw [hs, hy]
        _ = H := by
            simp only [Matrix.mul_assoc]
            rw [hPi, Matrix.mul_one, ← Matrix.mul_assoc, hPiH, Matrix.one_mul]
    refine ⟨P * Y * P⁻¹, hg, ?_⟩
    have hat := isAtTau_atTau θ hθ τ (P * Y * P⁻¹) hg
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹))).1 (Formalism.L2.Host.tauPl D τ)) = Y
    rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ τ) (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹)) = P * Y * P⁻¹ := hat.2.1
    rw [e]
    exact (conj_eq_iff _ _ _ (hPu _)).2 rfl

theorem iotaX_real_finite : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod hιE
  exact iota_real_finite_of_eq R.θ hMod.inf X.B.I h X.ιE X.pl X.φ_eq hιE

end GlobalTheory.IotaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicSphericalEigenfunctionLocalHeckeAlgebraEig
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

variable {D : D7}

theorem isUnram_of_not_isSplit {v : HeightOneSpectrum (𝓞 D.host.F)} (hs : ¬ IsSplit (E := D.host.E) v) :
    Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := by
  intro P hP
  have hPv : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Q ∈ Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (P.under (𝓞 D.host.F)) ↔ Q.under (𝓞 D.host.F) = v := by
    intro Q
    rw [hPv]
    simp only [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have h1 : (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (P.under (𝓞 D.host.F))).card = 1 := by
    refine Finset.card_eq_one.2 ⟨P, Finset.eq_singleton_iff_unique_mem.2 ⟨(hmem P).2 hPv, fun Q hQ => ?_⟩⟩
    by_contra hne
    exact hs ⟨Q, P, hne, congrArg HeightOneSpectrum.asIdeal ((hmem Q).1 hQ), hP⟩
  exact PI.UnitaryGroupMassFormula.HostPrimeFacts.unram D.R D.host P h1

theorem exists_cartan (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), ∀ g : Gv V v,
      ∃ k₁ ∈ Kv V v, ∃ k₂ ∈ Kv V v, ∃ (g' : Gv V v) (a : GL (Fin V.rank) (w.adicCompletion D.host.E))
        (d : Fin V.rank → ℤ) (u : Fin V.rank → w.adicCompletion D.host.E),
        IsFrameAt w (frameLat V) a ∧ Antitone d ∧ (∀ i, Valued.v (u i) = WithZero.exp (-d i)) ∧
        (a⁻¹ * locMat D.sp.cm.sig V.gram h g' * a).1 = Matrix.diagonal u ∧ g = k₁ * g' * k₂ := by
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  by_cases hsp : IsSplit (E := D.host.E) v
  · obtain ⟨w, -, -, hw, -⟩ := id hsp
    have h : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hw
    obtain ⟨e, ⟨⟨a, ha, e1⟩, e2⟩, -⟩ :=
      GlobalTheory.LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hspan h hsp hd
    refine ⟨w, h, fun g => ?_⟩
    obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    obtain ⟨d, hdA, k₁, h₁, k₂, h₂, eg⟩ := Formalism.UG.Final.CartanDecomp D.host.E w V.rank ϖ (mem_Ov_of_isUnifV hϖ) hϖ (e g)
    refine ⟨e.symm k₁, (e2 _).2 (by simpa using h₁), e.symm k₂, (e2 _).2 (by simpa using h₂),
      e.symm (k₁⁻¹ * e g * k₂⁻¹), a, d, fun i => ϖ ^ d i, ha, hdA, fun i => ?_, ?_, ?_⟩
    · rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
      simp
    · rw [← e1, e.apply_symm_apply, Units.val_mul, Units.val_mul, eg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rfl
    · apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      group
  · obtain ⟨w, hw⟩ := ((exists_isInertChart _ (isCMExt_host D) v).1 (isUnram_of_not_isSplit hsp)).resolve_left hsp
    have h : w.under (𝓞 D.host.F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
    obtain ⟨-, ⟨c, hc, -⟩, -, -, hrest⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w h hw
    obtain ⟨⟨ϖ, hU⟩, hch⟩ := hrest c hc
    obtain ⟨e, ⟨-, ⟨a, ha, -, e1⟩, e2⟩, -⟩ := hch _ _ _ hH hL.fg hspan hd
    refine ⟨w, h, fun g => ?_⟩
    obtain ⟨d, t, hdA, ht, k₁, h₁, k₂, h₂, eg⟩ := GlobalTheory.LFun.cartanU hU (e g)
    refine ⟨e.symm k₁, (e2 _).2 (by simpa using h₁), e.symm k₂, (e2 _).2 (by simpa using h₂),
      e.symm t, a, d, fun i => ϖ ^ d i, ha, hdA, fun i => ?_, by rw [← e1, e.apply_symm_apply, ht], ?_⟩
    · rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hU.2.2.2.1, ← WithZero.exp_zsmul]
      simp
    · apply e.injective
      simp only [map_mul, e.apply_symm_apply, eg]

theorem eigen_heckeAlg : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ v ∉ Sb, ∀ f : GA D V → ℂ, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) ∧ ∀ h ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f := by
  intro D V J χ Sb hJ v hv f hf c hc
  have hfix : f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (fixed_of_level hJ hv hf hk)
  refine ⟨hfix, fun x hx => ?_⟩
  obtain ⟨w, h, hcart⟩ := exists_cartan V v
  have hs := isEigenSys_of_heckeLin hJ hv h hfix (hc w)
  have := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat V
  have hK : IsCommensurated (Kv V v) := PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _
    (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v) (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
  have hm := Formalism.UG.Final.DosetIndMem (Gv V v) (Kv V v) ℂ
  refine GlobalTheory.LFun.hecke_induction (K := Kv V v)
    (p := fun h => ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f)
    ⟨0, by simp [heckeVec]⟩ ?_ ?_ hx
  · rintro g1 hg1 g2 hg2 ⟨a1, e1⟩ ⟨a2, e2⟩
    exact ⟨a1 + a2, by rw [GlobalTheory.LFun.heckeVec_add hK _ hg1 hg2, e1, e2, add_smul]⟩
  · intro r g
    obtain ⟨k₁, hk₁, k₂, hk₂, g', a, d, u, ha, hd, hu, hg, rfl⟩ := hcart g
    refine ⟨r * c w (List.ofFn d), ?_⟩
    rw [GlobalTheory.LFun.dosetInd_mul hk₁ hk₂, GlobalTheory.LFun.heckeVec_smul hK _ r (hm g'), hs a g' d u ha hd hu hg, smul_smul]

end GlobalTheory.FinZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointInjOfParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjointInjectiveOfParts

theorem adjoint_inj_of_parts {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (T : H' →ₗ[ℂ] H) {ι : Type*}
    (P : ι → Submodule ℂ H) (s : ι → ℂ) (hs : ∀ c, s c ≠ 0)
    (hP : ∀ c, ∀ x ∈ P c, T (LinearMap.adjoint T x) = s c • x) {x : H} (hx : x ∈ ⨆ c, P c)
    (h0 : LinearMap.adjoint T x = 0) : x = 0 := by
  have hle : (⨆ c, P c) ≤ LinearMap.range T := by
    refine iSup_le fun c y hy => ⟨LinearMap.adjoint T ((s c)⁻¹ • y), ?_⟩
    rw [hP c _ ((P c).smul_mem _ hy), smul_smul, mul_inv_cancel₀ (hs c), one_smul]
  obtain ⟨w, rfl⟩ := hle hx
  have h1 : ⟪T w, T w⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.AdjointInjectiveOfParts


open GlobalTheory.Hk3 in
theorem GlobalTheory.LiftRows.upInj_of_scal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → Scal R SF → UpInj R ∧ UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI SF hSF hScal
  obtain ⟨lam, κ, hκ, hl, hW, hE⟩ := hScal
  constructor
  · intro t
    refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
    obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c)
      (fun c => ((κ * ∏ i, lam i t c : ℝ) : ℂ))
      (fun c => Complex.ofReal_ne_zero.2 (mul_pos hκ (Finset.prod_pos fun i _ => hl i t c)).ne')
      (fun c x hx => hE t c x hx) ?_ h0
    rw [hsp]; trivial
  · intro i t x hx h0
    obtain ⟨h, -, -, -, hsp, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hI SF hSF i
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.thG i t) (fun c => Wcc R SF i c)
      (fun c => ((lam i t c : ℝ) : ℂ)) (fun c => Complex.ofReal_ne_zero.2 (hl i t c).ne')
      (fun c x hx => hW i t c x hx) ?_ h0
    rw [hsp]; exact ⟨x, hx⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharpolyUnitaryEqConjugateReciprocalStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ γ : GRat σ J, γ.1.1.charpoly = sharp σ n γ.1.1.charpoly := by
  first | exact @GlobalTheory.TrEll.charpoly_eq_sharp | exact GlobalTheory.TrEll.charpoly_eq_sharp | (intros; apply GlobalTheory.TrEll.charpoly_eq_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermEqVolumeMulOrbitalIntegral
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ClassUnfold

theorem hasClassInt_of_hasOrbInt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → IsMulCommutative (cent γ) →
    ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)),
    IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → dt 𝓣 < ⊤ →
    ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ γ dt f c →
    ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (dt.real 𝓣 * c) := by
  intro H _ _ _ _ _ _ _ _ Γ _ γ hγ hc μ _ dt _ 𝓣 h𝓣 hfin f c hf hfc hO 𝓕 h𝓕
  obtain ⟨α, hαm, hα1, hαI⟩ := GlobalTheory.T.exists_weight_bruhat_fundamental_domain_centralizer H Γ γ hc μ dt 𝓣 h𝓣
  have hL : ∀ G : H → ℝ≥0∞, Measurable G →
      ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ =
        dt 𝓣 * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂(quotMeas (cent γ) dt μ) := by
    intro G hG
    have hψ : Measurable fun y : H => G (y⁻¹ * γ * y) := hG.comp (by fun_prop)
    have hinv : LeftInv (cent γ) fun y : H => G (y⁻¹ * γ * y) := fun t ht y => by
      have : (t * y)⁻¹ * γ * (t * y) = y⁻¹ * (t⁻¹ * (γ * t)) * y := by group
      simp only [this, ← mem_cent.1 ht, inv_mul_cancel_left]
    have hF : ∀ g : Γ, AEMeasurable (fun x : H => α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)))
        (μ.restrict 𝓕) := fun g =>
      ((hαm.mul hψ).comp (measurable_const_mul (g : H))).aemeasurable
    calc ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ
        = ∫⁻ x in 𝓕, ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) ∂μ :=
          lintegral_congr fun x => GlobalTheory.T.tsum_subgroupConjugacyClass_eq_tsum_weighted H Γ γ hγ α hα1 G x
      _ = ∑' g : Γ, ∫⁻ x in 𝓕, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) ∂μ :=
          lintegral_tsum hF
      _ = ∫⁻ y, α y * G (y⁻¹ * γ * y) ∂μ :=
          (h𝓕.lintegral_eq_tsum'' (fun y => α y * G (y⁻¹ * γ * y))).symm
      _ = dt 𝓣 * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂(quotMeas (cent γ) dt μ) :=
          hαI _ hψ hinv
  exact _root_.GlobalTheory.ClassTerm.hasClassInt_of_lintegral_eq H Γ γ hγ μ 𝓕 (quotMeas (cent γ) dt μ) (dt 𝓣) hfin hL f c hf hfc hO.1 hO.2

end GlobalTheory.ClassUnfold
end
end

