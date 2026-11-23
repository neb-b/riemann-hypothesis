module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarDensityConjUnitaryHermitianGroups
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbability
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SubsingletonIdxZero
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0299

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelSchurOfFormalDegreeDensity
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FdegDens

theorem volUn_pos (j : ℕ) : 0 < volUn j := by
  unfold volUn
  refine Finset.prod_pos fun i _ => ?_
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  exact div_pos (pow_pos h2π _) (by exact_mod_cast Nat.factorial_pos i)

theorem exists_sort {n : ℕ} (ε : Fin n → Bool) : ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin n), p + q = n ∧
    (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false := by
  classical
  let A := {i : Fin n // ε i = true}
  let B := {i : Fin n // ¬ε i = true}
  let e : Fin (Fintype.card A) ⊕ Fin (Fintype.card B) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin A).symm (Fintype.equivFin B).symm).trans
      (Equiv.sumCompl fun i => ε i = true)
  refine ⟨Fintype.card A, Fintype.card B, e, ?_, fun i => ?_, fun j => ?_⟩
  · simpa using Fintype.card_congr e
  · exact ((Fintype.equivFin A).symm i).2
  · show ε (((Fintype.equivFin B).symm j : B) : Fin n) = false
    simpa using ((Fintype.equivFin B).symm j).2

theorem measurable_reindex {n p q : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n) :
    Measurable fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) := by
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  have hmat : Continuous (Formalism.BasicNotions.UpqT.mat : Formalism.BasicNotions.UpqT p q → _) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) :=
    hmat.matrix_reindex e e
  exact hc.measurable

theorem reindex_mem {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (g : Formalism.BasicNotions.UpqT p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
  obtain ⟨g0, hg0⟩ := g
  have hg : ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Formalism.UG.Jpq p q *
      (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hg0
  show (Matrix.reindex e e ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))ᴴ *
      Formalism.REAL.Jm ε * Matrix.reindex e e (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.REAL.Jm ε
  rw [GlobalTheory.OmegaFrobenius.jm_eq h1 h2, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem hasDens_unique {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c c' : ℝ≥0∞}
    (h : HasDens S μ c) (h' : HasDens S μ c') : c = c' := by
  unfold HasDens at h h'
  exact tendsto_nhds_unique h h'

theorem hasDens_smul {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c : ℝ≥0∞}
    (h : HasDens S μ c) (t : NNReal) : HasDens S (t • μ) (t * c) := by
  unfold HasDens at h ⊢
  refine (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top) (a := (t : ℝ≥0∞))).congr fun ρ => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem cd_dens {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n) (hpq : p + q = n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (cd : Formalism.BasicNotions.CDHaar) :
    PI.IsHaarOnM (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧
    HasDens (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)))
      (ENNReal.ofReal (volUn n)⁻¹) := by
  subst hpq
  obtain ⟨c0, -, -, hc1, hc2⟩ := cd.trick p q
  have hK := _root_.GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity (p + q) (fun _ => true) (p + q) 0 (Equiv.sumEmpty _ _) (fun _ => rfl)
    (fun j => j.elim0) (cd.cd (p + q) 0) c0 (cd.haar _ _) hc2
  have hJ : Formalism.REAL.Jm (fun _ : Fin (p + q) => true) = 1 := by
    unfold Formalism.REAL.Jm
    simp
  rw [hJ] at hK
  have hprob : ((cd.cd (p + q) 0).map fun g => Matrix.of.symm (Matrix.reindex
      (Equiv.sumEmpty (Fin (p + q)) (Fin 0)) (Equiv.sumEmpty (Fin (p + q)) (Fin 0))
      (Formalism.BasicNotions.UpqT.mat g))) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_reindex _) MeasurableSet.univ, Set.preimage_univ]
    haveI := cd.prob (p + q)
    exact measure_univ
  have hc0 : c0 = ENNReal.ofReal (volUn (p + q))⁻¹ :=
    hasDens_unique hK.2 (_root_.GlobalTheory.UnitaryVolume.hasDens_unitary (p + q) _ hK.1 hprob)
  have hM := _root_.GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity (p + q) ε p q e h1 h2 (cd.cd p q) c0 (cd.haar p q) hc1
  rw [hc0] at hM
  exact hM

theorem umat_emb {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n) := by
  have h : Topology.IsClosedEmbedding (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem conj_emb {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    MeasurableEmbedding fun x : PI.MtM n => (Matrix.of.symm (P⁻¹ * Matrix.of x * P) : PI.MtM n) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hm : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      Measurable fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) := by
    intro A B
    have hx : Continuous fun x : PI.MtM n => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) := continuous_id
    have hc : Continuous fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) :=
      (continuous_const.matrix_mul hx).matrix_mul continuous_const
    exact hc.measurable
  let φ : PI.MtM n ≃ PI.MtM n :=
    { toFun := fun x => Matrix.of.symm (P⁻¹ * Matrix.of x * P)
      invFun := fun y => Matrix.of.symm (P * Matrix.of y * P⁻¹)
      left_inv := fun x => by
        show Matrix.of.symm (P * (P⁻¹ * Matrix.of x * P) * P⁻¹) = x
        simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, ← Matrix.mul_assoc P P⁻¹,
          Matrix.mul_nonsing_inv_cancel_left _ _ hu]
      right_inv := fun y => by
        show Matrix.of.symm (P⁻¹ * (P * Matrix.of y * P⁻¹) * P) = y
        simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] }
  exact (MeasurableEquiv.mk φ (hm _ _) (hm _ _)).measurableEmbedding

theorem schur_of_dens : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (cd : Formalism.BasicNotions.CDHaar) (sc : NNReal) (P : Mat k r) (d c : ℝ) (μG : Measure (Mt k r)), (∀ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin (2 * r + k + 1)), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A → ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) A = cd.cd p q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) → IsCayley k r ε P → IsFdeg ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → 0 < c → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → SchurH μG σ (d / (c * volUn (2 * r + k + 1))) := by
  intro k r H _ _ _ σ ε cd sc P d c μG hcomp hP hF hc hμG hdG
  obtain ⟨p, q, e, hpq, h1, h2⟩ := exists_sort ε
  have hU := umat_emb ε
  have hC := conj_emb P hP.1

  have hν : ((sc : ℝ≥0∞) • Formalism.REAL.muG ε).map (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM (2 * r + k + 1))) =
      (cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
    ext B hB
    rw [Measure.map_apply hU.measurable hB, Measure.map_apply (measurable_reindex e) hB,
      hcomp p q e h1 h2 _ (hU.measurable hB)]
    congr 1
    ext g
    constructor
    · rintro ⟨a, ha, hag⟩
      show Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) ∈ B
      rw [← hag]
      exact ha
    · intro hg
      have hmem : Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) ∈ Set.range
          (fun a : Formalism.REAL.UJ ε => ((a : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
            Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
        rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).2]
        exact reindex_mem ε e h1 h2 g
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a, ?_, ha⟩
      show Matrix.of.symm (umat a) ∈ B
      rw [show umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) from ha]
      exact hg
  have hcd := cd_dens ε e hpq h1 h2 cd
  rw [← hν] at hcd
  have hHk := Formalism.QuantumDeterminants.hpkFacts k r
  have hD := _root_.GlobalTheory.AdDens.haar_dens_conj (2 * r + k + 1) (Formalism.QuantumDeterminants.Hpk k r) (Formalism.REAL.Jm ε) P hHk.1 hHk.2.1
    (Formalism.REAL.Jm_conjTranspose ε) (Formalism.REAL.Jm_mul_self ε) hP.1 hP.2 _ _ hcd.1 hcd.2
  obtain ⟨t, -, httop, hμt⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _
    (GlobalTheory.AdDens.isMatGroup_UH _ hHk.2.1) hD.1).1 μG hμG
  have hdt : HasDens (GG k r) μG (t * ENNReal.ofReal (volUn (2 * r + k + 1))⁻¹) := by
    have h := hasDens_smul hD.2 t.toNNReal
    rwa [ENNReal.smul_def, ENNReal.coe_toNNReal httop.ne, ← hμt] at h
  have hV := volUn_pos (2 * r + k + 1)
  have htr : t.toReal = c * volUn (2 * r + k + 1) := by
    have h := congrArg ENNReal.toReal (hasDens_unique hdG hdt)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal (inv_nonneg.mpr hV.le)] at h
    rw [h, mul_assoc, inv_mul_cancel₀ hV.ne', mul_one]
  rw [Measure.map_map hC.measurable hU.measurable] at hμt
  have hemb := hC.comp hU
  obtain ⟨hd, hFd⟩ := hF
  refine ⟨div_pos hd (mul_pos hc hV), fun v w v' w' => ?_⟩
  obtain ⟨hI, hE⟩ := hFd v w v' w'
  rw [hμt]
  refine ⟨Integrable.smul_measure ?_ httop.ne, ?_⟩
  · rw [hemb.integrable_map_iff]
    exact hI
  rw [integral_smul_measure, hemb.integral_map]
  refine (congrArg (fun z : ℂ => t.toReal • z) hE).trans ?_
  rw [htr, Complex.real_smul]
  push_cast
  rw [div_div_eq_mul_div]
  ring

end GlobalTheory.FdegDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOneOfUniq
section
open GlobalTheory.Mom

namespace GlobalTheory.BesselMultOne

theorem psi_eq_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) := by
  funext g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    PI.UpqRep.dsigW (k := k) (r := r) σ w v = Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons X w ih => simp only [PI.UpqRep.dsigW, Formalism.MainNotions.S.dsigW, ih]; rfl

theorem isBesselMapSm_of {k r : ℕ} {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {z : Fin (2 * r + k + 1) → ℂ}
    {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (W →L[ℂ] W)} {B : H → W}
    (h : Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simp only [dsigW_eq]
  exact h5 v hv

end GlobalTheory.BesselMultOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClsOmNonneg
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {X : HidaSetting D}

def frCls {Y : Full X} {u : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) :
    Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) :=
  {G | GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) G}

def clsOm (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : ℝ :=
  if h : ∃ t : GTu Y u, t.lam = Λ ∧ frCls Λ t = b then omT h.choose else 0

theorem frCls_eq_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t t' : GTu Y u) :
    frCls Λ t = frCls Λ t' ↔ GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) (Ft t') := by
  have hE := (GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).1
  constructor
  · intro h
    have : Ft t' ∈ frCls Λ t := by rw [h]; exact hE.refl _
    exact this
  · intro h
    ext G
    exact ⟨fun hG => hE.trans (hE.symm h) hG, fun hG => hE.trans h hG⟩

theorem clsOm_nonneg (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : 0 ≤ clsOm Y u Λ b := by
  unfold clsOm
  split_ifs with h
  · exact ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
  · exact le_rfl

theorem clsOm_frCls (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) (ht : t.lam = Λ) : clsOm Y u Λ (frCls Λ t) = omT t := by
  have hex : ∃ s : GTu Y u, s.lam = Λ ∧ frCls Λ s = frCls Λ t := ⟨t, ht, rfl⟩
  unfold clsOm
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have hq := (frCls_eq_iff hK Λ _ _).1 h2
  have := ((GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).2 _ _ hq).1
  unfold omT
  rw [h1, ht]
  exact this
end

end GlobalTheory.TypeAsm.PerRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousConv
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ConvContRep

theorem continuous_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [FirstCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) (ψ f : G → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hf : AEStronglyMeasurable f μ) (hi : ∀ C, IsCompact C → IntegrableOn f C μ) :
    Continuous fun x => ∫ z, ψ (x⁻¹ * z) * f z ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hc
  set L : Set G := (fun p : G × G => p.1 * p.2) '' (K ×ˢ tsupport ψ) with hLdef
  have hL : IsCompact L := (hK.prod hc.isCompact).image continuous_mul
  refine continuousAt_of_dominated
    (bound := fun z => C * L.indicator (fun z => ‖f z‖) z) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hψ.comp (continuous_const_mul x⁻¹)).aestronglyMeasurable).mul hf
  · filter_upwards [hKx] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · have h0 : ψ (x⁻¹ * z) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hm => hz ?_
        exact ⟨(x, x⁻¹ * z), ⟨hx, hm⟩, mul_inv_cancel_left x z⟩
      simp [h0, Set.indicator_of_notMem hz]
  · exact (IntegrableOn.integrable_indicator (hi _ hL).norm hL.isClosed.measurableSet).const_mul C
  · refine Filter.Eventually.of_forall fun z => ?_
    have hz : Continuous fun x : G => ψ (x⁻¹ * z) * f z := by fun_prop
    exact hz.continuousAt

theorem conv_isContRep : ∀ (B : RowsAut) (ψ : B.I.GA → ℂ) (F : B.I.L2 B.μf B.fund), Continuous ψ → HasCompactSupport ψ → IsContRep B (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf)) (fun x => ∫ z, ψ (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) := by
  intro B ψ F hψ hc
  obtain ⟨iT2, iLC, iSC, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have iK : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  obtain ⟨hl, -, -, -, -⟩ := _root_.GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  have iL : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  obtain ⟨-, -, hiso, hcontR, hext⟩ := _root_.GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨hEinv, hEm⟩ := hext F
  unfold IsContRep
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_conv _ ψ _ hψ hc hEm fun C hC => ((_root_.GlobalTheory.LocalL2Isometry.ext_integrableOn B C hC).choose_spec F).1
  · intro γ hγ x
    calc ∫ z, ψ ((γ * x)⁻¹ * z) * B.I.ext F z ∂B.I.muA B.μf
        = ∫ w, ψ ((γ * x)⁻¹ * (γ * w)) * B.I.ext F (γ * w) ∂B.I.muA B.μf :=
          (integral_mul_left_eq_self (fun z => ψ ((γ * x)⁻¹ * z) * B.I.ext F z) γ).symm
      _ = ∫ w, ψ (x⁻¹ * w) * B.I.ext F w ∂B.I.muA B.μf := by
          refine integral_congr_ae ?_
          filter_upwards [hEinv] with w hw
          rw [hw γ hγ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · have hint : Integrable (fun y => ψ y • B.R y F) (B.I.muA B.μf) :=
      (hψ.smul (hcontR F)).integrable_of_hasCompactSupport hc.smul_right
    have hK : AEStronglyMeasurable (fun p : B.I.GA × B.I.GA => B.I.ext F (p.1 * p.2))
        (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) :=
      hEm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_mul ((B.I.muA B.μf).restrict B.fund) (B.I.muA B.μf))
    have hw := (GlobalTheory.ConvKernel.weak_integral_ae_eq (fun x g => B.I.ext F (x * g)) hK
      (fun g => B.R g F) (fun g => B.R_spec g F) ‖F‖ (fun g => (hiso g F).le) ψ
      (hψ.integrable_of_hasCompactSupport hc) (∫ y, ψ y • B.R y F ∂B.I.muA B.μf)
      (fun u => by rw [← integral_inner (𝕜 := ℂ) hint u]; simp only [inner_smul_right])).2
    filter_upwards [hw] with x hx
    refine hx.trans ?_
    rw [← integral_mul_left_eq_self (fun z => ψ (x⁻¹ * z) * B.I.ext F z) x]
    simp only [inv_mul_cancel_left]

end GlobalTheory.ConvContRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPartStatement
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V) (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W), (∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X) → ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  first | exact @GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | exact GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | (intros; apply GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdmissibleIntegralFrameOfLocalTerms
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AdmFrame

theorem frame_mem_locP (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : IsLift Λ (lf D F0)) (hF : FrameOK D Λ (lf D F0))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frame (lf D F0) a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction a using Fin.lastCases with
  | last =>
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    simp only [one_smul, frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
    exact hL.1
  | cast i =>
    obtain ⟨c, -, hc1, hc⟩ := hF.1.1 P
    have hci : c i = 1 := hc1 hP i
    have hmem : (lf D F0).fl.e i ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F0)) := by
      rw [hc]
      refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
      rw [one_smul]
      have : (lf D F0).fl.e i = c i • (lf D F0).fl.e i := by rw [hci, one_smul]
      rw [this]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := hmem
    refine ⟨s, hs, ?_⟩
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    exact (inf_le_left : XLam Λ (lf D F0) ≤ Λ) hx

theorem lift_transport (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂) {T : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (hL : IsLift Λ₁ F) : IsLift Λ₂ (mapLF γ F) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  refine ⟨?_, ?_⟩
  · rw [← h]
    exact ⟨F.fl.z, hL.1, rfl⟩
  · show γ F.zt = γ F.fl.z
    rw [hL.2]

theorem exists_admissible_integralFrame_of_localTerms_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  have hγ : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hrow' : IsRowLat D (X.Fu u') t₀.lam' := (Y.rowsOK u').1 _ t₀.mem'
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  have hpd' := Formalism.L2.SG.TermDef.pd_self (X.Fu u') t₀.lam' hrow'
  have hpd := Formalism.L2.SG.TermDef.pd_self (X.Fu u) t₀.lam hrow
  refine ⟨lift_transport D _ hγ _ _ hlam _ hpd'.1, ?_, _root_.GlobalTheory.FrameIsom.frameOK_mapLF D _ hγ _ _ hlam _ _ hpd'.2.2⟩
  have hloc := GlobalTheory.T.movedReferenceFrame_congruent_unitriangular D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  obtain ⟨ξ, h1, h2, h3⟩ := GlobalTheory.T.glue_frame_congruences_unitriangular_integral (VS D) D.R.rS t₀.lam (gS D) (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
    (frame (lf D (X.Fu u))) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))))
    (fun P hP a => frame_mem_locP D (X.Fu u) t₀.lam hpd.1 hpd.2.2 P hP a) hloc
  exact ⟨ξ, h1, h2, h3⟩

end GlobalTheory.HL.AdmFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub {g | uMat g - 1 ∈ A} d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ (∀ μ', IsGaugeSub {g | uMat g - 1 ∈ A} d μ' → μ' = μ) ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ r₀ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | Formalism.REAL.hs (uMat g - 1) < r₁}, φ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re / r) ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t, φ t)) := by
  first | exact @GlobalTheory.GaugeSubLoc.gauge_local_asymptotics | exact GlobalTheory.GaugeSubLoc.gauge_local_asymptotics | (intros; apply GlobalTheory.GaugeSubLoc.gauge_local_asymptotics <;> assumption)
end

