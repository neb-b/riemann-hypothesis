module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeAction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpan
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.PendClose

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) →
    SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D →
    SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  intro D M hT hR hA hPar h0 h5 hIne hDep hGen hZL hCI hCT hSer hZeta hDZ hAdm
  have hSU : GlobalTheory.EtaJoin.SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hSec : ∀ i, Nonempty (Sec D i) := fun i =>
    _root_.GlobalTheory.PendOf.SecProof.main D M i hT hR hA hSU (_root_.GlobalTheory.HeckeScalarAll.heckeScalar_all D M hT hA i)
  obtain ⟨lz, hlz⟩ := _root_.GlobalTheory.LzExist.exists_lz_serEq D
  obtain ⟨Ω, hΩ⟩ := _root_.GlobalTheory.PendOf.LabIneAll.main D hIne hDep hGen
  have hChar : LabChar D := _root_.main D h0 hIne hDep hGen
  obtain ⟨Z⟩ := _root_.GlobalTheory.CenOAct.cenO_nonempty D hSec hZL hCI hCT
  have hPr : PrType D := _root_.GlobalTheory.PendOf.PrTypeProof.main D hSec
  have hSplit : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v) := fun k v =>
    _root_.GlobalTheory.TypeSplit.main D k _ (D.naut.plGw_over k v)
  have hPS : ParSurj D := _root_.GlobalTheory.ParOfPoint.main D hPar h0 h5 hSplit hDep hDZ
  let P : PairedCharacterCondition.Pend D := mk lz hlz hSer hZeta Ω hΩ hChar Z hZL hPr hPS
  exact ⟨P, GlobalTheory.T.depthZeroAdmissible_all_pending_data D P hAdm, _root_.GlobalTheory.PendOf.EigSpanProof.main D P hSec hCT⟩

end GlobalTheory.PendClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.SplitStabFrame

open GlobalTheory.StdFrames GlobalTheory.IdemSupport GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

variable {D : D7}


set_option maxHeartbeats 400000 in
theorem cpt_sg_mem {Q : Pl D.host.E} {z : Ef D}
    (hz : cpt Q z ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    cpt (cP Q) (sg D z) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) := by
  obtain ⟨e, -, -, h1, h0⟩ := exists_idem (D := D) {Q}
  have hQ1 : cpt Q e = 1 := h1 Q (Set.mem_singleton Q)
  have hez : e * z ∈ OA D := by
    refine (mem_OA_iff _).2 fun R => ?_
    rw [map_mul]
    by_cases hR : R = Q
    · rw [hR, hQ1, one_mul]; exact hz
    · rw [h0 R (Set.notMem_singleton_iff.2 hR), zero_mul]; exact zero_mem _
  have h2 : cpt (cP Q) (sg D (e * z)) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
    (mem_OA_iff (sg D (e * z))).1 (GlobalTheory.LevSplit.sigR_int hez) (cP Q)
  have h3 : cpt (cP Q) (sg D (1 - e)) = 0 :=
    cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, hQ1, sub_self])
  have h4 : cpt (cP Q) (sg D e) = 1 := by
    rw [map_sub, map_one, map_sub, map_one, sub_eq_zero] at h3
    exact h3.symm
  rw [map_mul, map_mul, h4, one_mul] at h2
  exact h2

theorem int_mul {Q : Pl D.host.E} {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Ef D)}
    (hA : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hB : ∀ i j, cpt Q (B i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt Q ((A * B) i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  intro i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun l _ => by rw [map_mul]; exact mul_mem (hA i l) (hB l j)

theorem int_of_OA {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)} (h : ∀ i j, A i j ∈ OA D) :
    ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q :=
  fun i j => (mem_OA_iff _).1 (h i j) Q

theorem int_cT {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)}
    (h : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt (cP Q) (Formalism.UG.cT (sg D) A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
  fun i j => cpt_sg_mem (h j i)

theorem inv_eq_of_unitary {n : ℕ} {J U' : Matrix (Fin n) (Fin n) (Ef D)} (hU : U' * J = 1) (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) : (Y⁻¹).val = U' * Formalism.UG.cT (sg D) Y.val * J := by
  have h1 : U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val) = 1 := by rw [hY, hU]
  calc (Y⁻¹).val = (U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val)) * (Y⁻¹).val := by rw [h1, Matrix.one_mul]
    _ = U' * Formalism.UG.cT (sg D) Y.val * J * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, Matrix.mul_one]

theorem unitary_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) (Ef D)} (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) :
    Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val = J := by
  calc Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val
        = Formalism.UG.cT (sg D) (Y⁻¹).val * (Formalism.UG.cT (sg D) Y.val * J * Y.val) * (Y⁻¹).val := by rw [hY]
    _ = Formalism.UG.cT (sg D) (Y.val * (Y⁻¹).val) * J * (Y.val * (Y⁻¹).val) := by
        rw [cT_mul']; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, cT_one', Matrix.one_mul, Matrix.mul_one]

theorem inv_int_at {Q : Pl D.host.E} {n : ℕ} (X : GL (Fin n) (Ef D))
    (hint : ∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hdet : Valued.v (cpt Q X.val.det) = 1) :
    ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  set A := (cpt Q).mapMatrix X.val with hAdef
  have hBA : (cpt Q).mapMatrix (X⁻¹).val * A = 1 := by rw [hAdef, ← map_mul, Units.inv_mul, map_one]
  have hB : (cpt Q).mapMatrix (X⁻¹).val = A⁻¹ := (Matrix.inv_eq_left_inv hBA).symm
  let A' : Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :=
    fun i j => ⟨A i j, hint i j⟩
  have hA' : (HeightOneSpectrum.adicCompletionIntegers D.host.E Q).subtype.mapMatrix A' = A := rfl
  have hdetA : A.det = cpt Q X.val.det := (RingHom.map_det _ _).symm
  intro i j
  have e : cpt Q ((X⁻¹).val i j) = ((cpt Q).mapMatrix (X⁻¹).val) i j := rfl
  rw [e, hB, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem ?_ ?_
  · rw [hdetA, Ring.inverse_eq_inv', HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hdet, inv_one]
  · rw [← hA', ← RingHom.map_adjugate]
    exact (A'.adjugate i j).2

theorem int_of_split {n : ℕ} (J U' : Matrix (Fin n) (Fin n) (Ef D)) (hJ : ∀ i j, J i j ∈ OA D)
    (hU' : ∀ i j, U' i j ∈ OA D) (hUJ : U' * J = 1) (X : GL (Fin n) (Ef D))
    (hX : Formalism.UG.cT (sg D) X.val * J * X.val = J) (P : Pl D.host.E)
    (hint : ∀ i j, cpt P (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P)
    (hdet : Valued.v (cpt P X.val.det) = 1)
    (hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1) :
    (∀ i j, X.val i j ∈ OA D) ∧ ∀ i j, (X⁻¹).val i j ∈ OA D := by
  have hXi := unitary_inv X hX
  have intPi := inv_int_at X hint hdet
  have key : ∀ Y : GL (Fin n) (Ef D), Formalism.UG.cT (sg D) Y.val * J * Y.val = J →
      (∀ i j, cpt P (Y.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P) →
      ∀ i j, cpt (cP P) ((Y⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP P) := by
    intro Y hY hYP
    rw [inv_eq_of_unitary hUJ Y hY]
    exact int_mul (int_mul (int_of_OA hU') (int_cT hYP)) (int_of_OA hJ)
  have hall : ∀ Q : Pl D.host.E,
      (∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) ∧
        ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
    intro Q
    by_cases h1 : Q = P
    · rw [h1]; exact ⟨hint, intPi⟩
    by_cases h2 : Q = cP P
    · rw [h2]
      refine ⟨?_, key X hX hint⟩
      have := key X⁻¹ hXi intPi
      rwa [inv_inv] at this
    · have h3 := hoff Q h1 h2
      have h4 : (cpt Q).mapMatrix (X⁻¹).val = 1 :=
        calc (cpt Q).mapMatrix (X⁻¹).val = (cpt Q).mapMatrix (X⁻¹).val * (cpt Q).mapMatrix X.val := by
              rw [h3, Matrix.mul_one]
          _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      have one_int : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E)) i j ∈
          HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
        intro i j
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have : cpt Q (X.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h3 i) j
        rw [this]; exact one_int i j
      · have : cpt Q ((X⁻¹).val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h4 i) j
        rw [this]; exact one_int i j
  exact ⟨fun i j => (mem_OA_iff _).2 fun Q => (hall Q).1 i j,
    fun i j => (mem_OA_iff _).2 fun Q => (hall Q).2 i j⟩


set_option maxHeartbeats 800000 in
theorem finE_mem_St_of_split : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  intro D W β Λ hSD e f P hP hf _ k hS hint hdet
  obtain ⟨hJ, U', hU', hUJ⟩ := unimod_of_isSD hSD
  have hg : Formalism.UG.cT (sg D) (finE W k).val * ratM W.gram * (finE W k).val = ratM W.gram :=
    GlobalTheory.LevSplit.finE_mem_UA W k
  set g := finE W k with hgdef
  let X : GL (Fin W.rank) (Ef D) := β⁻¹ * g * β
  have hXv : X.val = (β⁻¹).val * g.val * β.val := rfl
  have hX : Formalism.UG.cT (sg D) X.val * gramOf W β * X.val = gramOf W β := by
    have e2 : Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val = 1 := by
      rw [← cT_mul', Units.mul_inv, cT_one']
    have e3 : β.val * (β⁻¹).val = 1 := Units.mul_inv β
    show Formalism.UG.cT (sg D) X.val * (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * X.val =
      Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val
    rw [hXv, cT_mul', cT_mul']
    calc Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * Formalism.UG.cT (sg D) (β⁻¹).val) *
          (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * ((β⁻¹).val * g.val * β.val)
        = Formalism.UG.cT (sg D) β.val * Formalism.UG.cT (sg D) g.val *
          (Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val) * ratM W.gram * (β.val * (β⁻¹).val) *
          g.val * β.val := by simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * ratM W.gram * g.val) * β.val := by
          rw [e2, e3]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hg]
  have hf0 : ∀ Q, Q ≠ P → Q ≠ cP P → cpt Q (toEAf D f) = 0 := by
    intro Q h1 h2
    have h3 : cP Q ≠ P := fun h => h2 (by rw [← h, cP_cP])
    rw [hf, RingHom.map_add (toEAf D), toEAf_cA, RingHom.map_add (cpt Q), (cpt_of_isIdemAt hP).2 Q h1,
      cpt_sg_eq_zero ((cpt_of_isIdemAt hP).2 _ h3), add_zero]
  have hM : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix g.val = 1 := by
    intro Q h1 h2
    refine Matrix.ext fun i j => ?_
    have h3 := congrArg (fun z => cpt Q (toEAf D z)) (hS i j)
    rw [RingHom.map_mul (toEAf D), RingHom.map_mul (cpt Q), hf0 Q h1 h2, zero_mul, Matrix.sub_apply,
      RingHom.map_sub (toEAf D), RingHom.map_sub (cpt Q)] at h3
    rw [eq_comm, sub_eq_zero] at h3
    change cpt Q (toEAf D (Formalism.L2.Theta.mt W k i j)) = (1 : Matrix (Fin W.rank) (Fin W.rank) _) i j
    rw [h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1 := by
    intro Q h1 h2
    rw [hXv, map_mul, map_mul, hM Q h1 h2, Matrix.mul_one, ← map_mul, Units.inv_mul, map_one]
  obtain ⟨h1, h2⟩ := int_of_split (gramOf W β) U' hJ hU' hUJ X hX P hint hdet hoff
  let Mi : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h1 i j⟩
  let Mi' : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h2 i j⟩
  have inj : Function.Injective ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix (m := Fin W.rank)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p1 : Mi * Mi' = 1 := inj (by rw [map_mul, map_one]; exact Units.mul_inv X)
  have p2 : Mi' * Mi = 1 := inj (by rw [map_mul, map_one]; exact Units.inv_mul X)
  refine ⟨⟨Mi, Mi', p1, p2⟩, ?_⟩
  have hX' : intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ = X := Units.ext rfl
  show β * intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ * β⁻¹ = g
  rw [hX']
  show β * (β⁻¹ * g * β) * β⁻¹ = g
  rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul]

end GlobalTheory.SplitStabFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LocDisj

theorem map_cA_smul_of_fix (D : D7) {m n : ℕ} (f : AE D) (hf : cA D f = f) (X : Matrix (Fin m) (Fin n) (AE D)) :
    (f • X).map (cA D) = f • X.map (cA D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hf]

theorem map_toEAf_smul (D : D7) {m n : ℕ} (f : AE D) (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (f • Y).map (toEAf D) = toEAf D f • Y.map (toEAf D) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem frMapAdj_smul_of_fix (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (x : WO V W) :
    frMapAdj V W βV βW (f • x) = toEAf D f • frMapAdj V W βV βW x := by
  unfold frMapAdj
  have h3 : (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((f • (x : Matrix (Fin W.rank) (Fin V.rank) (AE D))).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D))
      = f • (HMul.hMul (HMul.hMul ((V.gram⁻¹).map (incA D)) ((x : Matrix (Fin W.rank) (Fin V.rank) (AE D)).map (cA D)).transpose) (W.gram.map (incA D)) : Matrix (Fin V.rank) (Fin W.rank) (AE D)) := by
    rw [map_cA_smul_of_fix D f hf, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [h3, map_toEAf_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_smul_eq {n : ℕ} {R : Type} [CommRing R] (c : R) (β : GL (Fin n) R) (M : Matrix (Fin n) (Fin n) R)
    (h0 : ∀ i j, c * (M - 1) i j = 0) :
    c • (β⁻¹.val * M * β.val) = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hM : c • M = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← sub_eq_zero, ← smul_sub]
    ext i j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using h0 i j
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul]

theorem split_mul {m n : ℕ} {R : Type} [CommRing R] (c : R) (A A' : Matrix (Fin m) (Fin n) R) (K : Matrix (Fin n) (Fin n) R)
    (hx : c • A = c • A') (hK : (1 - c) • K = (1 - c) • (1 : Matrix (Fin n) (Fin n) R)) :
    A' * K = c • (A * K) + (1 - c) • A' := by
  calc A' * K = (c + (1 - c)) • (A' * K) := by rw [add_sub_cancel, one_smul]
    _ = (c • A') * K + A' * ((1 - c) • K) := by rw [add_smul, Matrix.smul_mul, Matrix.mul_smul]
    _ = (c • A) * K + A' * ((1 - c) • (1 : Matrix (Fin n) (Fin n) R)) := by rw [hx, hK]
    _ = c • (A * K) + (1 - c) • A' := by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]

theorem suppF_entry (D : D7) (W : HSp D) (f : AE D) (k : GA D W) (hk : SuppF W f k) (i j : Fin W.rank) :
    (1 - toEAf D f) * ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = 0 := by
  have e : ((Formalism.L2.Theta.mt W k).map (toEAf D) - 1) i j = toEAf D ((Formalism.L2.Theta.mt W k - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_one (toEAf D), ← map_sub, ← map_mul, sub_mul, one_mul, hk i j, sub_self, map_zero]

end GlobalTheory.LocDisj

namespace GlobalTheory.LocDisj

theorem frMapAdj_mul_frame_eq (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (hf : cA D f = f) (k : GA D W) (hk : SuppF W f k) (x x' : WO V W) (hxx : ∀ a b, f * x a b = f * x' a b) :
  (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  have hfx : f • x = f • x' := by
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hxx a b
  have hx : toEAf D f • frMapAdj V W βV βW x = toEAf D f • frMapAdj V W βV βW x' := by
    rw [← frMapAdj_smul_of_fix D V W βV βW f hf, ← frMapAdj_smul_of_fix D V W βV βW f hf, hfx]
  exact split_mul (toEAf D f) _ _ _ hx (conj_smul_eq _ βW _ (suppF_entry D W f k hk))

end GlobalTheory.LocDisj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.TranslateAdj

theorem frameAdjoint_translate_mul_frameConj_algebra {R S : Type} [CommRing R] [CommRing S] (σ : R →+* R) (f : R →+* S) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (G K K' : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin n) (Fin m) R) (βV : GL (Fin m) S) (βW : GL (Fin n) S)
    (hkey : (K'.map σ)ᵀ * G = G * K) (hP : P = 1) :
    (βV⁻¹).val * ((A * ((K' * x * P).map σ)ᵀ * G).map f) * βW.val =
      ((βV⁻¹).val * ((A * (x.map σ)ᵀ * G).map f) * βW.val) * ((βW⁻¹).val * K.map f * βW.val) := by
  subst hP
  have hβ : βW.val * (βW⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : A * ((K' * x * (1 : Matrix (Fin m) (Fin m) R)).map σ)ᵀ * G = A * (x.map σ)ᵀ * G * K := by
    rw [Matrix.mul_one, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc A, Matrix.mul_assoc, hkey]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βW.val, hβ, Matrix.one_mul]

theorem frMapAdj_actO_inv : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (x : WO V W), frMapAdj V W βV βW (actO V W 1 k⁻¹ x) = (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) := by
  intro D V W βV βW k x
  have hU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt W k⁻¹) * W.gram.map (incA D) * Formalism.L2.Theta.mt W k⁻¹ =
      W.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig W.gram from k⁻¹).2
  have hi : Formalism.L2.Theta.mt W k⁻¹ * Formalism.L2.Theta.mt W k = 1 := by
    show Formalism.L2.Theta.mt W (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hkey : ((Formalism.L2.Theta.mt W k⁻¹).map (cA D)).transpose * W.gram.map (incA D) =
      W.gram.map (incA D) * Formalism.L2.Theta.mt W k := by
    calc _ = Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt W k⁻¹) * W.gram.map (incA D) *
          (Formalism.L2.Theta.mt W k⁻¹ * Formalism.L2.Theta.mt W k) := by rw [hi, Matrix.mul_one]; rfl
      _ = _ := by rw [← Matrix.mul_assoc, hU]
  have hmt1 : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by rw [inv_one]; rfl
  exact frameAdjoint_translate_mul_frameConj_algebra (cA D) (toEAf D) ((V.gram⁻¹).map (incA D)) (W.gram.map (incA D)) (Formalism.L2.Theta.mt W k)
    (Formalism.L2.Theta.mt W k⁻¹) (Formalism.L2.Theta.mt V (1 : GA D V)⁻¹) x βV βW hkey hmt1

end GlobalTheory.TranslateAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixComponentSubOneEqZeroOffIdempotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.FrameOff

theorem cpt_frame_sub_one_eq_zero_of_suppF : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  intro D W β f k PP hS hf a b
  set M := Formalism.L2.Theta.mt W k with hMdef
  have hmap : M.map (toEAf D) - 1 = (M - 1).map (toEAf D) := by
    rw [Matrix.map_sub (toEAf D) (fun x y => (toEAf D).map_sub x y),
      Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one]
  have hM : ((M - 1).map (toEAf D)).map (GlobalTheory.StdFrames.cpt PP) = 0 := by
    refine Matrix.ext fun i j => ?_
    change GlobalTheory.StdFrames.cpt PP (toEAf D ((M - 1) i j)) = 0
    rw [← hS i j, RingHom.map_mul, RingHom.map_mul, hf, zero_mul]
  have hk : (HMul.hMul (HMul.hMul ((β)⁻¹).val (M.map (toEAf D))) (β).val :
        Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1
      = ((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [hk]
  change ((((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val).map (GlobalTheory.StdFrames.cpt PP)) a b = 0
  rw [Matrix.map_mul, Matrix.map_mul, hmap, hM, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end GlobalTheory.FrameOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsData_transport_localFieldIso : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (l : List (Segment k)) (l' : List (Segment k')) (x : IrrGL (k := k)) (x' : IrrGL (k := k')), List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) l l' → RepRel i x x' → IsL (l : Multiset (Segment k)) x.rep → IsL (l' : Multiset (Segment k')) x'.rep := by
  first | exact @GlobalTheory.LocLanglands.isL_transport | exact GlobalTheory.LocLanglands.isL_transport | (intros; apply GlobalTheory.LocLanglands.isL_transport <;> assumption)
end

