module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigLocalSum

open GlobalTheory.PRep

theorem exists_eigen_family {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθU : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b)
    (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hinv : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ u : ι → V, (∀ j, ∀ h ∈ K, ρ h (u j) = θ h • u j) ∧ ∑ i, T i (u i) = ∑ i, T i (y i) := by
  first
  | exact @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family
  | (apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenFamilyStabilizer.exists_eigen_family ..)


set_option maxHeartbeats 1000000 in
theorem exists_eigen_local_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  intro L _ _ _ n a S hS s σ hloc c hc hci K θ U hK hKOne hU hU1 hθU f hf hθ ι _ xs z hxs hz
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hz
    simp
  have hrt : ∀ h ∈ K, ∃ x : GAf L n, TrivOutside {s.v} x ∧
      Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h ∧ NG.rt L n x f = θ h • f := by
    intro h hh
    obtain ⟨x, hx, e⟩ := GlobalTheory.EigLocal.exists_trivOutside_map_loc n s c h
    exact ⟨x, hx, e, by rw [hθ x hx (e ▸ hh), e]⟩
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, θ (k * k') = θ k * θ k' := by
    intro k hk k' hk'
    obtain ⟨x, hx, e, hfx⟩ := hrt k hk
    obtain ⟨x', hx', e', hfx'⟩ := hrt k' hk'
    have hxx : TrivOutside {s.v} (x * x') := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hx'
    have e2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (x * x')) = k * k' := by
      rw [map_mul, map_mul, e, e']
    have h2 := hθ (x * x') hxx (e2 ▸ mul_mem hk hk')
    rw [e2] at h2
    have h3 : NG.rt L n (x * x') f = NG.rt L n x (NG.rt L n x' f) := by
      funext g; simp [NG.rt, mul_assoc]
    rw [h3, hfx', map_smul, hfx, smul_smul] at h2
    have h4 : (θ (k * k') - θ k' * θ k) • f = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · rw [sub_eq_zero.1 h5, mul_comm]
    · exact absurd h5 hf0
  have hmem := _root_.GlobalTheory.SpanLoc.main L n a S hS s σ hloc c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨F, hF, hFsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose y hy using fun i => LinearMap.mem_range.1 (hF i)
  have hsum : ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y j.1) = f := by
    rw [← hFsum, Finsupp.sum, ← Finset.sum_attach F.support]
    exact Finset.sum_congr rfl fun j _ => hy j.1
  have hKo : IsOpen (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    Subgroup.isOpen_mono hKOne GlobalTheory.StepData.isOpen_KOne
  have hKc : IsCompact (K : Set (GL (Fin n) (s.w.adicCompletion L))) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) hK
  have hint : ∀ (j : F.support) (x : GAf L n), TrivOutside {s.v} x → ∀ v,
      (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
        (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) =
      NG.rt L n x ((j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W)) v) := fun j x hx v => j.1.2.2 x hx v
  obtain ⟨u, hu, hus⟩ := exists_eigen_family σ.smooth hKc hU hU1 θ hθU hmul
    (fun j : F.support => (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))) (fun j => y j.1) (by
      intro k hk
      obtain ⟨x, hx, e, hfx⟩ := hrt k hk
      subst e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun j _ => hint j x hx (y j.1), ← map_sum, hsum, hfx])
  rw [hsum] at hus
  by_contra hall
  push_neg at hall
  apply hz
  have key : ∀ j, ∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j) = 0 := by
    intro j
    by_contra hne
    exact hne (hall (u j) (hu j))
  calc ∑ m, z m • NG.rt L n (xs m) f
      = ∑ m, z m • ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hus, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (hint j (xs m) (hxs m) (u j)).symm
    _ = ∑ j : F.support, (j.1.1 : σ.V →ₗ[ℂ] (GAf L n → a.W))
          (∑ m, z m • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs m))) (u j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Finset.smul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [key j, map_zero]

end GlobalTheory.EigLocalSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFrameChangeMemIntegralGLAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.LocCore

theorem adj_det_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, v (A i j) ≤ 1) :
    (∀ i j, v (A.adjugate i j) ≤ 1) ∧ v A.det ≤ 1 := by
  let A' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨A i j, hA i j⟩
  have hA' : A'.map v.integer.subtype = A := by ext i j; rfl
  constructor
  · intro i j
    have h := RingHom.map_adjugate v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.adjugate i j).2
  · have h := RingHom.map_det v.integer.subtype A'
    simp only [RingHom.mapMatrix_apply, hA'] at h
    rw [← h]
    exact (A'.det).2

theorem solve_integral {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} (A B κ : Matrix (Fin n) (Fin n) K) (hAB : A * κ = B)
    (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hdA : v A.det = 1) (hdB : v B.det = 1) :
    (∀ a b, v (κ a b) ≤ 1) ∧ v κ.det = 1 ∧
      ((∀ i j, v ((A - 1) i j) < 1) → (∀ i j, v ((B - 1) i j) < 1) →
        ∀ a b, v ((κ - 1) a b) < 1) := by
  obtain ⟨hadj, -⟩ := adj_det_integral v A hA
  have key : A.det • κ = A.adjugate * B := by
    rw [← hAB, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have key' : A.det • (κ - 1) = A.adjugate * (B - A) := by
    rw [smul_sub, key, Matrix.mul_sub, Matrix.adjugate_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have h := congrFun (congrFun key a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hadj a k) (hB k b)
  · have h := congrArg v (congrArg Matrix.det hAB)
    rw [Matrix.det_mul, map_mul, hdA, one_mul, hdB] at h
    exact h
  · intro hA1 hB1 a b
    have h := congrFun (congrFun key' a) b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
    have h2 := congrArg v h
    rw [map_mul, hdA, one_mul] at h2
    rw [h2]
    apply v.map_sum_lt one_ne_zero
    intro k _
    rw [map_mul]
    have hBA : (B - A) k b = (B - 1) k b - (A - 1) k b := by
      simp only [Matrix.sub_apply, sub_sub_sub_cancel_right]
    have hlt : v ((B - A) k b) < 1 := by
      rw [hBA]; exact lt_of_le_of_lt (v.map_sub _ _) (max_lt (hB1 k b) (hA1 k b))
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hadj a k)) hlt

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

noncomputable def topAt {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) :
    Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion D.host.E P) :=
  fun i j => GlobalTheory.StdFrames.cpt P (U (Fin.castLE hmn i) j)

theorem topAt_facts {D : D7} (P : Pl D.host.E) {m n : ℕ} (hmn : n ≤ m)
    (U : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (hU : IsIntM U)
    (hdU : IsUnit (topL n (redM P U)).det) :
    (∀ i j, Valued.v (topAt P hmn U i j) ≤ 1) ∧ Valued.v (topAt P hmn U).det = 1 ∧
      (topL n (redM P U) = 1 → ∀ i j, Valued.v ((topAt P hmn U - 1) i j) < 1) := by
  let S := Formalism.L2.Herm.intAf (↥D.host.F) D.host.E
  let A' : Matrix (Fin n) (Fin n) S := fun i j => ⟨U (Fin.castLE hmn i) j, hU _ _⟩
  let φ : S →+* HeightOneSpectrum.adicCompletion D.host.E P :=
    (GlobalTheory.StdFrames.cpt P).comp S.subtype
  have hA : A'.map φ = topAt P hmn U := by ext i j; rfl
  have hred : A'.map (resS (↥D.host.F) P) = topL n (redM P U) := by
    ext i j
    simp only [Matrix.map_apply, topL, redM]
    rw [dite_eq_left ⟨lt_of_lt_of_le i.2 hmn, j.2⟩, dite_eq_left (hU _ _)]
    rfl
  have hint : ∀ i j, Valued.v (topAt P hmn U i j) ≤ 1 := by
    intro i j
    have := (GlobalTheory.StdFrames.mem_OA_iff (U (Fin.castLE hmn i) j)).1 (hU _ _) P
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 this
  have hφ : ∀ s : S, resS (↥D.host.F) P s = 0 ↔ Valued.v (φ s) < 1 :=
    fun s => GlobalTheory.AdIsom.resS_eq_zero_iff_cpt P s
  refine ⟨hint, ?_, ?_⟩
  · apply le_antisymm ((adj_det_integral Valued.v _ hint).2)
    have h1 : resS (↥D.host.F) P A'.det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hred]; exact hdU.ne_zero
    rw [Ne, hφ, not_lt, RingHom.map_det, RingHom.mapMatrix_apply, hA] at h1
    exact h1
  · intro h1 i j
    have hm : (resS (↥D.host.F) P).mapMatrix (A' - 1) = 0 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hred, h1, sub_self]
    have h2 : resS (↥D.host.F) P ((A' - 1) i j) = 0 := by
      have := congrFun (congrFun hm i) j
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hm' : φ.mapMatrix (A' - 1) = topAt P hmn U - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hA]
    have h3 : (topAt P hmn U - 1) i j = φ ((A' - 1) i j) := by
      have e := congrFun (congrFun hm' i) j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e
      exact e.symm
    rw [h3]
    exact (hφ _).1 h2

end GlobalTheory.LocCore

namespace GlobalTheory.LocCore

theorem kappa_integral_at : ∀ (D : D7) (P : Pl D.host.E) (m n : ℕ) (U Y : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (κ : Matrix (Fin n) (Fin n) (Formalism.IndefR.Datum.EAf D)) (c : Formalism.IndefR.Datum.EAf D), GlobalTheory.StdFrames.cpt P c = 1 → (HMul.hMul U κ : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) = c • Y + (1 - c) • U → IsIntM U → IsIntM Y → IsUnit (topL n (redM P U)).det → IsUnit (topL n (redM P Y)).det → (∀ a b, GlobalTheory.StdFrames.cpt P (κ a b) ∈ P.adicCompletionIntegers D.host.E) ∧ Valued.v (GlobalTheory.StdFrames.cpt P κ.det) = 1 ∧ (topL n (redM P U) = 1 → topL n (redM P Y) = 1 → ∀ a b, Valued.v (GlobalTheory.StdFrames.cpt P ((κ - 1) a b)) < 1) := by
  intro D P m n U Y κ c hc hUk hU hY hdU hdY
  by_cases hmn : n ≤ m
  swap
  · exfalso
    push_neg at hmn
    have h0 : (topL n (redM P U)).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero ⟨m, hmn⟩
      intro j
      simp [topL]
    rw [h0] at hdU
    exact not_isUnit_zero hdU
  set cp := GlobalTheory.StdFrames.cpt (D := D) P with hcp
  obtain ⟨hAi, hAd, hA1⟩ := topAt_facts P hmn U hU hdU
  obtain ⟨hBi, hBd, hB1⟩ := topAt_facts P hmn Y hY hdY
  have hAB : topAt P hmn U * κ.map cp = topAt P hmn Y := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg cp (congrFun (congrFun hUk (Fin.castLE hmn i)) j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, map_add, map_sub, map_one, hc, sub_self, zero_mul, add_zero, one_mul] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply]
    exact h
  obtain ⟨k1, k2, k3⟩ := solve_integral Valued.v _ _ _ hAB hAi hBi hAd hBd
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (k1 a b)
  · rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact k2
  · intro h1 h2 a b
    have e : cp.mapMatrix (κ - 1) = κ.map cp - 1 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply]
    have e2 := congrFun (congrFun e a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at e2
    rw [e2]
    exact k3 (hA1 h1) (hB1 h2) a b

end GlobalTheory.LocCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicSubLtOne
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

section Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tr {F1 : Subfield E} (h : F1 = maximalRealSubfield E) : AL E →+* E ⊗[F1] Formalism.L2.Herm.Af F1 :=
  (GlobalTheory.LevSplit.swp F1 E).comp (GlobalTheory.Mem.R3.swapCast h).symm.toRingHom

theorem tr_rfl (z : AL E) : tr (rfl : maximalRealSubfield E = maximalRealSubfield E) z = z := by
  exact (Algebra.TensorProduct.comm _ _ _).apply_symm_apply z

theorem tr_int {F1 : Subfield E} (h : F1 = maximalRealSubfield E) {z : AL E} (hz : z ∈ ALint E) :
    tr h z ∈ Formalism.L2.Herm.intAf F1 E := by
  subst h
  rw [tr_rfl]
  have key : ReciprocityTheory.Aut.ALint E ≤ Formalism.L2.Herm.intAf (maximalRealSubfield E) E := by
    unfold ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : E), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact key hz

theorem proj_le_one (s : SplitPlace E) {z : AL E} (hz : z ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E) :
    Valued.v (s.proj z) ≤ 1 := by
  have key : Formalism.L2.Herm.intAf (maximalRealSubfield E) E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield E)).toSubring.comap s.proj := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring,
        IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact s.split_le_one b
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  have := key hz
  rwa [Subring.mem_comap, ValuationSubring.mem_toSubring,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem res_eq {F1 : Subfield E} (h : F1 = maximalRealSubfield E) (s : SplitPlace E) (z : AL E)
    (y : Formalism.L2.Herm.intAf F1 E) (hy : (y : E ⊗[F1] Formalism.L2.Herm.Af F1) = tr h z) (a : 𝓞 E)
    (ha : Valued.v (s.proj z - s.i (a : E)) < 1) : resS F1 s.w y = Ideal.Quotient.mk _ a := by
  subst h
  have key : ∀ (t : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E))
      (ht : t ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E),
      ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c := by
    intro t ht
    refine Subring.closure_induction
      (p := fun t ht => ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c) ?_ ?_ ?_ ?_ ?_ ?_ ht
    · rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · refine ⟨b, ?_, ?_⟩
        · simp [ReciprocityTheory.Aut.SplitPlace.proj]
        · have e : (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.oToS (maximalRealSubfield E) E b :=
            Subtype.ext (Formalism.L2.DIV.oToS_coe (F := maximalRealSubfield E) b).symm
          rw [e, Formalism.L2.DIV.resS_oToS]
      · obtain ⟨D0, hD0, hD0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.v.ne_bot
        obtain ⟨r, hr⟩ := Formalism.UG.P.csApprox_local s.v D0 hD0ne (a s.v) (ha s.v)
        have hlt : s.v.intValuation D0 < 1 := by
          exact (s.v.intValuation_lt_one_iff_mem D0).mpr hD0
        have hi : s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E)) : E) =
            algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r := by
          rw [ReciprocityTheory.Aut.split_coe_algebraMap, AlgHom.commutes,
            IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
              (s.v.adicCompletion (maximalRealSubfield E)) r]
        refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r, ?_, ?_⟩
        · have hp : s.proj ((1 : E) ⊗ₜ[maximalRealSubfield E] a) = a s.v := by
            simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              Algebra.TensorProduct.lift_tmul, map_one, one_mul]
            rfl
          rw [hp, hi]
          exact hr.trans hlt
        · have hsplit : (⟨_, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.adS (maximalRealSubfield E) E (⟨a, ha⟩ - Formalism.L2.DIV.oToAd (maximalRealSubfield E) r) +
                Formalism.L2.DIV.oToS (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r) := by
            rw [← Formalism.L2.DIV.adS_oToAd, ← map_add (f := _), sub_add_cancel]
            exact Subtype.ext (Formalism.L2.DIV.adS_coe (E := E) ⟨a, ha⟩).symm
          rw [hsplit, map_add (f := _), Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_adS_eq_zero s.w s.v s.w_under.symm, zero_add]
          show Valued.v (a s.v - algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r) < 1
          exact hr.trans hlt
    · refine ⟨0, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 0 = _
      simp
    · refine ⟨1, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 1 = _
      simp
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 + c2, ?_, ?_⟩
      · have : s.proj (x + y) - s.i ((c1 + c2 : 𝓞 E) : E) = (s.proj x - s.i (c1 : E)) + (s.proj y - s.i (c2 : E)) := by
          push_cast
          rw [map_add (f := _), map_add (f := _)]
          ring
        rw [this]
        exact Valuation.map_add_lt _ h1 h2
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ + ⟨y, hy⟩) = _
        rw [map_add (f := _), e1, e2, map_add (f := _)]
    · rintro x hx ⟨c1, h1, e1⟩
      refine ⟨-c1, ?_, ?_⟩
      · have : s.proj (-x) - s.i ((-c1 : 𝓞 E) : E) = -(s.proj x - s.i (c1 : E)) := by
          push_cast
          rw [map_neg, map_neg]
          ring
        rw [this, Valuation.map_neg]
        exact h1
      · change resS (maximalRealSubfield E) s.w (-⟨x, hx⟩) = _
        rw [map_neg, e1, map_neg]
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 * c2, ?_, ?_⟩
      · have : s.proj (x * y) - s.i ((c1 * c2 : 𝓞 E) : E) =
            s.proj x * (s.proj y - s.i (c2 : E)) + (s.proj x - s.i (c1 : E)) * s.i (c2 : E) := by
          push_cast
          rw [map_mul, map_mul]
          ring
        rw [this]
        have hx1 : Valued.v (s.proj x) ≤ 1 := proj_le_one s hx
        have hc2 : Valued.v (s.i (c2 : E)) ≤ 1 := s.split_le_one c2
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' hx1) h2
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_right' hc2) h1
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ * ⟨y, hy⟩) = _
        rw [map_mul, e1, e2, map_mul]
  obtain ⟨c, hc1, hc2⟩ := key y.1 y.2
  have hyz : (y : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E)) = z := by rw [hy, tr_rfl]
  rw [hyz] at hc1
  have hca : Valued.v (s.i ((c - a : 𝓞 E) : E)) < 1 := by
    have : s.i ((c - a : 𝓞 E) : E) = (s.proj z - s.i (a : E)) - (s.proj z - s.i (c : E)) := by
      push_cast
      rw [map_sub]
      ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hc1)
  have hmem : c - a ∈ s.w.asIdeal := (s.split_mem_ideal (c - a)).mpr hca
  have hyy : (⟨y.1, y.2⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) = y := rfl
  rw [hyy] at hc2
  rw [hc2]
  exact Ideal.Quotient.eq.mpr hmem

end Res

section Padic

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {g : ℕ} [Fact g.Prime]

end Padic

end GlobalTheory.RowGood

end

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

end GlobalTheory.RowGood

end
end

