module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

theorem mat_mul_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {A B : Matrix m m R} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem mulVec_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {A : Matrix m m R} {y : m → R} (hA : ∀ i j, A i j ∈ I) (hy : ∀ j, y j ∈ I) :
    ∀ i, (A *ᵥ y) i ∈ I := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hy k)

theorem conj_mulVec_mem {R : Type} [CommRing R] (I : Subring R) {m : Type} [Fintype m]
    {C N Ci : Matrix m m R} (hC : ∀ i j, C i j ∈ I) (hCi : ∀ i j, Ci i j ∈ I) (s : R)
    (hN : ∀ i j, s * N i j ∈ I) {y : m → R} (hy : ∀ j, y j ∈ I) (a : m) :
    s * ((C * N * Ci) *ᵥ y) a ∈ I := by
  have h : s * ((C * N * Ci) *ᵥ y) a = ((C * (s • N) * Ci) *ᵥ y) a := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h]
  refine mulVec_mem I (mat_mul_mem I (mat_mul_mem I hC (fun i j => ?_)) hCi) hy a
  simpa [Matrix.smul_apply, smul_eq_mul] using hN i j

end GlobalTheory.Mem.R3.LiftBrg.EtaInvLat

namespace GlobalTheory.Mem.R3.LiftBrg.EtaInvLat


set_option maxHeartbeats 2000000 in
theorem eta_inv_lat : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → (∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → C ∈ Formalism.L2.DIV.St 1 → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec y a) ∈ Formalism.L2.NTheta.LamHat V) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y a)) =
      fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec z a) := by
  intro D V n _ h v Pb Ut d e C α hI hV hL hC hα hg
  subst h
  rw [GlobalTheory.Mem.R3.LiftBrg.StdFrame.castGL_rfl] at hg
  have hee : e * e = e := hI.1.1
  have hεI : swapAE D (finPart D e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    (GlobalTheory.IdemSupport.mem_intAE_iff _).1 (GlobalTheory.SplitPlace.idem_mem hee)
  have hiA : ∀ x : 𝓞 D.host.E, Formalism.L2.Col.iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E x) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := fun x => Formalism.L2.Col.iA_mem x
  have hπ0 : algebraMap (𝓞 D.host.E) D.host.E Ut.π ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 D.host.E) D.host.E)]
    exact (IsFractionRing.injective (𝓞 D.host.E) D.host.E).ne Ut.hπ0
  have hsπ0 : star (algebraMap (𝓞 D.host.E) D.host.E Ut.π) ≠ 0 := star_ne_zero.mpr hπ0
  have hπinv : swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (algebraMap (𝓞 D.host.E) D.host.E Ut.π)⁻¹ ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h1 := not_not.mp ((hI.2 Ut.π Ut.hπ0).not.mp Ut.hπP)
    have h2 := (GlobalTheory.IdemSupport.mem_intAE_iff _).1 h1
    rw [map_mul, map_mul] at h2
    exact h2
  have hstar : star (algebraMap (𝓞 D.host.E) D.host.E Ut.π) =
      algebraMap (𝓞 D.host.E) D.host.E (Formalism.L2.Col.cO D.host.E Ut.π) := rfl
  have hCC := (Formalism.L2.Col.rll_mem_St_iff _ C).1 hC
  obtain ⟨η, hη⟩ : ∃ η : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      η = ((Formalism.L2.Col.mhlEta D.sp.cm V.rank v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm V.rank) : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) :=
    ⟨_, rfl⟩
  rw [← hη] at hg
  have hprη : ∀ i j, Formalism.UG.prV v ((Units.val η) i j) =
      Formalism.UG.prV v (Formalism.L2.Col.iA D.host.F D.host.E (if i = j then Formalism.L2.Col.mhlDiag V.rank Ut.π d i else 0)) := by
    intro i j
    have := congrArg (fun g : GL (Fin V.rank) (D.host.E ⊗[D.host.F] HeightOneSpectrum.adicCompletion D.host.F v) => (Units.val g) i j) (Formalism.L2.Col.rll_put_self (F := D.host.F) (E := D.host.E) V.rank v
      ((Formalism.UG.bc (Formalism.UG.prV v)) ((Formalism.UG.bc (Formalism.L2.Col.iA D.host.F D.host.E)) (Formalism.L2.Col.mhlD V.rank Ut.hπ0 d))))
    rw [hη]
    exact this
  have hV' : ∀ a b : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v a = Formalism.UG.prV v b →
      swapAE D (finPart D e) * a = swapAE D (finPart D e) * b := by
    intro a b hab
    have h0 := hV (a - b) (by
      rw [map_sub, sub_eq_zero]
      exact hab)
    rw [mul_sub] at h0
    exact sub_eq_zero.mp h0
  have hεη : ∀ i j, swapAE D (finPart D e) * (Units.val η) i j =
      swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (if i = j then Formalism.L2.Col.mhlDiag V.rank Ut.π d i else 0) :=
    fun i j => hV' _ _ (hprη i j)
  have hεηi : ∀ i j, swapAE D (finPart D e) * (Units.val η⁻¹) i j =
      swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (if i = j then (Formalism.L2.Col.mhlDiag V.rank Ut.π d i)⁻¹ else 0) :=
    fun i j => hV' _ _ (by rw [hη]; exact Formalism.L2.Col.mhl_prV_eta_inv _ _ _ _ _ _)
  have hN1 : ∀ i j, swapAE D (finPart D e) * (Units.val η⁻¹) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    rw [hεηi]
    split_ifs with hij
    · simp only [Formalism.L2.Col.mhlDiag]
      split_ifs
      · rw [Formalism.L2.Col.mhlA, _root_.mul_inv_rev, inv_inv, map_mul, mul_left_comm]
        exact Subring.mul_mem _ (hstar ▸ hiA _) hπinv
      · rw [inv_one, map_one, mul_one]
        exact hεI
    · rw [map_zero, mul_zero]
      exact Subring.zero_mem _
  have hN2 : ∀ i j, (swapAE D (finPart D e) * Formalism.L2.Col.iA D.host.F D.host.E (star (algebraMap (𝓞 D.host.E) D.host.E Ut.π))) *
      (Units.val η) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    rw [mul_right_comm, hεη]
    split_ifs with hij
    · simp only [Formalism.L2.Col.mhlDiag]
      split_ifs
      · rw [Formalism.L2.Col.mhlA, mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ hsπ0, mul_one]
        exact Subring.mul_mem _ hεI (hiA _)
      · rw [map_one, mul_one]
        exact Subring.mul_mem _ hεI (hstar ▸ hiA _)
    · rw [map_zero, mul_zero, zero_mul]
      exact Subring.zero_mem _
  have hT : ∀ (β : GA D V) (w : Fin V.rank → GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (a : Fin V.rank),
      swapAE D ((finMat D.sp.cm.sig V.gram β *ᵥ w) a) =
        ((Units.val (Formalism.UG.bc (swapAE D) (finHom V β))) *ᵥ (fun b => swapAE D (w b))) a := by
    intro β w a
    rw [RingHom.map_mulVec]
    rfl
  have hgi : Formalism.UG.bc (swapAE D) (finHom V α⁻¹) = C * η⁻¹ * C⁻¹ := by
    rw [map_inv, map_inv, hg]
    group
  have hinv : finMat D.sp.cm.sig V.gram α⁻¹ * finMat D.sp.cm.sig V.gram α = 1 := by
    show Units.val (finHom V α⁻¹) * Units.val (finHom V α) = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hL] at hy ⊢
    intro a
    show swapAE D (finPart D e * _) ∈ _
    rw [map_mul, hT, hgi, Units.val_mul, Units.val_mul]
    exact conj_mulVec_mem _ hCC.1 hCC.2 _ hN1 hy a
  · refine ⟨fun a => finPart D e * (finMat D.sp.cm.sig V.gram α *ᵥ
      (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) a, ?_, ?_⟩
    · rw [hL] at hy ⊢
      intro a
      show swapAE D (finPart D e * _) ∈ _
      rw [map_mul, hT, hg, Units.val_mul, Units.val_mul]
      have hw : (fun b => swapAE D (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) =
          (Formalism.L2.Col.iA D.host.F D.host.E (star (algebraMap (𝓞 D.host.E) D.host.E Ut.π))) • (fun b => swapAE D (y b)) := by
        funext b
        rw [map_mul]
        rfl
      rw [hw, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
      exact conj_mulVec_mem _ hCC.1 hCC.2 _ hN2 hy a
    · have hz : (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α *ᵥ
          (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) a) =
          finPart D e • (finMat D.sp.cm.sig V.gram α *ᵥ
          (fun b => finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y b)) := rfl
      rw [hz, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      funext a
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc (finPart D e) (finPart D e), ← map_mul, hee]

end GlobalTheory.Mem.R3.LiftBrg.EtaInvLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedLevelEqParahoricWithTupleCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtPara

theorem levelPara : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelPara (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ξ := by
  intro D T L μ0 hL hPg i t hr ψ v hv
  have loc_mul (a b : HChar D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E))
      (x : (w.adicCompletion D.host.E)ˣ) :
      (a * b).loc w x = a.loc w x * b.loc w x := rfl
  obtain ⟨s, hsv, hsQ⟩ := _root_.GlobalTheory.TwistSplitPlace.exists_splitPlace_of_mem_qPl D T L μ0 hL i t v hv
  have hvg : s.v ∉ gPl D := hsv ▸ hv.1
  obtain ⟨hPgo, hQo⟩ := _root_.GlobalTheory.OtherPlaces.over_ne D T L μ0 hL hPg t s hvg hsQ

  have hunr : (L.C.mu0 i).UnrAt s.w := by
    refine (L.C.isMu0 i).unr s.w fun k hk => hvg ⟨s.w, s.w_under, k, hk⟩
  have htame : (L.C.mu0 i * L.xiH t).TameAt s.w := by
    intro x hx hx1
    rw [loc_mul, (L.C.isMu0 i).tame s.w x hx hx1, hL.xi_tame t s.w x hx hx1, one_mul]
  obtain ⟨ξ, hξc, hξr⟩ := _root_.GlobalTheory.HeckeSplitComp.main D.host.E s _ htame
  obtain ⟨hUA, hSt, hred, hloc⟩ := _root_.GlobalTheory.MtRed.km_reduction D D.R.nV
  obtain ⟨φ, -, hφ0, hφa, hφe⟩ := hloc s
  have hoff : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ PP,
      (PP ∈ L.Pg ∨ (PP ∈ L.Q t ∧ PP ≠ s.w)) → redFn 1 PP (km D D.R.nV κ) = 1 := by
    intro κ hκ htr PP hPP
    obtain ⟨v', hov, hne⟩ : ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v :=
      hPP.elim (hPgo PP) (fun h => hQo PP h.1 h.2)
    exact hred κ hκ {s.v} v' PP htr hov (by simpa using hne)
  refine ⟨s, ξ, hsv, hξc, ⟨?_, ?_⟩⟩
  · intro κ htr
    have hkey : ∀ hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV,
        (redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) ↔ ∀ a b : Fin D.R.nV, D.R.r ≤ a.val → b.val < D.R.r →
          Valued.v (((s.loc D.R.nV κ : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) := fun hκ =>
      (_root_.GlobalTheory.reduction_blockTri_detDD D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκ)).1
    constructor
    · intro hJ
      have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _ := hJ
      rw [mem_lev, mem_parLev] at hJ'
      obtain ⟨⟨-, hSt', -, hQ'⟩, -⟩ := hJ'
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 hSt'
      refine ⟨GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => GlobalTheory.HeckeStdFacts.proj_mem s (hκU a b), fun a b => ?_⟩, ?_⟩
      · rw [← map_inv]
        exact GlobalTheory.HeckeStdFacts.proj_mem s ((inv_mem hκU) a b)
      · exact (hkey hκU).1 (hQ' s.w hsQ)
    · rintro ⟨hG, hlow⟩
      obtain ⟨hG1, hG2⟩ := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 hG
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV :=
        GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ htr (fun a b => hG1 a b) (fun a b => by rw [map_inv]; exact hG2 a b)
      have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
        funext PP
        show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
        rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      show km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _
      rw [mem_lev, mem_parLev, hrt]
      refine ⟨⟨hUA κ, (hSt κ).2 hκU, fun PP hPP => ?_, fun PP hPP => ?_⟩, Subgroup.one_mem _⟩
      · rw [hoff κ hκU htr PP (Or.inl hPP)]; exact Subgroup.one_mem _
      · by_cases hPs : PP = s.w
        · subst hPs; exact (hkey hκU).2 hlow
        · rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hPs⟩)]; exact Subgroup.one_mem _
  · intro κ hJ htr u hu
    have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1
        (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) := hJ
    have hpar := (mem_lev.1 hJ').1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 (parLev_St hpar)
    have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
      funext PP
      show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
      rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    have hQ' : redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) := parLev_q hpar hsQ
    obtain ⟨hd, hdv⟩ := (_root_.GlobalTheory.reduction_blockTri_detDD D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκU)).2 hQ'
    obtain ⟨w0, hw0⟩ : ∃ w0, w0 = dBlk (blk2 D.R.r) 1 (redFn 1 s.w (km D D.R.nV κ)) := ⟨_, rfl⟩
    rw [← hw0] at hdv
    have hQ1 : ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP (km D D.R.nV κ))) = L.xiR t s.w w0 := by
      rw [hw0]
      refine Finset.prod_eq_single_of_mem s.w hsQ fun PP hPP hne => ?_
      rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hne⟩)]
      show L.xiR t PP (ext1 _ _ 1) = 1
      rw [blockDiagonalExtendByOnePrimeField_one, map_one]
    have hval : stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) ⟨κ, hJ⟩ =
        L.xiR t s.w w0 := by
      show levFn 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = _
      unfold levFn
      rw [hrt, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, one_mul]
      · exact hQ1
      · intro PP hPP
        refine Finset.prod_eq_one fun c _ => ?_
        rw [hoff κ hκU htr PP (Or.inl hPP)]
        exact (congrArg _ (blockDiagonalExtendByOnePrimeField_one _ _)).trans (map_one _)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (w0 : kP s.w)
    have hw0ne : (w0 : kP s.w) ≠ 0 := w0.ne_zero
    have haP : a ∉ s.w.asIdeal := fun h => hw0ne (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
    have ha0 : (a : D.host.E) ≠ 0 := fun h => haP (by
      rw [show a = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
    obtain ⟨k, hk⟩ : ∃ k : D.host.Eˣ, (k : D.host.E) = a := ⟨Units.mk0 _ ha0, rfl⟩
    have hres : L.xiR t s.w w0 = (L.xiH t).locK s.w k := hL.xiR t s.w hsQ a k w0 hk ha.symm
    obtain ⟨hia, hφia⟩ := hφa a
    have hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
      rw [hu]
      refine le_antisymm hd (not_lt.1 fun hlt => hw0ne ?_)
      rw [hdv]; exact (hφ0 _).2 hlt
    have hu2 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1 := by
      have h0 : φ (⟨_, hd⟩ - ⟨_, hia⟩) = 0 := by rw [map_sub, ← hdv, hφia, ha, sub_self]
      have h1 := (hφ0 _).1 h0
      rw [AddSubgroupClass.coe_sub] at h1
      rw [hu]; exact h1
    have hk1 : (L.C.mu0 i).locK s.w k = 1 := by
      have hv1 : Valued.v (((k : D.host.E) : s.w.adicCompletion D.host.E)) = 1 := by
        rw [hk]
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
          HeightOneSpectrum.intValuation_eq_one_iff]
        exact haP
      exact hunr _ hv1
    have hmul : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k :=
      loc_mul _ _ s.w (atFin s.w k)
    refine hval.trans (hres.trans ?_)
    rw [hξr u a k hk hu1 hu2, hmul, hk1, one_mul]

end GlobalTheory.MtPara
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLoc.TraitOrd

section Specialise

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} [IsOpenImmersion j]
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

theorem isSemiAbelian_of_isGrpPullback {T : Scheme.{0}} {f : T ⟶ S} {G' : Over T} [GrpObj G'] [IsCommMonObj G']
    {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end Specialise

theorem eq_of_associated_pow {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)


end GlobalTheory.SiegLoc.TraitOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChartLevelsDeterminantMapsValuesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_levels_determinant_maps_values : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∃ dt : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.DetTie (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev,
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) β cl, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r =
        (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).tw β).ch
          (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).K β).y cl) : ℂ) := by
  first | exact @GlobalTheory.Mem.Top.KerTwDet.detTie_vals | exact GlobalTheory.Mem.Top.KerTwDet.detTie_vals | (intros; apply GlobalTheory.Mem.Top.KerTwDet.detTie_vals <;> assumption)
end

