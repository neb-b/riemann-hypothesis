module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPos
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0394
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleNotKilledByGoodProjectorSatisfiesH
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.Published GlobalTheory.Chain.RealIt

namespace GlobalTheory.Chain.ItPairObj

theorem exists_record (hD : DiscreteSeriesCover) (hH : HarishChandraModules) :
    ∃ X : ProvA, ChosenSeries X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X := by
  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam (GlobalTheory.CoverDS.exists_hasParam hD)
  have a1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have a2 : admH2 X := GlobalTheory.JointHarm.fock_polynomials X
  have a3 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hD X hX
  have a5 : admQ5 X := hH.admQ5_of_harishChandraModules X
  have a6 : CoverHaarIntegration X := _root_.GlobalTheory.PolarU.polar_coordinates X
  have a7 : admQ7 := GlobalTheory.TensorHW.highestWeight_tensor
  have a8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have a4 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X a3 a5 a7 a8
  have h1 := _root_.GlobalTheory.DoublingPos.doubling_pos X a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨X, hX, h1, _root_.GlobalTheory.FockTensor.fock_contains_tensor X a1 a2 a3 a4 a5 a6 a7 a8 h1⟩

theorem itPair_of_rows (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D) (hV : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (hC : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction) : ItPair D := by
  obtain ⟨X, hX, h1, h2⟩ := exists_record hD hH
  exact itPair D X hX h1 h2 hF hV hB hC

theorem itPair_holds (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7) : ItPair D :=
  itPair_of_rows hD hH D (_root_.GlobalTheory.vacuumFock_all_records D) (_root_.GlobalTheory.vacChar_of_record D) (_root_.GlobalTheory.modelsAreCoverSeries_of_hypotheses hD hH D) GlobalTheory.Contr.contraction

end GlobalTheory.Chain.ItPairObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.FrameMatch

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem frGL_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL (β * intGL F E n y) z = frGL β (y * z * y⁻¹) := by
  show MulAut.conj (β * intGL F E n y) (intGL F E n z) = MulAut.conj β (intGL F E n (y * z * y⁻¹))
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  group

theorem St_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    St (β * intGL F E n y) = St β := by
  ext x
  show x ∈ (frGL (β * intGL F E n y)).range ↔ x ∈ (frGL β).range
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨y * z * y⁻¹, (frGL_mul_intGL β y z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨y⁻¹ * z * y, ?_⟩
    rw [frGL_mul_intGL]
    congr 1
    group

theorem redFn_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    redFn (β * intGL F E n y) PP x =
      (Formalism.UG.bc (resS F PP) y)⁻¹ * redFn β PP x * Formalism.UG.bc (resS F PP) y := by
  by_cases hx : x ∈ St β
  · obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hx
    have h1 : frGL β z = frGL (β * intGL F E n y) (y⁻¹ * z * y) := by
      rw [frGL_mul_intGL]
      congr 1
      group
    conv_lhs => rw [h1]
    rw [redFn_frGL, redFn_frGL]
    rw [map_mul, map_mul, map_inv]
  · have hx' : x ∉ St (β * intGL F E n y) := by rwa [St_mul_intGL]
    simp only [redFn, ext1, dif_neg hx, dif_neg hx', mul_one, inv_mul_cancel]

theorem frGL_mul (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL β y * β = β * intGL F E n y := by
  simp only [frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_intGL_of_isFrame {β₁ β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : IsFrame β₁ Λ) (h₂ : IsFrame β₂ Λ) : ∃ m : GL (Fin n) (Formalism.L2.Herm.intAf F E), β₂ = β₁ * intGL F E n m := by
  classical

  have key : ∀ {γ δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}, IsFrame γ Λ → IsFrame δ Λ → ∀ i j,
      ((γ⁻¹ * δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j ∈
        Formalism.L2.Herm.intAf F E := by
    intro γ δ hγ hδ i j
    set v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F :=
      (δ : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (Pi.single j 1) with hv
    have hvL : v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
      rw [hδ v]
      intro k
      rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rcases eq_or_ne k j with hk | hk
      · subst hk
        simp only [Pi.single_eq_same]
        exact Subring.one_mem _
      · simp only [Pi.single_eq_of_ne hk]
        exact Subring.zero_mem _
    have hi := (hγ v).1 hvL i
    rw [hv, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, ← Units.val_mul] at hi
    simpa [Matrix.transpose_apply] using hi
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₁ h₂ i j⟩
  let N : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₂ h₁ i j⟩
  have hM : M.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₁⁻¹ * β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hN : N.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₂⁻¹ * β₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hinj : Function.Injective
      (fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => A.map (Formalism.L2.Herm.intAf F E).subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hone : (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hMN : M * N = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₁⁻¹ * β₂ * (β₂⁻¹ * β₁) = 1 by group, Units.val_one])
  have hNM : N * M = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₂⁻¹ * β₁ * (β₁⁻¹ * β₂) = 1 by group, Units.val_one])
  refine ⟨⟨M, N, hMN, hNM⟩, ?_⟩
  have hm : intGL F E n ⟨M, N, hMN, hNM⟩ = β₁⁻¹ * β₂ := by
    ext1
    rw [← hM]
    exact Formalism.UG.P.bc_coe _ _
  rw [hm]
  group

end General


set_option maxHeartbeats 1000000 in
theorem frames_match : ∀ {D : D7} (V : HSp D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∀ β₁ β₂ : GL (Fin V.rank) (EAf D), IsFrame β₁ (Formalism.L2.Herm.crdLat V V.L0) → IsFrame β₂ (Formalism.L2.Herm.crdLat V V.L0) → ∃ u ∈ GfC V, IsFrame (finE V u * β₁) (Formalism.L2.Herm.crdLat V V.L0) ∧ ∀ PP ∈ Pg, ∀ x, redFn (finE V u * β₁) PP x = redFn β₂ PP x := by
  classical
  intro D V Pg hPg β₁ β₂ h₁ h₂
  obtain ⟨m, hm⟩ := exists_intGL_of_isFrame h₁ h₂

  obtain ⟨β₀, ⟨c, h₀⟩, -⟩ := GlobalTheory.StdFrames.exists_frame_std V
  have hB : IsBaseFrame V β₁ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ c) := ⟨h₁, h₀.2⟩

  have hloc : ∀ PP, ∃ κ : GA D V, κ ∈ GfC V ∧ finE V κ ∈ St β₁ ∧
      (PP ∈ Pg → redFn β₁ PP (finE V κ) = Formalism.UG.bc (resS D.host.F PP) m) ∧
      ∀ P', P' ≠ PP → (PP ∈ Pg → ¬ IsConjPl (D := D) PP P') → redFn β₁ P' (finE V κ) = 1 := by
    intro PP
    by_cases hPP : PP ∈ Pg
    · obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (hPg PP hPP PP hPP)
      obtain ⟨κ, -, k1, k2, k3, k4⟩ :=
        GlobalTheory.ParahoricLift.exists_local_lift hB he (Formalism.UG.bc (resS D.host.F PP) m)
      exact ⟨κ, k1, k2, fun _ => k3, fun P' hP' hc => k4 P' hP' (hc hPP)⟩
    · refine ⟨1, Subgroup.one_mem _, ?_, fun h => absurd h hPP, fun P' _ _ => ?_⟩
      · rw [map_one]
        exact Subgroup.one_mem _
      · rw [map_one]
        exact blockDiagonalExtendByOnePrimeField_one (St β₁) (redAt β₁ P')
  choose κ hκG hκS hκR hκO using hloc
  have hprod := GlobalTheory.ParahoricLift.redFn_list_prod V β₁ (Pg.toList.map κ) (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκS b)

  have hred : ∀ PP ∈ Pg, redFn β₁ PP (finE V (Pg.toList.map κ).prod) = Formalism.UG.bc (resS D.host.F PP) m := by
    intro PP hPP
    have hs := GlobalTheory.ParahoricLift.prod_map_single (Finset.nodup_toList Pg) (Finset.mem_toList.2 hPP)
      (fun b => redFn β₁ PP (finE V (κ b)))
      (fun b hb => hκO b PP (Ne.symm hb) (fun hbP => hPg b hbP PP hPP))
    rw [hprod.2 PP, List.map_map]
    exact hs.trans (hκR PP hPP)
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hprod.1
  refine ⟨(Pg.toList.map κ).prod, (GfC V).list_prod_mem (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκG b), GlobalTheory.StabLatInv.isFrame_mul_of_mem_St β₁ _ _ h₁ hprod.1, ?_⟩
  intro PP hPP x
  have hz' : Formalism.UG.bc (resS D.host.F PP) z = Formalism.UG.bc (resS D.host.F PP) m := by
    rw [← redFn_frGL β₁ PP z, hz]
    exact hred PP hPP
  rw [← hz, frGL_mul, hm, redFn_mul_intGL, redFn_mul_intGL, hz']

end GlobalTheory.FrameMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUnique
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_proj {K M : Type} [Field K] [AddCommGroup M] [Module K M] (U : Submodule K M) :
    ∃ Q : M →ₗ[K] M, (∀ x ∈ U, Q x = 0) ∧ ∀ x, x - Q x ∈ U := by
  obtain ⟨W, hW⟩ := U.exists_isCompl
  refine ⟨LinearMap.id - U.subtype ∘ₗ U.projectionOnto W hW, fun x hx => ?_, fun x => ?_⟩
  · have := Submodule.projectionOnto_apply_left hW ⟨x, hx⟩
    simp [this]
  · simp

theorem exists_lattice {O K : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K))
    (h : Λ.FG) : ∃ (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (Λ' : Submodule O (Fin n → K)),
      Submodule.IsFullLattice K Λ' ∧ Λ ≤ Λ' ∧ (∀ x ∈ Λ, Q x = 0) ∧ ∀ x ∈ Λ', Q x = 0 → x ∈ Λ := by
  classical
  obtain ⟨Q, h1, h2⟩ := exists_proj (Submodule.span K (Λ : Set (Fin n → K)))
  have h3 : ∀ x, Q (Q x) = Q x := fun x => by
    have := h1 _ (h2 x)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  let N := Submodule.span O (Set.range fun j : Fin n => Q (Pi.single j 1))
  have hfg : (Λ ⊔ N).FG := h.sup (Submodule.fg_span (Set.finite_range _))
  refine ⟨Q, Λ ⊔ N, { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := ?_ }, le_sup_left,
    fun x hx => h1 x (Submodule.subset_span hx), fun x hx h0 => ?_⟩
  · apply Submodule.eq_top_iff'.2
    intro x
    have hQ : Q x ∈ Submodule.span K (N : Set (Fin n → K)) := by
      have hx : (∑ j : Fin n, x j • Pi.single j (1 : K)) = x := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply, mul_ite]
      rw [← hx, map_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))
    have hleft := Submodule.span_mono (R := K) (show Λ ≤ Λ ⊔ N from le_sup_left)
    have hright := Submodule.span_mono (R := K) (show N ≤ Λ ⊔ N from le_sup_right)
    simpa only [sub_add_cancel] using add_mem (hleft (h2 x)) (hright hQ)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have h4 : Q b = b := by
      refine Submodule.span_induction (p := fun b _ => Q b = b) ?_ (map_zero Q) ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩
        exact h3 _
      · intro x y _ _ hx hy
        rw [map_add (f := _), hx, hy]
      · intro c x _ hx
        rw [← algebraMap_smul K c x, map_smul, hx]
    rw [map_add (f := _), h1 a (Submodule.subset_span ha), h4, zero_add] at h0
    rwa [h0, add_zero]

theorem map_mulVec_gen {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) {n : ℕ}
    (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (x : Fin n → K) :
    (LinearMap.toMatrix' Q).map f *ᵥ (fun i => f (x i)) = fun i => f (Q x i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec, RingHom.map_mulVec]
  rfl

variable {D : D7}

theorem inc_injective : Function.Injective (inc D) := by
  obtain ⟨P, hP, h0⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField D.host.E) |>.imp fun _ h => h.symm
  intro a b hab
  have := congrArg (GlobalTheory.StdFrames.cpt (D := D) ⟨P, hP.isPrime, h0⟩) hab
  rw [cpt_inc, cpt_inc] at this
  exact (algebraMap D.host.E _).injective this

theorem mem_of_inc_mem_hat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    {x : Fin n → D.host.E} (hx : (fun i => inc D (x i)) ∈ hat Λ) : x ∈ Λ := by
  obtain ⟨Q, Λ', h1, h2, h3, h4⟩ := exists_lattice Λ h
  have := h1
  refine h4 x ((inc_mem_hat_iff (by infer_instance) x).1 (hat_mono h2 hx)) ?_
  have h5 : (LinearMap.toMatrix' Q).map (inc D) *ᵥ (fun i => inc D (x i)) = 0 := by
    refine hat_induction (p := fun y => (LinearMap.toMatrix' Q).map (inc D) *ᵥ y = 0) ?_ (mulVec_zero _) ?_ ?_ hx
    · intro y hy
      rw [map_mulVec_gen, h3 y hy]
      funext i
      exact RingHom.map_zero _
    · intro a b ha hb
      rw [mulVec_add, ha, hb, add_zero]
    · intro a _ b hb
      rw [mulVec_smul, hb, smul_zero]
  rw [map_mulVec_gen] at h5
  funext i
  exact inc_injective ((congrFun h5 i).trans (RingHom.map_zero _).symm)

theorem inCmp_iff {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y L) y ↔ InCmp (idem w) (Formalism.L2.Herm.crdLat Y L') y := by
  by_cases hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  · rcases (T_mem_iff hπ w).1 hT with hw | hw
    · exact ((h.2.2 w _ (isPlIdem_idem w) hw).1 y).trans ((h'.2.2 w _ (isPlIdem_idem w) hw).1 y).symm
    · have a := h.2.2 _ _ (isPlIdem_idem _) hw
      have a' := h'.2.2 _ _ (isPlIdem_idem _) hw
      rw [cjA_idem, GlobalTheory.StdFrames.cP_cP] at a a'
      refine (a.2 y).trans (Iff.trans ?_ (a'.2 y).symm)
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun y' => ?_
      rw [a.1 y', a'.1 y']
  · exact (h.2.1 w _ (isPlIdem_idem w) hT y).trans (h'.2.1 w _ (isPlIdem_idem w) hT y).symm

theorem glued_le {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') : L ≤ L' := by
  intro x hx
  have hfg : (Formalism.L2.Herm.crdLat Y L').FG := h'.1.map _
  have h1 : vA Y x ∈ hat (Formalism.L2.Herm.crdLat Y L') := mem_hat_of_idem hfg fun w =>
    ((inCmp_iff hπ h h' w _).1 ⟨smul_mem_hat (idem_mem w) (vA_mem_hat Y hx), by rw [smul_smul, idem_mul_self]⟩).1
  obtain ⟨x', hx', e⟩ := mem_of_inc_mem_hat hfg h1
  rwa [← (Formalism.L2.Herm.crd Y).injective e]

theorem glued_unique (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (Y X : HSp D)
    (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D)
    (L L' : Submodule (𝓞 D.host.E) Y.V) (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') :
    L = L' :=
  le_antisymm (glued_le hπ h h') (glued_le hπ h' h)

end GlobalTheory.GlueUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.GoodStableGiven

theorem goodStable_of_given : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Given R F → Formalism.L2.DIV.GoodStable A.X := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F h
  obtain ⟨om, hT⟩ := _root_.GlobalTheory.TameTieOfGood.exists_tameTie_of_given R F h
  exact GlobalTheory.GoodStableDual.goodStable_of_irr R F h.irr h.core.grp om
    (GlobalTheory.GoodIdemTie.idemTie_of_tameTie hGC D om hT)

end GlobalTheory.GoodStableGiven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodSplitPlaceOfFamilyPrimeBaseTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.GoodSplitFam

theorem good_split_pl : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ P, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P ∧ A3.A.q P0 ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW e P hG hP
  obtain ⟨hC, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW e
  obtain ⟨hQ0, -, -, hfam⟩ := _root_.GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev
  have hSb : R.Sb = R.Pg := hW.allPl
  have hci : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (Formalism.DivisionValues.conjPl P).asIdeal :=
    GlobalTheory.InertValLab.conjIdeal_eq_conjPl P
  have hsplit : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hci]
      intro h
      exact hP (HeightOneSpectrum.ext h)
    · intro hm
      have hm' : P ∈ R.Pg := by rw [← hSb]; exact hm
      exact (hG P (Or.inl hm')).1 rfl
    · intro Q hQ h
      rw [hci] at h
      have hQ' : Q ∈ R.Pg := by rw [← hSb]; exact hQ
      have hQe : Q = Formalism.DivisionValues.conjPl P := HeightOneSpectrum.ext h
      apply (hG Q (Or.inl hQ')).2
      rw [GlobalTheory.GoodPrimes.isConjPl_iff, hQe, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  obtain ⟨P0, hP0⟩ := hC.fam.pl_onto P hsplit
  obtain ⟨gramR, c0R, c0L, htie⟩ := hC.fam.tie
  have hok : P0 ∈ A3.A.ok A3.A.μ0 := by
    rw [htie.ok, hQ0, hP0]
    simpa using hsplit
  refine ⟨P0, hok, hP0, ?_⟩
  rw [(hfam hC.fam A3.A.μ0 P0 hok).2.2]
  intro h0
  exact (R.pl P0).ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)

end GlobalTheory.GoodSplitFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleNotKilledByGoodProjectorSatisfiesHStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_not_killed_by_good_projector_satisfies_H : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (G0 R.Pg D.R.r) W), τ.IsIrreducible → (∃ x : W, x ≠ 0 ∧ ∑ g, RealDat.eC (A := A) D.what₂.embLL g • τ (R.eG g) x = x) → ∀ a : ℕ, 0 < a → a < D.R.r → ∃ PP : R.Pg, GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ {g | (∀ PP' : R.Pg, PP' ≠ PP → g PP' = 1) ∧ g PP ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (kP PP.1) D.R.r a} := by
  first | exact @GlobalTheory.GoodProjHypH.hypH_of_goodProj | exact GlobalTheory.GoodProjHypH.hypH_of_goodProj | (intros; apply GlobalTheory.GoodProjHypH.hypH_of_goodProj <;> assumption)
end

