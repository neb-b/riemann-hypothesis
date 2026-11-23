module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisWithDualBasisInHermitianLatticeAwayPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryMinorMapRealPlaces
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearFormStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admitted_diagonal_integral_linearForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a a' : ℕ) (G : Geo σ a a') (ψ : AddChar (AF F) ℂ)
    (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a')))
    (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd → ∀ v : Pl (F := F),
    ∃ l ∈ (adeleClass F).adm ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
      (∀ z : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
        l (dd.rho ψ (z * (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ r₀ : ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ, (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), Rest (evFin F v) φ r₀) ∧
      ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∃ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) ∧
        ∃ φ₀ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∫ x, φ₀ x * φ₀ x ∂μ ≠ 0 := by
  first | exact @GlobalTheory.DiagLocal.exists_diag_form | exact GlobalTheory.DiagLocal.exists_diag_form | (intros; apply GlobalTheory.DiagLocal.exists_diag_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisWithDualBasisInHermitianLatticeAwayPlStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_with_dual_basis_in_hermitian_lattice_away_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n r s : ℕ} (X : Spc F E n), X.IsHerm σ B r s → ∀ v : Pl (F := F),
    ∃ f p : Fin n → Fin n → E, (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • f k ∈ X.L) ∧
      (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • p k ∈ X.L) ∧
      ∀ k l, form σ X.J (p k) (f l) = if k = l then 1 else 0 := by
  first | exact @GlobalTheory.HermLocDualBasis.exists_locDualBasis | exact GlobalTheory.HermLocDualBasis.exists_locDualBasis | (intros; apply GlobalTheory.HermLocDualBasis.exists_locDualBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryMinorMapRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementaryMinor_map_realPlaces : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n : D.what₂.Tau → ℕ),
    ∃ (Pl : PolF D d a →ₗ[ℂ] PolF D d a') (ε : Tup D a d n → ℤˣ),
      (∀ T : Tup D a d n, Pl (GlobalTheory.BotFormula.minorF rfl rfl T) =
        ((ε T : ℤ) : ℂ) • GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) ∧
      ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)))⁻¹ • GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (Pl P) := by
  first | exact @GlobalTheory.BotMatch.complementary_minor_map | exact GlobalTheory.BotMatch.complementary_minor_map | (intros; apply GlobalTheory.BotMatch.complementary_minor_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMeanLogAreaLogThetaNormLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean


open Classical in
private theorem meanInf_avg_le (K M : Type) [Field K] [NumberField K] [Field M] [Algebra ℚ M] [FiniteDimensional ℚ M]
    (i : K →+* M) (h : (M →ₐ[ℚ] ℂ) → ℝ) (h0 : ∀ ρ, 0 ≤ h ρ) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun p => (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}, h ρ) /
      Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}) ≤
      2 * ((∑ ρ, h ρ) / (Module.finrank ℚ M : ℝ)) := by
  letI : Algebra K M := i.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  have hcard : ∀ σ : K →+* ℂ, (Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x} : ℝ) = Module.finrank K M := by
    intro σ
    have h1 := GlobalTheory.ArchMean.sum_comp_algHom K M (fun φ => if φ = σ.toRatAlgHom then 1 else 0)
    rw [Finset.sum_ite_eq' Finset.univ σ.toRatAlgHom, if_pos (Finset.mem_univ _), mul_one, Finset.sum_boole] at h1
    rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    refine Finset.filter_congr fun ρ _ => ?_
    rw [AlgHom.ext_iff]
    rfl
  have hsum : ∀ σ : K →+* ℂ, (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x}, h ρ) =
      ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ := by
    intro σ
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext ρ
    simp [RingHom.ext_iff]
  have hle : ∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ ≤
      ∑ ρ, h ρ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i) h]
    have hinj : Function.Injective (fun p : InfinitePlace K => p.embedding) := fun p q hpq => by
      rw [← p.mk_embedding, ← q.mk_embedding]
      exact congrArg _ hpq
    rw [← Finset.sum_image (s := Finset.univ) (g := fun p : InfinitePlace K => p.embedding)
      (f := fun σ : K →+* ℂ => ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ)
      (fun p _ q _ hpq => hinj hpq)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => Finset.sum_nonneg fun ρ _ => h0 ρ
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hk : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  simp only [hcard, hsum]
  rw [← Finset.sum_div, ← ht]
  generalize (∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ) = S at *
  calc _ = 2 * (S / (Module.finrank ℚ K * Module.finrank K M : ℝ)) := by field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le : ∃ C1 : ℝ, 0 < C1 ∧ ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hArea D δ t0)) ≤ C1 * L ∧ Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hTh D δ t0)) ≤ C1 * L := by
  obtain ⟨C₀, hC₀, hmean⟩ := _root_.GlobalTheory.PositiveMeans.means_le
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro D hI δ t0 hc ht L hL hrL hdL
  obtain ⟨hdata, htor⟩ := (_root_.GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have h2 : g2 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h3 : g3 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h4 : wpF (lat D δ) t0 ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  haveI : FiniteDimensional ℚ (fld D δ t0) := by
    let b := Module.finBasis ℚ D.what₂.LL
    obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
      (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
      ((Set.finite_range _).union (Set.toFinite _)) (by
        rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
        · exact mem_algebraicClosure_iff.2
            ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
        · exact hdata.2.1
        · exact hdata.2.2
        · exact hwp)
    have hle : fld D δ t0 ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro y (⟨y, rfl⟩ | hy)
      · set_option synthInstance.maxHeartbeats 100000 in
        rw [← b.sum_repr y, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
      · exact hM _ (Or.inr hy)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have htt : ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ) := fun ρ => by
    have h := (hI.t0Ex _ δ hc).2 (fld D δ t0) ρ h2 h3
    unfold tc
    rw [dite_eq_left h]
    exact h.choose_spec
  obtain ⟨hu, hv⟩ := hmean D hI _ δ t0 hc ht L hL hrL hdL (fld D δ t0) h2 h3 h4 (tc D δ t0) htt
  let i : D.what₂.LL →+* fld D δ t0 := D.what₂.embLL.codRestrict (fld D δ t0) (embLL_mem D δ t0)
  refine ⟨(meanInf_avg_le D.what₂.LL (fld D δ t0) i (hArea D δ t0) fun ρ => Real.posLog_nonneg).trans ?_,
    (meanInf_avg_le D.what₂.LL (fld D δ t0) i (hTh D δ t0) fun ρ => Real.posLog_nonneg).trans ?_⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hu zero_le_two
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hv zero_le_two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCutOperatorsMirabolicFinitePlaces
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

theorem cuts_mir {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ)
    (hψ : IsLocallyConstant ψ) (hψ1 : ψ ≠ 1) (m : ℕ) (U : Subgroup (GL (Fin (m + 1)) F))
    (hUc : IsCompact (U : Set (GL (Fin (m + 1)) F))) (hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)))
    (z : GL (Fin (m + 1)) F) : Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (cell z (U : Set (GL (Fin (m + 1)) F)))
      {p | lr p = lr 1} := by
  induction m with
  | zero =>
    classical
    have h1 : ∀ q : GL (Fin (0 + 1)) F, lr q = lr 1 → q = 1 := fun q hq => by
      obtain ⟨h, x, rfl⟩ := exists_mir hq
      rw [Subsingleton.elim h 1, Subsingleton.elim x 0, mir_one]
    refine ⟨Finsupp.single 1 (if (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F)) then 1 else 0),
      fun f _ _ g hg => ?_⟩
    rw [h1 g hg, act_single, mul_one]
    by_cases h : (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F))
    · rw [if_pos h, one_mul, Set.indicator_of_mem h]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem h]
  | succ m ih =>
    refine _root_.GlobalTheory.JSW.Cut.cuts_mir_of_res ψ hψ hψ1 m (GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup ψ hψ hψ1 m (fun V hVc hVo z' => ?_)) U hUc hUo z
    refine GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup ψ V hVo _ _ (fun x hx u hu => ?_) (ih V hVc hVo z')
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    exact ⟨n, hn, k * u, V.mul_mem hk hu, by rw [mul_assoc]⟩

end GlobalTheory.JSW.Cut


open GlobalTheory.JSW.Cut in
theorem GlobalTheory.JSW.MirPatch.cut_operators : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  intro E _ _ _ m S K hKo hKc q
  classical
  obtain ⟨U, N, z, hU, hdisj, hchar⟩ := GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets E m S K hKo hKc q
  choose ψ hψv hψl hψ1 using _root_.GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one E
  have hcut : ∀ i : Fin N, ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧
      GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
      (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
        GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
    intro i
    refine GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic E m S ψ hψv K U (z i) (fun w hw => (hU w hw).2.2) fun w hw => ?_
    haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
    haveI : IsUltrametricDist (w.adicCompletion E) :=
      inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
        (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
    exact cuts_mir (ψ w) (hψl w) (hψ1 w) m (U w) (hU w hw).1 (hU w hw).2.1 (z i w)
  choose T hTs hT using hcut
  obtain ⟨n, h, c, hh, he⟩ := exists_fin (∑ i, T i)
  refine ⟨n, h, c, fun j => ?_, fun W hW hWK p hp => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finsupp.mem_support_finsetSum _ (hh j)
    exact (hTs i _ hi).1
  · rw [← he, act_finset_sum]
    simp_rw [fun i => hT i W hW hWK p hp]
    by_cases hc : p ∈ GlobalTheory.JSW.MirPatch.cell K q
    · obtain ⟨i, hi⟩ := (hchar p hp).1 hc
      rw [Set.indicator_of_mem hc, Finset.sum_eq_single i]
      · exact Set.indicator_of_mem (s := {x : GA E (m + 1) | _}) hi _
      · intro j _ hj
        exact Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hj' => hj (hdisj p hp j i hj' hi)) _
      · simp
    · rw [Set.indicator_of_notMem hc]
      refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hi => hc ((hchar p hp).2 ⟨i, hi⟩)) _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetCharInvariantSameValueTwistedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detCharInvariant_same_value_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  first | exact @GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | exact GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted | (intros; apply GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenuineSplittingAdelicSchwartzPlaceSignatuStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genuineSplitting_adelicSchwartz_placeSignature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsByD τ C ω₀ Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c₀ := by
  first | exact @GlobalTheory.GenRepD.genRepD | exact GlobalTheory.GenRepD.genRepD | (intros; apply GlobalTheory.GenRepD.genRepD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HypPairSelfDual

theorem exists_partner : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : S.V),
    IsSelfDualC S Λ → x ≠ 0 → S.hT x x = 0 →
    ∃ y : S.V, S.hT y y = 0 ∧ S.hT x y = 1 ∧
      ∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y) := by
  intro D S Λ x hΛ hx0 hxx
  set σ : D.host.E →ₐ[D.host.F] D.host.E := D.sp.cm.sig with hσdef
  have hσs : ∀ e : D.host.E, σ e = star e := fun _ => rfl
  have hσ : ∀ e, σ (σ e) = e := fun e => by rw [hσs, hσs, star_star]
  set J : Matrix (Fin S.rank) (Fin S.rank) D.host.E := Matrix.transpose (HSpace.gram S) with hJ
  set co : S.V ≃ₗ[D.host.E] (Fin S.rank → D.host.E) := S.frame.equivFun with hco

  have hform : ∀ a b : S.V, S.hT a b = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co b) (co a) := fun a b => by
    rw [GlobalTheory.RelFlag.hT_eq_form]
    simp only [GlobalTheory.SgAlg.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IntPair.co, dotProduct, Matrix.mulVec, hJ,
      Matrix.transpose_apply, hσs, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hco]; ring
  have hframe : ∀ i, co (S.frame i) = Pi.single i 1 := fun i => by
    ext j; simp [hco, Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hherm : ∀ i j, σ (J j i) = J i j := fun i j => by
    have h1 := S.herm.eq (S.frame i) (S.frame j)
    have e1 : S.hT (S.frame i) (S.frame j) = J j i := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    have e2 : S.hT (S.frame j) (S.frame i) = J i j := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [e1, e2] at h1
    rw [hσs]; simpa [starRingEnd_apply] using h1
  have hfg : Λ.FG := hΛ.1.fg
  have hdual : ∀ w, w ∈ Λ ↔ ∀ v ∈ Λ, IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v) := fun w => by
    rw [hΛ.2 w]
    refine forall₂_congr fun v _ => ?_
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v = ∑ i, ∑ j, star (v i) * S.gram i j * w j := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, hJ, Matrix.transpose_apply, hσs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← GlobalTheory.PlaneSplit.mem_range_iff]
    simp [RingHom.mem_range, eq_comm]
  have hfu : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := GlobalTheory.HeckeAdjoint.unramified_host D; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E σ
    (GlobalTheory.AdelicU.isCMExt_host D) hfu
  have hcx0 : co x ≠ 0 := fun h => hx0 (co.injective (by rw [h, map_zero]))
  have hcxx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co x) (co x) = 0 := by rw [← hform]; exact hxx
  obtain ⟨z0, hz0L, hz0⟩ := _root_.GlobalTheory.selfDual_pair_nondeg D.host.F D.host.E σ hσ S.rank J Λ hfg hherm hdual (co x) hcx0
  obtain ⟨y₀, hy₀1, hy₀L⟩ := _root_.GlobalTheory.FormSection.exists_section D.host.F D.host.E σ S.rank J Λ hfg (co x) ⟨z0, hz0L, hz0⟩
  obtain ⟨y, hyy, hxy, hL⟩ := _root_.GlobalTheory.TraceCorrection.exists_pair D.host.F D.host.E σ hσ S.rank J Λ hherm hdual θ hθ (co x) y₀ hcxx hy₀1 hy₀L
  have hconj : ∀ a b, σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun a b => by
    have hh' : ∀ i j, σ (J i j) = J j i := fun i j => hherm j i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hh']
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨co.symm y, ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [hform, co.apply_symm_apply]; exact hyy
  · rw [hform, co.apply_symm_apply, ← hconj, hxy, map_one]
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform, co.apply_symm_apply]
    exact (hL _ hz).1
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform]
    change _ • co (co.symm y) ∈ Λ
    rw [co.apply_symm_apply]
    exact (hL _ hz).2

end GlobalTheory.HypPairSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPlaceDenominatorUnramifiedTraceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl (F := F)) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  first | exact @GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | exact GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | (intros; apply GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatProductDepthPeriodicGcdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatProductDepthPeriodic_gcd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ), DepthOK S t Φ β e k → DepthOK S t Φ β e k' → DepthOK S t Φ β e (Nat.gcd k k') := by
  first | exact @GlobalTheory.DepthUnf.depthOK_gcd | exact GlobalTheory.DepthUnf.depthOK_gcd | (intros; apply GlobalTheory.DepthUnf.depthOK_gcd <;> assumption)
end

