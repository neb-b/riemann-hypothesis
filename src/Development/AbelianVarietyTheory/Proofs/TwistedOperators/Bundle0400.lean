module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalHeckeMatrixIntermediateLattice
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFockIntertwinerAdjointExchangedPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl UA)
open Formalism.L2.Theta (GA GfC finHom frameMat)
open Formalism.IndefR.Lev (EAf finE)
open Formalism.IndefR.Datum (IsSelfDualC)
open Formalism.UG (cT hform)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsomCorrection

section Algebra

variable {A : Type} [CommRing A] (σ : A →+* A)

theorem cT_mul_rect {l m n : ℕ} (M : Matrix (Fin l) (Fin m) A) (N : Matrix (Fin m) (Fin n) A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  rw [cT, Matrix.map_mul, transpose_mul]
  rfl

theorem gram_of_form {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x : Matrix (Fin m) (Fin n) A)
    (h : ∀ i j, hform σ J' (x *ᵥ Pi.single i 1) (x *ᵥ Pi.single j 1) = J i j) :
    cT σ x * J' * x = J := by
  ext i j
  rw [← h i j]
  simp only [hform, mulVec_single_one, Matrix.mul_apply, cT, transpose_apply, map_apply, col_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

theorem exists_unitary {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) (y' : Matrix (Fin n) (Fin m) A) (h1 : y * y' = 1) (h2 : y' * y = 1)
    (hb : Function.Surjective x.mulVec) (hx : cT σ x * J' * x = J) (hy : cT σ y * J' * y = J) :
    ∃ g : GL (Fin m) A, cT σ g.1 * J' * g.1 = J' ∧ g.1 * y = x := by
  have hu : IsUnit (x * y') := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w, rfl⟩ := hb v
    exact ⟨y *ᵥ w, by rw [mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [hu.unit_spec, cT_mul_rect]
    have e : cT σ y' * cT σ y = 1 := by
      rw [← cT_mul_rect, h1, cT, Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    calc cT σ y' * cT σ x * J' * (x * y') = cT σ y' * (cT σ x * J' * x) * y' := by simp only [Matrix.mul_assoc]
      _ = (cT σ y' * cT σ y) * J' * (y * y') := by rw [hx, ← hy]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [e, h1, Matrix.one_mul, Matrix.mul_one]
  · rw [hu.unit_spec, Matrix.mul_assoc, h2, Matrix.mul_one]

end Algebra

variable {D : D7}

theorem exists_finE (V : HSp D) (g : GL (Fin V.rank) (EAf D)) (hg : g ∈ UA D.sp.cm V.gram) :
    ∃ k ∈ GfC V, finE V k = g := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨g, hg⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, ?_⟩
  have e := congrArg Subtype.val hb
  have e2 := GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram b
  refine Eq.trans ?_ (e2.symm.trans e)
  exact congrArg (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)) k2

theorem mA_mul (X Y Z : HSp D) (f : X.V →ₗ[D.host.E] Y.V) (g : Y.V →ₗ[D.host.E] Z.V) :
    mA Z Y g * mA Y X f = mA Z X (g.comp f) := by
  rw [mA, mA, mA, ← Matrix.map_mul, frameMat, frameMat, frameMat, LinearMap.toMatrix_comp X.frame Y.frame Z.frame]

theorem mA_id (X : HSp D) : mA X X LinearMap.id = 1 := by
  rw [mA, frameMat, LinearMap.toMatrix_id, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem vA_frame (X : HSp D) (i : Fin X.rank) : vA X (X.frame i) = Pi.single i 1 := by
  funext j
  have : Formalism.L2.Herm.crd X (X.frame i) j = X.frame.repr (X.frame i) j := rfl
  rw [vA, this, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm, RingHom.map_one]
  · rw [if_neg h, if_neg (Ne.symm h), RingHom.map_zero]

theorem gram_mA (Y Y' : HSp D) (f : Y.V →ₗ[D.host.E] Y'.V) (hf : HSpace.IsIsomEmb Y Y' f) :
    HMul.hMul (HMul.hMul (cT (cjA D) (mA Y' Y f)) (Y'.gram.map (inc D))) (mA Y' Y f) = Y.gram.map (inc D) := by
  refine gram_of_form _ _ _ _ fun i j => ?_
  rw [← vA_frame, ← vA_frame, mA_mulVec_vA, mA_mulVec_vA, ← hA_eq, hA_vA, HSpace.hD, hf]
  rfl

theorem correction_of_transport : ∀ D : D7, TransportSt D → CorrectionSt D := by
  intro D hT Y Y' io hio Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  have hr : Y.rank = Y'.rank := by rw [← Y.rank_eq, ← Y'.rank_eq, io.finrank_eq]
  obtain ⟨⟨x, hx⟩, -⟩ := hT Y Y' hr Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  obtain ⟨g, hg, hgx⟩ := exists_unitary (cjA D) (Y'.gram.map (inc D)) (Y.gram.map (inc D)) x
    (mA Y' Y io.toLinearMap) (mA Y Y' io.symm.toLinearMap)
    (by rw [mA_mul, LinearEquiv.comp_symm, mA_id]) (by rw [mA_mul, LinearEquiv.symm_comp, mA_id]) hx.1.1.2
    (gram_of_form _ _ _ _ fun i j => (hx.1.2 _ _).trans (hform_single _ _ i j)) (gram_mA Y Y' _ hio)
  obtain ⟨k, hk, e⟩ := exists_finE Y' g hg
  refine ⟨k, hk, ?_⟩
  rw [e, hgx]
  exact hx

end GlobalTheory.AdIsomCorrection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceHermitian
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChooseHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def scaleSpc {d : ℕ} (V : Spc F E d) (δ : E) : Spc F E d where
  J := δ • V.J
  L := V.L
  θ := V.θ
  bas := V.bas

theorem incM_smul {d : ℕ} (δ : E) (J : Matrix (Fin d) (Fin d) E) :
    incM F (δ • J) = inclR (F := F) (AF F) δ • incM F J := by
  ext i j
  simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]

theorem dbl_smul {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (X : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : dbl (c • X) = c • dbl X := by
  simp [dbl, Matrix.fromBlocks_smul, smul_neg]

end GlobalTheory.SplitChooseHerm

namespace GlobalTheory.SplitChooseHerm

theorem exists_admissible_unipotent_split_place_hermitian : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  intro _ F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, S, hS, hSe⟩ := GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary σ B V r s hB hV v hv hψ
  obtain ⟨δ, hδ, u, hu⟩ := GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace σ hB.cm v π₁ hP.2.2.1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((u : v.adicCompletionIntegers F) : Fv F v) = 0 := by rw [hu, map_zero, map_zero]
    exact u.ne_zero (Subtype.ext h0)
  have hcu : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ0, map_one]
  have h2' : IsUnit (2 : v.adicCompletionIntegers F) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h2
    rwa [map_ofNat] at this
  let W' : Spc F E d := scaleSpc V δ
  have hskew : ∀ i j, σ (W'.J j i) = -W'.J i j := by
    intro i j
    show σ (δ * V.J j i) = -(δ * V.J i j)
    rw [map_mul, hδ, hV.herm]
    ring
  have hS' : ∃ S' : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S'.det ∧
      S'.map (fun x => (x : Fv F v)) =
        (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W'.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    refine ⟨(u : v.adicCompletionIntegers F) • S, ?_, ?_⟩
    · rw [Matrix.det_smul]
      exact (u.isUnit.pow _).mul hS
    · have e1 : (incM F W'.J).map π₁ = π₁ (inclR (F := F) (AF F) δ) • (incM F V.J).map π₁ := by
        show (incM F (δ • V.J)).map π₁ = _
        rw [incM_smul]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply]
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, ← hSe, ← hu]
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply]
  let g' : GlobalTheory.DblVac.UD σ W' := ⟨g.1, by
    have h := g.2
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F V.J) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F V.J) at h
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F (δ • V.J)) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F (δ • V.J))
    rw [incM_smul, dbl_smul, Matrix.mul_smul, Matrix.smul_mul, h]⟩
  have hg' : g' ∈ GlobalTheory.DblVac.KD σ W' v := hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ :=
    GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt _root_.GlobalTheory.exists_dual_pair_isUnit_det_blocks σ W' v hskew h2' π₁ π₂ b₁ b₂ hP hS' g' hg'
  refine ⟨Y, hYat, hYlat, ?_, M, hM, hMlat⟩
  change Yᵀ * incM F (δ • V.J) + incM F (δ • V.J) * Y.map (cA σ) = 0 at hYadm
  rw [incM_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hYadm
  have h3 := congrArg (fun X => inclR (F := F) (AF F) δ⁻¹ • X) hYadm
  simp only [smul_smul, hcu, one_smul, smul_zero] at h3
  exact h3

end GlobalTheory.SplitChooseHerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjScale


open Classical in
noncomputable def forestLift {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (w : Fin r → Fin r → G) (j : Fin r) : G :=
  if h : ∃ i, Ed i j then forestLift Ed hlt w (Classical.choose h) * w (Classical.choose h) j else 1
termination_by j.val
decreasing_by all_goals (try simp_wf); exact hlt _ _ (Classical.choose_spec h)

theorem forestLift_edge {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (huniq : ∀ i i' j, Ed i j → Ed i' j → i = i') (w : Fin r → Fin r → G) {i j : Fin r} (h : Ed i j) :
    (forestLift Ed hlt w i)⁻¹ * forestLift Ed hlt w j = w i j := by
  have hex : ∃ i, Ed i j := ⟨i, h⟩
  have hc : Classical.choose hex = i := huniq _ _ _ (Classical.choose_spec hex) h
  have e : forestLift Ed hlt w j = forestLift Ed hlt w i * w i j := by
    rw [forestLift, dite_eq_left hex, hc]
  rw [e, inv_mul_cancel_left]

theorem symEdge_lt {r : ℕ} (ρ k : ℕ) : ∀ i j : Fin r, symEdge ρ k i j → i < j := by
  intro i j h
  show i.val < j.val
  unfold symEdge at h
  omega

theorem symEdge_uniq {r : ℕ} (ρ k : ℕ) : ∀ i i' j : Fin r, symEdge ρ k i j → symEdge ρ k i' j → i = i' := by
  intro i i' j h h'
  apply Fin.ext
  unfold symEdge at h h'
  omega

theorem scale_conj : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  intro κf _ _ hF r ρ k ψ' ψ0 h1 h0 a
  let _ : Field κf := hF.toField
  have := Fintype.ofFinite κf
  have hprim : ψ0.IsPrimitive := AddChar.IsPrimitive.of_ne_one h0
  have hinj : Function.Injective ψ0.mulShift := AddChar.to_mulShift_inj_of_isPrimitive hprim
  have hbij : Function.Bijective ψ0.mulShift := by
    classical
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, (AddChar.card_eq).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1
    rw [← hc]
    exact AddChar.mulShift_zero ψ0
  let w : Fin r → Fin r → κfˣ := fun i j => Units.mk0 c hc0 * a i j
  refine ⟨forestLift (symEdge ρ k) (symEdge_lt ρ k) w, fun u _ => ?_⟩
  rw [← hc, AddChar.mulShift_apply]
  congr 1
  unfold edgeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [diagGL_conj_apply]
    have e := congrArg Units.val (forestLift_edge (symEdge ρ k) (symEdge_lt ρ k) (symEdge_uniq ρ k) w h)
    rw [Units.val_mul] at e
    have e2 : (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
        ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf) = c * (a i j : κf) := by
      rw [e]; rfl
    symm
    calc (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) * u.val i j *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)
        = ((((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)) * u.val i j := by ring
      _ = c * ((a i j : κf) * u.val i j) := by rw [e2]; ring
  · rw [mul_zero]

end GlobalTheory.SeeConjScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementIdempotentPartSplitPlaceLattic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLocLift
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem exists_hecke_ePart : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ ∀ v ∈ latG V g,
      (finPart D e • finVec V v ∈ latGHat V (g * a₀) ↔
        finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  intro D V P e ϖ k g M he hϖ1 hϖ2 hPM hMΛ hidx
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨t, ht, hch⟩ := _root_.GlobalTheory.EPartChart.latGHat_chart D V e v π s B he.1.1 h2 h3 h4 hB
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V g
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) (latG V g) := isNoetherian_of_fg_of_noetherian _ hfg
    have hc := (IsNoetherian.noetherian (M.comap (latG V g).subtype)).map (latG V g).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin V.rank → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ hsp).symm.le.trans (Submodule.span_mono hPM))
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.HatLocalChart.exists_chart D e v π s V.rank M he.1.1 h2 h3 h4 hMfg hMsp
  have hT : ∀ y : Fin V.rank → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ↔
      ∀ i, ((t • (GlobalTheory.SplitPlace.comp V π B g⁻¹ * B⁻¹).1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
    intro y
    rw [← hhat, Units.val_mul]
    exact hch g y
  obtain ⟨Z, hZ1, hZ2, hZ3, hZM⟩ := _root_.GlobalTheory.HeckeLocMatrix.exists_local_matrix D P e ϖ k V.rank v π s (latG V g) M t _ C he hϖ1 hϖ2
    h1 h2 h3 h4 h5 hfg hsp hPM hMΛ hidx ht hT hC
  obtain ⟨a₀, hsupp, hcomp⟩ := (GlobalTheory.SplitPlace.comp_bij (V := V) (B := B) he.1 h1 h2).1 Z
  have hu := GlobalTheory.SplitPlace.isUnif he h4 h5 ϖ hϖ1 hϖ2
  have hϖ0 := (GlobalTheory.SplitPlace.unif_facts hu).1
  refine ⟨a₀, (GlobalTheory.SplitPlace.hecke_iff he.1 h1 h2 h3 h4 hB hϖ0 k a₀).2 ⟨hsupp, ?_, ?_, ?_⟩, fun w _ => ?_⟩
  · rw [hcomp]; exact hZ1
  · rw [hcomp]; exact hZ2
  · rw [hcomp]; exact hZ3
  · rw [hch, hZM]
    have : (GlobalTheory.SplitPlace.comp V π B (g * a₀)⁻¹).1 = (Z⁻¹).1 * (GlobalTheory.SplitPlace.comp V π B g⁻¹).1 := by
      rw [mul_inv_rev, map_mul, map_inv, hcomp, Units.val_mul]
    rw [this, Units.val_mul, Matrix.mul_assoc, Matrix.mul_smul]

end GlobalTheory.HeckeLocLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_itW : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (V W : HSp D)
    (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → (∀ τ, UpPair t (S τ) (S' τ) (aS τ) (aT τ)) →
    (∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω →
      GlobalTheory.Chain.IsVacVec ψ θ M M' f → IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It) ∧
    ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ W V aT aS ω →
      GlobalTheory.Chain.IsVacVec ψ θ M' M f → IsItW θ M' M ω (GlobalTheory.Chain.ptOf ψ θ M' M f) It := by
  intro hDS hHC D t V W S S' M M' aS aT θ ψ hθ hP
  obtain ⟨X, hX, h1, h2, -⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
  have hB := _root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd e1 e2
  choose hr A hA using key
  refine ⟨?_, ?_⟩
  · obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.ContrObj.contraction.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA
    refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
    have hv := fun τ => _root_.GlobalTheory.VacuumCharacter.vacChar D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
    exact isItW_of_globIt hθ hI hr (_root_.GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
      fun τ => (hv τ).2.2
  · have hA' : ∀ τ, ∃ A', LocIt M' M τ (aT τ) (aS τ) A' := fun τ =>
      _root_.GlobalTheory.AdjLocIt.adj_locIt D V W _ _ M M' τ _ _ (A τ) (hA τ)
    choose A' hA' using hA'
    obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D W V _ _ M' M aT aS A' GlobalTheory.ContrObj.contraction.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA'
    refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
    have hv := fun τ => _root_.GlobalTheory.VacuumCharacter.vacChar D W V _ _ M' M θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
    exact isItW_of_globIt hθ hI (fun τ => ⟨(hr τ).2, (hr τ).1⟩)
      (_root_.GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D W V _ _ M' M ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1) fun τ => (hv τ).2.2

end GlobalTheory.EvenOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
section
set_option autoImplicit false

namespace GlobalTheory.HeckePointLaw

theorem heckePointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws :=
  heckePointLaws_of_transport _root_.GlobalTheory.ThetaTransport.thetaTransportLaw

end GlobalTheory.HeckePointLaw
end

