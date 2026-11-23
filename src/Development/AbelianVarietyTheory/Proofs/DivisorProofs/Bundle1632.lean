module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLattices
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLatticesStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f : WO S T → ℂ),
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT f →
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  first | exact @GlobalTheory.VacMove.isVacO_move | exact GlobalTheory.VacMove.isVacO_move | (intros; apply GlobalTheory.VacMove.isVacO_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryAdelicMatrixConjOrthonormalFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem sg_one_tmul (c : E ≃ₐ[F] E) (e : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c e := by
  simp [sg, Algebra.TensorProduct.map_tmul]

theorem fm_map_sg (c : E ≃ₐ[F] E) (A : Matrix (Fin n) (Fin n) E) :
    (fm F A).map (sg (FiniteAdeleRing (𝓞 F) F) c) = fm F (A.map c) := by
  ext i j
  simp only [fm, Matrix.map_apply, sg_one_tmul]

theorem hermA_eq_dot (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c H x y = x ⬝ᵥ (fm F H *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  simp only [hermA, dotProduct, Matrix.mulVec, fm, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermA_mulVec (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (RA F E))
    (x y : Fin n → RA F E) :
    hermA c H (M *ᵥ x) (M *ᵥ y) =
      x ⬝ᵥ ((Mᵀ * fm F H * M.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  rw [hermA_eq_dot]
  have h1 : (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((M *ᵥ y) b)) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b) := by
    funext b
    exact RingHom.map_mulVec (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom M y b
  rw [h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem sg_single (c : E ≃ₐ[F] E) (j : Fin n) :
    (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((Pi.single j (1 : RA F E) : Fin n → RA F E) b)) = Pi.single j 1 := by
  funext b
  by_cases h : b = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem mat_eq_of_dot (c : E ≃ₐ[F] E) {K K' : Matrix (Fin n) (Fin n) (RA F E)}
    (h : ∀ x y : Fin n → RA F E, x ⬝ᵥ (K *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) =
      x ⬝ᵥ (K' *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b))) : K = K' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [sg_single] at this
  simpa [Matrix.mulVec_single_one] using this

theorem gram_of_isUnA (c : E ≃ₐ[F] E) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    gᵀ * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) = 1 := by
  have h := mat_eq_of_dot c (K := gᵀ * fm F 1 * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) (K' := fm F 1)
    fun x y => by rw [← hermA_mulVec, ← hermA_eq_dot]; exact hg x y
  rwa [GlobalTheory.UnRep.FullReps.fm_one, Matrix.mul_one] at h

end General

end GlobalTheory.UnitConjFrame

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem map_mul_sg (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) (RA F E)) :
    (M * N).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) * N.map (sg (FiniteAdeleRing (𝓞 F) F) c) :=
  Matrix.map_mul (f := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom)

theorem map_mul_c (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) E) :
    (M * N).map c = M.map c * N.map c :=
  Matrix.map_mul (f := (c : E →+* E))

theorem fm_transpose (A : Matrix (Fin n) (Fin n) E) : (fm F A)ᵀ = fm F Aᵀ := by
  ext i j; rfl

theorem isUnA_conj (c : E ≃ₐ[F] E) (A B G : Matrix (Fin n) (Fin n) E) (hAB : A * B = 1)
    (h : Aᵀ * Gᵀ * A.map c = 1) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    IsUnA c Gᵀ (fm F A * g * fm F B) := by
  have hg' := gram_of_isUnA c hg
  have hB : Bᵀ * B.map c = Gᵀ := by
    have e1 : Bᵀ * B.map c = Bᵀ * (Aᵀ * Gᵀ * A.map c) * B.map c := by rw [h, Matrix.mul_one]
    rw [e1, ← Matrix.transpose_transpose Gᵀ]
    have e2 : (A * B).map c = A.map c * B.map c := map_mul_c c A B
    rw [hAB, Matrix.map_one _ (map_zero c) (map_one c)] at e2
    calc Bᵀ * (Aᵀ * Gᵀᵀᵀ * A.map c) * B.map c = (A * B)ᵀ * Gᵀᵀᵀ * (A.map c * B.map c) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Gᵀᵀᵀ := by rw [hAB, ← e2, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hM : (fm F A * g * fm F B)ᵀ * fm F Gᵀ * (fm F A * g * fm F B).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      fm F Gᵀ := by
    rw [map_mul_sg, map_mul_sg, fm_map_sg, fm_map_sg, Matrix.transpose_mul, Matrix.transpose_mul,
      fm_transpose, fm_transpose]
    have e3 : fm F Aᵀ * fm F Gᵀ * fm F (A.map c) = 1 := by
      rw [← GlobalTheory.UnRep.FullReps.fm_mul, ← GlobalTheory.UnRep.FullReps.fm_mul, h, GlobalTheory.UnRep.FullReps.fm_one]
    calc _ = fm F Bᵀ * (gᵀ * (fm F Aᵀ * fm F Gᵀ * fm F (A.map c)) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *
            fm F (B.map c) := by simp only [Matrix.mul_assoc]
      _ = fm F Gᵀ := by
          rw [e3, Matrix.mul_one, hg', Matrix.mul_one, ← GlobalTheory.UnRep.FullReps.fm_mul, hB]
  intro x y
  rw [hermA_mulVec, hM, hermA_eq_dot]

end General

end GlobalTheory.UnitConjFrame

theorem GlobalTheory.UnitConjFrame.isUnA_frame_conj : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g →
    GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) V.gramᵀ (GlobalTheory.UnRep.fm D.host.F fr.1 * g * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1) := by
  intro D V fr g hfr hg
  refine GlobalTheory.UnitConjFrame.isUnA_conj (GlobalTheory.Member.cF D) fr.1 (fr⁻¹).1 V.gram (Units.mul_inv fr) ?_ hg
  have h := congrArg Matrix.transpose hfr
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one] at h
  rw [← h, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.mul_assoc]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMovedRiggingIsStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometryMovedRigging_is : ∀ {D : D7} {S S' : HSp D} (I : GlobalTheory.Mem.Isom.IsoMat S S') (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig S), r.Is → (GlobalTheory.TriMove.rigMove I r).Is := by
  first | exact @GlobalTheory.TriMove.rigMove_is | exact GlobalTheory.TriMove.rigMove_is | (intros; apply GlobalTheory.TriMove.rigMove_is <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirst
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamPet

open scoped ENNReal

theorem log_le_of_sq_le {A B : ℝ≥0∞} {K L : ℝ} (hL : 0 < L) (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hA0 : A ≠ 0)
    (h : A ^ 2 ≤ ENNReal.ofReal K * B ^ 2) :
    0 < L * B.toReal ∧ Real.log (L * A.toReal) ≤ 1 / 2 * Real.log K + Real.log (L * B.toReal) := by
  have hApos : 0 < A.toReal := ENNReal.toReal_pos hA0 hA
  have hK0 : 0 ≤ K := by
    by_contra hK
    rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hK)), zero_mul] at h
    exact hA0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h zero_le))
  have h2 : A.toReal ^ 2 ≤ K * B.toReal ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB)) h
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_pow] at this
  have hB0 : 0 < B.toReal := by
    rcases (ENNReal.toReal_nonneg (a := B)).lt_or_eq with hb | hb
    · exact hb
    · rw [← hb] at h2; nlinarith
  have hKpos : 0 < K := by
    by_contra hK
    have : K * B.toReal ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hK) (sq_nonneg _)
    nlinarith
  refine ⟨mul_pos hL hB0, ?_⟩
  rw [Real.log_mul hL.ne' hApos.ne', Real.log_mul hL.ne' hB0.ne']
  have h3 : Real.log (A.toReal ^ 2) ≤ Real.log (K * B.toReal ^ 2) := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul hKpos.ne' (by positivity), Real.log_pow] at h3
  push_cast at h3
  linarith

theorem mean_log_petersson_ge : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 → (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧ -lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) / (Module.finrank ℚ c.F : ℝ) := by
  intro hM hT D j H Dw l Xo c U dict hL _ χ hχ a n hD F hF hF0
  have hFc : (F : Rul Xo c) ∈ cusp Xo c U a n := cuspW_wtZ (Xo := Xo) (c := c) (U := U) a n ▸ F.2
  have hF0' : (F : Rul Xo c) ≠ 0 := fun h => hF0 (Subtype.ext h)
  have hsup := _root_.GlobalTheory.lamSup_of_laws D j H Dw l Xo c U dict hL χ hχ a n hD _ hFc hF hF0'
  have hsl := _root_.GlobalTheory.supPet_principal hM hT D j H Dw l Xo c U dict hL
  have hsp := _root_.GlobalTheory.LamSpread.sum_spread_laU_le D j H Dw l Xo c U dict hL
  have hdef : Formalism.L2.Pj.SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp _ H Dw l Xo c _ _ hL.unf)
  set x := xiR D
  set K := supConst D.host.E D.R.r D.host.d l.M
    (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) with hK
  have hper : ∀ σ : c.F →+* ℂ, 0 < normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F ∧
      Real.log (supC Xo c U x (goodOf c σ) a n F) ≤
        1 / 2 * Real.log K + Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    intro σ
    have hσ : GoodEmb c (goodOf c σ) := Formalism.L2.PjFree.goodEmb_goodOf c σ
    have hhol := ((mem_cusp Xo c U a n _).1 hFc).2 _ hσ
    have hw : (0 : ℝ) < ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 := by positivity
    have hb := hsl _ hσ (laU (U (goodOf c σ)) a n) _ hw
      (fun k => (hsp _ hσ a n k).trans (by linarith)) (hL.chiTriv _ hσ a n hD) _ hhol
    have hne0 : supE (U (goodOf c σ)).X (laU (U (goodOf c σ)) a n) (rdU (U (goodOf c σ)) F) ≠ 0 := by
      intro h0
      refine hF0' (hdef a n hD _ hσ _ hFc ?_)
      unfold supN; rw [h0, ENNReal.toReal_zero]
    have hfin := supE_cusp_ne_top hσ hFc
    obtain ⟨_, _, _, _, _, hdu, _⟩ := hL.dictU _ hσ
    have hpfin : petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
        (rdU (U (goodOf c σ)) F) ≠ ⊤ :=
      petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hhol
    have key := log_le_of_sq_le (lieFac_pos Dw x a) hfin hpfin hne0 hb
    have e : normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F = lieFac Dw x a *
        (petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
          (rdU (U (goodOf c σ)) F)).toReal := by
      show lieFacZ Dw x (wtZ a n) * _ = _
      rw [lieFacZ_wtZ, modelWt_wtZ]
    rw [e]
    exact key
  refine ⟨fun σ => (hper σ).1, ?_⟩
  have hN : (0 : ℝ) < (Module.finrank ℚ c.F : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (Finset.univ : Finset (c.F →+* ℂ)).card = Module.finrank ℚ c.F := by
    rw [Finset.card_univ]; exact NumberField.Embeddings.card c.F ℂ
  have hsum : (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U x (goodOf c σ) a n F)) -
      (Module.finrank ℚ c.F : ℝ) * (1 / 2 * Real.log K) ≤
      ∑ σ : c.F →+* ℂ, Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun σ _ => (hper σ).2
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at this
    linarith
  have e : lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ)
      ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) = lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re
      ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 / 2 * Real.log K := rfl
  rw [e, le_div_iff₀ hN]
  rw [le_div_iff₀ hN] at hsup
  nlinarith

end GlobalTheory.LamPet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistenceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  first | exact @GlobalTheory.LagLocForm.lagr_local_form | exact GlobalTheory.LagLocForm.lagr_local_form | (intros; apply GlobalTheory.LagLocForm.lagr_local_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinMApply
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.ArchPull

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

def linM (D : Matrix κ ι F) :
    (ι → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun a := fun k => ∑ i, mixedEmbedding F (D k i) * a i
  map_add' a b := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by funext k; simp [Finset.smul_sum, mul_smul_comm]

theorem linM_apply (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) (k : κ) :
    linM D a k = ∑ i, mixedEmbedding F (D k i) * a i := rfl

theorem linM_mul (L : Matrix ι κ F) (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) :
    linM L (linM D a) = linM (L * D) a := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linM_apply, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul, map_mul, mul_assoc]
  exact Finset.sum_comm

theorem linM_one (a : ι → mixedEmbedding.mixedSpace F) : linM (1 : Matrix ι ι F) a = a := by
  funext i
  simp [linM_apply, Matrix.one_apply]

theorem exists_leftInv (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0) :
    ∃ L : Matrix ι κ F, L * D = 1 := by
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz; exact hD z (by simpa using hz)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' D, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end GlobalTheory.ArchPull

open GlobalTheory.ArchPull in
theorem GlobalTheory.ArchPull.exists_pull : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ,
      ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i) := by
  intro F _ _ ι κ _ _ D hD
  obtain ⟨L, hL⟩ := exists_leftInv D hD
  let M := LinearMap.toContinuousLinearMap (linM D)
  let N := LinearMap.toContinuousLinearMap (linM L)
  have hb : ∀ a, ‖a‖ ≤ ‖N‖₊ * ‖M a‖ := fun a => by
    have e : N (M a) = a := by
      change linM L (linM D a) = a
      rw [linM_mul, hL, linM_one]
    calc ‖a‖ = ‖N (M a)‖ := by rw [e]
      _ ≤ ‖N‖ * ‖M a‖ := N.le_opNorm _
      _ = _ := rfl
  have hl : AntilipschitzWith ‖N‖₊ M := ContinuousLinearMap.antilipschitz_of_bound M hb
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ M.hasTemperateGrowth hl, fun f a => rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflectionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_double_reflection : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F), (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  first | exact @GlobalTheory.WeylFour.LocInv.fourV_fourV | exact GlobalTheory.WeylFour.LocInv.fourV_fourV | (intros; apply GlobalTheory.WeylFour.LocInv.fourV_fourV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchrodingerIntertwineStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_schrodinger_intertwine : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  first | exact @GlobalTheory.WeylFour.schr_fourV_loc | exact GlobalTheory.WeylFour.schr_fourV_loc | (intros; apply GlobalTheory.WeylFour.schr_fourV_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStableStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_schwartz_stable : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F), (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ],
    (∀ φ ∈ SB (κ → Fv F v), fourV ψ v φ ∈ SB (κ → Fv F v)) ∧
    (∀ φ ∈ SB (κ → Fv F v), ∀ χ ∈ SB (κ → Fv F v), fourV ψ v (φ + χ) = fourV ψ v φ + fourV ψ v χ) ∧
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (κ → Fv F v) := by
  first | exact @GlobalTheory.WeylFour.fourV_sb | exact GlobalTheory.WeylFour.fourV_sb | (intros; apply GlobalTheory.WeylFour.fourV_sb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourierStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_indicator_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F)) (κ : Type) [Fintype κ],
    GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  first | exact @GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | exact GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | (intros; apply GlobalTheory.WeylFour.IndOSelf.indO_self_fourier <;> assumption)
end

