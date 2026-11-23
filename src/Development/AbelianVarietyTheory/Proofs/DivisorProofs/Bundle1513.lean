module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurface
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutside
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem alpha_unrAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) → GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j) w := by
  intro D T L sc G μ₀ hL t i j w hS hQ
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hS (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : (L.xiH t).UnrAt w := by
    by_contra hc
    rcases (hL.Q_ram t _).1 hc with h | ⟨P, h, hc'⟩
    · exact hQ _ h rfl
    · exact hQ P h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have h1 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 hmu
  have h2 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 hxi
  have h3 := (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  have h4 : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (L.eta ^ n) w := fun n => by
    induction n with
    | zero => rw [pow_zero]; exact fun _ _ => Units.ext rfl
    | succ n ih => rw [pow_succ]; exact ih.mul h3
  exact (h1.mul h2).mul (h4 _)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixUnitaryGroupPreservesGram
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchUnit

theorem gram_archM : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ g : GA D V, gram τ (-(V.gram)ᵀ) (archM V θ g) = (-(V.gram)ᵀ).map τ := by
  intro D V τ θ hθ g
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  have hu := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram τ
    (fun x => IsCMField.complexEmbedding_complexConj D.host.E τ x) θ hθ g
  have hm : archM V θ g = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram θ g := rfl
  rw [hm]
  have h' := congrArg Matrix.transpose hu
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h'
  have hG : (-(V.gram)ᵀ).map τ = -(V.gram.map τ)ᵀ := by
    ext a b
    simp
  have hg : ∀ (G : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
    intro G x
    ext a b
    simp only [gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hg, hG, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc]
  exact h'

end GlobalTheory.ArchUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHilbertSamuelBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem geoBound_of_quoted' : Quoted → GeoBound := fun hQ =>
  _root_.GlobalTheory.HSShortTop.geoBound_of_abstract hQ (_root_.GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel hQ) (GlobalTheory.HeightTieProof.heightTie GlobalTheory.HSShort.htMul) _root_.GlobalTheory.HSShort.SlopeTop.slopeBound

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutside
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem beta_unrAt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (beta G i j) w := by
  intro D T L sc G μ₀ hL i j w hw
  have hi := i.2
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := by omega
  have hχ : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hw)
  have hη : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) L.eta w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  have hp : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (L.eta ^ n) w := fun n x hx =>
    (map_pow Circle.toUnits _ n).trans
      (show GlobalTheory.LFun.locChar (F := D.host.F) (E := D.host.E) L.eta w x ^ n = 1 by rw [hη x hx, one_pow])
  exact hχ.mul (hp _)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem hatId_mul_of_mem_OhE (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ OhE D)
    (hy : y ∈ hatId D 𝔪) : x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, (OhE D).mul_mem hx hs, by ring⟩
  | zero => simp
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

def blockUpperSub (R : Type) [CommRing R] (N a : ℕ) : Subalgebra R (Matrix (Fin N) (Fin N) R) where
  carrier := {A | ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0}
  mul_mem' {A B} hA hB i j hj hi := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [hA i l hl hi, zero_mul]
    · rw [hB l j hj (not_lt.1 hl), mul_zero]
  add_mem' {A B} hA hB i j hj hi := by simp [hA i j hj hi, hB i j hj hi]
  algebraMap_mem' r i j hj hi := by
    have : i ≠ j := fun e => by subst e; omega
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne this]

theorem blockUpper_of_mul_eq_one {R : Type} [CommRing R] {N a : ℕ} {A B : Matrix (Fin N) (Fin N) R}
    (hAB : A * B = 1) (hA : ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0) :
    ∀ i j : Fin N, j.1 < a → a ≤ i.1 → B i j = 0 := by
  have hA' : A ∈ blockUpperSub R N a := hA
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set p := A.charpoly
  have hq : Polynomial.aeval A p.divX ∈ blockUpperSub R N a :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hA') (Polynomial.aeval_mem_adjoin_singleton R _)
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add p, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
  have h2 : p.coeff 0 • B = -Polynomial.aeval A p.divX := by
    have := congrArg (fun M => B * M) hCH
    simp only [mul_add, ← mul_assoc, hBA, one_mul, mul_zero, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      mul_one] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  have hB : B ∈ blockUpperSub R N a := by
    have hu : ((-1) ^ Fintype.card (Fin N) * B.det) * p.coeff 0 = 1 := by linear_combination hdet
    have : B = ((-1) ^ Fintype.card (Fin N) * B.det) • (p.coeff 0 • B) := by rw [smul_smul, hu, one_smul]
    rw [this, h2]
    exact Subalgebra.smul_mem _ (neg_mem hq) _
  exact hB

def blockLevelSub (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) where
  carrier := blockSet D 𝔪 a N
  one_mem' := by
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hij : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hij]
  mul_mem' {x y} hx hy := by
    have hX := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hY := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [mul_comm]; exact hatId_mul_of_mem_OhE D 𝔪 (hY l j).1 (hx.2 i l hl hi)
    · exact hatId_mul_of_mem_OhE D 𝔪 (hX i l).1 (hy.2 l j hj (not_lt.1 hl))
  inv_mem' {x} hx := by
    refine ⟨inv_mem hx.1, fun i j hj hi => ?_⟩
    have hI := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    let J : Ideal (OhE D) :=
      { carrier := {z | (z : AE D) ∈ hatId D 𝔪}
        add_mem' := fun {u v} hu hv => by simpa using add_mem hu hv
        zero_mem' := by simp
        smul_mem' := fun c z hz => by simpa using hatId_mul_of_mem_OhE D 𝔪 c.2 hz }
    let M : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).1⟩
    let M' : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).2⟩
    have hMM : M * M' = 1 := by
      have hinj : Function.Injective fun A : Matrix (Fin N) (Fin N) (OhE D) => A.map (OhE D).subtype :=
        fun A B e => by
          ext i j
          exact congrFun (congrFun e i) j
      apply hinj
      change (M * M').map (OhE D).subtype = (1 : Matrix (Fin N) (Fin N) (OhE D)).map (OhE D).subtype
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have e1 : M.map (OhE D).subtype = ((x : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      have e2 : M'.map (OhE D).subtype =
          (((x : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      rw [e1, e2, Units.mul_inv]
    have hred := blockUpper_of_mul_eq_one (a := a) (A := M.map (Ideal.Quotient.mk J))
      (B := M'.map (Ideal.Quotient.mk J))
      (by rw [← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i j hj hi => by
        rw [Matrix.map_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hx.2 i j hj hi)) i j hj hi
    rw [Matrix.map_apply] at hred
    have hm := Ideal.Quotient.eq_zero_iff_mem.1 hred
    exact hm

theorem blockJ_mem_iff_blockSet : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) (h : GA D N),
    h ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 a N ↔ h ∈ GlobalTheory.BotPairSmall.blockSet D 𝔪 a N := by
  intro D 𝔪 a N h
  constructor
  · intro hh
    exact (Subgroup.closure_le (blockLevelSub D 𝔪 a N)).2 (fun _ hx => hx) hh
  · intro hh
    exact Subgroup.subset_closure hh

end GlobalTheory.BotPairSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiGridVertexRankAddLtTwoExponentAddCentre
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChiGrid

theorem rankV_add_lt_two_e_add_two_cen {D : D7} (C : ℝ) (τ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) :
    ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) < 2 * (D.hc τ).e ⟨j, hj⟩ + 2 * (cen D C τ (D.R.m - i) : ℚ) := by
  set P := D.hc τ with hP
  set G := GlobalTheory.SignedHC.GridData.ofHCParam P (sLen D) (gap D C) 0 with hG
  obtain ⟨hv, hb, -⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec P (sLen D) (gap D C) 0
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGga : G.ga = gap D C := rfl

  have h1 := P.gap_be ⟨j, hj⟩

  have e0 : P.b ⟨0, by omega⟩ = (G.b 1 : ℚ) := hb ⟨0, by omega⟩
  have ej : P.b ⟨j, hj⟩ = (G.b (j + 1) : ℚ) := hb ⟨j, hj⟩
  have h2 : P.b ⟨0, by omega⟩ ≤ P.b ⟨j, hj⟩ := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact le_rfl
    · have := G.b_mono 1 (j + 1) le_rfl (by omega) (by rw [hGm]; omega)
      rw [e0, ej]; exact_mod_cast this.le

  have hu2 := P.u_last_gt (by omega) (by omega)
  have hu1 := P.v_gt_u ⟨D.R.k - 2, by omega⟩
  have hu : P.u ⟨D.R.k - 2 + 1, by omega⟩ = P.u ⟨D.R.k - 1, by omega⟩ :=
    congrArg P.u (Fin.ext (by dsimp only; omega))
  have ev0 : P.v ⟨0, by omega⟩ = (G.v 2 : ℚ) := hv ⟨0, by omega⟩
  have evl : P.v ⟨D.R.k - 2, by omega⟩ = (G.v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    dsimp only at this
    rwa [Nat.sub_add_cancel (by omega : 2 ≤ D.R.k)] at this
  have hvv : G.v D.R.k < G.v 2 := G.v_anti 2 D.R.k le_rfl (by omega) (by rw [hGk])
  have hvv' : (G.v D.R.k : ℚ) < G.v 2 := by exact_mod_cast hvv
  rw [hu] at hu1
  rw [evl] at hu1

  have hc : G.mid (D.R.m - i) < (cen D C τ (D.R.m - i) : ℚ) + 1 := Int.lt_floor_add_one _
  have hmid : G.mid (D.R.m - i) = G.a (D.R.m - i) + G.ga / 2 := G.mid_eq (by omega)
  have ha : G.a (D.R.m - i) = (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * (gap D C : ℚ) := by
    simp only [GlobalTheory.SignedHC.GridData.a, hGm, hGga]
    rw [Nat.cast_sub hi.le]; ring
  rw [hmid, ha, hGga] at hc

  have hg := (isLeast_gap D C).1.2.1
  have hN : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Formalism.BasicNotions.Ranks.r; omega
  have m1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
  have m3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have m4 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have hrank : rankV D (i + 1) (j + 1) + rankV D i j ≤ 2 * bigN D := by
    unfold rankV bigN; nlinarith
  have hR : rankV D (i + 1) (j + 1) + rankV D i j + 1 ≤ gap D C := by omega
  have hR' : ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) + 1 ≤ (gap D C : ℚ) := by exact_mod_cast hR
  have hpos : (0 : ℚ) ≤ (i : ℚ) * (gap D C : ℚ) := by positivity
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h0 : (0 : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by positivity
  nlinarith

end GlobalTheory.ChiGrid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondESupConj
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem condE_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), condE P ⊔ D.host.conj • condE P = ⊤ := by
  intro D T L P
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hne : ∀ v ∈ P.S0, ∀ v' ∈ P.S0, (P.w v).asIdeal ≠ D.host.conj • (P.w v').asIdeal := by
    intro v hv v' hv' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv (P.w v') (P.w v) := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    by_cases e : v' = v
    · subst e
      obtain ⟨f, hf⟩ := P.w_split v' hv'
      exact GlobalTheory.GridChars.not_conjPl_self hf hcc hc
    · apply e
      have h1 := (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D)
        (P.w v') (P.w v)).2 (Or.inr hc)
      rw [P.under_w hv, P.under_w hv'] at h1
      exact h1.symm
  have hmax' : ∀ v, (D.host.conj • (P.w v).asIdeal).IsMaximal := by
    intro v
    have := (P.w v).isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v).ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  rw [condE, Finset.smul_prod']
  simp only [smul_pow']
  refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun v' hv' => ?_
  exact Ideal.pow_sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal (hmax' v') (hne v hv v' hv'))

end GlobalTheory.FunObj.SqNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverWithDualNumberDerivationsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_with_dual_number_derivations : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  first | exact @GlobalTheory.CompHS.exists_derivFrame | exact GlobalTheory.CompHS.exists_derivFrame | (intros; apply GlobalTheory.CompHS.exists_derivFrame <;> assumption)
end

