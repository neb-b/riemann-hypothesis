module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamification
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSplitChars
open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem twVal_of_unit (χ : HChar E) (w : ℝ) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) (hk : P.valuation E (k : E) = 1) :
    twVal χ w P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  have h0 : Formalism.L2.Host.ordF P k = 0 := by simp [Formalism.L2.Host.ordF, hk]
  simp [twVal, h0]

theorem isClopen_oneUnits (P : HeightOneSpectrum (𝓞 E)) :
    IsClopen {x : (P.adicCompletion E)ˣ | Valued.v ((x : P.adicCompletion E) - 1) < 1} := by
  have := (Valued.isClopen_ball (P.adicCompletion E) (r := 1)).preimage
      (f := fun x : (P.adicCompletion E)ˣ => (x : P.adicCompletion E) - 1)
      ((Units.continuous_val (M := P.adicCompletion E)).sub continuous_const)
  convert this using 1
  ext x
  simp

theorem tameAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E ((u : E) - 1) < 1 → χ.locK P u = 1) : χ.TameAt P := by
  have key : ∀ x : (P.adicCompletion E)ˣ, Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1 := by
    intro x
    refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on
      (p := fun x => Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1) x ?_ fun k hk => h k ?_
    · exact isClosed_imp (isClopen_oneUnits P).2
        (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)
    · have e : ((atFin P k : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 =
          algebraMap E (P.adicCompletion E) ((k : E) - 1) := by
        rw [map_sub, map_one]; rfl
      rwa [e, Formalism.UG.P.levelaf_valued_algebraMap] at hk
  intro x _ hx
  refine key x (lt_of_le_of_lt hx ?_)
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 (by norm_num)

theorem locK_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ)
    (hk : P.valuation E (k : E) = 1) : ((χ'.locK P k : ℂˣ) : ℂ) = s ((χ.locK P k : ℂˣ) : ℂ) := by
  have := h P k
  rwa [twVal_of_unit _ _ _ _ hk, twVal_of_unit _ _ _ _ hk] at this

theorem unrAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (hu : χ.UnrAt P) : χ'.UnrAt P :=
  GlobalTheory.EtaConjType.unrAt_of_locK χ' P fun u hu' => Units.ext (by
    rw [locK_conj h P u hu', GlobalTheory.NormOneUnit.locK_unr hu hu', Units.val_one, map_one])

theorem tameAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (ht : χ.TameAt P) : χ'.TameAt P := by
  refine tameAt_of_locK χ' P fun u hu => Units.ext ?_
  have h1 : P.valuation E ((1 : Eˣ) : E) = 1 := by simp
  have hu1 : P.valuation E (u : E) = 1 := by
    have := Valuation.map_eq_of_sub_lt (P.valuation E) (x := 1) (y := (u : E)) (by rwa [map_one])
    rwa [map_one] at this
  rw [locK_conj h P u hu1, GlobalTheory.NormOneUnit.locK_tame ht h1 (by simpa using hu), map_one, Units.val_one, map_one]


open Classical in
theorem conj_chars_res : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t s cμ cη m hc
  obtain ⟨μ', η', hμ, hη, ecμ, ecη, hres⟩ := hc
  obtain ⟨-, p1, p2, p3⟩ := _root_.GlobalTheory.levCh_unramified_places D T R.toLevCh A.μ0 hL t
  have uη : ∀ P, η'.UnrAt P := fun P => unrAt_conj hη (R.C.isEta.unr P)
  have uμ : ∀ P : Pl D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) →
      μ'.UnrAt P := fun P hP => unrAt_conj hμ (((p3 P hP).2 i).mul (p3 P hP).1)
  have tμ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → μ'.TameAt PP := by
    intro PP hPP
    refine tameAt_conj hμ ?_
    rcases hPP with hP | hP
    · exact ((R.C.isMu0 i).tame PP).mul ((p1 PP hP).levelLe 1)
    · exact ((p2 PP hP i).levelLe 1).mul (hL.xi_tame t PP)
  have rη : ∀ PP, GlobalTheory.StepLaw.ResAt cη⁻¹ PP 1 := fun PP => by
    have := ((_root_.GlobalTheory.ResLoc.resAt_of_chrEq D cη η' ecη PP).2 (uη PP)).inv
    rwa [inv_one] at this
  have uoη : ∀ Z, GlobalTheory.StepLaw.UnrOff cη Z := fun Z v ε hε _ =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cη η' ecη v ε hε fun P _ => uη P
  refine ⟨fun PP hPP => ?_, fun Z hZ => ?_, fun w hw => ?_⟩
  · have h1 := (_root_.GlobalTheory.ResLoc.resAt_of_chrEq D cμ μ' ecμ PP).1 (m PP) (tμ PP hPP) (hres PP hPP)
    refine ⟨h1, ?_⟩
    have := h1.mul (rη PP)
    rwa [mul_one] at this
  · have h1 : GlobalTheory.StepLaw.UnrOff cμ Z := fun v ε hε hv =>
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cμ μ' ecμ v ε hε fun P hP => uμ P fun PP hPP => hP ▸ hv PP (hZ PP hPP)
    exact ⟨h1, h1.mul (uoη Z).inv⟩
  · have hw' : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ w.under (𝓞 D.host.F) := fun PP hPP he =>
      hw (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, he⟩)
    have h1 : UnrAt cμ w := (unrAt_iff_of_chrEq ecμ w).2 (uμ w hw')
    exact ⟨h1, h1.mul ((unrAt_iff_of_chrEq ecη w).2 (uη w)).inv⟩

end GlobalTheory.ConjSplitChars

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffAlongSandwich
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaCoefCont

private theorem measure_fundamentalDomain_ratL_lt_infty {D : D7} (V W : HSp D) (ν : Measure (WO V W)) (𝓕 : Set (WO V W))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) : ν 𝓕 < ⊤ := by
  obtain ⟨hg, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI := hg
  haveI := hsc
  haveI := hdisc
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov ν h𝓕

theorem continuous_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  intro D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  have hfin : ν 𝓕 < ⊤ := measure_fundamentalDomain_ratL_lt_infty V W ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C', hC'⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG'
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hE : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
    unfold GlobalTheory.IsoMean.emb
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  rw [continuous_iff_continuousAt]
  intro y₀
  haveI : SecondCountableTopology (Mx D a b) := (GlobalTheory.MixModel.lattice_Mx D a b).2.2.1
  haveI : FirstCountableTopology (Mx D a b) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C * C') ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_id continuous_const))).mul
        (hG.cont.comp (continuous_id.add continuous_const))).mul
        (continuous_star.comp hG'.cont)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star, heisO, norm_mul, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg (G u)).trans (hC u))
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_const hE))).mul
      (hG.cont.comp (continuous_const.add hE))).mul continuous_const).continuousAt

end GlobalTheory.ThetaCoefCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetEqOfColsUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open Finset
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramJacobi

theorem det_eq_of_cols_unit {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (h : ∀ i j, ¬ p j → M i j = (1 : Matrix n n R) i j) :
    M.det = (M.toSquareBlockProp p).det := by
  rw [← Matrix.det_transpose, Matrix.twoBlockTriangular_det (Matrix.transpose M) p]
  · have h1 : ((Matrix.transpose M).toSquareBlockProp fun i => ¬ p i) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.transpose_apply,
        Matrix.submatrix_apply]
      rw [h _ _ i.2, Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e.symm))]
    rw [h1, Matrix.det_one, mul_one, ← Matrix.det_transpose]
    rfl
  · intro i hi j hj
    rw [Matrix.transpose_apply, h _ _ hi, Matrix.one_apply_ne]
    rintro rfl
    exact hi hj

theorem jacobi_minor {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (G H : Matrix n n R) (hHG : H * G = 1) (p : n → Prop) [DecidablePred p] :
    (H.toSquareBlockProp fun i => ¬ p i).det * G.det = (G.toSquareBlockProp p).det := by
  have hGH : G * H = 1 := mul_eq_one_comm.mp hHG
  let N : Matrix n n R := Matrix.of fun i j => if p j then (1 : Matrix n n R) i j else H i j
  have hN : N.det = (H.toSquareBlockProp fun i => ¬ p i).det := by
    rw [Matrix.twoBlockTriangular_det N p]
    · have h1 : N.toSquareBlockProp p = 1 := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_pos j.2]
        rw [Matrix.one_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e))]
      have h2 : (N.toSquareBlockProp fun i => ¬ p i) = H.toSquareBlockProp fun i => ¬ p i := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_neg j.2]
      rw [h1, h2, Matrix.det_one, one_mul]
    · intro i hi j hj
      simp only [N, Matrix.of_apply, if_pos hj]
      rw [Matrix.one_apply_ne]
      rintro rfl
      exact hi hj
  have hGN : (G * N).det = (G.toSquareBlockProp p).det := by
    rw [det_eq_of_cols_unit (G * N) p]
    · have : (G * N).toSquareBlockProp p = G.toSquareBlockProp p := by
        ext i j
        simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.mul_apply, N, Matrix.of_apply, if_pos j.2, Matrix.one_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
    · intro i j hj
      rw [← hGH]
      simp only [Matrix.mul_apply, N, Matrix.of_apply, if_neg hj]
  rw [← hN, mul_comm, ← Matrix.det_mul, hGN]

end GlobalTheory.GramJacobi

namespace GlobalTheory.GramJacobi

end GlobalTheory.GramJacobi

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InfZeroFinSum

open Module

theorem repr_map_id {F A A' E ι : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']
    [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E) (f : A →ₐ[F] A')
    (z : A ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis A' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k
      = f ((Algebra.TensorProduct.basis A b).repr z k) := by
  have hz : z = ∑ i, (Algebra.TensorProduct.basis A b).repr z i • (Algebra.TensorProduct.basis A b) i :=
    ((Algebra.TensorProduct.basis A b).sum_repr z).symm
  have hm : Algebra.TensorProduct.map f (AlgHom.id F E) z
      = ∑ i, f ((Algebra.TensorProduct.basis A b).repr z i) • (Algebra.TensorProduct.basis A' b) i := by
    conv_lhs => rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [hm, (Algebra.TensorProduct.basis A' b).repr_sum_self]

theorem eq_sum_of_fst_zero {F Ai Afn E ι : Type*} [Field F] [CommRing Ai] [Algebra F Ai] [CommRing Afn]
    [Algebra F Afn] [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E)
    (z : (Ai × Afn) ⊗[F] E)
    (hz : Algebra.TensorProduct.map (AlgHom.fst F Ai Afn) (AlgHom.id F E) z = 0) :
    z = ∑ k, ((0 : Ai), (Algebra.TensorProduct.basis Afn b).repr
      (Algebra.TensorProduct.map (AlgHom.snd F Ai Afn) (AlgHom.id F E) z) k) ⊗ₜ[F] b k := by
  have h1 : ∀ k, ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k).1 = 0 := by
    intro k
    have := repr_map_id b (AlgHom.fst F Ai Afn) z k
    rw [hz, map_zero] at this
    simpa using this.symm
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Ai × Afn) b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [repr_map_id b (AlgHom.snd F Ai Afn) z k]
  have hc : (Algebra.TensorProduct.basis (Ai × Afn) b).repr z k
      = ((0 : Ai), AlgHom.snd F Ai Afn ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k)) :=
    Prod.ext (h1 k) rfl
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact congrArg (fun x => x ⊗ₜ[F] b k) hc

end GlobalTheory.InfZeroFinSum

theorem GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  intro D z hz
  exact GlobalTheory.InfZeroFinSum.eq_sum_of_fst_zero (Module.finBasis D.host.F D.host.E) z hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfContr
section
noncomputable section

open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift.TensorFormProof

open GlobalTheory.Chain.IoLift

variable {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]

theorem contr_tmul (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  unfold contr
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply, innerₛₗ_apply_apply]
  exact TensorProduct.rid_tmul _ _

theorem dual_contr (ι : V →ₗ[ℂ] H) (y : V) (l : A →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] V) :
    l (contr ι y t) = ⟪ι y, ι (TensorProduct.lid ℂ V (LinearMap.rTensor V l t))⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [contr_tmul, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, inner_smul_right,
      smul_eq_mul, mul_comm]
  | add s u hs hu => simp only [map_add (f := _), inner_add_right, hs, hu]

theorem eq_zero_of_contr (ι : V →ₗ[ℂ] H) (hι : Function.Injective ι) (t : A ⊗[ℂ] V)
    (h : ∀ y, contr ι y t = 0) : t = 0 := by

  have hl : ∀ l : A →ₗ[ℂ] ℂ, LinearMap.rTensor V l t = 0 := by
    intro l
    set w := TensorProduct.lid ℂ V (LinearMap.rTensor V l t) with hw
    have h0 : ⟪ι w, ι w⟫_ℂ = 0 := by
      have := dual_contr ι w l t
      rw [h w, map_zero] at this
      exact this.symm
    have hw0 : w = 0 := hι ((inner_self_eq_zero.mp h0).trans (map_zero ι).symm)
    rw [hw] at hw0
    exact (LinearEquiv.map_eq_zero_iff _).mp hw0

  let e := (Module.Basis.ofVectorSpace ℂ A).repr
  have hs : TensorProduct.finsuppScalarLeft ℂ V _ (LinearMap.rTensor V e.toLinearMap t) = 0 := by
    ext i
    rw [TensorProduct.finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply, hl, map_zero]
    rfl
  have h2 : LinearMap.rTensor V e.toLinearMap t = 0 := (LinearEquiv.map_eq_zero_iff _).mp hs
  have h3 := congrArg (LinearMap.rTensor V e.symm.toLinearMap) h2
  rwa [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id_apply, map_zero] at h3

theorem exists_tensor (ι : V →ₗ[ℂ] H) (β : V →ₛₗ[starRingEnd ℂ] A) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (h : ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → β y = 0) : ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = β y := by

  set F : Submodule ℂ H := E.map ι with hF
  haveI : FiniteDimensional ℂ F := by rw [hF]; infer_instance
  let b := stdOrthonormalBasis ℂ F
  have hpre : ∀ k, ∃ e : V, e ∈ E ∧ ι e = (b k : H) := fun k => Submodule.mem_map.mp (b k).2
  choose e heE he using hpre
  refine ⟨∑ k, β (e k) ⊗ₜ[ℂ] e k, fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [contr_tmul, he]

  set z : V := ∑ k, ⟪(b k : H), ι y⟫_ℂ • e k with hz
  have hperp : ∀ x ∈ E, ⟪ι (y - z), ι x⟫_ℂ = 0 := by
    intro x hx
    have hxF : ι x ∈ F := Submodule.mem_map_of_mem hx
    have hx' : ι x = ∑ j, ⟪(b j : H), ι x⟫_ℂ • (b j : H) := by
      have := congrArg Subtype.val (b.sum_repr' ⟨ι x, hxF⟩)
      simpa [Submodule.coe_inner] using this.symm
    have key : ⟪ι y, ι x⟫_ℂ = ∑ j, ⟪ι y, (b j : H)⟫_ℂ * ⟪(b j : H), ι x⟫_ℂ := by
      conv_lhs => rw [hx']
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sub, map_sum, map_smul, he, inner_sub_left, sum_inner, inner_smul_left, inner_conj_symm]
    rw [key, sub_self]
  have hyz := h (y - z) hperp
  rw [map_sub, sub_eq_zero] at hyz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hyz, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, inner_conj_symm]

theorem tensorForm : TensorForm := by
  intro U A V H _ _ _ _ _ _ _ _ ι hι
  have sep : ∀ s u : A ⊗[ℂ] V, (∀ y, contr ι y s = contr ι y u) → s = u := fun s u hsu =>
    sub_eq_zero.mp (eq_zero_of_contr ι hι _ fun y => by rw [map_sub, hsu, sub_self])
  refine ⟨fun t ht => eq_zero_of_contr ι hι t ht, fun B hB => ?_⟩
  have hex : ∀ P, ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = B P y := by
    intro P
    obtain ⟨E, hE, hk⟩ := hB P
    exact exists_tensor ι (B P) E hk
  choose g hg using hex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sep _ _ fun y => by simp [hg]
           map_smul' := fun c P => sep _ _ fun y => by simp [hg] }, hg⟩

end GlobalTheory.Chain.IoLift.TensorFormProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalarAnnih

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem exists_compact_annihilator_finiteAdeles_traceChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hc : Continuous ψ)
    (hfin : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)))
    (O : Set (Af F)) (hO : O ∈ nhds (0 : Af F)) : ∃ K : Set (Af F), IsCompact K ∧
      ∀ x : Af F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K := by
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O hO
  obtain ⟨t, ht⟩ := exists_idealOf_eq (GlobalTheory.StdDual.codiff_ne_zero (F := F))
  let c : Af F := algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F)
  refine ⟨(fun a => c * a) '' {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id), ?_⟩
  intro x hx
  have h1 : (N : Af F) * x ∈ adelicIdeal (GlobalTheory.StdDual.codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hc hfin]
    intro α hα
    have := hx _ (hNO α hα)
    rwa [nsmul_eq_mul, mul_assoc, mul_left_comm] at this
  have h2 : (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x)) ∈
      adelicIdeal (t • (1 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [Units.mul_inv_cancel_left, smul_one_eq, ht]; exact h1
  rw [mul_mem_adelicIdeal_smul, mem_adelicIdeal] at h2
  refine ⟨_, fun v => (mem_localIdeal_one_iff v _).1 (h2 v), ?_⟩
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e : algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) N, ← map_mul, inv_mul_cancel₀ hN0, map_one]
  simp only [c]
  calc algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x))
      = algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) * x := by
        rw [mul_assoc, Units.mul_inv_cancel_left, mul_assoc]
    _ = x := by rw [e, one_mul]

theorem exists_compact_of_annih : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧
      ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K :=
  fun D ψ hψ O hO =>
    exists_compact_annihilator_finiteAdeles_traceChar D.host.F ψ hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) O hO

end GlobalTheory.ScalarAnnih

end
end

