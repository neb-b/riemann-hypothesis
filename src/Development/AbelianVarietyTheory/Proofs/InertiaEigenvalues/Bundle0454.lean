module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def ioL (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) →ₗ[O] (V ⧸ L.T) :=
  (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T).liftQ
    (L.T.mkQ ∘ₗ (((algebraMap O LL ϖ)⁻¹ ^ r • (LinearMap.id : V →ₗ[LL] V)).restrictScalars O) ∘ₗ
      L.T.subtype) (by
    intro x hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.coe_smul,
      LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [← algebraMap_smul LL (ϖ ^ r) (y : V), smul_smul, map_pow, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simpa using y.2
      · rw [h, inv_zero, zero_mul, zero_pow hr.ne', zero_smul]; exact L.T.zero_mem
    · rw [inv_mul_cancel₀ h, one_pow, one_smul]; exact y.2)

theorem ioL_mk (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (y : ↥L.T) :
    ioL L ϖ r (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • (y : V)) := rfl

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def cupQ (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O)
    (r : ℕ) (c : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (c' : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T)) (x : G × G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (c x.1)) (ρ' x.1 (Formalism.MainNotions.LocalSituation.liftQ L' _ (c' x.2)))

end GlobalTheory.BKFinLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactAdelicUnitriangularEntriesMemCompact
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CellDec

theorem isCompact_unip_entries_mem :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  intro E _ _ n C hC
  classical
  let S : Fin n → Fin n → Set (Ad E) := fun i j => if j < i then {0} else if i = j then {1} else C
  let P : Set (Matrix (Fin n) (Fin n) (Ad E)) := Set.univ.pi fun i => Set.univ.pi (S i)
  have hP : IsCompact P := by
    refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
    simp only [S]
    split_ifs
    · exact isCompact_singleton
    · exact isCompact_singleton
    · exact hC
  have memP : ∀ M : Matrix (Fin n) (Fin n) (Ad E), M ∈ P ↔
      (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1) ∧ ∀ i j, i < j → M i j ∈ C := by
    intro M
    change (∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ S i j) ↔ _
    simp only [S]
    constructor
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_, fun i j hij => ?_⟩
      · have := h i trivial j trivial; rw [if_pos hji] at this; exact this
      · have := h i trivial i trivial; rw [if_neg (lt_irrefl i), if_pos rfl] at this; exact this
      · have := h i trivial j trivial; rw [if_neg (not_lt.2 hij.le), if_neg hij.ne] at this; exact this
    · rintro ⟨h0, h1, hc⟩ i - j -
      split_ifs with hji hij
      · exact h0 i j hji
      · subst hij; exact h1 i
      · exact hc i j (lt_of_le_of_ne (not_lt.1 hji) hij)
  have hdet : ∀ M ∈ P, M.det = 1 := by
    intro M hM
    obtain ⟨h0, h1, -⟩ := (memP M).1 hM
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => h0 i j hji)]
    simp [h1]
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have key : (Units.embedProduct (Matrix (Fin n) (Fin n) (Ad E))) ''
      {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} =
      (fun M => (M, MulOpposite.op M.adjugate)) '' P := by
    ext x
    constructor
    · rintro ⟨g, ⟨hN, hc⟩, rfl⟩
      obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hN
      have hgP : (g : Matrix (Fin n) (Fin n) (Ad E)) ∈ P := (memP _).2 ⟨h0, h1, hc⟩
      refine ⟨g, hgP, ?_⟩
      have hadj : (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
        calc (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate
            = (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * g) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate := by
              rw [Units.inv_mul, Matrix.one_mul]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * ((g : Matrix (Fin n) (Fin n) (Ad E)) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate) := by
              rw [Matrix.mul_assoc]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
              rw [Matrix.mul_adjugate, hdet _ hgP, one_smul, Matrix.mul_one]
      simp only [Units.embedProduct_apply, hadj]
    · rintro ⟨M, hM, rfl⟩
      have hd := hdet M hM
      let g : GA E n := ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul],
        by rw [Matrix.adjugate_mul, hd, one_smul]⟩
      obtain ⟨h0, h1, hc⟩ := (memP M).1 hM
      refine ⟨g, ⟨(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨h0, h1⟩, hc⟩, ?_⟩
      rfl
  rw [key]
  exact hP.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate))

end GlobalTheory.CellDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectorsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_character_of_crystalline_vectors : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  first | exact @GlobalTheory.LetterCrys.isCrys_of_letters | exact GlobalTheory.LetterCrys.isCrys_of_letters | (intros; apply GlobalTheory.LetterCrys.isCrys_of_letters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallinePeriodsLeSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.BKGal

theorem card_le_finrank_of_mem_span {K U W : Type} [Field K] [Field U] [AddCommGroup W] [Module K W]
    [Module U W] (hKU : ∀ c : K, ∃ c' : U, ∀ w : W, c • w = c' • w) (D : Submodule K W) [Module.Finite K D]
    {d : ℕ} (e : Fin d → W) (he : LinearIndependent U e) (hsp : ∀ i, e i ∈ Submodule.span U (D : Set W)) :
    d ≤ Module.finrank K D := by
  classical
  let u := Module.finBasis K D
  let u' := fun i => (u i : W)
  have hle : (D : Set W) ⊆ Submodule.span U (Set.range u') := by
    intro x hx
    have h4 := congrArg Subtype.val (u.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h4
    rw [← h4]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hKU (u.repr ⟨x, hx⟩ i)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h6 := linearIndependent_le_span_aux' _ he (Set.range u') (by
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le.2 hle (hsp i))
  have h7 := Fintype.card_range_le u'
  simp only [Fintype.card_fin] at h6 h7
  exact h6.trans h7

theorem isCrys_of_span_generic {G G' : Type} [Group G] [Group G'] {Qp K₀ K K₀' K' U : Type} [Field Qp] [Field K₀]
    [Field K] [Field K₀'] [Field K'] [Field U]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [IsDomain B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra U B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR] [SMulCommClass Qp U B]
    (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (hf : FracInv PD) (hf' : FracInv PD') (hU : ∀ c : K₀, ∃ c' : U, algebraMap K₀ B c = algebraMap U B c')
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (ρ' : Representation LL G' V) (hc : IsCrys PD' ρ')
    (hsp : ∀ m ∈ DcrisK₀ PD' ρ', m ∈ Submodule.span U (DcrisK₀ PD ρ : Set (B ⊗[Qp] V))) : IsCrys PD ρ := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_le₀ PD hf ρ
  obtain ⟨h3, -⟩ := finite_le₀ PD' hf' ρ'
  rw [isCrys_iff_finrank] at hc ⊢
  refine le_antisymm h2 ?_
  let e := Module.finBasisOfFinrankEq K₀' _ hc
  have hB := (indepB PD' hf' ρ' e e.linearIndependent).restrict_scalars' U
  refine card_le_finrank_of_mem_span (U := U) (fun c => ?_) _ _ hB fun i => hsp _ (e i).2
  obtain ⟨c', h⟩ := hU c
  exact ⟨c', fun w => by rw [← algebraMap_smul B c w, h, algebraMap_smul]⟩

theorem isCrys_of_dcris_le_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (LL : FinExt l) (T : QLat LL) (F K'' : FinExt l), IsCrys (P.PD K'') (T.ρ.comp (inclG K'')) → (∀ m ∈ DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')), m ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (↑(DcrisK₀ (P.PD F) (T.ρ.comp (inclG F))) : Set (P.R.B ⊗[ℚ_[l]] T.V))) → IsCrys (P.PD F) (T.ρ.comp (inclG F)) := by
  intro l _ P AI hs LL T F K'' hc hsp
  obtain ⟨Ti⟩ := hs
  haveI := LL.2
  haveI : IsDomain P.R.B := isDomain_of_tied Ti F
  exact isCrys_of_span_generic (U := ↥(MaximalUnramifiedExtension l)) (P.PD F) (P.PD K'') (GlobalTheory.Per.TiedRestrict.fracInv_of_tied Ti F)
    (GlobalTheory.Per.TiedRestrict.fracInv_of_tied Ti K'') (fun c => ⟨⟨c.1, c.2.2⟩, rfl⟩) _ _ hc hsp

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfSplit
section
noncomputable section

namespace GlobalTheory.SplitCrys

open Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.BlockCrys

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {n : ℕ}

theorem finrank_coordInv_of_split (A : G → Matrix (Fin n) (Fin n) Qp) (W : Matrix (Fin n) (Fin n) B)
    (hu : IsUnit W.det) (hW : ∀ g, (A g).map (algebraMap Qp B) * W.map (PD.actB g) = W) :
    finrank K₀ (coordInv PD A) = n := by
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply PD.not_mem_filtration_two
    rw [Subsingleton.elim PD.t 0, map_zero]
    exact zero_mem _
  have hact : ∀ g (y : Fin n → B),
      coordAct PD A g (W.mulVec y) = W.mulVec fun i => PD.actB g (y i) := by
    intro g y
    have h1 : (fun i => PD.actB g (W.mulVec y i)) =
        (W.map (PD.actB g)).mulVec fun i => PD.actB g (y i) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum]
    change ((A g).map (algebraMap Qp B)).mulVec _ = _
    rw [h1, Matrix.mulVec_mulVec, hW]
  have hinj : Function.Injective W.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det W).2 hu)
  let f : (Fin n → K₀) →ₗ[K₀] (Fin n → B) :=
    (W.mulVecLin.restrictScalars K₀).comp ((Algebra.linearMap K₀ B).compLeft (Fin n))
  have hf : ∀ c, f c = W.mulVec fun i => algebraMap K₀ B (c i) := fun c => rfl
  have hfi : Function.Injective f := by
    intro c d h
    rw [hf, hf] at h
    funext i
    exact (algebraMap K₀ B).injective (congrFun (hinj h) i)
  have hr : LinearMap.range f = coordInv PD A := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩ g
      rw [hf, hact]
      simp only [AlgEquiv.commutes]
    · intro hx
      have hxy : W.mulVec (W⁻¹.mulVec x) = x := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      have hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = W⁻¹.mulVec x i := fun i =>
        PD.invB _ fun g => by
          have h2 := hact g (W⁻¹.mulVec x)
          rw [hxy, hx g] at h2
          exact congrFun (hinj (h2.symm.trans hxy.symm)) i
      choose c hc using hc
      refine ⟨c, ?_⟩
      rw [hf, funext hc, hxy]
  rw [← hr, LinearMap.finrank_range_of_inj hfi, Module.finrank_fin_fun]

theorem isCrys_of_split {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
    [FiniteDimensional Qp LL] (W : Matrix (Fin n) (Fin n) B) (hu : IsUnit W.det)
    (hW : ∀ g, (Matrix.of fun i j => algebraMap Qp B (e.repr (ρ g (e j)) i)) * W.map (PD.actB g) = W) :
    IsCrys PD ρ := by
  let A : G → Matrix (Fin n) (Fin n) Qp := fun g => Matrix.of fun i j => e.repr (ρ g (e j)) i
  have h1 := finrank_coordInv PD ρ e A fun g i j => rfl
  have h2 := finrank_coordInv_of_split PD A W hu hW
  have hL : 0 < finrank Qp LL := Module.finrank_pos
  have hV : finrank Qp LL * finrank LL V = n := by
    rw [Module.finrank_mul_finrank Qp LL V, finrank_eq_card_basis e, Fintype.card_fin]
  rw [h2, ← hV, mul_left_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hL h1

end GlobalTheory.SplitCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus : ∀ (l : ℕ) [Fact l.Prime] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (D : Delta l Q) (DC : Delta l C) (J : Ideal Q) (JC : Ideal C) (h : Q →+* C), (l : Q) ∈ J → J.map h ≤ JC → IsHausdorff JC C → (∀ (x : Q) (n : ℕ), ∃ a ∈ δLocus D DC h, x - a ∈ J ^ n) → IsδMap D DC h := by
  first | exact @GlobalTheory.isδMap_of_dense_δLocus | exact GlobalTheory.isδMap_of_dense_δLocus | (intros; apply GlobalTheory.isδMap_of_dense_δLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KerGood

theorem map_aeval {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) (A : Module.End R M) (A' : Module.End R N) (hA : ∀ y, F (A y) = A' (F y))
    (p : Polynomial R) (y : M) : F (Polynomial.aeval A p y) = Polynomial.aeval A' p (F y) := by
  induction p using Polynomial.induction_on generalizing y with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c h =>
    simp only [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    rw [h (A y), hA]

theorem isGood_of_injective (hF : GlobalTheory.Published.FontaineBcris) {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a]
    {ϖ : PiSys l e} {LL : FinExt l} {Pl : LocPrime l} {AI : LocAinf l Pl} (hs : IsStd Pl AI)
    {Sig : Finset (ZMod e)} {U : Finset ℤ} {T₀ T₁ : QLat LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (hf : Function.Injective f) (he : ∀ g x, f (T₀.ρ g x) = T₁.ρ g (f x))
    (hT : IsGood a ϖ Pl T₁ Sig U) : IsGood a ϖ Pl T₀ Sig U := by
  refine ⟨?_, ?_, ?_⟩
  · have hS := (GlobalTheory.RegularRing.fontaineFormalism hF l Pl AI hs).2.2.2.1 (ϖ.field a) LL
    exact hS _ (resF T₁ (ϖ.field a)).ρ _ (resF T₀ (ϖ.field a)).ρ f (fun g x => he _ x) hf hT.crys
  · intro γ hγ w hw x hx
    obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hrf : ∀ v, r (f v) = v := fun v => LinearMap.congr_fun hr v
    have hRF : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) r
        (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, hrf]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    have hFi : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f) :=
      Function.LeftInverse.injective hRF
    have hFx := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB_mem (Pl.PD (ϖ.field a)) (ρ := (resF T₀ (ϖ.field a)).ρ)
      (ρ' := (resF T₁ (ϖ.field a)).ρ) (f := f) (fun g x => he _ x) x hx
    have h1 := hT.type γ hγ w hw _ hFx
    have hc : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f
        (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₀.ρ γ y) =
        actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₁.ρ γ (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, actVB, he]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    apply hFi
    exact (map_aeval _ _ _ hc _ x).trans (h1.trans (map_zero _).symm)
  · intro τ b hb
    exact hT.jumps τ b (GlobalTheory.HTW.isJumpV_of_injective _ _ T₁.ρ f hf he τ b hb)

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  intro hF l _ a e _ _ ϖ LL _ _ Pl AI hs Sig U T₁ T₂ g hg hT
  obtain ⟨⟨_, hD, hFr⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors ↥(OL LL)) c
    refine ⟨s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, x, ?_⟩
    rw [mul_comm]
    exact hxs
  have hinj : Function.Injective (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).f := fun x y h => Subtype.ext h
  refine ⟨Formalism.MainNotions.LiftingTheory.lker_T₀ g hg hden, Formalism.MainNotions.LiftingTheory.lker_ι g hg hden, ?_,
    isGood_of_injective hF hs _ hinj (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).equiv hT⟩
  exact ⟨hinj, Formalism.MainNotions.LiftingTheory.lker_surj g hg, hg,
    fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩, fun y hy => hy⟩

end GlobalTheory.KerGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateJumpOfGaloisFixedFiltrationVector
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem mem_DdRE_qlExt {l : ℕ} [Fact l.Prime] (Pl : LocPrime l) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] (ρ : Representation LL ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)) V)
    (τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] LL) (y : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hy : y ∈ DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    y ∈ DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ τ := by
  refine Submodule.mem_inf.mpr ⟨hy, ?_⟩
  clear hy
  refine Submodule.mem_iInf _ |>.mpr fun c => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp c.2
  obtain rfl : c = algebraMap ℚ_[l] _ r := Subtype.ext hr.symm
  rw [AlgHom.commutes, algebraMap_smul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      LinearMap.mulLeft_apply]
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      TensorProduct.tmul_smul]
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]

theorem isJumpV_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  intro l _ Pl LL T F _ i x hfix hi hni τ
  have h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ F.1 := bot_le
  have hE : ∀ u, DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u =
      DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u := by
    intro u
    refine le_antisymm (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ fun y hy => ?_)
    exact mem_DdRE_qlExt Pl T.ρ τ y hy
  unfold IsJumpV FildR
  rw [hE, hE]
  refine (GlobalTheory.JumpDescent.jump_iff l Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F LL h T i).mp ?_
  intro heq
  have hxD : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) := by
    refine (GlobalTheory.JumpDescent.mem_DdR Pl F _ x).mpr fun g => ?_
    rw [GlobalTheory.JumpDescent.actVdR_comp Pl h]
    exact hfix _ g.2
  have hx : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
      FilV (Pl.PD F) (LL := ↥LL.1) (V := T.V) i :=
    ⟨hxD, by rw [GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hi⟩
  rw [← heq] at hx
  exact hni (by rw [← GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hx.2)

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrame_hf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (f : Hom bk.prism B), IsFrame bk B (BK.hf f bk.E) (BK.hf f X) := by
  intro l _ K bk B f
  refine ⟨?_, ?_⟩
  · refine (GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f).symm.trans ?_
    change (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  · apply f.f_str
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str.toRingHom (bk.str.symm _)
    simp

end GlobalTheory.BSP
end

