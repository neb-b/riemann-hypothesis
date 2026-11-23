module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadical
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Proj

open GlobalTheory.StdPar

section Abstract

variable {A : Type} [CommRing A] {n r : ℕ} {X : Matrix (Fin n) (Fin r) A} {K : Matrix (Fin r) (Fin n) A}

theorem mulVec_left_inv (hKX : K * X = 1) {I : Set (Fin r)} {y : Fin n → A}
    (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : X *ᵥ (K *ᵥ y) = y := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.eqLocus (X * K).mulVecLin LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, -, rfl⟩
    change (X * K * X).col i = _
    rw [Matrix.mul_assoc, hKX, Matrix.mul_one]
    rfl
  rw [mulVec_mulVec]
  exact this hy

theorem mulVec_mem_span {I : Set (Fin r)} {a : Fin r → A} (ha : ∀ i, i ∉ I → a i = 0) :
    X *ᵥ a ∈ Submodule.span A ((fun i => Xᵀ i) '' I) := by
  rw [mulVec_eq_sum]
  refine sum_mem fun i _ => ?_
  rw [op_smul_eq_smul]
  by_cases hi : i ∈ I
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [ha i hi, zero_smul]
    exact zero_mem _

theorem coef_mul (hKX : K * X = 1) (M N : Matrix (Fin n) (Fin n) A) (hN : (N - 1) * X = X * (K * ((N - 1) * X))) :
    K * ((M * N - 1) * X) = K * ((M - 1) * X) + K * ((N - 1) * X) + K * ((M - 1) * X) * (K * ((N - 1) * X)) := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc K, Matrix.mul_assoc (M - 1) X, ← hN,
    Matrix.mul_assoc (M - 1)]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}
  {K : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}


omit [NumberField E] in
theorem col_mem {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) (j : Fin r) :
    (((matHom _ σ J g).1 - 1) * adMat F X).col j ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := by
  have := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  rw [Matrix.sub_mul, Matrix.one_mul]
  exact this


omit [NumberField E] in
theorem coef_eq_zero (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {i j : Fin r}
    (hi : ¬ ∃ k ∈ T, i ≤ k ∧ k < j) : (K * (((matHom _ σ J g).1 - 1) * adMat F X) : Matrix (Fin r) (Fin r) _) i j = 0 :=
  Norm.row_span (Z := K) (a := i) (fun m hm => by
    rw [hKX, Matrix.one_apply_ne]
    rintro rfl
    exact hi hm) (col_mem hg j)


omit [NumberField E] in
theorem eq_mul_coef (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) :
    ((matHom _ σ J g).1 - 1) * adMat F X = adMat F X * (K * (((matHom _ σ J g).1 - 1) * adMat F X)) :=
  Matrix.ext_col fun j => (mulVec_left_inv hKX (col_mem hg j)).symm

theorem exists_blockProj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, hΦc, _, hj, hΦ, hι⟩ hS ⟨k₀, hk₀, hk₀'⟩ hl r' hr0 hrd k hk
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
  have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
  have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKY : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [hm, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show jj (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  let c : GAd σ J → Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun g =>
    adMat F (cT (σ : E →+* E) Y * J) * (((matHom _ σ J g).1 - 1) * adMat F X)
  have hc : Continuous c := continuous_const.matrix_mul ((continuous_mat.sub continuous_const).matrix_mul continuous_const)
  refine ⟨fun a p => Φ (c a (e p.1.1) (e p.1.2)), ?_, fun a b => ?_, fun a x hx => ?_, fun a => ⟨fun h0 => ?_, fun ha => ?_⟩,
    fun a ha => ?_⟩
  · exact continuous_pi fun p => hΦc.comp ((hc.comp continuous_subtype_val).matrix_elem _ _)
  · funext p
    have h1 : c (a * b : unip σ J X (insert k S)) = c a + c b + c a * c b := by
      simp only [c]
      rw [Subgroup.coe_mul, map_mul, Units.val_mul]
      exact coef_mul hKX _ _ (eq_mul_coef hKX b.2)
    have h2 : (c a * c b) (e p.1.1) (e p.1.2) = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have hp2 := p.1.2.2
      by_cases hmk : m ≤ k
      · rw [show c a (e p.1.1) m = 0 from coef_eq_zero hKX a.2 ?_, zero_mul]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : l + p.1.1.val ≤ k'.val := h3
        have h4' : k'.val < m.val := h4
        have h5 : m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
      · rw [show c b m (e p.1.2) = 0 from coef_eq_zero hKX b.2 ?_, mul_zero]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : m.val ≤ k'.val := h3
        have h4' : k'.val < l + p.1.2.val := h4
        have h5 : ¬ m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
    change Φ (c (a * b : unip σ J X (insert k S)) _ _) = Φ _ + Φ _
    rw [h1, Matrix.add_apply, h2, add_zero, Matrix.add_apply, map_add (f := _)]
  · funext p
    have b1 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h X) = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hKX (e i)) (e j)).trans (by simp [Matrix.one_apply, e, Fin.ext_iff])
    have b2 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h Y) = 0 := Matrix.ext fun i j =>
      congrFun (congrFun hKY (e i)) (e j)
    have h1 : c a (e p.1.1) (e p.1.2) = (adMat F (cT (σ : E →+* E) (blkCols h Y) * J) *
        (((matHom _ σ J (a : GAd σ J)).1 - 1) * adMat F (blkCols h X)) : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 := rfl
    have hne : p.1.1 ≠ p.1.2 := fun h' => by have := p.2; rw [h'] at this; omega
    change Φ (c a _ _) = _
    rw [h1, hx, hι, add_assoc, add_sub_cancel_left, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc, b1,
      Matrix.mul_one, ← Matrix.mul_assoc, b1, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F _),
      b2, Matrix.zero_mul, add_zero, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, Matrix.map_apply,
      RingEquiv.apply_symm_apply]
    change (1 + GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 = _
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, GlobalTheory.CuspRep.nilM, Matrix.of_apply, dite_eq_left p.2]
  · have ha := a.2
    have hset : {i | ∃ k' ∈ insert k S, i ≤ k'} = {i | ∃ k' ∈ S, i ≤ k'} := Set.ext fun i =>
      ⟨fun ⟨k', hk', h1⟩ => by
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · exact ⟨k₀, hk₀, h1.trans (show k'.val ≤ k₀.val by omega)⟩
        · exact ⟨k', hk', h1⟩,
      fun ⟨k', hk', h1⟩ => ⟨k', Finset.mem_insert_of_mem hk', h1⟩⟩
    refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan ha ?_, fun y hy => ?_⟩, hset ▸ ha.2⟩
    · rintro i ⟨k', hk', hik, hkj⟩ m hm
      exact ⟨k', hk', hm.le.trans hik, hkj⟩
    · unfold colSpan at hy
      rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
      obtain ⟨t, rfl⟩ := hy
      rw [mulVec_smul, ← smul_sub]
      refine Submodule.smul_mem _ t ?_
      have h1 : (matHom _ σ J (a : GAd σ J)).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j = adMat F X *ᵥ (c a).col j := by
        have := congrArg (fun Z => Matrix.col Z j) (eq_mul_coef hKX ha)
        rw [Matrix.sub_mul, Matrix.one_mul] at this
        refine Eq.trans ?_ (this.trans ?_)
        · rfl
        · simp only [c]
          rw [Matrix.sub_mul, Matrix.one_mul]
          rfl
      rw [h1]
      refine mulVec_mem_span fun i hi => ?_
      by_cases hi' : ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j
      · obtain ⟨k', hk', h2, h3⟩ := hi'
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · have h2' : i.val ≤ k'.val := h2
          have h3' : k'.val < j.val := h3
          have h4 : j.val < l + d := by
            by_contra h4
            exact hi ⟨k₀, hk₀, show i.val ≤ k₀.val by omega, show k₀.val < j.val by omega⟩
          have h5 : l ≤ i.val := by
            by_contra h5
            rcases hl with hl | ⟨p, hp, hp'⟩
            · omega
            · exact hi ⟨p, hp, show i.val ≤ p.val by omega, show p.val < j.val by omega⟩
          have h6 := congrFun h0 ⟨(⟨i.val - l, by omega⟩, ⟨j.val - l, by omega⟩), by constructor <;> dsimp only <;> omega⟩
          have h7 : e ⟨i.val - l, by omega⟩ = i := Fin.ext (show l + (i.val - l) = i.val by omega)
          have h8 : e ⟨j.val - l, by omega⟩ = j := Fin.ext (show l + (j.val - l) = j.val by omega)
          change Φ (c a (e ⟨i.val - l, _⟩) (e ⟨j.val - l, _⟩)) = 0 at h6
          rw [h7, h8] at h6
          exact (map_eq_zero_iff Φ Φ.injective).1 h6
        · exact absurd ⟨k', hk', h2, h3⟩ hi
      · exact coef_eq_zero hKX ha hi'
  · funext p
    change Φ (c a _ _) = 0
    rw [show c a (e p.1.1) (e p.1.2) = 0 from coef_eq_zero hKX ha ?_, map_zero]
    rintro ⟨k', hk', h3, h4⟩
    have h3' : l + p.1.1.val ≤ k'.val := h3
    have h4' : k'.val < l + p.1.2.val := h4
    have hp2 := p.1.2.2
    exact hS k' (by omega) (by omega) hk'
  · obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
    have h1 : (matHom _ σ J (a : GAd σ J)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    refine ⟨fun p => (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X) : Matrix (Fin r) (Fin r) E) (e p.1.1) (e p.1.2), funext fun p => ?_⟩
    have h2 : c a = adMat F (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X)) := by
      simp only [c]
      rw [h1, ← hm (cT (σ : E →+* E) Y * J), ← hm (γ.1 - 1)]
      congr 2
      rw [adMat, adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    change _ = Φ (c a _ _)
    rw [h2]
    exact (hΦE _).symm

end GlobalTheory.BlockForms.Proj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisorStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor : ∀ (T : Scheme.{0}) (c : ℕ), (∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) → ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  first | (exact @GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (exact GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (intros; apply GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledPairWeilDatumSchrodingerTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

theorem exists_dbl_weilDatum_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd ∧
          ∃ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco
  have h1 : Formalism.L2.Theta.IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r0 : Formalism.L2.Theta.ResEta D 1 0 := ⟨rT.1, fun _ _ _ => by simp⟩
  have r1 : Formalism.L2.Theta.ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank :=
    Formalism.L2.Theta.resEta_parity r0 (by show 0 % 2 = (S.rank + S.rank) % 2; omega)
  obtain ⟨ωd, hωd⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp S) T 1 χT hψ h1 hT r1 rT
  refine ⟨ωd, hωd, ?_⟩
  exact _root_.GlobalTheory.ThetaTransform.exists_isTransport D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA
    (_root_.GlobalTheory.DblSchr.dblGram_xi D S JB ξ hξ) (κ ⊕ κ) (ddr co) (_root_.GlobalTheory.DblSchr.ddr_rat D S T JA JB ξ κ co hco) ωd hωd

end GlobalTheory.DblSchr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualBasesIsotropicSubspacesDuality
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IsoDuality

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_herm (V : Formalism.BasicNotions.HSpace E) (x y : V.V) : star (V.hT x y) = V.hT y x := by
  have := V.herm.eq x y
  rw [← starRingEnd_apply]; exact this

theorem iso_zero (V : Formalism.BasicNotions.HSpace E) {W : Submodule E V.V} (hW : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W)
    {w v : V.V} (hw : w ∈ W) (hv : v ∈ W) : V.hT w v = 0 := by
  have := hW hv
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this w hw

theorem finrank_le_of_sep (V : Formalism.BasicNotions.HSpace E) (A B : Submodule E V.V)
    (h : ∀ y ∈ B, (∀ x ∈ A, V.hT x y = 0) → y = 0) :
    Module.finrank E B ≤ Module.finrank E A := by
  classical
  let bA := Module.finBasis E A
  let Φ : B →ₗ[E] (Fin (Module.finrank E A) → E) :=
    LinearMap.pi (fun i => (V.hT (bA i : V.V)).comp B.subtype)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (bA i : V.V) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h y y.2
    intro x hx
    have hx' : (⟨x, hx⟩ : A) = ∑ i, (bA.repr ⟨x, hx⟩ i) • bA i := (bA.sum_repr _).symm
    have : x = ∑ i, (bA.repr ⟨x, hx⟩ i) • (bA i : V.V) := by
      calc x = ((∑ i, (bA.repr ⟨x, hx⟩ i) • bA i : A) : V.V) := by rw [← hx']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp [map_smulₛₗ, hy']
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end GlobalTheory.IsoDuality

namespace GlobalTheory.IsoDuality

theorem exists_dual_bases : ∀ {D : D7} {V : HSp D} (X X' : Submodule D.host.E V.V), X ≠ ⊥ → X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X → X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' → (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) → (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) → ∃ (a : ℕ) (x x' : Fin a → V.V), 0 < a ∧ a ≤ wittIndex V ∧ Submodule.span D.host.E (Set.range x) = X ∧ Submodule.span D.host.E (Set.range x') = X' ∧ LinearIndependent D.host.E (Sum.elim x x') ∧ (∀ i j, V.hD (x i) (x j) = 0) ∧ (∀ i j, V.hD (x' i) (x' j) = 0) ∧ (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) := by
  classical
  intro D V X X' hX0 hX hX' h1 h2
  have hTX := fun {w v : V.V} (hw : w ∈ X) (hv : v ∈ X) => iso_zero V hX hw hv
  have hTX' := fun {w v : V.V} (hw : w ∈ X') (hv : v ∈ X') => iso_zero V hX' hw hv

  have hle1 : Module.finrank D.host.E X ≤ Module.finrank D.host.E X' :=
    finrank_le_of_sep V X' X (fun y hy h => h1 y hy (fun z hz => h z hz))
  have hle2 : Module.finrank D.host.E X' ≤ Module.finrank D.host.E X :=
    finrank_le_of_sep V X X' (fun y hy h => h2 y hy (fun z hz => by
      show V.hT y z = 0
      rw [← hT_herm, h z hz, star_zero]))
  set a := Module.finrank D.host.E X with ha
  let bx := Module.finBasis D.host.E X
  let x : Fin a → V.V := fun i => (bx i : V.V)
  have hxX : ∀ i, x i ∈ X := fun i => (bx i).2
  let Φ : X' →ₗ[D.host.E] (Fin a → D.host.E) :=
    LinearMap.pi (fun i => (V.hT (x i)).comp X'.subtype)
  have hΦ : ∀ y i, Φ y i = V.hT (x i) y := fun y i => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (x i) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h2 y y.2
    intro z hz
    have hz' : (⟨z, hz⟩ : X) = ∑ i, (bx.repr ⟨z, hz⟩ i) • bx i := (bx.sum_repr _).symm
    have : z = ∑ i, (bx.repr ⟨z, hz⟩ i) • x i := by
      calc z = ((∑ i, (bx.repr ⟨z, hz⟩ i) • bx i : X) : V.V) := by rw [← hz']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    show V.hT (y : V.V) z = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hT_herm, this, map_sum]
    simp [map_smulₛₗ, hy']
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinj
    · simp [a]; omega
  choose g hg using fun j : Fin a => hsurj (Pi.single j 1)
  let x' : Fin a → V.V := fun j => (g j : V.V)
  have hx'X : ∀ j, x' j ∈ X' := fun j => (g j).2
  have hxx' : ∀ i j, V.hT (x i) (x' j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hg j) i
    rw [hΦ] at this
    show V.hT (x i) (g j : V.V) = _
    rw [this, Pi.single_apply]
  have hxli : LinearIndependent D.host.E x :=
    bx.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hli : LinearIndependent D.host.E (Sum.elim x x') := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr] at hc
    have hd : ∀ k, c (Sum.inr k) = 0 := by
      intro k
      have := congrArg (V.hT (x k)) hc
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, map_sum, map_zero] at this
      simp only [map_smul, smul_eq_mul, hTX (hxX k) (hxX _), mul_zero, Finset.sum_const_zero,
        zero_add, hxx', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
      exact this
    have hc' : ∑ i, c (Sum.inl i) • x i = 0 := by
      simpa [hd] using hc
    have hcl := Fintype.linearIndependent_iff.1 hxli _ hc'
    rintro (i | j)
    · exact hcl i
    · exact hd j
  have hx'li : LinearIndependent D.host.E x' := hli.comp Sum.inr Sum.inr_injective
  refine ⟨a, x, x', ?_, ?_, ?_, ?_, hli, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (fun h => hX0 (Submodule.finrank_eq_zero.1 h))
  · exact GlobalTheory.Cusp.finrank_le_wittIndex hX
  · have : Set.range x = X.subtype '' Set.range bx := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bx.span_eq, Submodule.map_top, Submodule.range_subtype]
  · apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact hx'X j
    · rw [finrank_span_eq_card hx'li]; simp [a]; omega
  · intro i j
    show V.hT (x j) (x i) = 0
    exact hTX (hxX j) (hxX i)
  · intro i j
    show V.hT (x' j) (x' i) = 0
    exact hTX' (hx'X j) (hx'X i)
  · intro i j
    show V.hT (x' j) (x i) = _
    rw [← hT_herm, hxx']
    split_ifs <;> simp

end GlobalTheory.IsoDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePropeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbertSch.main) | (exact GlobalTheory.HilbertSch.main) | (intros; apply GlobalTheory.HilbertSch.main <;> assumption)
end

