module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermOfRange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereIntegral
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSixth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.BaseForm

variable {K : Type} {ι : K → Type}

def incl (S : K → Prop) : (Σ k : {k // S k}, ι k.1) → (Σ k, ι k) := fun q => ⟨q.1.1, q.2⟩

theorem incl_injective (S : K → Prop) : Function.Injective (incl (ι := ι) S) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [incl, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl

theorem isMultiHomog_rename_incl [Fintype K] [∀ k, Fintype (ι k)] (S : K → Prop)
    {D : MRing (fun k : {k // S k} => ι k.1)} {a : {k // S k} → ℕ} (hD : IsMultiHomog D a) :
    IsMultiHomog (rename (incl (ι := ι) S) D : MRing ι) (Function.extend Subtype.val a 0) := by
  classical
  intro m hm k
  rw [MvPolynomial.support_rename_of_injective (incl_injective S), Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  by_cases hk : S k
  · have he : Function.extend Subtype.val a 0 k = a ⟨k, hk⟩ := Subtype.val_injective.extend_apply a 0 ⟨k, hk⟩
    rw [he, ← hD m₀ hm₀ ⟨k, hk⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective (incl_injective S) m₀ ⟨⟨k, hk⟩, i⟩
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨c, rfl⟩; exact hk c.2), Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨q, hq⟩
    exact hk ((Sigma.mk.inj_iff.mp hq).1 ▸ q.1.2)

theorem mConeMap_rename_incl {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) (D : MRing (fun k : {k // S k} => ι k.1)) :
    mConeMap y (rename (incl (ι := ι) S) D) =
      map (algebraMap Ω Φ) (rename Subtype.val (mConeMap x D)) := by
  induction D using MvPolynomial.induction_on with
  | C r => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X, map_C, map_X, hy] <;> rfl

theorem rename_incl_notMem {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) {D : MRing (fun k : {k // S k} => ι k.1)}
    (hD : D ∉ mCoordIdeal x) : (rename (incl (ι := ι) S) D : MRing ι) ∉ mCoordIdeal y := by
  intro hmem
  apply hD
  have e : mConeMap y (rename (incl (ι := ι) S) D) = 0 := hmem
  rw [mConeMap_rename_incl S x y hy D] at e
  have e2 : rename Subtype.val (mConeMap x D) = 0 :=
    MvPolynomial.map_injective _ (algebraMap Ω Φ).injective (e.trans (map_zero _).symm)
  show mConeMap x D = 0
  exact MvPolynomial.rename_injective _ Subtype.val_injective (e2.trans (map_zero _).symm)

theorem exists_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a → D ∉ mCoordIdeal M.x → ∃ (G : MRing ι) (a' : K → ℕ), IsMultiHomog G a' ∧ G ∉ mCoordIdeal y ∧ ∀ w : (Σ k, ι k) → ℂ, eval w (map (Int.castRingHom ℂ) G) = eval (basePart M.blk w) (map (Int.castRingHom ℂ) D) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ D a hD hDx
  refine ⟨rename (incl (ι := ι) fun k => ∀ p, M.blk p ≠ some k) D, Function.extend Subtype.val a 0,
    isMultiHomog_rename_incl _ hD, rename_incl_notMem _ M.x y (fun q => M.y_base q) hDx, fun w => ?_⟩
  rw [map_rename, eval_rename]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.BaseForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThird
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase

section Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem sameOrbit_comp {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (z ∘ v) (z' ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hb.2.2.1 q]

theorem mCoordIdeal_le {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : mCoordIdeal z' ≤ mCoordIdeal z := by
  obtain ⟨c, hc, rfl⟩ := h
  intro f hf
  let ψ : MvPolynomial K ℂ →ₐ[ℤ] MvPolynomial K ℂ :=
    (aeval fun k => C (c k) * X k : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ).restrictScalars ℤ
  have e : mConeMap (fun p : Σ k, ι k => c p.1 * z' p) = ψ.comp (mConeMap z') := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, ψ, mul_assoc, mul_left_comm]
  have hf' : mConeMap z' f = 0 := hf
  show mConeMap _ f = 0
  rw [e, AlgHom.comp_apply, hf', map_zero]

theorem mCoordIdeal_eq {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le (Cj.sameOrbit_symm h)) (mCoordIdeal_le h)

theorem coord_ne {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun e =>
  h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, e, map_zero, zero_mul])

theorem comp_mem_mcPts {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (φ : Ω₁ →+* Ω)
    {x₁ : (Σ k, ι₁ k) → Ω₁} {x : (Σ k, ι k) → Ω} (hx : ∀ q, x (v q) = φ (x₁ q)) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) : z ∘ v ∈ mcPts (mCoordIdeal x₁) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨⟨k', i'⟩, hp⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have hk : k' = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k', i'⟩).symm)
    subst hk
    exact ⟨i', by simpa [Function.comp, hp] using hi⟩
  · let ρ : MvPolynomial K₁ Ω₁ →+* MvPolynomial K Ω :=
      (MvPolynomial.map φ).comp (rename κ : MvPolynomial K₁ Ω₁ →ₐ[Ω₁] MvPolynomial K Ω₁).toRingHom
    have e : (mConeMap x).comp (rename v) = ρ.toIntAlgHom.comp (mConeMap x₁) := by
      apply MvPolynomial.algHom_ext
      intro p
      show mConeMap x (rename v (X p)) = ρ (mConeMap x₁ (X p))
      simp [mConeMap, ρ, hx, hb.2.2.1 p]
    have hf' : mConeMap x₁ f = 0 := hf
    have hr : rename v f ∈ mCoordIdeal x := by
      show mConeMap x (rename v f) = 0
      have e' : mConeMap x (rename v f) = ρ (mConeMap x₁ f) := DFunLike.congr_fun e f
      rw [e', hf', map_zero]
    have := hz.2 _ hr
    rwa [MvPolynomial.map_rename, MvPolynomial.eval_rename] at this

end Orbits

theorem img_lies_over : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w, CovMap.IsImg Cv z w → SameOrbit (basePart M.blk w) (basePart M'.blk z ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w hI
  have P' := _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M'
  have P := _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M
  obtain ⟨F', hF', hg'⟩ := P'.2.1 _ (P'.1 z hz)
  let c : K' → ℂ := fun k => if h : ∀ p, M'.blk p ≠ some k then (z ⟨k, F'.c ⟨k, h⟩⟩)⁻¹ else 1
  have hne : ∀ k : NonPluckerBlocks M'.blk, z ⟨k.1, F'.c k⟩ ≠ 0 := fun k => coord_ne (q := ⟨k, F'.c k⟩) (hg'.1 k)
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M'.blk p ≠ some k
    · simp only [c, dif_pos h]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z₁ : (Σ k, ι' k) → ℂ := fun p => c p.1 * z p
  have h1 : SameOrbit z₁ z := ⟨c, hc, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mcPts_smul hA'.2.1.2.1 c hc hz
  have hn : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := fun k => by
    show c k.1 * z ⟨k.1, F'.c k⟩ = 1
    have hk : ∀ p, M'.blk p ≠ some k.1 := k.2
    simp only [c, dif_pos hk]
    exact inv_mul_cancel₀ (hne k)
  have hb₁ := P'.1 z₁ hz₁
  have ho := sameOrbit_basePart M'.blk h1
  have hgood : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [mCoordIdeal_eq ho]
    exact hg'
  obtain ⟨h, hh⟩ := (P'.2.2 F' hF' z₁ hb₁ hgood hn).1 hz₁
  obtain ⟨F, hF, hg⟩ := P.2.1 _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq hb₁)
  obtain ⟨z₀, a, b, -⟩ := hI z₁ h1 F' F hF' hF hgood hg h hh
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm (sameOrbit_basePart M.blk a))
    (Cj.sameOrbit_trans b (sameOrbit_comp Cv.block ho))

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem stepGap_eq_of_base_block : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (x₀ : BM.Rb.X) (z z' : (Σ k, ι k) → ℂ), x₀ ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z' ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → basePart M.blk z = basePart M.blk z' → (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → stepGap M BM p z = stepGap M BM p z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p x₀ z z' hx₀ hz hz' horb hbase hblk
  obtain ⟨l, hl⟩ := BM.O_cover x₀
  have hx : x₀ ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := ⟨hl, hx₀⟩
  have horb' : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.basePart M.blk z') (BM.Rb.lift x₀ x₀) := by
    rw [← hbase]
    exact horb
  have hbm : GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z = GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z' := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono
    rw [hbase]
  have hfs : (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z =
      (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z' := by
    show GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z =
      GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z'
    unfold GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm
    refine Finset.prod_congr rfl (fun k _ => ?_)
    by_cases h0 : M.dy p k = 0
    · simp [h0]
    · have hcoord : ∀ i, z ⟨k, i⟩ = z' ⟨k, i⟩ := by
        intro i
        by_cases hk : M.blk p = some k
        · exact hblk k hk i
        · by_cases hb : ∀ p' : Ψ × Fin N, M.blk p' ≠ some k
          · exact congrFun hbase ⟨⟨k, hb⟩, i⟩
          · exfalso
            apply h0
            unfold GlobalTheory.CompanionTheory.Ar.PB.FlagModel.dy
            rw [dite_eq_right hb, if_neg hk]
      simp only [hcoord]
  have hh : Real.log ((BM.hom p).h z) = Real.log ((BM.hom p).h z') := by
    cases hp : M.blk p with
    | none =>
      rw [_root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main K ι Φ y Ψ N j M n BM p l x₀ z hp hx hz horb,
        _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main K ι Φ y Ψ N j M n BM p l x₀ z' hp hx hz' horb', hbm, hbase]
    | some k₀ =>
      obtain ⟨I₀, hI₀, hne⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.exists_plk_ne_zero K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hl hz horb
      obtain ⟨C, B, hCB⟩ := GlobalTheory.CompanionTheory.Ar.PB.StepW.GrChart.exists_isGrChart N j p.2 I₀ M.j_le hI₀
      have hfun : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z = GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' := by
        funext I
        unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.plk
        rw [hbase]
        simp only [hblk k₀ hp]
      have hne' : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' I₀ ≠ 0 := by
        rw [← hfun]
        exact hne
      rw [_root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main K ι Φ y Ψ N j M n BM p k₀ l x₀ z I₀ C B hp hCB hx hz horb hne,
        _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep.main K ι Φ y Ψ N j M n BM p k₀ l x₀ z' I₀ C B hp hCB hx hz' horb' hne', hfun, hbm]
  unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap
  rw [hh, hfs]

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDegGeomDeg_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement :=
  fun hI _ => GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof
    (degreeGeneric_of_degree (degree_of_system hI))

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianFormPeriodMatrixNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.NForm

open Matrix

private theorem hermForm_cols {g : ℕ} (N P Q : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    hermForm N (P *ᵥ Pi.single i 1) (Q *ᵥ Pi.single j 1) =
      (Pᵀ * N * Q.map (starRingEnd ℂ)) i j := by
  simp only [mulVec_single_one, hermForm]
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc, col_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem re_of_real_add {g : ℕ} (B C : Matrix (Fin g) (Fin g) ℝ) (i j : Fin g) :
    ((B.map (fun x : ℝ => (x : ℂ)) + Complex.I • C.map (fun x : ℝ => (x : ℂ))) i j).re = B i j := by
  simp

private theorem imInv_periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    GlobalTheory.CanTh.imInv (periodMatrix X Y) = Y⁻¹.map (fun x : ℝ => (x : ℂ)) := by
  have : (periodMatrix X Y).map Complex.im = Y := by ext i j; simp [periodMatrix]
  rw [GlobalTheory.CanTh.imInv, this]

private theorem map_ofReal_mul {g : ℕ} (B C : Matrix (Fin g) (Fin g) ℝ) :
    (B * C).map (fun x : ℝ => (x : ℂ)) =
      B.map (fun x : ℝ => (x : ℂ)) * C.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem gram_eq_siegelGram {g : ℕ} {X Y : Matrix (Fin g) (Fin g) ℝ} (hX : X.IsSymm) (hY : Y.PosDef) :
    (Matrix.of fun α β : Fin g ⊕ Fin g =>
      (hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y))
        (Sum.elim (fun i => (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1)
          (fun i => periodMatrix X Y *ᵥ Pi.single i 1) α)
        (Sum.elim (fun i => (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1)
          (fun i => periodMatrix X Y *ᵥ Pi.single i 1) β)).re) = siegelGram X Y := by
  have hYs : Yᵀ = Y := by
    ext i j
    simpa using hY.isHermitian.apply i j
  have hXs : Xᵀ = X := hX
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hYY : Y * Y⁻¹ * Y = Y := by rw [mul_nonsing_inv _ hu, Matrix.one_mul]
  set c : Matrix (Fin g) (Fin g) ℝ → Matrix (Fin g) (Fin g) ℂ := fun B => B.map (fun x : ℝ => (x : ℂ)) with hc
  have hτ : periodMatrix X Y = c X + Complex.I • c Y := rfl
  have hτt : (periodMatrix X Y)ᵀ = c X + Complex.I • c Y := by
    rw [hτ, transpose_add, transpose_smul]
    have : ∀ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ = B → (c B)ᵀ = c B := fun B hB => by
      rw [hc]; simp only; rw [← transpose_map, hB]
    rw [this X hXs, this Y hYs]
  have hτc : (periodMatrix X Y).map (starRingEnd ℂ) = c X - Complex.I • c Y := by
    ext i j; simp [periodMatrix, hc, Complex.ext_iff]
  have h1c : (1 : Matrix (Fin g) (Fin g) ℂ).map (starRingEnd ℂ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have mm : ∀ B C, c (B * C) = c B * c C := map_ofReal_mul
  ext α β
  rcases α with i | i <;> rcases β with j | j <;>
    simp only [of_apply, Sum.elim_inl, Sum.elim_inr, hermForm_cols, imInv_periodMatrix, siegelGram,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_one, h1c, hτt, hτc,
      Matrix.one_mul, Matrix.mul_one]
  · simp
  · have : (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) =
        c (Y⁻¹ * X) + Complex.I • c (-(Y⁻¹ * Y)) := by
      have hneg : ∀ B, c (-B) = -c B := fun B => by ext i j; simp [hc]
      change c Y⁻¹ * _ = _
      rw [hneg, mm, mm, Matrix.mul_sub, Matrix.mul_smul, smul_neg, sub_eq_add_neg]
    rw [this]; exact re_of_real_add _ _ i j
  · have : (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) =
        c (X * Y⁻¹) + Complex.I • c (Y * Y⁻¹) := by
      simp [hc, Matrix.add_mul, map_ofReal_mul]
    rw [this]; exact re_of_real_add _ _ i j
  · have : (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) =
        c (Y + X * Y⁻¹ * X) + Complex.I • c (Y * Y⁻¹ * X - X * Y⁻¹ * Y) := by
      have e1 : c (Y + X * Y⁻¹ * X) = c (Y * Y⁻¹ * Y) + c (X * Y⁻¹ * X) := by
        rw [hYY]; ext i j; simp [hc]
      have e2 : c (Y * Y⁻¹ * X - X * Y⁻¹ * Y) = c (Y * Y⁻¹ * X) - c (X * Y⁻¹ * Y) := by
        ext i j; simp [hc]
      rw [e1, e2]
      simp only [mm]
      change _ = _ + _
      have hI : ∀ N : Matrix (Fin g) (Fin g) ℂ, Complex.I • (Complex.I • N) = -N := fun N => by
        rw [smul_smul, Complex.I_mul_I]; simp
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add, hI]
      abel
    rw [this]
    have := re_of_real_add (Y + X * Y⁻¹ * X) (Y * Y⁻¹ * X - X * Y⁻¹ * Y) i j
    simpa [hc] using this

theorem normal_form_gram : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (v : Fin g ⊕ Fin g → Fin g → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (v α) (v β)).im = Matrix.J (Fin g) ℝ α β) →
    ∃ (h : Matrix (Fin g) (Fin g) ℂ) (X Y : Matrix (Fin g) (Fin g) ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ i, h.mulVec (v (Sum.inl i)) = Pi.single i 1) ∧
      (∀ i, h.mulVec (v (Sum.inr i)) = (periodMatrix X Y).mulVec (Pi.single i 1)) ∧
      (Matrix.of fun α β => (hermForm Hm (v α) (v β)).re) = siegelGram X Y := by
  intro g Hm v hH hpos hJ
  set A : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inl j) i with hA
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inr j) i with hF
  set τ : Matrix (Fin g) (Fin g) ℂ := A⁻¹ * F with hτ
  obtain ⟨hu, hs, hp, hform⟩ := GlobalTheory.HolTheta.normal_form Hm (fun j => v (Sum.inl j)) (fun j => v (Sum.inr j)) hH hpos
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) (Sum.inl k))
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inr j) (Sum.inr k))
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) (Sum.inr k)) hA hτ
  have hPer : periodMatrix (τ.map Complex.re) (τ.map Complex.im) = τ := by
    ext i j; apply Complex.ext <;> simp [periodMatrix]
  have hXs : (τ.map Complex.re).IsSymm := by
    ext i j; simpa using congrArg Complex.re (hs.apply i j)
  have he : ∀ i, A⁻¹ *ᵥ v (Sum.inl i) = (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1 := fun i => by
    have : v (Sum.inl i) = A *ᵥ Pi.single i 1 := by ext k; simp [hA]
    rw [this, mulVec_mulVec, nonsing_inv_mul A hu]
  have hf : ∀ i, A⁻¹ *ᵥ v (Sum.inr i) = τ *ᵥ Pi.single i 1 := fun i => by
    have : v (Sum.inr i) = F *ᵥ Pi.single i 1 := by ext k; simp [hF]
    rw [this, mulVec_mulVec]
  refine ⟨A⁻¹, τ.map Complex.re, τ.map Complex.im, Matrix.isUnit_nonsing_inv_det A hu, hXs, hp, ?_, ?_, ?_, ?_⟩
  · intro z w; rw [hPer]; exact hform z w
  · intro i; rw [he, one_mulVec]
  · intro i; rw [hPer]; exact hf i
  · rw [← gram_eq_siegelGram hXs hp]
    ext α β
    rw [hPer]
    simp only [of_apply]
    rw [hform]
    rcases α with i | i <;> rcases β with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, he, hf]

end GlobalTheory.CompanionTheory.NForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormIntegralVerticalInvariance
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem vert_deg : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L L' : Fin D → HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, L j = L' j ∨ VertClose P T α (L j) (L' j)) → ∀ (Am : HermLine ι) (s : MRing ι), IsSmoothHerm Am → IsSectionOn P Am s → ptsIntegral P (pot L) (logNorm Am s) = ptsIntegral P (pot L') (logNorm Am s) :=
  @PositivityTheory.Xgp.t_vert_deg

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mixWord {n : ℕ} (a a₀ A' : HermLine ι) (k i : ℕ) : Fin n → HermLine ι :=
  fun j => if (j : ℕ) < i then a else if (j : ℕ) + 1 < k then a₀ else A'


open Classical in
def logRatio (a a₀ : HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (a₀.h z) - Real.log (a.h z) else 0

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereIntegralStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_monge_ampere_integral : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame <;> assumption)
end

