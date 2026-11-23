module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0020
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
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamily
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (q : Σ k, ι k) (h : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ I, valAt M.x (F.u q I) b * minorIJ h I (stepCols N j i)

def stepCoord {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    (p : Ψ × Fin N) (k' : K') (q : Σ k, ι k) : ℂ :=
  ∑ I, valAt M.x (F.u q I) (basePart M'.blk z ∘ Cv.v) *
    ∑ I', if IsStepRows N j p.2 I' then minorIJ (Cv.trans F' F (basePart M'.blk z) p.1) I I' *
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ else 0

def img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then basePart M'.blk z (Cv.v ⟨⟨q.1, hk⟩, q.2⟩)
  else
    have hp : ∃ p, M.blk p = some q.1 := by simpa using hk
    match M'.blk hp.choose with
    | none => 0
    | some k' => stepCoord Cv F' F z hp.choose k' q

theorem img_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    basePart M.blk (img Cv F' F z) = basePart M'.blk z ∘ Cv.v := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  simp only [basePart, img, Function.comp]
  rw [dite_eq_left hk]

theorem img_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    {p : Ψ × Fin N} {k : K} {k' : K'} (hp : M.blk p = some k) (hp' : M'.blk p = some k') (m : ι k) :
    img Cv F' F z ⟨k, m⟩ = stepCoord Cv F' F z p k' ⟨k, m⟩ := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h => h p hp
  have hex : ∃ p', M.blk p' = some k := ⟨p, hp⟩
  have hch : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
  simp only [img, dif_neg hk]
  split
  · next h =>
    rw [hch, hp'] at h
    exact absurd h (by simp)
  · next k'' h =>
    rw [hch, hp'] at h
    cases h
    rw [hch]

theorem exists_blk_cover {M : FlagModel y Ψ N j} (M' : FlagModel y' Ψ N j) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : ∃ k', M'.blk p = some k' := by
  have h1 : ¬ (M.blk p = none) := by
    rw [hp]
    simp
  rw [M.blk_none] at h1
  have h2 : M'.blk p ≠ none := by
    rw [Ne, M'.blk_none]
    exact h1
  exact Option.ne_none_iff_exists'.mp h2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunction
section
set_option maxSynthPendingDepth 1
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem cuspWeight_descends :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
      [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
      [Module O Lt] (X : ComponentSetting D O Lt),
      ∃ (G : X.M.Xc → ℝ) (C : ℝ), @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G) ∧
        (∀ x ∈ X.S.R.Yo, |G x| ≤ C + C * Real.log (X.S.R.r x)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → X.Cd.cuspWeight z = G (X.M.proj z) := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, C', hC⟩ := CuspWeightIntegrable.uFn_bound X
  letI : MeasurableSpace X.M.Xc := borel X.M.Xc
  haveI : BorelSpace X.M.Xc := ⟨rfl⟩
  refine ⟨fun x => 2 * CuspWeightIntegrable.uFn X x, 2 * max C C', ?_, ?_, ?_⟩
  · exact ((CuspWeightIntegrable.measurable_uFn X).const_mul 2).indicator X.S.R.isOpen_Yo.measurableSet
  · intro x hx
    have h1 := hC x hx
    have hl := Real.log_nonneg (X.S.R.one_le_r x hx)
    have h2 : C' * Real.log (X.S.R.r x) ≤ max C C' * Real.log (X.S.R.r x) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hl
    have h3 : C ≤ max C C' := le_max_left _ _
    rw [abs_mul, abs_two]
    nlinarith
  · intro z hz hy
    have hzB : z ∉ D.Bd := by
      intro hB
      obtain ⟨z0, ⟨hz0X, hz0m⟩, hp⟩ := X.S.Yo_sub _ hy
      obtain ⟨c, hc, rfl⟩ := (X.M.fibre z hz z0 hz0m).1 hp.symm
      exact hz0X.2 (D.bd_torus z hB c hc)
    have := CuspWeightIntegrable.cuspWeight_eq X hz hzB hy
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSymplecticBasisPrincipalPolarization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice

open scoped Matrix

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun y w => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im)
    (fun a b w => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct])
    (fun c a w => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul,
        Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im := rfl

theorem imForm_smul_I {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    imForm Hm z (Complex.I • z) = -(ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re := by
  simp [imForm_apply, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul,
    dotProduct_smul, Matrix.mulVec_neg, dotProduct_neg]

theorem imForm_injective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Injective (imForm Hm) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have h1 := imForm_smul_I Hm z
  rw [hz] at h1
  have := hpos z h0
  simp at h1
  linarith

theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 (imForm_injective Hm hpos)

theorem exists_symplectic_basis : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k) →
    (∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) →
    ∃ bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, ∀ α β,
      (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β := by
  intro g Λ Hm hdisc hspan hH hpos hint hdual
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ (fun x y => k x y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
    (fun x y y' => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
  have hE : ∀ l m : Λ, (Ef l m : ℝ) = imForm Hm (l : Fin g → ℂ) (m : Fin g → ℂ) :=
    fun l m => (hk l m).symm
  have hanti : ∀ l m : Λ, Ef m l = - Ef l m := fun l m => by
    apply Int.cast_injective (α := ℝ)
    have h1 := congrArg Complex.im (GlobalTheory.SiegelNormalForm.form_conj hH (l : Fin g → ℂ) m)
    simp only [Complex.star_def, Complex.conj_im] at h1
    push_cast
    rw [hE, hE, imForm_apply, imForm_apply]
    exact h1.symm
  have halt : Ef.IsAlt := fun l => by
    have := hanti l l
    omega
  have hinj : Function.Injective Ef := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro l hl
    have hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤
        LinearMap.ker (imForm Hm (l : Fin g → ℂ)) := by
      rw [Submodule.span_le]
      intro m hm
      have := hE l ⟨m, hm⟩
      rw [hl] at this
      simpa using this.symm
    rw [hspan] at hle
    have h0 : imForm Hm (l : Fin g → ℂ) = 0 := LinearMap.ext fun y => hle (Submodule.mem_top)
    exact Subtype.ext ((injective_iff_map_eq_zero _).1 (imForm_injective Hm hpos) _ h0)
  have hsurj : Function.Surjective Ef := by
    intro φ
    let b := Module.finBasis ℤ Λ
    let bR := b.ofZLatticeBasis ℝ Λ
    let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ := bR.constr ℝ fun i => (φ (b i) : ℝ)
    have hψ : ∀ y : Λ, ψ (y : Fin g → ℂ) = (φ y : ℝ) := by
      intro y
      have hb : ∀ i, ψ (b i : Fin g → ℂ) = (φ (b i) : ℝ) := fun i => by
        have h := bR.constr_basis ℝ (fun i => (φ (b i) : ℝ)) i
        rwa [show bR i = (b i : Fin g → ℂ) by simp [bR]] at h
      conv_lhs => rw [← b.sum_repr y]
      conv_rhs => rw [← b.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, map_sum, map_zsmul, hb]
      simp
    obtain ⟨w, hw⟩ := imForm_surjective Hm hpos ψ
    have hwy : ∀ y : Λ, imForm Hm w (y : Fin g → ℂ) = (φ y : ℝ) := fun y => by rw [hw, hψ]
    have hwΛ : w ∈ Λ := hdual w fun l => ⟨φ l, hwy l⟩
    refine ⟨⟨w, hwΛ⟩, LinearMap.ext fun y => ?_⟩
    apply Int.cast_injective (α := ℝ)
    rw [hE, hwy]
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm ⟨hinj, hsurj⟩) hrank
  have hval : ∀ α β, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (bs α : Fin g → ℂ)
      (bs β : Fin g → ℂ)).im = (Ef (bs α) (bs β) : ℝ) := fun α β => (hE _ _).symm
  refine ⟨bs, ?_⟩
  have hee : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inl j)) = 0 := fun i j => by
    have := hbs.left_left i j
    simpa using this
  have hff : ∀ i j, Ef (bs (Sum.inr i)) (bs (Sum.inr j)) = 0 := fun i j => by
    have := hbs.right_right i j
    simpa using this
  have hef : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inr j)) = if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [this]; split_ifs <;> simp
  rintro (i | i) (j | j)
  · rw [hval, hee]; simp [Matrix.J]
  · rw [hval, hef]
    by_cases h : i = j <;> simp [Matrix.J, h, Matrix.one_apply]
  · rw [hval, hanti, hef]
    by_cases h : i = j
    · subst h; simp [Matrix.J]
    · simp [Matrix.J, h, Ne.symm h, Matrix.one_apply]
  · rw [hval, hff]; simp [Matrix.J]

end GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_le_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z' ≤ mCoordIdeal z := by
  obtain ⟨c, hc, rfl⟩ := h
  let θ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k) * X k
  have key : ∀ f : MRing ι, mConeMap (fun p => c p.1 * z' p) f = θ (mConeMap z' f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      simp [mConeMap, θ, mul_assoc, mul_left_comm]
  intro f hf
  have hf' : mConeMap z' f = 0 := hf
  show mConeMap _ f = 0
  rw [key, hf', map_zero]

theorem mCoordIdeal_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le_of_sameOrbit (Cj.sameOrbit_symm h)) (mCoordIdeal_le_of_sameOrbit h)

theorem coord_ne_of_X_notMem {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) :
    z q ≠ 0 := fun e => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

end Orbit

section Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) (φ : Ω →+* Ω')
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : ∀ q, x' (v q) = φ (x q))
    {zb : (Σ k, ι' k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x')) : zb ∘ v ∈ mcPts (mCoordIdeal x) := by
  have key : ∀ f : MRing ι, mConeMap x' (rename v f) = rename κ (map φ (mConeMap x f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, hx, hv.2.2.1 i]
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    obtain ⟨k₁, i₁⟩ := p
    have e : k₁ = k := hv.1 (by rw [← hv.2.2.1 ⟨k₁, i₁⟩, hp])
    subst e
    exact ⟨i₁, by simpa [Function.comp, hp] using hi⟩
  · have hf' : mConeMap x f = 0 := hf
    have h1 : rename v f ∈ mCoordIdeal x' := by
      show mConeMap x' (rename v f) = 0
      rw [key, hf', map_zero, map_zero]
    have h2 := hz.2 _ h1
    rwa [map_rename, eval_rename] at h2

end Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

theorem sameOrbit_of_isFlagOf (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {z z' : (Σ k, ι k) → ℂ} {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hb : SameOrbit (basePart M.blk z) (basePart M.blk z')) (H : M.IsFlagOf F z h) (H' : M.IsFlagOf F z' h) :
    SameOrbit z z' := by
  have hbase : basePart M.blk z = basePart M.blk z' := by
    obtain ⟨c, -, e⟩ := hb
    have hc : ∀ k, c k = 1 := fun k => by
      have := congrFun e ⟨k, F.c k⟩
      rw [H.1 k, H'.1 k, mul_one] at this
      exact this.symm
    rw [e]
    funext p
    simp [hc]
  have blockwise : ∀ k, ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = t * z' ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact ⟨1, one_ne_zero, fun m => by
        simpa [basePart] using congrFun hbase ⟨⟨k, hk⟩, m⟩⟩
    · push_neg at hk
      obtain ⟨p, hp⟩ := hk
      obtain ⟨a, ha, ea⟩ := H.2.2 p k hp
      obtain ⟨a', ha', ea'⟩ := H'.2.2 p k hp
      refine ⟨a / a', div_ne_zero ha ha', fun m => ?_⟩
      rw [ea m, ea' m, hbase]
      field_simp
  choose t ht e using blockwise
  exact ⟨t, ht, funext fun p => e p.1 p.2⟩

theorem isImg_unique : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w w', CovMap.IsImg Cv z w → CovMap.IsImg Cv z w' → SameOrbit w w' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w w' hw hw'
  obtain ⟨-, fr, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M
  obtain ⟨bs', fr', fl'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hG'⟩ := fr' _ (bs' z hz)
  have hne : ∀ k : NonPluckerBlocks M'.blk, basePart M'.blk z ⟨k, F'.c k⟩ ≠ 0 := fun k =>
    coord_ne_of_X_notMem (hG'.1 k)
  let c : K' → ℂ := fun k =>
    if h : ∀ p, M'.blk p ≠ some k then (basePart M'.blk z ⟨⟨k, h⟩, F'.c ⟨k, h⟩⟩)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M'.blk, c k.1 = (basePart M'.blk z ⟨k, F'.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M'.blk p ≠ some k
    · rw [hcb ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z₁ : (Σ k, ι' k) → ℂ := fun p => c p.1 * z p
  have h1 : SameOrbit z₁ z := ⟨c, hc, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mcPts_smul hA'.2.1.2.1 c hc hz
  have hb1 : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) :=
    ⟨fun k => c k.1, fun k => hc k.1, rfl⟩
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [mCoordIdeal_eq_of_sameOrbit hb1]
    exact hG'
  have hnorm : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := fun k => by
    show c k.1 * basePart M'.blk z ⟨k, F'.c k⟩ = 1
    rw [hcb k]
    exact inv_mul_cancel₀ (hne k)
  obtain ⟨h, hh⟩ := (fl' F' hF' z₁ (bs' z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨F, hF, hG⟩ := fr _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq (bs' z₁ hz₁))
  obtain ⟨z₀, a, b, e⟩ := hw z₁ h1 F' F hF' hF hG₁ hG h hh
  obtain ⟨z₀', a', b', e'⟩ := hw' z₁ h1 F' F hF' hF hG₁ hG h hh
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm a) (Cj.sameOrbit_trans
    (sameOrbit_of_isFlagOf M (Cj.sameOrbit_trans b (Cj.sameOrbit_symm b')) e e') a')

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyArithmetic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pFl_isArithVar : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) :=
  @PositivityTheory.Xgp.t_c_fl_arith

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDrop
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flag_isArithVar_and_image : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ :=
  @PositivityTheory.Xgp.t_fl_arith

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamilyStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_index_of_orthogonal_family : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r : ℕ) (v : Fin r → V), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → ∀ s, logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L = -(r * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) + Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | exact GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree <;> assumption)
end

