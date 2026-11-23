module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianSchemeBaseChangeExists
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem exists_abelianScheme_baseChange_ringHom :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) := by
  intro R R' _ _ _ A _ g hA hg
  exact ⟨(Over.pullback (spMap (algebraMap R R'))).obj A, Functor.grpObjObj,
    Limits.pullback.fst A.hom (spMap (algebraMap R R')),
    GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA _,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback _ _) hg,
    IsPullback.of_hasPullback _ _⟩

end GlobalTheory.CompanionTheory.Axis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFactsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_level_one_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := by
  first | exact @GlobalTheory.CompanionTheory.ACrisMod.acr1 | exact GlobalTheory.CompanionTheory.ACrisMod.acr1 | (intros; apply GlobalTheory.CompanionTheory.ACrisMod.acr1 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

end Norms

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

end GlobalTheory.CompanionTheory.WaveK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefSmoothOnG
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefSmooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coef_smoothOnG (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) :
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := v.2 g₀ hg₀
  refine ⟨U, fun x => ⟪w, F x⟫_ℂ, hU, hgU, ?_, fun g hg hgJ => ?_⟩
  · exact (((innerSL ℂ w).restrictScalars ℝ).contDiff.comp_contDiffOn hF)
  · exact congrArg (fun z => ⟪w, z⟫_ℂ) (hfF g hg hgJ)

theorem coef_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H),
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) :=
  fun n ε H _ _ σ v w => coef_smoothOnG n ε H σ v w

end GlobalTheory.CompanionTheory.CoefSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.ConeHaar

open PositivityTheory.RgBcC

def coneW (n : ℕ) (v : Fin n × Fin n → ℝ) : ℝ≥0∞ := ENNReal.ofReal (((hOf v).det.re ^ n)⁻¹)

def coneMeas (n : ℕ) : Measure (Fin n × Fin n → ℝ) :=
  (volume.restrict (cone n)).withDensity (coneW n)

end GlobalTheory.CompanionTheory.ConeHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverSystemCechPullNatural
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLerayPull

theorem cechHEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) : ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : GroundTheory.Arith.SchemeCoh.cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : GroundTheory.Arith.SchemeCoh.cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro n
  induction n with
  | zero =>
    intro G G' _ _ φ x
    exact _root_.GlobalTheory.CompanionTheory.CechZero.cechHZeroEquivH_pull f V hV U hU τ hτ φ x
  | succ n ih =>
    cases n with
    | zero =>
      intro G G' hG hG' φ x
      obtain ⟨α, hα⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      rw [← hα]
      exact _root_.GlobalTheory.CompanionTheory.CechOne.cechHOneEquiv_pull f V hV U hU τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α x
    | succ m =>
      intro G G' hG hG' φ x
      obtain ⟨α, hα⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      rw [← hα]
      exact _root_.GlobalTheory.CompanionTheory.CechStep.cechHEquivStep_pull f V U τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α m _ _
        (fun y => ih (injectiveSequence_goodAcyclic hCY G hG)
          (injectiveSequence_goodAcyclic hCX G' hG') α.τ₃ y) x

end GlobalTheory.CompanionTheory.CechLerayPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetAddOnesField
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AdjSum

open Matrix Polynomial

theorem det_add_ones_field {K : Type*} [Field K] {n : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) :
    (B + Matrix.of fun _ _ => (1 : K)).det = B.det + ∑ a, ∑ b, B.adjugate a b := by
  have hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin n) (Fin n) K) =
      replicateCol Unit (fun _ => (1 : K)) * replicateRow Unit (fun _ => (1 : K)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hJ, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hB)]
  have hinv : B⁻¹ = (B.det)⁻¹ • B.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have h1 : ∀ C : Matrix Unit Unit K, C.det = C () () := fun C => det_unique C
  rw [h1, hinv]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.smul_apply,
    replicateRow_apply, replicateCol_apply, one_mul, mul_one, smul_eq_mul, Finset.univ_unique,
    Finset.sum_singleton]
  rw [mul_add, mul_one]
  congr 1
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  field_simp

theorem det_add_ones {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    (A + Matrix.of fun _ _ => (1 : R)).det = A.det + ∑ a, ∑ b, A.adjugate a b := by
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have hdet : ∀ C : Matrix (Fin n) (Fin n) R, f C.det = (C.map f).det := fun C =>
    RingHom.map_det f C
  apply hf
  have h := det_add_ones_field (A.map f) (by
    rw [← hdet]
    exact (map_ne_zero_iff f hf).mpr hA)
  have hadj : (A.map f).adjugate = A.adjugate.map f := by
    have := RingHom.map_adjugate f A
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hsum : (A.map f + Matrix.of fun _ _ => (1 : K)) =
      (A + Matrix.of fun _ _ => (1 : R)).map f := by
    ext i j
    simp
  rw [hsum, ← hdet, ← hdet, hadj] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_add (f := _), map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

theorem entry (n : ℕ) (l : Fin n → ℂ) (a b : Fin n) :
    ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
        (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z)) a b =
      if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem adj_sum : ∀ (n : ℕ) (l : Fin n → ℂ), ∑ a, ∑ b, (Matrix.adjugate ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) + (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z))) a b = ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) - ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
  intro n l
  set M : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
    (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
      (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z) with hM
  have he : ∀ a b, M a b = if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := entry n l
  have hdet : M.det = ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
    rw [Matrix.det_of_upperTriangular]
    · exact Finset.prod_congr rfl fun s _ => by rw [he]; simp
    · intro i j hij
      have hij' : j < i := hij
      rw [he, if_neg (ne_of_gt hij'), if_neg (not_lt_of_gt hij')]
  have hdet1 : (M + Matrix.of fun _ _ => (1 : Polynomial ℂ)).det =
      ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) := by
    rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun s _ => by simp [he]
    · intro i j hij
      have hij' : i < j := hij
      simp [he, ne_of_lt hij', hij']
  have hne : M.det ≠ 0 := by
    rw [hdet, Finset.prod_ne_zero_iff]
    intro s _
    exact (Polynomial.monic_X_add_C (l s)).ne_zero
  have h := det_add_ones M hne
  rw [hdet1, hdet] at h
  rw [h]
  ring

end GlobalTheory.CompanionTheory.AdjSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_fderiv_field {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem fderiv_field_bracket {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A B : E →L[ℝ] E)
    {g : E} (hg : g ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ f y (B y)) g (A g) - fderiv ℝ (fun y => fderiv ℝ f y (A y)) g (B g) =
      fderiv ℝ f g (B (A g) - A (B g)) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) g :=
    ((h1.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simp))
  have hs : IsSymmSndFDerivAt ℝ f g :=
    (hf.contDiffAt (hU.mem_nhds hg)).isSymmSndFDerivAt (by simp)
  have hA := (h2.hasFDerivAt.clm_apply A.hasFDerivAt).fderiv
  have hB := (h2.hasFDerivAt.clm_apply B.hasFDerivAt).fderiv
  rw [hA, hB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_sub]
  rw [hs.eq (A g) (B g)]
  abel

theorem fderiv_add_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f + h) g v = fderiv ℝ f g v + fderiv ℝ h g v := by
  rw [fderiv_add hf hh]; rfl

end General

theorem fderiv_csmul_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (c : ℂ) (v : E) :
    fderiv ℝ (c • f) g v = c • fderiv ℝ f g v := by
  rw [fderiv_const_smul (R := ℂ) hf c]; rfl

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

@[simp] theorem mulR_apply (X g : Mat n) : mulR X g = g * X := rfl
@[simp] theorem mulL_apply (x g : Mat n) : mulL x g = x * g := rfl

theorem differentiableAt_of_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℝ f g :=
  ((hf.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp))

theorem Rd_contDiffOn (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_fderiv_field isOpen_GLs hf (mulR X)

theorem Rd_bracket (X Y : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g := by
  have := fderiv_field_bracket isOpen_GLs hf (mulR X) (mulR Y) hg
  have e : (mulR Y) ((mulR X) g) - (mulR X) ((mulR Y) g) = g * (X * Y - Y * X) := by
    show g * X * Y - g * Y * X = _
    simp [mul_sub, mul_assoc]
  exact this.trans (congrArg (fderiv ℝ f g) e)

theorem Rd_congr (X : Mat n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : Set.EqOn (Rd X f) (Rd X h) (GLs n) := by
  intro g hg
  have : f =ᶠ[nhds g] h := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) e
  simp [Rd, this.fderiv_eq]

theorem Rd_add_left (X Y : Mat n) (f : Mat n → V) : Rd (X + Y) f = Rd X f + Rd Y f := by
  funext g; simp [Rd, mul_add]

theorem Rd_smul_left (r : ℝ) (X : Mat n) (f : Mat n → V) : Rd (r • X) f = r • Rd X f := by
  funext g
  simp only [Rd, Pi.smul_apply, mul_smul_comm, map_smul]

theorem Rd_add {f h : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    Set.EqOn (Rd X (f + h)) (Rd X f + Rd X h) (GLs n) := by
  intro g hg
  exact fderiv_add_apply' (differentiableAt_of_smooth hf hg) (differentiableAt_of_smooth hh hg) _

theorem Rd_smul (c : ℂ) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro g hg
  exact fderiv_csmul_apply (differentiableAt_of_smooth hf hg) c _

def IBP : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → Cpt f →
    ∀ X, ∫ y : G n, Rd X f y.val ∂μ = 0

end GlobalTheory.CompanionTheory.RCalc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SobGL

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Idx (n : ℕ) := Bool × Fin n × Fin n

def cm {n : ℕ} (t : Idx n → ℝ) : Mat n := ∑ p, t p • bs p

def pd {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List ι → ((ι → ℝ) → V) → ((ι → ℝ) → V) :=
  fun L F => L.foldr (fun i H t => fderiv ℝ H t (Pi.single i 1)) F

def Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Idx n) → (Mat n → V) → (Mat n → V) :=
  fun L f => L.foldr (fun p H y => fderiv ℝ H y (bs p)) f

theorem pd_nil {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (ι → ℝ) → V) : pd [] F = F := rfl

theorem pd_cons {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : ι) (L : List ι) (F : (ι → ℝ) → V) :
    pd (i :: L) F = fun t => fderiv ℝ (pd L F) t (Pi.single i 1) := rfl

theorem Dw_nil {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Mat n → V) :
    Dw [] f = f := rfl

theorem Dw_cons {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Idx n)
    (L : List (Idx n)) (f : Mat n → V) :
    Dw (p :: L) f = fun y => fderiv ℝ (Dw L f) y (bs p) := rfl

end GlobalTheory.CompanionTheory.SobGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EwordCoef
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefWord

theorem eword_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) (l : List (Fin n × Fin n)), ∀ g ∈ Formalism.MainNotions.S.UJset ε, Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ) g = ⟪w, σ g (((l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v : GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ := by
  intro n ε H _ _ σ hσ v w l
  induction l with
  | nil =>
    intro g _
    rfl
  | cons p l ih =>
    intro g hg
    have hg' : Formalism.REAL.inUJ ε g := hg
    set u : GlobalTheory.SmoothVecMod.smoothVec ε σ :=
      (l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v with hu
    have h1 : Formalism.REAL.Eword ε (p :: l) (fun x => ⟪w, σ x (v : H)⟫_ℂ) g =
        Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g := rfl
    have h2 : Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g =
        Formalism.REAL.EabV ε p.1 p.2 (fun x => innerSL ℂ w (σ x (u : H))) g :=
      GlobalTheory.SmoothVecMod.eabV_congr (fun x hx => ih x hx) p.1 p.2 hg'
    have h3 := GlobalTheory.CapelliCoef.eabV_pair (innerSL ℂ w) (f := fun x => σ x (u : H)) u.2 p.1 p.2 hg'
    have h4 := GlobalTheory.SmoothVecMod.rep_eabV hσ u.2 p.1 p.2 hg'
    rw [h1, h2, ← h3, ← h4]
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl

end GlobalTheory.CompanionTheory.CoefWord
end
end

