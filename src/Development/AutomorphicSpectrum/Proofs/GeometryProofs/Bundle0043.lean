module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingIntegralFraction
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FracExt

def genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ :=
  ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (genCpt ξ).2 = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, e]
  exact hs

theorem exists_frac {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c (genCpt M.ξ) := ⟨hc, fun _ => mem_regAt_genCpt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ := ((_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c _ hp).2 a).1 (mem_regAt_genCpt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem algebraMap_mem_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) {a : Ω}
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem exists_integral_div : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω']
    [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω',
      IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧
        v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ _ _ _ c hc a
  haveI : IsFractionRing (chRing o x c) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, hu, v, hv, e⟩ := exists_frac M hc z
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, e⟩
  have halg : IsAlgebraic (chRing o x c) a := by
    haveI : Algebra.IsAlgebraic (chRing o x c) Ω' :=
      (IsFractionRing.comap_isAlgebraic_iff (A := chRing o x c) (K := Ω) (C := Ω')).2 inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨y, hy0, hi⟩ := halg.exists_integral_multiple
  have hy0' : (y : Ω) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hv : algebraMap Ω Ω' (y : Ω) ≠ 0 := (map_ne_zero _).2 hy0'
  let φ : chRing o x c →+* chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((algebraMap Ω Ω').comp (chRing o x c).val.toRingHom).codRestrict _
      fun r => algebraMap_mem_chRing x Ω' c r.2
  have hb := IsIntegral.map_of_comp_eq φ (RingHom.id Ω') (by ext r; rfl) hi
  refine ⟨y • a, algebraMap Ω Ω' (y : Ω), hb, algebraMap_mem_chRing x Ω' c y.2, hv, ?_⟩
  have e : y • a = algebraMap Ω Ω' (y : Ω) * a := by
    rw [Algebra.smul_def]; rfl
  rw [e, mul_div_cancel_left₀ _ hv]

end GlobalTheory.CompanionTheory.Ar.FracExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexConjugationHermCompat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

section Basic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem conjPt_conjPt (z : (Σ k, ι k) → ℂ) : conjPt (conjPt z) = z := by
  funext p
  simp [conjPt]

theorem evC_conjPt (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    evC (conjPt z) f = starRingEnd ℂ (evC z f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]
    simp [conjPt]

def conjCLM : ((Σ k, ι k) → ℂ) →L[ℝ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p =>
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (Σ k, ι k) => ℂ) p)

theorem conjCLM_apply (z : (Σ k, ι k) → ℂ) : conjCLM z = conjPt z := by
  funext p
  simp [conjCLM, conjPt]

theorem conjPt_mem_mcPts_iff (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) :
    conjPt z ∈ mcPts P ↔ z ∈ mcPts P := by
  have key : ∀ w : (Σ k, ι k) → ℂ, w ∈ mcPts P → conjPt w ∈ mcPts P := by
    rintro w ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := h1 k
      exact ⟨i, by simpa [conjPt] using hi⟩
    · have := evC_conjPt w f
      simp only [evC] at this
      rw [this, h2 f hf, map_zero]
  refine ⟨fun h => ?_, key z⟩
  simpa [conjPt_conjPt] using key _ h

theorem conjLine_smooth (A : HermLine ι) (hA : IsSmoothHerm A) : IsSmoothHerm (conjLine A) := by
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => conjCLM z)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := (conjCLM (ι := ι)).contDiff.contDiffOn
  have := ContDiffOn.comp (g := A.h) (f := fun z : (Σ k, ι k) → ℂ => conjCLM z)
    (s := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (t := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA hc (fun z hz k => by
      obtain ⟨i, hi⟩ := hz k
      refine ⟨i, ?_⟩
      show conjCLM z ⟨k, i⟩ ≠ 0
      rw [conjCLM_apply]
      simpa [conjPt] using hi)
  unfold IsSmoothHerm
  refine this.congr fun z _ => ?_
  simp [conjLine, conjCLM_apply]

theorem logNorm_conjLine (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm (conjLine A) s z = logNorm A s (conjPt z) := by
  have h := evC_conjPt z s
  simp only [evC] at h
  simp only [logNorm, conjLine]
  rw [h, RCLike.norm_conj]

theorem conjLine_tensor (A B : HermLine ι) :
    conjLine (A.tensor B) = (conjLine A).tensor (conjLine B) := rfl

theorem conjLine_conjLine (A : HermLine ι) : conjLine (conjLine A) = A := by
  cases A with
  | mk a h pos smul =>
    simp only [conjLine, HermLine.mk.injEq, heq_eq_eq, true_and]
    funext z
    rw [conjPt_conjPt]

end Basic

theorem conj_basic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], (∀ (P : Ideal (MRing ι)) z, conjPt z ∈ mcPts P ↔ z ∈ mcPts P) ∧ (∀ (z : (Σ k, ι k) → ℂ) f, evC (conjPt z) f = starRingEnd ℂ (evC z f)) ∧ (∀ A : HermLine ι, IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ (∀ (A : HermLine ι) s z, logNorm (conjLine A) s z = logNorm A s (conjPt z)) ∧ (∀ A B : HermLine ι, conjLine (A.tensor B) = (conjLine A).tensor (conjLine B)) ∧ ∀ A : HermLine ι, conjLine (conjLine A) = A :=
  fun _ _ _ _ => ⟨conjPt_mem_mcPts_iff, evC_conjPt, conjLine_smooth, logNorm_conjLine, conjLine_tensor, conjLine_conjLine⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_mcPts_iff_exists_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ w : (Σ k, J k) → ℂ, w ∈ mcPts (mCoordIdeal y) ↔ ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  intro X Ω _ ξ K _ J _ y tie w
  have key := _root_.GlobalTheory.CompanionTheory.Ar.tie_points X Ω ξ K J y tie ℂ
  have hval : ∀ g : MvPolynomial (Σ k, J k) ℤ,
      MvPolynomial.aeval w g = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) := by
    intro g
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  constructor
  · rintro ⟨hne, hvan⟩
    obtain ⟨z, ⟨hz, hc⟩, -⟩ := key.1 w
      (fun k => (hne k).imp fun _ h => isUnit_iff_ne_zero.mpr h)
      (fun g hg => by rw [hval]; exact hvan g hg)
    exact ⟨z, hz, hc⟩
  · rintro ⟨z, hz, hc⟩
    refine ⟨fun k => (hc.1 k).imp fun _ h => h.ne_zero, fun f hf => ?_⟩
    rw [← hval]
    exact (key.2.2 z w hz hc).1 f hf

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpecialFibreConstant
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem unitAt_of_localLifts_of_unitAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) :=
  @PositivityTheory.Xgn.function_on_connected_fibre_unit

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenOnChart
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChCoh

def IsU {Ω : Type} [Field Ω] (S : Subring Ω) (a : Ω) : Prop := a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S

section Units

variable {Ω : Type} [Field Ω] {S : Subring Ω}

theorem IsU.one : IsU S 1 := ⟨one_ne_zero, S.one_mem, by simpa using S.one_mem⟩

theorem IsU.mul {a b : Ω} (ha : IsU S a) (hb : IsU S b) : IsU S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem IsU.of_mul {a b : Ω} (ha : a ∈ S) (hb : b ∈ S) (h : IsU S (a * b)) : IsU S a := by
  have ha0 := left_ne_zero_of_mul h.1
  have hb0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact S.mul_mem hb h.2.2

theorem IsU.of_isUnit {a : S} (h : IsUnit a) : IsU S (a : Ω) := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  have hb' : (a : Ω) * (b : Ω) = 1 := by exact_mod_cast congrArg (Subtype.val) hb
  have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hb'
  refine ⟨h0, a.2, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hb']
  exact b.2

end Units

def satIdeal {A E : Type} [CommRing A] [AddCommGroup E] [Module A E] (S : Submodule A E) (f : A) (e : E) : Ideal A where
  carrier := {a | ∃ k : ℕ, (f ^ k * a) • e ∈ S}
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have : (f ^ (k + l) * (a + b)) • e = f ^ l • ((f ^ k * a) • e) + f ^ k • ((f ^ l * b) • e) := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    rw [this]
    exact S.add_mem (S.smul_mem _ hk) (S.smul_mem _ hl)
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (f ^ k * (c • a)) • e = c • ((f ^ k * a) • e) := by
      simp only [smul_smul, smul_eq_mul]
      congr 1
      ring
    rw [this]
    exact S.smul_mem _ hk

section Abstract

variable {A : Type} [CommRing A] {Ω : Type} [Field Ω] (ι : A →+* Ω) {E : Type} [AddCommGroup E] [Module Ω E]
  [Module A E]

theorem clear_denoms (hsm : ∀ (a : A) (e : E), a • e = ι a • e) {S : Subring Ω}
    (hfrac : ∀ a ∈ S, ∃ u v : A, IsU S (ι v) ∧ a = ι u / ι v) (s : Set E) {e : E}
    (he : e ∈ Submodule.span S s) : ∃ v : A, IsU S (ι v) ∧ v • e ∈ Submodule.span A s := by
  induction he using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simpa using IsU.one, by simpa using Submodule.subset_span hx⟩
  | zero => exact ⟨1, by simpa using IsU.one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv, h⟩ := hx
    obtain ⟨w, hw, h'⟩ := hy
    refine ⟨v * w, by rw [map_mul]; exact hv.mul hw, ?_⟩
    have : (v * w) • (x + y) = w • (v • x) + v • (w • y) := by
      simp only [smul_add, smul_smul, mul_comm]
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ h')
  | smul r x _ hx =>
    obtain ⟨v, hv, h⟩ := hx
    obtain ⟨u, w, hw, hr⟩ := hfrac r r.2
    refine ⟨w * v, by rw [map_mul]; exact hw.mul hv, ?_⟩
    have : (w * v) • (r • x) = u • (v • x) := by
      have h1 : r • x = (r : Ω) • x := rfl
      rw [h1, hsm, hsm, hsm, smul_smul, smul_smul, map_mul, hr]
      congr 1
      have := hw.1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ h

theorem mem_of_mem_spanA (hsm : ∀ (a : A) (e : E), a • e = ι a • e) {S : Subring Ω} (hAS : ∀ a, ι a ∈ S)
    {s : Set E} {e : E} (he : e ∈ Submodule.span A s) : e ∈ Submodule.span S s := by
  induction he using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    rw [hsm]
    exact Submodule.smul_mem _ (⟨ι a, hAS a⟩ : S) hx

variable {Pt : Type} (R : Pt → Subring Ω)

theorem pow_smul_mem (hsm : ∀ (a : A) (e : E), a • e = ι a • e) (hAR : ∀ q a, ι a ∈ R q)
    (hfrac : ∀ q, ∀ a ∈ R q, ∃ u v : A, IsU (R q) (ι v) ∧ a = ι u / ι v)
    (hprime : ∀ P : Ideal A, P.IsPrime → ∃ q : Pt, ∀ u : A, u ∈ P ↔ ¬ IsU (R q) (ι u))
    (L : ∀ q, Submodule (R q) E) {f g : A} {s t : Set E}
    (hf : ∀ q, IsU (R q) (ι f) → L q = Submodule.span (R q) s)
    (hg : ∀ q, IsU (R q) (ι g) → L q = Submodule.span (R q) t) {e : E} (he : e ∈ s) :
    ∃ m : ℕ, ∀ q, IsU (R q) (ι g) → (ι f) ^ m • e ∈ L q := by
  have hrad : g * f ∈ (satIdeal (Submodule.span A t) g e).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hn
    obtain ⟨q, hq⟩ := hprime P hP
    have hgf : IsU (R q) (ι g * ι f) := by
      rw [← map_mul]
      exact not_not.1 fun h => hn ((hq _).2 h)
    have hg' : IsU (R q) (ι g) := IsU.of_mul (hAR q g) (hAR q f) hgf
    have hf' : IsU (R q) (ι f) := IsU.of_mul (hAR q f) (hAR q g) (by rwa [mul_comm])
    have hmem : e ∈ Submodule.span (R q) t := by
      rw [← hg q hg', hf q hf']
      exact Submodule.subset_span he
    obtain ⟨v, hv, hve⟩ := clear_denoms ι hsm (hfrac q) t hmem
    have hvJ : v ∈ satIdeal (Submodule.span A t) g e := ⟨0, by simpa using hve⟩
    exact (hq v).1 (hJP hvJ) hv
  obtain ⟨m, k, hk⟩ := hrad
  refine ⟨m, fun q hgq => ?_⟩
  rw [hg q hgq]
  have h1 := mem_of_mem_spanA ι hsm (hAR q) hk
  rw [hsm] at h1
  have h2 : (ι f) ^ m • e = ((ι g ^ (k + m))⁻¹) • (ι (g ^ k * (g * f) ^ m) • e) := by
    rw [smul_smul]
    congr 1
    have := hgq.1
    simp only [map_mul, map_pow, mul_pow, pow_add]
    field_simp
  rw [h2]
  exact Submodule.smul_mem _ (⟨(ι g ^ (k + m))⁻¹, by rw [← inv_pow]; exact pow_mem hgq.2.2 _⟩ : R q) h1

theorem finite_gen (hsm : ∀ (a : A) (e : E), a • e = ι a • e) (hAR : ∀ q a, ι a ∈ R q)
    (hfrac : ∀ q, ∀ a ∈ R q, ∃ u v : A, IsU (R q) (ι v) ∧ a = ι u / ι v)
    (hprime : ∀ P : Ideal A, P.IsPrime → ∃ q : Pt, ∀ u : A, u ∈ P ↔ ¬ IsU (R q) (ι u))
    (hloc : ∀ q, IsLocalRing (R q)) (L : ∀ q, Submodule (R q) E)
    (hcover : ∀ p : Pt, ∃ (f : A) (n : ℕ) (b : Fin n → E), IsU (R p) (ι f) ∧
      ∀ q, IsU (R q) (ι f) → L q = Submodule.span (R q) (Set.range b)) :
    ∃ (n : ℕ) (b : Fin n → E), ∀ q, L q = Submodule.span (R q) (Set.range b) := by
  choose F n b hF hL using hcover
  have htop : Ideal.span (Set.range F) = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨q, hq⟩ := hprime P hP.isPrime
    exact (hq (F q)).1 (hle (Ideal.subset_span ⟨q, rfl⟩)) (hF q)
  have h1 : (1 : A) ∈ Ideal.span (Set.range F) := by rw [htop]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have hsome : ∀ q, ∃ l ∈ c.support, IsU (R q) (ι (F l)) := by
    intro q
    by_contra hn
    push_neg at hn
    letI := hloc q
    let φ : A →+* R q := ι.codRestrict (R q) (hAR q)
    have hmem : (1 : A) ∈ (IsLocalRing.maximalIdeal (R q)).comap φ := by
      rw [← hc]
      refine Ideal.sum_mem _ fun l hl => Ideal.mul_mem_left _ _ ?_
      show φ (F l) ∈ IsLocalRing.maximalIdeal (R q)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hn l hl (IsU.of_isUnit hu)
    have h1' : (1 : R q) ∈ IsLocalRing.maximalIdeal (R q) := by simpa using hmem
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1'
  have hm : ∀ (l : Pt) (i : Fin (n l)), ∃ m : ℕ, ∀ q, (ι (F l)) ^ m • b l i ∈ L q := by
    intro l i
    have h := fun j => pow_smul_mem ι R hsm hAR hfrac hprime L (f := F l) (g := F j) (hL l) (hL j)
      (e := b l i) ⟨i, rfl⟩
    choose m hm using h
    refine ⟨c.support.sup m, fun q => ?_⟩
    obtain ⟨j, hj, hu⟩ := hsome q
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) hj)
    rw [hd, add_comm, pow_add, mul_smul]
    exact (L q).smul_mem (⟨(ι (F l)) ^ d, pow_mem (hAR q _) _⟩ : R q) (hm j q hu)
  choose m hm using hm
  let g : (Σ l : c.support, Fin (n l)) → E := fun t => (ι (F t.1)) ^ (m t.1 t.2) • b t.1 t.2
  let eq := Fintype.equivFin (Σ l : c.support, Fin (n l))
  refine ⟨_, g ∘ eq.symm, fun q => ?_⟩
  rw [EquivLike.range_comp]
  apply le_antisymm
  · obtain ⟨l, hl, hu⟩ := hsome q
    rw [hL l q hu, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : b l i = ((ι (F l))⁻¹) ^ (m l i) • g ⟨⟨l, hl⟩, i⟩ := by
      show _ = _ • (ι (F l)) ^ (m l i) • b l i
      rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hu.1, one_pow, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ (⟨_, pow_mem hu.2.2 _⟩ : R q) (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hm _ _ q

end Abstract

end GlobalTheory.CompanionTheory.Ar.ChCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstantStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_herm_unit_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GreenCurrentIntegralFormula
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ptsIntegral_place : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ), OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ z, PtOver y φ σ z → u z = t σ) → (∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) → ptsIntegral W (pot L) u = ∑ σ : F →+* ℂ, t σ * ptsIntegral W (pot L) (χ σ) :=
  PositivityTheory.Xgn.integral_over_place_density

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilySymmetric
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem movePositionToLast : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (e : ℕ) (L : Fin (e + 1) → HermLine ι) (i : Fin (e + 1)), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → I P (e + 1) L = I P (e + 1) (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i)) := by
  intro K _ ι _ I hI P e L i hP hL
  let σ : Equiv.Perm (Fin (e + 1)) := (finSuccEquivLast (n := e)).trans (finSuccEquiv' i).symm
  have h : (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i) : Fin (e + 1) → HermLine ι) = L ∘ σ := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [σ]
    · simp [σ]
  rw [h]
  exact (hI.1 P (e + 1) L σ hP hL).symm

end GlobalTheory.CompanionTheory.Ar.Cmp
end

