module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def fracMap (ρ : R →+* R') (hρ : Function.Injective ρ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.map (A := R) (B := R') (K := FractionRing R) (L := FractionRing R') (j := ρ) hρ

theorem fracMap_algebraMap (ρ : R →+* R') (hρ : Function.Injective ρ) (r : R) :
    fracMap ρ hρ (algebraMap R _ r) = algebraMap R' _ (ρ r) := by
  simp [fracMap, IsFractionRing.map]

theorem jK_comp_spMap (ρ : R →+* R') (hρ : Function.Injective ρ) :
    jK R' ≫ spMap ρ = spMap (fracMap ρ hρ) ≫ jK R := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (fracMap_algebraMap ρ hρ r).symm

def fracAut (σ : R' ≃+* R') : FractionRing R' ≃+* FractionRing R' :=
  IsFractionRing.ringEquivOfRingEquiv σ

theorem fracAut_algebraMap (σ : R' ≃+* R') (x : R') :
    fracAut σ (algebraMap R' _ x) = algebraMap R' _ (σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x

theorem fracAut_fracMap {ρ : R →+* R'} (hρ : Function.Injective ρ) (σ : Gal ρ) (x : FractionRing R) :
    fracAut σ.1 (fracMap ρ hρ x) = fracMap ρ hρ x := by
  have h : ((fracAut σ.1).toRingHom.comp (fracMap ρ hρ)) = fracMap ρ hρ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [fracMap_algebraMap, fracAut_algebraMap, σ.2 r]
  exact congrArg (fun f : FractionRing R →+* FractionRing R' => f x) h

def genMap {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ) (β : G'.left ⟶ G.left)
    (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R) :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _ ≫ spMap (fracMap ρ hρ)) (by
    rw [Category.assoc, hβ, ← Category.assoc, pullback.condition, Category.assoc, jK_comp_spMap ρ hρ,
      Category.assoc])

theorem genMap_fst {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β :=
  pullback.lift_fst _ _ _

theorem genMap_snd {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (fracMap ρ hρ) :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.ConjUnitary
open Matrix

theorem unitary_of_norm_preserving {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    V ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hn : ∀ v : EuclideanSpace ℂ (Fin N), ‖toEuclideanCLM (n := Fin N) (𝕜 := ℂ) V v‖ = ‖v‖ := by
    intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simpa using h v.ofLp
  have h1 := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 hn
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← ContinuousLinearMap.mul_def, ← map_mul,
    ← map_one (toEuclideanCLM (n := Fin N) (𝕜 := ℂ))] at h1
  rw [Matrix.mem_unitaryGroup_iff']
  exact (toEuclideanCLM (n := Fin N) (𝕜 := ℂ)).injective h1

theorem conj_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    (fun j => (starRingEnd ℂ) ((M *ᵥ fun k => (starRingEnd ℂ) (z k)) j)) =
      M.map (starRingEnd ℂ) *ᵥ z := by
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem conj_frame_unitary : ∀ (K : Type) [Field K] (N : ℕ) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.ChowHt.ConjCompat A → (∀ σ, (A σ).det ≠ 0) →
    ∀ σ : K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U := by
  intro K _ N A hC hdet σ
  set B := A ((starRingEnd ℂ).comp σ) with hBdef
  set A0 := A σ with hA0
  set C := A0.map (starRingEnd ℂ) with hCdef
  set V := B⁻¹ * C with hV
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 (hdet _)
  have hA0u : IsUnit A0.det := isUnit_iff_ne_zero.2 (hdet _)
  have hnorm : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have h := hC σ (A0 *ᵥ fun k => (starRingEnd ℂ) (z k))
    rw [← hBdef, ← hA0, conj_mulVec] at h
    unfold GlobalTheory.ChowHt.frameNorm at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA0u,
      Matrix.one_mulVec, ← hV] at h
    rw [Real.sqrt_inj (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)] at h
    rw [h]
    simp
  have hVu := unitary_of_norm_preserving V hnorm
  refine ⟨star V, Unitary.star_mem hVu, ?_⟩
  have hVs : V * star V = 1 := (Matrix.mem_unitaryGroup_iff).1 hVu
  have hBV : B * V = C := by
    rw [hV, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
  rw [← hBV, Matrix.mul_assoc, hVs, Matrix.mul_one]

end GlobalTheory.ConjUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.FubiniStudyFrame

theorem exists_ne_zero_of_rel {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n N : ℕ}
    (σ : K →+* ℂ) (u : Fin n → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin n) (Fin N) K)
    (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin n → ℂ) (hw : w ≠ 0)
    (hrel : ∀ lam : Fin n → K, ∑ k, lam k • u k = 0 → ∑ k, σ (lam k) * w k = 0)
    (hb : ∀ j, b j = ∑ k, c k j • u k) (hA : A.det ≠ 0) :
    ∃ a, ∑ k, (c.map σ * A) k a * w k ≠ 0 := by
  classical
  have hx : Matrix.vecMul w (c.map σ) ≠ 0 := by
    intro hx
    apply hw
    funext l
    set r := b.repr (u l)
    have hl : ∑ k, ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) • u k = 0 := by
      have e : ∑ k, (∑ j, c k j * r j) • u k = u l := by
        calc ∑ k, (∑ j, c k j * r j) • u k = ∑ j, r j • ∑ k, c k j • u k := by
              simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
          _ = ∑ j, r j • b j := by simp only [hb]
          _ = u l := b.sum_repr (u l)
      simp only [sub_smul, Finset.sum_sub_distrib, e, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    have h2 := hrel _ hl
    have h3 : ∀ j, ∑ k, w k * σ (c k j) = 0 := fun j => by
      have := congrFun hx j
      simpa [Matrix.vecMul, dotProduct] using this
    have h4 : ∑ k, σ ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) * w k =
        w l - ∑ j, σ (r j) * ∑ k, w k * σ (c k j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_mul]
      congr 1
      · rw [Finset.sum_eq_single l]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h2
    simpa [h3] using h2
  by_contra hne
  push_neg at hne
  have h0 : Matrix.vecMul (Matrix.vecMul w (c.map σ)) A = 0 := by
    rw [Matrix.vecMul_vecMul]
    funext a
    have := hne a
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact hA (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hx, h0⟩)

theorem rel_field_of_rel_int {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {n : ℕ} (τ : 𝓞 K →+* ℂ) (u : Fin n → V)
    (w : Fin n → ℂ)
    (H : ∀ lam : Fin n → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0)
    (lam : Fin n → K) (h : ∑ k, lam k • u k = 0) :
    ∑ k, OfLattice.extEmb τ (lam k) * w k = 0 := by
  classical
  set σ := OfLattice.extEmb τ
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (Finset.univ.image lam)
  have hk : ∀ k, IsLocalization.IsInteger (𝓞 K) (d • lam k) := fun k =>
    hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  choose lam' hlam' using hk
  have hσ : ∀ x : 𝓞 K, σ (algebraMap (𝓞 K) K x) = τ x := fun x =>
    RingHom.congr_fun (OfLattice.extEmb_comp τ) x
  have h1 : ∑ k, lam' k • u k = 0 := by
    have : ∀ k, lam' k • u k = d • (lam k • u k) := fun k => by
      rw [← algebraMap_smul K (lam' k) (u k), hlam' k, Algebra.smul_def, mul_smul,
        algebraMap_smul]
    simp only [this, ← Finset.smul_sum, h, smul_zero]
  have h2 := H lam' h1
  have h3 : ∀ k, τ (lam' k) = σ (algebraMap (𝓞 K) K d) * σ (lam k) := fun k => by
    rw [← hσ, hlam' k, Algebra.smul_def, map_mul]
  simp only [h3, mul_assoc, ← Finset.mul_sum] at h2
  have hd0 : σ (algebraMap (𝓞 K) K d) ≠ 0 := by
    rw [map_ne_zero, ne_eq, ← map_zero (algebraMap (𝓞 K) K),
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.ne_zero hd
  exact (mul_eq_zero.1 h2).resolve_left hd0

end GlobalTheory.FubiniStudyFrame


open GlobalTheory.FubiniStudyFrame in
theorem GlobalTheory.FubiniStudyFrame.noCommonZero_comb : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  intro K V _ _ _ _ _ _ m N X _ p g u b c A _hg hrel hb hA τ i y hy
  classical
  set s := fun k => GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g with hs
  set w : Fin (m + 1) → ℂ := fun k => secVal p τ (s k) i y with hw_def
  have hsup := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  have hw : w ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y.1 (IsLocalRing.closedPoint ℂ) ∈ ⨆ k, nonzeroLocus (s k) by rw [hsup]; trivial)
    intro h0
    exact (secVal_ne_zero_iff (s k) hy).2 (mem_ptsIn.2 hk) (congrFun h0 k)
  have H : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0 := by
    intro lam h
    have e := congrArg (fun t => secVal p τ t i y) (hrel lam h)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, secVal_smul, Finset.sum_apply, hw_def] using e
  obtain ⟨a, ha⟩ := exists_ne_zero_of_rel (OfLattice.extEmb τ) u b c (A (OfLattice.extEmb τ)) w hw
    (rel_field_of_rel_int τ u w H) hb (hA _)
  refine ⟨a, ?_⟩
  simpa [Finset.sum_apply, hw_def] using ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def GalMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} {ρ : R →+* R'}
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') (σ : Gal ρ) (a : G'.left ⟶ G'.left) : Prop :=
  IsGrpPullback G' G' (spMap (Gal.hom σ)) a ∧
    ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutomorphismActsOnDeeperLevelLabels
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalAct


open MonObj in
theorem exists_mulEquiv_points {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  have f₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) f
  have f₂ : Surjective (spMap f) := ⟨fun y => ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem eq_id_of_frac {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (h : ∀ x, ∃ a b, x = φ a / φ b)
    (u : Sp K ⟶ Sp K) (hu : u ≫ spMap φ = spMap φ) : u = 𝟙 _ := by
  obtain ⟨j, rfl⟩ := Spec.map_surjective u
  have e : CommRingCat.ofHom φ ≫ j = CommRingCat.ofHom φ := Spec.map_injective ((Spec.map_comp _ _).trans hu)
  have e' : ∀ a, j.hom (φ a) = φ a := fun a => congrArg (fun q => q.hom a) e
  have : j = 𝟙 _ := by
    ext x
    obtain ⟨a, b, rfl⟩ := h x
    exact (map_div₀ j.hom (φ a) (φ b)).trans (by rw [e', e']; rfl)
  rw [this, Spec.map_id]


open MonObj in
theorem exists_generic_labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b) :
    ∃ w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G), (∀ x, (w x).left ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) ∧
      (∀ x y, w (x + y) = w x * w y) ∧ Function.Injective w ∧ (∀ x, w x ^ (S.r * S.N) = 1) ∧
      ∀ z, z ^ (S.r * S.N) = 1 → ∃ a, w a = z := by
  obtain ⟨e, he⟩ := exists_mulEquiv_points hb (𝟙 _) (spMap S.R.val.toRingHom) (Category.id_comp _)
  let j : Over.mk (spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) := Over.homMk (spMap S.R.val.toRingHom) (by simp)
  let k : Sp (AlgebraicClosure Ω) ⟶ Sp Ω := spMap (algebraMap Ω (AlgebraicClosure Ω))
  have : Epi k := epi_spMap_of_field _
  let k' : Over.mk (k ≫ spMap S.R.val.toRingHom) ⟶ Over.mk (spMap S.R.val.toRingHom) := Over.homMk k rfl
  let w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G) := fun x => e.symm (j ≫ ρ.pt x)
  have hw : ∀ x, e (w x) = j ≫ ρ.pt x := fun x => e.apply_symm_apply _
  have hadd : ∀ x y, w (x + y) = w x * w y := fun x y => by
    apply e.injective
    rw [map_mul, hw, hw, hw, ρ.pt_add, MonObj.comp_mul]
  let w' : Multiplicative S.Gam →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := MonoidHom.mk' (fun x => w x.toAdd) fun x y => hadd _ _
  have htor : ∀ x, w x ^ (S.r * S.N) = 1 := fun x => by
    have h0 : (S.r * S.N) • x = 0 := by
      funext i
      simp [nsmul_eq_mul]
    have h1 : (Multiplicative.ofAdd x) ^ (S.r * S.N) = 1 := by rw [← ofAdd_nsmul, h0, ofAdd_zero]
    exact (map_pow w' (Multiplicative.ofAdd x) _).symm.trans (by rw [h1, map_one])
  have key : ∀ z : Over.mk (𝟙 (Sp Ω)) ⟶ G, z ^ (S.r * S.N) = 1 → ∃! a, w a = z := fun z hz => by
    have h := ρ.pt_bij (AlgebraicClosure Ω) (k ≫ spMap S.R.val.toRingHom) (k' ≫ e z)
      ((map_pow (preHom k') (e z) _).symm.trans (by rw [← map_pow, hz, map_one, map_one]))
    refine (existsUnique_congr fun a => ?_).1 h
    constructor
    · intro ha
      apply e.injective
      rw [hw]
      refine Over.OverMorphism.ext ((cancel_epi k).1 ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left) ha)
    · rintro rfl
      rw [hw]
      exact Over.OverMorphism.ext (Category.assoc _ _ _)
  refine ⟨w, fun x => (he _).symm.trans (congrArg (fun q => q.left) (hw x)), hadd,
    fun x y h => (key _ (htor y)).unique h rfl, htor, fun z hz => (key z hz).exists⟩


open MonObj in
theorem exists_label_action {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b)
    (σ : Ω →+* Ω) (hσ : Function.Surjective σ) {t : G.left ⟶ G.left} (ht : IsGrpPullback G G (spMap σ) t) :
    ∃ a : S.Gam ≃+ S.Gam, (∀ x (w w' : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left) ∧
      ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w ≫ t = spMap σ ≫ w → a x = x := by
  obtain ⟨p, hp, hadd, hinj, htor, hsurj⟩ := exists_generic_labels ρ hb
  obtain ⟨e, he⟩ := exists_mulEquiv_points ht (𝟙 _) (spMap σ) (Category.id_comp _)
  have : Epi (spMap σ) := epi_spMap_of_field _
  let s : Over.mk (spMap σ) ⟶ Over.mk (𝟙 (Sp Ω)) := Over.homMk (spMap σ) (Category.comp_id _)
  let τ : (Over.mk (𝟙 (Sp Ω)) ⟶ G) →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := e.symm.toMonoidHom.comp (preHom s)
  have hτ : ∀ z, (τ z).left ≫ t = spMap σ ≫ z.left := fun z =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (s ≫ z)))
  have τinj : Function.Injective τ := fun z z' h => by
    refine Over.OverMorphism.ext ((cancel_epi (spMap σ)).1 ?_)
    rw [← hτ, ← hτ, h]
  have hex : ∀ x, ∃ y, p y = τ (p x) := fun x => hsurj _ (by rw [← map_pow, htor, map_one])
  choose a ha using hex
  let a' : S.Gam →+ S.Gam := AddMonoidHom.mk' a fun x y => hinj (by rw [hadd, ha, ha, ha, hadd, map_mul])
  have ainj : Function.Injective a' := fun x y h => hinj (τinj (by
    rw [← ha, ← ha]; exact congrArg p h))
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have abij : Function.Bijective a' := Finite.injective_iff_bijective.1 ainj
  have h₁ : ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w = (p x).left := fun x w h => by
    refine hb.1.hom_ext (h.trans (hp x).symm) (Eq.trans ?_ (Over.w (p x)).symm)
    refine eq_id_of_frac S.R.val.toRingHom (fun y => ?_) _ ?_
    · obtain ⟨c, hc, d, hd, rfl⟩ := S.frac y
      exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
    · rw [Category.assoc, ← hb.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (ρ.pt x))).trans (Category.comp_id _)
  have h₂ : ∀ x (w' : Sp Ω ⟶ G.left), w' ≫ t = spMap σ ≫ (p x).left → w' = (p (a x)).left := fun x w' h => by
    rw [ha]
    refine ht.1.hom_ext (h.trans (hτ _).symm) (Eq.trans ?_ (Over.w (τ (p x))).symm)
    refine eq_id_of_frac σ (fun y => ?_) _ ?_
    · obtain ⟨c, rfl⟩ := hσ y
      exact ⟨c, 1, by rw [map_one, div_one]⟩
    · rw [Category.assoc, ← ht.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (p x))).trans (Category.comp_id _)
  refine ⟨AddEquiv.ofBijective a' abij, fun x w w' hw hw' => ?_, fun x w hw hw' => ?_⟩
  · rw [h₁ x w hw] at hw'
    rw [h₂ x w' hw']
    exact hp _
  · have e₁ := h₁ x w hw
    subst e₁
    exact hinj (Over.OverMorphism.ext (h₂ x _ hw').symm)

theorem exists_galLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D σ
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  have hs : spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun y => σ.commutes _))
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a₁ = a₁ ∧
      t ≫ P₀.A.hom = P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) :=
    ⟨h₁.1.lift a₁ (P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) (by rw [Category.assoc, hs, h₁.1.w]),
      h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (X₁.ρ.P.L.pull a₁) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame X₁.ρ.P.L (fun _ => a₁) (fun _ => a₁) _ t fun _ => ht₁.symm)
  obtain ⟨a, ha, ha'⟩ := exists_label_action D.X.ρ h₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective ht
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂,
    LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, fun E => ⟨(hε E).2, ?_⟩, ha⟩,
    fun x => ?_⟩
  · refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · obtain ⟨w, hw₁, hw₂⟩ := hpt x
    refine ha' _ w hw₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, hw₁, ← Category.assoc, hs]
    · have hw : w ≫ P₀.A.hom = 𝟙 _ := by
        refine eq_id_of_frac D.X.S.R.val.toRingHom (fun y => ?_) _ ?_
        · obtain ⟨c, hc, d, hd, rfl⟩ := D.X.S.frac y
          exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
        · rw [Category.assoc, ← h₂.1.w, ← Category.assoc, hw₂, Category.assoc]
          exact (congrArg _ (Over.w (D.X.ρ.pt _))).trans (Category.comp_id _)
      rw [Category.assoc, Category.assoc, ht₂, hw, ← Category.assoc, hw, Category.id_comp, Category.comp_id]

end GlobalTheory.Poinc.GalAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacksStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  first | (exact @GlobalTheory.HTTransport.lieHer_geomAt_iff) | (exact GlobalTheory.HTTransport.lieHer_geomAt_iff) | (intros; apply GlobalTheory.HTTransport.lieHer_geomAt_iff  <;> assumption)
end

