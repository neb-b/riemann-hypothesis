module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.ClosedPt

variable {ι : Type} {m : ι → ℕ}

theorem par_zero_top {K : Type} [Field K] {g : Mat m K} (h : ∀ τ, (g τ).det ≠ 0) : Par 0 ⊤ g := fun τ =>
  ⟨fun _ _ => trivial, h τ, trivial, fun _ _ hi _ => absurd hi (Nat.not_lt_zero _)⟩

theorem map_mul_inv {R K : Type} [CommRing R] [Field K] (g : R →+* K) (N₁ N₂ : Mat m R) (τ : ι)
    (hu : IsUnit (N₂ τ).det) : (N₁.map g * (N₂.map g)⁻¹) τ = (N₁ τ * (N₂ τ)⁻¹).map g := by
  have e : (N₂ τ).map g * ((N₂ τ)⁻¹).map g = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ g.map_zero g.map_one]
  show (N₁ τ).map g * ((N₂ τ).map g)⁻¹ = _
  rw [Matrix.map_mul, Matrix.inv_eq_right_inv e]

theorem descend {R L : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field L] [Algebra R L]
    [IsFractionRing R L] (N₁ N₂ : Mat m R)
    (h₁ : ∀ τ, (N₁.map (IsLocalRing.residue R) τ).det ≠ 0)
    (h₂ : ∀ τ, (N₂.map (IsLocalRing.residue R) τ).det ≠ 0)
    (hL : Par m ⊤ (N₁.map (algebraMap R L) * (N₂.map (algebraMap R L))⁻¹)) :
    Par m ⊤ (N₁.map (IsLocalRing.residue R) * (N₂.map (IsLocalRing.residue R))⁻¹) := by
  have hu : ∀ τ, IsUnit (N₂ τ).det := fun τ => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    exact h₂ τ
  have hP := (par_zero_top h₁).mul (par_zero_top h₂).inv
  intro τ
  refine ⟨fun _ _ => trivial, hP.det_ne τ, trivial, fun i j hi hij => ?_⟩
  have h0 := (hL τ).2.2.2 i j hi hij
  rw [map_mul_inv _ _ _ τ (hu τ)] at h0
  rw [map_mul_inv _ _ _ τ (hu τ)]
  have h0' : algebraMap R L ((N₁ τ * (N₂ τ)⁻¹) i j) = 0 := h0
  show IsLocalRing.residue R ((N₁ τ * (N₂ τ)⁻¹) i j) = 0
  rw [(map_eq_zero_iff _ (IsFractionRing.injective R L)).1 h0', map_zero]

variable {F : Type} [Field F]

noncomputable def vals {Y : Var F} {R : Type} [CommRing R] [IsLocalRing R] (v : Sp R ⟶ Y.X) (M : Mat m Y.Fn)
    (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) : Mat m R :=
  fun τ a b => RatModel.valLoc (M := ratOf Y) v _ specializes_rfl ⟨M τ a b, hM τ a b⟩

theorem map_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    (M : Mat m Y.Fn) (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) :
    M.map ((ratOf Y).val (spMap σ ≫ v)) = (vals v M hM).map σ := by
  funext τ
  ext a b
  have := RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl ⟨M τ a b, hM τ a b⟩
  exact this

theorem par_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    {M : Mat m Y.Fn} (hM : Par 0 ((ratOf Y).O (v (IsLocalRing.closedPoint R))).toSubring M) :
    Par 0 ⊤ (M.map ((ratOf Y).val (spMap σ ≫ v))) :=
  Par.map_of hM _ (σ.comp (RatModel.valLoc (M := ratOf Y) v _ specializes_rfl))
    (fun x => RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl x)

end GlobalTheory.FlagBundle.ClosedPt

namespace GlobalTheory.FlagBundle.ClosedPt

theorem closedPt_comp {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (v : Sp R ⟶ Z) :
    (spMap (IsLocalRing.residue R) ≫ v) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      v (IsLocalRing.closedPoint R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact congrArg v (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))

theorem gen_specializes {R L : Type} [CommRing R] [IsLocalRing R] [Field L] [Algebra R L] {Z : Scheme.{0}}
    (v : Sp R ⟶ Z) (w : Sp L) : (spMap (algebraMap R L) ≫ v) w ⤳ v (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint (spMap (algebraMap R L) w)).map v.continuous
  convert h using 1
  exact Scheme.Hom.comp_apply _ _ _

end GlobalTheory.FlagBundle.ClosedPt


open GlobalTheory.FlagBundle.ClosedPt in
theorem GlobalTheory.FlagBundle.coBear_closedPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ R _ _ _ L _ _ _ v₁ v₂ e hgen
  have sub₁ := hR₁.2.1
  have sub₂ := hR₂.2.1
  have hf₁ : f₁ (v₁ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) :=
    (Scheme.Hom.comp_apply _ _ _).symm
  have hf₂ : f₂ (v₂ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) := by
    rw [e]; exact (Scheme.Hom.comp_apply _ _ _).symm
  obtain ⟨A, hA⟩ := Eb.nonempty ((v₁ ≫ f₁) (IsLocalRing.closedPoint R))
  obtain ⟨A₁, hA₁⟩ := S₁.nonempty (v₁ (IsLocalRing.closedPoint R))
  obtain ⟨A₂, hA₂⟩ := S₂.nonempty (v₂ (IsLocalRing.closedPoint R))
  have hM₁ := sub₁ _ A₁ hA₁ A (by rw [hf₁]; exact hA)
  have hM₂ := sub₂ _ A₂ hA₂ A (by rw [hf₂]; exact hA)

  obtain ⟨B, hB, hg, hgP, hb1, hb2⟩ := hgen
  have hA₁g : A₁ ∈ S₁.S ((spMap (algebraMap R L) ≫ v₁) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₁ (gen_specializes v₁ _)
  have hA₂g : A₂ ∈ S₂.S ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hAg : A ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact Fr.mem_of_specializes hA (gen_specializes (v₁ ≫ f₁) _)
  have hBg : B ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact hB
  have heq : (spMap (algebraMap R L) ≫ v₁) ≫ f₁ = (spMap (algebraMap R L) ≫ v₂) ≫ f₂ := by
    rw [Category.assoc, Category.assoc, e]
  have hH := par_val (algebraMap R L) v₁ hM₁
  have hself : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (algebraMap R L) ≫ v₁)))
      (spMap (algebraMap R L) ≫ v₁) :=
    ⟨A₁, hA₁g, by rw [Mat.mul_inv hH.det_ne]; exact Par.one⟩
  obtain ⟨A₂', hA₂', hpar⟩ := _root_.GlobalTheory.FlagBundle.Bears.transfer F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ L _ _ heq A hAg B hBg
    _ hg hself hb1 hb2

  have hsp₂ := gen_specializes (L := L) v₂ (IsLocalRing.closedPoint L)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring
      (A₂ * (A.map φ₂)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y₂) (spMap (algebraMap R L) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint L))
  have hv : ∀ x : ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring,
      (ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ₂)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ₂)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) *
        (A₂ * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one] at hL
  rw [map_val (algebraMap R L) v₁ _ (fun τ a b => (hM₁ τ).1 a b),
    map_val (algebraMap R L) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL

  have hk₁ := par_val (IsLocalRing.residue R) v₁ hM₁
  have hk₂ := par_val (IsLocalRing.residue R) v₂ hM₂
  have hD := descend _ _ (by rw [← map_val]; exact hk₁.det_ne) (by rw [← map_val]; exact hk₂.det_ne) hL
  rw [← map_val, ← map_val] at hD
  have hAk : A ∈ Eb.S ((spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    (congrArg (fun z => A ∈ Eb.S z) (closedPt_comp (v₁ ≫ f₁))).mpr hA
  have hb₁ : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₁) :=
    ⟨A₁, (congrArg (fun z => A₁ ∈ S₁.S z) (closedPt_comp v₁)).mpr hA₁, by
      rw [Mat.mul_inv hk₁.det_ne]; exact Par.one⟩
  have hb₂ : Bears S₂ φ₂ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ S₂.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  exact ⟨A, hAk, _, hk₁, hb₁, hb₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ModelCharts

theorem exists_etale_coords_of_opens {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (D : ℕ)
    (W : X.Opens) [SmoothOfRelativeDimension D (W.ι ≫ p)] {z : X} (hz : z ∈ W) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ z ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have hzr : z ∈ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact hz
  obtain ⟨z', rfl⟩ := hzr
  obtain ⟨U', x', hU', hzU', hx'⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := W.ι ≫ p) (D := D) z'
  let e : Γ(X, W.ι ''ᵁ U') ≃+* Γ(W, U') := (W.ι.appIso U').commRingCatIsoToRingEquiv
  refine ⟨W.ι ''ᵁ U', fun a => e.symm (x' a), hU'.image_of_isOpenImmersion W.ι, ⟨z', hzU', rfl⟩, ?_⟩
  have h2 : (W.ι ≫ p).appLE ⊤ U' (by simp) =
      p.appLE ⊤ (W.ι ''ᵁ U') (by simp) ≫ (W.ι.appIso U').hom := by
    first
    | rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    | (rw [Scheme.Hom.appIso_hom']; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    | simp [Scheme.Hom.appIso_hom, Scheme.Hom.appLE, Scheme.Hom.comp_app]
    | (simp only [Scheme.Hom.appIso_hom']; rw [Scheme.Hom.appLE_comp_appLE])
  have halg : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U' = (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX
    rw [h2]
    rfl
  have heq : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U') x' =
      (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp
        (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) fun a => e.symm (x' a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [halg]
    · intro i; simp
  rw [heq] at hx'
  have h3 := RingHom.Etale.respectsIso.left _ e.symm hx'
  convert h3 using 1
  ext <;> simp

set_option maxHeartbeats 1000000 in
private theorem exists_algChart_mem_source {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := by
  obtain ⟨a, ha⟩ := y
  obtain ⟨τ', hcomp⟩ : ∃ τ' : K →+* ℂ, τ'.comp (algebraMap R K) = τ :=
    ⟨IsFractionRing.lift hτ, RingHom.ext fun r => IsFractionRing.lift_algebraMap hτ r⟩
  have hsp : a ≫ p = Spec.map (CommRingCat.ofHom τ') ≫ spMap (algebraMap R K) := by
    rw [ha]; unfold spMap; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  obtain ⟨b, hb⟩ : ∃ b, b ≫ j = a := ⟨h.lift a (Spec.map (CommRingCat.ofHom τ')) hsp, h.lift_fst _ _ _⟩
  haveI : Flat (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat K (nonZeroDivisors R)
  haveI : SurjectiveOnStalks (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2 ?_
    rw [CommRingCat.hom_ofHom]
    exact RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors R) K
  obtain ⟨W, hW, hsm⟩ := GlobalTheory.GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback h D
    (b (IsLocalRing.closedPoint ℂ))
  haveI := hsm
  have hz : a (IsLocalRing.closedPoint ℂ) ∈ W := by
    rw [← hb]
    first | exact hW | simpa using hW
  obtain ⟨U, x, hU, hzU, hx⟩ := exists_etale_coords_of_opens p D W hz
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale (σ := τ) hU x hx (y := ⟨a, ha⟩)
    (GlobalTheory.CxPts.mem_ptsIn.2 hzU)
  exact ⟨c, hc⟩

theorem exists_chart {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := exists_algChart_mem_source h hτ y

end GlobalTheory.ModelCharts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
section
open MeasureTheory GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartGlue

theorem glueMeas_add_of_compat_on : ∀ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] {n : ℕ} {κ : Type} (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ (ρ ρ' : κ → Y → ℝ≥0∞),
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) →
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ' j y) →
    (∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))) →
    glueMeas e (fun i y => ρ i y + ρ' i y) S = glueMeas e ρ S + glueMeas e ρ' S := by
  intro Y _ _ _ _ n κ e hd hcov S hS ρ ρ' hρ hρ' hAE

  have same : ∀ (τ τ' : κ → Y → ℝ≥0∞), (∀ i y, y ∈ S → τ i y = τ' i y) →
      glueMeas e τ S = glueMeas e τ' S := by
    intro τ τ' h
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := τ) (ρ' := τ') (c := 1) ENNReal.one_ne_top hS
      (fun i y _ hy => by rw [one_mul]; exact h i y hy)
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [Measure.smul_apply, smul_eq_mul, one_mul, Measure.restrict_apply_self] using this

  have compat : ∀ (τ : κ → Y → ℝ≥0∞), (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      τ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * τ j y) →
      ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (τ i) y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * S.indicator (τ j) y := by
    intro τ hτ i j y hi hj
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hτ i j y hy hi hj
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have cσ := compat ρ hρ
  have cσ' := compat ρ' hρ'
  have cs : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (ρ i) y + S.indicator (ρ' i) y =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * (S.indicator (ρ j) y + S.indicator (ρ' j) y) := by
    intro i j y hi hj
    rw [mul_add, cσ i j y hi hj, cσ' i j y hi hj]

  have aem : ∀ i (A : Set Y), MeasurableSet A → A ⊆ (e i).source →
      AEMeasurable (fun v => S.indicator (ρ i) ((e i).symm v)) (volume.restrict ((e i) '' A)) := by
    intro i A hAm hA
    have hT : MeasurableSet ((e i).target ∩ (e i).symm ⁻¹' S) := by
      rw [← (e i).image_source_inter_eq']
      exact measurableSet_image (e i) ((e i).open_source.measurableSet.inter hS) Set.inter_subset_left
    have hg := ((aemeasurable_indicator_iff hT).2 (hAE i)).mono_measure
      (Measure.restrict_le_self (s := (e i) '' A))
    refine hg.congr ((ae_restrict_iff' (measurableSet_image (e i) hAm hA)).2
      (Filter.Eventually.of_forall ?_))
    rintro _ ⟨y, hy, rfl⟩
    have ht : (e i) y ∈ (e i).target := (e i).map_source (hA hy)
    show _ = S.indicator (ρ i) ((e i).symm ((e i) y))
    by_cases hs : (e i).symm ((e i) y) ∈ S
    · rw [Set.indicator_of_mem (show (e i) y ∈ (e i).target ∩ (e i).symm ⁻¹' S from ⟨ht, hs⟩),
        Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem (show (e i) y ∉ (e i).target ∩ (e i).symm ⁻¹' S from fun h => hs h.2),
        Set.indicator_of_notMem hs]
  have key : glueMeas e (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y) =
      glueMeas e (fun i => S.indicator (ρ i)) + glueMeas e (fun i => S.indicator (ρ' i)) := by
    refine ext_of_cover (fun i => (e i).source) (fun i => (e i).open_source) hcov fun i A hA hAi => ?_
    rw [Measure.add_apply, glueMeas_apply e _ hd cs i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ i)) hd cσ i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ' i)) hd cσ' i hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi, chartMeas_apply_of_subset _ _ hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi]
    exact lintegral_add_left' (aem i A hA hAi) _
  rw [same (fun i y => ρ i y + ρ' i y) (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y)
      (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ (fun i => S.indicator (ρ i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ' (fun i => S.indicator (ρ' i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    key, Measure.add_apply]

end GlobalTheory.ChartGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7}

def FixRed (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd)
    (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) : Prop :=
  ∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv) ∧ ∀ k ∈ X.B.I.Kset, ∀ i,
    X.B.I.fmat k *ᵥ incl X.B.I (b kv i) -
      ∑ j, (((((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) •
        incl X.B.I (b kv j) ∈ wLf X (D.naut.plGw kv.1 kv.2)

theorem goodAt_of_fixRed {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (hf : FixRed X red b) :
    ∀ k ∈ X.B.I.Kset, GoodAt X k (red k) :=
  fun k hk kv => ⟨b kv, (hf kv).1, (hf kv).2 k hk⟩

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermRe
section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def hermRe (H : Formalism.L2.Herm.ColsHermS D) : Formalism.L2.Herm.ColsHermS (reD D Z) :=
  { H with
    base := { H.base with }
    atT := fun u => { H.atT u with }
    ad := { H.ad with } }

end GlobalTheory.Mem.SRe.ColRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedPull

variable {X X' Z : Scheme.{0}}

theorem val_pull_g (B : LB X) (a : Z ⟶ X) (i i' : (B.pull a).ι)
    (l : (B.pull a).U i ⊓ (B.pull a).U i' ≤ a ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit))) :
    ((B.pull a).g i i').val = (a.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
  have : (B.pull a).g i i' = res l (pullU a _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

end GlobalTheory.TrueGeo.InducedPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameC
section
set_option autoImplicit false

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign

theorem mContDiffAt_domGram {m r : ℕ} {k : WithTop ℕ∞} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : MContDiffAt k (domGram m r) x := by
  have h : MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) x := fun a b => by
    simp only [Matrix.of_apply]
    fun_prop
  exact (((mContDiffAt_const 1).sub (h.mul h.conjTranspose)).inv hx).transpose

theorem isUnit_det_domGram {m r : ℕ} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : IsUnit (domGram m r x).det := by
  rw [domGram, det_transpose]
  exact isUnit_nonsing_inv_det _ hx

theorem isNegSq_curv_of_changeFrame_comp {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n)
    (W : V n → Matrix (Fin m) (Fin m) ℂ) (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ) (hκ : 0 < κ)
    (hG : ∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ))
    (hZ : ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u)
    (hW : ∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u)
    (hWu : IsUnit (W v).det) (hpos : (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef)
    (hneg : IsNegSq (curv (domGram m r) (Z v)) r) : IsNegSq (curv G v) r := by
  obtain ⟨S, T, hS, hF⟩ := hneg
  have hu : IsUnit (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).det :=
    (isUnit_iff_isUnit_det _).1 hpos.isUnit
  have hD2 : MContDiffAt 2 (domGram m r) (Z v) := mContDiffAt_domGram _ hu
  have hDu : IsUnit (domGram m r (Z v)).det := isUnit_det_domGram _ hu
  have hZ2 : ContDiffAt ℂ 2 Z v := (GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hZ).contDiffAt
  have hW2 : MContDiffAt 2 W v := fun i j =>
    ((GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 (hW i j)).contDiffAt (n := 2)).restrict_scalars ℝ
  have hW0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar W x η = 0 := by
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hW i j]
      with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b)]
    rfl
  have hH2 : MContDiffAt 2 (fun x => domGram m r (Z x)) v :=
    fun a b => (hD2 a b).comp v (hZ2.restrict_scalars ℝ)
  have hK2 : MContDiffAt 2 (fun u => (W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ) v :=
    (hW2.transpose.mul hH2).mul hW2.conjTranspose.transpose
  have hKu : IsUnit ((W v)ᵀ * domGram m r (Z v) * (W v)ᴴᵀ).det := by
    simp only [det_mul, det_transpose, det_conjTranspose]
    exact (hWu.mul hDu).mul hWu.star
  refine ⟨S * W v, T ∘ₗ (fderiv ℂ Z v).toLinearMap, by rw [det_mul]; exact hS.mul hWu, fun ξ η => ?_⟩
  rw [curv_congr hG, curv_smul (f := fun _ => κ) contDiffAt_const hκ.ne' hK2 hKu, leviForm_const,
    curv_changeFrame (H := fun x => domGram m r (Z x)) hH2 hDu hW2 hWu hW0,
    curv_comp_holo hD2 hDu hZ2, hF, Matrix.mul_inv_rev]
  simp [Matrix.mul_assoc]

end GlobalTheory.PointFormSign
end

