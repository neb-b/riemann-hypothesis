module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (n : ℕ), 0 < n → IsUnit (n : Γ(S, ⊤)) →
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (t : Sp R ⟶ S)
    (K : Type) [Field K] (φ : R →+* K),
    (∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g =
        (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ h → g = h) ∧
    ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 → ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g = x := by
  have exists_iso_sp_of_finite_etale : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsFinite f → Etale f →
      ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Algebra.Etale R B ∧ Module.Finite R B ∧
        ∃ e : X ≅ Sp B, e.hom ≫ spMap (algebraMap R B) = f := by
    intro R _ X f hf hfe
    have : IsAffine X := isAffine_of_isAffineHom f
    let ρ : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
    let _ : Algebra R Γ(X, ⊤) := ρ.toAlgebra
    have key : X.isoSpec.hom ≫ spMap (algebraMap R Γ(X, ⊤)) = f := by
      have h := Scheme.isoSpec_hom_naturality f
      rw [Scheme.isoSpec_Spec_hom] at h
      show X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ) = f
      rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop from rfl,
        Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
        Spec.map_id, Category.comp_id]
    have hsp : spMap (algebraMap R Γ(X, ⊤)) = X.isoSpec.inv ≫ f := by
      rw [← key, Iso.inv_hom_id_assoc]
    have het : Etale (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
    have hfi : IsFinite (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
    refine ⟨Γ(X, ⊤), inferInstance, inferInstance, ?_, ?_, X.isoSpec, key⟩
    · exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 het
    · exact (IsFinite.SpecMap_iff _).1 hfi

  have preconnectedSpace_sp : ∀ (R : Type) [CommRing R] [IsLocalRing R], PreconnectedSpace (Sp R) := by
    intro R _ _
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    have key : ∀ z : Sp R, z ⤳ (IsLocalRing.closedPoint R : PrimeSpectrum R) := fun z =>
      IsLocalRing.specializes_closedPoint (R := R) z
    by_cases h : (IsLocalRing.closedPoint R : PrimeSpectrum R) ∈ s
    · right
      ext z
      simp only [Set.mem_univ, iff_true]
      exact (key z).mem_open hs.isOpen h
    · left
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hz => h ((key z).mem_closed hs.isClosed hz)

  intro S A _ _ hA n _ hn R _ _ _ t K _ φ
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  let ψK : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let E := GlobalTheory.TorsionUnram.torsionEquiv A n
  refine ⟨fun g h hg hh hgh => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := (E _).surjective ⟨g, hg⟩
    obtain ⟨b, hb⟩ := (E _).surjective ⟨h, hh⟩
    have ga : a ≫ torsion.ι A n = g := congrArg Subtype.val ha
    have gb : b ≫ torsion.ι A n = h := congrArg Subtype.val hb
    have hab : ψK ≫ a = ψK ≫ b := by
      apply (E _).injective
      apply Subtype.ext
      show (ψK ≫ a) ≫ torsion.ι A n = (ψK ≫ b) ≫ torsion.ι A n
      rw [Category.assoc, Category.assoc, ga, gb]
      exact hgh
    have hab' : spMap φ ≫ a.left = spMap φ ≫ b.left := congrArg (fun u => u.left) hab
    have : PreconnectedSpace (Over.mk t).left := preconnectedSpace_sp R
    have : a = b := GlobalTheory.over_eq_of_preconnected_of_unramified (spMap φ) hab'
    rw [← ga, ← gb, this]
  · obtain ⟨y, hy⟩ := (E _).surjective ⟨x, hx⟩
    have yx : y ≫ torsion.ι A n = x := congrArg Subtype.val hy
    obtain ⟨B, _, _, _, _, e, he⟩ :=
      exists_iso_sp_of_finite_etale R _ (pullback.snd (torsion A n).hom t) inferInstance inferInstance
    let q : Sp K ⟶ Sp B := pullback.lift y.left (spMap φ) (Over.w y) ≫ e.hom
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective q
    have hq : q ≫ spMap (algebraMap R B) = spMap φ := by
      simp only [q, Category.assoc, he, pullback.lift_snd]
    have hχ : χ'.hom.comp (algebraMap R B) = φ := by
      have h0 : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ χ') =
          Spec.map (CommRingCat.ofHom φ) := by
        rw [Spec.map_comp, hχ']
        exact hq
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
    obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.TorsLift.exists_section_of_point R B K φ χ'.hom hχ
    let s : Sp R ⟶ (torsion A n).left := spMap ψ ≫ e.inv ≫ pullback.fst _ _
    have h1 : e.inv ≫ pullback.snd (torsion A n).hom t = spMap (algebraMap R B) := by
      rw [← he, Iso.inv_hom_id_assoc]
    have hs : s ≫ (torsion A n).hom = t := by
      simp only [s, Category.assoc, pullback.condition]
      rw [reassoc_of% h1, ← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp', hψ1]
      show Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫ t = t
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    let gs : Over.mk t ⟶ torsion A n := Over.homMk s hs
    refine ⟨gs ≫ torsion.ι A n, ((E _) gs).2, ?_⟩
    have h2 : spMap φ ≫ spMap ψ = q := by
      rw [← GlobalTheory.TorsionUnram.spMap_comp', hψ2, ← hχ']
      rfl
    have hy' : ψK ≫ gs = y := by
      apply Over.OverMorphism.ext
      show spMap φ ≫ s = y.left
      simp only [s, ← Category.assoc]
      rw [h2]
      simp only [q, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
    rw [← Category.assoc, hy', yx]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem evI_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

theorem mem_latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → F)
    (hy : ∀ i, IsIntegral ℤ (y i)) : (fun i => mixedEmbedding F (y i)) ∈ latPi F κ := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro ji
  rw [Pi.basis_repr]
  have h1 : mixedEmbedding F (y ji.1) ∈ mixedEmbedding.integerLattice F := by
    exact ⟨⟨y ji.1, hy ji.1⟩, rfl⟩
  have h2 := (mem_span_latticeBasis F).mpr h1
  exact (Module.Basis.mem_span_iff_repr_mem ℤ _ _).mp h2 ji.2

theorem summable_inv_one_add_pow (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Summable fun z : latPi F κ =>
      ((1 + ‖(z : κ → mixedSpace F)‖) ^ (Module.finrank ℤ (latPi F κ) + 1))⁻¹ := by
  set N : ℕ := Module.finrank ℤ (latPi F κ) + 1 with hN
  have h0 := ZLattice.summable_norm_rpow (latPi F κ) (-(N : ℝ)) (by rw [hN]; push_cast; linarith)
  have h1 : Summable fun z : latPi F κ => (if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro z hz
    have : z ≠ 0 := by simpa using hz
    simp [this]
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add h1)
  have hr : 0 ≤ ‖z‖ ^ (-(N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, if_false, add_zero]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    have : ‖z‖ = ‖(z : κ → mixedSpace F)‖ := rfl
    rw [← this]
    gcongr
    linarith

end GlobalTheory.LatScaleSum

namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  intro F _ _ κ _
  set L := latPi F κ with hL
  set N₀ : ℕ := Module.finrank ℤ L + 1 with hN
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ N₀)⁻¹ with hH
  have hHs : Summable fun z : L => H z := summable_inv_one_add_pow F κ
  refine ⟨N₀, N₀, ∑' z : L, H z, ?_⟩
  intro A m Ψ hm hb hint
  set f : (κ → F) → ℂ := fun ξ => Ψ (fun i => algebraMap F (AF F) (ξ i)) with hf
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  have hψ : ∀ ξ : κ → F, (fun i => evI F (algebraMap F (AF F) (ξ i))) = ψ ξ :=
    fun ξ => funext fun i => evI_algebraMap F (ξ i)
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have hA : 0 ≤ A := le_trans (by positivity) (hb 0)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have key : ∀ ξ, ‖f ξ‖ ≤ A * (m : ℝ) ^ N₀ * Lind (g ξ) := by
    intro ξ
    by_cases h : f ξ = 0
    · rw [h, norm_zero]
      have := hLnn (g ξ)
      positivity
    · have hi := hint ξ h
      have hmem : g ξ ∈ L := mem_latPi F κ _ hi
      rw [hLind, Set.indicator_of_mem hmem]
      have hb' := hb ξ
      rw [hψ ξ] at hb'
      have hpos : 0 < (1 + ‖ψ ξ‖) ^ N₀ := by positivity
      have e1 : ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb'
      have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
      have hmpos : (0 : ℝ) < m := by linarith
      have e2 : ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ ≤ (m : ℝ) ^ N₀ * H (g ξ) := by
        simp only [hH]
        calc ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ = (m : ℝ) ^ N₀ * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ N₀)⁻¹ := by
              rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
          _ ≤ (m : ℝ) ^ N₀ * ((1 + ‖g ξ‖) ^ N₀)⁻¹ := by
              gcongr
              nlinarith [norm_nonneg (ψ ξ)]
      calc ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := e1
        _ ≤ A * ((m : ℝ) ^ N₀ * H (g ξ)) := mul_le_mul_of_nonneg_left e2 hA
        _ = _ := by ring
  have hu : Summable fun ξ => A * (m : ℝ) ^ N₀ * Lind (g ξ) :=
    (hLs.comp_injective hginj).mul_left _
  have hfs : Summable fun ξ => ‖f ξ‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hu
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  have hmk : 0 ≤ A * (m : ℝ) ^ N₀ := by positivity
  calc ‖thetaSum F Ψ‖ = ‖∑' ξ, f ξ‖ := rfl
    _ ≤ ∑' ξ, ‖f ξ‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' ξ, A * (m : ℝ) ^ N₀ * Lind (g ξ) := hfs.tsum_le_tsum key hu
    _ = A * (m : ℝ) ^ N₀ * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ A * (m : ℝ) ^ N₀ * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp hmk
    _ = (∑' z : L, H z) * A * (m : ℝ) ^ N₀ := by ring

end GlobalTheory.LatScaleSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCharacterDetPower
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem mu_real_eq_prod_det : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) (e : D.what₂.Tau → ℤ), IsInfFam θ → MuVal V χ mu → (∀ ρ, HasInfExp D χ ρ (-(e ρ : ℚ))) → ∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ)) := by
  intro D θ V χ mu e hθ hmu he u hu
  obtain ⟨x, hx, h⟩ := GlobalTheory.VacuumCharacter.exists_root hθ V
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ).ne_zero) u hu
  rw [hmu.2 u x hx, h χ (fun ρ => -(e ρ)) (fun ρ => by push_cast; exact he ρ)]
  rfl

end GlobalTheory.HolRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIwasawaMajorantFrameStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_iwasawa_majorant_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (a : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → ∀ (w : InfinitePlace F) (g : GArch σ J w), ∃ q k : GArch σ J w, k ∈ stabArch σ J w (bc (compInf F E w) a) ∧ g = q * k ∧ ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1 := by
  first | exact @GlobalTheory.IwArchLine.exists_q_k | exact GlobalTheory.IwArchLine.exists_q_k | (intros; apply GlobalTheory.IwArchLine.exists_q_k <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineD
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeisTransport

theorem actsD_heisLine_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi u hu f f₁ hf
  have hS := IsUWeilPair.isUSplitting hWeil
  set ψ := B.ψ with hψ
  set p : UA σ X.J × UA σ W.J := (g, h) with hp

  have hrest : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      Rest (evI F) (⇑φ) (fun x => g' (fun i => (x i).2)) := by
    intro φ g' hg'
    refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
    change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have hpure : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      om p (pureA F φ g') = pureA F (T φ) g' := fun φ g' hg' => hT φ _ (hrest φ g' hg')

  have h0 : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ t : ℝ, M.heisLine ψ v t 0 = 0 := by
    intro v t
    funext x
    simp [Model.heisLine, Darboux.rho, schr]

  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hB.std
  have hSDD := (hD u hu f).1
  have hL := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ (D u f)
  have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (D u f) f₁).1 _ (h0 u) hSDD
  have hf₁ : f₁ = D u f := hL.2.2.1 _ hf hAD
  rw [← hf₁] at hSDD

  have himpl : ∀ t : ℝ, ∀ Φ ∈ schA F (Fin n × Fin d),
      M.heisLine ψ (mat g * u * (mat h).transpose) t (om p Φ) = om p (M.heisLine ψ u t Φ) := by
    intro t Φ hΦ
    have e := hS.impl p (realAd F t • u) Φ hΦ
    simp only [Model.heisLine]
    rw [e]
    congr 2
    simp only [actAB, hp, mat, Matrix.mul_smul, Matrix.smul_mul]

  have hSD : GlobalTheory.RealLift.SD (M.heisLine ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
    intro g' hg' l hl
    have hΦ : pureA F (⇑f) g' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g', hg', rfl⟩
    have e : (fun t => l (M.heisLine ψ (mat g * u * (mat h).transpose) t (pureA F (⇑(T f)) g'))) =
        fun t => (l ∘ₗ om p) (M.heisLine ψ u t (pureA F (⇑f) g')) := by
      funext t
      rw [← hpure f g' hg', himpl t _ hΦ]
      rfl
    rw [e, ← hpure f₁ g' hg']
    exact hSDD g' hg' (l ∘ₗ om p) (hS.adm p l hl)
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T f) (T f₁) (T f₁)).1 _ (h0 _) hSD

end GlobalTheory.HeisTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblSiegelX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def zs {n n₁ d : ℕ} (H : Plane E n n₁) (u : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Matrix.vecMulVec (incV F H.y) ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ u)

variable {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {d : ℕ}

theorem rho_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (Φ Ψ : (κ → AF F) → ℂ) :
    dd.rho ψ w (Φ + Ψ) = dd.rho ψ w Φ + dd.rho ψ w Ψ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    dd.rho ψ w (c • Φ) = c • dd.rho ψ w Φ := by
  funext x; simp [Darboux.rho, schr]; ring

def avgFun (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (Φ : (κ → AF F) → ℂ) : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ :=
  fun u => lam (dd.rho ψ (z u) Φ)

theorem avgFun_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (Φ Ψ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (Φ + Ψ) = avgFun dd ψ z lam Φ + avgFun dd ψ z lam Ψ := by
  funext u; simp [avgFun, rho_add]

theorem avgFun_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (c • Φ) = c • avgFun dd ψ z lam Φ := by
  funext u; simp [avgFun, rho_smul]

def avgSub (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Integrable (avgFun dd ψ z lam Φ) μ}
  zero_mem' := by
    show Integrable (avgFun dd ψ z lam 0) μ
    have : avgFun dd ψ z lam 0 = 0 := by
      have h := avgFun_smul dd ψ z lam 0 0
      simpa using h
    rw [this]; exact integrable_zero _ _ _
  add_mem' := fun {Φ Ψ} hΦ hΨ => by
    show Integrable (avgFun dd ψ z lam (Φ + Ψ)) μ
    rw [avgFun_add]; exact hΦ.add hΨ
  smul_mem' := fun c Φ hΦ => by
    show Integrable (avgFun dd ψ z lam (c • Φ)) μ
    rw [avgFun_smul]; exact hΦ.smul c

def averagedIntegralIntegrable (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) : avgSub dd ψ z lam μ →ₗ[ℂ] ℂ where
  toFun Φ := ∫ u, avgFun dd ψ z lam Φ.1 u ∂μ
  map_add' Φ Ψ := by
    simp only [Submodule.coe_add, avgFun_add, Pi.add_apply]
    exact integral_add Φ.2 Ψ.2
  map_smul' c Φ := by
    simp only [Submodule.coe_smul, avgFun_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

def avgL (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose

theorem avgL_apply (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) (Φ : (κ → AF F) → ℂ)
    (h : Integrable (avgFun dd ψ z lam Φ) μ) : avgL dd ψ z lam μ Φ = ∫ u, avgFun dd ψ z lam Φ u ∂μ := by
  have := congrArg (fun f => f ⟨Φ, h⟩) (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose_spec
  exact this

end GlobalTheory.DblSiegelX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKTorus.IntegralOfAdic

theorem evFin_realAd (F : Type) [Field F] [NumberField F] (v : Pl F) (x : ℝ) :
    evFin F v (realAd F x) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

end GlobalTheory.ThKTorus.IntegralOfAdic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockSymbolMatrixNeZeroStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_blockSymbolMatrix_ne_zero' : ∀ (E : Type) [Field E] (J : Type) [Fintype J] [DecidableEq J] (δ e : ℕ) (g : Fin δ → E) (R : Matrix (Fin δ) (Fin δ) E), (∀ p, g p ≠ 0) → R.det ≠ 0 → (Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0).det ≠ 0 := by
  first | exact @GlobalTheory.det_blockSymbolMatrix_ne_zero | exact GlobalTheory.det_blockSymbolMatrix_ne_zero | (intros; apply GlobalTheory.det_blockSymbolMatrix_ne_zero <;> assumption)
end

