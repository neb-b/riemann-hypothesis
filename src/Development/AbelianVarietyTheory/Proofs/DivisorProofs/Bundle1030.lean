module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealCharacter
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.RealChar

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem xB_mem_dom {B : C.Bas} (hB : C.IsB B) : C.xB B ∈ C.X.dom :=
  GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hB)

theorem Th_ne_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem Th_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem scalar_eq {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : GlobalTheory.Ker.IsWeak C.ψ S T om)
    {u : GA D T} {B B' : C.Bas} (hB : C.IsB B) (hB' : C.IsB B') {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) {c c' : ℂ} (hc' : ‖c'‖ = 1)
    (e : om (1, u) (C.Th (C.xB B) φ) = c • C.Th (C.xB (C.mvB u B)) φ)
    (e' : om (1, u) (C.Th (C.xB B') φ) = c' • C.Th (C.xB (C.mvB u B')) φ) : c = c' := by
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hmv : ∀ A, C.IsB A → C.IsB (C.mvB u A) := fun A hA =>
    (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 A hA).2.2.2.2.2 u).1
  have hth : ∀ A, C.IsB A → C.IsTh (C.Th (C.xB A) φ) := fun A hA =>
    (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (xB_mem_dom C hA) φ hφ).1.1
  have hd : dbl C.X C.bas C.idx φ φ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB) hφ hφ
    rw [hc, zero_mul] at h1
    exact Th_ne_zero C (xB_mem_dom C hB) hφ h0 ((hip μ 𝓕 hμ _ (hth B hB)).2.1 h1)
  have hk : kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
    rw [GlobalTheory.AdTh.Overlap.kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)
      (DblPoint.det_aAnti_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)))
  have h1 := ((hip μ 𝓕 hμ _ (hth B hB)).2.2.2 _ (hth B' hB')).2.2.2.2.2 om hom (1, u)
  have h2 : GlobalTheory.Ker.ipO μ 𝓕 (c • C.Th (C.xB (C.mvB u B)) φ) (c' • C.Th (C.xB (C.mvB u B')) φ) =
      c * conj c' * GlobalTheory.Ker.ipO μ 𝓕 (C.Th (C.xB (C.mvB u B)) φ) (C.Th (C.xB (C.mvB u B')) φ) := by
    rw [GlobalTheory.Ker.ipO, GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [e, e', h2, GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C (hmv B hB)) (xB_mem_dom C (hmv B' hB')) hφ hφ,
    GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB') hφ hφ,
    GlobalTheory.AdTh.Overlap.kZero_mvB C hB u] at h1
  have h3 : c * conj c' = 1 := mul_right_cancel₀ (mul_ne_zero hd hk) (h1.trans (one_mul _).symm)
  have h4 : c' * conj c' = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc']
    simp
  linear_combination c' * h3 - c * h4

end GlobalTheory.FrameEquiv.RealChar


open GlobalTheory.FrameEquiv.RealChar in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FrameEquiv.exists_real_character : ∀ (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak C.ψ S T om → ∃ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ‖χ u‖ = 1) ∧ (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') ∧ ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ → om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := by
  intro D S T C om hom
  by_cases hex : ∃ φ₀ : TF S.rank C.g, GlobalTheory.SW.IsSB φ₀ ∧ φ₀ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm, fun u _ B hB φ hφ => ?_⟩
    have h0 : φ = 0 := by
      by_contra h
      exact hex ⟨φ, hφ, h⟩
    have hmv : C.IsB (C.mvB u B) := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.2.2 u).1
    rw [h0, Th_zero C (xB_mem_dom C hB), Th_zero C (xB_mem_dom C hmv), map_zero, smul_zero]
  obtain ⟨φ₀, s₀, n₀⟩ := hex
  obtain ⟨⟨B₀, hB₀⟩, hJ⟩ := GlobalTheory.Ker.onBasis_frame_period D S T C
  have hr := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _)
  choose! χ hχ1 hχ using fun u hu => hr u hu B₀ hB₀
  have main : ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ →
      om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := fun u hu B hB φ hφ => by
    obtain ⟨c, -, hc⟩ := hr u hu B hB
    rw [← scalar_eq C hom hB hB₀ s₀ n₀ (hχ1 u hu) (hc φ₀ s₀) (hχ u hu φ₀ s₀)]
    exact hc φ hφ
  refine ⟨χ, hχ1, fun u hu u' hu' => ?_, main⟩
  have h1 := main (u * u') (mul_mem hu hu') B₀ hB₀ φ₀ s₀
  obtain ⟨hm, hmul, -⟩ := (hJ B₀ hB₀).2.2.2.2.2 u'
  have e : ((1, u * u') : GA D S × GA D T) = (1, u) * (1, u') := by simp
  rw [e, map_mul, mul_apply_eq_comp, main u' hu' B₀ hB₀ φ₀ s₀, map_smul, main u hu _ hm φ₀ s₀, hmul u,
    smul_smul] at h1
  have hne := Th_ne_zero C (xB_mem_dom C ((hJ _ hm).2.2.2.2.2 u).1) s₀ n₀
  rw [mul_comm]
  exact (smul_left_injective ℂ hne h1).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultiple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Renorm

theorem alg_renorm {M : Type} [CommGroup M] {q q₀ a p p₀ g g₀ x y : M} (h₀ : q = y * x⁻¹ * q₀)
    (h₁ : a = g₀ * (q₀ * p₀)⁻¹) (h₂ : p = x * p₀) (h₃ : g = y * g₀) : q * (a * p) = g := by
  rw [h₀, h₁, h₂, h₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section Norm
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_unit_normW (w₀ : W0 U) (hw : w₀.IsGen) (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) :
    ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, NormW U w₀ (GlobalTheory.UU.scaleGen a ρ) := by
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨JA₀, hA₀⟩ := exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := exists_good' U.LG.isLB z₀
  let eK : Spec (CommRingCat.of (FractionRing R)) ⟶ ((Over.pullback (jK R)).obj G).left :=
    eSec ((Over.pullback (jK R)).obj G)
  have h₁ : eK ≫ U.gen.hom.left = eSec A.A := EvalZero.eK_gen U
  have h₂ : eK ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := EvalZero.eK_fst
  have hsurj : ∀ u : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z₀)ˣ,
      ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, gm (𝟙 _) z₀ ⊤ a = u := by
    intro u
    obtain ⟨V, hV, s, hs⟩ := (Spec (CommRingCat.of (FractionRing R))).presheaf.exists_germ_eq u.val
    obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ =>
      (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y) ▸ hV
    have hu : IsUnit s := (Spec (CommRingCat.of (FractionRing R))).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain rfl : z₀ = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y
      exact (congrArg IsUnit hs).mpr u.isUnit
    exact ⟨hu.unit, Units.ext ((gm_val _ z₀ ⊤ trivial _).trans hs)⟩
  obtain ⟨a, ha⟩ := hsurj (val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (jK R) z₀ JG₀ *
    (pw w₀ eK z₀ (JA₀ (eSec A.A)) (JG₀ (jK R ≫ eSec G)) *
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) (Z := Spec (CommRingCat.of (FractionRing R)))
        ρ (𝟙 _) z₀ JA₀)⁻¹)
  refine ⟨a, hw, GlobalTheory.UU.scaleGen_isGen a hρ, fun z JA JG hA hG => ?_⟩
  obtain rfl : z₀ = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ z
  have mA : ∀ J, Good A.L z₀ J → U.gen.hom.left (eK z₀) ∈ A.L.U (J (eSec A.A)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ A.L.U (J (eSec A.A))) h₁).mpr (hJ _)
  have mG : ∀ J, Good U.LG.L z₀ J → pullback.fst G.hom (jK R) (eK z₀) ∈ U.LG.L.U (J (jK R ≫ eSec G)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ U.LG.L.U (J (jK R ≫ eSec G))) h₂).mpr (hJ _)
  have b₀ : gw w₀ eK z₀ (JG (jK R ≫ eSec G)) (fun _ => JA (eSec A.A)) =
      pw w₀ eK z₀ (JA (eSec A.A)) (JG (jK R ≫ eSec G)) := rfl
  have b₁ := pw_trans hw eK z₀ (mA _ hA) (mA _ hA₀) (mG _ hG) (mG _ hG₀)
  have b₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1)
    (Z := Spec (CommRingCat.of (FractionRing R))) hρ (𝟙 _) hA hA₀
  have b₃ := val_tr (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rigGen (jK R) hG hG₀
  have b₄ := GlobalTheory.UU.val_scaleGen (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) a ρ (𝟙 _) hA
  rw [h₁, h₂] at b₁
  rw [Fintype.prod_unique, zpow_one] at b₂ b₃
  rw [Category.id_comp] at b₂
  rw [b₀, b₄]
  exact alg_renorm b₁ ha b₂ b₃

end Norm

theorem alg_rig {M : Type} [CommGroup M] (g v : M) (k : ℤ) :
    g ^ (k - 1) * (v ^ k * v⁻¹) = (g * v) ^ k * (g * v)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem alg_frame {M : Type} [CommGroup M] {g t α r : M} {k : ℤ} (h : t ^ k = α * r ^ (1 : ℤ)) :
    (g * t) ^ k = g ^ (k - 1) * α * (g * r) ^ (1 : ℤ) := by
  apply Additive.ofMul.injective
  replace h := congrArg Additive.ofMul h
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at h ⊢
  linear_combination (norm := module) h

section Tors
variable {S : Scheme.{0}} {P : PolAV S}

theorem isTorsFrame_scale (rig : LB.Gen (P.L.pull (eSec P.A))) (a : Γ(S, ⊤)ˣ) {n : ℕ} {T : Over S} {x : T ⟶ P.A}
    {τ τ' : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x τ) (hτ' : τ'.IsGen)
    (ht : ∀ z J, Good P.L z J → val τ' (𝟙 _) z J = gm T.hom z ⊤ a * val τ (𝟙 _) z J) :
    IsTorsFrame P (GlobalTheory.UU.scaleGen a rig) n x τ' := by
  obtain ⟨hn, -, α, hα, hN, hc⟩ := H
  let u : Γ(P.A.left, ⊤)ˣ := pullU P.A.hom ⊤ a ^ ((n : ℤ) ^ 2 - 1)
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z),
      gm r z ⊤ u = gm (r ≫ P.A.hom) z ⊤ a ^ ((n : ℤ) ^ 2 - 1) := fun Z r z =>
    (map_zpow _ _ _).trans (congrArg (· ^ _) (gm_pull r P.A.hom z ⊤ trivial a))
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) J, Good P.L z J →
      FrameMove.rval (GlobalTheory.UU.scaleGen a rig) r z J = gm r z ⊤ a * FrameMove.rval rig r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) a rig r hJ
  have hα' : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) J, Good P.L z J →
      val (GlobalTheory.UU.scaleGen u α) r z J = gm r z ⊤ u * val α r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen u α r hJ
  have he : eSec P.A ≫ P.A.hom = 𝟙 S := Over.w η[P.A]
  refine ⟨hn, hτ', GlobalTheory.UU.scaleGen u α, GlobalTheory.UU.scaleGen_isGen u hα, corr_of_val P.isLB fun y J hJ => ?_,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  · have e0 : val α (𝟙 _ ≫ eSec P.A) y J =
        FrameMove.rval rig (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (FrameMove.rval rig (𝟙 _) y J)⁻¹ :=
      (val_pull hJ α (eSec P.A) (𝟙 _)).symm.trans ((val_corr hJ hN (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))
    have e1 : val (rigPow P.A P.L (GlobalTheory.UU.scaleGen a rig) ((n : ℤ) ^ 2)) (𝟙 _) y J =
        FrameMove.rval (GlobalTheory.UU.scaleGen a rig) (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_pull hJ, hα' _ _ _ _ hJ, hu, e0, val_mul hJ, e1, val_inv, hr _ _ _ _ hJ, Category.assoc, he,
      Category.id_comp]
    rw [show val (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) (GlobalTheory.UU.scaleGen a rig) (𝟙 (𝟙_ (Over S)).left) y J = _ from hr _ _ _ _ hJ]
    exact alg_rig (M := (S.presheaf.stalk y)ˣ) _ _ _
  · have a1 : val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α (𝟙 _ ≫ x.left) y J * FrameMove.rval rig (𝟙 _ ≫ T.hom) y J ^ (1 : ℤ) :=
      (map_zpow _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (FrameMove.val_rigT _ _ _ hJ))))
    rw [FrameMove.val_powFrame, val_mul hJ, val_pull hJ, FrameMove.val_rigT _ _ _ hJ, hα' _ _ _ _ hJ, hu,
      hr _ _ _ _ hJ, ht y J hJ, Category.assoc, Over.w x]
    simp only [Category.id_comp] at a1 ⊢
    exact alg_frame a1

end Tors

theorem cst_gm {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ) (z : (TFK (R := R) F).left) :
    (gm (jFK (R := R) F) z ⊤ a).val = cst (R := R) F z (algebraMap (FractionRing R) F
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val)) := by
  rw [← gs_unit _ z ⊤ trivial]
  have e : a.val = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val) := by simp
  conv_lhs => rw [e]
  exact FrameMove.gs_spMap (algebraMap (FractionRing R) F) z _

theorem exists_renorm : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ (ρ' : LB.Gen (A.L.pull (eSec A.A))) (c : FractionRing R), c ≠ 0 ∧ NormW U w₀ ρ' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (x : TFK (R := R) F ⟶ A.A) (fr fr' : FrAt x), IsTorsFrame A ρ N x fr → fr'.IsGen → (∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (algebraMap (FractionRing R) F c)) * (val fr (𝟙 _) z J).val) → IsTorsFrame A ρ' N x fr' := by
  intro R _ _ I D A G _ _ U w₀ hw ρ hρ
  obtain ⟨a, ha⟩ := exists_unit_normW U w₀ hw ρ hρ
  refine ⟨GlobalTheory.UU.scaleGen a ρ, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val, ?_, ha,
    fun F _ _ N x fr fr' H hfr' hv => ?_⟩
  · exact (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  · refine isTorsFrame_scale ρ a H hfr' fun z J hJ => Units.ext ?_
    rw [Units.val_mul, hv z J hJ]
    exact congrArg (· * _) (cst_gm F a z).symm

end GlobalTheory.Poinc.Renorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimes
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkewScale

variable {E : Type} [Field E] [NumberField E]

theorem exists_intValuation_eq {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 E))
    (hw : Function.Injective w) (k : ι → ℕ) :
    ∃ a : 𝓞 E, ∀ i, (w i).intValuation a = WithZero.exp (-(k i : ℤ)) := by
  classical
  choose π hπ using fun i => (w i).intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := (Finset.univ : Finset ι))
    (fun i => (w i).asIdeal) (fun i => k i + 1) (fun i _ => (w i).prime)
    (fun i _ j _ hij e => hij (hw (HeightOneSpectrum.ext e))) (fun i => π i.1 ^ k i.1)
  refine ⟨a, fun i => ?_⟩
  have h1 : (w i).intValuation (π i ^ k i) = WithZero.exp (-(k i : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have h2 := ((w i).intValuation_le_pow_iff_mem _ _).2 (ha i (Finset.mem_univ i))
  rw [← h1]
  apply Valuation.map_eq_of_sub_lt
  rw [h1]
  refine lt_of_le_of_lt h2 ?_
  rw [WithZero.exp_lt_exp]
  push_cast
  omega

theorem exists_valuation_eq {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 E))
    (hw : Function.Injective w) (t : ι → WithZero (Multiplicative ℤ)) (ht : ∀ i, t i ≠ 0) :
    ∃ c : E, c ≠ 0 ∧ ∀ i, (w i).valuation E c = t i := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_ne_zero, fun i => isEmptyElim i⟩
  obtain ⟨a, ha⟩ := exists_intValuation_eq w hw (fun i => (-(t i).log).toNat)
  obtain ⟨b, hb⟩ := exists_intValuation_eq w hw (fun i => ((t i).log).toNat)
  have hne : ∀ r : 𝓞 E, (w i₀).intValuation r ≠ 0 → algebraMap (𝓞 E) E r ≠ 0 := fun r hr e => by
    apply hr
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 e, map_zero]
  have ha0 := hne a (by rw [ha]; exact WithZero.exp_ne_zero)
  have hb0 := hne b (by rw [hb]; exact WithZero.exp_ne_zero)
  refine ⟨algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b, div_ne_zero ha0 hb0, fun i => ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, ha, hb,
    ← WithZero.exp_sub]
  conv_rhs => rw [← WithZero.exp_log (ht i)]
  congr 1
  omega

end GlobalTheory.PlaneSkewScale

namespace GlobalTheory.PlaneSkewScale

variable {E : Type} [Field E] [NumberField E]

theorem exists_smul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (x : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ L := by
  exact GlobalTheory.NonzeroSmulMembership.exists_ne_zero_smul_mem L hL x

theorem exists_max {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) {x : Fin n → E} (hx : x ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ s₀ : E, s₀ ≠ 0 ∧ s₀ • x ∈ L ∧ ∀ s : E, s • x ∈ L → w.valuation E s ≤ w.valuation E s₀ := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  obtain ⟨G, hG⟩ := hL.fg
  set B := G.sup fun g => w.valuation E (g j)
  have hB : ∀ z ∈ L, w.valuation E (z j) ≤ B := by
    intro z hz
    rw [← hG] at hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact Finset.le_sup (f := fun g => w.valuation E (g j)) hz
    | zero => simp
    | add z₁ z₂ _ _ h₁ h₂ => rw [Pi.add_apply]; exact Valuation.map_add_le _ h₁ h₂
    | smul a z _ h =>
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      exact mul_le_of_le_one_left' (w.valuation_le_one a) |>.trans h
  have hxj : w.valuation E (x j) ≠ 0 := (map_ne_zero _).2 (by simpa using hj)
  have hbound : ∀ s : E, s • x ∈ L → w.valuation E s ≤ B * (w.valuation E (x j))⁻¹ := fun s hs => by
    have := hB _ hs
    rw [Pi.smul_apply, smul_eq_mul, map_mul] at this
    exact (le_mul_inv_iff₀ (zero_lt_iff.2 hxj)).2 this
  obtain ⟨K, hK⟩ : ∃ K : ℤ, B * (w.valuation E (x j))⁻¹ ≤ WithZero.exp K := by
    by_cases h0 : B * (w.valuation E (x j))⁻¹ = 0
    · exact ⟨0, by rw [h0]; exact zero_le'⟩
    · exact ⟨_, (WithZero.exp_log h0).ge⟩
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem L hL x
  have hd' : algebraMap (𝓞 E) E d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hd
  let S : ℤ → Prop := fun k => ∃ s : E, s ≠ 0 ∧ s • x ∈ L ∧ w.valuation E s = WithZero.exp k
  obtain ⟨k₀, ⟨s₀, hs₀, hs₀L, hs₀v⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := S)
    ⟨K, fun k ⟨s, _, hs, hv⟩ => by
      have := (hbound s hs).trans hK
      rwa [hv, WithZero.exp_le_exp] at this⟩
    ⟨_, algebraMap (𝓞 E) E d, hd', by rwa [algebraMap_smul],
      (WithZero.exp_log ((map_ne_zero _).2 hd')).symm⟩
  refine ⟨s₀, hs₀, hs₀L, fun s hs => ?_⟩
  by_cases h0 : s = 0
  · rw [h0, map_zero]; exact zero_le'
  · have hv := (WithZero.exp_log ((map_ne_zero (w.valuation E)).2 h0)).symm
    rw [hv, hs₀v, WithZero.exp_le_exp]
    exact hmax _ ⟨s, h0, hs, hv⟩

theorem primAt_smul {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    {c s₀ : E} (hc : c ≠ 0) (hs₀ : s₀ • x ∈ L) (hmax : ∀ s : E, s • x ∈ L → w.valuation E s ≤ w.valuation E s₀)
    (he : w.valuation E c = w.valuation E s₀) : PrimAt w L (c • x) := by
  have hc' : w.valuation E c ≠ 0 := (map_ne_zero _).2 hc
  refine ⟨fun s hs => ?_, s₀ * c⁻¹, ?_, ?_⟩
  · rw [smul_smul] at hs
    have h1 := hmax _ hs
    rw [map_mul, ← he] at h1
    have h2 : w.valuation E s * w.valuation E c ≤ 1 * w.valuation E c := by rwa [one_mul]
    have h3 : w.valuation E s ≤ 1 * w.valuation E c * (w.valuation E c)⁻¹ := (le_mul_inv_iff₀ (zero_lt_iff.2 hc')).2 h2
    rwa [one_mul, mul_inv_cancel₀ hc'] at h3
  · rwa [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · rw [map_mul, map_inv₀, ← he, mul_inv_cancel₀ hc']

end GlobalTheory.PlaneSkewScale

namespace GlobalTheory.PlaneSkewScale

theorem exists_rescale_primAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 →
    ∀ (P : Finset (HeightOneSpectrum (𝓞 F))) (τ : ∀ v : P, E →ₐ[F] Fv F v.1), ∃ c : E, c ≠ 0 ∧
      ∀ v : P, PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L (c • x) ∧ PrimAt (GlobalTheory.AdelicU.splitPrime (τ v)) L ((σ c)⁻¹ • y) := by
  intro F E _ _ _ _ _ σ hσ n L hL x y hx hy P τ
  classical
  choose sx hsx0 hsxL hsxmax using fun v : P => exists_max L hL hx (GlobalTheory.AdelicU.splitPrime (τ v))
  choose sy hsy0 hsyL hsymax using fun v : P => exists_max L hL hy (GlobalTheory.AdelicU.splitPrime (τ v))
  let w : P ⊕ P → HeightOneSpectrum (𝓞 E) :=
    Sum.elim (fun v => GlobalTheory.AdelicU.splitPrime (τ v)) (fun v => GlobalTheory.AdelicU.splitPrime ((τ v).comp σ))
  have hunder : ∀ i, (w i).under (𝓞 F) = (Sum.elim (fun v : P => v.1) (fun v : P => v.1) i) := by
    rintro (v | v) <;> exact GlobalTheory.AdelicU.splitPrime_under _
  have hw : Function.Injective w := by
    intro i j e
    have hv := (hunder i).symm.trans ((congrArg (fun u => u.under (𝓞 F)) e).trans (hunder j))
    rcases i with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases j with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hv <;> subst hv
    · rfl
    · exact absurd e.symm (GlobalTheory.AdelicU.splitPrime_comp_ne hσ _)
    · exact absurd e (GlobalTheory.AdelicU.splitPrime_comp_ne hσ _)
    · rfl
  let t : P ⊕ P → WithZero (Multiplicative ℤ) :=
    Sum.elim (fun v => (GlobalTheory.AdelicU.splitPrime (τ v)).valuation E (sx v))
      (fun v => ((GlobalTheory.AdelicU.splitPrime (τ v)).valuation E (sy v))⁻¹)
  obtain ⟨c, hc0, hc⟩ := exists_valuation_eq w hw t (by
    rintro (v | v)
    · exact (map_ne_zero _).2 (hsx0 v)
    · exact inv_ne_zero ((map_ne_zero _).2 (hsy0 v)))
  refine ⟨c, hc0, fun v => ⟨primAt_smul hc0 (hsxL v) (hsxmax v) (hc (Sum.inl v)),
    primAt_smul (inv_ne_zero ((map_ne_zero σ).2 hc0)) (hsyL v) (hsymax v) ?_⟩⟩
  have h1 := hc (Sum.inr v)
  simp only [w, t, Sum.elim_inr] at h1
  rw [← GlobalTheory.AdelicU.valued_apply_eq_valuation, AlgHom.comp_apply, GlobalTheory.AdelicU.valued_apply_eq_valuation] at h1
  rw [map_inv₀, h1, inv_inv]

end GlobalTheory.PlaneSkewScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnit
section
open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpFrame

theorem Frame.prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  intro l _ ι N F hF hu
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  obtain ⟨L, -, hL⟩ := hF.ring.2
  have hmem : F.emb u ∈ Set.range F.emb := ⟨u, rfl⟩
  rw [hL] at hmem
  have h1 : F.emb u * (l : PadicAlgCl l) = 1 := by
    have := congrArg F.emb hu
    rwa [map_mul, map_natCast, map_one] at this
  have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.norm_p]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one, hl] at h2
  have hlgt : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  have h3 : ‖F.emb u‖ * (l : ℝ)⁻¹ < 1 := by
    calc ‖F.emb u‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ := by gcongr; exact hmem.2
      _ = (l : ℝ)⁻¹ := one_mul _
      _ < 1 := inv_lt_one_of_one_lt₀ hlgt
  linarith

end GlobalTheory.ExpFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
section
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_mono_neg_add :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (∀ r r', r ≤ r' → B r ⊆ B r') ∧ (∀ r x, x ∈ B r → -x ∈ B r) ∧
        (∀ r r' x y, x ∈ B r → y ∈ B r' → x + y ∈ B (r + r')) := by
  intro G _ Λ B hB
  have hneg : ∀ r x, x ∈ B r → -x ∈ B r := by
    intro r x hx
    have h := hB.sub_mem 0 r 0 x (hB.zero_mem 0 le_rfl) hx
    simpa using h
  refine ⟨?_, hneg, ?_⟩
  · intro r r' hrr' x hx
    have h := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.mpr hrr'))
    simpa using h
  · intro r r' x y hx hy
    have h := hB.sub_mem r r' x (-y) hx (hneg r' y hy)
    simpa using h

end GlobalTheory.VolBr
end

