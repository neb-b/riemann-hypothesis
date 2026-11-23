module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SemiAbExtDomain

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem existsUnique_hom_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f :=
  GlobalTheory.semiAbelianHomExtension_holds.fractionField R K G H hG hH f

theorem existsUnique_iso_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback (spMap (algebraMap R K))).map E.hom = e.hom :=
  GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso (GlobalTheory.IsNormalScheme.pred _)
    (.fractionField R K) hG hH e

end GlobalTheory.SemiAbExtDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

theorem exists_unit_of_cocycle_rightAction_charZero :
    ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] [Finite Γ] (σ : Γ → K →+* K),
    (∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)) → ∀ (c : Γ → Kˣ),
    (∀ γ δ, (c (γ * δ) : K) = σ δ (c γ) * c δ) → (∀ γ, (∀ a, σ γ a = a) → c γ = 1) →
    ∃ f : Kˣ, ∀ γ, σ γ f = c γ * f := by
  intro K _ _ Γ _ _ σ hσ c hc htriv
  classical
  haveI := Fintype.ofFinite Γ
  have h1 : ∀ a, σ 1 a = a := by
    intro a
    have e := hσ 1 1 a
    rw [mul_one] at e
    exact (σ 1).injective e.symm
  have key : ∀ γ δ, (σ δ (c γ : K))⁻¹ = (c δ : K) * ((c (γ * δ) : K))⁻¹ := by
    intro γ δ
    rw [hc γ δ, mul_inv, mul_left_comm, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  let F : K → K := fun b => ∑ γ, ((c γ : K))⁻¹ * σ γ b
  have hF : ∀ b δ, σ δ (F b) = c δ * F b := by
    intro b δ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, map_mul, map_inv₀, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight δ)
    intro γ
    simp only [Equiv.coe_mulRight]
    rw [key γ δ, hσ]
    ring
  have hex : ∃ b, F b ≠ 0 := by
    by_contra hno
    push_neg at hno
    let φ : Γ → (K →* K) := fun γ => (σ γ : K →* K)
    let s : Finset (K →* K) := Finset.univ.image φ
    let g : (K →* K) → K := fun ψ => ∑ γ ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c γ : K))⁻¹
    have hli := linearIndependent_monoidHom K K
    have hsum : ∑ ψ ∈ s, g ψ • (ψ : K → K) = 0 := by
      funext b
      rw [Finset.sum_apply, Pi.zero_apply, ← hno b]
      simp only [Pi.smul_apply, smul_eq_mul, g, Finset.sum_mul]
      have hterm : ∀ ψ ∈ s, ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * ψ b
          = ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * σ i b := fun ψ _ =>
        Finset.sum_congr rfl fun γ hγ => by rw [← (Finset.mem_filter.mp hγ).2]; rfl
      rw [Finset.sum_congr rfl hterm, Finset.sum_fiberwise_of_maps_to
        (fun γ _ => Finset.mem_image_of_mem φ (Finset.mem_univ γ))]
    have hz := linearIndependent_iff'.mp hli s g hsum (φ 1)
      (Finset.mem_image_of_mem φ (Finset.mem_univ 1))
    have hterm : ∀ γ ∈ Finset.univ.filter (fun γ => φ γ = φ 1), ((c γ : K))⁻¹ = 1 := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      have hid : ∀ a, σ γ a = a := fun a => (DFunLike.congr_fun hγ.2 a).trans (h1 a)
      rw [htriv γ hid]
      simp
    have hcard : g (φ 1) = ((Finset.univ.filter (fun γ => φ γ = φ 1)).card : K) := by
      simp only [g]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard, Nat.cast_eq_zero, Finset.card_eq_zero] at hz
    have hmem : (1 : Γ) ∈ Finset.univ.filter (fun γ => φ γ = φ 1) := by simp
    rw [hz] at hmem
    simp at hmem
  obtain ⟨b, hb⟩ := hex
  refine ⟨Units.mk0 (F b) hb, fun γ => ?_⟩
  simp only [Units.val_mk0]
  exact hF b γ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine
open GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.Reg

namespace GlobalTheory.KeyFourth

theorem prod_zpow_four_smul_keyEx {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    (∏ i, t i ^ ((4 : ℤ) • keyEx Dw) i) = kch t ^ 4 := by
  rw [kch, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  norm_cast


set_option maxHeartbeats 1000000 in
theorem exists_unit_secZ_keyRule : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), 1 ≤ Dw.p + Dw.q → ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro κ h₁ h₂ h₃ E _ _ _ H Dw l Xo c g e hpq
    obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
    have hex : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
        ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
          ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
      have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
        charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
      choose Ψ hΨ using fun Z : Comp Xo c => _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
      refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
      haveI := C.sm
      haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
      haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
      haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
      obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e C.R C.y hpq
      obtain ⟨Φ', hΦ'⟩ := _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e (Om C.Z) C.yg hpq
      obtain ⟨u, hu⟩ := h₃ C.R Φ.key
      refine ⟨Φ, u, hΦ, hu, ?_⟩
      rw [← _root_.GlobalTheory.KeyFourth.rule_frBor κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
      exact (hu (Om C.Z) _ _ (_root_.GlobalTheory.KeyFourth.tied_keyPB E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm
    obtain ⟨v, hv⟩ := hex
    obtain ⟨f, hf, hfb⟩ := _root_.GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h ((4 : ℤ) • keyEx Dw) (fun Z => (v Z : Om Z)) fun C => by
      obtain ⟨-, u, -, -, huv⟩ := hv C
      rw [prod_zpow_four_smul_keyEx, ← Units.val_mul, ← huv]
      exact (u : C.R).2
    obtain ⟨f', hf', hfb'⟩ := _root_.GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (-((4 : ℤ) • keyEx Dw))
        (fun Z => (((v Z)⁻¹ : (Om Z)ˣ) : Om Z)) fun C => by
      obtain ⟨-, u, -, -, huv⟩ := hv C
      have hm : Units.map (C.R.val : C.R →* Om C.Z) u = kch C.t ^ 4 * v C.Z := Units.ext huv
      have hp : (∏ i, C.t i ^ (-((4 : ℤ) • keyEx Dw)) i) = (kch C.t ^ 4)⁻¹ := by
        rw [← prod_zpow_four_smul_keyEx, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.neg_apply, zpow_neg]
      have hq : (kch C.t ^ 4)⁻¹ * (v C.Z)⁻¹ = Units.map (C.R.val : C.R →* Om C.Z) u⁻¹ := by
        rw [map_inv, hm, mul_inv_rev, mul_comm]
      rw [hp, ← Units.val_mul, hq]
      exact ((u⁻¹ : (C.R)ˣ) : C.R).2
    have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
      rw [← GlobalTheory.AllWt.secZ_nat]
      congr 1
      funext i
      cases i <;> rfl
    have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
    rw [add_neg_cancel, h0] at hm
    have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
    rw [h0] at h1
    have hff : f * f' = 1 := by
      refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
      have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
      have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
      have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
        (f * f') 1
      refine e₃.trans ?_
      change evC h Z (f * f') - evC h Z 1 = 0
      rw [e₁, e₂, hfb, hfb', Units.mul_inv, sub_self]
    refine ⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf, ?_⟩
    intro F _ _ _ y Φ hΦ
    change evR Xo c f y = _
    obtain ⟨C, ψ, z, t', hz, hb⟩ := hA h F y
    obtain ⟨ΦC, u, hΦC, hu, huv⟩ := hv C
    obtain ⟨p, a, u₀, hu₀⟩ := hL.test C.R C.y
    have k₁ : evR Xo c f C.yg = C.R.val (evR Xo c f C.y) := by
      rw [GlobalTheory.FlagTan.evR_eq hf.1 hu₀, GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := C.R.val.comp a) hu₀ C.gen fun _ => rfl)]
      rfl
    have k₂ : evR Xo c f C.yg = ((u : C.R) : Om C.Z) := by
      rw [GlobalTheory.FlagTan.evR_frBor hf C.bor, prod_zpow_four_smul_keyEx, huv]
      have := hfb C.Z
      simp only [evC] at this
      rw [this, Units.val_mul]
    have k₃ : evR Xo c f C.y = (u : C.R) := Subtype.val_injective (k₁.symm.trans k₂)
    have k₄ : evR Xo c f z = ψ (u : C.R) := by
      rw [GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := ψ.comp a) hu₀ hz fun _ => rfl), ← k₃, GlobalTheory.FlagTan.evR_eq hf.1 hu₀]
      rfl
    obtain ⟨Ψ, hΨ⟩ := _root_.GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c g e F z hpq
    have k₅ := _root_.GlobalTheory.KeyFourth.rule_frBor κ h₁ h₂ E H Dw l Xo c g e F t' z y Ψ Φ hb hΨ hΦ
    have k₆ : (κ F Ψ.key : F) = ψ (u : C.R) :=
      hu F ψ.toRingHom Ψ.key (_root_.GlobalTheory.KeyFourth.tied_keyPB E H Dw l Xo c g e C.R F ψ C.y z ΦC Ψ hz hΦC hΨ)
    rw [GlobalTheory.FlagTan.evR_frBor hf hb, prod_zpow_four_smul_keyEx, k₄, k₅, Units.val_mul, k₆]

end GlobalTheory.KeyFourth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLinearBarDual
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeilTransfer

theorem transfer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∃ t : E →ₐ[F] Fv F v, ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (ν₀ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := GlobalTheory.T.split_place_embedding_exists F E σ hcm v hv.2
  let B' : Base F E := { B with v₁ := v, τ₁ := t }
  have hT' : IsTriple B' G X om om' :=
    { base := { hT.base with }
      geo := { hT.geo with hV := { hT.geo.hV with }, hV' := { hT.geo.hV' with }, hW := { hT.geo.hW with } }
      chars := { hT.chars with good := hv }
      weil := hT.weil
      weil' := hT.weil' }
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.LinBarAt.exists_isLinBar_at hP F E σ B a a' G X om om' hT v hv t
  have hι' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι := hι

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm t G.V'.J 1 herm hdet
  have hK : ∀ g, K g ∈ UAt σ G.V' (evFin F B'.v₁) ∧ (mat (K g)).map (piW B'.τ₁) = g.val ∧
      (mat (K g)).map (piW (B'.τ₁.comp σ)) = (G.V'.J.map B'.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map B'.τ₁ :=
    fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V' 1 herm hdet g, GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V'.J 1 herm hdet g,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.V'.J 1 herm hdet g⟩

  choose S hS using fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v (K g) (hK g).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (K g, 1) (tens (evFin F v) φ R) = tens (evFin F v) (S g φ) R :=
    fun g φ hφ => (hS g φ hφ).2 R (hR φ hφ)
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro c φ φ'; funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    apply eqR
    rw [← hSR g _ hm, tensLin, map_add (f := _), map_smul, hSR g φ hφ, hSR g φ' hφ', tensLin]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    apply eqR
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← hSR _ φ hφ, e1, map_mul, Module.End.mul_apply, hSR g' φ hφ, hSR g _ (h1 g' φ hφ)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    apply eqR
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← hSR _ φ hφ, e1, map_one, Module.End.one_apply]
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ g φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r :=
    fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hT v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator B' G X om om' hT' K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char B' G X om om' hT' K hK S h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι'

  have hvac := hT.geo.hM'.vac v
  have hιv : ι (G.M'.vac v) ≠ 0 := fun h0 =>
    hvac.2.1 (hι.bij.injOn hvac.1 (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  set φ₀ := GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT Y₀) (G.M'.vac v) with hφ₀def
  have hφ₀ : φ₀ ∈ SB (Fin a' × Fin (a + a') → Fv F v) := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ _ hvac.1
  have hφ₀0 : ι φ₀ 0 ≠ 0 := by
    have e := congrFun (hTι Y₀ _ hvac.1) 0
    simp only [zero_add] at e
    rw [e]; exact hY₀

  obtain ⟨-, -, hcont⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  obtain ⟨U, hU, hUact⟩ := hcont φ₀ hφ₀
  have hKt : Tendsto K (𝓝 1) (𝓝 1) := GlobalTheory.T.split_unitary_lift_tendsto_one hcm t G.V'.J 1 herm hdet
  have hP1 : {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U} ∈ 𝓝 1 :=
    (hKt.prodMk_nhds tendsto_const_nhds) hU
  have hone : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := fun u _ => by simp [mat]
  have hsm : ∀ g ∈ {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U},
      (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) = 1 := by
    intro g hg
    have hact := hUact (K g, 1) hg (hK g).1 hone
    have hfix : S g φ₀ = φ₀ := eqR _ _ (by rw [← hSR g φ₀ hφ₀]; exact hact R (hR φ₀ hφ₀))
    have e := congrFun (hC ι hι' g φ₀ hφ₀) 0
    rw [hfix] at e
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_zero,
      Matrix.zero_mul] at e
    have e2 : ι φ₀ 0 * 1 = ι φ₀ 0 * ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
      rw [mul_one]; nth_rw 1 [e]; ring
    exact (mul_left_cancel₀ hφ₀0 e2).symm
  have hsmooth : GlobalTheory.SmGL.IsSmoothChar ν := _root_.GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds (by have := (GlobalTheory.ThK.Inhab.two_le_rank hT).1; omega) ν _ _ hP1 hsm

  have hSo : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0 := by
    intro φ hφ
    constructor
    · rintro ⟨-, ι₂, hι₂, hvan⟩ Y hY
      have hι₂' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι₂ := hι₂
      obtain ⟨hT₂, hM₂, -, -⟩ := hA ι₂ hι₂'
      obtain ⟨c, hc⟩ := _root_.GlobalTheory.LinSchur.eq_smul_of_commute (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) hψc hψ1 ι₂ ι
        hι₂.bij (fun x _ y _ c => by rw [map_add (f := _), map_smul])
        (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT C))
        (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wM l))
        (fun C x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hT₂ C x hx, hTι C x hx⟩)
        (fun l x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hM₂ l x hx, hMι l x hx⟩)
      rw [hc φ hφ, Pi.smul_apply, hvan Y hY, smul_zero]
    · intro h
      exact ⟨hφ, ι, hι, h⟩
  refine ⟨t, ι, ν, hsmooth, hν, hι.bij, hSo, fun g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ =>
    ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩, _root_.GlobalTheory.WeilTransferW.unitaryW_acts_right hP F E σ B a a' G X om om' hT v hv t ι hι⟩
  rw [hC ι hι' g₀ φ hφ]
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, GlobalTheory.FullRankCoinv.lact, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one,
    Matrix.mul_one, Fintype.card_fin]

end GlobalTheory.WeilTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_vecEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Xo.XF c) :
    ∃ e : (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G) ≃ (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G),
      ∀ (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)),
        SameVecs Y x v (fun i => e (v i)) ∧ ∀ χ : 𝓞 E →+* R,
          IsEigBasisAt Xo.univ.t.act (x ≫ toX Xo c) χ v ↔
            IsEigBasisAt Y.t.act ((x ≫ Y.jQ) ≫ genι Y) χ (fun i => e (v i)) := by
  obtain ⟨e₀, he₀, hb₀⟩ := BdryUnit.exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act x (x ≫ toX Xo c) rfl
  obtain ⟨e, he, hb⟩ := BdryUnit.exists_eigEquiv Y.m.cart Y.m.act x ((x ≫ Y.jQ) ≫ genι Y) (Category.assoc _ _ _)
  refine ⟨e₀.symm.trans e, fun n v => ⟨fun i => ⟨e₀.symm (v i), ?_, (he _).symm⟩, fun χ => ?_⟩⟩
  · exact (he₀ _).symm.trans (congrArg (fun z => z.left) (e₀.apply_symm_apply (v i)))
  · have h := hb₀ χ n fun i => e₀.symm (v i)
    have hv : (fun i => e₀ (e₀.symm (v i))) = v := funext fun i => e₀.apply_symm_apply (v i)
    rw [hv] at h
    exact h.symm.trans (hb χ n fun i => e₀.symm (v i))

theorem frame_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c), (∀ v w, FrU Xo c U τ j x v w → ∃ vb wb, FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) ∧ (∀ (V : Set (gen Y)) vb wb, Set.range x ⊆ U → FrY Y V τ j (x ≫ Y.jQ) vb wb → ∃ v w, FrU Xo c U τ j x v w ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ R _ j x
  obtain ⟨e, he⟩ := exists_vecEquiv Y x
  have hs : (x ≫ Y.jQ) ≫ genStr Y = x ≫ toF Xo c := by
    rw [Category.assoc]
    exact congrArg (x ≫ ·) Y.jQ_over
  refine ⟨fun v w h => ⟨fun i => e (v i), fun i => e (w i),
    ⟨hs.trans h.1, ?_, ((he _ v).2 _).1 h.2.2.1, ((he _ w).2 _).1 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩,
    fun V vb wb hU h => ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact subset_closure ⟨x z, h.2.1 ⟨z, rfl⟩, by simp⟩
  · obtain ⟨v, rfl⟩ : ∃ v : Fin D.p → _, vb = fun i => e (v i) :=
      ⟨fun i => e.symm (vb i), funext fun i => (e.apply_symm_apply _).symm⟩
    obtain ⟨w, rfl⟩ : ∃ w : Fin D.q → _, wb = fun i => e (w i) :=
      ⟨fun i => e.symm (wb i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, w, ⟨hs.symm.trans h.1, hU, ((he _ v).2 _).2 h.2.2.1, ((he _ w).2 _).2 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveQuasiCompactQStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_q_surjective_and_quasiCompact : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X] {oa : D.OAct O} (Y : Ray oa), Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  first | exact @GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | exact GlobalTheory.RayEv.Ray.surjective_quasiCompact_q | (intros; apply GlobalTheory.RayEv.Ray.surjective_quasiCompact_q <;> assumption)
end

