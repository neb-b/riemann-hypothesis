module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushSectionsCanonicalModification
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

namespace GlobalTheory.ModifCanon
open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

theorem stalkMap_bijective_of_isIso_restrict : ∀ (Y X : Scheme.{0}) (σ : X ⟶ Y) (U : Y.Opens), IsIso (σ ∣_ U) →
    ∀ x : X, x ∈ σ ⁻¹ᵁ U → Function.Bijective (σ.stalkMap x).hom := by
  intro Y X σ U h x hx
  have e := morphismRestrictStalkMap σ U ⟨x, hx⟩
  have h1 : IsIso ((σ ∣_ U).stalkMap ⟨x, hx⟩) := ((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 h).2 _
  have h2 : IsIso (σ.stalkMap x) := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).1 h1
  exact ConcreteCategory.bijective_of_isIso _

theorem isUnit_val_of_isUnit_germ : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y) (O : Y.Opens)
    (x : Sp ℂ ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) (e : Sp ℂ)
    (hy : x e ∈ O) (hiy : x e ∈ B.U i), IsUnit (H0.germ i (x e) hy hiy f) → IsUnit (H0.val x i hO hi f) := by
  intro k _ Y p B O x i hO hi f e hy hiy hu
  have hb : x e ∈ Y.basicOpen (f.loc i) := (Y.mem_basicOpen _ _ (Vanishing.memInf hy hiy)).2 hu
  have hV : ⊤ ≤ x ⁻¹ᵁ Y.basicOpen (f.loc i) := fun y _ => by rw [Subsingleton.elim y e]; exact hb
  rw [H0.val_apply, ← evalPt_res x (Y.basicOpen_le (f.loc i)) _ hV]
  exact (RingedSpace.isUnit_res_basicOpen Y.toLocallyRingedSpace.toRingedSpace (f.loc i)).map _

end GlobalTheory.ModifCanon

namespace GlobalTheory.ModifCanon

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

variable {X Y : Scheme.{0}}

abbrev jacChart {K' : LB X} {K B : LB Y} (σ : X ⟶ Y) (hK' : K'.IsLB) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.div K' (K.pull σ)) ((tens K B).pull σ) (tens K' (B.pull σ)) where
  isLB₁ := LB.isLB_div hK' (LB.isLB_pull hK σ)
  isLB₂ := LB.isLB_pull (isLB_tens hK hB) σ
  isLB₃ := isLB_tens hK' (LB.isLB_pull hB σ)
  τ := K'.ι × K.ι × B.ι
  a t := (t.1, pIdx K σ t.2.1)
  b t := pIdx (tens K B) σ (t.2.1, t.2.2)
  c t := (t.1, pIdx B σ t.2.2)
  cover x := by
    obtain ⟨i, hi⟩ := exists_chart hK' x
    obtain ⟨j, hj⟩ := exists_chart hK (σ x)
    obtain ⟨l, hl⟩ := exists_chart hB (σ x)
    exact ⟨(i, j, l), ⟨hi, mem_pIdx.2 hj⟩, mem_pIdx.2 ⟨hj, hl⟩, hi, mem_pIdx.2 hl⟩
  rule x t t' e e' := by
    rw [tr_tens _ _ x e.2.2 e'.2.2, tr_div _ _ x e.1 e'.1, tr_pull _ σ x e.2.1 e'.2.1,
      tr_pull _ σ x e.2.2.2 e'.2.2.2, tr_pull _ σ x e.1.2 e'.1.2,
      tr_tens _ _ (σ x) (mem_pull.1 e.2.1) (mem_pull.1 e'.2.1), map_mul, mul_assoc]
    exact congrArg (tr K' x t.1 t'.1 * ·) (inv_mul_cancel_left _ _).symm

theorem val_restr {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} (x : Sp ℂ ⟶ Y) (i : B.ι)
    (h : O' ≤ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) _ _ (f.loc i)

theorem exists_push_sections : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  intro F _ _ Y _ p d _ U M K K' B hproj hU hB
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  have : Nonempty U := hU.to_subtype
  have := M.iso
  have hXi : IsIntegral M.X := _root_.GlobalTheory.isIntegral_of_nonempty_modif F Y p U d M hU
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.exists_jacobian_section_isUnit_germ F Y M.X p M.σ d K K'
  have hL : (tens K.bundle B).IsLB := isLB_tens K.isLB hB
  let C := jacChart M.σ K'.isLB K.isLB hB
  have hopn : ∀ x ∈ M.opn, Function.Bijective (M.σ.stalkMap x).hom :=
    stalkMap_bijective_of_isIso_restrict Y M.X M.σ U M.iso
  have hJU : NowhereZero (H0.restr (le_top : M.opn ≤ ⊤) J) := fun x hx a ha => by
    rw [germ_restr]; exact hJ x (hopn x hx) a ha
  have hT : M.opn ≤ M.σ ⁻¹ᵁ (⊤ : Y.Opens) := fun x _ => memTop (M.σ x)
  have ext : ∀ g : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤, ∃ s : H0 p (tens K.bundle B) ⊤,
      C.mul (H0.restr le_top J) (H0.pull M.σ hT s) = H0.restr le_top g := by
    intro g
    obtain ⟨s₀, hs₀⟩ := (M.bijective_pull hL).2 ((C.mulEquiv hJU).symm (H0.restr le_top g))
    have rel : C.mul (H0.restr le_top J) (H0.pull M.σ le_rfl s₀) = H0.restr le_top g := by
      rw [hs₀]; exact (C.mulEquiv hJU).apply_symm_apply _
    obtain ⟨t, ht⟩ := (exists_sec_res_eq_iff hL (W := U) (LB.coord_mem s₀)).2 (fun x hx1 _ => by
      have := IsNormalScheme.isDiscreteValuationRing_stalk hx1
      obtain ⟨x', rfl, hb⟩ := _root_.GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr F Y p U d M hproj hU x this
      obtain ⟨i, hi⟩ := exists_chart hL (M.σ x')
      have : Nonempty ((tens K.bundle B).U i) := ⟨⟨_, hi⟩⟩
      have hne := nonempty_inf_of_isIntegral U ((tens K.bundle B).U i)
      exact ⟨i, hne, hi, _root_.GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull F Y M.X p M.σ U _ _ _ C J g s₀ rel x' hb (hJ x' hb) i hi⟩)
    refine ⟨H0.ofSec p ⊤ t, ?_⟩
    have e : H0.restr (le_top : U ≤ ⊤) (H0.ofSec p ⊤ t) = s₀ := by
      rw [restr_ofSec]; exact LB.sec_ext fun i => ht i
    rw [← rel, ← e, pull_restr]
  choose Ψ hΨ using ext
  refine ⟨Ψ, fun z hz k' hk' k hk => ?_⟩
  obtain ⟨e⟩ : Nonempty (Sp ℂ) := inferInstance
  have all : ∀ (V : M.X.Opens), z e ∈ V → ⊤ ≤ z ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y e]; exact hV
  have he : z e ∈ M.opn := hz trivial
  obtain ⟨t, ha, hb, hc⟩ := C.cover (z e)
  have ha' := all _ ha
  have hb' := all _ hb
  have hc' := all _ hc
  have hb'' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U ((C.b t) PUnit.unit) := fun y _ => by
    rw [Subsingleton.elim y e]; exact mem_pull.1 hb
  have hJv := isUnit_val_of_isUnit_germ F M.X M.str _ M.opn z (C.a t) hz ha' (H0.restr le_top J) e he ha
    (hJU _ he _ ha)
  obtain ⟨T1, hT1, e2⟩ : ∃ T1 : ℂ, T1 ≠ 0 ∧ ∀ g, H0.val z k' le_top hk' g = T1 * H0.val z (C.c t) le_top hc' g :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := M.str) (O := ⊤) z k' (C.c t) le_top hk' hc' g⟩
  obtain ⟨T2, hT2, e1⟩ : ∃ T2 : ℂ, T2 ≠ 0 ∧ ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) =
      T2 * H0.val (z ≫ M.σ) ((C.b t) PUnit.unit) le_top hb'' (Ψ g) :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := p) (O := ⊤) (z ≫ M.σ) k ((C.b t) PUnit.unit) le_top hk hb'' (Ψ g)⟩
  refine ⟨Units.mk0 (T2 / (H0.val z (C.a t) hz ha' (H0.restr le_top J) * T1))
    (div_ne_zero hT2 (mul_ne_zero hJv.ne_zero hT1)), fun g => ?_⟩
  have e3 := C.val_mul (H0.restr le_top J) (H0.pull M.σ hT (Ψ g)) t z hz ha' hb' hc'
  rw [hΨ g, val_restr z _ le_top hz le_top] at e3
  have e4 := val_pull M.σ hT z (C.b t) hz hb' le_top hb'' (Ψ g)
  rw [e1, e2, e3, ← e4, Units.val_mk0]
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hJv.ne_zero hT1)]
  ring

end GlobalTheory.ModifCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarOfModels
section
set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCuspTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem cuspW_congr {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : cuspW Xo c U G = cuspW Xo c U G' := by
  ext f
  rw [mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem wtOf_four_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 4).1 (τ, i) = -4 := by
  unfold Datum.mult at hi
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h] at hi
    simp only [wtOf, dif_pos h, dif_pos hi, Pi.zero_apply, zero_sub]
  · rw [if_neg h] at hi
    have h' : conjEmb τ (H.rt : E) = H.rt0 := conj_mem h
    simp only [wtOf, dif_neg h, dif_pos h', dif_pos hi, Pi.zero_apply, neg_zero, zero_sub]

theorem exZ_four_add (n : ℕ) :
    exZ Dw (wtZ (fun _ => 4) n + wtOf Dw 0 4) = exZ Dw (wtZ 0 (n + 8)) := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · show ((n : ℤ) + 2 * 4) = ((n + 8 : ℕ) : ℤ)
    push_cast; ring
  · show ((4 : ℕ) : ℤ) + (wtOf Dw 0 4).1 (τ, i) = ((0 : ℕ) : ℤ)
    rw [wtOf_four_fst τ i i.2]
    simp

theorem exists_twist {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (Z : Comp Xo c) :
    ∃ s : Rul Xo c, (∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + wtOf Dw 0 4)) ∧
      ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 ≠ 0 := by
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨ρ, -⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0)
    hL.geo hL.pos hKmem hKval
  have hadd : wtOf Dw 0 4 + wtOf Dw 0 (-4) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  have hex : exZ Dw (wtOf Dw 0 4) = -((4 : ℤ) • GlobalTheory.ShFam.keyEx Dw) := by
    rw [← GlobalTheory.KeyArchNorm.exZ_wtOf, ← GlobalTheory.FlatTw.exZ_neg_eq, neg_eq_of_add_eq_zero_left hadd]
  set s : Rul Xo c := idem Z * ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 4)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hKmem)
    rwa [zero_add, ← hex] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsK : s * (K : Rul Xo c) = idem Z := by rw [hs, mul_assoc, Units.inv_mul, mul_one]
  have hnorm : ∀ σ, GoodEmb c σ → ∃ C : ℝ, 0 < C ∧ ∀ z ∈ framesOn (U σ) Z,
      homN (U σ) x (wtOf Dw 0 4) s z * C = 1 := by
    intro σ hσ
    obtain ⟨C, hC0, -, hC⟩ := GlobalTheory.KeyArchNorm.homN_key_const κ k₁ k₂ k₅ E H Dw l Xo c _ e σ r (U σ) x K hσ (hL.unf σ hσ)
      (hL.xi σ hσ) ⟨ρ⟩ hL.pos hKmem hKval
    refine ⟨C, hC0, fun z hz => ?_⟩
    obtain ⟨hy, hlies⟩ := hz
    have h1 : homN (U σ) x (wtOf Dw 0 (-4)) (K : Rul Xo c) z = C := hC z.1 z.2 hy
    have ht := tested_of_homN_ne (U σ) x hy (h1.trans_ne hC0.ne')
    rw [← h1, ← homN_mul (U σ) x (even_wtOf _ _) (even_wtOf _ _) _ _ z hy, hadd, hsK]
    exact homN_idem (U σ) x hy hlies ht
  refine ⟨s, GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 4) s ⟨ρ⟩ hL.unf hL.pos (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_four_fst τ j hj, wtOf_four_fst τ i (hij.trans_lt hj)]) hsm hsupp
    (fun σ hσ => ?_), fun σ hσ z hz h0 => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hnorm σ hσ
    exact ⟨C⁻¹, fun z hz => (eq_inv_of_mul_eq_one_left (hC z hz)).le⟩
  · obtain ⟨C, -, hC⟩ := hnorm σ hσ
    have h3 := hC z hz
    have h4 : homN (U σ) x (wtOf Dw 0 4) s z = 0 := by
      simp [homN, ptN, Data.pnorm, h0]
    rw [h4, zero_mul] at h3
    exact zero_ne_one h3

theorem exists_scalar_of_four {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) {n : ℕ} (hn : Even n) {f : Rul Xo c} (hf : f ∈ cusp Xo c U (fun _ => 4) n)
    {z : Σ k, Frame ((U σ).X k).Ψ r} (hz : z ∈ framesOn (U σ) Z) (hne : rdU (U σ) f z.1 z.2 ≠ 0) :
    ∃ f₀ ∈ cusp Xo c U 0 (n + 8), rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  obtain ⟨s, hs, hs0⟩ := exists_twist hL Z
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 4) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  have hev : Even (wtZ (E := E) (fun _ => 4) n).2 := by
    show Even ((n : ℕ) : ℤ)
    exact_mod_cast hn
  have h1 := (hs _ hev g g.2).1
  rw [cuspW_congr hL.unf (exZ_four_add n), cuspW_wtZ] at h1
  refine ⟨_, h1, ?_⟩
  have h2 := hs0 σ hσ z hz
  obtain ⟨hy, hlies⟩ := hz
  have e : rdU (U σ) (g : Rul Xo c) z.1 z.2 = rdU (U σ) f z.1 z.2 := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, e]
  exact mul_ne_zero hne h2

theorem exists_scalar_of_model {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) {n : ℕ} (hn : Even n) (hb : 4 * (finrank ℚ E * r) + 4 ≤ n)
    {k : (U σ).Comp} {y : Frame ((U σ).X k).Ψ r} (hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z)
    {P : Frame ((U σ).X k).Ψ r → ℂ} (hP : P ∈ ((U σ).X k).SS (laU (U σ) 0 (n + 8) k)) (hne : P y ≠ 0) :
    ∃ f₀ ∈ cusp Xo c U 0 (n + 8), rdU (U σ) f₀ k y ≠ 0 := by
  classical
  have hla : laU (U σ) (fun _ => 4) n = laU (U σ) 0 (n + 8) := by
    funext k' τ j
    have e : (n + 8) / 2 = n / 2 + 4 := by omega
    simp only [laU, Pi.zero_apply, e]
    split_ifs <;> push_cast <;> ring
  let P₀ : FDSec (U σ).X := Pi.single k (((U σ).X k).dom.indicator P)
  have hQ : P₀ ∈ holSub0 (U σ).X (laU (U σ) (fun _ => 4) n) := by
    rw [hla]
    refine ⟨holCusp_mem_holSub _ _ fun k' => ?_, fun k' y' hy' => ?_⟩
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact (GlobalTheory.DomCongr.bddSec_cusp_congr E r _ _ P _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
      · simp only [P₀, Pi.single_eq_of_ne h]
        exact (siegelSpaceAlgebra_holds (E := E) r ((U σ).X k') (laU (U σ) 0 (n + 8) k') (laU (U σ) 0 (n + 8) k') 0).1.1
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact Set.indicator_of_notMem hy' _
      · simp only [P₀, Pi.single_eq_of_ne h, Pi.zero_apply]
  have hQy : P₀ k y ≠ 0 := by
    simp only [P₀, Pi.single_eq_same]
    rw [Set.indicator_of_mem hz.1]; exact hne
  have hspan := hL.onto _ hσ (fun _ => 4) n ⟨fun _ => antitone_const, hn⟩ (fun _ _ _ => by norm_num) hb hQ
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 4) n, rdU (U σ) f k y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let ev : FDSec (U σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U (fun _ => 4) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    exact hQy (hle hspan)
  exact exists_scalar_of_four hL hσ Z hn hf hz hfy

theorem exists_scalar_of_models
    (hP : ∀ X : Data E r, 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0)
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  obtain ⟨k, hk⟩ := GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  have hp0 : ((U σ).X k).p0 = Dw.q := (hU.2.1 k).1
  have hla : ∀ n : ℕ, laU (U σ) 0 n k = fun (τ : ((U σ).X k).Ψ) (j : Fin r) =>
      if ((U σ).X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) := fun n => by
    funext τ j
    simp [laU]
  obtain ⟨n, hn, hev, P, hPm, y, hy, hne⟩ := hP ((U σ).X k) (by omega) (by omega)
    (fun n hn γ hγ => by rw [← hla]; exact hL.chi σ hσ 0 n ⟨fun _ => antitone_const, hn⟩ k γ hγ)
    (4 * (finrank ℚ E * r) + 12)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have hm : Even m := by
    obtain ⟨t, ht⟩ := hev
    exact ⟨t - 4, by omega⟩
  have hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
    rw [hk]; exact ⟨rfl, hy⟩
  rw [← hla] at hPm
  obtain ⟨f, hf, hf0⟩ := exists_scalar_of_model hL hσ Z hm (by omega) hz hPm hne
  exact ⟨m + 8, by omega, hev, f, hf, ⟨k, y⟩, hz, hf0⟩

end GlobalTheory.ScalarCuspTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingSectionOfIsolatedNonKltPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_sep_of_lcCut : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  intro hNadel X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro M Δ m G N D ρ d x x' hM hΔ hm hG hN hdeg hD hdρ hx hxx' hlc hx'
  haveI hNoeth : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m', D₀, hm', hD₀, rfl, hDn⟩ := hD

  have hq0 : 0 < ρ - d := sub_pos.2 hdρ
  set a : ℕ := (ρ - d).num.toNat with ha_def
  set b : ℕ := (ρ - d).den with hb_def
  have hb : 0 < b := (ρ - d).den_pos
  have hnum : 0 < (ρ - d).num := Rat.num_pos.2 hq0
  have ha : ((a : ℤ) : ℚ) = (ρ - d).num := by
    rw [ha_def, Int.toNat_of_nonneg hnum.le]
  have ha1 : 1 ≤ a := by omega
  have hab : ρ - d = (a : ℚ) / b := by
    have e := Rat.num_div_den (ρ - d)
    rw [← ha, Int.cast_natCast] at e
    exact e.symm
  have hpS : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hNa : IsAmpleLB (lbPow N a) := (isAmpleLB_pow_iff hN.isLB ha1).2 hN
  have hdeg' : ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) =
      interNumRed ℂ C ![toLB (m' • G + m • D₀)] / ((m * m' : ℕ) : ℚ) +
        interNumRed ℂ C ![lbPow N a] / (b : ℚ) := by
    intro C hC
    have e := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • G + m • D₀))
      (isLB_lbPow (isLB_toLB G) m') (isLB_lbPow (isLB_toLB D₀) m)
      (by rw [cls_lbPow (isLB_toLB G), cls_lbPow (isLB_toLB D₀), ← toPic_apply, ← toPic_apply,
        ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (isLB_toLB G), hC.interNumRed_lbPow hH (isLB_toLB D₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have h3 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have hD' := hDn C hC
    rw [div_eq_iff h2] at hD'
    rw [hdeg C hC, e, hC.interNumRed_lbPow hH hN.isLB a, show ρ = d + a / b by linarith]
    push_cast
    rw [hD']
    field_simp
    ring
  obtain ⟨J, hJ, hvan⟩ := hNadel X p n hp hn M (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) b
    (lbPow N a) hM (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', D₀, hm', hD₀, rfl⟩)
    (Nat.mul_pos hm hm') (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG) hb
    hNa.isNef (IsAmpleLB.isBig ℂ X hpS _ hNa) hdeg'
  have hxJ : x ∈ J.support := (hJ x).2 hlc.2.1
  have hx'J : x' ∈ J.support := (hJ x').2 hx'
  obtain ⟨U, hxU, hU⟩ := exists_open_inter_eq_singleton_of_no_generisation X (J.support : Set X) x
    J.support.isClosed hx hxJ fun z hz hzx => by
      by_contra hne
      obtain ⟨e, -, he, h1⟩ := closure_point_topologicalKrullDim X n z hn
      have h0 := hlc.2.2 z hzx ((hJ z).1 hz)
      have he1 := h1 x hzx (Ne.symm hne)
      rw [he] at h0
      have : e ≤ 0 := by exact_mod_cast h0
      omega
  obtain ⟨s, hs1, hs2⟩ := exists_sec_mem_nonzeroLocus_of_isolated_zero_else ℂ X p hp M hM J x U hx
    hxU hU (hvan 1 one_pos)
  exact ⟨s, hs1, hs2 x' hx'J (Ne.symm hxx')⟩

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTangentOfAdditiveMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorVec

theorem exists_torus_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ D l
  obtain ⟨ν, hb, hv⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := epsR R)
    (fun x => GlobalTheory.TorusTangent.oneAdd (l x)) fun x y => by rw [map_add (f := _), GlobalTheory.TorusTangent.oneAdd_add]
  refine ⟨ν, ?_, hb, fun χ Z q z J hJ => ?_⟩
  · obtain ⟨g₀, h₀, v₀⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := baseOver (Sp R)) (fun _ => 1)
      fun _ _ => (_root_.mul_one _).symm
    refine ⟨g₀, ⟨h₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [v₀ x _ _ y J hJ, map_one, val_one]
    · rw [h₀, hb, GlobalTheory.TorusTangent.zeroT_left, GlobalTheory.TorusTangent.zeroT_left, ← Category.assoc]
      exact congrArg (· ≫ eSec D.P.A) GlobalTheory.TorusTangent.fst_inl.symm
    · refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
        (GlobalTheory.TorusTangent.hasVal_spMap (hv x) (TrivSqZeroExt.fstHom R R R).toRingHom hJ).symm))
      rw [GlobalTheory.TorusTangent.valR_oneAdd, map_one]
      simp
  · rw [hv χ Z q z J hJ, ← gs_unit q z ⊤ trivial]
    rfl

end GlobalTheory.MBLow.TorVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorGroupDeterminantsNeZeroStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_groupDeterminants_ne_zero : ∀ (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V] (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ)) (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V), (∀ i, ∃ j, r i j = 1) → (∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0) → (∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) → ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  first | exact @GlobalTheory.GenericGroupDet.exists_vec_det_ne_zero | exact GlobalTheory.GenericGroupDet.exists_vec_det_ne_zero | (intros; apply GlobalTheory.GenericGroupDet.exists_vec_det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyMemberTangentValueEqFirstJetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyMember_tangentValue_eq_firstJet : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g) (G : Geo ν d) (b : TE R ℂ ⟶ D.P.A) (W : Fin g → ℂ), redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → IsD ν d W b → ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (ct : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ), ν.FamV s f → N.c α = d.ex ct → Differentiable ℂ φ → (∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z)) → sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) = (TrivSqZeroExt.inl (φ 0) + TrivSqZeroExt.inr (fderiv ℂ φ 0 W)) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) ^ k * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) := by
  first | exact @GlobalTheory.MBLow.Cl.sE_fam_eq_jet | exact GlobalTheory.MBLow.Cl.sE_fam_eq_jet | (intros; apply GlobalTheory.MBLow.Cl.sE_fam_eq_jet <;> assumption)
end

