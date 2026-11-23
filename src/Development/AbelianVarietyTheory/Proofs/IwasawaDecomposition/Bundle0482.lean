module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActionsOnLiftRulesExtendedDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.ActExt

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.LevelActionPinned
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

private theorem congr_of_two_lifts {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : V.rank = L.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM0 : M ≠ 0) {Mb Mh : Ideal (𝓞 D.host.E)}
    (hMb : Mb = ∏ PP ∈ L.Pg, PP.asIdeal) (hM : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) (hcop : Mb ⊔ Mh = ⊤)
    {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {u u' : La →ₗ[𝓞 D.host.E] La}
    (hu : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w)
    (hu' : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u' a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w) (a : La) :
    u' a - u a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨κ, hκ, h1⟩ := hu
  obtain ⟨κ', hκ', h1'⟩ := hu'
  have hM₁ : (∏ PP ∈ L.Pg, PP.asIdeal) * Mh = Ideal.span {(M : 𝓞 D.host.E)} := by rw [← hMb, hM]
  have hMm : (M : 𝓞 D.host.E) ∈ Mb :=
    Ideal.mul_le_left (I := Mb) (J := Mh) (by rw [hM]; exact Ideal.mem_span_singleton_self _)
  have hst := mulVec_mem_of_St hβ (Formalism.L2.DIV.parLev_St hκ.2.1)
  have hd := Lev.lift_div_mem hκ hκ'
  obtain ⟨s, hs, v, hv, huv⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Mb ⊔ Mh)
  have hva : v • a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La) := Submodule.smul_mem_smul hv Submodule.mem_top
  obtain ⟨w₁, hw₁, e₁⟩ := h1 _ hva
  obtain ⟨w₂, hw₂, e₂⟩ := h1' _ hva
  obtain ⟨w₃, hw₃, e₃⟩ := lift_one_congr (L := L) hβ hL hι hM₁ hd.2.1 (Subgroup.mem_bot.1 hd.2.2) _ hva
  have e₄ : (finHom V κ').val = (finHom V κ).val * (finHom V (κ⁻¹ * κ')).val := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e₅ : fvec V ι (u' (v • a) - u (v • a)) = M • (w₂ - w₁ + (finHom V κ).val *ᵥ w₃) := by
    have e₁' : fvec V ι (u (v • a)) - (finHom V κ).val *ᵥ fvec V ι (v • a) = M • w₁ := e₁
    have e₂' : fvec V ι (u' (v • a)) - (finHom V κ').val *ᵥ fvec V ι (v • a) = M • w₂ := e₂
    rw [smul_add, smul_sub, ← Matrix.mulVec_smul, ← e₁', ← e₂', ← e₃, map_sub, e₄, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  obtain ⟨x, hx⟩ := exists_eq_nsmul hι hM0 _ _ (add_mem (sub_mem hw₂ hw₁) (hst _ hw₃)) e₅
  have e₆ : u' a - u a = s • (u' a - u a) + (M : 𝓞 D.host.E) • x := by
    rw [Nat.cast_smul_eq_nsmul, ← hx, map_smul, map_smul, ← smul_sub, ← add_smul, huv, one_smul]
  rw [e₆]
  exact add_mem (Submodule.smul_mem_smul hs Submodule.mem_top) (Submodule.smul_mem_smul hMm Submodule.mem_top)

private theorem latEmb_iota {D : D7} (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)

private theorem act_heq {D : D7} (i : Fin D.R.m)
    {β β' : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} (eβ : β' = β)
    {Λ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)} (hβ : IsSDFrame (Wc D i) (β i) Λ 1)
    {Pg Pg' : Finset (Formalism.L2.DIV.Pl D.host.E)} (eP : Pg' = Pg)
    {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {ι : ∀ j, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} {ι' : ∀ j, (Dw' j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    (hι : HEq ι' ι)
    (hemb : LatEmb (Wc D i) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)))
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal)
    {G : Type} [Group G] {eG : G ≃* G0 Pg D.R.r} {eG' : G ≃* G0 Pg' D.R.r} (heG : HEq eG' eG)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La}
    {lev' : G → (Dw' ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw' ((i : ℕ) + 1)).La}
    (hlev : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) (Dw ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) (lev g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) a)) = l.M • w)
    (hlev' : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β' i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG' g) κ ∧
      ∀ a ∈ Mfr l' • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) (lev' g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) a)) = l'.M • w)
    (g : G) (r : Rul (Xo ((i : ℕ) + 1)) c) (r' : Rul (Xo' ((i : ℕ) + 1)) c') (hr : HEq r' r) :
    HEq (actLev (Xo := Xo' ((i : ℕ) + 1)) c' (fun g => (lev' g, LinearMap.id)) g r')
      (actLev (Xo := Xo ((i : ℕ) + 1)) c (fun g => (lev g, LinearMap.id)) g r) := by
  subst eβ eP hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hι
  obtain rfl := eq_of_heq heG
  obtain rfl := eq_of_heq hr
  have key : ∀ g a, lev' g a - lev g a ∈ l'.Mb • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La) := fun g a =>
    congr_of_two_lifts
      (L := datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B)
      hβ (rank_Wc i) hemb (by have := l'.three_le; omega) hMb l'.prod l'.coprime (hlev g) (hlev' g) a
  have e : (fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev' g, LinearMap.id)) g y y') =
      fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev g, LinearMap.id)) g y y' := by
    funext S _ _ g y y'
    exact propext (GlobalTheory.LevelActionOfLifts.levR_congr (key g) y y')
  unfold actLev
  rw [e]

private theorem geo_facts {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
    (B : GlobalTheory.RealGeo.GeoHalf T R ph) (i : Fin D.R.m) :
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (B.O i).lev ∧ T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧ LatEmb (Wc D i) (iotaW T i) :=
  ⟨(B.pins i).2.lift.lev, ((B.pins i).2.tuple ()).half.1, latEmb_iota T B.fw.laws i⟩

end GlobalTheory.Mem.R3.ActExt

set_option maxHeartbeats 2000000 in
theorem _root_.GlobalTheory.T.levelActions_on_liftRules_extendedData : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g →
        ∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r →
          HEq (Formalism.L2.Pj.actLev z'.core.Q.c (z'.geo.O j').lev2 g' r') (Formalism.L2.Pj.actLev z.core.Q.c (z.geo.O j).lev2 g r) := by
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj g g' hg r r' hr => ?_
  obtain ⟨h1, h3, h4⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z.geo j
  obtain ⟨h2, -, -⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z'.geo j'
  have h5 := z.lev.is.βW j
  have hB := hE.1
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e
  cases w with | mk px => ?_
  cases w' with | mk px' => ?_
  dsimp only at hpx px px'
  cases hpx
  have eg : g' = g := eq_of_heq hg
  subst eg
  exact GlobalTheory.Mem.R3.ActExt.act_heq j' (eq_of_heq hx.βW) h5 (eq_of_heq hx.Pg) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.iota h4 h3 hx.eG h1 h2 g' r r' hr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LocalRigid

theorem eq_of_diagonal_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion (pullback.diagonal f)] (a b : Sp A ⟶ X) (h : a ≫ f = b ≫ f)
    (κ : Type) [Field κ] (c : A →+* κ) [IsLocalHom c] (hc : spMap c ≫ a = spMap c ≫ b) : a = b := by
  let l : Sp A ⟶ pullback f f := pullback.lift a b h
  have hq : (spMap c ≫ a) ≫ pullback.diagonal f = spMap c ≫ l := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, pullback.lift_snd, hc]
  let q : Sp κ ⟶ pullback (pullback.diagonal f) l := pullback.lift _ _ hq
  have hmem : (IsLocalRing.closedPoint A : Sp A) ∈ Set.range (pullback.snd (pullback.diagonal f) l) := by
    let pt : Sp κ := IsLocalRing.closedPoint κ
    refine ⟨q pt, ?_⟩
    have e : (q ≫ pullback.snd _ _) pt = spMap c pt := by rw [pullback.lift_snd]
    rw [Scheme.Hom.comp_apply] at e
    rw [e]
    exact IsLocalRing.comap_closedPoint c
  have hs : Function.Surjective (pullback.snd (pullback.diagonal f) l) := fun p =>
    (IsLocalRing.specializes_closedPoint (R := A) p).mem_open
      (pullback.snd (pullback.diagonal f) l).isOpenEmbedding.isOpen_range hmem
  have : Epi (pullback.snd (pullback.diagonal f) l).base := (TopCat.epi_iff_surjective _).2 hs
  have : IsIso (pullback.snd (pullback.diagonal f) l) := IsOpenImmersion.isIso _
  have hl : l = inv (pullback.snd (pullback.diagonal f) l) ≫ pullback.fst _ _ ≫ pullback.diagonal f := by
    rw [pullback.condition, IsIso.inv_hom_id_assoc]
  have ha : a = l ≫ pullback.fst f f := (pullback.lift_fst _ _ _).symm
  have hb : b = l ≫ pullback.snd f f := (pullback.lift_snd _ _ _).symm
  rw [ha, hb, hl]
  simp

end GlobalTheory.LocalRigid

namespace GlobalTheory.LocalRigid

theorem eq_of_pow_eq_of_closedPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ S) (k : ℕ), IsUnit (k : A) →
    ∀ (x y : Over.mk s ⟶ G), x ^ k = y ^ k →
    ∀ (κ : Type) [Field κ] (c : A →+* κ), IsLocalHom c → spMap c ≫ x.left = spMap c ≫ y.left → x = y := by
  intro S G _ _ hG A _ _ s k hk x y hxy κ _ c hc hxc
  haveI := hc
  let GA := (Over.pullback s).obj G
  haveI : Smooth GA.hom := inferInstanceAs (Smooth (pullback.snd G.hom s))
  have hu : IsUnit (k : Γ(Sp A, ⊤)) := by
    simpa using hk.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  haveI het : Etale (mulN GA k).left := GrpTangent.etale_mulN GA hu
  let e := TorsionLift.ptsEquiv s G (Over.mk (𝟙 (Sp A))) s (Category.id_comp s)
  have h1 : e.symm x ≫ mulN GA k = e.symm y ≫ mulN GA k := by
    rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← map_pow, ← map_pow, hxy]
  have h2 : (e.symm x).left ≫ (mulN GA k).left = (e.symm y).left ≫ (mulN GA k).left := by
    simpa using congrArg CommaMorphism.left h1
  have hfst : ∀ z, (e z).left = z.left ≫ pullback.fst G.hom s := fun z =>
    TorsionLift.ptsEquiv_left s G _ s (Category.id_comp s) z
  have h3 : spMap c ≫ (e.symm x).left = spMap c ≫ (e.symm y).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← hfst, ← hfst]
      simpa using hxc
    · have wx := Over.w (e.symm x)
      have wy := Over.w (e.symm y)
      rw [Category.assoc, Category.assoc]
      exact (congrArg (spMap c ≫ ·) wx).trans (congrArg (spMap c ≫ ·) wy).symm
  have h4 := eq_of_diagonal_of_closedPoint _ _ _ h2 κ c h3
  have h5 : e.symm x = e.symm y := Over.OverMorphism.ext h4
  simpa using congrArg e h5

end GlobalTheory.LocalRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepNearLiftsComponentMemLocalChartGroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevGe

theorem exists_put : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (κ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∃ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) ∧ bc (prV (E := E) v) x = bc (prV (E := E) v) κ := by
  intro F E _ _ _ _ _ σ n J v κ hκ
  classical
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ) 1,
    Formalism.UG.P.afsplitU_mem v σ J _ 1 (Formalism.UG.P.afsplit_bc_mem σ J v κ hκ) (one_mem _), fun w hw => ?_, ?_⟩
  · apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw, Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · exact Formalism.UG.P.afsplit_right1 v _ 1


set_option maxHeartbeats 800000 in
theorem mem_uloc : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → (∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ LiftsInv I κ' P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ' P' 1) → bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ (K (chOf c)).lev.Uloc v := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P v hv κ hκ g hg hF hL
  obtain ⟨N, hN⟩ := GlobalTheory.T.stepLevel_contains_deep_congruence_at_bad_prime I hOk hPins l Z a (B.T u) i hi bad (K (chOf c)).lev P v hv
  obtain ⟨x, hx, hxoff, hxv⟩ := exists_put _ _ v κ hκ
  obtain ⟨kk, hkk⟩ : ∃ kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)), kk = k (chOf c) := ⟨_, rfl⟩
  obtain ⟨z, hz, hzoff, hzN, g', hg', hgg', hpt⟩ := GlobalTheory.T.deepElement_conj_rational_at_badPrime I hOk hPins l Z a i hi kk fb (hkk ▸ hfb) P v hv κ hκ g hg hF x hx hxv N
  obtain ⟨κ', hK, hLP, hLo⟩ := hL g' hg' hgg'
  have hxz : x * z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := mul_mem hx hz
  have hxzoff : ∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') (x * z) = 1 := fun v' hv' => by
    calc
      _ = bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') x * bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') z := map_mul _ _ _
      _ = 1 * 1 := congrArg₂ (· * ·) (hxoff v' hv') (hzoff v' hv')
      _ = 1 := one_mul 1
  have hpt' : ∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s) := hpt
  have hq := GlobalTheory.T.representative_image_point_of_lift I hOk hPins l Z u a i hi bad Ch chOf K k hR c kk hkk P v hv (x * z) hxz hxzoff g' hg' hpt' κ' hK hLP hLo
  subst hkk
  have hxzU : x * z ∈ (K (chOf c)).lev.U := (hR.lev c (x * z) _ hq).2 ⟨κ', hK.1, rfl, hK.2⟩
  have hzU : z ∈ (K (chOf c)).lev.U := hN z hz hzoff hzN
  have hxU : x ∈ (K (chOf c)).lev.U := by
    have := mul_mem hxzU (inv_mem hzU)
    rwa [mul_inv_cancel_right] at this
  have := (((K (chOf c)).lev.U_eq x).1 hxU).2 v
  rwa [hxv] at this

end GlobalTheory.Mem.Col2.AdT.LevGe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section
namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cusp_match {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f' : cusp (Xo' j') c' (U' j') a' n') :
    ∃ f : cusp (Xo j) c (U j) a n, HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f', HEq.rfl, Iff.rfl⟩

theorem cusp_match' {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f : cusp (Xo j) c (U j) a n) :
    ∃ f' : cusp (Xo' j') c' (U' j') a' n', HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f, HEq.rfl, Iff.rfl⟩

theorem extendByZero_eq_of_heq_families {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : ext0 (a' t) = ext0 (a t) := by
  subst hj; cases h; rfl

section Comparison₂
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem nrm_le_one_iff (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m)
    (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) :
    (∀ la (y : (R.FW i).Pt la), (R.FW i).nrm la y (fw.e i f) ≤ 1) ↔
      ∀ la, ∀ v ∈ valSet (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (algCls (T.Q.Xo ((i : ℕ) + 1)) T.Q.c) la,
        0 ≤ v (f : T.R ((i : ℕ) + 1)) := by
  constructor
  · intro h la v hv
    have h1 := h la ((fw.pt i la).symm ⟨v, hv⟩)
    rw [fw.nrm_eq, Core.nrmM_le_one_iff, Equiv.apply_symm_apply] at h1
    exact h1
  · intro h la y
    rw [fw.nrm_eq, Core.nrmM_le_one_iff]
    exact h la _ (fw.pt i la y).2

end Comparison₂

end GlobalTheory.Mem.R3.MKExt

namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor


set_option maxHeartbeats 4000000 in
theorem mk_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ((z'.R.FW j').MK : Set (Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)) = {x' | ∃ x ∈ (z.R.FW j).MK, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hN j j' hj φ hφ => ?_
  obtain ⟨hB, -⟩ := hE
  clear * - hB hN hj φ hφ
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M1 := fun f' => cusp_match hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f'
  have M2 := fun f => cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  ext x'
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨f', he'⟩ : ∃ f', z'.geo.fw.e j' f' = ⟨x', h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f, hff, hP⟩ := M1 f'
    have hI' : ∀ la (y : (z'.R.FW j').Pt la), (z'.R.FW j').nrm la y (z'.geo.fw.e j' f') ≤ 1 := by
      rw [he']; exact h2
    have hI := hP.1 ((nrm_le_one_iff z'.geo.fw j' f').1 hI')
    have hx' : ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = x' :=
      congrArg Subtype.val he'
    refine ⟨((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL),
      ⟨(z.geo.fw.e j f).2, (nrm_le_one_iff z.geo.fw j f).2 hI⟩, fun k k' hk => ?_⟩
    have h3 := hN.forms j j' hj f f' hff k k' hk
    apply hinj
    rw [hφ]
    exact (congrArg (fun v => (w'.st Z').toD7.what₂.embLL (v k')) hx').symm.trans h3
  · rintro ⟨x, ⟨h1, h2⟩, hrel⟩
    obtain ⟨f, he⟩ : ∃ f, z.geo.fw.e j f = ⟨x, h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f', hff, hP⟩ := M2 f
    have hI : ∀ la (y : (z.R.FW j).Pt la), (z.R.FW j).nrm la y (z.geo.fw.e j f) ≤ 1 := by
      rw [he]; exact h2
    have hI' := hP.2 ((nrm_le_one_iff z.geo.fw j f).1 hI)
    have hx : ((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = x :=
      congrArg Subtype.val he
    have hx' : x' = ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
      funext k'
      have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
      have h3 := hN.forms j j' hj f f' hff (Fin.cast hn k') k' hk
      have h4 := hrel (Fin.cast hn k') k' hk
      apply hinj
      rw [h4]
      exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
    subst hx'
    exact ⟨(z'.geo.fw.e j' f').2, (nrm_le_one_iff z'.geo.fw j' f').2 hI'⟩

end GlobalTheory.Mem.R3.MKExt
end
end

