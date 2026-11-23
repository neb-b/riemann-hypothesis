module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpLinComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverDominatingPairStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_dominating_pair : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (W V : Mean4O.Cover Y) (k : W.G ⟶ V.G),
    k ≫ V.π = W.π →
    ∃ (W' : Mean4O.Cover Y) (a : W'.X ⟶ W.X) (b : W'.X ⟶ V.X), a ≫ W.p = W'.p ∧ b ≫ V.p = W'.p ∧
      Lies W' W a ∧ Lies W' V b := by
  first | exact @GlobalTheory.Mean4O.CoverDom.exists_cover_dominating_cover | exact GlobalTheory.Mean4O.CoverDom.exists_cover_dominating_cover | (intros; apply GlobalTheory.Mean4O.CoverDom.exists_cover_dominating_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverValueRoot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.OnCmp.CoverRoot

theorem xiVal_cast {D : D7} (T : Full D) (hT : LawsFull T) (j n : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : σ = T.toTop.toCore.σ₀) (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    ∃ (U₂ : _) (dict₂ : _), CXiVal W hr σ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j σ) fun _ => T.xi := by
  subst hσ hV
  obtain ⟨_, U, d, h⟩ := hT.xiVal j hj n
  exact ⟨U, d, h⟩

theorem value_mem {D : D7} (T : Full D) (hT : LawsFull T) (j n : ℕ) (hj : InR D j) (τ : (T.dδ j n).c₂.F →+* ℂ)
    (hτ : τ = (T.dδ j n).c₂.F.val.toRingHom) (y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt τ)) :
    ∃ z, toC (evR (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).cδ y) = τ z := by
  subst hτ
  obtain ⟨Cls, _, _, δ, gdet, -, h⟩ := hT.sh.dRoot j hj n
  exact ⟨_, h y⟩


open GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal GlobalTheory.AdTh.CoverVal in
set_option maxHeartbeats 1000000 in
theorem cover_value_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ χ : (AE D)ˣ →* Circle, ChrEq χ (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) → ∃ c0' : ℂ, c0' ∈ D.what₂.embLL.range ∧ (∃ m : ℕ, 0 < m ∧ c0' ^ m = 1) ∧ (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hR i hO v _ hval0 hrun χ hχ
  have hI : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hs : (O i).s0 = T.toTop.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨U₂, dict₂, c0, hroot, hc⟩ := xiVal_cast T hT _ (Vc D i).rank (inR i) (O i).s0 hs (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc ()
  have hlev := hT.sh.dLev _ (inR i) (Vc D i).rank
  have hA := hT.lvA _ (inR i) (Vc D i).rank
  obtain ⟨-, -, -, χ₁, hχ₁, hxi⟩ := hrun
  obtain rfl : χ₁ = χ := GlobalTheory.ChrEqUnique.idc_unique D _ _ _ hχ₁ hχ
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hR hI i (O i).s0
    hs (T.dict _ (O i).s0 1).1
  have hτ : (O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F) =
      (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F.val.toRingHom := RingHom.ext fun _ => rfl
  have hσ : GoodEmb (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ((O i).s0.comp
      ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((U₂ ()).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((U₂ ()).X j) (T.x₀ ((i : ℕ) + 1) (O i).s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hex, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  have hv : ∀ (k : GA D (Wc D i)) (xk : (AE D)ˣ), IsDetRoot (Wc D i) k xk →
      rdU (U₂ ()) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ (dict₂ () k).1 (dict₂ () k).2 = c0 * ((χ₁ xk : Circle) : ℂ) := by
    intro k xk hxk
    obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
    obtain ⟨a, ha⟩ := hrat γ' hγ'
    have hv := hval k γ' ⟨hγ', h2, h3⟩
    rw [hxi _ _ (hmul _ _ _ _ ha hxk), map_mul, hχ.1.2 a, _root_.one_mul] at hv
    exact hv
  have hat := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (U₂ ()) hσ hU h1 hA R.θ (Wc D i) (rank_Wc i)
    (dict₂ ()) (iotaW T.J i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt
  refine ⟨c0, ?_, hroot, ?_⟩
  · obtain ⟨x1, hx1⟩ := hex 1
    obtain ⟨hon, -⟩ := hat 1
    obtain ⟨-, hu2, -⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r ((U₂ ()).X (dict₂ () 1).1).p0
      ((U₂ ()).X (dict₂ () 1).1).Ψ ((U₂ ()).X (dict₂ () 1).1).Gm ((U₂ ()).X (dict₂ () 1).1).Gm_herm
    have hd : (dict₂ () 1).2 ∈ ((U₂ ()).X (dict₂ () 1).1).dom := (hu2 _ hon).1
    obtain ⟨z, hz⟩ := value_mem T hT _ _ (inR i) _ hτ ((U₂ ()).un _ ⟨_, hd⟩)
    have h2 : c0 * ((χ₁ x1 : Circle) : ℂ) = _ := ((hv 1 x1 hx1).symm.trans (dif_pos hd)).trans hz
    obtain ⟨y, hy⟩ := GlobalTheory.BigOn.CoreWit.exists_val_of_chrEq hχ x1
    obtain ⟨b, hb⟩ := hval0 y
    have hres := res_embLL T.J hI.alg hI.laws.pins.2.2.1
    refine ⟨algebraMap T.Q.c.F D.what₂.LL ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm z) / b, ?_⟩
    rw [map_div₀, hb, ← hy, div_eq_iff (Circle.coe_ne_zero _), h2]
    exact (DFunLike.congr_fun hres _).trans (DFunLike.congr_fun hs.symm _)
  · intro X g bas idx e k xk mk hX hp hsy hi hL hxk hmk hk y₂ A₂ hA₂
    obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := hat k
    obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (U₂ ())) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T.J i)
      _ Wt (dict₂ () k).1 (dict₂ () k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hsy hi hL hmk hk y₂ A₂ hA₂
    exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans (hv k xk hxk))

end GlobalTheory.OnCmp.CoverRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechKS

theorem Pt.nonempty_affHom_of_in {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s) (h : P.In U.1) :
    Nonempty ((Pt.aff s U).Hom P) := by
  let φ := GlobalTheory.Points.valMap P.x U.1 h
  have hc : ∀ r : R, φ.hom (algebraMap R (CechDR.Sec s U.1) r) = algebraMap R P.B r := by
    intro r
    change φ.hom ((s.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [← GlobalTheory.Points.valR_eq P.x U.1 h, GlobalTheory.Points.valR_appLE P.x s le_top h, P.w,
      GlobalTheory.Points.valR_specMap]
    rfl
  refine ⟨⟨{ φ.hom with commutes' := hc }, ?_⟩⟩
  exact GlobalTheory.Points.specMap_valMap_fromSpec U.2 P.x h

theorem Pt.affHom_ρ_eq_valR {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a : (Pt.aff s U).Hom P) (b : Γ(X, U.1)) : a.ρ b = valR P.x U.1 b := by
  have hpre : ⊤ ≤ (CechDR.affPt s U) ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have hid : valR (CechDR.affPt s U) U.1 b = b := by
    rw [GlobalTheory.Points.valR_eq _ _ hpre]
    have h1 : Spec.map (𝟙 Γ(X, U.1)) ≫ U.2.fromSpec = CechDR.affPt s U := by
      rw [Spec.map_id, Category.id_comp]; rfl
    have h2 := GlobalTheory.Points.valMap_specMap_fromSpec U.2 (𝟙 Γ(X, U.1)) (h1 ▸ hpre)
    have h3 : GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre = 𝟙 _ := by
      have key : ∀ (x : Spec Γ(X, U.1) ⟶ X) (hx : x = CechDR.affPt s U) (h : ⊤ ≤ x ⁻¹ᵁ U.1),
          GlobalTheory.Points.valMap x U.1 h = GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre := by
        rintro _ rfl _; rfl
      exact (key _ h1 _).symm.trans h2
    rw [h3]; rfl
  rw [← a.pt, GlobalTheory.Points.valR_spMap_comp _ _ _ hpre, hid]
  rfl

theorem eq_of_valR_eq_on_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {J : Type} (W : J → X.Opens)
    (hW : ⨆ j, W j = ⊤) (V : X.Opens) (f g : Γ(X, V))
    (h : ∀ (P : Pt s) (j : J), P.In V → P.In (W j) → valR P.x V f = valR P.x V g) : f = g := by
  refine TopCat.Presheaf.section_ext X.sheaf V f g fun x hx ↦ ?_
  have hxW : x ∈ ⨆ j, W j := by rw [hW]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxW
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ W j) ⟨hx, hj⟩
  have hle : U' ≤ V ⊓ W j := hsub
  have hleV : U' ≤ V := hle.trans inf_le_left
  let Ua : X.affineOpens := ⟨U', hU'⟩
  have hPU : (Pt.aff s Ua).In U' := hU'.fromSpec_preimage_self.ge
  have hv := h (Pt.aff s Ua) j (hPU.mono hleV) (hPU.mono (hle.trans inf_le_right))
  have key : ∀ b : Γ(X, V), valR (Pt.aff s Ua).x V b = (X.presheaf.map (homOfLE hleV).op).hom b := by
    intro b
    rw [← GlobalTheory.Points.valR_res (Pt.aff s Ua).x hleV hPU b]
    exact (Pt.affHom_ρ_eq_valR s Ua (Pt.aff s Ua) (Pt.Hom.id _) _).symm
  rw [key, key] at hv
  have := congrArg (X.presheaf.germ U' x hxU') hv
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this

theorem Pt.affHom_subsingleton {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a a' : (Pt.aff s U).Hom P) : a = a' := by
  obtain ⟨ρ, e⟩ := a
  obtain ⟨ρ', e'⟩ := a'
  have : ρ = ρ' := AlgHom.ext fun b ↦ (Pt.affHom_ρ_eq_valR s U P ⟨ρ, e⟩ b).trans (Pt.affHom_ρ_eq_valR s U P ⟨ρ', e'⟩ b).symm
  subst this; rfl

theorem Pt.Hom.comp_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {P Q T : Pt s}
    (φ : P.Hom Q) (ψ : Q.Hom T) : (φ.comp ψ).triv = φ.triv ≫ ψ.triv :=
  Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)

theorem h1_mk_mem_f1_of_isRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  intro R _ X s J W hW c hc
  obtain ⟨G, hG1, hG2⟩ := hc
  have hG : ∀ j j' (P : Pt s), P.In (W j) → P.In (W j') → G j P = G j' P := fun j j' P h h' ↦
    sub_eq_zero.1 (hG2 j j' P h h')
  change toH1O s (H1.mk _ c) = 0
  refine (injective_iff_map_eq_zero (GlobalTheory.CechDR.cmpO s)).1
    (GlobalTheory.CechDR.cmpO_injective R X s) _ ?_
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine H1.mk_eq_zero.2 ?_
  classical
  let aP : ∀ (U : X.affineOpens) (P : Pt s), P.In U.1 → (Pt.aff s U).Hom P :=
    fun U P h ↦ (Pt.nonempty_affHom_of_in s U P h).some
  let FU : X.affineOpens → PtFn s := fun U P ↦
    if h : P.In U.1 ∧ ∃ j, P.In (W j) then G h.2.choose P - ev c (aP U P h.1).triv else 0
  have FU_eq : ∀ U (P : Pt s) j (hU : P.In U.1), P.In (W j) → FU U P = G j P - ev c (aP U P hU).triv := by
    intro U P j hU hj
    have h : P.In U.1 ∧ ∃ j, P.In (W j) := ⟨hU, j, hj⟩
    simp only [FU, dif_pos h]
    rw [hG _ j P h.2.choose_spec hj]
  have ex : ∀ U : X.affineOpens, ∃ f : Γ(X, U.1), ∀ (j : J) (P : Pt s), P.In (U.1 ⊓ W j) →
      FU U P = valR P.x U.1 f := by
    intro U
    refine GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover R X s J (fun j ↦ U.1 ⊓ W j) U.1 (fun j ↦ inf_le_left) ?_ (FU U) ?_
    · rw [← inf_iSup_eq, hW, inf_top_eq]
    · intro j P Q φ hP
      have hU : P.In U.1 := hP.mono inf_le_left
      have hj : P.In (W j) := hP.mono inf_le_right
      rw [FU_eq U P j hU hj, FU_eq U Q j (hU.map φ) (hj.map φ),
        Pt.affHom_subsingleton s U Q (aP U Q (hU.map φ)) ((aP U P hU).comp φ), Pt.Hom.comp_triv, ev_comp,
        hG1 j P Q φ hj, map_sub]
      have e : φ.triv.φ (ev c (aP U P hU).triv) = φ.ρ (ev c (aP U P hU).triv) := rfl
      rw [e]; ring
  choose f hf using ex
  refine ⟨fun U ↦ f U.unop, ?_⟩
  funext U V a
  have hle : V.unop.1 ≤ U.unop.1 := leOfHom a.unop
  refine eq_of_valR_eq_on_cover s W hW V.unop.1 _ _ fun P j hV hj ↦ ?_
  change valR P.x V.unop.1 (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
    (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) = valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv)
  have hU : P.In U.unop.1 := hV.mono hle
  set b := aP V.unop P hV
  have e1 : valR P.x V.unop.1 (f V.unop) = FU V.unop P := (hf V.unop j P (hV.inf hj)).symm
  have e2 : valR P.x V.unop.1 (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) = FU U.unop P :=
    (GlobalTheory.Points.valR_res P.x hle hV (f U.unop)).trans (hf U.unop j P (hU.inf hj)).symm
  have e3 : aP U.unop P hU = (Pt.affHom s hle).comp b := Pt.affHom_subsingleton s _ P _ _
  have e4 : ev c (aP U.unop P hU).triv = b.ρ (ev c (Pt.affHom s hle).triv) + ev c b.triv := by
    rw [e3, Pt.Hom.comp_triv, ev_comp]; rfl
  have e5 : valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv) = b.ρ (ev c (Pt.affHom s hle).triv) :=
    (Pt.affHom_ρ_eq_valR s V.unop P b _).symm
  have e6 : b.ρ (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
      (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) =
      b.ρ (f V.unop) - b.ρ (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) := map_sub b.ρ _ _
  rw [e5, ← Pt.affHom_ρ_eq_valR s V.unop P b, e6, Pt.affHom_ρ_eq_valR s V.unop P b (f V.unop),
    Pt.affHom_ρ_eq_valR s V.unop P b (GlobalTheory.CechDR.Sec.res s hle (f U.unop)), e1, e2,
    FU_eq V.unop P j hV hj, FU_eq U.unop P j hU hj, e4]
  ring

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianScheme
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanAdd

theorem tanVal_mul_all (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (f : Form (A.hom ≫ 𝟙 (Sp R))) (a b : epsR R ⟶ A) :
    tanVal (a * b) f = tanVal a f + tanVal b f := by
  have hg2 : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom A.hom).flip hg
    rw [Over.tensorObj_hom]
    exact smoothOfRelativeDimension_comp g g _ _
  have hP : AllPrim (dp0 R) (𝟙 _) A :=
    (GlobalTheory.AbelianPrim.abelianDeRham_free (_root_.GlobalTheory.Proof.abelianDeRhamFree_of_hodge hC hH) R A g hA hg).1
  have hc : Form.cl _ f ∈ prim (dp0 R) (𝟙 _) A := by rw [hP]; trivial
  rw [mem_prim_iff] at hc
  have mμ : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R) (μ[A]).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m1 : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R)
      (SemiCartesianMonoidalCategory.fst A A).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m2 : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 (Sp R)) (RingHom.id R)
      (SemiCartesianMonoidalCategory.snd A A).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have e0 : pullOver (dp0 R) (𝟙 _) μ[A] (Form.cl _ f) = mμ.pull1 (Form.cl _ f) := rfl
  have e1 : pullOver (dp0 R) (𝟙 _) (SemiCartesianMonoidalCategory.fst A A) (Form.cl _ f) =
    m1.pull1 (Form.cl _ f) := rfl
  have e2 : pullOver (dp0 R) (𝟙 _) (SemiCartesianMonoidalCategory.snd A A) (Form.cl _ f) =
    m2.pull1 (Form.cl _ f) := rfl
  have hcl : Form.cl _ (mμ.pullForm f - (m1.pullForm f + m2.pullForm f)) = 0 :=
    ((map_sub _ _ _).trans (congrArg₂ (· - ·) (IsMor.cl_pullForm mμ f)
      ((map_add _ _ _).trans (congrArg₂ (· + ·) (IsMor.cl_pullForm m1 f) (IsMor.cl_pullForm m2 f))))).trans
      ((congrArg₂ (· - ·) e0 (congrArg₂ (· + ·) e1 e2)).symm.trans (sub_eq_zero.2 hc))
  have hinj : Function.Injective (GlobalTheory.CechDR.clForm ((A ⊗ A).hom ≫ 𝟙 (Sp R))) :=
    (hH R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hg2).2.2.2.2.1.2.1
  have hcmp : GlobalTheory.CechDR.cmpForm _ (mμ.pullForm f - (m1.pullForm f + m2.pullForm f)) = 0 :=
    hinj (((GlobalTheory.CechDR.comparison_formClass _ _).symm.trans ((congrArg _ hcl).trans (map_zero _))).trans (map_zero _).symm)
  have h0 := _root_.GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero R (A ⊗ A) (lift a b) _ hcmp
  have h1 : tanVal (lift a b) (mμ.pullForm f) = tanVal (lift a b) (m1.pullForm f + m2.pullForm f) :=
    sub_eq_zero.1 ((map_sub _ _ _).symm.trans h0)
  calc tanVal (a * b) f = tanVal (lift a b ≫ μ[A]) f := by rw [Hom.mul_def]
    _ = tanVal (lift a b) (mμ.pullForm f) := tanVal_comp _ _ mμ f
    _ = tanVal (lift a b) (m1.pullForm f) + tanVal (lift a b) (m2.pullForm f) := h1.trans (map_add _ _ _)
    _ = tanVal (lift a b ≫ SemiCartesianMonoidalCategory.fst A A) f +
        tanVal (lift a b ≫ SemiCartesianMonoidalCategory.snd A A) f :=
      (congrArg₂ (· + ·) (tanVal_comp _ _ m1 f) (tanVal_comp _ _ m2 f)).symm
    _ = tanVal a f + tanVal b f :=
      congrArg₂ (fun x y ↦ tanVal x f + tanVal y f) (lift_fst a b) (lift_snd a b)

end GlobalTheory.TanAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeSymm_compat_descends_from_pushed_points : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  first | exact @GlobalTheory.CubeSymDescent.of_push | exact GlobalTheory.CubeSymDescent.of_push | (intros; apply GlobalTheory.CubeSymDescent.of_push <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8Power
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowE8

theorem exists_cp_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), ∃ Q : GlobalTheory.UU.CP (powObj G₀ 8), Q.L.L = GlobalTheory.PowE8.e8LB G₀ P.L.L W := by
  intro S G₀ _ _ P W
  haveI hm : ∀ k : (Fin 8 × Fin 8) × Fin 4,
      IsMonHom ((![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
        Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2) := by
    rintro ⟨⟨a, b⟩, i⟩
    fin_cases i <;> dsimp <;>
      first
        | infer_instance
        | exact (inferInstance : IsMonHom (lift (powPr G₀ a) (powPr G₀ b) ≫ μ))
        | exact (inferInstance : IsMonHom (toUnit (powObj G₀ 8) ≫ η[G₀]))
  obtain ⟨Q, hQ⟩ := GlobalTheory.LinCombCP.exists_cp_linComb P (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => (![powPr G₀ k.1.1 * powPr G₀ k.1.2, powPr G₀ k.1.1, powPr G₀ k.1.2, 1] :
      Fin 4 → (powObj G₀ 8 ⟶ G₀)) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2))
  refine ⟨Q, hQ.trans ?_⟩
  unfold GlobalTheory.PowE8.e8LB GlobalTheory.LinCombCP.cpLB
  congr 1
  funext k
  rcases k with ⟨⟨a, b⟩, i⟩
  fin_cases i <;> rfl

end GlobalTheory.PowE8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPullbackCocyclesPointValue
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cupZ_pull_apply_fv : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  intro R _ A B m₁ m₂ a b E _ _ E' _ _ E'' _ _ φ ψ z
  have e1 : fv (m₁.coef.pullbackOneCocycle a) E E' φ z = fv a E E' φ (z ≫ fst A B) := by
    rw [_root_.GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull R A (A ⊗ B) (fst A B) m₁ a]; rfl
  have e2 : fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
    rw [_root_.GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull R B (A ⊗ B) (snd A B) m₂ b]; simp only [Fn1.pull, Category.assoc]
  rw [cupZ_apply]
  change ψ (fv (m₁.coef.pullbackOneCocycle a) E E' φ z) *
    fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = _
  rw [e1, e2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentInvariantOfChartwiseProjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.descent_eqn_of_chart_projection : ∀ (B S X G : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)) (ψ : J → (U.left ⟶ G)) (β : X ⟶ G), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ j, e j ≫ β = pullback.fst _ _ ≫ ψ j) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  intro B S X G π f Φ U J e ψ β he hcov hf hβ hch
  let 𝒰 : (pullback f (pullback.fst π π)).OpenCover :=
    Scheme.Cover.mkOfCovers J (fun j => pullback (e j) (pullback.fst f (pullback.fst π π)))
      (fun j => pullback.snd _ _) (by
        intro q
        obtain ⟨j, y, hy⟩ := (by simpa [Set.mem_range] using hcov (pullback.fst f (pullback.fst π π) q) :
          ∃ j, ∃ y, (e j) y = pullback.fst f (pullback.fst π π) q)
        obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback
          (IsPullback.of_hasPullback (e j) (pullback.fst f (pullback.fst π π))) y q hy
        exact ⟨j, p, hp⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ (fun (j : J) => ?_)
  change pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _ =
    pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _
  have hc := pullback.condition (f := e j) (g := pullback.fst f (pullback.fst π π))
  generalize pullback.snd (e j) (pullback.fst f (pullback.fst π π)) = z at hc ⊢
  generalize pullback.fst (e j) (pullback.fst f (pullback.fst π π)) = y₁ at hc
  have h1 : y₁ ≫ pullback.snd U.hom π = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π := by
    calc y₁ ≫ pullback.snd U.hom π = y₁ ≫ e j ≫ f := by rw [hf]
      _ = z ≫ pullback.fst f (pullback.fst π π) ≫ f := by rw [reassoc_of% hc]
      _ = z ≫ pullback.snd f (pullback.fst π π) ≫ pullback.fst π π := by rw [pullback.condition]
      _ = _ := (Category.assoc _ _ _).symm
  have h2 : (y₁ ≫ pullback.fst U.hom π) ≫ U.hom =
      ((z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.snd π π) ≫ π := by
    calc (y₁ ≫ pullback.fst U.hom π) ≫ U.hom = y₁ ≫ pullback.snd U.hom π ≫ π := by
          rw [Category.assoc, pullback.condition]
      _ = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by rw [reassoc_of% h1]; simp only [Category.assoc]
      _ = _ := by rw [pullback.condition]; simp only [Category.assoc]
  have hΦ := hch j _ y₁ (pullback.lift _ _ h2) _ (pullback.lift_fst _ _ _).symm h1
    (pullback.lift_snd _ _ _) z hc.symm rfl
  calc z ≫ pullback.fst f (pullback.fst π π) ≫ β = y₁ ≫ e j ≫ β := by
        rw [reassoc_of% hc]
    _ = pullback.lift _ _ h2 ≫ e j ≫ β := by
        rw [hβ, pullback.lift_fst_assoc, Category.assoc]
    _ = z ≫ Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
        have h3 := congrArg (· ≫ β) hΦ
        simpa only [Category.assoc] using h3.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevelsStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_generate_connected_levels : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n, (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧ ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  first | exact @GlobalTheory.PDivGroup.exists_coords_generate | exact GlobalTheory.PDivGroup.exists_coords_generate | (intros; apply GlobalTheory.PDivGroup.exists_coords_generate <;> assumption)
end

