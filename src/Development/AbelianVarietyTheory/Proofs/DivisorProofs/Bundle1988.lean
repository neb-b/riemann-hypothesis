module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem frameCover_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V : (gen Y).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) D.p D.q := by
  intro E _ _ _ H D l Xo c O _ β Y V τ hτ z hz
  obtain ⟨U, hU, φ, f, hzU, hs, -⟩ := _root_.GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H D l Xo c O β Y z
  obtain ⟨⟨v, w, hfr, -⟩, -⟩ := GlobalTheory.DetLine.EigParts.eigFrame_match E H D l Xo c O β Y τ hτ Set.univ
    Γ(gen Y, U) φ hU.fromSpec hs (Set.subset_univ _) f
  obtain ⟨r, hrV, hzr⟩ := hU.exists_basicOpen_le (V := V) ⟨z, hz⟩ hzU
  have hW := hU.basicOpen r
  have hle : (gen Y).basicOpen r ≤ U := (gen Y).basicOpen_le r
  let g : Γ(gen Y, U) →+* Γ(gen Y, (gen Y).basicOpen r) := ((gen Y).presheaf.map (homOfLE hle).op).hom
  have hx : (show Sp Γ(gen Y, (gen Y).basicOpen r) ⟶ gen Y from hW.fromSpec) = spMap g ≫ hU.fromSpec :=
    (hU.map_fromSpec hW (homOfLE hle).op).symm
  obtain ⟨v', w', h', -, -⟩ := exists_pull g hfr hx
  refine ⟨(gen Y).basicOpen r, hW, g.comp φ, v', w', hzr, h'.1, ?_, h'.2.2⟩
  rw [hW.range_fromSpec]
  exact hrV

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentCharacterValuesAdditive
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtTanClass

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem exists_unit {T : Over (Sp R)} (g : GtPt D T) (hb : g.b = 1) (χ : D.X) :
    ∃ ρ : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ T.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (g.s χ) q z J = Geo.Tor.gm q z ⊤ ρ := by
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T g.b χ) (ε' := DegPre.gtε)
    (fun U _ h => Eq.symm (by
      refine (prod_pt g.b χ h).trans ?_
      rw [hb, _root_.mul_one]; simp)) (LB.oneGen D.P.L (Y := T.left))
    (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio D.P.isLB rfl (g.s χ) u (g.isGen χ) hu
  exact ⟨ρ, fun Z q z J hJ => by rw [hρ Z q z J hJ, vu Z q z J hJ, val_one, _root_.mul_one]⟩

omit [IsDomain R] in
theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    gs (spMap f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = toStkA z (f a) := by
  rw [gs_eq _ _ ⊤ trivial]
  have e := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom e.symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ _ D gm ⟨o, ho, hp⟩ hb
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
      IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hb1 : gm.b = 1 := hb
  choose ρ hρ using exists_unit gm hb1
  choose u hu using fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).commRingCatIsoToRingEquiv.symm.surjective (ρ χ).val
  have hv : ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → (val (gm.s χ) q z J).val =
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (u χ)) := fun χ Z q z J hJ =>
    (congrArg Units.val (hρ χ Z q z J hJ)).trans ((gs_unit q z ⊤ trivial _).symm.trans
      (congrArg (gs q z ⊤) (hu χ).symm))
  have h1 : ∀ χ, TrivSqZeroExt.fst (u χ : DualNumber R) = 1 := fun χ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt R)
    have e : val (gm.s χ) (redE R) (cpt R) J = 1 := by
      have e₁ := (val_corr hJ (hp.2 χ) (𝟙 (Sp R))).trans (val_pull hJ _ _ _)
      have e₂ := (val_corr hJ (ho.2 χ) (𝟙 (Sp R))).trans (val_one _)
      rw [← e₂, e₁]
      congr 1
    have e' := hv χ _ (redE R) (cpt R) J hJ
    rw [e] at e'
    refine toStkA_injective (A := R) ?_
    rw [map_one]
    exact (gs_spMap (TrivSqZeroExt.fstHom R R R).toRingHom (cpt R) (u χ)).symm.trans e'.symm
  have hm : ∀ χ χ', (u (χ + χ') : DualNumber R) = u χ * u χ' := fun χ χ' => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))
    have C : IsCub (th D (T := epsR R) (cpt (DualNumber R)) J) := isCub_cubV D.cub hJ
    have e := cv_add gm hJ χ χ'
    rw [hb1, C.face₃, _root_.mul_one] at e
    have k : ∀ χ, (cv gm χ (cpt (DualNumber R)) J).val = toStkA (cpt (DualNumber R)) (u χ) := fun χ =>
      (hv χ _ (𝟙 _) _ J hJ).trans (gs_eq _ _ ⊤ trivial _)
    refine toStkA_injective (A := DualNumber R) ?_
    rw [map_mul]
    exact (k _).symm.trans ((congrArg Units.val e).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (k _) (k _))))
  refine ⟨AddMonoidHom.mk' (fun χ => TrivSqZeroExt.snd (u χ : DualNumber R)) fun χ χ' => ?_, fun χ Z q z J hJ => ?_⟩
  · rw [hm, DualNumber.snd_mul, h1, h1]; ring
  · refine (hv χ Z q z J hJ).trans (congrArg (fun x => gs q z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom x)) ?_)
    exact TrivSqZeroExt.ext (by simp [h1]) (by simp)

end GlobalTheory.MBLow.GtTanClass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentPullbackComplexDualNumbers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanPull


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel in
set_option maxHeartbeats 1000000 in
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  intro V _ _ D C _ _ N ν gm₀ htan
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hG (TorusModel.splitExt D)
  obtain ⟨Φ, hp, ha⟩ := TorusModel.exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  have hTF : spMap (toF V C) = (TF (R := V) C).hom := by
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hTE : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    rw [TanLift.dualMap_over, hTF]; rfl
  let hh : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hTE
  obtain ⟨x₀, rfl⟩ := (Φ (epsR V)).surjective gm₀
  refine ⟨Φ _ (hh ≫ x₀), hp _ _ hh x₀, ?_, ?_, ?_⟩
  · obtain ⟨o₀, ho₀, hpo⟩ := htan
    let r : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) (TanLift.redE_over V)
    have e₀ : o₀ = Φ _ (r ≫ x₀) := by
      have hpo' : GtPt.IsPull (redE V) (Φ _ x₀) (Φ _ (r ≫ x₀)) := hp _ _ r x₀
      generalize hg : Φ _ (r ≫ x₀) = g at hpo' ⊢
      obtain ⟨b, s, h, hs, hm⟩ := o₀
      obtain ⟨b', s', h', hs', hm'⟩ := g
      have hb : b = b' := Over.OverMorphism.ext (hpo.1.trans hpo'.1.symm)
      subst b'
      have he : s = s' := funext fun χ =>
        GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ)
          (corr_of_val D.P.isLB fun y J hJ =>
            (val_corr hJ (hpo.2 χ) _).trans (val_corr hJ (hpo'.2 χ) _).symm)
      subst s'
      rfl
    have e₁ : r ≫ x₀ = 1 := (Φ _).injective ((e₀.symm.trans (GtVec.isZero_unique ho₀ (hz _))))
    let k : TF (R := V) C ⟶ TE V C := Over.homMk (redE C) (by
      show redE C ≫ spMap (algebraMap C (DualNumber C)) ≫ (TF (R := V) C).hom = (TF (R := V) C).hom
      rw [← Category.assoc, GtVec.red_comp, Category.id_comp])
    let tf : TF (R := V) C ⟶ baseOver (Sp V) := Over.homMk (TF (R := V) C).hom (Category.comp_id _)
    have e₂ : k ≫ hh = tf ≫ r := by
      ext
      show redE C ≫ spMap (dualMap (toF V C)) = (TF (R := V) C).hom ≫ redE V
      rw [← hTF]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have e₃ : k ≫ hh ≫ x₀ = 1 := by
      rw [← Category.assoc, e₂, Category.assoc, e₁, MonObj.comp_one]
    have hpk := hp _ _ k (hh ≫ x₀)
    rw [e₃] at hpk
    let g := Φ (TF (R := V) C) 1
    refine ⟨⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩, ⟨(hz _).1, (hz _).2⟩, hpk⟩
  · intro hb
    have e := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ hh x₀)).1
    rw [e, hb]
    simp
  · intro a χ hval
    have hloc : IsLocalRing (DualNumber C) := TanLift.isLocalRing_dualNumber C
    have hlocH : IsLocalHom (TrivSqZeroExt.fstHom C C C).toRingHom :=
      ⟨fun x hx => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 hx⟩
    set gm := Φ _ (hh ≫ x₀)
    let J' : (Sp (DualNumber C) ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (redE C ≫ ψ)
    have hJ' : Good D.P.L (cpt (DualNumber C)) J' := fun ψ => by
      have h1 := ν.good (redE C ≫ ψ) (show cpt C ∈ (⊤ : (Sp C).Opens) from trivial)
      have hc : (redE C) (cpt C) = cpt (DualNumber C) :=
        IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom C C C).toRingHom
      have h2 : ψ ((redE C) (cpt C)) ∈ D.P.L.U (J' ψ) := h1
      rw [hc] at h2
      exact h2
    have ht := (top_le_iff_cpt (𝟙 (Sp (DualNumber C))) _).2 (hJ'.mem (DegPre.gtφT D (TE V C) gm.b χ) (𝟙 _))
    apply toStkA_injective (A := DualNumber C)
    have toStkA_valR {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
        (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
        toStkA z (valR x U a.val) = (Geo.Tor.gm x z U a).val := by
      have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
      rw [valR, dif_pos ht, Geo.Tor.gm, dif_pos hz]
      show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) = _
      rw [Iso.hom_inv_id_apply]
      exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial _
    have l1 := toStkA_valR (𝟙 (Sp (DualNumber C))) _ (cpt (DualNumber C)) ht ((gm.s χ).s _)
    have l2 := (val_corr hJ' ((hp _ _ hh x₀).2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
    have l3 := hval _ (𝟙 _ ≫ hh.left) _ _ hJ'
    have hv1 : valR (𝟙 (Sp (DualNumber V))) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom
        (1 + TrivSqZeroExt.inr a)) = 1 + TrivSqZeroExt.inr a := by
      have h0 : ⊤ ≤ 𝟙 (Sp (DualNumber V)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
      rw [valR, dite_eq_left h0]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      erw [show (homOfLE h0) = 𝟙 (⊤ : (Sp (DualNumber V)).Opens) from rfl]
      simp
    have l4 := FormalValue.toStkA_map_valR (dualMap (toF V C)) (𝟙 (Sp (DualNumber V))) ⊤ (cpt (DualNumber C))
      (fun _ _ => trivial) ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))
    rw [hv1, Category.comp_id] at l4
    have hd : dualMap (toF V C) (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (toF V C a) := by
      ext <;> simp [dualMap]
    rw [hd] at l4
    rw [l4]
    refine l1.trans ?_
    refine (congrArg Units.val l2).trans ?_
    refine l3.trans ?_
    rw [Category.id_comp]
    rfl

end GlobalTheory.MBLow.TanPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentCombinationCharacterValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R]

theorem dual_mul (a b : R) : ((1 : DualNumber R) + TrivSqZeroExt.inr a) * (1 + TrivSqZeroExt.inr b) = 1 + TrivSqZeroExt.inr (a + b) := by
  ext <;> simp [add_comm]

theorem epsScaleR_one_add (c a : R) : epsScaleR c (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (c * a) := by
  ext <;> simp [epsScaleR, mul_comm]

section Gs

variable {Z : Scheme.{0}} (q : Z ⟶ (epsR R).left) (z : Z)

theorem gs_one_add_zero : gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr 0)) = 1 := by
  rw [gs_eq q z ⊤ trivial, TrivSqZeroExt.inr_zero, add_zero, map_one, map_one, map_one]

theorem gs_dual_mul (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) *
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr b)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a + b))) := by
  rw [← gs_mul q z ⊤ trivial, ← map_mul, dual_mul]

theorem gs_scale (c a : R) :
    gs (q ≫ (epsScale R c).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (c * a))) := by
  rw [← gs_pull q (epsScale R c).left z ⊤ trivial, ← epsScaleR_one_add]
  have e := congrArg (fun f => f.hom (1 + TrivSqZeroExt.inr a : DualNumber R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (epsScaleR c)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [e]
  rfl

end Gs

variable [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

def HasVals (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) (y : epsR R ⟶ H) (a : D.X → R) : Prop :=
  (Φ _ y).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (val ((Φ _ y).s χ) q z J).val = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a χ)))

theorem hasVals_one (hΦ : TorusModel.Represents Φ) : HasVals Φ 1 (fun _ => 0) := by
  have hz : (Φ (epsR R) 1).IsZero := GtVec.isZero_of_isAdd (by simpa using hΦ.2 (epsR R) 1 1)
  refine ⟨hz.1, fun χ Z q z J hJ => ?_⟩
  rw [val_corr hJ (hz.2 χ) q, val_one, gs_one_add_zero]
  rfl

theorem hasVals_scale (hΦ : TorusModel.Represents Φ) {y : epsR R ⟶ H} {a : D.X → R} (h : HasVals Φ y a) (c : R) :
    HasVals Φ (epsScale R c ≫ y) (fun χ => c * a χ) := by
  have hp := hΦ.1 (epsR R) (epsR R) (epsScale R c) y
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isPull_iff _ _ _).1 hp).1, h.1]
    simp only [DegPre.zeroT, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  · rw [val_corr hJ (hp.2 χ) q, val_pull hJ, h.2 χ Z _ z J hJ, gs_scale]

theorem hasVals_mul (hΦ : TorusModel.Represents Φ) {y y' : epsR R ⟶ H} {a a' : D.X → R} (h : HasVals Φ y a)
    (h' : HasVals Φ y' a') : HasVals Φ (y * y') (fun χ => a χ + a' χ) := by
  have hs := hΦ.2 (epsR R) y y'
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isAdd_iff _ _ _).1 hs).1, h.1, h'.1]
    exact _root_.mul_one _
  · have e := (val_mul hJ _ _ q).symm.trans ((val_corr hJ (hs.2 χ) q).trans (val_mul hJ _ _ q))
    let T' : Over (Sp R) := Over.mk (q ≫ (epsR R).hom)
    let ρ : T' ⟶ epsR R := Over.homMk q rfl
    have hc : val (DegPre.cubAtT D (epsR R) (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b) q z J = 1 := by
      have := val_cub D.cub ρ hJ (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b
      refine this.trans ?_
      rw [h'.1]
      have e1 : ρ ≫ DegPre.zeroT D (epsR R) = (1 : T' ⟶ D.P.A) := by
        simp only [DegPre.zeroT, ← Category.assoc]
        rw [Hom.one_def]
        congr 1
      rw [e1]
      exact (isCub_cubV D.cub hJ).face₃ _ _
    rw [hc, _root_.mul_one] at e
    rw [e, Units.val_mul, h.2 χ Z q z J hJ, h'.2 χ Z q z J hJ, gs_dual_mul]

end GlobalTheory.MBLow.TorusVals

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H]
  {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

theorem hasVals_tanComb (hΦ : TorusModel.Represents Φ) : ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)),
    (∀ l, HasVals Φ (x l) (a l)) → ∀ d : Fin r → R, HasVals Φ (tanComb d x) (fun χ => ∑ l, d l * a l χ)
  | 0, a, x, _, d => by
    have e : tanComb d x = 1 := by simp [tanComb]
    have ef : (fun χ => ∑ l : Fin 0, d l * a l χ) = fun _ => 0 := funext fun _ => by simp
    rw [e, ef]
    exact hasVals_one hΦ
  | r + 1, a, x, hx, d => by
    have e : tanComb d x = (epsScale R (d 0) ≫ x 0) * tanComb (fun i => d i.succ) (fun i => x i.succ) := by
      simp only [tanComb, List.ofFn_succ, List.prod_cons]
    have key := hasVals_mul hΦ (hasVals_scale hΦ (hx 0) (d 0))
      (hasVals_tanComb hΦ r (fun i => a i.succ) (fun i => x i.succ) (fun l => hx l.succ) (fun i => d i.succ))
    have ef : (fun χ => ∑ l, d l * a l χ) = fun χ => d 0 * a 0 χ + ∑ l : Fin r, d l.succ * a l.succ χ :=
      funext fun χ => Fin.sum_univ_succ _
    rw [e, ef]
    exact key

theorem tanComb_vals : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) :=
  fun _ _ _ _ _ _ _ _ hΦ r a x hx d => hasVals_tanComb hΦ r a x hx d

end GlobalTheory.MBLow.TorusVals

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  first | exact @GlobalTheory.MBLow.trF_dualPoint_of_isPull | exact GlobalTheory.MBLow.trF_dualPoint_of_isPull | (intros; apply GlobalTheory.MBLow.trF_dualPoint_of_isPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingIntegralStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_gl_embedding_integral : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((p : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat (K g)) 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ'' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) (boxFun φ₁ φ₂) φ'' →
    ∀ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ x, φ'' (Sum.elim x x) ∂μ =
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) * ∫ x, φ₁ x * φ₂ x ∂μ := by
  first | exact @GlobalTheory.DblDiag.diag_integral | exact GlobalTheory.DblDiag.diag_integral | (intros; apply GlobalTheory.DblDiag.diag_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackNonvanishingOfPulledSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullback_nonvanishing_of_pulledSection : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := by
  first | exact @GlobalTheory.TwistNZ.twistPull_nonzero | exact GlobalTheory.TwistNZ.twistPull_nonzero | (intros; apply GlobalTheory.TwistNZ.twistPull_nonzero <;> assumption)
end

