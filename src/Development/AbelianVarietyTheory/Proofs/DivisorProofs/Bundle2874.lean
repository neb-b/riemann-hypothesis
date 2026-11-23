module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumLiftDatumSameHalfTranslateConjugatePlac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtAlg

theorem valR_eq' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq' x U h, map_add (f := _)]

theorem valR_sub' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq' x U h, map_sub]

theorem valR_mul'' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq' x U h, map_mul]

theorem valR_zero' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) :
    valR x U (0 : Γ(X, U)) = 0 := by
  unfold valR; split_ifs <;> simp

theorem valR_natCast' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (m : ℕ) : valR x U (m : Γ(X, U)) = m := by
  simp only [valR_eq' x U h, map_natCast]

theorem appLE_congr_top {P P' : Scheme.{0}} (b b' : P ⟶ P') (e : b = b') (h h') :
    b.appLE ⊤ ⊤ h = b'.appLE ⊤ ⊤ h' := by
  subst e; rfl

theorem valR_constFn_congr {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (x x' : Sp A ⟶ X) (p : X ⟶ Sp B)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : x ≫ p = x' ≫ p) (r : B) :
    valR x U (constFn p U r) = valR x' U (constFn p U r) := by
  have key : ∀ (b : Sp A ⟶ X) (hb : ⊤ ≤ b ⁻¹ᵁ U) (y : Γ(Sp B, ⊤)),
      (b.appLE U ⊤ hb).hom ((p.appLE ⊤ U (fun _ _ => trivial)).hom y) = ((b ≫ p).appLE ⊤ ⊤ (fun _ _ => trivial)).hom y := by
    intro b hb y
    rw [← Scheme.Hom.appLE_comp_appLE]; rfl
  rw [valR_eq' x U h, valR_eq' x' U h', constFn, key, key]
  have hh := appLE_congr_top (x ≫ p) (x' ≫ p) e (fun _ _ => trivial) (fun _ _ => trivial)
  rw [hh]

theorem rsT_self {X : Scheme.{0}} {O : X.Opens} (s : Γ(X, O)) : rsT s O = s := by
  simp [rsT, resG]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_zero {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    c 0 = 1 := by
  have hu : unitOn (c 0) = 1 := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e := hc 0 y J hJ
    rw [(val_corr hJ (Y.Φ _ x').s_zero _).trans (val_one _), (val_corr hJ (Y.Φ _ x).s_zero _).trans (val_one _),
      _root_.mul_one] at e
    rw [map_one]; exact e.symm
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_one, map_one] at this
  exact Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans this)

theorem isWt_add {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f + g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_add' _ _ hV', valR_add' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_add]

theorem isWt_sub {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_sub' _ _ hV', valR_sub' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_sub]

theorem isWt_zero (α : Q.X) (V : Y.H.left.Opens) : IsWt Y α V 0 := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_zero', valR_zero', mul_zero]

theorem isWt_sum {α : Q.X} {V : Y.H.left.Opens} {I : Type} (s : Finset I) (f : I → Γ(Y.H.left, V))
    (hf : ∀ i ∈ s, IsWt Y α V (f i)) : IsWt Y α V (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsWt Y α V) (fun _ _ => isWt_add) (isWt_zero α V) hf

theorem isRaynaudTorusWeightFunction_weightZero_mul {α : Q.X} {V : Y.H.left.Opens} {g f : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (hf : IsWt Y α V f) :
    IsWt Y α V (g * f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_zero x x' c hc, Units.val_one, _root_.one_mul]
  ring

theorem isWt_natCast (V : Y.H.left.Opens) (m : ℕ) : IsWt Y 0 V (m : Γ(Y.H.left, V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_natCast' _ _ hV', valR_natCast' _ _ hV, c_zero x x' c hc, Units.val_one, _root_.one_mul]

theorem isWt_constFn (V : Y.H.left.Opens) (r : R) : IsWt Y 0 V (constFn Y.H.hom V r) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  rw [valR_constFn_congr x'.left x.left Y.H.hom V hV' hV ((Over.w x').trans (Over.w x).symm) r,
    c_zero x x' c hc, Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

theorem op_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB i k α f hf
  obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
  have key : ∀ g : Γ(Y.H.left, h.W i), IsWt Y α (h.W i) g → IsWt Y α (h.W i) (h.d i (h.W i) g) := by
    have := hd α V hV.ge
    rw [← hV] at this
    exact this
  have h2 : IsWt Y 0 (h.W i) (2 : Γ(Y.H.left, h.W i)) := by simpa using isWt_natCast (Y := Y) (h.W i) 2
  have hk : IsWt Y 0 (h.W i) (k : Γ(Y.H.left, h.W i)) := isWt_natCast (h.W i) k
  have hk2 : IsWt Y 0 (h.W i) ((k : Γ(Y.H.left, h.W i)) ^ 2) := by rw [sq]; exact isRaynaudTorusWeightFunction_weightZero_mul hk hk
  have hrp : IsWt Y 0 (h.W i) (rsT (h.p i) (h.W i)) := by rw [rsT_self]; exact hp
  have hrp' : IsWt Y 0 (h.W i) (rsT (h.p' i) (h.W i)) := by rw [rsT_self]; exact hp'
  unfold op
  refine isWt_add (isWt_add (isWt_sub ?_ ?_) ?_) ?_
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) (key f hf)
  · exact isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ =>
      isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul h2 (isWt_sum _ _ fun a _ => isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isWt_add (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk2) hrp) (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) hrp')) hf

end GlobalTheory.Heat.WtAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTuple
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

theorem flat_gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧
    (princ B).vecFlat ψ = c • R.ωP i t (z⁻¹, 1) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  classical
  obtain ⟨eg, ea, et, fg, hA, heg, hea, het, hfg, hhA, hflat⟩ := GlobalTheory.T.flatVector_three_steps_conjugate_places D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  have hdisj : Disjoint (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hun : keepPart (R := R) t (B.de.Q ∪ ψ.Q) ∪ flipPart (R := R) t (B.de.Q ∪ ψ.Q) = R.Q t :=
    Finset.filter_union_filter_not_eq _ _
  obtain ⟨gA, hgA, hvP⟩ := _root_.GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition D G Pl0 T0 A Ks R F hC hQG i t hV _ _ hdisj hun eg ea et fg heg hea het hfg
  obtain ⟨zA, cA', hzA, hzA', hcA, hAeq⟩ := _root_.GlobalTheory.PartFlat.flat_eq_unit_smul_om_part D G Pl0 T0 A Ks R F hC hQG i t hV _ (Finset.filter_subset _ _) eg ea fg heg hea hfg
  obtain ⟨zT, cT, -, hzT', hcT, hT⟩ := GlobalTheory.T.flatDatum_liftDatum_same_half_translate_conjugatePlaces D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid eg ea et fg hA heg hea het hfg hhA
  have e1 : hA = cA' • R.ωP i t (zA⁻¹, 1) gA := hAeq hA gA hhA hgA
  have hm := _root_.GlobalTheory.ThetaBaseMove.thAt_move D G Pl0 T0 A Ks R F hC hQG i t hV _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj eg ea et fg gA _ _ zA cA'
    heg hea het hfg hgA hzA hcA.1 hvP
  rw [← e1] at hm
  have e2 := hT _ _ hflat hm
  refine ⟨zA * zT, cT * cA', suppAt_mul' hzA' hzT', GlobalTheory.BigOn.Exp.TupLe.unitOff_mul hcT hcA, ?_⟩
  rw [e2, map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_rev]

end GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.BigOn.Exp.TupLe


end GlobalTheory.BigOn.Exp.TupLe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPeriodsTranslatedBundleTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

theorem GlobalTheory.MumCmp.psi_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ hB D A G _ _ hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw h0
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  obtain ⟨σ, f, hσ0, hE⟩ : ∃ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α),
      (¬ ∀ j, σ.f j = 0) ∧ ∀ e : ℕ, U.ExpandsAt e 1 σ f := by
    obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hS R _ D A G U.toUnifPre 1 le_rfl
    let i₀ : Fin (1 ^ A.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
    have hs : ¬ ∀ j, (b i₀).f j = 0 := fun h0 => by
      obtain ⟨c, -, hc⟩ := hb SecOps.secZero
      have e₁ := hc 0 (fun j => by simp [scal]; rfl)
      have e₂ := hc 1 (fun j => by
        refine (Finset.sum_eq_zero fun i _ => ?_).symm
        obtain rfl : i = i₀ := Fin.ext (by have := i.2; simp only [one_pow] at this; show i.1 = 0; omega)
        rw [h0 j, MulZeroClass.mul_zero])
      exact one_ne_zero (congrFun (e₂.trans e₁.symm) i₀)
    obtain ⟨E, ⟨r, hr, σ, f, hσ, -, hE⟩, -⟩ := (U.expand 1 le_rfl).1 (b i₀)
    refine ⟨σ, f, fun hz0 => hs ?_, hE⟩
    refine GlobalTheory.ThetaScalar.eq_zero_of_sval U.LG.isLB _ fun y J hJ => ?_
    have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hσ (𝟙 _) y hJ
    rw [GlobalTheory.ThetaScalar.sval_eq_zero σ hz0 _ y hJ] at e₁
    have e₃ : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK R) ≫ jK R) r) =
        cst (pullback.snd G.hom (jK R) ≫ jK R) y r :=
      (gs_pull (𝟙 _) (pullback.snd G.hom (jK R) ≫ jK R) y ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    rw [e₃] at e₁
    exact (GlobalTheory.IntegralExpansionLocal.isUnit_cst_of_ne_zero _ y hr).mul_right_eq_zero.1 e₁.symm
  obtain ⟨σ₂, f₂, ν, hν, hE₂, h0σ, hrel⟩ :=
    GlobalTheory.T.translate_integral_thetaExpansion_by_twoTorsion R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw σ f hE
  have hne : ¬ ∀ mu j, (f₂ mu).f j = 0 := fun h0' => hσ0 (h0σ (by
    have H := (GlobalTheory.comb_eq_zero_iff_expansion_comb_eq_zero R _ hR D₂ A₂ G U₂.toUnifPre 1 1 ![1] ![σ₂] ![f₂]
      (fun i => by fin_cases i; exact hE₂)).2 hsa.geomConnected (fun α j => by
        simpa [scal] using h0' α j)
    exact fun j => by simpa [scal] using H j))
  exact GlobalTheory.T.psi_twisted_eq_psi_mul_character_of_point R hB D D₂ g β hβm xe hc w hw h0 f f₂ ν hν
    (GlobalTheory.PsiCompare.levelOneEq_of_expandsAt hG hR U.toUnifPre (U.expand 1 le_rfl) σ f hE)
    (GlobalTheory.PsiCompare.levelOneEq_of_expandsAt hG hR U₂.toUnifPre (U₂.expand 1 le_rfl) σ₂ f₂ hE₂) hne hrel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeOfSectionRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem agree_near_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k k' : ℕ), k₀ ≤ k → ∀ (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x'.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i i' i'' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x').left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i'')).hom (s₀.f i'')) → ∃ W : (thickObj R (maximalIdeal R) e G).left.Opens, y ∈ W ∧ W.ι ≫ x.left = W.ι ≫ x'.left := by

  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₁, hk₁, H₁⟩ := _root_.GlobalTheory.Mum.eq_of_germRatioAgree R hB D A G hG U
  obtain ⟨k₂, -, H₂⟩ := _root_.GlobalTheory.Mum.LocAgree.locAgree R hB D A G hG U
  refine ⟨max k₁ k₂, le_trans hk₁ (le_max_left _ _), ?_⟩
  intro e k k' hk x x' T hx hx' y s₀ i i' i'' hy₁ hy₂ hy₃
  have m₁ : (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₁
  have m₂ : (fstG (maximalIdeal R) e G).left y ∈ secChart U.LG.L i' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₂
  have m₃ : (x'.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i'' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₃
  have u₁ : IsUnit (secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i) := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₁ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₁).1 hy₁)
  have u₂ : IsUnit (secGerm (fstG (maximalIdeal R) e G).left y (T s₀) i') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₂ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₂).1 hy₂)
  have u₃ : IsUnit (secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₃ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₃).1 hy₃)
  have hA : GermRatioAgree (x.left ≫ (fstG (maximalIdeal R) e G).left)
      (x'.left ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' y := by
    refine ⟨m₁, m₃, u₁, u₃, fun s₁ => ?_⟩
    have e₁ := secRatioEq_iff_germ.1 (hx s₁ s₀) y i i' m₁ m₂
    have e₂ := secRatioEq_iff_germ.1 (hx' s₁ s₀) y i'' i' m₃ m₂
    apply (u₂.mul_left_inj).1
    linear_combination secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'' * e₁ -
      secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i * e₂
  have hb : x.left ≫ (thickObj R (maximalIdeal R) e G).hom = x'.left ≫ (thickObj R (maximalIdeal R) e G).hom := by
    rw [Over.w x, Over.w x']
  have hk₁' : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk₂' : k₂ ≤ k := le_trans (le_max_right _ _) hk
  exact H₂ e k hk₂' _ x.left x'.left hb s₀ i i'' y hA (H₁ e k hk₁' _ x.left x'.left hb s₀ i i'' y hA)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRay

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv_mem mkT tv_mkT tanM_ext tv_add tv_smul)

theorem tanBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ∀ a, b a = v' a := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  have hc : IsAdicComplete ((maximalIdeal R).map (algebraMap R (DualNumber R))) (DualNumber R) := by
    have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
    exact GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (maximalIdeal R) (overAt (𝟙 (Sp R)) (DualNumber R)) := by
    refine GlobalTheory.AdicColimit.IsAdicColimit.of_iso (Over.isoMk (Iso.refl _) ?_)
      (GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing R (maximalIdeal R) (DualNumber R)
        (algebraMap R (DualNumber R)) hc)
    simp
  have hΦ := Y.rep
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusModel.exists_mulEquiv P.U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hΦ
  have nat : ∀ (k : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ overAt (𝟙 (Sp R)) (DualNumber R))
      (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H), J _ hT (k ≫ w) = k ≫ J _ hT w := fun k w =>
    (hJ _ hT _ _).2 (((hJ _ hT w _).1 rfl).pull k (hΦ.1 _ _ k _))
  have hs : ∀ (a : R) (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H),
      J _ hT (smT (𝟙 (Sp R)) a w) = smT (𝟙 (Sp R)) a (J _ hT w) := fun a w => nat _ w
  have mem : ∀ v : TanM (𝟙 (Sp R)) Y.H, smT (𝟙 (Sp R)) 0 (J _ hT (tv v)) = 1 := fun v => by
    rw [← hs, tv_mem, map_one]
  let L : TanM (𝟙 (Sp R)) Y.H →ₗ[R] TanM (𝟙 (Sp R)) t.G :=
    { toFun := fun v => mkT (J _ hT (tv v)) (mem v)
      map_add' := fun u v => tanM_ext (by
        simp only [tv_mkT, tv_add, map_mul])
      map_smul' := fun a v => tanM_ext (by
        simp only [tv_mkT, tv_smul, RingHom.id_apply, hs]) }
  have hL : Function.Bijective L := by
    refine ⟨fun u v h => tanM_ext ((J _ hT).injective ?_), fun w => ?_⟩
    · have := congrArg tv h
      simpa [L, tv_mkT] using this
    · have h0 : smT (𝟙 (Sp R)) 0 ((J _ hT).symm (tv w)) = 1 := by
        apply (J _ hT).injective
        rw [hs, MulEquiv.apply_symm_apply, tv_mem, map_one]
      refine ⟨mkT _ h0, tanM_ext ?_⟩
      show J _ hT ((J _ hT).symm (tv w)) = tv w
      exact MulEquiv.apply_symm_apply _ _
  refine ⟨vH.map (LinearEquiv.ofBijective L hL), fun a => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply]
  refine tanM_ext ?_
  exact (hJ _ hT _ _).2 (hv a)

end GlobalTheory.TanRay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldsEqOnSubopensOfEqAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

theorem isField_eq_basicOpen {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    {d₁ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (h₁ : IsField V d₁) (h₂ : IsField V d₂)
    (h : ∀ a, d₁ V a = d₂ V a) (s : Γ(Z, V)) (g : Γ(Z, Z.basicOpen s)) :
    d₁ (Z.basicOpen s) g = d₂ (Z.basicOpen s) g := by
  have hle : Z.basicOpen s ≤ V := Z.basicOpen_le s
  haveI := hV.isLocalization_basicOpen s
  have halg : ∀ x, algebraMap Γ(Z, V) Γ(Z, Z.basicOpen s) x = resG Z hle x := fun _ => rfl

  have hres : ∀ x : Γ(Z, V), d₁ _ (resG Z hle x) = d₂ _ (resG Z hle x) := by
    intro x
    rw [h₁.2.2 V _ hle le_rfl, h₂.2.2 V _ hle le_rfl, h]
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) g
  simp only [halg] at hm
  have hu : IsUnit (resG Z hle (m : Γ(Z, V))) := by
    rw [← halg]; exact IsLocalization.map_units _ m
  have e₁ := congrArg (d₁ _) hm
  have e₂ := congrArg (d₂ _) hm
  rw [h₁.2.1 _ hle] at e₁
  rw [h₂.2.1 _ hle] at e₂
  have key : resG Z hle (m : Γ(Z, V)) * (d₁ _ g - d₂ _ g) = 0 := by
    rw [hres m] at e₁
    rw [hres a] at e₁
    linear_combination e₁ - e₂
  exact sub_eq_zero.mp ((hu.mul_right_eq_zero).mp key)

theorem isField_eq_of_affine : ∀ (Z : Scheme.{0}) (V : Z.Opens), IsAffineOpen V → ∀ (d₁ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField V d₁ → IsField V d₂ → (∀ a, d₁ V a = d₂ V a) → ∀ O : Z.Opens, O ≤ V → ∀ f, d₁ O f = d₂ O f := by
  intro Z V hV d₁ d₂ h₁ h₂ h O hO f
  refine TopCat.Presheaf.section_ext Z.sheaf O _ _ fun x hx => ?_
  obtain ⟨r, hrO, hxr⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ (hO hx)
  have e₁ := h₁.2.2 O _ hrO hO f
  have e₂ := h₂.2.2 O _ hrO hO f
  have e := isField_eq_basicOpen hV h₁ h₂ h r (resG Z hrO f)
  rw [e₁, e₂] at e
  have g₁ := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hrO) x hxr (d₁ O f)
  have g₂ := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hrO) x hxr (d₂ O f)
  exact g₁.symm.trans ((congrArg _ e).trans g₂)

end GlobalTheory.LogKS
end

