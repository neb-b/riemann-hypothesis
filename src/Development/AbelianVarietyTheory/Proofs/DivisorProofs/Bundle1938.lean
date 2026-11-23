module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem qLevel_of_torsion_labels : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hI
  intro g k hk ζ pt hζ hadd hinj hsurj hw
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.ZH.uTors_closed V hV A G D U C k hk
  obtain ⟨-, -, hAdd, -, hQ⟩ := GlobalTheory.Ex.GtValues.points_correspond V D.toPre D.psi_even D.tau_bimult C N ν
  have hWp := GlobalTheory.WeilValues.weil_eq_values GlobalTheory.Ex.GtValues.points_correspond
    (GlobalTheory.Ex.brFam GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2) V D.toPre D.psi_even D.tau_bimult C N ν k hk
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ k

  have hmul : ∀ (p₁ p₂ p₃ : QkPt D.toPre C k) (q₁ q₂ : N.QT k), ν.QPt p₁ q₁ → ν.QPt p₂ q₂ → ν.QPt p₃ (q₁ * q₂) →
      f p₃ = f p₁ * f p₂ := by
    intro p₁ p₂ p₃ q₁ q₂ h₁ h₂ h₃
    apply hf4
    refine ⟨p₃, ?_, ?_, ?_⟩
    · rw [← h₃.1, ← h₁.1, ← h₂.1]
      exact map_add ν.eX _ _
    · exact (hAdd _ _ _ _ _ _ h₁.2 h₂.2 h₃.2).2 rfl
    · exact (hQ3 p₃ p₃ _ _ h₃ h₃).2 (by exact ⟨0, by simp, by simp⟩)

  have hpt0 : pt 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hptn : ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
    intro n a
    induction n with
    | zero => simpa using hpt0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hkt : ∀ a, pt a ^ k = 1 := by
    intro a
    have : k • a = 0 := by
      funext i
      simp [nsmul_eq_mul]
    rw [← hptn, this, hpt0]
  have hex : ∀ a, ∃ p, f p = pt a := fun a => hf2 (pt a) (hkt a)
  choose p hp using hex
  have hexq : ∀ a, ∃ q, ν.QPt (p a) q := fun a => (hQ1 (p a)).exists
  choose q hq using hexq

  have hpow : ∀ (q' : N.QT k) (p' : QkPt D.toPre C k), ν.QPt p' q' → ∀ (n : ℕ) (pn : QkPt D.toPre C k),
      ν.QPt pn (q' ^ n) → f pn = f p' ^ n := by
    intro q' p' hp' n
    induction n with
    | zero =>
      intro pn hpn
      rw [pow_zero] at hpn ⊢
      have h := hmul pn pn pn 1 1 hpn hpn (by rw [_root_.mul_one]; exact hpn)
      exact (mul_eq_left.1 h.symm)
    | succ n ih =>
      intro pn hpn
      obtain ⟨pm, hpm⟩ := hQ2 (q' ^ n)
      rw [pow_succ] at hpn
      rw [hmul pm p' pn _ _ hpm hp' hpn, ih pm hpm, pow_succ]
  have hqk : ∀ q' : N.QT k, q' ^ k = N.qTriv k (Multiplicative.toAdd q'.1.1) := by
    intro q'
    apply Subtype.ext
    apply Prod.ext
    · show q'.1.1 ^ k = Multiplicative.ofAdd (k • Multiplicative.toAdd q'.1.1)
      rw [ofAdd_nsmul, ofAdd_toAdd]
    · show q'.1.2 ^ k = N.io (Multiplicative.toAdd q'.1.1)
      exact (N.mem_QT).1 q'.2
  refine ⟨p, q, ⟨hζ, ?_, ?_, ?_, ?_⟩, fun a => ⟨hq a, (hf1 _ _).2 (hp a).symm⟩⟩
  · intro a b
    obtain ⟨p'', hp''⟩ := hQ2 (q a * q b)
    have h : f p'' = f (p (a + b)) := by rw [hmul _ _ _ _ _ (hq a) (hq b) hp'', hp, hp, hp, hadd]
    exact (hQ3 _ _ _ _ hp'' (hq (a + b))).1 ((hf3 _ _).1 h)
  · intro a b h
    apply hinj
    rw [← hp, ← hp]
    exact (hf3 _ _).2 ((hQ3 _ _ _ _ (hq a) (hq b)).2 h)
  · intro q'
    obtain ⟨p', hp'⟩ := hQ2 q'
    obtain ⟨p₀, hp₀⟩ := hQ2 1
    obtain ⟨pk, hpk⟩ := hQ2 (q' ^ k)
    have h0 := hpow q' p' hp' 0 p₀ (by rw [pow_zero]; exact hp₀)
    have hk' := hpow q' p' hp' k pk hpk
    have heq : N.QEq 1 (q' ^ k) := (N.qEq_iff _ _).2 ⟨_, by rw [_root_.one_mul]; exact hqk q'⟩
    have h1 : f p₀ = f pk := (hf3 _ _).2 ((hQ3 _ _ _ _ hp₀ hpk).2 heq)
    have htor : f p' ^ k = 1 := by rw [← hk', ← h1, h0, pow_zero]
    obtain ⟨a, ha⟩ := hsurj (f p') htor
    refine ⟨a, (hQ3 _ _ _ _ (hq a) hp').1 ((hf3 _ _).1 ?_)⟩
    rw [hp, ha]
  · intro i j
    have h := hw i j
    rw [← hp, ← hp] at h
    have h' := (hf5 _ _ (ζ ^ stdSymp g i j)).2 h
    exact Units.ext ((hWp _ _ _ _ _ (hq _) (hq _)).1 h').symm

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtDualNumberTermValueSmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.JcSmul

theorem valR_const_mul {F A : Type} [Field F] [CommRing A] [Algebra F A] {Y : Scheme.{0}} (r : Sp A ⟶ Y)
    (π : Y ⟶ Sp F) (h : r ≫ π = spMap (algebraMap F A)) (U : Y.Opens) (z : F) (f : Γ(Y, U)) :
    valR r U (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) * f) =
      algebraMap F A z * valR r U f := by
  unfold valR
  by_cases hU : ⊤ ≤ r ⁻¹ᵁ U
  · rw [dite_eq_left hU, dite_eq_left hU, map_mul, map_mul]
    congr 1
    have e : (r.appLE U ⊤ hU).hom (resTop U (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z))) =
        (r ≫ π).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
      simp only [resTop]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop,
        CommRingCat.hom_comp, RingHom.comp_apply]
      exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Sp A, ⊤) => g.hom (π.appTop.hom _)) (Scheme.Hom.appLE_eq_app r (U := ⊤))
    rw [e, h]
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F A))
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z)) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  · rw [dite_eq_right hU, dite_eq_right hU, mul_zero]

theorem jc_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := by
  intro R _ _ D F _ _ N ν k s a gm α
  have e : (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ≫
      (fst (TF (R := R) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) := by
    rw [← Over.comp_left, lift_fst]
    rfl
  unfold jc sE
  rw [← _root_.mul_assoc]
  congr 1
  have h2 : (TrivSqZeroExt.inl a : DualNumber F) = algebraMap F (DualNumber F) a := rfl
  rw [h2]
  exact valR_const_mul _ _ e _ a _

end GlobalTheory.JcSmul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionCharacterValueConstantTermOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section
namespace GlobalTheory.MBLow.Cl

theorem fst_vE_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  intro R _ _ D _ N ν gm ⟨o, hz, hp⟩ χ
  have hJ : Good D.P.L (IsLocalRing.closedPoint ℂ) ν.J := fun ψ => ν.good ψ trivial
  have hm : redE ℂ (IsLocalRing.closedPoint ℂ) ∈ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    simpa only [Category.id_comp] using hJ.mem (DegPre.gtφT D (TE R ℂ) gm.b χ) (redE ℂ)
  have h : ⊤ ≤ (𝟙 (Sp (DualNumber ℂ))) ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    refine (GlobalTheory.KS.TangentAt.top_le_iff_dual _ _).2 ((GlobalTheory.ZH.CrdCalc.top_le_iff _ _).2 ?_)
    rw [Category.comp_id]
    exact hm
  have e1 : valR (redE ℂ ≫ 𝟙 (Sp (DualNumber ℂ))) (LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)))
      ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val = (vE (gm.s χ) (𝟙 _) ν.J).fst :=
    (GlobalTheory.ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _) _ h).2 _
  rw [Category.comp_id] at e1
  have e2 := GlobalTheory.ZH.ThetaData.valR_eq_gs (redE ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val
  have e3 := gs_unit (redE ℂ) (IsLocalRing.closedPoint ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k))
  have e4 := val_of (gm.s χ) (redE ℂ) (IsLocalRing.closedPoint ℂ) ν.J
    (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) (fun k => by rw [Category.id_comp])
  have v1 := val_pull hJ (gm.s χ) (redE ℂ) (𝟙 _)
  rw [Category.id_comp] at v1
  have v2 := (val_corr hJ (hp.2 χ) (𝟙 _)).symm.trans ((val_corr hJ (hz.2 χ) (𝟙 _)).trans (val_one _))
  rw [v1] at v2
  refine e1.symm.trans (e2.trans ?_)
  rw [e3, ← e4, v2, Units.val_one, map_one]

end GlobalTheory.MBLow.Cl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionDualCharValuesMulCube
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.DualMult

theorem redE_closedPoint :
    (redE ℂ) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint (DualNumber ℂ) := by
  have hl : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  exact Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)

variable {X : Scheme.{0}} {L : LB X}

theorem good_dual (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) :
    Good L (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ)) := by
  intro ψ
  have h := hJ (redE ℂ ≫ ψ) (x := IsLocalRing.closedPoint ℂ) trivial
  change ψ ((redE ℂ) (IsLocalRing.closedPoint ℂ)) ∈ L.U (J (redE ℂ ≫ ψ)) at h
  rwa [redE_closedPoint] at h

theorem vE_eq_val (J : (Sp ℂ ⟶ X) → L.ι) (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {K : Type} [Fintype K]
    {φ : K → (Sp (DualNumber ℂ) ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) :
    vE t (𝟙 _) J = (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom
      (val t (𝟙 _) (IsLocalRing.closedPoint (DualNumber ℂ) : Sp (DualNumber ℂ)) (fun ψ => J (redE ℂ ≫ ψ))).val := by
  have hm := (good_dual J hJ).mem φ (𝟙 _)
  unfold vE val
  exact (GlobalTheory.ZH.ThetaData.valR_eq_gs _ _ hm _).trans (congrArg _ (gs_unit _ _ _ hm _))

end GlobalTheory.DualMult

namespace GlobalTheory.DualMult
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

theorem mult_vE (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X) :
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  have hJ := good_dual (L := D.P.L) ν.J ν.good
  have e := val_corr hJ (gm.mult χ χ') (𝟙 _)
  replace e := (val_mul hJ _ _ _).symm.trans (e.trans (val_mul hJ _ _ _))
  refine (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).trans
    (Eq.trans ?_ (congrArg₂ (· * ·) (vE_eq_val ν.J ν.good _) (vE_eq_val ν.J ν.good _)).symm)
  rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul]
  exact congrArg (fun u => (stalkClosedPointIso (CommRingCat.of (DualNumber ℂ))).hom.hom (Units.val u)) e

end GlobalTheory.DualMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitGenericPointMemCompactFlagSpaceOpenPart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenTrait

theorem mem_of_dense_of_forall_specializes {X : Scheme.{0}} [IsLocallyNoetherian X] {U : X.Opens}
    (hU : Dense (U : Set X)) {z : X} (hz : ∀ ξ : X, ξ ⤳ z → ξ = z) : z ∈ U := by
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  have : IsAffine V := hV
  have : IsNoetherian V.toScheme := {}
  have : NoetherianSpace V.toScheme := inferInstance
  let z' : V.toScheme := ⟨z, hzV⟩
  have hC := irreducibleComponent_mem_irreducibleComponents z'
  obtain ⟨o, ho, ⟨u, huo⟩, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hoX : IsOpen (V.ι '' o) := V.ι.isOpenEmbedding.isOpenMap o ho
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwU⟩ := hU.inter_open_nonempty _ hoX ⟨_, u, huo, rfl⟩
  have h1 : V.ι hC.1.genericPoint ⤳ V.ι w := (hg.specializes (hoC hwo)).map V.ι.continuous
  have h2 : V.ι hC.1.genericPoint ⤳ V.ι z' := (hg.specializes mem_irreducibleComponent).map V.ι.continuous
  have h3 : V.ι z' = z := rfl
  rw [h3] at h2
  rw [← hz _ h2]
  exact h1.mem_open U.isOpen hwU

end GlobalTheory.GenTrait

namespace GlobalTheory.GenTrait

theorem isLocallyNoetherian_flag {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) :
    IsLocallyNoetherian TF.X.YY := by
  have := TF.smooth
  have : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have := TF.X.proper
  exact LocallyOfFiniteType.isLocallyNoetherian (TF.X.π ≫ TF.Y.s)

theorem top_le_preimage_flagOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z) (K : Type) [Field K] (g : (Y₀ TF.X Z).presheaf.stalk y →+* K), Function.Injective g → ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by
  intro E _ _ _ H Dw l Xo c TF Z y K _ g hg p _
  have := isLocallyNoetherian_flag TF
  let q := Spec.map (CommRingCat.ofHom g) p
  have hq0 : q.asIdeal = ⊥ := by
    have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime
    change Ideal.comap g p.asIdeal = ⊥
    rw [hp, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot g).1 hg
  have hq : ∀ q' : Spec ((Y₀ TF.X Z).presheaf.stalk y), q' ⤳ q → q' = q := fun q' h =>
    PrimeSpectrum.ext (le_antisymm ((show q'.asIdeal ≤ q.asIdeal from (PrimeSpectrum.le_iff_specializes _ _).2 h)) (hq0.le.trans bot_le))
  change ((Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) p) ∈ flagOpen TF.X
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  refine mem_of_dense_of_forall_specializes (dense_flagOpen TF.X) fun ξ hξ => ?_
  have hy : (Y₀ TF.X Z).fromSpecStalk y q ⤳ y := by
    have : (Y₀ TF.X Z).fromSpecStalk y q ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hmem : ξ ∈ Set.range (inc₀ TF.X Z) := by
    rw [Scheme.Opens.range_ι]
    refine hξ.mem_open (TopologicalSpace.Opens.isOpen _) ?_
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨ξ₀, rfl⟩ := hmem
  have h₀ : ξ₀ ⤳ (Y₀ TF.X Z).fromSpecStalk y q := (inc₀ TF.X Z).isEmbedding.specializes_iff.1 hξ
  obtain ⟨q', rfl⟩ : ξ₀ ∈ Set.range ((Y₀ TF.X Z).fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]; exact h₀.trans hy
  rw [hq q' (((Y₀ TF.X Z).fromSpecStalk y).isEmbedding.specializes_iff.1 h₀)]

end GlobalTheory.GenTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trF_dualPoint_of_isPull : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  intro V _ _ D C _ _ gm₀ gm hp mu
  have hsq : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    simp only [epsR, TE, TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hsq
  have hb : gm.b = k ≫ gm₀.b := by
    ext1
    simpa [k] using hp.1
  set e : TE V C ⟶ TF (R := V) C := Over.homMk (spMap (algebraMap C (DualNumber C))) rfl with he
  refine ⟨?_, Over.w _, ?_⟩
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ DegPre.prB D C = k ≫ padd D.P.A gm₀.b (toUnit _ ≫ D.c mu) := by
      simp only [DegPre.trF, DegPre.prB, lift_snd, padd, comp_lift_assoc, comp_lift, hb, Category.assoc, comp_toUnit_assoc]
    have h2 := congrArg CommaMorphism.left h1
    simpa [k] using h2
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ fst _ _ = e := by
      simp [DegPre.trF]
    have h2 := congrArg CommaMorphism.left h1
    simpa [he] using h2

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquiv
section
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory

theorem transport_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem transport_minimisers : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  intro O _ X Y _ _ _ _ n N _ ebX ebY f μ hμ
  let A : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebY.toLinearMap ∘ₗ f.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebX.symm.toLinearMap
  let B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebX.toLinearMap ∘ₗ f.symm.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebY.symm.toLinearMap
  have hA : ∀ x, A x = ebY (f (ebX.symm x)) := fun x => rfl
  have hB : ∀ x, B x = ebX (f.symm (ebY.symm x)) := fun x => rfl
  have hBA : ∀ x, B (A x) = x := fun x => by simp [hA, hB]
  have hAB : ∀ x, A (B x) = x := fun x => by simp [hA, hB]
  have key : ∀ (F G : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)), (∀ x, G (F x) = x) → ∀ c i,
      ((G (ebY (μ (fun i => ((F (ebY (μ c)) i : ℤ) : ZMod N)))) i : ℤ) : ZMod N) = c i := by
    intro F G hGF c i
    rw [transport_cong G _ (F (ebY (μ c))) (fun j => hμ _ j) i, hGF, hμ]
  let σ : Equiv.Perm (Fin n → ZMod N) :=
    { toFun := fun c i => ((A (ebY (μ c)) i : ℤ) : ZMod N)
      invFun := fun c i => ((B (ebY (μ c)) i : ℤ) : ZMod N)
      left_inv := fun c => by funext i; exact key A B hBA c i
      right_inv := fun c => by funext i; exact key B A hAB c i }
  refine ⟨σ, fun c i => ?_, ?_⟩
  · have := key A B hBA c i
    rw [hB, LinearEquiv.symm_apply_apply] at this
    exact this
  · intro b hmin c α hα
    simp only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply hmin (σ c) (f α)
    intro i
    have h1 : ebY (f α) = A (ebX α) := by rw [hA, LinearEquiv.symm_apply_apply]
    rw [h1]
    exact transport_cong A (ebX α) (ebY (μ c)) (fun j => (hα j).trans (hμ c j).symm) i

end GlobalTheory
end

