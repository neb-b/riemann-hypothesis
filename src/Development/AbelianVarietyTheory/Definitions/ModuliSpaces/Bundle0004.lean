module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.Inhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def trivTriple (H : Host E) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (a : OAct (𝓞 E) G) : SAB H S where
  G := G
  semi := hG
  act := a
  PP := UU.trivRig G
  cub := UU.trivCub G
  sym := PrimNorm.isSymmetric_of_hasGen _ ⟨UU.unitGen _ _, UU.unitGen_isGen _ _⟩
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (fun _ _ => rfl))⟩

def zeroTriple (H : Host E) (S : Scheme.{0}) : SAB H S :=
  trivTriple H (𝟙_ (Over S)) (isSemiAbelian_of_isAbelianScheme _ (UU.isAbelianScheme_unit S))
    ⟨fun _ => 𝟙 _, fun _ => inferInstance, rfl, fun _ _ => toUnit_unique _ _, fun _ _ => toUnit_unique _ _⟩

theorem isProper_zeroTriple (S : Scheme.{0}) : IsProper (zeroTriple H S).G.hom :=
  (UU.isAbelianScheme_unit S).proper

theorem abLocus_eq_univ {S : Scheme.{0}} (G : Over S) (h : IsProper G.hom) : abLocus G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance

theorem abOpen_and_splitFib {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : AbOpen t.G ∧ SplitFib t.G := by
  refine ⟨⟨⊤, (abLocus_eq_univ _ h).symm, inferInstance⟩, fun x => ?_⟩
  exact ⟨S.residueField x, inferInstance, Algebra.id _, inferInstance, inferInstance, _,
    ZJ.isGt_splitExtOfAbelian _ (isAbelianScheme_pullback_obj _ t.G ⟨t.semi.comm, t.semi.smooth, h, t.semi.geomConnected⟩)⟩

theorem good_zeroTriple (S : Scheme.{0}) : Good (zeroTriple H S) := by
  obtain ⟨h₁, h₂⟩ := abOpen_and_splitFib (zeroTriple H S) (isProper_zeroTriple S)
  refine ⟨h₁, h₂, fun x => ⟨⊤, trivial, fun _ => 1, fun i j => ?_, fun y _ => ⟨y, PUnit.unit, rfl, ?_⟩⟩⟩
  · exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · rw [Scheme.basicOpen_one]
    exact ⟨trivial, trivial⟩

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

section General

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

end General

section Above

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

end Above

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  have := ProjSpace.Model.isIso_str_zero (R := R)
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def RZ.rt (H : Host E) (S A : ℕ) : RZ H S A :=
  2 * ⟨(1 + H.rt0) / 2, Subring.subset_closure (Or.inl rfl)⟩ - 1

def RZ.ze (H : Host E) (S A : ℕ) : RZ H S A := ⟨zeta A, Subring.subset_closure (Or.inr (Or.inr rfl))⟩

structure FullObj (D : Datum H) {n N : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (RZ H n N)) (t : SAB H S)
    (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) : Prop where
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L
  add : ∀ a c, lev (a + c) = lev a * lev c
  ker : ∀ a, lev (N • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : RZ H n N →+* k), x ≫ s = spMap β →
    DetCond D t.act x (β (RZ.rt H n N)) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      (I.ζ N : k) = β (RZ.ze H n N) ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a

structure FamCore (D : Datum H) {n N : ℕ} {MM : Scheme.{0}} (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM)
    (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) : Prop where
  red : IsReduced MM
  flat : Flat sM
  qproj : IsQProjOver sM
  gen : Smooth (pullback.snd sM (spMap (algebraMap (RZ H n N) (FractionRing (RZ H n N)))))
  obj : FullObj D sM tM lev
  rep : ∀ (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)),
    IsReduced S → IsLocallyNoetherian S → Flat s → FullObj D s t lv →
    ∃! f : S ⟶ MM, f ≫ sM = s ∧ ∃ ν : SABMap t tM f, ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ MM) (t : SAB H (Sp (DualNumber k)))
    (lv : D.La → (𝟙_ (Over (Sp (DualNumber k))) ⟶ t.G)) (ν : SABMap t tM x) (ν' : SABMap t tM (constPt x)),
    x ≫ sM = constPt x ≫ sM → (∀ a, (lv a).left ≫ ν.φ = x ≫ (lev a).left) →
    (∀ a, (lv a).left ≫ ν'.φ = constPt x ≫ (lev a).left) → x = constPt x

def SiegClause (D : Datum H) {n N : ℕ} {MM : Scheme.{0}} (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM)
    (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ n → ∃ (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N)
    (bas : (Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) ⊕ Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤ) ≃ₗ[ℤ] D.La),
    (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) ∧
    ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p N →+* O) (b : RZ H n N →+* O), Function.Injective i →
      IsInc (ZP p N).subtype i z → IsInc (RZ H n N).subtype i b →
      ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ MM) (tT : SAB H T) (ν : SABMap tT tM f)
        (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsPullback f sT sM (spMap b) →
        (∀ x, (levT x).left ≫ ν.φ = f ≫ (lev x).left) →
        ∃ w : T ⟶ pullback Ag.s (spMap z), SiegData sT tT levT Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w

def SiegRep {h p N : ℕ} (Ag : SiegelFamily h p N) : Prop :=
  IsQProjOver Ag.s ∧ ∀ (S : Scheme.{0}) (s : S ⟶ Sp (ZP p N)) (o : SiegPre h N (zetaZP p N) s),
    IsReduced S → IsLocallyNoetherian S → Flat s → o.Principal → ∃! f : S ⟶ Ag.X, f ≫ Ag.s = s ∧ SiegPB o Ag.univ f

structure ZOn {O : Type} [CommRing O] {MM : Scheme.{0}} (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ) where
  Z : Scheme.{0}
  s : Z ⟶ Sp O
  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z
  proj : IsProjOver s
  flat : Flat s
  t : SAB H Z
  qproj : IsQProjOver (t.G.hom ≫ s)
  good : Good t
  W : MM.Opens
  dense : Dense (W : Set MM)
  j : W.toScheme ⟶ Z
  j_open : IsOpenImmersion j
  j_dom : IsDominant j
  j_over : j ≫ s = W.ι ≫ sM
  tW : SAB H W.toScheme
  m₁ : SABMap tW tM W.ι
  m₂ : SABMap tW t j
  amp : GlobalTheory.LN.AmpFrames t.G t.PP.L (m ^ 2)

def TopAmpExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (Xo : ∀ l : Level H, Moduli D l) (n : ℕ), AuxiliaryInertOddPrime H n →
      ∃ (J k : ℕ) (T : Top Xo n (n ^ J)), 1 ≤ J ∧ Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2))

end GlobalTheory.Models

end
end

