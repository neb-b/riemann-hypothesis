module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0207

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanAdd

section General

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem corr_mul {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (ρ : (Over.map (thick R I e)).obj T' ⟶ T) (x x' : T' ⟶ thickObj R I e G) (p p' p'' : GtPt D T)
    (h : GtPt.IsAdd p p' p'') (hb : TorusCoord.im g x = ρ ≫ p.b) (hb' : TorusCoord.im g x' = ρ ≫ p'.b) (χ : D.X)
    (hs : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x.left) (LB.pullGen D.P.L _ _ (p.s χ) ρ.left))
    (hs' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x'.left) (LB.pullGen D.P.L _ _ (p'.s χ) ρ.left)) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left) (LB.pullGen D.P.L _ _ (p''.s χ) ρ.left) := by
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have k := TorusCoord.val_t_mul_points g GlobalTheory.globalFns_holds χ x x' z J hJ
  have a := val_corr hJ (h.2 χ) ρ.left
  have a₁ := (val_mul hJ _ _ _).symm.trans (a.trans (val_mul hJ _ _ _))
  have c : val (DegPre.cubAtT D T (DegPre.cT D T χ) p.b p'.b) ρ.left z J = TorusCoord.cubeVal g χ z J x x' := by
    refine (val_cub D.cub ρ hJ _ _ _).trans ?_
    unfold TorusCoord.cubeVal
    rw [hb, hb']
    congr 1
    simp
  have s := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs (𝟙 _))).trans (val_pull hJ _ _ _)
  have s' := ((val_pull hJ _ _ _).symm.trans (val_corr hJ hs' (𝟙 _))).trans (val_pull hJ _ _ _)
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  simp only [Category.id_comp] at s s' ⊢
  refine mul_right_cancel (k.trans ?_)
  exact ((congrArg₂ (· * ·) s s').trans a₁.symm).trans (congrArg (_ * ·) c)

theorem fst_mul {T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T' ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).map (x * x') ≫ fstG I e G =
      ((Over.map (thick R I e)).map x ≫ fstG I e G) * ((Over.map (thick R I e)).map x' ≫ fstG I e G) :=
  map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T') x x'

end General

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_over {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ (epsR A).hom = (epsR B).hom ≫ spMap f := by
  change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_scale {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : A) :
    spMap (epsScaleR (f c)) ≫ spMap (dualMap f) = spMap (dualMap f) ≫ spMap (epsScaleR c) := by
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap, epsScaleR, mul_comm]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem tanRel_mul (y y' : epsR R ⟶ G) (gm gm' gm'' : GtPt D.toPre (epsR R)) (h : TanRel U y gm) (h' : TanRel U y' gm')
    (ha : GtPt.IsAdd gm gm' gm'') : TanRel U (y * y') gm'' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  obtain ⟨ye', h₁', h₂', h₃'⟩ := h' e
  have hci : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hw := dual_over (Ideal.Quotient.mk (I ^ (e + 1)))
  let ρ : (Over.map (thick R I e)).obj (epsR (R ⧸ I ^ (e + 1))) ⟶ epsR R :=
    Over.homMk (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))) hw
  have key : ∀ (w : epsR R ⟶ G) (we : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      we ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ w.left →
      we ≫ (thickObj R I e G).hom = (epsR (R ⧸ I ^ (e + 1))).hom := by
    intro w we hh
    have h0 := congrArg (· ≫ G.hom) hh
    simp only [Category.assoc, Over.w] at h0
    rw [← cancel_mono (thick R I e), Category.assoc]
    exact h0.trans hw
  let x : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye (key y ye h₁)
  let x' : epsR (R ⧸ I ^ (e + 1)) ⟶ thickObj R I e G := Over.homMk ye' (key y' ye' h₁')
  have f : (Over.map (thick R I e)).map x ≫ fstG I e G = ρ ≫ y := Over.OverMorphism.ext h₁
  have f' : (Over.map (thick R I e)).map x' ≫ fstG I e G = ρ ≫ y' := Over.OverMorphism.ext h₁'
  have b : TorusCoord.im (U.gt e) x = ρ ≫ gm.b := Over.OverMorphism.ext h₂
  have b' : TorusCoord.im (U.gt e) x' = ρ ≫ gm'.b := Over.OverMorphism.ext h₂'
  refine ⟨(x * x').left, ?_, ?_, fun χ => corr_mul (U.gt e) ρ x x' gm gm' gm'' ha b b' χ (h₃ χ) (h₃' χ)⟩
  · have := fst_mul x x'
    rw [f, f', ← MonObj.comp_mul] at this
    exact congrArg (·.left) this
  · have := TorusCoord.im_mul (U.gt e) x x'
    rw [b, b', ← MonObj.comp_mul] at this
    rw [ha.1]
    exact congrArg (·.left) this

theorem tanRel_scale (c : R) (y : epsR R ⟶ G) (gm gm' : GtPt D.toPre (epsR R)) (h : TanRel U y gm)
    (hp : GtPt.IsPull (epsScale R c).left gm gm') : TanRel U (epsScale R c ≫ y) gm' := by
  intro e
  obtain ⟨ye, h₁, h₂, h₃⟩ := h e
  have hc : spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsScale R c).left := dual_scale _ c
  refine ⟨spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c)) ≫ ye, ?_, ?_, fun χ => ?_⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.left) hc).trans (Category.assoc _ _ _))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ gm.b.left) hc).trans ((Category.assoc _ _ _).trans ?_))
    exact congrArg (_ ≫ ·) hp.1.symm
  · refine corr_of_val D.toPre.P.isLB fun z J hJ => ?_
    have s := ((val_pull hJ _ _ _).symm.trans
      (val_corr hJ (h₃ χ) (spMap (epsScaleR (Ideal.Quotient.mk (I ^ (e + 1)) c))))).trans (val_pull hJ _ _ _)
    have t := (val_corr hJ (hp.2 χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))))).trans (val_pull hJ _ _ _)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    simp only [Category.id_comp]
    exact s.trans ((congrArg (fun q => val (gm.s χ) q z J) hc).trans t.symm)

end GlobalTheory.MBLow.TanAdd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanLift

theorem isLocalRing_dualNumber (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem dualMap_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ (epsR R).hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem redE_over (R : Type) [CommRing R] : redE R ≫ (epsR R).hom = 𝟙 _ := by
  show spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 2

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R]
  {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem exists_tan (U : UnifPre I D A G) (y : epsR R ⟶ G) (hy : IsTangent y) :
    ∃ gm : GtPt D.toPre (epsR R), TanRel U y gm ∧ GtTan gm ∧ IsTangent gm.b := by
  have hL := D.toPre.P.isLB
  have := isLocalRing_dualNumber R
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := isAdicComplete_map_of_finite I (DualNumber R)
  obtain ⟨g, hg⟩ := IntegralGt.exists_gtPt U (φ := algebraMap R (DualNumber R)) y
  have hz := fun e => hg e _ (thick R I e ≫ redE R) (eSec (thickObj R I e G))
    ((UnitValue.eSec_fGl (G := G) e).trans ((congrArg (thick R I e ≫ ·) hy.symm).trans (Category.assoc _ _ _).symm))
  have hb : redE R ≫ g.b.left = η[D.toPre.P.A].left := hom_ext_of_isHausdorff I fun e =>
    (Category.assoc _ _ _).symm.trans ((hz e).1.symm.trans (UnitValue.eSec_pGl U e))
  refine ⟨g, fun e => ?_, ?_, hb⟩
  · have w : (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left) ≫ G.hom =
        spMap (algebraMap _ (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e := by
      rw [Category.assoc, Over.w y]; exact dualMap_over _
    have h₁ : pullback.lift _ _ w ≫ (fstG I e G).left = _ := pullback.lift_fst _ _ _
    obtain ⟨h₂, h₃⟩ := hg e _ _ _ h₁
    refine ⟨_, h₁, h₂, fun χ => corr_of_val hL fun z J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp, Category.id_comp]
    exact h₃ χ z J hJ
  · obtain ⟨o, ho⟩ := FormalValue.exists_isZero D.toPre (baseOver (Sp R))
    have hob : o.b.left = redE R ≫ g.b.left := by
      rw [hb, ho.1]
      exact (congrArg (· ≫ η[D.toPre.P.A].left)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (baseOver (Sp R)))))).trans (Category.id_comp _)
    have e₁ := TorusCoord.comp_eq_of_left g.b o.b (redE R) (𝟙 _) (hob.symm.trans (Category.id_comp _).symm)
    refine ⟨o, ho, hob, fun χ => RedTotal.corr_of_levels I hL (fun W _ f => ?_) (o.isGen χ)
      (DVR.pullGen_isGen _ _ _ _ (g.isGen χ) _) fun e z J hJ => ?_⟩
    · exact Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
        ((e₁.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq o.b χ) k).symm)).symm
    · refine ((val_corr hJ (ho.2 χ) _).trans (val_one _)).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      refine Eq.trans ?_ ((hz e).2 χ z J hJ)
      have := (val_corr hJ ((U.gt e).t_unit χ) (𝟙 _)).trans (val_one _)
      rw [val_pull hJ, Category.id_comp] at this
      exact this.symm

end GlobalTheory.MBLow.TanLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsometryTorsionEqLevelSmul
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.TateTorsion


open NumberField in
theorem _root_.GlobalTheory.TateTorsion.torsion_eq_level_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (T : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso Dw k Q act e) (eta : Dw.La → Q) (I : Ideal (𝓞 E)) (g : ℕ), (∀ a b x, act (a + b) x = act a x * act b x) → (∀ x, act 1 x = x) → (∀ (n : ℕ) x, act (n : 𝓞 E) x = x ^ n) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), eta a = T.ev l.M a) → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → l.Mb ≤ I → ∃ t : 𝓞 E, (∀ c ∈ I • (⊤ : Submodule (𝓞 E) Dw.La), t • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ ∀ x : Q, (∀ a ∈ I, act a x = 1) → ∃ c : Dw.La, x = eta (t • c) := by
  intro E _ _ _ H Dw l k _ Q _ act e T eta I g hadd hone hnat heta hg hI hsq hle
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hprime : I.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hI]
    exact (Nat.prime_iff.mp hg).irreducible
  have hne : I ≠ ⊥ := by
    rintro rfl
    simp only [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  obtain ⟨B, hB⟩ : I ∣ Ideal.span {(g : 𝓞 E)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hgI)
  have hIB : I ⊔ B = ⊤ := by
    by_contra h
    have hBI : B ≤ I := (hmax.eq_of_le h le_sup_left).symm ▸ le_sup_right
    apply hsq
    have hgB : (g : 𝓞 E) ∈ I * B := hB ▸ Ideal.mem_span_singleton_self _
    rw [pow_two]
    exact Ideal.mul_mono_right hBI hgB
  have hIbar : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ :=
    eq_top_iff.mpr (l.coprime ▸ sup_le_sup_right hle _)
  have hIK : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIB hIbar ⊢
    exact hIbar.mul_right hIB
  obtain ⟨i, hi, u, hu, hiu⟩ :=
    Submodule.mem_sup.mp (hIK ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B)
  have huB : u ∈ B := Ideal.mul_le_right hu
  have huBar : u ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_le_left hu
  have hgN : g ∣ l.M := by
    have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr (hle hMb))
    have h' : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [hI, Ideal.absNorm_span_singleton, h', Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast] at h
    exact hg.dvd_of_dvd_pow h
  obtain ⟨m, hm⟩ := hgN
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; have := l.three_le; omega)
  have key : ∀ j ∈ I, (m : 𝓞 E) * u * j ∈ l.Mb := by
    intro j hj
    have h : u * j ∈ Ideal.span {(g : 𝓞 E)} := hB ▸ (mul_comm j u ▸ Ideal.mul_mem_mul hj huB)
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
    have h2 : (m : 𝓞 E) * u * j = r * (l.M : 𝓞 E) := by
      rw [mul_assoc, ← hr, hm]; push_cast; ring
    rw [h2]
    exact Ideal.mul_mem_left _ r hMb
  refine ⟨(m : 𝓞 E) * u, ?_, ?_⟩
  · intro c hc
    refine Submodule.smul_induction_on hc (fun j hj y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul]
      exact Submodule.smul_mem_smul (key j hj) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hy hz
  · intro x hx
    have hxg : x ^ g = 1 := by rw [← hnat]; exact hx _ hgI
    obtain ⟨b, hb⟩ := (T.onto g hg.pos x).mp hxg
    have hpow : ∀ (n j : ℕ) (a : Dw.La), T.ev n (j • a) = T.ev n a ^ j := by
      intro n j a
      induction j with
      | zero =>
        have h := T.add n 0 0
        rw [add_zero] at h
        simpa using h
      | succ j ih => rw [succ_nsmul, T.add, ih, pow_succ]
    have hux : act u x = x := by
      have h := hone x
      rwa [← hiu, hadd, hx i hi, one_mul] at h
    refine ⟨b, ?_⟩
    have hmem : ((m : 𝓞 E) * u) • b ∈
        l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ huBar) Submodule.mem_top
    rw [heta _ hmem, mul_comm, mul_smul, T.lin, Nat.cast_smul_eq_nsmul, hpow, hm,
      T.tower g m hg.pos hm0, hb, hux]

end GlobalTheory.TateTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FJ

theorem dot_split {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (u v : Fin g → ℂ) :
    u ⬝ᵥ v = zP σ u ⬝ᵥ zP σ v + tP σ u ⬝ᵥ tP σ v := by
  simp only [dotProduct, zP, tP]
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]

theorem quad_full {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (A : Matrix (Fin g') (Fin g') ℂ)
    (B : Matrix (Fin g') (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ) (v : Fin g → ℂ) :
    v ⬝ᵥ (Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v =
      zP σ v ⬝ᵥ A *ᵥ zP σ v + 2 * (zP σ v ⬝ᵥ B *ᵥ tP σ v) + tP σ v ⬝ᵥ D *ᵥ tP σ v := by
  rw [dot_split σ]
  have h1 : zP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = A *ᵥ zP σ v + B *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  have h2 : tP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = Bᵀ *ᵥ zP σ v + D *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  rw [h1, h2, dotProduct_add, dotProduct_add, mulVec_transpose, dotProduct_comm (tP σ v) (vecMul _ _),
    ← dotProduct_mulVec]
  ring

def thT {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) (n : Fin k → ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
    2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (z + b)))

theorem thetaChar_eq_tsum {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) :
    thetaChar τ a b z = ∑' n, thT τ a b z n := rfl

theorem summable_thT {k : ℕ} {τ : Matrix (Fin k) (Fin k) ℂ} (hτ : (τ.map Complex.im).PosDef) {a : Fin k → ℂ}
    (ha : ∀ i, ((a i).re : ℂ) = a i) (b z : Fin k → ℂ) : Summable fun n => ‖thT τ a b z n‖ := by
  have hd : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin k) := hτ.add hτ.transpose
  refine (GlobalTheory.thetaSummable_holds (Fin k) (fun i => (a i).re) 0 (z + b) τ hd).congr fun n => ?_
  congr 1
  have hs : ReciprocityTheory.PTheta.shiftVec (fun i => (a i).re) n = (fun i => (n i : ℂ)) + a :=
    funext fun i => by simp [ReciprocityTheory.PTheta.shiftVec, ha i]
  have h0 : ReciprocityTheory.PTheta.ofRealVec (0 : Fin k → ℝ) = 0 := funext fun i => by simp [ReciprocityTheory.PTheta.ofRealVec]
  simp only [ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC, thT]
  rw [hs, h0, add_zero]
  congr 1
  ring

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem thT_full (S : Matrix (Fin r) (Fin r) ℂ) (Z : Fin g → ℂ) (n : Fin g → ℤ) :
    thT (d.full σ S) (d.aF σ) (d.bF σ) Z n =
      Complex.exp (Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (d.t22 + S) *ᵥ cv (tP σ n)) +
        2 * Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (tP σ Z + d.b2))) *
      thT d.τ d.a d.b (zP σ Z + d.t12 *ᵥ cv (tP σ n)) (zP σ n) := by
  have hz : zP σ ((fun i => (n i : ℂ)) + d.aF σ) = (fun i => ((zP σ n i : ℤ) : ℂ)) + d.a := by
    funext i; simp [zP, CD.aF]
  have ht : tP σ ((fun i => (n i : ℂ)) + d.aF σ) = cv (tP σ n) := by
    funext i; simp [tP, CD.aF, cv]
  have hz' : zP σ (Z + d.bF σ) = zP σ Z + d.b := by
    funext i; simp [zP, CD.bF]
  have ht' : tP σ (Z + d.bF σ) = tP σ Z + d.b2 := by
    funext i; simp [tP, CD.bF]
  unfold thT CD.full
  rw [quad_full, dot_split σ _ (Z + d.bF σ), hz, ht, hz', ht', ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

end GlobalTheory.MBLow.Cl.FJ


open GlobalTheory.MBLow.Cl.FJ in
theorem GlobalTheory.MBLow.Cl.fj_expansion : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm →
    ((d.full σ S).map Complex.im).PosDef → ∀ Z, (Summable fun χ => ‖d.fj σ S χ Z‖) ∧
      ∑' χ, d.fj σ S χ Z = thetaChar (d.full σ S) (d.aF σ) (d.bF σ) Z := by
  intro N g' r g bX d σ S _ hpos Z
  let e : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ) :=
    { toFun := fun n => (tP σ n, zP σ n)
      invFun := fun p j => Sum.elim p.2 p.1 (σ j)
      left_inv := fun n => by
        funext j
        rcases h : σ j with i | l
        · simp only [h, Sum.elim_inl, zP]; rw [σ.symm_apply_eq.mpr h.symm]
        · simp only [h, Sum.elim_inr, tP]; rw [σ.symm_apply_eq.mpr h.symm]
      right_inv := fun p => by ext <;> simp [zP, tP] }
  have haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j := by
    intro j
    simp only [CD.aF]
    rcases σ j with i | l
    · rcases d.ha i with h | h <;> simp [h]
    · simp
  let F : (Fin r → ℤ) × (Fin g' → ℤ) → ℂ := fun p => thT (d.full σ S) (d.aF σ) (d.bF σ) Z (e.symm p)
  have hF : Summable fun p => ‖F p‖ :=
    (e.symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) Z n‖)).mpr
      (summable_thT hpos haF (d.bF σ) Z)
  have hFc : Summable F := hF.of_norm
  have hkey : ∀ χ, d.fj σ S χ Z = ∑' m, F (bX.equivFun χ, m) := by
    intro χ
    have hcv : cv (bX.equivFun χ) = co bX χ := by
      funext l; simp [cv, co, Module.Basis.equivFun_apply]
    have hsymm : ∀ p, e (e.symm p) = p := e.apply_symm_apply
    simp only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left, F]
    congr 1
    funext m
    have h1 : tP σ (e.symm (bX.equivFun χ, m)) = bX.equivFun χ := congrArg Prod.fst (hsymm (bX.equivFun χ, m))
    have h2 : zP σ (e.symm (bX.equivFun χ, m)) = m := congrArg Prod.snd (hsymm (bX.equivFun χ, m))
    rw [thT_full, h1, h2, hcv]
  refine ⟨?_, ?_⟩
  · refine ((hF.prod).comp_injective bX.equivFun.injective).of_nonneg_of_le (fun _ => norm_nonneg _) fun χ => ?_
    rw [hkey χ]
    exact norm_tsum_le_tsum_norm (hF.prod_factor _)
  · have hre := bX.equivFun.toEquiv.tsum_eq (fun k => ∑' m, F (k, m))
    simp only [LinearEquiv.coe_toEquiv] at hre
    rw [tsum_congr hkey, hre, ← hFc.tsum_prod, thetaChar_eq_tsum, ← e.symm.tsum_eq]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem key_value_of_nf : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  intro κ hH hT g x hg u τ a b c Mx h
  subst hg
  obtain ⟨h₁, h₂, ha, hb, hc, hΛ, hr, hs, hd⟩ := h
  have hW := GlobalTheory.KeyFormulaCompare.det_ne_zero x u ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx) hd
  have hM : Mx.det ≠ 0 := by
    rw [Matrix.det_smul] at hW
    exact right_ne_zero_of_mul hW
  refine ⟨hM, ?_⟩
  have hN : KeyPow.NormalAt x τ Mx a b c := ⟨u, h₁, h₂, hΛ, hr, hs, hd⟩
  obtain ⟨P, hg, rig, hr', th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, h₀, e₁, e₂⟩ := KeyConst.exists_rescale _ _ _ _ _ _ _ _ _ _ _ _ _ hc hM hN
  obtain ⟨u₀, t₁, t₂, t₃, t₄, t₅, t₆⟩ := (KeyPow.normalAt_one_iff _ _ _ _).1 h₀
  have h₃ := hH ℂ P hg rig hr' th₀ hth₀ v₀ hv₀ th hth v hv c Mx e₁ e₂
  have h₄ := hT _ u₀ _ _ _ t₁ t₂ ha hb t₃ t₄ t₅ t₆
  rw [h₄, Units.val_one, _root_.mul_one] at h₃
  rw [mul_comm]
  exact h₃.trans (_root_.mul_one _)

end GlobalTheory.MBLow.Cl
end

