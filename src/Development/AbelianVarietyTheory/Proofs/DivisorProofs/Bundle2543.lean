module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsExt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GFib

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf}

def IsEndoExt (X : USetup C) (wi : UWit X) {Y : RatModel X.o₁ X.Ω₁} {U₀ : Y.Z.Opens} {EE : Y.Lat X.S.J}
    (FinalForm : ZHOut X.ρ Y U₀ EE) (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) : Prop :=
  ∀ a, IsMonHom (f a) ∧ ∀ (x₀ : Sp X.Ω₁ ⟶ U₀.toScheme) (_ : x₀ ≫ U₀.ι = Y.pt)
    (hw : wi.α ≫ X.ρ.P.A.hom = (wi.G.hom ≫ x₀) ≫ FinalForm.u₀) (e₀ : wi.G ⟶ wi.G),
    e₀.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left →
    e₀.left ≫ pullback.lift wi.α (wi.G.hom ≫ x₀) hw ≫ FinalForm.φ = pullback.lift wi.α (wi.G.hom ≫ x₀) hw ≫ FinalForm.φ ≫ (f a).left

def IsTorsExt (X : USetup C) (wi : UWit X) {Y : RatModel X.o₁ X.Ω₁} {U₀ : Y.Z.Opens} {EE : Y.Lat X.S.J}
    (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z) (z : X.M.Z) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)) : Prop :=
  ∀ t, gγ t ^ (X.S.r * X.S.N) = 1 ∧
    (∀ (x₀ : Sp X.Ω₁ ⟶ U₀.toScheme) (_ : x₀ ≫ U₀.ι = Y.pt) (hw : wi.α ≫ X.ρ.P.A.hom = (wi.G.hom ≫ x₀) ≫ FinalForm.u₀)
      (w : Sp X.Ω₁ ⟶ wi.G.left), w ≫ wi.G.hom = 𝟙 _ → w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt (t : X.S.Gam)).left →
      w ≫ pullback.lift wi.α (wi.G.hom ≫ x₀) hw ≫ FinalForm.φ = (gγ t).left) ∧
    ∀ w, q.base w = z → ExtNear (gγ t) w

end GlobalTheory.UPoinc.GFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalConjLabels

variable {R : Type} [CommRing R] [IsDomain R]

theorem spMap_jFK (f : Kb R →ₐ[FractionRing R] Kb R) :
    spMap f.toRingHom ≫ jFK (R := R) (Kb R) = jFK (R := R) (Kb R) := by
  rw [spMap, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) f.comp_algebraMap

def tauHom (f : Kb R →ₐ[FractionRing R] Kb R) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap f.toRingHom) (spMap_jFK f)

theorem tauHom_left (f : Kb R →ₐ[FractionRing R] Kb R) : (tauHom f).left = spMap f.toRingHom := rfl

theorem tauHom_comp_eq_id (f g : Kb R →ₐ[FractionRing R] Kb R) (h : ∀ a, f (g a) = a) :
    tauHom f ≫ tauHom g = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.id_left, tauHom_left, tauHom_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have e : f.toRingHom.comp g.toRingHom = RingHom.id _ := RingHom.ext h
  rw [e, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem map_unitOn' {k k' : Type} [CommRing k] [CommRing k'] (σ : k →+* k') (u : kˣ) :
    Units.map (spMap σ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map σ.toMonoidHom u) :=
  Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))).symm

end GlobalTheory.Mum.GalConjLabels

namespace GlobalTheory.Mum


open GalConjLabels in
theorem labTors_galConj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  intro R _ _ _ hR D A σ k hk x x' hx hxx'
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  have hB := D.tau_bimult
  have hL := GlobalTheory.allSixLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hbij : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hbij
  let ρ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have hσρ : ∀ a, σ (ρ a) = a := fun a => e.apply_symm_apply a
  have hρσ : ∀ a, ρ (σ a) = a := fun a => e.symm_apply_apply a
  have hfσ : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hfρ : ρ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    ρ.comp_algebraMap
  haveI : CharZero (Kb R) :=
    (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk0 : (k : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have rev : ∀ {p p' : QkPt D.toPre (Kb R) k}, QkExt σ.toRingHom p p' → QkExt ρ.toRingHom p' p := by
    intro p p' h
    obtain ⟨q, hq⟩ := GlobalTheory.QkClosure.exists_qkExt ρ.toRingHom hfρ p'
    have h2 := GlobalTheory.LevelField.qkExt_trans h hq
    have eid : ρ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext hρσ
    rw [eid] at h2
    have := GlobalTheory.QkClosure.qkExt_unique (RingHom.id (Kb R)) (RingHom.id_comp _) h2 (GlobalTheory.LabExt.qkExt_refl p)
    rwa [this] at hq
  have desc : ∀ p' : QkPt D.toPre (Kb R) k, ∃ p, QkExt σ.toRingHom p p' := fun p' =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom hfσ hk0 p'
  have hx'eq : ∀ p p', QkExt σ.toRingHom p p' → x' p' = tauHom σ ≫ x p := fun p p' h =>
    Over.OverMorphism.ext (hxx' p p' h)
  have cσρ : tauHom σ ≫ tauHom ρ = 𝟙 _ := tauHom_comp_eq_id σ ρ hσρ
  have cρσ : tauHom ρ ≫ tauHom σ = 𝟙 _ := tauHom_comp_eq_id ρ σ hρσ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  refine ⟨fun y hy => ?_, fun p' => ?_, fun p' q' => ?_, fun p' q' r' hadd => ?_, fun p' q' z => ?_⟩
  · obtain ⟨p, hp⟩ := h1 (tauHom ρ ≫ y) (by rw [← comp_pow, hy, comp_one])
    obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt σ.toRingHom hfσ p
    exact ⟨p', by rw [hx'eq p p' hp', hp, ← Category.assoc, cσρ, Category.id_comp]⟩
  · obtain ⟨p, hp⟩ := desc p'
    rw [hx'eq p p' hp, ← comp_pow, h2, comp_one]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro h
      have h' : x p = x q := by
        have := congrArg (tauHom ρ ≫ ·) h
        simpa only [← Category.assoc, cρσ, Category.id_comp] using this
      exact GlobalTheory.TorusExt.equiv_of_qkExt hB σ.toRingHom hfσ hp hq ((h3 p q).1 h')
    · intro h
      rw [(h3 p q).2 (GlobalTheory.TorusExt.equiv_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) h)]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    obtain ⟨r, hr⟩ := desc r'
    rw [hx'eq p p' hp, hx'eq q q' hq, hx'eq r r' hr,
      h4 p q r (GlobalTheory.TorusExt.qkAdd_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) (rev hr) hadd), comp_mul]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    let z₀ : (Kb R)ˣ := Units.map ρ.toRingHom.toMonoidHom z
    have hz : Units.map σ.toRingHom.toMonoidHom z₀ = z := Units.ext (hσρ z)
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro hW
      have w₀ : WeilQkIs D.toPre (Kb R) k p q (z₀ : Kb R) := by
        have := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB ρ.toRingHom hfρ k hk p' q' z hW
        rwa [← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hp),
          ← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hq)] at this
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom σ) ((h5 p q z₀).1 w₀)
      rwa [tauHom_left, map_unitOn', hz] at this
    · intro hW
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom ρ) hW
      rw [tauHom_left, map_unitOn', ← Category.assoc, ← Category.assoc, cρσ, Category.id_comp,
        Category.id_comp] at this
      have w₀ := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB σ.toRingHom hfσ k hk p q _
        ((h5 p q z₀).2 this)
      rw [← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hp,
        ← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hq] at w₀
      have e' : σ.toRingHom (z₀ : Kb R) = (z : Kb R) := hσρ z
      rwa [e'] at w₀

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueTranslateOrthogonalTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTwistedThetaValue_translate_orthogonal_torsion : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) (k : T ⟶ P.A), k ^ m = 1 → WeilIs P.A P.L N x k 1 → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x (h * k) v := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_transl | exact GlobalTheory.UPoinc.USum.isTwVal_transl | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_transl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTwistedThetaValue_unique : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v v' : Γ(T.left, ⊤)), Odd N → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x h v' → v = v' := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_unique | exact GlobalTheory.UPoinc.USum.isTwVal_unique | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfIsUnitConstantClosedPointLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.unit_of_isUnit_cst_closedPoint : ∀ (V : Type) [CommRing V] [IsLocalRing V] (a : V), IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a) → IsUnit a := by
  intro V _ _ a h
  have e := gs_eq (𝟙 (Sp V)) (closedPoint V) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have h' : IsUnit ((Sp V).presheaf.germ ⊤ (closedPoint V) trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) := by
    have h2 : IsUnit (gs (𝟙 (Sp V)) (closedPoint V) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) := h
    rw [e] at h2
    simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply] at h2
    exact h2
  have hm := (Scheme.mem_basicOpen_top (X := Sp V) ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) (closedPoint V)).mpr h'
  rw [basicOpen_eq_of_affine] at hm
  by_contra ha
  exact ((PrimeSpectrum.mem_basicOpen _ _).mp hm) ((IsLocalRing.mem_maximalIdeal a).mpr ha)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitRigidifiedValueAtOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem stalkOf_closedPoint_isUnit {W : Type} [CommRing W] [IsLocalRing W] (v : W)
    (h : IsUnit (stalkOf (closedPoint W) v)) : IsUnit v := by
  have e : stalkOf (closedPoint W) = (stalkClosedPointIso (CommRingCat.of W)).inv.hom := by
    unfold stalkOf
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    ext x
    simp
  rw [e] at h
  exact (isUnit_map_iff (stalkClosedPointIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv v).1 h

theorem isUnit_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R), OrigVal D b v → eSec D.P.A (closedPoint R) ∈ nonzeroLocus b → IsUnit v := by
  intro R _ _ _ D k α b v hv hmem
  have hmem' : ∃ j, eSec D.P.A (closedPoint R) ∈ D.P.A.left.basicOpen (b.f j) := by
    unfold nonzeroLocus at hmem
    simpa [TopologicalSpace.Opens.mem_iSup] using hmem
  obtain ⟨j, hj⟩ := hmem'
  have hjU := D.P.A.left.basicOpen_le (b.f j) hj
  have hu := (Scheme.mem_basicOpen _ _ _ hjU).1 hj
  obtain ⟨J, hJ, -⟩ := exists_good (Z := Sp R) D.P.L D.P.isLB (closedPoint R) (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hsv := hv (closedPoint R) J hJ
  have e1 := sec_trans b (unitW D.P.A) (closedPoint R) (hJ.mem (D.famφB α) (unitW D.P.A)) hjU
  have hg : IsUnit (gs (unitW D.P.A) (closedPoint R) _ (b.f j)) := by
    rw [gs_eq _ _ _ hjU]
    have e2 := Scheme.Hom.germ_stalkMap_apply (eSec D.P.A) _ (closedPoint R) hjU (b.f j)
    exact e2 ▸ hu.map ((eSec D.P.A).stalkMap (closedPoint R)).hom
  have hs : IsUnit (sval b (unitW D.P.A) (closedPoint R) J) := by
    show IsUnit (gs _ _ _ _)
    rw [e1]
    exact (Units.isUnit _).mul hg
  rw [hsv] at hs
  exact stalkOf_closedPoint_isUnit v (isUnit_of_mul_isUnit_left hs)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoGermTrans
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFamGlue

section General

variable {X₁ X₂ Y T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂} {K : Type} [Fintype K]

def isoGerm (w : LB.Iso (L.pull a) (M.pull b)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : M.ι) (q : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q)) (w.s (fun _ => p, fun _ => q))

theorem isoGerm_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {p p' : M.ι} {q q' : L.ι}
    (hp : b (r z) ∈ M.U p) (hp' : b (r z) ∈ M.U p') (hq : a (r z) ∈ L.U q) (hq' : a (r z) ∈ L.U q') :
    isoGerm w r z p q = gm (r ≫ b) z _ (M.g p p') * (gm (r ≫ a) z _ (L.g q q'))⁻¹ * isoGerm w r z p' q' := by
  have hm : r z ∈ (M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q) ⊓
      ((M.pull b).U (fun _ => p') ⊓ (L.pull a).U (fun _ => q')) :=
    ⟨⟨mem_pull.2 hp, mem_pull.2 hq⟩, mem_pull.2 hp', mem_pull.2 hq'⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (hw (fun _ => p, fun _ => q) (fun _ => p', fun _ => q'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_div (L.pull a) (M.pull b) r z (fun _ => p, fun _ => q) (fun _ => p', fun _ => q') hm).trans ?_)
      (gm_res r z _ hm _))))
  exact congrArg₂ (· * ·) (gm_pull_g M b r z _ _ hm.1.1 hm.2.1) (congrArg (·⁻¹) (gm_pull_g L a r z _ _ hm.1.2 hm.2.2))

theorem prod_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {p p' : K → M.ι} {q q' : K → L.ι}
    (hp : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p) (hp' : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p')
    (hq : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q) (hq' : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q') :
    ∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k = trF (fun k => ψ k ≫ b) ε r z p p' *
      (trF (fun k => ψ k ≫ a) ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ ψ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ ψ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, inv_zpow]
  simp only [Category.assoc]

theorem exists_down (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y))
    (ε : K → ℤ) (σ : LB.Sec (LB.LinComb M (fun k => ψ k ≫ b) ε)) :
    ∃ τ : LB.Sec (LB.LinComb L (fun k => ψ k ≫ a) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (p : K → M.ι) (q : K → L.ι),
      r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L (fun k => ψ k ≫ a) q) (τ.f q) =
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
  have cov : ∀ y : T, ∃ p, y ∈ LB.wchart M (fun k => ψ k ≫ b) p := fun y => by
    choose I hI using fun k => exists_chart hM ((ψ k ≫ b) y)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  have glue : ∀ q : K → L.ι, ∃ c : Γ(T, LB.wchart L (fun k => ψ k ≫ a) q), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z)
      (p : K → M.ι), r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      gs r z _ c = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
    intro q
    let V : (K → M.ι) → T.Opens := fun p => LB.wchart M (fun k => ψ k ≫ b) p ⊓ LB.wchart L (fun k => ψ k ≫ a) q
    have h₃ : ∀ p k, V p ≤ ψ k ⁻¹ᵁ ((M.pull b).U (fun _ => p k) ⊓ (L.pull a).U (fun _ => q k)) := fun p k y hy =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 k), mem_pull.2 (Set.mem_iInter.1 hy.2 k)⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(T, V p), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p, r z ∈ V p →
        gs r z (V p) (u p) = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
          gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) :=
      ⟨fun p => (∏ k, res (h₃ p k) (pullU (ψ k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹.val *
          (T.presheaf.map (homOfLE (inf_le_left : V p ≤ LB.wchart M (fun k => ψ k ≫ b) p)).op).hom (σ.f p),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) ((map_prod _ _ _).trans
            (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
              ((gm_res r z (h₃ p k) hz _).trans (gm_pull r (ψ k) z _ (h₃ p k hz) _))))))))) (gs_res r z _ hz _))⟩
    obtain ⟨c, hc, -⟩ := T.sheaf.existsUnique_gluing' V (LB.wchart L (fun k => ψ k ≫ a) q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨p, hp⟩ := cov y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hp, hy⟩) u
      (fun p p' => fn_ext (V := V p ⊓ V p') fun y hy => by
        refine (gs_res (𝟙 T) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 T) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2, sec_trans σ (𝟙 T) y hy.1.1 hy.2.1,
          prod_trans hw ψ ε (𝟙 T) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          mul_eq_left.1 (trF_trans hL _ ε (𝟙 T) y hy.1.2 hy.1.2 hy.1.2), ← _root_.mul_assoc, ← Units.val_mul]
        congr 2
        rw [inv_one, _root_.mul_one, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨c, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ V p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz c).symm.trans ((congrArg (gs r z (V p)) (hc p)).trans (hu Z r z p hz))
  choose c hc using glue
  refine ⟨⟨c, fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z p q hp hq => ?_⟩
  · obtain ⟨p, hp⟩ := cov y
    refine (gs_res (𝟙 T) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 T) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 T) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 T) y q q' hy.1 hy.2)))
      (gs_res (𝟙 T) y _ hy _))).symm)
    refine (hc q _ (𝟙 T) y p hp hy.1).trans (Eq.trans ?_ (congrArg _ (hc q' _ (𝟙 T) y p hp hy.2)).symm)
    rw [prod_trans hw ψ ε (𝟙 T) y hp hp hy.1 hy.2, mul_eq_left.1 (trF_trans hM _ ε (𝟙 T) y hp hp hp),
      ← _root_.mul_assoc, ← Units.val_mul, _root_.one_mul, mul_inv_rev, inv_inv, _root_.mul_comm _⁻¹]
    rfl
  · exact (congrArg _ (hc q Z r z p hp hq)).trans (Units.mul_inv_cancel_left _ _)

def sumSec {N : LB Y} {A : Type} (S : Finset A) (s : A → N.Sec) : N.Sec where
  f i := ∑ x ∈ S, (s x).f i
  compat i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (s x).compat i j

theorem sval_sumSec {φ : K → (Y ⟶ X₁)} {ε : K → ℤ} {A : Type} (S : Finset A) (s : A → (LB.LinComb L φ ε).Sec)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (sumSec S s) r z J = ∑ x ∈ S, sval (s x) r z J := DVR.gs_fsum r z _ (hJ.mem φ r) S _

end General

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

theorem formEq_term (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left) (n j : ℤ) (β : D.toPre.X) :
    FormEq (Sum.elim (fun k => DVR.pGl U e ≫ tφ D.toPre a β k) (DVR.Oφl U e β)) (Sum.elim (tε n j) Oinvε)
      (fun k => (![𝟙 _, b.left] : Fin 2 → _) k ≫ DVR.pGl U e) ![n, j] := by
  intro V _ h
  have a₀ : DVR.pGl U e ≫ tφ D.toPre a β 0 = DVR.pGl U e := Category.comp_id _
  have a₁ : DVR.pGl U e ≫ tφ D.toPre a β 1 = DVR.Oφl U e β 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (DVR.cP D.toPre _ β)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (DVR.comp_cP D.toPre _ β)))
  have a₂ : DVR.pGl U e ≫ tφ D.toPre a β 2 = DVR.Oφl U e β 1 :=
    congrArg (fun z => z.left) (DVR.comp_cP D.toPre (U.gt e).pG β)
  have a₃ : DVR.pGl U e ≫ tφ D.toPre a β 3 = DVR.Oφl U e β 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : DVR.Oφl U e β 2 = DVR.pGl U e := rfl
  have a₅ : DVR.pGl U e ≫ tφ D.toPre a β 4 = b.left ≫ DVR.pGl U e := hb.symm
  have a₆ : (![𝟙 _, b.left] : Fin 2 → _) 0 ≫ DVR.pGl U e = DVR.pGl U e := Category.id_comp _
  have a₇ : (![𝟙 _, b.left] : Fin 2 → _) 1 ≫ DVR.pGl U e = b.left ≫ DVR.pGl U e := rfl
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_four, Fin.prod_univ_two]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, tε, Oinvε, Matrix.cons_val]
  module

theorem exists_texp (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) (n j : ℤ) {Ix : Type}
    {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (hs : Small I s) :
    ∃ τ : SecE U b n j, TExp U τ s := by
  classical
  have hb' : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left := by
    have h₁ : b.left ≫ (U.gt e).q.left = (U.gt e).q.left ≫ ((Over.pullback (thick R I e)).map a).left :=
      congrArg (fun f => f.left) hb
    have h₂ : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
        pullback.fst D.toPre.P.A.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _
    show b.left ≫ (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
      ((U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e)) ≫ a.left
    rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
  choose σ hσ using fun i => exists_sec D.toPre.P.isLB (formEq_term U e a b hb' n j (w i))
    (pullMulSec (s i) (DVR.pGl U e) (DVR.tG U e (w i)) ((U.gt e).t_gen (w i)))
  obtain ⟨τ₀, h₀⟩ := exists_down U.LG.isLB D.toPre.P.isLB (U.w_gen e) (![𝟙 _, b.left] : Fin 2 → _) ![n, j]
    (sumSec (hs e).toFinset σ)
  obtain ⟨τ, hτ⟩ := exists_sec U.LG.isLB (φ' := ![(fstG I e G).left, b.left ≫ (fstG I e G).left]) (ε' := ![n, j])
    (fun V _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      exact congrArg (fun f => h f ^ n * _) (Category.id_comp _)) τ₀
  refine ⟨τ, fun S hS Z x z J J' hJ hJ' => ?_⟩
  have H := h₀ Z x z _ _ (hJ.mem _ x) (hJ'.mem _ x)
  have van : ∀ i, Van I (s i) e → sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val = 0 :=
    fun i hi => by
      have := hi Z (x ≫ (U.gt e).q.left) z J hJ
      rw [Category.assoc] at this
      exact (congrArg (· * _) this).trans (zero_mul _)
  have H₂ : sval (sumSec (hs e).toFinset σ) x z J =
      ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val := by
    rw [sval_sumSec _ _ x z hJ]
    refine (Finset.sum_congr rfl fun i _ => (hσ i Z x z J hJ).trans (sval_pullMulSec _ _ _ _ x z hJ)).trans ?_
    refine Finset.sum_subset (fun i hi => by_contra fun h => (hs e).mem_toFinset.1 hi (hS i h)) fun i _ hi => ?_
    exact van i (by_contra fun h => hi ((hs e).mem_toFinset.2 h))
  refine Eq.trans ?_ (H.trans H₂)
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) (hτ Z x z J' hJ')
  rw [Fin.prod_univ_two]
  show _ = DVR.wv U e (x ≫ 𝟙 _) z (J (x ≫ 𝟙 _ ≫ _)) (J' (x ≫ 𝟙 _ ≫ _)) ^ n * _
  rw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

end Main

theorem glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map a → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ τ : SecE U.toUnifPre b n j, TExp U.toUnifPre τ s :=
  fun _ _ _ _ _ _ a _ _ _ _ _ U e b hb n j _ _ s hs => exists_texp U.toUnifPre e a b hb n j s hs

end GlobalTheory.TwFamGlue
end
end

