module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsilonPartDeformationFormClassEqCoboundaryOfLif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftTriv

section General

variable {R₁ R₂ R' : Type} [CommRing R₁] [CommRing R₂] [CommRing R'] {I₁ : Ideal R₁} {I₂ : Ideal R₂}
  {I' : Ideal R'} {X₁ X₂ X' : Scheme.{0}} {κ₁ : DividedPowers I₁} {κ₂ : DividedPowers I₂} {κ' : DividedPowers I'}
  {s₁ : X₁ ⟶ Sp R₁} {s₂ : X₂ ⟶ Sp R₂} {s' : X' ⟶ Sp R'} {σ₁ : R₁ →+* R'} {σ₂ : R₂ →+* R'}
  {p₁ : X' ⟶ X₁} {p₂ : X' ⟶ X₂}

def pv (h : IsMor κ₁ s₁ κ' s' σ₁ p₁) (f : Z1 (O κ₁ s₁)) {T T' : Thick κ' s'} (φ : T ⟶ T') : T'.B :=
  ev f (h.functor.map φ)

theorem exists_of_pull1_eq (h₁ : IsMor κ₁ s₁ κ' s' σ₁ p₁) (h₂ : IsMor κ₂ s₂ κ' s' σ₂ p₂) (f : Z1 (O κ₁ s₁))
    (g b : Z1 (O κ₂ s₂)) (r : R')
    (e : h₁.pull1 (H1.mk _ f) = h₂.pull1 (H1.mk _ g) + r • h₂.pull1 (H1.mk _ b)) :
    ∃ G : ∀ T : Thick κ' s', T.B, ∀ (T T' : Thick κ' s') (φ : T ⟶ T'),
      G T' - φ.φ (G T) = pv h₁ f φ - (pv h₂ g φ + algebraMap R' T'.B r * pv h₂ b φ) := by
  have e' : H1.mk (O κ' s') (h₁.coef.pullbackOneCocycle f) =
      H1.mk (O κ' s') (h₂.coef.pullbackOneCocycle g + r • h₂.coef.pullbackOneCocycle b) := by
    rw [map_add (f := _), map_smul]
    exact e
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 e'
  refine ⟨G, fun T T' φ ↦ ?_⟩
  rw [← Algebra.smul_def]
  exact congrFun (congrFun (congrFun hG T) T') φ

theorem form_idLift {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Form s)
    {T T' : Thick (dp0 R) s} (Φ : T ⟶ T') (y : Sp T.B ⟶ X) (hy : y ≫ s = spMap (algebraMap R T.B))
    (ey : spMap T.π ≫ y = T.x) (y' : Sp T'.B ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R T'.B))
    (ey' : spMap T'.π ≫ y' = T'.x) (e : spMap (Φ.φ : T.B →+* T'.B) ≫ y = y') :
    ev f.1 Φ = ev f.1 (idLift T' y' hy' ey') - Φ.φ (ev f.1 (idLift T y hy ey)) := by
  let a : Thick.triv T.B y hy ⟶ Thick.triv T'.B y' hy' := Thick.trivHom Φ.φ e
  have k := Form.ev_sq f a (idLift T' y' hy' ey') (idLift T y hy ey) Φ rfl rfl fun _ ↦ rfl
  exact eq_sub_of_add_eq' k.symm

end General

section Eps

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]


omit [GrpObj A] in
def epsHom {P Q : GPt A} (φ : P.Hom Q) : P.eps ⟶ Q.eps :=
  letI := P.eps.alg
  letI := Q.eps.alg
  { φ := { dualMap (φ.ρ : P.B →+* Q.B) with
      commutes' := fun r ↦ by
        change dualMap (φ.ρ : P.B →+* Q.B) (dualMap (algebraMap K P.B) r) = dualMap (algebraMap K Q.B) r
        ext <;> simp [dualMap] }
    φ₀ := (φ.ρ : P.B →+* Q.B)
    comm := fun c ↦ by
      change φ.ρ c.fst = (dualMap (φ.ρ : P.B →+* Q.B) c).fst
      simp [dualMap]
    dp := isDPMorphism_sqDP (SqExt.ofModule K P.B P.B).sq (SqExt.ofModule K Q.B Q.B).sq _ fun a ha ↦ by
      have ha' : a.fst = 0 := ha
      change (dualMap (φ.ρ : P.B →+* Q.B) a).fst = 0
      simp [dualMap, ha']
    pt := φ.pt }

def epsSec (P : GPt A) : P.triv ⟶ (constMor A).isMor.obj P.eps :=
  letI := ((constMor A).isMor.obj P.eps).alg
  Thick.trivHom
    { (TrivSqZeroExt.inlAlgHom K P.B P.B : P.B →+* DualNumber P.B) with
      commutes' := fun r ↦ by
        change TrivSqZeroExt.inl (algebraMap K P.B r) =
          dualMap (algebraMap K P.B) (algebraMap K (DualNumber K) r)
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] }
    (by
      change spMap (RingHom.id P.B) ≫ P.x = P.x ≫ (𝟙 A : A ⟶ A).left
      simp [Cris.spMap_id])

def secVal (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (P : GPt A) : DualNumber P.B := ev f (epsSec P)

theorem pv_const (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) {P Q : GPt A} (φ : P.Hom Q) :
    (pv (constMor A).isMor f (epsHom φ) : DualNumber Q.B) =
      TrivSqZeroExt.inl (ev f φ.triv : Q.B) + secVal f Q - dualMap (φ.ρ : P.B →+* Q.B) (secVal f P) := by
  have k := Cris.ev_sq f φ.triv (epsSec Q) (epsSec P) ((constMor A).isMor.functor.map (epsHom φ)) fun c ↦ by
    change (TrivSqZeroExt.inl (φ.ρ c) : DualNumber Q.B) = dualMap (φ.ρ : P.B →+* Q.B) (TrivSqZeroExt.inl c)
    ext <;> simp [dualMap]
  exact eq_sub_of_add_eq' (G := DualNumber Q.B) k.symm

variable {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}

theorem pv_lift (h : IsGrpPullback A A' (DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    {P Q : GPt A} (φ : P.Hom Q) {y : Sp (DualNumber P.B) ⟶ A'.left} {y' : Sp (DualNumber Q.B) ⟶ A'.left}
    (hy : IsLift i P y) (hy' : IsLift i Q y') (e : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y') :
    (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) =
      liftVal h ω'.1 hy' - dualMap (φ.ρ : P.B →+* Q.B) (liftVal h ω'.1 hy) := by
  exact form_idLift ω' ((liftMor (epsDP K) h).isMor.functor.map (epsHom φ)) y hy.1 hy.2 y' hy'.1 hy'.2 e

end Eps

theorem eps_part_eq_coboundary (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (ω : Form (A.hom ≫ 𝟙 (Sp K))) (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hyp : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') = (constMor A).isMor.pull1 (Form.cl _ ω) +
      (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (P Q : GPt A) (φ : P.Hom Q) (y : Sp (DualNumber P.B) ⟶ A'.left)
      (y' : Sp (DualNumber Q.B) ⟶ A'.left) (hy : IsLift i P y) (hy' : IsLift i Q y'),
      spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y' →
      ev b φ.triv = ((liftVal h ω'.1 hy').snd + G Q) - φ.ρ ((liftVal h ω'.1 hy).snd + G P) := by
  obtain ⟨G₀, hG⟩ := exists_of_pull1_eq (liftMor (epsDP K) h).isMor (constMor A).isMor ω'.1 ω.1 b
    DualNumber.eps hyp
  let G₁ : ∀ P : GPt A, DualNumber P.B := fun P ↦ G₀ (Pt.eps P)
  refine ⟨fun P ↦ -(secVal ω.1 P).snd - (secVal b P).fst - (G₁ P).snd, fun P Q φ y y' hy hy' e ↦ ?_⟩
  have k : G₁ Q - dualMap (φ.ρ : P.B →+* Q.B) (G₁ P) =
      (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) -
        ((pv (constMor A).isMor ω.1 (epsHom φ) : DualNumber Q.B) +
          dualMap (algebraMap K Q.B) DualNumber.eps * (pv (constMor A).isMor b (epsHom φ) : DualNumber Q.B)) :=
    hG P.eps Q.eps (epsHom φ)
  rw [pv_lift h ω' φ hy hy' e, pv_const, pv_const] at k
  have k2 := congrArg TrivSqZeroExt.snd k
  simp [dualMap] at k2
  simp only [map_add (f := _), map_sub, map_neg]
  linear_combination k2

end GlobalTheory.CechKS.LiftTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTorsionPointClassAtStalkEq
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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_of_valAt_eq : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (x : Sp K) (c : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) c)
    (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) c), P = Q := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ K _ _ t P Q PT QT hPT hQT x c hcP hcQ
  haveI hEt : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  let q := pq (IsLocalRing.closedPoint K)
  have hfq : (pullback.fst (torsion G n).hom (torsion G n).hom) q = PT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_fst]
  have hsq : (pullback.snd (torsion G n).hom (torsion G n).hom) q = QT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.snd (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_snd]
  haveI hdom : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk q) :=
    isDomain_stalk_of_etale (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q
  let Wp := pullback (torsion G n).hom (torsion G n).hom
  let R : Type := Wp.presheaf.stalk q
  let Ω := AlgebraicClosure (FractionRing R)
  let φ : R →+* Ω := algebraMap R Ω
  have hφ : Function.Injective φ := by
    have e : φ = (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) :=
      IsScalarTower.algebraMap_eq R (FractionRing R) Ω
    rw [e]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let ybar : Sp Ω ⟶ Spec (Wp.presheaf.stalk q) := Spec.map (CommRingCat.ofHom φ)
  haveI hyd : IsDominant ybar := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  let s0 : Sp Ω := IsLocalRing.closedPoint Ω
  have hgen : ∀ e, ybar s0 ⤳ e := by
    intro e
    have hr : Set.range ybar = {ybar s0} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨s0, rfl⟩, by rintro _ ⟨s, rfl⟩; rw [Subsingleton.elim s s0]⟩
    rw [specializes_iff_mem_closure, ← hr, ybar.denseRange.closure_range]
    trivial
  let f : Spec (Wp.presheaf.stalk q) ⟶ X' :=
    Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  obtain ⟨w', hw'q, hw'ξ⟩ := Flat.generalizingMap (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom)
    (genericPoint_specializes ((pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q))
  have hw'r : w' ∈ Set.range (Wp.fromSpecStalk q) := by rw [Scheme.range_fromSpecStalk]; exact hw'q
  obtain ⟨d, hd⟩ := hw'r
  have hξV : genericPoint X' ∈ Set.range ℓ := by
    rw [(genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range]
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, trivial, v, rfl⟩
  have hsp : (ybar ≫ f) s0 ⤳ genericPoint X' := by
    have h1 := (hgen d).map f.continuous
    have e2 : f d = (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) w' := by
      rw [← hd]; rfl
    rw [show (ybar ≫ f) s0 = f (ybar s0) from rfl, ← hw'ξ, ← e2]
    exact h1
  have H : Set.range (ybar ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s0]
    exact hsp.mem_open ℓ.isOpenEmbedding.isOpen_range hξV
  let z : Sp Ω ⟶ V := IsOpenImmersion.lift ℓ (ybar ≫ f) H
  have hz : z ≫ ℓ = ybar ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hcP' : ValAt G n ℓ w ((pullback.fst (torsion G n).hom (torsion G n).hom) q) c := by rw [hfq]; exact hcP
  have hcQ' : ValAt G n ℓ w ((pullback.snd (torsion G n).hom (torsion G n).hom) q) c := by rw [hsq]; exact hcQ
  have k1 : Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.fst (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have k2 : Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.snd (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have h1 := hcP' Ω (ybar ≫ Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k1])
  have h2 := hcQ' Ω (ybar ≫ Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k2, ← pullback.condition])
  rw [Category.assoc, reassoc_of% k1] at h1
  rw [Category.assoc, reassoc_of% k2] at h2
  have hu : Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
    refine ext_of_isDominant_of_isSeparated G.hom ?_ ybar (h1.trans h2.symm)
    simp only [Category.assoc, hιT, pullback.condition]
  have hpq : Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q = pq :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk pq
  apply Over.OverMorphism.ext
  rw [← hPT, ← hQT]
  calc PT ≫ (torsion.ι G n).left
      = pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [← Category.assoc, pullback.lift_fst]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [hu]
    _ = QT ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq, ← Category.assoc, pullback.lift_snd]

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvNatSmulMemDiscreteSubmodule
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory

theorem discrete_submodule_inv_smul_eq_zero : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → ∀ d : Fin g → ℂ, (∀ k : ℕ, 0 < k → (k : ℂ)⁻¹ • d ∈ Λ) → d = 0 := by
  intro g Λ hΛ d hd
  have hc1 : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  have hlim : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹ • d) Filter.atTop (nhds 0) := by
    simpa using hc1.smul_const d
  let f : ℕ → Λ := fun k => ⟨(((k + 1 : ℕ) : ℂ))⁻¹ • d, hd (k + 1) k.succ_pos⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [tendsto_subtype_rng]
    simpa [f] using hlim
  rw [nhds_discrete, Filter.tendsto_pure] at hf
  obtain ⟨k, hk⟩ := hf.exists
  have h0 : (((k + 1 : ℕ) : ℂ))⁻¹ • d = 0 := congrArg Subtype.val hk
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exfalso
    rw [inv_eq_zero] at h0
    exact (Nat.cast_ne_zero.mpr k.succ_ne_zero) h0
  · exact h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSqZeroBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CechPic

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res h1 (res h2 x) = res (h1.trans h2) x :=
  unit_ext fun y hy => by rw [gm_res _ y _ hy, gm_res _ y _ (h1 hy), gm_res _ y _ hy]

theorem app_restrict {X X₀ : Scheme.{0}} (i : X₀ ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (i.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (X₀.presheaf.map (homOfLE (fun y (hy : y ∈ i ⁻¹ᵁ V) => (h hy : i y ∈ U))).op).hom ((i.app U).hom x) := by
  have e := congrArg (fun q => q.hom x) (i.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

end GlobalTheory.CechPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalkOfArithBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.ZH.RatModel

theorem essFiniteType_int_stalk_of_arithBase {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω]
    [hA : ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) :
    Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o' := M.s x
  letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h := ((h₀.comp h₂).comp h₁)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  exact RingHom.ext_int _ _

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfCompEtaleSameRelativeDimension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_of_comp_etale_of_smoothOfRelativeDimension :
    ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ),
      h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY →
      Etale (h ≫ f) → Etale h := by
  intro X Y Z S h f sX sY d hs hX hY he
  subst hs
  haveI : FormallyUnramified (h ≫ f) := inferInstance
  haveI : FormallyUnramified h := FormallyUnramified.of_comp h f
  exact etale_of_formallyUnramified_of_smoothOfRelativeDimension h sY d hY hX

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianQuotientAffineCoverStatement
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianQuotient_affineCover : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∀ j : S.affineCover.I₀,
    ∃ (B : Over (S.affineCover.X j)) (_ : GrpObj B) (q : (Over.pullback (S.affineCover.f j)).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A) ≫
          (Over.pullback (S.affineCover.f j)).map i) *
          snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A))
        (snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A)) q q := by
  first | (exact @GlobalTheory.AbQuotientLocal.exists_local_quotient) | (exact GlobalTheory.AbQuotientLocal.exists_local_quotient) | (intros; apply GlobalTheory.AbQuotientLocal.exists_local_quotient  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRing
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLiftGlue

theorem exists_lift_of_split : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (e : R), IsIdempotentElem e → ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → (∀ f : R, (f = e ∨ f = 1 - e) → ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (B : Over (Sp (R₀ ⧸ Ideal.span {π f}))) (_ : GrpObj B) (i : B.left ⟶ A.left) (j : B.left ⟶ A₀.left) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π ∧ IsGrpPullback B A (spMap ρ) i ∧ IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) j ∧ IsAbelianScheme A) → ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  intro R R₀ _ _ I hI π hπ hk e he A₀ _ hA₀ H
  obtain ⟨A₁, gA₁, B₁, gB₁, i₁, j₁, ρ₁, hρ₁, hp₁, hq₁, hab₁⟩ := H e (Or.inl rfl)
  obtain ⟨A₂, gA₂, B₂, gB₂, i₂, j₂, ρ₂, hρ₂, hp₂, hq₂, hab₂⟩ := H (1 - e) (Or.inr rfl)
  have cS := _root_.GlobalTheory.specQuotIdemCoprod R e (1 - e) he (by ring)
  have cT := _root_.GlobalTheory.specQuotIdemCoprod R₀ (π e) (π (1 - e)) (he.map π) (by rw [← map_add (f := _)]; simp)
  obtain ⟨i, hi₁, hi₂, hpb⟩ := _root_.GlobalTheory.isPullback_coprod_desc_of_pieces _ _ cS _ _ cT (spMap π) (spMap ρ₁) (spMap ρ₂) (_root_.GlobalTheory.QuotBaseChange.isPullback_spMap_quot R R₀ π e ρ₁ hρ₁) (_root_.GlobalTheory.QuotBaseChange.isPullback_spMap_quot R R₀ π (1 - e) ρ₂ hρ₂)
    A₁.hom A₂.hom A₀.hom B₁.hom B₂.hom j₁ j₂ i₁ i₂ hq₁.1 hq₂.1 hp₁.1 hp₂.1
  have hsm := _root_.GlobalTheory.ProdGlue.smooth_desc_of_isColimit _ _ cS A₁.hom A₂.hom hab₁.smooth hab₂.smooth
  set X : Over (Sp R) := Over.mk (Limits.coprod.desc (A₁.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {e}))) (A₂.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {1 - e})))) with hX
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.ProdGlue.mul_glue _ _ cS _ _ cT (spMap ρ₁) (spMap ρ₂) A₁ A₂ B₁ B₂ A₀ i₁ i₂ j₁ j₂ hp₁ hp₂ hq₁ hq₂ i hi₁ hi₂
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hsm' : Smooth X.hom := hsm
  have hpb' : IsPullback i A₀.hom X.hom (spMap π) := hpb
  obtain ⟨e₁, he₁, he₁'⟩ := _root_.GlobalTheory.SecLift.exists_section_lift R R₀ π hπ hnil X A₀ i hpb' hsm' (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left (Over.w _)
  have hw : ∀ g : A₀ ⊗ A₀ ⟶ A₀, (g.left ≫ i) ≫ X.hom = (Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π)).hom := fun g ↦ by
    simp only [Over.mk_hom, Category.assoc, hpb'.w]; rw [← Category.assoc, Over.w]
  let l : Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π) ⟶ X ⊗ X := lift (Over.homMk _ (hw (fst A₀ A₀))) (Over.homMk _ (hw (snd A₀ A₀)))
  have hl₁ : l.left ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hl₂ : l.left ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨g, hg, hab⟩ := _root_.GlobalTheory.LiftGroupLaw.exists_grpObj_isAbelianScheme R R₀ π hπ hnil A₀ hA₀ X i hpb' hsm' e₁ he₁ he₁' l.left hl₁ hl₂ m (hm l.left hl₁ hl₂)
  exact ⟨X, g, i, hg, hab⟩

end GlobalTheory.AbLiftGlue
end

