module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0004
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0001
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiPtsA
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

def fourfoldProductLift {X G : Over S} (c : Fin 4 → (X ⟶ G)) : X ⟶ G4 G := lift (c 0) (lift (c 1) (lift (c 2) (c 3)))

variable {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def eMap (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) * (∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))⁻¹)
    ((prj _ i ≫ snd A B) ^ (2 * m))

def eMap' (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) ^ (2 * m) * ∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))
    (prj _ i ≫ snd A B)

def lPart (mu : B ⟶ A) {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) :
    LB ((Over.pullback s).obj (G4 (A ⊗ B))).left :=
  LB.LinComb L (phiL mu s) fun _ => 1

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KilledAnyOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

open TensorProduct

namespace PositivityTheory.PrwZar.QiP

open GlobalTheory.CompanionTheory.Ar.GR

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Field C] [Algebra R C] {F : Type} [CommRing F] [Algebra R F]

def uu : F →ₐ[R] (C ⊗[R] F) := (Algebra.TensorProduct.includeRight : F →ₐ[R] C ⊗[R] F)

def lft {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    (C ⊗[R] F) →ₐ[C] T :=
  Algebra.TensorProduct.lift (Algebra.ofId C T) g (fun _ _ => Commute.all _ _)

theorem lft_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    ((lft g).restrictScalars R).comp (uu (C := C)) = g := by
  ext x
  simp [lft, uu]

theorem ext_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T]
    (x y : (C ⊗[R] F) →ₐ[C] T)
    (e : (x.restrictScalars R).comp (uu (C := C)) = (y.restrictScalars R).comp (uu (C := C))) : x = y := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · exact e

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def u1 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeLeft : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def u2 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeRight : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def dlt (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  lft (mulPt hs (u1 (C := C)) u2)

def eps (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] C :=
  lft (onePt hs C)

theorem eps_uu (hs : IsFinFlatSub G F h) :
    ((((Algebra.ofId C (C ⊗[R] F)).comp (eps (C := C) hs)).restrictScalars R).comp (uu (C := C))) = onePt hs (C ⊗[R] F) := by
  rw [← comp_onePt hs ((Algebra.ofId C (C ⊗[R] F)).restrictScalars R), ← lft_uu (C := C) (onePt hs C)]
  rfl

theorem mul_dlt_uu (hs : IsFinFlatSub G F h) (f g : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F)) :
    ((((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C))) = mulPt hs ((f.restrictScalars R).comp uu) ((g.restrictScalars R).comp uu) := by
  have e : (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C)) = ((((Algebra.TensorProduct.lmul' C).comp (Algebra.TensorProduct.map f g))).restrictScalars R).comp
        (((dlt (C := C) hs).restrictScalars R).comp uu) := rfl
  rw [e, dlt, lft_uu, comp_mulPt]
  congr 1
  · ext x
    simp [u1, uu]
  · ext x
    simp [u2, uu]

theorem counitL (hs : IsFinFlatSub G F h) : Qi.CounitL (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt hs _

theorem counitR (hs : IsFinFlatSub G F h) : Qi.CounitR (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt' hs _

theorem pw_uu (hs : IsFinFlatSub G F h) (n : ℕ) :
    ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n).restrictScalars R).comp uu = powPt hs uu n := by
  induction n with
  | zero => exact eps_uu hs
  | succ n ih =>
    change (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n)
      (AlgHom.id C (C ⊗[R] F))).comp (dlt (C := C) hs))).restrictScalars R).comp uu = _
    rw [mul_dlt_uu, ih]
    rfl

theorem pw_mul (hs : IsFinFlatSub G F h) (a b : ℕ) :
    Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (a * b) = (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b) := by
  apply ext_uu
  rw [pw_uu, powPt_mul]
  have hc : (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b)).restrictScalars R).comp
      (uu (C := C)) = ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b).restrictScalars R).comp uu) := rfl
  rw [hc, pw_uu, comp_powPt, pw_uu]

def ptGrp (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : Subgroup (sp (R₀ := R) S ⟶ G) where
  carrier := {g | ∃ φ : F →ₐ[R] S, spMap φ ≫ h = g}
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨φ', rfl⟩
    exact ⟨mulPt hs φ φ', mulPt_spec hs φ φ'⟩
  one_mem' := ⟨onePt hs S, onePt_spec hs S⟩
  inv_mem' := by
    rintro _ ⟨φ, rfl⟩
    obtain ⟨χ, hχ⟩ := hs.inv S φ
    exact ⟨χ, eq_inv_of_mul_eq_one_left hχ⟩

theorem pts_killed [Module.Finite R F] (hs : IsFinFlatSub G F h) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (C ⊗[R] F) →ₐ[C] C, x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) m) = eps hs := by
  haveI : Finite (ptGrp hs C) :=
    Finite.of_surjective (fun φ : F →ₐ[R] C => (⟨_, φ, rfl⟩ : ptGrp hs C))
      (by rintro ⟨_, φ, rfl⟩; exact ⟨φ, rfl⟩)
  refine ⟨Nat.card (ptGrp hs C), Nat.card_pos, fun x => ?_⟩
  apply ext_uu
  have hx : ((x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C)))).restrictScalars R).comp
      (uu (C := C)) = (x.restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C))).restrictScalars R).comp uu) := rfl
  have he : ((eps (C := C) hs).restrictScalars R).comp uu = onePt hs C := lft_uu _
  rw [hx, pw_uu, comp_powPt, he]
  apply pt_ext hs
  rw [powPt_spec, onePt_spec]
  have h1 := pow_card_eq_one' (G := ptGrp hs C) (x := ⟨_, (x.restrictScalars R).comp uu, rfl⟩)
  exact congrArg Subtype.val h1

theorem uu_injective [Module.Flat R F] (hR : Function.Injective (algebraMap R C)) :
    Function.Injective (uu (R := R) (C := C) (F := F)) := Algebra.TensorProduct.includeRight_injective hR

end BaseChange

end PositivityTheory.PrwZar.QiP

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR QiP

theorem killedAny_of (hc : Qi.KilledCore) : KilledAny := by
  intro C _ _ v R _ _ hv G _ _ F _ _ h hs
  haveI := hs.fin
  haveI := hs.proj
  obtain ⟨N, hN0, hN⟩ := hc C (C ⊗[R] F) (dlt (C := C) hs) (eps hs) (counitL hs) (counitR hs) (pw_mul hs)
    (pts_killed hs)
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have key : powPt hs (AlgHom.id R F) N = onePt hs F := by
    have e1 := pw_uu (C := C) hs N
    have e0 := pw_uu (C := C) hs 0
    rw [hN, e0] at e1
    have a1 : (uu (R := R) (C := C) (F := F)).comp (powPt hs (AlgHom.id R F) N) = powPt hs uu N := by
      rw [comp_powPt, AlgHom.comp_id]
    have a0 : (uu (R := R) (C := C) (F := F)).comp (onePt hs F) = powPt hs uu 0 := by
      rw [comp_onePt]
      rfl
    ext y
    apply uu_injective (C := C) hinj
    exact congrArg (fun f => f y) (a1.trans (e1.symm.trans a0.symm))
  refine ⟨N, hN0, fun S _ _ φ => ?_⟩
  rw [← powPt_spec hs, ← onePt_spec hs S]
  have e : φ.comp (powPt hs (AlgHom.id R F) N) = φ.comp (onePt hs F) := by rw [key]
  rw [comp_powPt, comp_onePt, AlgHom.comp_id] at e
  rw [e]

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PfiFRangeFiniteClosed
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

private theorem pfiF_fib_subset_lemma {G' : Over (Sp Ω)} (σ : 𝟙_ (Over (Sp Ω)) ⟶ G') {K : Type} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ G'.left) (p : (𝟙_ (Over (Sp Ω))).left)
    (ha : a (IsLocalRing.closedPoint K) = σ.left p) :
    a = (a ≫ G'.hom) ≫ σ.left := by
  have sec : σ.left ≫ G'.hom = 𝟙 _ := by simpa using Over.w σ
  obtain ⟨τ, hτ⟩ := GlobalTheory.exists_factor_of_lift_fromSpecResidueField G'.hom p
    (Scheme.fromSpecResidueField _ p ≫ σ.left)
    (by rw [Category.assoc, sec, Category.comp_id]; rfl) a
    (ha.trans (congrArg (fun q => σ.left q) (Scheme.fromSpecResidueField_apply p _)).symm)
  rw [← hτ]
  simp only [Category.assoc, sec, Category.comp_id]

theorem pfiF_range_finite_closed {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom) :
    (Set.range j.left).Finite ∧ ∀ z ∈ Set.range j.left, IsClosed ({z} : Set G.left) := by
  haveI : IsFinite H.hom := hH
  haveI : IsProper G.hom := hG.proper
  haveI : IsLocallyArtinian H.left := .of_locallyQuasiFinite H.hom
  haveI : CompactSpace H.left := QuasiCompact.compactSpace_of_compactSpace H.hom
  haveI : IsProper (j.left ≫ G.hom) := by rw [Over.w j]; infer_instance
  haveI : IsProper j.left := IsProper.of_comp j.left G.hom
  haveI : Finite H.left := finite_of_compact_of_discrete
  refine ⟨Set.finite_range _, ?_⟩
  rintro _ ⟨h, rfl⟩
  have hc := j.left.isClosedMap {h} (isClosed_discrete _)
  simpa [Set.image_singleton] using hc

private theorem pfiF_fib_closed_lemma_2 {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (s : 𝟙_ (Over (Sp Ω)) ⟶ G) (p : (𝟙_ (Over (Sp Ω))).left) (y : G.left)
    (hy : f.left y = f.left (s.left p)) : y ∈ Set.range (j * (toUnit H ≫ s)).left := by
  let T : Over (Sp Ω) := Over.mk (G.left.fromSpecResidueField y ≫ G.hom)
  let x : T ⟶ G := Over.homMk (G.left.fromSpecResidueField y) rfl
  let c : T ⟶ G := toUnit T ≫ s
  have e1 := Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint (G.left.residueField y))
  have hfy : (G.left.fromSpecResidueField y ≫ f.left) (IsLocalRing.closedPoint _) =
      (s ≫ f).left p :=
    (congrArg f.left e1).trans hy
  have key := pfiF_fib_subset_lemma (s ≫ f) (G.left.fromSpecResidueField y ≫ f.left) p hfy
  have hxc : x ≫ f = c ≫ f := by
    apply Over.OverMorphism.ext
    change G.left.fromSpecResidueField y ≫ f.left = (toUnit T ≫ (s ≫ f)).left
    have hb : (G.left.fromSpecResidueField y ≫ f.left) ≫ G'.hom = (toUnit T).left := by
      simp [T]
    rw [Over.comp_left]
    exact key.trans (congrArg (· ≫ (s ≫ f).left) hb)
  have hx' : (x * c⁻¹) ≫ f = 1 := by
    change (IsMonHom.monoidHom f T) (x * c⁻¹) = 1
    rw [map_mul, map_inv]
    change (x ≫ f) * (c ≫ f)⁻¹ = 1
    rw [hxc, mul_inv_cancel]
  obtain ⟨z, hz⟩ := hj T _ hx'
  have hxz : x = z ≫ (j * (toUnit H ≫ s)) := by
    have hm : z ≫ (j * (toUnit H ≫ s)) = (z ≫ j) * c := by
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc z (toUnit H) s,
        toUnit_unique (z ≫ toUnit H) (toUnit T)]
    rw [hm, hz, inv_mul_cancel_right]
  refine ⟨z.left (IsLocalRing.closedPoint (G.left.residueField y)), ?_⟩
  have h2 := congrArg
    (fun g : T ⟶ G => g.left (IsLocalRing.closedPoint (G.left.residueField y))) hxz
  exact h2.symm.trans e1

theorem pfiF_fib_closed {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G) (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (x : G.left) (hx : IsClosed ({x} : Set G.left)) :
    (f.left ⁻¹' {f.left x}).Finite ∧ ∀ z ∈ f.left ⁻¹' {f.left x}, IsClosed ({z} : Set G.left) := by
  haveI : LocallyOfFiniteType G.hom := by haveI := hG.smooth; infer_instance
  obtain ⟨s, hs⟩ := GlobalTheory.RationalPoint.exists_pt_mem (X := G) hx ⟨x, rfl⟩
  have hsx : s.left (IsLocalRing.closedPoint Ω) = x := hs
  have hsub : f.left ⁻¹' {f.left x} ⊆ Set.range (j * (toUnit H ≫ s)).left := fun y hy =>
    pfiF_fib_closed_lemma_2 f H j hj s (IsLocalRing.closedPoint Ω) y
      ((hy : f.left y = f.left x).trans (congrArg f.left hsx).symm)
  obtain ⟨hfin, hcl⟩ := pfiF_range_finite_closed hG H (j * (toUnit H ≫ s)) hH
  exact ⟨hfin.subset hsub, fun z hz => hcl z (hsub hz)⟩

theorem isFinite_of_ker {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (f : G ⟶ G') [IsMonHom f] (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x) : IsFinite f.left := by
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper G'.hom := hG'.proper
  haveI : IsProper (f.left ≫ G'.hom) := by rw [Over.w f]; infer_instance
  haveI : IsProper f.left := IsProper.of_comp f.left G'.hom
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G.hom
  haveI : LocallyQuasiFinite f.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints f.left fun y hy =>
      (pfiF_fib_closed hG f H j hH hj y hy).1
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

end PositivityTheory.PrwZar.Z2
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.SurjOfFiniteDimS
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem surj_of_finite_dimS {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] (g : ℕ)
    (hX : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = g)
    (hY : ∀ y : Y, IsClosed ({y} : Set Y) → ringKrullDim (Y.presheaf.stalk y) = g)
    (o : X) (ho : IsClosed ({o} : Set X)) : Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  suffices hη : genericPoint Y ∈ Set.range f by
    have hsub : closure ({genericPoint Y} : Set Y) ⊆ Set.range f :=
      closure_minimal (Set.singleton_subset_iff.mpr hη) hcl
    have hc : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
    rw [hc] at hsub
    exact hsub (Set.mem_univ y)
  by_contra hη
  have hmono : StrictMono f := GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite f
  let F : WithTop X → Y := fun a => WithTop.recTopCoe (genericPoint Y) (fun x => f x) a
  have hF : StrictMono F := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top =>
        refine lt_of_le_of_ne (genericPoint_specializes (f a)) ?_
        intro h
        have hi : Inseparable (f a) (genericPoint Y) := h.symm
        exact hη ⟨a, hi.eq⟩
      | coe b => exact hmono (WithTop.coe_lt_coe.mp hab)
  have h1 := Order.coheight_le_coheight_apply_of_strictMono F hF (o : WithTop X)
  rw [Order.coheight_coe_withTop] at h1
  have hfo : IsClosed ({f o} : Set Y) := by
    have := f.isClosedMap _ ho
    rwa [Set.image_singleton] at this
  have e1 := hX o ho
  have e2 := hY (f o) hfo
  rw [ringKrullDim_stalk_eq_coheight] at e1 e2
  have e1' : Order.coheight o = g := by exact_mod_cast e1
  have e2' : Order.coheight (f o) = g := by exact_mod_cast e2
  change Order.coheight o + 1 ≤ Order.coheight (f o) at h1
  rw [e1', e2'] at h1
  exact absurd h1 (by norm_cast; omega)

theorem isClosed_originS {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] [IsProper G.hom] :
    IsClosed ({η[G].left (IsLocalRing.closedPoint Ω)} : Set G.left) := by
  have hc : IsClosed ({IsLocalRing.closedPoint Ω} : Set (Sp Ω)) := isClosed_singleton
  have h1 := (η[G].left).isClosedEmbedding.isClosedMap _ hc
  convert h1 using 1
  exact (Set.image_singleton).symm

theorem flat_surj_of_finite {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (g : ℕ) (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (f : G ⟶ G') [IsMonHom f] (hf : IsFinite f.left) :
    Flat f.left ∧ Surjective f.left := by
  haveI := hG.smooth
  haveI := hG'.smooth
  haveI := hG.proper
  haveI := hG'.proper
  haveI := hf
  haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G hG
  haveI : AlgebraicGeometry.IsIntegral G'.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G' hG'
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hsurj : Surjective f.left :=
    surj_of_finite_dimS f.left g
      (fun x hx => GlobalTheory.CutDegree.ringKrullDim_stalk hgG hx)
      (fun y hy => GlobalTheory.CutDegree.ringKrullDim_stalk hgG' hy)
      _ (isClosed_originS (G := G))
  haveI := hsurj
  exact ⟨GlobalTheory.SS.flat_of_isDominant_grpHom Ω G G' f, hsurj⟩

end PositivityTheory.PrwZar.Z2
end
end

