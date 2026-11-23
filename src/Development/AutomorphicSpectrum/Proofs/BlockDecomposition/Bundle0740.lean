module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0735
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

abbrev Hc {S A B C : Type} [CommRing S] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C] (f : A →ₗ[S] B) (g : B →ₗ[S] C) : Type :=
  LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype

def Lift {A Q N : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (b : Q →ₗ[A] N) : Prop :=
  ∀ (J : Ideal A) (t : A), J ≠ ⊤ → (∀ x ∈ IsLocalRing.maximalIdeal A, x * t ∈ J) → ∀ z : Q,
    b z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A N) →
    ∃ x : Q, b x ∈ J • (⊤ : Submodule A N) ∧
      x - z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A Q)

def SmallLift {R P₀ P₁ P₂ : Type} [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁)
    (a₁ : P₁ →ₗ[R] P₂) : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B), (∀ x, ¬ IsUnit x → x * t = 0) →
    ∀ z : (B ⧸ Ideal.span {t}) ⊗[R] P₁, a₁.lTensor _ z = 0 →
    ∃ (x : B ⊗[R] P₁) (y : (B ⧸ Ideal.span {t}) ⊗[R] P₀), a₁.lTensor B x = 0 ∧
      (Ideal.Quotient.mkₐ R (Ideal.span {t})).toLinearMap.rTensor P₁ x - z = a₀.lTensor _ y

section Semi

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

def liftSemi {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) : S ⊗[R] M →ₗ[S] N :=
  letI : Module R N := Module.compHom N (algebraMap R S)
  haveI : IsScalarTower R S N := ⟨fun r s n ↦ by
    change (r • s) • n = algebraMap R S r • s • n
    rw [Algebra.smul_def, mul_smul]⟩
  LinearMap.liftBaseChange S
    { toFun := f, map_add' := f.map_add, map_smul' := fun r x ↦ f.map_smulₛₗ r x }

theorem liftSemi_tmul {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) (s : S) (x : M) : liftSemi f (s ⊗ₜ x) = s • f x := by
  simp [liftSemi]

end Semi

section Cochains

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

def c0 (m : BC F F') : C0 F →ₛₗ[algebraMap R S] C0 F' where
  toFun f T := m.α T (f T)
  map_add' f g := funext fun T ↦ map_add (m.α T) _ _
  map_smul' r f := funext fun T ↦ m.smul T r (f T)

def c1 (m : BC F F') : C1 F →ₛₗ[algebraMap R S] C1 F' where
  toFun f T T' φ := m.α T' (f T T' φ)
  map_add' f g := funext fun T ↦ funext fun T' ↦ funext fun φ ↦ map_add (m.α T') _ _
  map_smul' r f := funext fun T ↦ funext fun T' ↦ funext fun φ ↦ m.smul T' r (f T T' φ)

def c2 (m : BC F F') : C2 F →ₛₗ[algebraMap R S] C2 F' where
  toFun f T T' T'' φ ψ := m.α T'' (f T T' T'' φ ψ)
  map_add' f g := funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦
    map_add (m.α T'') _ _
  map_smul' r f := funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦
    m.smul T'' r (f T T' T'' φ ψ)

def th0 (m : BC F F') : S ⊗[R] C0 F →ₗ[S] C0 F' := liftSemi (c0 m)

def th1 (m : BC F F') : S ⊗[R] C1 F →ₗ[S] C1 F' := liftSemi (c1 m)

def th2 (m : BC F F') : S ⊗[R] C2 F →ₗ[S] C2 F' := liftSemi (c2 m)

end Cochains

def IsModel {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀]
    [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F)
    (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) : Prop :=
  a₁ ∘ₗ a₀ = 0 ∧ ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀ ∧ ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁ ∧
    ∀ M : ModuleCat.{0} R,
      QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] C0 F) ((d0 F).lTensor M)
        (ψ₀.lTensor M) ∧
      QIsoAt (a₀.lTensor M) (a₁.lTensor M) ((d0 F).lTensor M) ((d1 F).lTensor M) (ψ₁.lTensor M)

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalPropertyAffineIdealCriterion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc.Rep

theorem exists_basicOpen_le {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (r : Γ(Y, V)) (y : Y) (hyU : y ∈ U) (hyr : y ∈ Y.basicOpen r) :
    ∃ f : Γ(Y, U), y ∈ Y.basicOpen f ∧ Y.basicOpen f ≤ Y.basicOpen r := by
  obtain ⟨f, g, e, hy⟩ := exists_basicOpen_le_affine_inter hU (hV.basicOpen r) y ⟨hyU, hyr⟩
  exact ⟨f, hy, e ▸ Y.basicOpen_le g⟩

theorem isUnit_res_of_le {Y : Scheme.{0}} {V W : Y.Opens} (r : Γ(Y, V)) (hle : W ≤ Y.basicOpen r)
    (hWV : W ≤ V) : IsUnit ((Y.presheaf.map (homOfLE hWV).op).hom r) := by
  have h := Y.toRingedSpace.isUnit_res_basicOpen r
  have e : (Y.presheaf.map (homOfLE hWV).op).hom r =
      (Y.presheaf.map (homOfLE hle).op).hom
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact h.map (Y.presheaf.map (homOfLE hle).op).hom

theorem exists_ideal_on_basicOpen {Y : Scheme.{0}} (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (f : Γ(Y, U)) (r : Γ(Y, V))
    (I : Ideal Γ(Y, V)) (hle : Y.basicOpen f ≤ Y.basicOpen r)
    (hI : ∀ (R' : Type) [CommRing R'] (g : Γ(Y, V) →+* R'), IsUnit (g r) →
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) ↔ I ≤ RingHom.ker g)) :
    ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g f) →
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  have hWV : Y.basicOpen f ≤ V := hle.trans (Y.basicOpen_le r)
  let resV : Γ(Y, V) →+* Γ(Y, Y.basicOpen f) := (Y.presheaf.map (homOfLE hWV).op).hom
  let I₂ : Ideal Γ(Y, Y.basicOpen f) := I.map resV
  haveI := hU.isLocalization_basicOpen f
  refine ⟨I₂.comap (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f)), fun R' _ g hu => ?_⟩
  let h' : Γ(Y, Y.basicOpen f) →+* R' := IsLocalization.Away.lift f hu
  have hcomp : h'.comp (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f)) = g := IsLocalization.Away.lift_comp f hu
  have hW := hU.basicOpen f
  have hg : CommRingCat.ofHom g =
      Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op ≫ CommRingCat.ofHom h' := by
    rw [← hcomp]; rfl
  have hg' : CommRingCat.ofHom (h'.comp resV) =
      Y.presheaf.map (homOfLE hWV).op ≫ CommRingCat.ofHom h' := rfl
  have e : Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (h'.comp resV)) ≫ hV.fromSpec := by
    rw [hg, hg', Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      hU.map_fromSpec hW, hV.map_fromSpec hW]
  have hunit : IsUnit ((h'.comp resV) r) := (isUnit_res_of_le r hle hWV).map h'
  rw [e, hI R' _ hunit]
  constructor
  · intro h x hx
    have hx' : algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) x ∈ I₂ := hx
    have h2 : I₂ ≤ RingHom.ker h' := by
      rw [show I₂ = I.map resV from rfl, Ideal.map_le_iff_le_comap]
      intro z hz
      exact h hz
    have := h2 hx'
    rw [RingHom.mem_ker] at this ⊢
    rw [← hcomp]
    exact this
  · intro h z hz
    have h2 : I₂ ≤ RingHom.ker h' := by
      rw [← IsLocalization.map_under (Submonoid.powers f) Γ(Y, Y.basicOpen f) I₂, Ideal.map_le_iff_le_comap]
      intro x hx
      have := h hx
      rw [RingHom.mem_ker] at this
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [← hcomp] at this
      exact this
    exact h2 (Ideal.mem_map_of_mem resV hz)

theorem local_on_affine {Y : Scheme.{0}} (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    {U : Y.Opens} (hU : IsAffineOpen U) (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R') (s : Set R')
    (hs : Ideal.span s = ⊤)
    (hQ : ∀ a ∈ s, P (Spec (CommRingCat.of (Localization.Away a)))
      (Spec.map (CommRingCat.ofHom ((algebraMap R' (Localization.Away a)).comp g)) ≫ hU.fromSpec)) :
    P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) := by
  refine loc _ _ fun x => ?_
  let x' : PrimeSpectrum R' := x
  have hx : ∃ a ∈ s, a ∉ x'.asIdeal := by
    by_contra hcon
    push Not at hcon
    have : Ideal.span s ≤ x'.asIdeal := Ideal.span_le.2 hcon
    rw [hs] at this
    exact x'.2.ne_top (top_le_iff.1 this)
  obtain ⟨a, ha, hax⟩ := hx
  let j : Spec (CommRingCat.of (Localization.Away a)) ⟶ Spec (CommRingCat.of R') :=
    Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away a)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization a
  refine ⟨j.opensRange, ?_, ?_⟩
  · have h := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    have hx' : x' ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away a))) := by
      rw [h]; exact hax
    obtain ⟨z, hz⟩ := hx'
    exact ⟨z, hz⟩
  · have h0 := hQ a ha
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at h0
    have h1 := stab _ _ j.isoOpensRange.inv _ h0
    rwa [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] at h1

theorem exists_ideal_on_affine : ∀ (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop),
    (∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t) →
    (∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) →
    ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  intro Y P stab loc hloc U hU
  let Q : ∀ (R' : Type) [CommRing R'], (Γ(Y, U) →+* R') → Prop := fun R' _ g =>
    P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec)
  let S : Set Γ(Y, U) := {f | ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
    IsUnit (g f) → (Q R' g ↔ J ≤ RingHom.ker g)}
  have hS : Ideal.span S = ⊤ := by
    refine hU.self_le_iSup_basicOpen_iff.1 fun y hy => ?_
    obtain ⟨V, hV, r, I, hyr, hI⟩ := hloc y
    obtain ⟨f, hyf, hle⟩ := exists_basicOpen_le hU hV r y hy hyr
    have hf : f ∈ S := exists_ideal_on_basicOpen P hU hV f r I hle hI
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨s, hsS, hs⟩ := (Ideal.span_eq_top_iff_finite S).1 hS
  have hS' : ∀ f, f ∈ S → ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
    IsUnit (g f) → (Q R' g ↔ J ≤ RingHom.ker g) := fun _ h => h
  choose! I hI using hS'
  refine exists_ideal_of_local Q ?_ ?_ s hs I fun f hf => hI f (hsS hf)
  · intro R' R'' _ _ g h hq
    have := stab _ _ (Spec.map (CommRingCat.ofHom h)) _ hq
    change P _ _
    rwa [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at this
  · intro R' _ g s hs hQ
    exact local_on_affine P stab loc hU R' g s hs hQ

end GlobalTheory.CompanionTheory.TrivLoc.Rep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfModels
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.SpreadingModels

theorem perfAll_of_hasModel
    (hModel : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → HasModel f M) : PerfAll :=
  perfAll_of_models GlobalTheory.T.perfect_base_change _root_.GlobalTheory.CompanionTheory.PerfIso.perf_of_iso hModel

end GlobalTheory.CompanionTheory.SpreadingModels
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveTorsorClassAdditive
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SmallLift

theorem primitive_HO1_abelian : DescentSt → LowSt → AxOSt → AllAb fun _ _ A _ _ ↦ ∀ (c : HO1 A.hom) (a b d : HO1 (A ⊗ A).hom), IsPullO (wOver (fst A A * snd A A)) c a → IsPullO (wOver (fst A A)) c b → IsPullO (wOver (snd A A)) c d → a = b + d := by
  intro _ _ hAx R _ A _ g hA hg c a b d ha hb hd
  have hm : fst A A * snd A A = μ[A] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have p := GlobalTheory.CompanionTheory.HopfSys.primitive_structure_sheaf_cohomology_class A (hAx R A g hA hg) c
  revert ha
  rw [hm]
  intro ha
  rw [ha.eq_pullHO1, hb.eq_pullHO1, hd.eq_pullHO1]
  exact p

end GlobalTheory.CompanionTheory.SmallLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperIntegralPerfectFamilyExists
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem isPullback_lift_snd {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (lift (fst A X) (snd A X ≫ q)).left (snd A X).left (snd A Y).left q.left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact IsPullback.of_right hout e₂ hY

theorem triv_pull_iso {P Q X : Scheme.{0}} {L : LB X} (e : P ≅ Q) (a : Q ⟶ X) :
    Triv (L.pull (e.hom ≫ a)) ↔ Triv (L.pull a) := by
  constructor
  · intro h
    have := GlobalTheory.Biadditive.triv_pull_comp h e.inv
    rwa [Iso.inv_hom_id_assoc] at this
  · intro h
    exact GlobalTheory.Biadditive.triv_pull_comp h e.hom

theorem triv_pull_iff_locus {S : Scheme.{0}} {A Y T₀ : Over S} (N : LB (A ⊗ Y).left) (v : T₀ ⟶ Y)
    {W X' : Scheme.{0}} (t : W ⟶ T₀.left) (π : X' ⟶ (A ⊗ T₀).left) (f' : X' ⟶ W)
    (h : IsPullback π f' (snd A T₀).left t) :
    Triv ((ev N (fst A T₀) (snd A T₀ ≫ v)).pull π) ↔ Locus N (t ≫ v.left) := by
  let T' : Over S := Over.mk ((t ≫ v.left) ≫ Y.hom)
  let u : T' ⟶ T₀ := Over.homMk t (by simp [T'])
  let w : T' ⟶ Y := Over.homMk (t ≫ v.left) rfl
  have huv : u ≫ v = w := by ext; simp [u, w]
  have hp : IsPullback (lift (fst A T') (snd A T' ≫ u)).left (snd A T').left (snd A T₀).left t :=
    isPullback_lift_snd A T' T₀ u
  let e : X' ≅ (A ⊗ T').left := h.isoIsPullback _ _ hp
  have he : e.hom ≫ (lift (fst A T') (snd A T' ≫ u)).left = π := h.isoIsPullback_hom_fst _ _ hp
  have hc : (lift (fst A T') (snd A T' ≫ u)).left ≫ (lift (fst A T₀) (snd A T₀ ≫ v)).left =
      (lift (fst A T') (snd A T' ≫ w)).left := by
    rw [← Over.comp_left, ← huv]
    congr 1
    ext <;> simp
  have h1 : Triv ((ev N (fst A T₀) (snd A T₀ ≫ v)).pull π) ↔
      Triv (N.pull (π ≫ (lift (fst A T₀) (snd A T₀ ≫ v)).left)) :=
    GlobalTheory.AbLaw.CubeGen.triv_pull_iff N (fun _ : PUnit => (lift (fst A T₀) (snd A T₀ ≫ v)).left) (fun _ => 1) π
  rw [h1, ← he, Category.assoc, hc, triv_pull_iso]
  rfl

theorem family_props {R : Type} [CommRing R] [IsNoetherianRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsProper f] [GeometricallyConnected f] (s : Spec (CommRingCat.of R) ⟶ W) (hs : s ≫ f = 𝟙 _)
    {M : LB W} (hM : M.IsLB) :
    Nonempty (Perf f M) ∧ Nonempty (Perf f (pw M (-1))) ∧ GeometricallyIntegral f ∧ Surjective f := by
  refine ⟨GlobalTheory.ProperFinite.nonempty_perf_of_isProper (R := R) f hM,
    GlobalTheory.ProperFinite.nonempty_perf_of_isProper (R := R) f (isLB_pw hM _),
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance, ?_⟩
  have : Surjective (s ≫ f) := by rw [hs]; infer_instance
  exact Surjective.of_comp s f

theorem exists_chart_family : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (j : Spec (CommRingCat.of R) ⟶ Y.left),
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB ∧ Nonempty (Perf f M) ∧
      Nonempty (Perf f (pw M (-1))) ∧ IsProper f ∧ GeometricallyIntegral f ∧ Surjective f ∧
      (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
        IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
        (Triv (M.pull π) ↔ Locus N (Spec.map (CommRingCat.ofHom g) ≫ j)) := by
  intro S A Y _ hA N hN R _ _ j
  have hB : IsAbelianScheme ((Over.pullback (j ≫ Y.hom)).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA (j ≫ Y.hom)
  let T₀ : Over S := Over.mk (j ≫ Y.hom)
  let v : T₀ ⟶ Y := Over.homMk j rfl
  let f : (A ⊗ T₀).left ⟶ Spec (CommRingCat.of R) := (snd A T₀).left
  let M : LB (A ⊗ T₀).left := ev N (fst A T₀) (snd A T₀ ≫ v)
  have hM : M.IsLB := pull_isLB hN _
  have sm : Smooth f := hB.smooth
  have pr : IsProper f := hB.proper
  have gc : GeometricallyConnected f := hB.geomConnected
  let s : Spec (CommRingCat.of R) ⟶ (A ⊗ T₀).left := (η[(Over.pullback (j ≫ Y.hom)).obj A]).left
  have hs : s ≫ f = 𝟙 _ := Over.w (η[(Over.pullback (j ≫ Y.hom)).obj A])
  obtain ⟨p₁, p₂, p₃, p₄⟩ := family_props f s hs hM
  refine ⟨(A ⊗ T₀).left, f, M, hM, p₁, p₂, pr, p₃, p₄, ?_, ?_⟩
  · intro K _ g₀ X₀ π₀ f₀ h
    exact GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.globalFns_holds _ hB h
  · intro R' _ g X' π f' h
    exact triv_pull_iff_locus N v _ π f' h

end GlobalTheory.CompanionTheory.TrivLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StalkIdealRepresentsClosedSubscheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.StalkIdeal

theorem exists_stalk_ideal : ∀ (X Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (x : X), x ∈ Set.range i → (∀ z : Z, IsClosed ({z} : Set Z)) → ∃ I : Ideal (X.presheaf.stalk x), I ≠ ⊤ ∧ (∀ q : Ideal (X.presheaf.stalk x), q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧ ∀ J : Ideal (X.presheaf.stalk x), (∃ z : Sp (X.presheaf.stalk x ⧸ J) ⟶ Z, z ≫ i = spMap (Ideal.Quotient.mk J) ≫ X.fromSpecStalk x) ↔ I ≤ J := by
  intro X Z i _ x hx hcl
  have hq : IsClosedImmersion (pullback.snd i (X.fromSpecStalk x)) := inferInstance
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.1 hq
  have hpt : ∀ p : ↥(pullback i (X.fromSpecStalk x)),
      X.fromSpecStalk x (pullback.snd i (X.fromSpecStalk x) p) =
        i (pullback.fst i (X.fromSpecStalk x) p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hsnd : ∀ s : ↥(Spec (CommRingCat.of (X.presheaf.stalk x ⧸ I))),
      pullback.snd i (X.fromSpecStalk x) (e.inv s) = PrimeSpectrum.comap (Ideal.Quotient.mk I) s := by
    intro s
    rw [he, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, Iso.inv_hom_id]
    rfl
  refine ⟨I, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hx
    obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := X.fromSpecStalk x)
      z (IsLocalRing.closedPoint _) (by rw [Scheme.fromSpecStalk_closedPoint, hz])
    have hs : (show PrimeSpectrum (X.presheaf.stalk x ⧸ I) from e.hom p).asIdeal.IsPrime :=
      PrimeSpectrum.isPrime _
    rw [← Ideal.Quotient.nontrivial_iff]
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hs.ne_top (Subsingleton.elim _ _)
  · intro q hq hIq
    have hQ : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    let Q0 : PrimeSpectrum (X.presheaf.stalk x ⧸ I) := ⟨_, hQ⟩
    let Q : ↥(Spec (CommRingCat.of (X.presheaf.stalk x ⧸ I))) := Q0
    let P : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, hq⟩
    have hPQ : PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = P := by
      ext1
      show Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) = q
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hIq]
    have h1 : X.fromSpecStalk x P = i (pullback.fst i (X.fromSpecStalk x) (e.inv Q)) := by
      rw [← hPQ, ← hsnd, hpt]
    have hspec : P ⤳ IsLocalRing.closedPoint (X.presheaf.stalk x) := by
      rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
      exact IsLocalRing.le_maximalIdeal hq.ne_top
    have h2 : X.fromSpecStalk x P ⤳ x := by
      have := hspec.map (X.fromSpecStalk x).continuous
      rwa [Scheme.fromSpecStalk_closedPoint] at this
    have hclosed : IsClosed ({i (pullback.fst i (X.fromSpecStalk x) (e.inv Q))} : Set X) := by
      rw [← Set.image_singleton]
      exact i.isClosedEmbedding.isClosedMap _ (hcl _)
    have h3 : x = X.fromSpecStalk x P := by
      have := h2.mem_closed hclosed (by rw [h1]; exact Set.mem_singleton _)
      rw [Set.mem_singleton_iff] at this
      exact this.trans h1.symm
    have h4 : P = IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      (X.fromSpecStalk x).isEmbedding.injective (by rw [Scheme.fromSpecStalk_closedPoint]; exact h3.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  · intro J
    constructor
    · rintro ⟨z, hz⟩
      have hw := pullback.lift_snd z (spMap (Ideal.Quotient.mk J)) hz
      rw [he, ← Category.assoc] at hw
      have h2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
          Spec.preimage (S := CommRingCat.of (X.presheaf.stalk x ⧸ J))
            (pullback.lift z (spMap (Ideal.Quotient.mk J)) hz ≫ e.hom)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
        rw [Spec.map_comp, Spec.map_preimage]
        exact hw
      rw [Spec.map_inj] at h2
      intro a ha
      have h3 := congrArg (fun g => g.hom a) h2
      have h4 : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, h4, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3.symm
    · intro hIJ
      refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ)) ≫ e.inv ≫
        pullback.fst i (X.fromSpecStalk x), ?_⟩
      rw [Category.assoc, Category.assoc, pullback.condition, he, Category.assoc, Iso.inv_hom_id_assoc,
        ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

end GlobalTheory.CompanionTheory.StalkIdeal
end

