module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullUnitClass
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

theorem pull_unit_class {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{0} R) (A' : C' ⥤ CommAlgCat.{0} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  unfold CH.Mor.pull CH.oneH
  generalize_proofs p1 p2
  rw [CrystallineSemistableComparison.P.mapH_cls]
  · congr 1
    funext s
    exact h _
  · convert p2 using 2
    funext s
    exact h _

theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := by
  intro R R' _ _ C C' _ _ Φ Φ' σ m
  refine ⟨?_, pull_unit_class _ _ m.o (fun T => RingHom.map_one (m.ρ T))⟩
  intro i j k h x y
  have hz : ∀ n (c : (CH.cx (CH.modF Φ.A)).X n), c ∈ (CH.cx (CH.modF Φ.A)).Z n →
      m.o.hom.f n c ∈ (CH.cx (CH.modF Φ'.A)).Z n := by
    intro n c hc
    refine LinearMap.mem_ker.mpr ?_
    rw [m.o.hom.comm, LinearMap.mem_ker.mp hc, map_zero]
  have ex := CrystallineSemistableComparison.Auxff.cls_out _ x
  generalize Quotient.out x = z at ex
  subst ex
  have ey := CrystallineSemistableComparison.Auxff.cls_out _ y
  generalize Quotient.out y = w at ey
  subst ey
  obtain ⟨a, ha⟩ := z
  obtain ⟨b, hb⟩ := w
  have cup_cls {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
      {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
      {p q n : ℕ} (h : p + q = n) (a : CH.Cn F₁ p) (b : CH.Cn F₂ q) ha hb :
      ∃ hc, P.cup h ((CH.cx F₁).cls a ha) ((CH.cx F₂).cls b hb) =
        (CH.cx F₃).cls (P.cupC h a b) hc := by
    have ce (x : CH.H F₁ p) (y : CH.H F₂ q) :
        P.cup h x y = (CrystallineSemistableComparison.Auxff.toCx P).cup h x y := by
      unfold CH.Pairing.cup CxPairing.cup
      split_ifs with hz
      · rfl
      · exact absurd ((CrystallineSemistableComparison.Auxff.toCx P).leib h _ _ |>.trans (by
          rw [show CH.d F₁ p (Quotient.out x).1 = 0 from (Quotient.out x).2,
            show CH.d F₂ q (Quotient.out y).1 = 0 from (Quotient.out y).2]; simp)) hz
    exact ⟨CrystallineSemistableComparison.Auxff.closed (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb,
      (ce _ _).trans
        (CrystallineSemistableComparison.P.cxcup_cls (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb _)⟩
  obtain ⟨hc, e⟩ := cup_cls (CH.mulP Φ.A) h a b ha hb
  obtain ⟨hc', e'⟩ := cup_cls (CH.mulP Φ'.A) h _ _ (hz _ _ ha) (hz _ _ hb)
  rw [e]
  unfold CH.Mor.pull
  rw [CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ ha), CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hb), e',
    CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hc)]
  congr 1
  funext s
  simp [CH.Mor.hom, CH.Mor.pullC, CH.mulP, CH.Pairing.cupC, SMor.o, CH.term, CH.modF]
  congr 1 <;> exact m.nat _ _

end GlobalTheory.CompanionTheory.SiteCup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SupSecs

variable {X : Scheme.{0}} {E : X.Modules}

def sumMap (S T : Subobject E) : (S : X.Modules) ⊞ (T : X.Modules) ⟶ E :=
  biprod.desc S.arrow T.arrow

theorem sup_eq_imageSubobject (S T : Subobject E) : S ⊔ T = imageSubobject (sumMap S T) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inl_desc])
    · exact Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inr_desc])
  · refine imageSubobject_le (sumMap S T)
      (biprod.desc (Subobject.ofLE S (S ⊔ T) le_sup_left)
        (Subobject.ofLE T (S ⊔ T) le_sup_right)) ?_
    apply biprod.hom_ext' <;> simp [sumMap]

theorem sumMap_app (S T : Subobject E) (V : X.Opens)
    (x : Γ((S : X.Modules) ⊞ (T : X.Modules), V)) :
    (sumMap S T).app V x =
      S.arrow.app V ((biprod.fst : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) +
        T.arrow.app V ((biprod.snd : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) := by
  have h : sumMap S T = biprod.fst ≫ S.arrow + biprod.snd ≫ T.arrow := by
    apply biprod.hom_ext' <;> simp [sumMap, Preadditive.comp_add]
  rw [h]
  rfl

theorem sumMap_app_add (S T : Subobject E) (V : X.Opens) (s : Γ((S : X.Modules), V))
    (t : Γ((T : X.Modules), V)) :
    (sumMap S T).app V
        ((biprod.inl : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V s +
          (biprod.inr : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V t) =
      S.arrow.app V s + T.arrow.app V t := by
  have hs : biprod.inl ≫ sumMap S T = S.arrow := by simp [sumMap]
  have ht : biprod.inr ≫ sumMap S T = T.arrow := by simp [sumMap]
  rw [map_add (f := _), GlobalTheory.QCoh.app_app, GlobalTheory.QCoh.app_app, hs, ht]

end GlobalTheory.CompanionTheory.GE.SupSecs

namespace GlobalTheory.CompanionTheory.GE


open SupSecs in
theorem supsecs {X : Scheme.{0}} {E : X.Modules} (hE : E.IsQuasicoherent) (S T : Subobject E)
    (hS : (S : X.Modules).IsQuasicoherent) (hT : (T : X.Modules).IsQuasicoherent) :
    ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧
      ∀ V : X.Opens, IsAffineOpen V →
        secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  rw [SupSecs.sup_eq_imageSubobject]
  refine ⟨GlobalTheory.QCoh.isQuasicoherent_of_iso (imageSubobjectIso (SupSecs.sumMap S T)).symm, fun V hV ↦ ?_⟩
  have hr : secs (imageSubobject (SupSecs.sumMap S T)) V = Set.range ((SupSecs.sumMap S T).app V) := by
    have harrow : (imageSubobject (SupSecs.sumMap S T)).arrow =
        (imageSubobjectIso (SupSecs.sumMap S T)).hom ≫ image.ι (SupSecs.sumMap S T) :=
      (imageSubobject_arrow (SupSecs.sumMap S T)).symm
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := GlobalTheory.QCoh.surjective_factorThruImage_app (SupSecs.sumMap S T) hV
        ((imageSubobjectIso (SupSecs.sumMap S T)).hom.app V a)
      refine ⟨b, ?_⟩
      rw [harrow, ← GlobalTheory.QCoh.app_app, ← hb, GlobalTheory.QCoh.app_app, image.fac]
    · rintro ⟨b, rfl⟩
      refine ⟨(factorThruImageSubobject (SupSecs.sumMap S T)).app V b, ?_⟩
      rw [GlobalTheory.QCoh.app_app, imageSubobject_arrow_comp]
  rw [hr]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, SupSecs.sumMap_app S T V y⟩
  · rintro ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, SupSecs.sumMap_app_add S T V s t⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcOneH
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisUnit

universe w w' u v u' v'

theorem pull_oneH {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : ∀ s : ComposableArrows C' 1, (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A'.map (GlobalTheory.CatH.toLast i s)).hom 1 : A'.obj _) = 0 := by
    intro s
    rw [Fin.sum_univ_two, map_one, map_one]
    simp
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ ?_).trans ?_
  · rw [e]
    exact funext c
  · exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem omMor_oneH {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
    (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) :
    (omMor m σ₀ h).pull 0 (CH.oneH (OA L c)) = CH.oneH (OA L' c') :=
  pull_oneH _ _ _ fun _ => rfl

theorem redHc_oneH : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m), redHc F κ k h 0 (CH.oneH (OcA F κ k m)) = CH.oneH (OcA F κ k n) := by
  intro l _ O _ F κ k m n h
  exact omMor_oneH _ _ _

end GlobalTheory.CompanionTheory.CrisUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedHcPullHc
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

def redFn (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) :
    Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem redHc_pullHc {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F' κ k m j) : redHc F κ k h j (pullHc κ u k m j x) = pullHc κ u k n j (redHc F' κ k h j x) := by
  unfold redHc pullHc redMor pullMorC
  exact cr_square (SH.pullM κ u k m) (redFn F κ k h) (redFn F' κ k h) (SH.pullM κ u k n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (SH.base_map u (red_κb κ k h)) j x

end GlobalTheory.CompanionTheory.CrisTransition
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedMCup
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

theorem redM_cup {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) {i j k : ℕ} (h : i + j = k)
    (x : HO Q i) (y : HO Q j) :
    redM Q r c k ((CH.mulP (sP Q).A).cup h x y) = (sqP (stdI Q r c)).cup h (redM Q r c i x) (redM Q r c j y) := by
  have hm : ∀ T (u v : (CH.modF (sP Q).A).obj ((𝟭 _).obj T)),
      (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T ((CH.mulP (sP Q).A).μ _ u v) =
        (sqP (stdI Q r c)).μ T ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T u)
          ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T v) := fun _ _ _ => rfl
  exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (sP Q).A) (sqP (stdI Q r c)) (𝟭 _)
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat hm h x y

end GlobalTheory.CompanionTheory.RedCup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedMorCupOne
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

universe w w' w'' u v u' v' u'' v''

theorem one_cyc {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) :
    (CH.cx (CH.modF A)).d 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem pull_oneH_eq {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R''} {σ' : R' →+* R''} (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w'} R')
    {E : C'' ⥤ ModuleCat.{w''} R''} (m : CH.Mor (CH.modF A) E σ) (m' : CH.Mor (CH.modF A') E σ')
    (h : ∀ T : C'', m.τ T (1 : A.obj (m.G.obj T)) = m'.τ T (1 : A'.obj (m'.G.obj T))) :
    m.pull 0 (CH.oneH A) = m'.pull 0 (CH.oneH A') := by
  have e : m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0)))) =
      m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0)))) :=
    funext fun s => h (s.obj (Fin.last 0))
  have c : (CH.cx E).d 0 (m.hom.f 0 (fun s : ComposableArrows C 0 => (1 : A.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m.hom.comm, one_cyc, map_zero]
  have c' : (CH.cx E).d 0 (m'.hom.f 0 (fun s : ComposableArrows C' 0 => (1 : A'.obj (s.obj (Fin.last 0))))) = 0 := by
    rw [m'.hom.comm, one_cyc, map_zero]
  unfold CH.Mor.pull CH.oneH
  refine (CrystallineSemistableComparison.P.mapH_cls m.hom 0 _ _ c).trans (Eq.trans ?_ (CrystallineSemistableComparison.P.mapH_cls m'.hom 0 _ _ c').symm)
  exact congrArg Submodule.Quotient.mk (Subtype.ext e)

theorem redMor_mul {O A R Λ : Type} [CommRing O] [CommRing A] [CommRing R] [CommRing Λ] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (T)
    (x y : (B.OM (nlFun δ l X q κ) c).obj ((redMor q s d 𝒱 c lam hc r).G.obj T)) :
    (redMor q s d 𝒱 c lam hc r).τ T ((CH.mulP (B.OA (nlFun δ l X q κ) c)).μ _ x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).μ T ((redMor q s d 𝒱 c lam hc r).τ T x) ((redMor q s d 𝒱 c lam hc r).τ T y) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
  refine Subtype.ext ?_
  rfl

theorem redMor_cup_one {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) :
    (∀ {i j k : ℕ} (h : i + j = k) x y, (redMor q s d 𝒱 c lam hc r).pull k ((CH.mulP (B.OA (nlFun δ l X q κ) c)).cup h x y) =
      (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))).cup h ((redMor q s d 𝒱 c lam hc r).pull i x) ((redMor q s d 𝒱 c lam hc r).pull j y)) ∧
    (redMor q s d 𝒱 c lam hc r).pull 0 (CH.oneH (B.OA (nlFun δ l X q κ) c)) =
      redM (TS γ q l s 𝒱) r ((l : A) ^ n) 0 (CH.oneH (sP (TS γ q l s 𝒱)).A) := by
  refine ⟨fun {i j k} h x y => ?_, ?_⟩
  · exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (B.OA (nlFun δ l X q κ) c)) (sqP (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)))
      (redMor q s d 𝒱 c lam hc r).G (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).τ
      (redMor q s d 𝒱 c lam hc r).τ (redMor q s d 𝒱 c lam hc r).nat (redMor q s d 𝒱 c lam hc r).nat
      (redMor q s d 𝒱 c lam hc r).nat (redMor_mul d q s 𝒱 c lam hc r) h x y
  · exact pull_oneH_eq _ _ (redMor q s d 𝒱 c lam hc r) (toSq (IdF.top _) (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)) fun _ => rfl)
      fun T => Subtype.ext (by
        change Ideal.Quotient.factor (ln_le q s 𝒱 r T) 1 = 1
        exact map_one _)

end GlobalTheory.CompanionTheory.RedCup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedTrans
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedTrans

section
variable {O A R₁ R₂ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂]
  {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
  {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n s : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem tr_dp (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (n : ℕ) :
    IsDPMorphism (redδ T h (n + 1)) (redδ T h n) (lnMap (RingHom.id T.B) l n.le_succ) := by
  have key : ∀ y : T.B, lnMap (RingHom.id T.B) l n.le_succ (Ideal.Quotient.mk (lnT T l (n + 1)) y) =
      Ideal.Quotient.mk (lnT T l n) y := fun y => by
    simp only [lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [Ideal.mem_comap, key]
    exact Ideal.mem_map_of_mem _ hy
  · intro k x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [key]
    simp only [redδ]
    rw [DividedPowers.Quotient.dpow_apply _ _ hy, DividedPowers.Quotient.dpow_apply _ _ hy, key]

variable (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {σ' : R₁ →+* R₂}
  (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')

theorem tr_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (r : R₁) :
    lnMap (RingHom.id T.B) l n.le_succ (iBar T l (n + 1) (d₁.ρ r)) = iBar T l n (d₂.ρ (σ' r)) := by
  rw [hρ]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [← ha]
  simp only [iBar, lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]

def eta (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) : redObj T d₁ h ⟶ m.obj (redObj T d₂ h) :=
  mkH (lnMap (RingHom.id T.B) l n.le_succ) (tr_comm d₁ d₂ hρ T) (tr_dp T h n)
    (Ideal.map_le_iff_le_comap.1 (tr_dp T h n).1) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        refine Eq.trans ?_ ((m.obj (redObj T d₂ h)).w r).symm
        exact congrArg (Ideal.Quotient.mk _) (tr_comm d₁ d₂ hρ T r)
      · refine Eq.trans ?_ (hpt _ _).symm
        change Spec.map _ ≫ Spec.map _ ≫ pt T = Spec.map _ ≫ pt T
        rw [← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end

theorem red_trans : ∀ {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂} (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2) →
    (∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X q κ₁) c₁) j),
    (redMor q s d₂ 𝒱 c₂ lam hc₂ r).pull j ((B.omMor m (RingHom.id Λ) h₀).pull j x) =
      trM (TS γ q l s 𝒱) r (l : A) n j ((redMor q s d₁ 𝒱 c₁ lam hc₁ r).pull j x) := by
  intro O A R₁ R₂ Λ _ _ _ _ _ _ I γ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X q s 𝒱 σ' m c₁ c₂ lam hc₁ hc₂ h₀ hpt hρ r j x
  rw [CrystallineSemistableComparison.pull_pull lam, trM, CrystallineSemistableComparison.pull_pull lam]
  symm
  refine CrystallineSemistableComparison.cr_pull_eq (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R₁ J₁ δ₁ l) (ht := rfl) (κ := κ₁) _ _ ?η ?nat ?cmp j x
  case η => exact fun T => eta d₁ d₂ m hpt hρ T.obj T.property.1
  case nat =>
    intro T T' f y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl
  case cmp =>
    intro T y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl

end GlobalTheory.CompanionTheory.RedTrans
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCommutesGaloisAction
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

section

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

theorem red_galBase_le (σ : Gal(PadicAlgCl l/K)) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    (base l).red h (galBase σ m r) = galBase σ n ((base l).red h r) :=
  ((pdOk_twId σ _).red_acr h _).trans (congrArg (twAcr σ _ n) ((pdOk_hom (baseTw σ)).red_acr h r))

def redMle (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem reduction_commutes_galois_action (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ k m j) :
    redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  unfold redHc galHc redMor galMorC
  exact cr_square (SH.galM F κ σ hσ k m) (redMle F κ k h) (redMle F κ k h) (SH.galM F κ σ hσ k n) (galBase_cris σ m)
    (red_cris _ h) (red_cris _ h) (galBase_cris σ n) (red_galBase_le σ h)
    (SH.base_base F (gal_κb κ σ hσ k m) (red_κb κ k h) (red_κb κ k h) (gal_κb κ σ hσ k n)) j x

end

theorem redHc_galHc : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j), redHc F κ k h j (galHc F κ σ hσ k m j x) = galHc F κ σ hσ k n j (redHc F κ k h j x) := by
  intro l _ O _ F κ K σ hσ k m n h j x
  exact reduction_commutes_galois_action F κ σ hσ k h j x

end GlobalTheory.CompanionTheory.CrisTransition
end
end

