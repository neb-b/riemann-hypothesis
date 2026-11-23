module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0020
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

open CH E

def dlog {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) (v : B) : B :=
  ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : B) * δ.dpow (k + 1) (v - 1)

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((schFn q).cr b ht κ)) (D : LineData X)

def thPt (T : Thick ((schFn q).cr b ht κ)) : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ X := T.y.1.2

def thSp {T T' : Thick ((schFn q).cr b ht κ)} (φ : T ⟶ T') :
    Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ Spec (CommRingCat.of (T.B ⧸ T.J)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle))

structure CLift where
  p : ∀ T : C, Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y
  hp : ∀ T : C, p T ≫ D.f = thPt (G.obj T)
  w : ∀ {T T' : C}, (T ⟶ T') → ((G.obj T').B)ˣ
  hw : ∀ {T T' : C} (φ : T ⟶ T') (h : (thSp (G.map φ) ≫ p T) ≫ D.f = p T' ≫ D.f),
    Ideal.Quotient.mk (G.obj T').J (w φ) =
      (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom (D.u (thSp (G.map φ) ≫ p T) (p T') h)

variable {G D}

def CLift.r (Λ : CLift G D) (s : ComposableArrows C 2) : ((G.obj (s.obj (Fin.last 2))).B)ˣ :=
  Units.map (G.map (s.map' 1 2)).φ.toMonoidHom (Λ.w (s.map' 0 1)) * Λ.w (s.map' 1 2) * (Λ.w (s.map' 0 2))⁻¹

def CLift.coc (Λ : CLift G D) {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ) : Cn (G ⋙ OM _ c) 2 :=
  fun s => (dlog (G.obj (s.obj (Fin.last 2))).δ N (Λ.r s).val : (G.obj (s.obj (Fin.last 2))).B)


variable (D) in
def IsFirstChernClassOfLineBundle {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ) (x : H (OM ((schFn q).cr b ht κ) c) 2) : Prop :=
  ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ Thick ((schFn q).cr b ht κ)) (Λ : CLift G D),
    ∃ hz : d _ 2 (Λ.coc c N) = 0, (cx _).cls _ hz = (Mor.restrict (OM _ c) G).pull 2 x

variable {l : ℕ} [Fact l.Prime]


variable (q D) in
def IsFirstChernFamily (κ : O →+* OC l) (k : Bool) (x : ∀ n, Hc (schFn q) κ k n 2) : Prop :=
  ∀ n, IsFirstChernClassOfLineBundle (q := q) (b := bs l k n) (ht := rfl) (κ := κb κ k n) D ((PAlg.base l).cris n) (l * n) (x n)


variable (l) in
def FirstChernCompatible : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (k : Bool)
  (D : LineData X) (x : ∀ n, Hc (schFn q) κ k n 2), IsFirstChernFamily q D κ k x → E.IsFirstChernClassOfLineBundle q κ D fun n => β (schFn q) κ k n 2 (x n)

end CrystallineSemistableComparison.B
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

open PAlg

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]


variable (l) in
structure Eps where
  e : ℕ → (Ob l)ˣ
  succ : ∀ k, e (k + 1) ^ l = e k
  one : theta0 l (WittVector.teichmuller l (e 0 : Ob l)) = 1
  prim : theta0 l (WittVector.teichmuller l (e 1 : Ob l)) ≠ 1

namespace Eps

variable (ε : Eps l)

def qk (k : ℕ) : Acris l := algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l (ε.e k : Ob l))

def μ : Acris l := ε.qk 0 - 1

theorem cris_qk (A : PAlg l) (n k : ℕ) : A.cris n (ε.qk k) = A.toAcr n (WittVector.teichmuller l (A.s (ε.e k))) := by
  rw [qk, cris_algebraMap, sW, WittVector.map_teichmuller]

theorem sharp_e (A : PAlg l) : A.sharp (A.s (ε.e 0)) = 1 := by
  have := A.oC_theta0 (WittVector.teichmuller l (ε.e 0 : Ob l))
  rw [ε.one, map_one, sW, WittVector.map_teichmuller] at this
  exact this.symm

theorem μ_mem (k : Bool) (A : PAlg l) (n : ℕ) : A.cris n ε.μ ∈ JJ k A n := by
  have h := uJ_th k A n (WittVector.teichmuller l (A.s (ε.e 0)))
  have h' : A.th (WittVector.teichmuller l (A.s (ε.e 0))) = 1 := ε.sharp_e A
  rw [h', map_one] at h
  change A.cris n (ε.qk 0 - 1) ∈ JJ k A n
  rw [(A.cris n).map_sub, (A.cris n).map_one, cris_qk]
  exact Ideal.Quotient.eq.1 h.symm

def qU (n : ℕ) : ((base l).Acr n)ˣ :=
  Units.map (((base l).toAcr n).toMonoidHom.comp (WittVector.teichmuller l)) (ε.e 0)

theorem qU_val (n : ℕ) : (ε.qU n : (base l).Acr n) = (base l).cris n (ε.qk 0) := (ε.cris_qk (base l) n 0).symm

theorem qU_mem (k : Bool) (n : ℕ) : (ε.qU n : (bs l k n).R) - 1 ∈ (bs l k n).I := by
  have := ε.μ_mem k (base l) n
  change (base l).cris n (ε.qk 0 - 1) ∈ JJ k (base l) n at this
  rwa [((base l).cris n).map_sub, ((base l).cris n).map_one, ← qU_val] at this

end Eps

theorem mapU_sharp {A A' : PAlg l} (f : A ⟶ A') (a : A.A) : mapU f (A.sharp a) = A'.sharp (Hom.f f a) :=
  congrArg A'.th (WittVector.map_teichmuller _ _ _)

def epsU (ε : Eps l) (P : PAlg l ⥤ Type) : UF P.Elements where
  U T := (Units.map T.1.sharp).ker
  map {T T'} φ :=
    { toFun := fun x => ⟨Units.map (Hom.f φ.1).toMonoidHom x.1, by
        have h : T.1.sharp (x.1 : T.1.A) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 x.2)
        refine MonoidHom.mem_ker.2 (Units.ext ?_)
        change T'.1.sharp (Hom.f φ.1 (x.1 : T.1.A)) = 1
        rw [← mapU_sharp, h, map_one]⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  q T := ⟨Units.map T.1.s.toMonoidHom (ε.e 0), MonoidHom.mem_ker.2 (Units.ext (ε.sharp_e T.1))⟩
  map_q φ := Subtype.ext (Units.ext (RingHom.congr_fun (Hom.comm φ.1) _))

def contMap {A A' : PAlg l} (φ : A ⟶ A') (Γ : Type) [TopologicalSpace Γ] : A.cont Γ ⟶ A'.cont Γ where
  f := { toFun := fun f => ⟨fun z => Hom.f φ (f.1 z), fun k => (f.2 k).comp
           (Ideal.quotientMap (I := Ideal.span {A.pi ^ k}) (Ideal.span {A'.pi ^ k}) (Hom.f φ) (by
             rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
             exact (RingHom.congr_fun (Hom.comm φ) (pFlat l)).symm ▸ Ideal.mem_span_singleton_self _))⟩
         map_one' := Subtype.ext (funext fun _ => map_one _)
         map_mul' := fun _ _ => Subtype.ext (funext fun _ => map_mul _ _ _)
         map_zero' := Subtype.ext (funext fun _ => map_zero _)
         map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }
  comm := RingHom.ext fun x => Subtype.ext (funext fun _ => RingHom.congr_fun (Hom.comm φ) x)

def contShift (A : PAlg l) : A.cont ℤ_[l] ⟶ A.cont ℤ_[l] where
  f := { toFun := fun f => ⟨fun z => f.1 (z + 1), fun k => (f.2 k).comp_continuous (continuous_add_const 1)⟩
         map_one' := rfl
         map_mul' := fun _ _ => rfl
         map_zero' := rfl
         map_add' := fun _ _ => rfl }
  comm := rfl

variable {F : Fn O} (κ : O →+* OC l)

structure Tower {d : ℕ} (s : F.Small d) : Type 1 where
  A : PAlg l
  g : s.R →+* A.U
  hg : g.comp s.a = A.oC.comp κ
  c : Fin d → ℕ → (A.A)ˣ
  c_succ : ∀ k m, c k (m + 1) ^ l = c k m
  c_sharp : ∀ k, A.sharp (c k 0) = g (s.T k)
  univ : ∀ (B : Type) [CommRing B] (o : Ob l →+* B) (g' : s.R →+* B) (ρ : Fin d → ℕ → B), o (pFlat l) = 0 →
    (∀ x w, theta0 l w = κ x → g' (s.a x) = o (w.coeff 0)) → (∀ k, ρ k 0 = g' (s.T k)) → (∀ k m, ρ k (m + 1) ^ l = ρ k m) →
    ∃! f : A.A →+* B, f.comp A.s = o ∧ (∀ r a, A.sharp a - g r ∈ Ideal.span {(l : A.U)} → f a = g' r) ∧ ∀ k m, f (c k m) = ρ k m


variable {κ} in
def Tower.obj {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) : (F.pt κ).Elements :=
  (F.pt κ).elementsMk 𝒯.A
    ⟨F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀, 𝒯.hg ▸ F.ov_map (CommRingCat.ofHom 𝒯.g) s.ov⟩

def Fn.Sub.inc (V : F.Sub) : Fn.Map V.fn F where
  u := { app := fun B => TypeCat.ofHom fun y => y.1
         naturality := fun _ _ _ => rfl }
  ov h := h

abbrev subEl (V : F.Sub) : El (V.fn.pt κ) ⥤ El (F.pt κ) := elMap (V.inc.pt κ)

theorem subEl_gT (V : F.Sub) (k : Bool) (n : ℕ) :
    gT V.fn κ k n ⋙ subThick V (bs l k n) rfl (κb κ k n) = subEl κ V ⋙ gT F κ k n := rfl


variable (F) in
abbrev flt (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ) : Flt (Oc F κ k n) :=
  pdFlt (Lc F κ k n) ((base l).cris n) ρ hρ ε.μ (ε.μ_mem k (base l) n)


variable (l) in
def Local : Prop := ∀ d j : ℕ, ∃ N : ℕ, ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ)
  (ρ : ℕ → ℕ) (hρ : Slow ρ), n ≠ 0 → (k = false ∨ ρ = 0) → F.Small d →
    RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)


variable (l) in
def Main : Prop := ∀ d j : ℕ, ∃ N : ℕ, ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l), F.Atlas d →
  ∀ n : ℕ, (∀ k, UpTo (ε.μ ^ N) (β F κ k n j)) ∧ ∀ y, ∃ x ∈ HcFil F κ false n N j, β F κ false n j x = ε.μ ^ N • y

end CrystallineSemistableComparison.B
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

open PAlg

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

variable (F : Fn O) (κ : O →+* OC l)

theorem map_sq (P : CommRingCat.{0} ⥤ Type) {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (h : g.hom.comp f.hom = g'.hom.comp f'.hom) (y : P.obj A) : P.map g (P.map f y) = P.map g' (P.map f' y) := by
  have e : f ≫ g = f' ≫ g' := CommRingCat.hom_ext h
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, e]

def basePt {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂} (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) :
    F.ptK κ₂ ⟶ F.ptK κ₁ where
  app B := TypeCat.ofHom fun z => ⟨(z.1.1.comp τ, z.1.2), by rw [RingHom.comp_assoc, h]; exact z.2⟩
  naturality _ _ _ := rfl

theorem red_le (k : Bool) {m n : ℕ} (h : n ≤ m) : JJ k (base l) m ≤ (JJ k (base l) n).comap ((base l).red h) :=
  Ideal.map_le_iff_le_comap.1 (dd_red k _ h).1

theorem red_κb (k : Bool) {m n : ℕ} (h : n ≤ m) :
    (Ideal.quotientMap _ ((base l).red h) (red_le k h)).comp (κb κ k m) = κb κ k n := RingHom.ext fun x => by
  change Ideal.quotientMap _ _ (red_le k h) (uJ k (base l) m ((base l).oC (κ x))) = uJ k (base l) n ((base l).oC (κ x))
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((base l).oC (κ x))
  rw [← hw]; rfl

theorem red_cris (A : PAlg l) {m n : ℕ} (h : n ≤ m) (a : Acris l) : A.red h (A.cris m a) = A.cris n a :=
  RingHom.congr_fun (ACris.ringHom_ext (F := (A.red h).comp (A.cris m)) (G := A.cris n) fun y => by
    rw [RingHom.comp_apply, cris_of, cris_of, red_mk]) a

def redMor (k : Bool) {m n : ℕ} (h : n ≤ m) : CH.Mor (Oc F κ k m) (Oc F κ k n) (RingHom.id _) :=
  omMor (crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl (dd_red k _ h)
    (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl) (RingHom.id _) (red_cris _ h)

def redHc (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) : Hc F κ k m j →ₗ[Acris l] Hc F κ k n j := (redMor F κ k h).pull j

def HcSys (k : Bool) (j : ℕ) : Sys.{1} (Acris l) where
  M n := Hc F κ k n j
  r n := redHc F κ k n.le_succ j

section Gal
variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K))

theorem gal_le (k : Bool) (n : ℕ) : JJ k (base l) n ≤ (JJ k (base l) n).comap (galBase σ n) :=
  Ideal.map_le_iff_le_comap.1 (dd_gal k σ n).1

theorem gal_κb (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ) :
    (Ideal.quotientMap _ (galBase σ n) (gal_le σ k n)).comp (κb κ k n) = κb κ k n := RingHom.ext fun x => by
  change Ideal.quotientMap _ _ (gal_le σ k n) (uJ k (base l) n ((base l).oC (κ x))) = uJ k (base l) n ((base l).oC (κ x))
  obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (κ x)
  have hw' : theta0 l w = κ x := hw
  conv_rhs => rw [← hσ, ← hw', ← theta0_gal]
  rw [← hw', oC_theta0, oC_theta0, uJ_th, uJ_th, ← cris_algebraMap, ← cris_algebraMap, Ideal.quotientMap_mk, galBase_cris]
  exact congrArg (fun a => Ideal.Quotient.mk _ ((base l).cris n a)) (ACris.gal_smul_algebraMap σ w)

def galMorC (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ) : CH.Mor (Oc F κ k n) (Oc F κ k n) (ACris.galCris σ) :=
  omMor (crMor (F := F) (F' := F) (b := bs l k n) (b' := bs l k n) (ht := rfl) (ht' := rfl) (galBase σ n) rfl (dd_gal k σ n)
    (basePt F _ (gal_κb κ σ hσ k n)) fun _ _ _ => rfl) (ACris.galCris σ) (galBase_cris σ n)

def galHc (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) : Hc F κ k n j →ₛₗ[ACris.galCris σ] Hc F κ k n j :=
  (galMorC F κ σ hσ k n).pull j

def ptTw (hσ : ∀ x, galOC σ (κ x) = κ x) : F.pt κ ⟶ twF σ ⋙ F.pt κ where
  app A := TypeCat.ofHom fun y => ⟨F.Pt.map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) y.1, by
    have e : (twUEquiv σ A).symm.toRingHom.comp (A.oC.comp κ) = (tw σ A).oC.comp κ := RingHom.ext fun x =>
      (twUEquiv σ A).symm_apply_eq.2 ((twU_oC σ A _).trans (congrArg A.oC (hσ x))).symm
    have h := F.ov_map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) y.2
    rw [CommRingCat.hom_ofHom, e] at h
    exact h⟩
  naturality A A' f := by
    ext y
    refine Subtype.ext ?_
    change F.Pt.map (CommRingCat.ofHom (twUEquiv σ A').symm.toRingHom) (F.Pt.map (CommRingCat.ofHom (mapU f)) y.1) =
      F.Pt.map (CommRingCat.ofHom (mapU (twMap σ f))) (F.Pt.map (CommRingCat.ofHom (twUEquiv σ A).symm.toRingHom) y.1)
    have e : (twUEquiv σ A').symm.toRingHom.comp (mapU f) = (mapU (twMap σ f)).comp (twUEquiv σ A).symm.toRingHom :=
      RingHom.ext fun x => (twUEquiv σ A').symm_apply_eq.2
        ((twU_mapU σ f _).trans (congrArg (mapU f) ((twUEquiv σ A).apply_symm_apply x))).symm
    exact map_sq F.Pt _ _ _ _ e _

end Gal

noncomputable def frb {B : Type} [CommRing B] (h : (l : B) = 0) : B →+* B :=
  _root_.UpperTheory.Reformulated.B.FrobeniusElementAlt.frb h

theorem l_zero {B : Type} [CommRing B] {n : ℕ} (ψ : (base l).Acr n ⧸ JJ true (base l) n →+* B) : (l : B) = 0 := by
  have h : (l : (base l).Acr n) ∈ JJ true (base l) n := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  rw [← map_natCast ψ, ← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]

def phiPt (n : ℕ) : F.ptK (κb κ true n) ⟶ F.ptK (κb κ true n) where
  app B := TypeCat.ofHom fun z => (F.ptK _).map (CommRingCat.ofHom (frb (l_zero z.1.1))) z
  naturality B B' φ := by
    ext z
    exact map_sq (F.ptK _) φ (CommRingCat.ofHom (frb (l_zero (φ.hom.comp z.1.1)))) (CommRingCat.ofHom (frb (l_zero z.1.1))) φ
      (RingHom.ext fun x => (map_pow φ.hom x l).symm) z

theorem phi_mk (A : PAlg l) (n : ℕ) (r : A.Acr n) :
    Ideal.Quotient.mk (A.PFil n) (A.phi n r) = Ideal.Quotient.mk (A.PFil n) r ^ l := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (A.Acr 0) := subsingleton_of_zero_eq_one (by simpa using (A.pow_l_acr 0).symm)
    rw [← map_pow]; exact congrArg _ (Subsingleton.elim _ _)
  obtain ⟨u, hu⟩ := (RL.uToQ A n).2.2.1 (Ideal.Quotient.mk _ r)
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hu' : Ideal.Quotient.mk (A.PFil n) (A.toAcr n w) = Ideal.Quotient.mk _ r := hu
  have h1 : Ideal.Quotient.mk (A.PFil n) (A.phi n r) = Ideal.Quotient.mk _ (A.phi n (A.toAcr n w)) := by
    refine Ideal.Quotient.eq.2 ?_
    rw [← map_sub]
    exact (A.dpP_phi n).1 (Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.1 hu'.symm))
  have h2 : A.phiW w - w ^ l ∈ Ideal.span {(l : A.W)} := by
    rw [A.mem_span_l_iff, ← WittVector.constantCoeff_apply, map_sub, map_pow]
    exact sub_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  rw [h1, ← hu', phi_toAcr, ← map_pow, ← map_pow]
  refine Ideal.Quotient.eq.2 ?_
  rw [← map_sub, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

def phiMorC (n : ℕ) : CH.Mor (Oc F κ true n) (Oc F κ true n) (ACris.phi (K := ℂ_[l]) (p := l)) := by
  have hcris (a : Acris l) : (base l).phi n ((base l).cris n a) =
      (base l).cris n (ACris.phi (K := ℂ_[l]) (p := l) a) :=
    (base l).pdOk_frob.acr_cris (base l).frob_comp_s (ACris.phiZero (K := ℂ_[l]) (p := l))
      (fun y => RingHom.congr_fun (f := ACris.phiAway ℂ_[l] l)
        (awayW_ext fun x => by rw [ACris.phiAway_algebraMap, awayW_algebraMap, wmap_frobenius]) y.1) n a
  exact
    omMor (crMor (F := F) (F' := F) (b := bs l true n) (b' := bs l true n) (ht := rfl) (ht' := rfl) ((base l).phi n) rfl
      ((base l).dpP_phi n) (phiPt F κ n) fun _ y r =>
        ((congrArg y.1.1 (phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
      (ACris.phi (K := ℂ_[l]) (p := l)) hcris

def phiHc (n j : ℕ) : Hc F κ true n j →ₛₗ[ACris.phi (K := ℂ_[l]) (p := l)] Hc F κ true n j := (phiMorC F κ n).pull j

def cmpMor (n : ℕ) : CH.Mor (Oc F κ false n) (Oc F κ true n) (RingHom.id _) :=
  omMor (crMor (F := F) (F' := F) (b := bs l false n) (b' := bs l true n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    ((base l).dp_fil_pfil n) (basePt F (Ideal.Quotient.factor le_sup_right) rfl) fun _ _ _ => rfl) (RingHom.id _) fun _ => rfl

variable {F} {F' : Fn O}

def pullMorC (u : Fn.Map F F') (k : Bool) (n : ℕ) : CH.Mor (Oc F' κ k n) (Oc F κ k n) (RingHom.id _) :=
  omMor (crMor (F := F') (F' := F) (b := bs l k n) (b' := bs l k n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    (DPMorphism.id _).isDPMorphism (u.ptK _) fun _ _ _ => rfl) (RingHom.id _) fun _ => rfl

def pullHc (u : Fn.Map F F') (k : Bool) (n j : ℕ) : Hc F' κ k n j →ₗ[Acris l] Hc F κ k n j := (pullMorC κ u k n).pull j


variable (l) in
structure Compat : Prop where
  red : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ) (x : Hc F κ k m j),
    β F κ k n j (redHc F κ k h j x) = (CH.Mor.ofNatTrans (redEl (F.pt κ) h)).pull j (β F κ k m j x)
  gal : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j),
    β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x)
  phi : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ true n j),
    β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x)
  pull : ∀ {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j),
    β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x)
  cmp : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j),
    β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x
  cup : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ} (h : i + j = m)
    (x : Hc F κ k n i) (y : Hc F κ k n j), β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y)
  one : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ),
    β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n)
  red_fil : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) (r j : ℕ),
    ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j
  smul_fil : ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l),
    (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j

end CrystallineSemistableComparison.B
end
end

