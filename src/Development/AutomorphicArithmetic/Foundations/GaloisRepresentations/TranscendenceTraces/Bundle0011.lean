module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0052
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiSecRes

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.BTrPushQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trPushQ_of :
    TrPush → TrHl → WtPush → TrPushQ := by
  intro hP hH hW l _ n i Z Z' S h p _ _ w hw hl
  have key : trHl l (h ≫ p) w n i ∘ₗ pullHl l (sch.map h) n i = trHl l p (Wt.push h w) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    rw [LinearMap.comp_apply, hH l n i (h ≫ p) w hw hl, hH l n i p (Wt.push h w) (hW h p w hw) hl]
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero k (Fact.out : Nat.Prime l).ne_zero⟩
    exact hP (l ^ k) n i h p w hw (by push_cast; exact hl.pow k) (x.1 k)
  simp only [trHQ, pullHQ, ← key, LinearMap.baseChange_comp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumEx
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem ring_sec (Ω C : Type) [Field Ω] [IsAlgClosed Ω] [CommRing C] [Nontrivial C] (φ : Ω →+* C)
    (h : φ.FiniteType) : ∃ ρ : C →+* Ω, ρ.comp φ = RingHom.id Ω :=
  _root_.UpperTheory.Reformulated.B.Qh66.ring_sec Ω C φ h

private theorem etale_sec (Ω : Type) [Field Ω] [IsAlgClosed Ω] {V : Scheme.{0}} [IsAffine V] (g : V ⟶ gp Ω) [Etale g]
    [Nonempty V] : ∃ σ : gp Ω ⟶ V, σ ≫ g = 𝟙 _ := by
  have hl : LocallyOfFiniteType g := inferInstance
  have hft : g.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hl
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  haveI : Nontrivial Γ(V, ⊤) := by
    haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
    exact Scheme.component_nontrivial V ⊤
  have hft' : (e.inv ≫ g.appTop).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)
  obtain ⟨ρ, hρ⟩ := ring_sec Ω Γ(V, ⊤) (e.inv ≫ g.appTop).hom hft'
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv, ?_⟩
  have he : (gp Ω).isoSpec.hom ≫ Spec.map e.inv = 𝟙 _ := by
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
    simp [e]
  have h1 : g = V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, he, Category.comp_id]
  have h2 : (e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ = 𝟙 _ := CommRingCat.hom_ext hρ
  calc (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ g
      = (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by rw [← h1]
    _ = Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (e.inv ≫ g.appTop) := by simp
    _ = Spec.map ((e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ) := (Spec.map_comp _ _).symm
    _ = 𝟙 _ := by rw [h2, Spec.map_id]

private theorem loc_gp (Ω : Type) [Field Ω] [IsAlgClosed Ω] (P : ∀ V : Scheme.{0}, (V ⟶ gp Ω) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ gp Ω) (k : W ⟶ V), P V g → P W (k ≫ g)) (h : Loc (gp Ω) P) : P (gp Ω) (𝟙 _) := by
  obtain ⟨V, g, hV, hg, ⟨v, -⟩, hPg⟩ := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (gp Ω) P hP).1 h (IsLocalRing.closedPoint Ω)
  haveI : Nonempty V := ⟨v⟩
  obtain ⟨σ, hσ⟩ := etale_sec Ω g
  simpa [hσ] using hP _ _ g σ hPg

@[reducible] private noncomputable def bcSq {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) {V : Scheme.{0}} (g : V ⟶ A.U) : Sq p :=
  ⟨V, pullback A.r g, g ≫ A.u, pullback.fst A.r g ≫ A.v, pullback.snd A.r g,
    (IsPullback.of_hasPullback A.r g).paste_horiz A.pb⟩

theorem UpperTheory.Gal.TranscendenceTraces.sumEx_of :
    SumExLoc → SumNat → PtInj → SumEx := by
  intro hLoc hNat hInj q _ i Z S p _ w hw hq A a
  have hqU : IsUnit (q : Γ(A.U, ⊤)) := by
    simpa using hq.map A.u.appTop.hom
  obtain ⟨T, hT, hTp⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q A.U).1 hqU
  have hex : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g →
      ∃ b : Sec (tw q i) V, IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) b :=
    fun V g hg => hLoc q i p w hw (bcSq A g) (hTp V g hg) _
  have huniq : ∀ (B : Sq p) (a' : Sec (tw q i) B.V) (b b' : Sec (tw q i) B.U), IsSum w B a' b → IsSum w B a' b' → b = b' :=
    fun B a' b b' h h' => hInj q i B.U b b' fun Ω _ _ x => (h Ω x).trans (h' Ω x).symm
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g → Sec (tw q i) V := fun V g hg => (hex V g hg).choose
  have hs : ∀ (V : Scheme.{0}) (g : V ⟶ A.U) (hg : T.arrows g),
      IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) (s V g hg) := fun V g hg => (hex V g hg).choose_spec
  have hcomp : ∀ (V W : Scheme.{0}) (g : V ⟶ A.U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    obtain ⟨L, hLf, hLs⟩ : ∃ L : pullback A.r (k ≫ g) ⟶ pullback A.r g,
        L ≫ pullback.fst A.r g = pullback.fst A.r (k ≫ g) ∧ L ≫ pullback.snd A.r g = pullback.snd A.r (k ≫ g) ≫ k :=
      ⟨pullback.lift (pullback.fst A.r (k ≫ g)) (pullback.snd A.r (k ≫ g) ≫ k)
        (by rw [pullback.condition, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let t : (bcSq A (k ≫ g)).To (bcSq A g) :=
      { g := k
        k := L
        hu := by simp
        hv := by
          change L ≫ pullback.fst A.r g ≫ A.v = pullback.fst A.r (k ≫ g) ≫ A.v
          rw [← Category.assoc, hLf]
        hr := hLs }
    have h1 := hNat (ZMod q) (tw q i) w t _ _ (hs V g hg)
    have h2 : Sec.res t.k (Sec.res (pullback.fst A.r g) a) = Sec.res (pullback.fst A.r (k ≫ g)) a := by
      rw [res_res]
      change Sec.res (L ≫ pullback.fst A.r g) a = _
      rw [hLf]
    rw [h2] at h1
    exact huniq _ _ _ _ h1 (hs W (k ≫ g) (T.downward_closed hg k))
  obtain ⟨b, hb⟩ := (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) (tw q i) A.U).2 T hT s hcomp
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hx : T.arrows x := by
    have hl : Loc (gp Ω) fun V g => T.arrows (g ≫ x) :=
      GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 A.U (gp Ω) x (fun V g => T.arrows g) ⟨T, hT, fun _ _ h => h⟩
    have h0 := loc_gp Ω (fun V g => T.arrows (g ≫ x))
      (fun V W g k h => by simpa using T.downward_closed h k) hl
    simpa using h0
  have h1 := (res_id _).symm.trans (hs _ x hx Ω (𝟙 _))
  rw [hb _ x hx, h1]
  have hbij := fib_bijOn (IsPullback.of_hasPullback A.r x) (𝟙 (gp Ω))
  rw [Category.id_comp] at hbij
  refine finsum_mem_eq_of_bijOn _ hbij fun z hz => ?_
  change w Ω (z ≫ pullback.fst A.r x ≫ A.v) • Sec.res z (Sec.res (pullback.fst A.r x) a) =
    w Ω ((z ≫ pullback.fst A.r x) ≫ A.v) • Sec.res (z ≫ pullback.fst A.r x) a
  rw [res_res, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

def PhiUniv : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (G J : Shv (ZMod Q)) (t : Fam0 p G J),
  ∃! m : (phi p (ZMod Q)).obj G ⟶ J, ∀ A a, Sec.map m ((phiE p G).app A a) = t.app A a

def DSOne : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (u : U ⟶ S) (b : Sec T.X₂ (pullback p u)), Sec.map T.g b = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ u b)

def DSLoc : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (x : DS p T.X₂ U), DS.map p T.g U x = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g x

def PhiExact : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)),
  T.Exact → (T.map (phi p R)).Exact

def PhiQis : Prop := ∀ (R : Type) [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive],
  (∀ T : ShortComplex (Shv R), T.Exact → (T.map Φ).Exact) → ∀ F : Shv R,
  ∃ ε : sgl (Φ.obj F) ⟶ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F), QuasiIso ε ∧
    sglι (Φ.obj F) ≫ ε.f 0 = Φ.map (resι R F)

def ExtRes : Prop := ∀ (R : Type) [CommRing R] (F G : Shv R) (T : Cx R) (ε : sgl F ⟶ T) [QuasiIso ε],
  (∀ a : F ⟶ G, ∃ m : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = a ≫ resι R G) ∧
  ∀ m m' : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = sglι F ≫ ε.f 0 ≫ m'.f 0 → ∀ (U : Scheme.{0}) (i n k : ℤ), i + 1 = n → n + 1 = k →
    ∀ y : Sec (T.X n) U, Sec.map (T.d n k) y = 0 → ∃ c, Sec.map ((res R G).d i n) c = Sec.map (m.f n) y - Sec.map (m'.f n) y

def FamHom : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (Φ : Shv (ZMod Q) ⥤ Shv (ZMod Q)) [Φ.Additive]
  (e : ∀ G, Fam0 p G (Φ.obj G)), Rep0 p Q Φ e → ∀ I J : Cx (ZMod Q),
  (∀ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J, ∃ τ : Fam p I J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)) ∧
  ∀ τ : Fam p I J, ∃ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)

end UpperTheory.Gal.TranscendenceTraces

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.SpecCorrOfHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

theorem pullHQ_comp (l : ℕ) [Fact l.Prime] {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n i : ℤ) :
    pullHQ l (sch.map (f ≫ g)) n i = pullHQ l (sch.map f) n i ∘ₗ pullHQ l (sch.map g) n i := by
  rw [Functor.map_comp]
  simp only [pullHQ, pullHl_comp, LinearMap.baseChange_comp]

end UpperTheory.Gal.TranscendenceTraces

end
end

