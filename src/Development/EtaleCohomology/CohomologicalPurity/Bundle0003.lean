module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.Imports
section
namespace LateralTheory.CohomologicalPurity

theorem goal_of (hG : LeafGysin) (hS : LeafSemi) : Goal :=
  fun H => ⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩

end LateralTheory.CohomologicalPurity
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

section Defs
variable {R : Type} [CommRing R] {A B D : Cx R}

abbrev pb (f : A ⟶ B) {I : Cx R} {n : ℤ} (c : Cochain B I n) : Cochain A I n := (Cochain.ofHom f).comp c (zero_add n)

abbrev hpb (f : A ⟶ B) (I : Cx R) (n : ℤ) : CohomologyClass B I n →+ CohomologyClass A I n :=
  cpre (Cocycle.ofHom f) I n n (zero_add n)

structure Good (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) : Prop where
  w : i ≫ l = i ≫ r
  surj : ∀ (n : ℤ) (a : Cochain A I n), ∃ c : Cochain B I n, pb i c = a
  glue : ∀ (n : ℤ) (c c' : Cochain B I n), pb i c = pb i c' → ∃ b : Cochain D I n, pb l b = c ∧ pb r b = c'
  ext : ∀ (n : ℤ) (b b' : Cochain D I n), pb l b = pb l b' → pb r b = pb r b' → b = b'

def Tri (i : A ⟶ B) (l r : B ⟶ D) {I : Cx R} {n : ℤ} (a : Cocycle A I n) (c : Cochain B I n)
    (b : Cocycle D I (n + 1)) : Prop :=
  pb i c = a.1 ∧ pb l b.1 = δ n (n + 1) c ∧ pb r b.1 = 0

def IsDelta (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) (n : ℤ) (d : CohomologyClass A I n →+ (hpb r I (n + 1)).ker) : Prop :=
  ∀ (a : Cocycle A I n) (c : Cochain B I n) (b : Cocycle D I (n + 1)), Tri i l r a c b →
    (d (CohomologyClass.mk a)).1 = CohomologyClass.mk b

theorem Good.tri {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R} (h : Good i l r I) {n : ℤ} (a : Cocycle A I n) :
    ∃ c b, Tri i l r a c b := by
  obtain ⟨c, hc⟩ := h.surj n a.1
  obtain ⟨b, hl, hr⟩ := h.glue (n + 1) (δ n (n + 1) c) 0 (by
    rw [pb, ← δ_ofHom_comp]
    change δ n (n + 1) (pb i c) = _
    rw [hc]; simp [pb])
  refine ⟨c, Cocycle.mk b (n + 1 + 1) rfl (h.ext _ _ _ ?_ ?_), hc, hl, hr⟩
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb l b) = _
    rw [hl, δ_δ]; simp [pb]
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb r b) = _
    rw [hr]; simp [pb]

theorem pb_pb (f : A ⟶ B) (g : B ⟶ D) {I : Cx R} {n : ℤ} (c : Cochain D I n) : pb f (pb g c) = pb (f ≫ g) c := by
  simp [pb, Cochain.ofHom_comp]

end Defs

def LeafMono : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ p : ℤ, Mono (((chains R).map f).f p)

def LeafPush : Prop := ∀ (R : Type) [CommRing R] {U E E' D : Spc} (f : U ⟶ E) (g : U ⟶ E') (l : E ⟶ D) (r : E' ⟶ D),
  IsPushout f g l r → ∀ p : ℤ, IsPushout (((chains R).map f).f p) (((chains R).map g).f p) (((chains R).map l).f p)
    (((chains R).map r).f p)

def LeafGood : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  (∀ p, Mono (i.f p)) → (∀ p, IsPushout (i.f p) (i.f p) (l.f p) (r.f p)) → (∀ p, Injective (I.X p)) → Good i l r I

def LeafDelta : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ n : ℤ, ∃ d, IsDelta i l r I n d

def LeafExact : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ (n : ℤ) d, IsDelta i l r I n d →
    Function.Exact ((hpb l I n).comp (hpb r I n).ker.subtype) (hpb i I n) ∧ Function.Exact (hpb i I n) d ∧
    Function.Exact d ((hpb l I (n + 1)).comp (hpb r I (n + 1)).ker.subtype)

def LeafGen : Prop := ∀ (R : Type) [CommRing R] (P : PSh),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧
  (∀ (P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)),
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x)) ∧
  (∀ (G : Shv R) (φ ψ : (free R).obj P ⟶ G),
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧
  ∀ (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) →
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x

def LeafImgHom : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s),
    (∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s) (U : Scheme.{0}) (x : P.obj (op U)),
      Sec.map (T P s φ) (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x))) ∧
    (∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T P t (φ ≫ I.d s t) = T P s φ ≫ J.d s t) ∧
    ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T P s ((free S).map f ≫ φ) = (free R).map f ≫ T P' s φ

def LeafImg : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (E : Spc) (n : ℤ), Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n,
    (∀ (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
      (x : Sx E p U), ev (R := R) (T E n α) p s h U x = ρ.app U s (ev (R := S) α p s h U x)) ∧
    (∀ (E : Spc) (n m : ℤ) (α : Cochain ((chains S).obj E) I n), T E m (δ n m α) = δ n m (T E n α)) ∧
    ∀ (E E' : Spc) (f : E ⟶ E') (n : ℤ) (α : Cochain ((chains S).obj E') I n),
      T E n (pb ((chains S).map f) α) = pb ((chains R).map f) (T E' n α)

theorem good (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (R : Type) [CommRing R] (F : Shv R) (P : Arrow Spc)
    (hP : Mono P.hom) : Good ((chains R).map P.hom) ((chains R).map (dbl.inl P)) ((chains R).map (dbl.inr P)) (res R F) :=
  h3 R _ _ _ _ (h1 R _ hP) (h2 R _ _ _ _ (IsPushout.of_hasPushout P.hom P.hom)) fun p => by
    unfold res; infer_instance

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem goal_of (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (h4 : LeafDelta) (h5 : LeafExact) (h6 : LeafImg) :
    LeafBd := by
  have G := fun (q : ℕ) (i : ℤ) => good h1 h2 h3 (ZMod q) (tw q i)
  have ex : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), ∃ d : Ht q P.left n i →+ Hs q P (n + 1) i, Mono P.hom →
      IsDelta ((chains _).map P.hom) ((chains _).map (dbl.inl P)) ((chains _).map (dbl.inr P)) (res _ (tw q i)) n d := by
    intro q P n i
    by_cases hP : Mono P.hom
    · obtain ⟨d, hd⟩ := h4 _ _ _ _ _ (G q i P hP) n
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose d hd using ex
  refine ⟨d, fun q P hP n i => h5 _ _ _ _ _ (G q i P hP) n _ (hd q P n i hP), ?_, ?_⟩
  · intro q P' P φ hP' hP n i u
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G q i P hP).tri a
    have e := hd q P n i hP a c b ht
    have e' := hd q P' n i hP' (zcomp (Cocycle.ofHom ((chains _).map φ.left)) a (zero_add n))
      (pb ((chains _).map φ.right) c) (zcomp (Cocycle.ofHom ((chains _).map (dbl.map φ))) b (zero_add _)) (by
        obtain ⟨t1, t2, t3⟩ := ht
        refine ⟨?_, ?_, ?_⟩
        · change _ = pb _ a.1
          rw [← t1, pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, Arrow.w φ]
        · change pb _ (pb _ b.1) = _
          rw [δ_ofHom_comp, ← t2]
          change _ = pb _ (pb _ b.1)
          rw [pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, inl_map]
        · change pb _ (pb _ b.1) = _
          rw [pb_pb, ← Functor.map_comp, dbl.inr_map, Functor.map_comp, ← pb_pb, t3]
          exact Cochain.comp_zero _ _)
    apply Subtype.ext
    refine Eq.trans ?_ e'.symm
    exact congrArg (pull _ (dbl.map φ) (tw q i) (n + 1)) e
  · intro Q q _ _ P hP n i u
    obtain ⟨T, hv, hδ, hp⟩ := h6 _ _ _ _ (redMap Q q i)
    let Z : ∀ (E : Spc) (m : ℤ), Cocycle ((chains _).obj E) (res _ (tw Q i)) m → Cocycle ((chains _).obj E) (res _ (tw q i)) m :=
      fun E m α => Cocycle.mk (T E m α.1) (m + 1) rfl (by rw [← hδ, α.δ_eq_zero, map_zero])
    have key : (∀ E m x, red Q q E m i x = 0) ∨
        ∀ E m α, red Q q E m i (CohomologyClass.mk α) = CohomologyClass.mk (Z E m α) := by
      unfold red SemiMap.op pick
      split_ifs with h
      · exact Or.inr fun E m α => h.choose_spec E m α (Z E m α) (hv E m α.1)
      · exact Or.inl fun _ _ _ => rfl
    rcases key with k | k
    · rw [k, k, map_zero]; rfl
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G Q i P hP).tri a
    have e := hd Q P n i hP a c b ht
    have e' := hd q P n i hP (Z _ _ a) (T _ _ c) (Z _ _ b) (by
      obtain ⟨t1, t2, t3⟩ := ht
      refine ⟨?_, ?_, ?_⟩
      · change _ = T _ _ a.1
        rw [← hp, t1]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t2, hδ]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t3, map_zero])
    rw [k]
    refine e'.trans ?_
    rw [← k]
    exact congrArg _ e.symm

end LateralTheory.CohomologicalPurity.Bd
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

def LocStd (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (e + d)) φ ∧
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension e) ((Ideal.Quotient.mk I).comp φ)

def Std (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  φ.IsStandardSmoothOfRelativeDimension (e + d) ∧ ((Ideal.Quotient.mk I).comp φ).IsStandardSmoothOfRelativeDimension e

def IsCoord {e d : ℕ} {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
    (y : Fin e → A) : Prop :=
  (MvPolynomial.eval₂Hom φ (Sum.elim x y)).Etale ∧ I = Ideal.span (Set.range x)

def LeafLoc : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X) (W : P.X.Opens), x ∈ W →
  ∃ V : P.X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧
    ∃ (R : Type) (_ : CommRing R) (φ : R →+* Γ(P.X, V.1)), LocStd P.e d φ (P.ι.ker.ideal V)

def LeafShrink : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  LocStd e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    Std e d ((algebraMap A A').comp φ) (I.map (algebraMap A A'))

def LeafRank : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (I p : Ideal A) [p.IsPrime], I ≤ p →
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) = d

def LeafPick : Prop := ∀ (d : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] (p : Ideal A)
  [p.IsPrime], Module.finrank p.ResidueField (p.ResidueField ⊗[A] M) = d →
  ∃ (x : Fin d → M) (f : A), f ∉ p ∧ ∀ m : M, f • m ∈ Submodule.span A (Set.range x)

def LeafSpan : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  (I p : Ideal A), p.IsPrime → I ≤ p → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  ∀ (x : Fin d → A) (f : A), (∀ j, x j ∈ I) → f ∉ p → (∀ a ∈ I, f * a ∈ Ideal.span (Set.range x)) →
  ∃ (y : Fin e → A) (g : A), g ∉ p ∧ ∀ ω : Ω[A⁄R],
    g • ω ∈ Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))

def LeafEt : Prop := ∀ (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A),
  Fintype.card ι = n → Algebra.IsStandardSmoothOfRelativeDimension n R A →
  Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤ →
  (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale

def LeafCoord : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  Std e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    ∃ (x : Fin d → A') (y : Fin e → A'), IsCoord ((algebraMap A A').comp φ) (I.map (algebraMap A A')) x y

def LeafSec : Prop := ∀ (A T : Type) [CommRing A] [CommRing T] (φ : A →+* T) (I : Ideal A) (μ : T →+* A ⧸ I), φ.Etale →
  μ.comp φ = Ideal.Quotient.mk I → ∃ t : T, μ t = 1 ∧ ∀ s : T, μ s = 0 → t * s ∈ I.map φ

def LeafPoly : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y →
  (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp ((Ideal.Quotient.mk I).comp φ))
    (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))).Etale

def LeafNbhd : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y → Chart d A I

theorem etale_of_subsingleton {A B : Type} [CommRing A] [CommRing B] [Subsingleton B] (φ : A →+* B) : φ.Etale := by
  algebraize [φ]
  exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)

theorem chart_top (d : ℕ) (A : Type) [CommRing A] : Chart d A ⊤ := by
  have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  refine ⟨A ⧸ (⊤ : Ideal A), inferInstance, Ideal.Quotient.mk ⊤, MvPolynomial.constantCoeff,
    ⟨etale_of_subsingleton _, ?_⟩, etale_of_subsingleton _, Subsingleton.elim _ _, fun a => ?_⟩
  · have := (Ideal.Quotient.mk_surjective (I := (⊤ : Ideal A).map (Ideal.Quotient.mk (⊤ : Ideal A)))).subsingleton
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · rw [Subsingleton.elim (_ - _) 0]; exact zero_mem _

theorem mem_basicOpen_of_notMem {X : Scheme.{0}} (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ X.basicOpen f := by
  have h : V.2.primeIdealOf ⟨x, hx⟩ ∈ V.2.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [V.2.fromSpec_preimage_basicOpen]; exact hf
  have h2 : V.2.fromSpec (V.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h
  rwa [V.2.fromSpec_primeIdealOf] at h2

theorem shrink {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V' : X.affineOpens) (_ : Algebra Γ(X, V.1) Γ(X, V'.1)), x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ IsLocalization.Away f Γ(X, V'.1) ∧
      I.ideal V' = (I.ideal V).map (algebraMap Γ(X, V.1) Γ(X, V'.1)) :=
  ⟨X.affineBasicOpen f, (inferInstance : Algebra Γ(X, V.1) Γ(X, X.basicOpen f)), mem_basicOpen_of_notMem V x hx f hf,
    X.basicOpen_le f, V.2.isLocalization_basicOpen f, (I.map_ideal_basicOpen V f).symm⟩

theorem off_case (d : ℕ) {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1)
    (h : ¬ I.ideal V ≤ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ V' : X.affineOpens, x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ (I.ideal V').FG ∧ Chart d Γ(X, V'.1) (I.ideal V') := by
  obtain ⟨f, hfI, hf⟩ := SetLike.not_le_iff_exists.mp h
  obtain ⟨V', _, hx', hle, _, hI⟩ := shrink I V x hx f hf
  have ht : I.ideal V' = ⊤ := by
    rw [hI]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hfI) (IsLocalization.Away.algebraMap_isUnit f)
  refine ⟨V', hx', hle, ?_, ?_⟩
  · rw [ht]; exact Ideal.fg_top _
  · rw [ht]; exact chart_top d _

theorem goal_of (hL : LeafLoc) (hS : LeafShrink) (hC : LeafCoord) (hN : LeafNbhd) : LeafChart := by
  intro d P x W hx
  obtain ⟨V, hxV, hVW, R, _, φ, hφ⟩ := hL d P x W hx
  by_cases h : P.ι.ker.ideal V ≤ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V x hxV h
    exact ⟨V', a, b.trans hVW, c⟩
  obtain ⟨f, hf, H⟩ := hS P.e d R _ φ _ _ (V.2.primeIdealOf ⟨x, hxV⟩).isPrime h hφ
  obtain ⟨V₁, _, hx₁, hle₁, _, hI₁⟩ := shrink P.ι.ker V x hxV f hf
  have H₁ := H Γ(P.X, V₁.1)
  rw [← hI₁] at H₁
  by_cases h₁ : P.ι.ker.ideal V₁ ≤ (V₁.2.primeIdealOf ⟨x, hx₁⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V₁ x hx₁ h₁
    exact ⟨V', a, b.trans (hle₁.trans hVW), c⟩
  obtain ⟨g, hg, G⟩ := hC P.e d R _ _ _ _ (V₁.2.primeIdealOf ⟨x, hx₁⟩).isPrime h₁ H₁
  obtain ⟨V₂, _, hx₂, hle₂, _, hI₂⟩ := shrink P.ι.ker V₁ x hx₁ g hg
  obtain ⟨u, v, G₂⟩ := G Γ(P.X, V₂.1)
  rw [← hI₂] at G₂
  refine ⟨V₂, hx₂, hle₂.trans (hle₁.trans hVW), ?_, hN P.e d R _ _ _ u v G₂⟩
  rw [G₂.2]
  exact Submodule.fg_span (Set.finite_range u)

end LateralTheory.CohomologicalPurity.ChartCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem freeSq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) (p : SimplexCategoryᵒᵖ) :
    (free R).map (P'.hom.app p) ≫ (free R).map (φ.right.app p) =
      (free R).map (φ.left.app p) ≫ (free R).map (P.hom.app p) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app, Arrow.w φ]

def LeafExcFormal : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P),
  (∀ p : SimplexCategoryᵒᵖ, IsIso (cokernel.map ((free (ZMod q)).map (P'.hom.app p)) ((free (ZMod q)).map (P.hom.app p))
    ((free (ZMod q)).map (φ.left.app p)) ((free (ZMod q)).map (φ.right.app p)) (freeSq _ φ p))) → Exc q φ

theorem freeSqSch (R : Type) [CommRing R] {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens)
    (h : U' ≤ f ⁻¹ᵁ U) :
    (free R).map (yoneda.map U'.ι) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (f.resLE U U' h)) ≫ (free R).map (yoneda.map U.ι) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]

def LeafExcSheaf : Prop := ∀ (R : Type) [CommRing R] {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X')
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U' : X'.Opens) (U : X.Opens),
  (U : Set X) = (Set.range ι)ᶜ → ∀ h : U' = f ⁻¹ᵁ U,
  IsIso (cokernel.map ((free R).map (yoneda.map U'.ι)) ((free R).map (yoneda.map U.ι))
    ((free R).map (yoneda.map (f.resLE U U' h.le))) ((free R).map (yoneda.map f)) (freeSqSch R f U' U h.le))

theorem LeafExc_of (hF : LeafExcFormal) (hS : LeafExcSheaf) : LeafExc := by
  intro _ q X' X Z f _ ι' ι _ hp U' U hU h
  refine hF q _ fun p => ?_
  exact hS (ZMod q) f ι' ι hp U' U hU h

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafGysinPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

def LeafPur : Prop := Hyp → ∀ d, ∃ pur : ∀ (q : ℕ) (P : SP d) (n i : ℤ),
    Ht q (sch.obj P.Z) n i →+ Hs q (opn P.U) (n + 2 * d) (i + d),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  (∀ n i : ℤ, Function.Bijective (pur q P n i)) ∧
  (∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (pur q P n i a) = pur q P' n i (pull _ (sch.map φ.g) _ _ a)) ∧
  (∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    (Hs.fgt q (opn P.U) (n + m + 2 * d) (i + j + d) (pur q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)) :
      Ht q (sch.obj P.X) (n + m + 2 * d) (i + j + d)) =
      (cup q a (Hs.fgt q (opn P.U) (m + 2 * d) (j + d) (pur q P m j b) : Ht q (sch.obj P.X) (m + 2 * d) (j + d))).cast
        (by ring) (by ring)) ∧
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    (pur r P n i (red q r _ _ _ a)).1 = red q r _ _ _ (pur q P n i a).1

namespace GysinPf

theorem mono_opn {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  haveI : ∀ k, Mono ((sch.map U.ι).app k) := fun _ => by
    change Mono (yoneda.map U.ι); infer_instance
  exact NatTrans.mono_of_mono_app _

def castHs {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) : Hs q P a i →+ Hs q P b i := by
  subst h; exact AddMonoidHom.id _

theorem castHs_bij {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) :
    Function.Bijective (castHs (q := q) (P := P) i h) := by
  subst h; exact Function.bijective_id

theorem castHs_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {a b : ℤ} (i : ℤ) (h : a = b) (x : Hs q P a i) :
    Hs.pull q φ b i (castHs i h x) = castHs i h (Hs.pull q φ a i x) := by
  subst h; rfl

theorem castHs_val {Q q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) (x : Hs Q P a i) (y : Hs q P a i)
    (hxy : y.1 = red Q q _ a i x.1) : (castHs i h y).1 = red Q q _ b i (castHs i h x).1 := by
  subst h; exact hxy

theorem fgt_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right _ _ (Hs.fgt q P n i x) := by
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp,
    show dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P from pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _]

theorem fgt_red {Q q : ℕ} {P : Arrow Spc} (n i : ℤ) (x : Hs Q P n i) (y : Hs q P n i)
    (h : y.1 = red Q q _ n i x.1) : Hs.fgt q P n i y = red Q q _ n i (Hs.fgt Q P n i x) := by
  change pull _ (dbl.inl P) _ n y.1 = red Q q _ n i (pull _ (dbl.inl P) _ n x.1)
  rw [h, pull_red]

theorem exact_cast {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) {M : Type*} [AddCommGroup M]
    (f : M →+ Hs q P a i) (hf : Function.Exact f (Hs.fgt q P a i)) :
    Function.Exact ((castHs i h).comp f) (Hs.fgt q P b i) := by
  subst h; exact hf

end GysinPf


open GysinPf in
theorem LeafGysin_of (hBd : LeafBd) (hPur : LeafPur) : LeafGysin := by
  intro hH d
  obtain ⟨δ, hex, hnatδ, hredδ⟩ := hBd
  obtain ⟨pur, hp⟩ := hPur hH d
  classical
  let gys : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.Z) n i →+ Ht q (sch.obj P.X) (n + 2 * d) (i + d) :=
    fun q P n i => (Hs.fgt q (opn P.U) (n + 2 * d) (i + d)).comp (pur q P n i)
  let rs : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.U) (n + 2 * d - 1) (i + d) →+ Ht q (sch.obj P.Z) n i :=
    fun q P n i => if h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) then
      (AddEquiv.ofBijective _ ((@hp q ⟨h.1⟩ P h.2).1 n i)).symm.toAddMonoidHom.comp
        ((castHs (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring)).comp (δ q (opn P.U) (n + 2 * d - 1) (i + d)))
      else 0
  have hrs : ∀ (q : ℕ) [NeZero q] (P : SP d) (_ : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ) u,
      pur q P n i (rs q P n i u) =
        castHs (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring) (δ q (opn P.U) (n + 2 * d - 1) (i + d) u) := by
    intro q _ P hq n i u
    simp only [rs, dif_pos (⟨NeZero.ne q, hq⟩ : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)))]
    exact AddEquiv.ofBijective_apply_symm_apply (pur q P n i) ((hp q P hq).1 n i)
  refine ⟨gys, rs, ?_⟩
  intro q _ P hq
  obtain ⟨hbij, hnat, hproj, hred⟩ := hp q P hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    have ex := hex q (opn P.U) (mono_opn _) (n + 2 * d - 1) (i + d)
    have ex' := hex q (opn P.U) (mono_opn _) (n + 2 * d) (i + d)
    refine ⟨?_, ?_, ?_⟩
    · intro x
      refine Iff.trans ?_ (ex.2.1 x)
      constructor
      · intro h
        have h2 := congrArg (pur q P n i) h
        rw [hrs q P hq, map_zero] at h2
        exact (castHs_bij _ _).1 (by rw [h2, map_zero])
      · intro h
        apply (hbij n i).1
        rw [hrs q P hq, h, map_zero, map_zero]
    · intro y
      refine (exact_cast (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring) _ ex.2.2 (pur q P n i y)).trans ?_
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, (hbij n i).1 ((hrs q P hq n i x).trans hx)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hrs q P hq n i x).symm⟩
    · intro z
      refine (ex'.1 z).trans ?_
      constructor
      · rintro ⟨s, rfl⟩
        obtain ⟨y, rfl⟩ := (hbij n i).2 s
        exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨_, rfl⟩
  · intro P' φ n i
    have hq' : IsUnit (q : Γ(P'.X, ⊤)) := by
      have := hq.map (φ.f.appTop).hom
      rwa [map_natCast] at this
    refine ⟨?_, ?_⟩
    · intro a
      change _ = Hs.fgt q (opn P'.U) _ _ (pur q P' n i _)
      rw [← hnat, fgt_pull]
      rfl
    · intro u
      apply ((hp q P' hq').1 n i).1
      rw [← hnat, hrs q P hq, hrs q P' hq', castHs_pull]
      exact congrArg _ (hnatδ q _ _ (opnMap φ.f _ _ φ.le) (mono_opn _) (mono_opn _) _ _ u)
  · exact hproj
  · intro r hr n i
    have : NeZero r := ⟨fun h => by subst h; exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hr)⟩
    have hr' : IsUnit (r : Γ(P.X, ⊤)) := by
      obtain ⟨k, hk⟩ := hr
      rw [hk, Nat.cast_mul] at hq
      exact isUnit_of_mul_isUnit_left hq
    refine ⟨?_, ?_⟩
    · intro a
      exact fgt_red _ _ _ _ (hred r hr n i a)
    · intro u
      apply ((hp r P hr').1 n i).1
      apply Subtype.ext
      rw [hrs r P hr', hred r hr, hrs q P hq]
      exact castHs_val _ _ _ _ (hredδ q r hr _ (mono_opn _) _ _ u)

end LateralTheory.CohomologicalPurity
end
end

