module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.CupProductRingLaws

def LeafCupSpec : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
  (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
  ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
    μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LeafTwPairExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def LeafTwPairUnique : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k), μ.cup E hk = μ'.cup E hk

def LeafKumTExists : Prop := ∀ (q : ℕ) [NeZero q], ∃ t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U, IsKum q t

def IsOneCocycle (q : ℕ) (E : Spc) (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev (R := ZMod q) α.1 0 0 (by simp) U x = resGen 0 ζ

def IsEtaleFirstChernClassCocycle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def LeafOneSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  (∃ α, IsOneCocycle q E α) ∧ ∀ α, IsOneCocycle q E α → one q E = CohomologyClass.mk α

def EtaleFirstChernClassRepresentedByChernCocycle : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  (∃ γ, IsEtaleFirstChernClassCocycle q L γ) ∧ ∀ γ, IsEtaleFirstChernClassCocycle q L γ → c1 q L = CohomologyClass.mk γ

def LeafNatCup : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j),
  pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b)

def LeafNatOne : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E

def EtaleFirstChernClassNaturalUnderPullback : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
  pull _ f _ _ (c1 q L) = c1 q (f ≫ L)

def LeafNatKum : Prop := ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
  pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def LeafRingUnit : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)

def LeafRingAssoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
  cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)

def LeafRingComm : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j),
  cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)

end LateralTheory.E.CupProductRingLaws
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleChapterDThree
section
def LateralTheory.E.EtaleChapterDThree : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2 → GlobalTheory.EtC.D3
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleChapterDTwo
section
def LateralTheory.E.EtaleChapterDTwo : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleChapterEFour
section
def LateralTheory.E.EtaleChapterEFour : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2 → GlobalTheory.EtC.D3 → GlobalTheory.EtC.E1 → GlobalTheory.EtC.E2 → GlobalTheory.EtC.E3 → GlobalTheory.EtC.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleChapterEThree
section
def LateralTheory.E.EtaleChapterEThree : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2 → GlobalTheory.EtC.D3 → GlobalTheory.EtC.E1 → GlobalTheory.EtC.E2 → GlobalTheory.EtC.E3
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleChapterETwo
section
def LateralTheory.E.EtaleChapterETwo : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2 → GlobalTheory.EtC.D3 → GlobalTheory.EtC.E1 → GlobalTheory.EtC.E2
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.t_E1Cut

def QA (S : Type) [CommRing S] : Prop :=
  ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (π : T →+* S), AIC T ∧ Function.Surjective π

def Good (C : Type) [CommRing C] (J : Ideal C) : Prop :=
  J ≤ Ideal.jacobson ⊥ ∧ ∀ e : C ⧸ J, IsIdempotentElem e → ∃ x : C, IsIdempotentElem x ∧ Ideal.Quotient.mk J x = e

def lcMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type} (φ : LocallyConstant (PrimeSpectrum A) Y) :
    LocallyConstant (PrimeSpectrum B) Y :=
  φ.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩

def rL {S : Type} [CommRing S] (f g : S) : Localization.Away f →+* Localization.Away (f * g) :=
  IsLocalization.Away.awayToAwayRight f g

def rR {S : Type} [CommRing S] (f g : S) : Localization.Away g →+* Localization.Away (f * g) :=
  IsLocalization.Away.awayToAwayLeft g f

def Conn (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) : Prop :=
  (∀ j, j < n → Function.Bijective (pull R f F j)) ∧ Function.Injective (pull R f F n)

def Cover : Prop := ∀ (A : Type) [CommRing A], ∃ (A' : Type) (_ : CommRing A') (φ : A →+* A'),
  φ.IsIntegral ∧ Function.Surjective (PrimeSpectrum.comap φ) ∧ QA A'

def HensIdem : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → Good B (I.map φ)

def LCGood : Prop := ∀ (C : Type) [CommRing C] (J : Ideal C), Good C J → ∀ Y : Type,
  Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum C) Y => lcMap (Ideal.Quotient.mk J) φ)

def QAClosed : Prop := ∀ (S : Type) [CommRing S], QA S →
  AIC S ∧ (∀ f : S, QA (Localization.Away f)) ∧ ∀ J : Ideal S, QA (S ⧸ J)

def EtLift : Prop := ∀ (T S C : Type) [CommRing T] [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C] (π : T →+* S),
  Function.Surjective π → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra T C') (ρ : C' →+* C), Algebra.Etale T C' ∧
    Function.Surjective ρ ∧ ρ.comp (algebraMap T C') = (algebraMap S C).comp π ∧
    RingHom.ker ρ = (RingHom.ker π).map (algebraMap T C')

def EtAIC : Prop := ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], AIC T →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap T C))))

def FinEtSection : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C] [Module.Finite S C], QA S →
  Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) → Nonempty (C →ₐ[S] S)

def LCSplit : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S], QA S → ∀ f g : S, Ideal.span {f, g} = ⊤ →
  ∀ φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q),
  ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b

def EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions : Prop := A9 → ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ e : ∀ (B : Type) [CommRing B], Prim q B → (LocallyConstant (PrimeSpectrum B) (ZMod q) ≃+ Ht q (sp B) 0 i),
    ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)),
      pull _ (spMap f) _ _ (e B ζ φ) = e C (ζ.map f) (lcMap f φ)

def MV : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ → ∀ n : ℤ,
  (∀ c : H R (sp (Localization.Away (f * g))) F n, ∃ a b, c = pull R (spMap (rL f g)) F n a - pull R (spMap (rR f g)) F n b) →
  ∀ x : H R (sp S) F (n + 1), pull R (spMap (algebraMap S (Localization.Away f))) F _ x = 0 →
    pull R (spMap (algebraMap S (Localization.Away g))) F _ x = 0 → x = 0

def ZarLocal : Prop := B1 → B2 → ∀ (q : ℕ) (S : Type) [CommRing S], AIC S → IsUnit (q : S) → ∀ n i : ℤ, 0 < n →
  ∀ (x : Ht q (sp S) n i) (p : PrimeSpectrum S), ∃ f : S, f ∉ p.asIdeal ∧
    pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0

def AcycQA : Prop := A1 → A9 → B1 → B2 → ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S], QA S → IsUnit (q : S) → Acyc q (sp S)

def EqvQA : Prop := A1 → A9 → B1 → B2 → ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (J : Ideal S), QA S → Good S J →
  IsUnit (q : S) → ∀ i : ℤ, Eqv _ (spMap (Ideal.Quotient.mk J)) (tw q i)

def DescStep : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (n : ℤ),
  (∀ p, Conn R (disc.map (f.app p)) F n) → Eqv R (disc.map (f.app (op (SimplexCategory.mk 0)))) F → Conn R f F (n + 1)

def CechLevels : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A), φ.IsIntegral →
  Function.Surjective (PrimeSpectrum.comap φ) →
  (IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
    IsIntegralHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)))) ∧
  ∃ ψ : cech (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ⟶
      cech (Spec.map (CommRingCat.ofHom φ)),
    ψ ≫ cechAug _ = cechAug _ ≫ spMap (Ideal.Quotient.mk I) ∧
    (∀ p, ∃ (B : Type) (_ : CommRing B) (χ : A →+* B), χ.IsIntegral ∧ Nonempty (Arrow.mk (ψ.app p) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map χ))))))) ∧
    Nonempty (Arrow.mk (ψ.app (op (SimplexCategory.mk 0))) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))))))

theorem eqv_iso (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem sq (R : Type) [CommRing R] {E E' G G' : Spc} {f : E ⟶ E'} {g : G ⟶ G'} {a : E ⟶ G} {b : E' ⟶ G'} (w : f ≫ b = a ≫ g)
    {F : Shv R} (ha : Eqv R a F) (hb : Eqv R b F) (n : ℤ) :
    (Function.Bijective (pull R f F n) ↔ Function.Bijective (pull R g F n)) ∧
    (Function.Injective (pull R f F n) ↔ Function.Injective (pull R g F n)) := by
  have h : pull R f F n ∘ pull R b F n = pull R a F n ∘ pull R g F n := by
    funext x; simp only [Function.comp]; rw [← pull_comp, ← pull_comp, w]
  constructor
  · rw [← Function.Bijective.of_comp_iff _ (hb n), h, Function.Bijective.of_comp_iff' (ha n)]
  · rw [← Function.Injective.of_comp_iff' _ (hb n), h, Function.Injective.of_comp_iff (ha n).1]

theorem conn_sq (R : Type) [CommRing R] {E E' G G' : Spc} {f : E ⟶ E'} {g : G ⟶ G'} {a : E ⟶ G} {b : E' ⟶ G'} (w : f ≫ b = a ≫ g)
    {F : Shv R} (ha : Eqv R a F) (hb : Eqv R b F) (n : ℤ) : Conn R f F n ↔ Conn R g F n :=
  and_congr (forall_congr' fun j => imp_congr_right fun _ => (sq R w ha hb j).1) (sq R w ha hb n).2

theorem arr_w {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'} (e : Arrow.mk f ≅ Arrow.mk g) :
    ∃ (a : P ⟶ Q) (b : P' ⟶ Q'), IsIso a ∧ IsIso b ∧ disc.map f ≫ disc.map b = disc.map a ≫ disc.map g :=
  ⟨e.hom.left, e.hom.right, inferInstanceAs (IsIso e.hom.left), inferInstanceAs (IsIso e.hom.right), by
    rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ (Arrow.w e.hom).symm⟩

theorem unit_spec {A : Type} [CommRing A] {q : ℕ} (h : IsUnit (q : A)) : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

end LateralTheory.E.t_E1Cut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafChartRing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.t_E6Cut

def ConnK (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, (n < c - 1 → Function.Bijective (HK.pull R f F n)) ∧ (n < c → Function.Injective (HK.pull R f F n))

def Conn (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') : Prop := ConnK R F c ((chains R).map f)

def EtLoc (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop) : Prop :=
  ∃ S ∈ Scheme.etaleTopology.{0} T, ∀ (V : Scheme.{0}) (k : V ⟶ T), S k → P V k

def sxMap {E E' : Spc} (f : E ⟶ E') {p : ℕ} {T : Scheme.{0}} (x : Sx E p T) : Sx E' p T :=
  (f.app (op (SimplexCategory.mk p))).app (op T) x

def sxRes {E : Spc} {p : ℕ} {V T : Scheme.{0}} (k : V ⟶ T) (x : Sx E p T) : Sx E p V :=
  (E.obj (op (SimplexCategory.mk p))).map k.op x

end LateralTheory.E.t_E6Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafConeExactPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafConeExactPf

section General
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K L M : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)

theorem pre_inr_eq_zero (c : Cocycle (mappingCone φ) M n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom φ) (zcomp (Cocycle.ofHom (mappingCone.inr φ)) c (zero_add n))
      (zero_add n)) = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl φ).comp c.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp only [Cocycle.δ_eq_zero, Cochain.comp_zero, zero_add, mappingCone.δ_inl, smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro p q hpq
  simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq]

end General

end LateralTheory.E.LeafConeExactPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafExciseCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8.ExciseCut

def relMap (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) (i n : ℤ) :
    HK (ZMod q) (mappingCone ((chains _).map (sch.map ι))) (tw q i) n →+
      HK (ZMod q) (mappingCone ((chains _).map (sch.map ι'))) (tw q i) n :=
  HK.pull (ZMod q) (mappingCone.map ((chains _).map (sch.map ι')) ((chains _).map (sch.map ι))
    ((chains _).map (sch.map g)) ((chains _).map (sch.map f)) (by simp only [← Functor.map_comp, w])) (tw q i) n

def LeafConeZero : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R φ F n)) → ∀ n, Subsingleton (HK R (mappingCone φ) F n)

end LateralTheory.E.E8.ExciseCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKunEmptyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafKunEmptyPf

variable {R : Type} [CommRing R]

theorem sec_sub (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ModuleCat.isZero_iff_subsingleton.mp (Sheaf.isTerminalOfBotCover F U (Scheme.bot_mem_grothendieckTopology U)).isZero

theorem subsingleton_freePresheaf_hom_of_isEmpty (Z : Scheme.{0}) [IsEmpty Z] (M : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (hM : ∀ U : Scheme.{0}, IsEmpty U → Subsingleton (M.obj (op U))) :
    Subsingleton ((freeP R).obj (yoneda.obj Z) ⟶ M) := by
  constructor; intro α β
  apply NatTrans.ext; funext U
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  by_cases h : IsEmpty ((Opposite.unop U : Scheme.{0}) : Type)
  · haveI := hM _ h; exact Subsingleton.elim _ _
  · haveI : IsEmpty (Opposite.unop U ⟶ Z) := ⟨fun f => h ⟨fun y => isEmptyElim (f.base y)⟩⟩
    have hs : Subsingleton (((freeP R).obj (yoneda.obj Z)).obj U) := by
      change Subsingleton (ULift.{1} (Opposite.unop U ⟶ Z) →₀ ULift.{1} R); infer_instance
    rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem free_zero (Z : Scheme.{0}) [IsEmpty Z] : IsZero ((free R).obj (yoneda.obj Z)) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 := subsingleton_freePresheaf_hom_of_isEmpty (R := R) Z ((sheafToPresheaf Scheme.etaleTopology _).obj ((free R).obj (yoneda.obj Z)))
    (fun U hU => by haveI := hU; exact sec_sub _ U)
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv ((freeP R).obj (yoneda.obj Z))
    ((free R).obj (yoneda.obj Z))).injective
  exact h1.elim _ _

theorem chains_zero (Z : Scheme.{0}) [IsEmpty Z] (p : ℤ) : IsZero (((chains R).obj (sch.obj Z)).X p) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = p
  · obtain ⟨j, hj⟩ := h
    have hz : IsZero (((chainsN R).obj (sch.obj Z)).X j) := free_zero (R := R) Z
    exact hz.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat hj)
  · push Not at h
    exact HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj Z)) ComplexShape.embeddingDownNat p h

theorem H_sub (Z : Scheme.{0}) [IsEmpty Z] (F : Shv R) (n : ℤ) : Subsingleton (H R (sch.obj Z) F n) := by
  constructor; intro x y
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective y
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  exact (chains_zero (R := R) Z p).eq_of_src _ _

end LateralTheory.E.LeafKunEmptyPf
end
end

