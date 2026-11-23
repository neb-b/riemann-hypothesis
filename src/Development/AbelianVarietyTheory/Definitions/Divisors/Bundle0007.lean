module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.CupProducts
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.BlockGLMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import GroundTheory.FunctionField.PlaceBridge
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def A1 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (F : Shv R) (n : ℤ),
  Function.Bijective (HK.pull R f F n)

def A2 : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (F : Shv R), Eqv R (cechAug f) F

def A3 : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R),
  (∀ n, Eqv R (disc.map (f.app n)) F) → Eqv R f F

def A4 : Prop := ∀ (R : Type) [CommRing R] {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
  (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (F : Shv R),
  Cover2 R f g → Cover2 R f' g' → Eqv R u F → Eqv R v F → Eqv R (pullback.map f g f' g' u v p hu hv) F → Eqv R p F

def A5 : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ), 0 < n → ∀ x : H R (sch.obj X) F n,
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), Etale f ∧ Surjective f ∧ pull R (sch.map f) F n x = 0

def DivisorNaturality : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j),
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b)) ∧
  (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧
  (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def DivisorRingCompatibility : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc),
  (Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧
  (∀ {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)) ∧
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)

def DivisorSupportCondition : Prop := ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g →
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), pull _ f _ _ a = 0 → pull _ g _ _ b = 0 → cup q a b = 0

def DivisorAdditivity : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M) ∧
  ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

def A7 : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1, ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))

def A8 : Prop := ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (E : Spc) (F : Shv S) (n : ℤ),
  Function.Bijective (restrH φ E F n)

def A9 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spc) (n : ℤ), n < 0 → Subsingleton (H R E F n)) ∧
  ∃ e : ∀ X : Scheme.{0}, Sec F X ≃+ H R (sch.obj X) F 0,
    (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (e X s) = e Y (Sec.res f s)) ∧
    ∀ (X : Scheme.{0}) (s : Sec F X), ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = e X s ∧
      ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s

def A10 : Prop := ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G),
  (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) →
  ∀ n, Function.Bijective (HK.post R ((chains R).obj E) φ n)

def A11 : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc,
  (∀ {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j), red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b)) ∧
  (Inv Q E → red Q q E _ _ (one Q E) = one q E ∧ ∀ L : E ⟶ ofCat (glCat 1), red Q q E _ _ (c1 Q L) = c1 q L) ∧
  (∀ (n i : ℤ) (a : Ht Q E n i), red Q Q E n i a = a) ∧
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht Q E n i), red q r E n i (red Q q E n i a) = red Q r E n i a

def B1 : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
  ∀ n i : ℤ,
  (∀ x : Ht q (sp c.pt) n i, IsUnit (q : c.pt) → ∃ j y, pull _ (spMap (c.ι.app j).hom) _ _ y = x) ∧
  ∀ j (y : Ht q (sp (D.obj j)) n i), IsUnit (q : D.obj j) → pull _ (spMap (c.ι.app j).hom) _ _ y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull _ (spMap (D.map f).hom) _ _ y = 0

def B2 : Prop := ∀ (R : Type) [CommRing R] (A : Type) [CommRing A], SH A → ∀ (F : Shv R) (n : ℤ), 0 < n →
  Subsingleton (H R (sp A) F n)

def B3 : Prop := ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f]
  [QuasiSeparated f], IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ,
  (∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S), SH A →
    Eqv _ (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)) → Eqv _ (sch.map f) (tw q i)

def B4 : Prop := ∀ (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIntegralHom f] [Surjective f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  Eqv _ (cechAug f) (tw q i)

def B5 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A], AIC A → IsUnit (q : A) → Acyc q (sp A)

def DivisorPicardCompatibility : Prop := ∀ (A : Type) [CommRing A], Nonempty (H ℤ (sp A) Gm 1 ≃+ Additive (CommRing.Pic A))

def B6h1 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ u : Aˣ, ∃ v, u = v ^ q) →
  (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → Subsingleton (Ht q (sp A) 1 1)

def B7 : Prop := ∀ (q : ℕ) [NeZero q] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], IsUnit (q : K) → ∀ (i : ℕ)
  (M : Rep (ZMod q) (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (ζ : Ω), IsPrimitiveRoot ζ q → ∀ b : Module.Basis Unit (ZMod q) M,
  (∀ (σ : Ω ≃ₐ[K] Ω) (a : ℕ), σ ζ = ζ ^ a → M.ρ σ (b ()) = ((a : ZMod q) ^ i) • b ()) → ∀ n : ℕ,
  Nonempty (Ht q (sp K) n i ≃+ GroundTheory.ProfCoh.cohomology M n)

def C1 : Prop := ∀ (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K]
  [Algebra.IsAlgebraic (RatFunc k) K], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp K) n i)

def C2 : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp B) n i)

def C3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ (B : Type) [CommRing B] [Algebra (Polynomial T) B] [Algebra.Etale (Polynomial T) B] [Algebra T B]
    [IsScalarTower T (Polynomial T) B] (i : ℤ),
  Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := B)).toRingHom) (tw q i)

def C4 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)

def C5 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ,
  (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q)

def D1 : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → ∀ n i : ℤ,
  Function.Bijective fun a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ)) =>
    ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def D2 : Prop := ∀ (q : ℕ) [NeZero q] (k : ℕ), 0 < k →
  ∃ s : ∀ {E : Spc} {N : ℕ}, (E ⟶ ofCat (glCat N)) → Ht q E (2 * k) k,
    (∀ {E E' : Spc} {N} (f : E ⟶ E') (V : E' ⟶ ofCat (glCat N)), Inv q E' → pull _ f _ _ (s V) = s (f ≫ V)) ∧
    (∀ {E : Spc} {a b} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)), Inv q E → s (bsumOf V W) = s V + s W) ∧
    ∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → s L = cpow q (c1 q L) k

def D3 : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ),
  (∀ c : groupHomology.cycles (Rep.trivial R Γ R) m, ∃ z, IsSlant R X (groupHomology.iCycles (Rep.trivial R Γ R) m c) z) ∧
  ∀ (F : Shv R) (n : ℤ), IsSlantMap R Γ X F m n (slantR R Γ X F m n)

def E1 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Ideal.Quotient.mk I)) (tw q i)

def E2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))) (tw q i)

def E3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of T)) [Smooth p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i)

def E4 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ), Finite (Ht q (sch.obj X) n i)

def E6 : Prop := ∀ (q : ℕ) [NeZero q] {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)], IsUnit (q : Γ(S, ⊤)) →
  ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → ∀ n i : ℤ,
  (n < 2 * d - 1 → Function.Bijective (pull _ (sch.map U.ι) (tw q i) n)) ∧
  (n < 2 * d → Function.Injective (pull _ (sch.map U.ι) (tw q i) n))

def E8 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ tr : Ht q (sch.obj X) (2 * d) d ≃+ ZMod q, ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = tr ((cup q a b).cast (by ring) (by ring))

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IdTower
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

structure HTower (k : Type) [Field k] where
  Γ : Type
  Z : Scheme.{0}
  q : Z ⟶ Spec (CommRingCat.of k)
  Y : Γ → Scheme.{0}
  s : ∀ g, Y g ⟶ Z
  t : ∀ g, Y g ⟶ Z
  comm : ∀ g, t g ≫ q = s g ≫ q

variable {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]

abbrev HTower.geomZ : Scheme.{0} := GlobalTheory.Et.geom Ω H.q

def HTower.sΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.s g) rfl

def HTower.tΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.t g) (H.comm g)


open Classical in
def hop (g : H.Γ) : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) := by
  classical
  exact if h : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T then h.choose else 0

def V (L : Type) [Field L] [Algebra ℚ_[l] L] {J : Type} (ι : J → H.Γ) (θ : J → L) :
    Submodule L (TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω)))) :=
  genEig L (fun j => hop l H Ω (ι j)) θ

def galV (L : Type) [Field L] [Algebra ℚ_[l] L] (σ : Ω ≃ₐ[k] Ω) :
    TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) →ₗ[L] TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) :=
  (galTot l Ω H.q σ).baseChange L

def HTower.idTower (k : Type) [Field k] : HTower k where
  Γ := Unit
  Z := Spec (CommRingCat.of k)
  q := 𝟙 _
  Y := fun _ => Spec (CommRingCat.of k)
  s := fun _ => 𝟙 _
  t := fun _ => 𝟙 _
  comm := fun _ => rfl

end GlobalTheory.GalV

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
section
set_option autoImplicit false

noncomputable section

open scoped IntermediateField Polynomial

namespace GlobalTheory.Nef

def IsFF (k F : Type) [Field k] [Field F] [Algebra k F] : Prop :=
  ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F

def Place (k F : Type) [Field k] [Field F] [Algebra k F] : Type :=
  {v : Valuation F (WithZero (Multiplicative ℤ)) //
    Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1}

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Place.O (v : Place k F) : ValuationSubring F := v.1.valuationSubring

def ord (v : Place k F) (x : F) : ℤ := -WithZero.log (v.1 x)

def nrm {n : ℕ} (v : Place k F) (x : Fin n → F) : WithZero (Multiplicative ℤ) :=
  Finset.univ.sup fun i => v.1 (x i)

def ordVec {n : ℕ} (v : Place k F) (x : Fin n → F) : ℤ := -WithZero.log (nrm v x)

def Unimod {n : ℕ} (v : Place k F) (g : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, v.1 (g i j) ≤ 1) ∧ v.1 g.det = 1

def admitted {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ v, (g v).det ≠ 0) ∧ {v | ¬ Unimod v (g v)}.Finite

def deg [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : ℤ := ∑ᶠ v, ord v (g v).det

def degLine [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (w : Fin n → F) : ℤ :=
  ∑ᶠ v, ordVec v ((g v).mulVec w)

def IsRes {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) : Prop :=
  ∀ p x, p.1 (algebraMap F E x) ≤ 1 ↔ (ρ p).1 x ≤ 1

def pullAd {n : ℕ} {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F)
    (g : Place k F → Matrix (Fin n) (Fin n) F) : Place k E → Matrix (Fin n) (Fin n) E :=
  fun p => (g (ρ p)).map (algebraMap F E)

def LinesLE [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (b : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E]
    (ρ : Place k E → Place k F), IsRes ρ → ∀ w : Fin n → E, w ≠ 0 →
      (degLine (pullAd ρ g) w : ℝ) ≤ b * Module.finrank F E

def IsRat (φ : PowerSeries F) : Prop :=
  ∃ p q : F[X], q ≠ 0 ∧ (q : PowerSeries F) * φ = (p : PowerSeries F)

def hankel (c : ℕ → F) (n : ℕ) : F := (Matrix.of fun i j : Fin (n + 1) => c (i + j)).det

def sc (v : Place k F) (u : F) : PowerSeries v.O →+* PowerSeries F :=
  (PowerSeries.rescale u).comp (PowerSeries.map v.O.subtype)

namespace Lib

open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField


section Line

variable (k)


variable {k}

end Line

section Product

end Product

end Lib

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MiddleNotMem
section
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

section Alg
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

theorem symPr_zero (C : Subgroup (GL (n ⊕ Fin 0) k)) : symPr C = C.comap (embX 0) := by
  have h : ∀ p, N k n 0 p = ⊥ := fun p => (Subgroup.eq_bot_iff_forall _).2 fun g hg => Units.ext (by
    ext (r | r) (s | s)
    · exact RootEx.Model.mem_N_iff.1 hg _ _ le_rfl
    all_goals first | exact r.elim0 | exact s.elim0)
  ext g
  show (∃ u ∈ symN k n 0, u * embX 0 g ∈ C) ↔ _
  simp [symN, h]
end Alg

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid (k := k)} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)



end GlobalTheory.FunObj.UnfModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
section
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory

namespace GlobalTheory.PDivGroup.Test

open PDiv

variable {p : ℕ} {O : Type} [CommRing O]


open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory in
variable {p : ℕ} {O : Type} [CommRing O] in
theorem _root_.GlobalTheory.PDivGroup.Test.mulP_injective (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by
  intro x y hxy
  have hinj := _root_.GlobalTheory.CartierDual.map_injective_of_surjective (G.dual_mulP_surjective n)
  have hx := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) x
  have hy := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) y
  rw [hxy, ← hy] at hx
  exact (_root_.GlobalTheory.CartierDual.bidual O (G.A n)).injective (hinj hx)

theorem hodgeTate_values [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    (∀ t, hodgeTate (mu p O) t = 0) ∧ hodgeTate (const p O) (constGen p O) ≠ 0 := by
  refine ⟨fun t => Subsingleton.elim _ _, fun h => dlogT_ne_zero p O hp ?_⟩
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id,
    Category.id_comp] at h
  have h2 := LinearMap.congr_fun (omegaMap_comp (mu p O).bidual.hom (mu p O).bidual.inv) (dlogT p O)
  rw [Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h2
  rw [h2]
  exact (congrArg _ h).trans (map_zero _)

section Prod

variable (A B : Type) [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

def inl : A →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id O A) (Bialgebra.unitBialgHom O B)).comp
    (Bialgebra.TensorProduct.rid O O A).symm.toBialgHom

def inr : B →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom O A) (BialgHom.id O B)).comp
    (Bialgebra.TensorProduct.lid O B).symm.toBialgHom

variable {A B}

theorem inl_apply (a : A) : inl (O := O) A B a = a ⊗ₜ 1 :=
  congrArg (fun y : B => a ⊗ₜ[O] y) (map_one (Bialgebra.unitBialgHom O B))

theorem inr_apply (b : B) : inr (O := O) A B b = 1 ⊗ₜ b :=
  congrArg (fun y : A => y ⊗ₜ[O] b) (map_one (Bialgebra.unitBialgHom O A))

theorem pts_ext {E : Type} [CommRing E] [Algebra O E] {x y : WithConv (A ⊗[O] B →ₐ[O] E)}
    (h1 : pointsMap E (inl A B) x = pointsMap E (inl A B) y)
    (h2 : pointsMap E (inr A B) x = pointsMap E (inr A B) y) : x = y := by
  refine ofConv_injective (Algebra.TensorProduct.ext' fun a b => ?_)
  have e1 : x.ofConv (inl A B a) = y.ofConv (inl A B a) := DFunLike.congr_fun (congrArg ofConv h1) a
  have e2 : x.ofConv (inr A B b) = y.ofConv (inr A B b) := DFunLike.congr_fun (congrArg ofConv h2) b
  have e : a ⊗ₜ[O] b = inl A B a * inr A B b := by simp [inl_apply, inr_apply]
  rw [e, map_mul, map_mul, e1, e2]

end Prod

@[reducible] def prod (G H : PDivGroup p O) : PDivGroup p O where
  height := G.height + H.height
  A n := G.A n ⊗[O] H.A n
  rank_eq n q := by
    rw [rankAtStalk_tensorProduct, Pi.mul_apply, G.rank_eq, H.rank_eq, mul_add, pow_add]
  res n := Bialgebra.TensorProduct.map (G.res n) (H.res n)
  res_surjective n := TensorProduct.map_surjective (g := (G.res n).toLinearMap) (g' := (H.res n).toLinearMap) (G.res_surjective n) (H.res_surjective n)
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · let π := Ideal.Quotient.mkₐ O
        (torsionIdeal (R := O) (A := G.A (n + 1) ⊗[O] H.A (n + 1)) (p ^ n))
      have h1 := (torsionIdeal_le_ker_iff (p ^ n) π).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      obtain ⟨y, hy⟩ := (G.exists_comp_res_iff n (pointsMap _ (inl _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      obtain ⟨z, hz⟩ := (H.exists_comp_res_iff n (pointsMap _ (inr _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      have h2 : (Algebra.TensorProduct.lift y z fun _ _ => .all _ _).comp
          (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
            G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n) = π :=
        Algebra.TensorProduct.ext' fun a b => by
          have e1 : y (G.res n a) = π (inl _ _ a) := DFunLike.congr_fun hy a
          have e2 : z (H.res n b) = π (inr _ _ b) := DFunLike.congr_fun hz b
          change y (G.res n a) * z (H.res n b) = _
          rw [e1, e2, ← map_mul, inl_apply, inr_apply]
          simp
      have h3 := (DFunLike.congr_fun h2 a).symm
      rw [AlgHom.comp_apply] at h3
      erw [show Bialgebra.TensorProduct.map (G.res n) (H.res n) a = 0 from ha, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3
    · refine (torsionIdeal_le_ker_iff (p ^ n) (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
          G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n)).2 (pts_ext ?_ ?_)
      · rw [map_pow, map_one]
        refine (G.exists_comp_res_iff n _).1 ⟨(inl (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inl _ _ (G.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a)
        simp [inl_apply]
      · rw [map_pow, map_one]
        refine (H.exists_comp_res_iff n _).1 ⟨(inr (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inr _ _ (H.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inr _ _ a)
        simp [inr_apply]

end GlobalTheory.PDivGroup.Test
end
end

