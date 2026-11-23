module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def RZ (H : Host E) (S A : ℕ) : Subring ℂ := Subring.closure {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}

def IsInc {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* ℂ) (i' : R' →+* ℂ) (β : R →+* R') : Prop :=
  ∀ x, i' (β x) = i x

def IsDedFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  (∃ _ : IsDomain O, IsDedekindDomain O) ∧ CharZero O ∧ @IsFractionRing O _ F _ β.toAlgebra

variable {H : Host E}

structure Cpt {U : Scheme.{0}} {F : Type} [Field F] (c : U ⟶ Sp F) (t₀ : SAB H U) {O : Type} [CommRing O]
    (β : O →+* F) where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  jQ : U ⟶ pullback s (spMap β)
  jQ_over : jQ ≫ pullback.snd _ _ = c
  jQ_open : IsOpenImmersion jQ
  jQ_dense : Dense (Set.range jQ)
  t : SAB H X
  m : SABMap t₀ t (jQ ≫ pullback.fst _ _)
  ab_gen : pullback.fst s (spMap β) ⁻¹' abLocus t.G = Set.range jQ

def AbOpen {X : Scheme.{0}} (G : Over X) : Prop :=
  ∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)

def SplitFib {X : Scheme.{0}} (G : Over X) [GrpObj G] : Prop :=
  ∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)

def HasTheta {X : Scheme.{0}} (G : Over X) (L : LB G.left) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)

def Good {X : Scheme.{0}} (t : SAB H X) : Prop := AbOpen t.G ∧ SplitFib t.G ∧ HasTheta t.G t.PP.L

section

variable {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

def Cpt.j (C : Cpt c t₀ β) : U ⟶ C.X := C.jQ ≫ pullback.fst _ _

structure Cpt.Above (C' : Cpt c' t₀' β') (C : Cpt c t₀ β) (b : O →+* O') (r : U' ⟶ U) (ν : SABMap t₀' t₀ r) where
  π : C'.X ⟶ C.X
  π_over : π ≫ C.s = C'.s ≫ spMap b
  fin : IsFinite (pullback.lift π C'.s π_over)
  mu : SABMap C'.t C.t π
  j_comm : C'.j ≫ π = r ≫ C.j
  φ_comm : C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ

def Cpt.ExtendsAut (C : Cpt c t₀ β) (r : U ≅ U) (ν : SABMap t₀ t₀ r.hom) : Prop :=
  ∃ (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), ρ.hom ≫ C.s = C.s ∧ C.j ≫ ρ.hom = r.hom ≫ C.j ∧
    C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ

end

variable {D : Datum H}

def ofModel {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Cpt (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) Y.oF.t β :=
  ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩

def LevComp {l l' : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l' B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} (o' : Obj D l' b' s') (o : Obj D l b s) (r : S' ⟶ S)
    (ν : SABMap o'.t o.t r) : Prop :=
  (∀ a, (o'.eta a ^ (l'.M / l.M)).left ≫ ν.φ = r ≫ (o.eta a).left) ∧
    ∀ a, (o'.etaA a ^ (l'.A / l.A)).left ≫ ν.φ = r ≫ (o.etaA a).left

def SiegData {T : Scheme.{0}} {O : Type} [CommRing O] (sT : T ⟶ Sp O) (t : SAB H T)
    (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) {g p N : ℕ} (Ag : SiegelFamily g p N) (z : ZP p N →+* O)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (cl : T ⟶ pullback Ag.s (spMap z)) : Prop :=
  ∃ (o : SiegPre g N (zetaZP p N) (sT ≫ spMap z)) (φ : o.A.left ⟶ t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 t.G).left),
    IsGrpPullback o.A t.G (𝟙 T) φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ t.G t.PP.L).pull φ₂) ∧
    (∀ u, (o.lev u).left ≫ φ = (lev (bas u)).left) ∧ cl ≫ pullback.snd _ _ = sT ∧
    SiegPB o Ag.univ (cl ≫ pullback.fst _ _)

structure Top (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) where
  Z : Scheme.{0}
  s : Z ⟶ Sp (RZ H n N)
  normal : IsNormalScheme Z
  proj : IsProjOver s
  flat : Flat s
  t : SAB H Z
  qproj : IsQProjOver (t.G.hom ≫ s)
  good : Good t
  ga : genericPoints Z ⊆ abLocus t.G
  a : ∀ l : Level H, l.A = N → ((Xo l).X ⟶ Z)
  m : ∀ l h, SABMap (Xo l).univ.t t (a l h)
  fin : ∀ l h (β : RZ H n N →+* KA l), IsInc (RZ H n N).subtype (KA l).val.toRingHom β →
    ∃ (W : (pullback s (spMap β)).Opens) (f : (Xo l).X ⟶ W.toScheme),
      (W : Set _) = pullback.fst s (spMap β) ⁻¹' abLocus t.G ∧ IsFinite f ∧ Surjective f ∧
      f ≫ W.ι ≫ pullback.fst _ _ = a l h ∧ f ≫ W.ι ≫ pullback.snd _ _ = (Xo l).s
  compat : ∀ l l' h h' (r : (Xo l').X ⟶ (Xo l).X) (ν : SABMap (Xo l').univ.t (Xo l).univ.t r) (k : KA l →+* KA l'),
    IsInc (KA l).val.toRingHom (KA l').val.toRingHom k → r ≫ (Xo l).s = (Xo l').s ≫ spMap k →
    (∀ x, ((Xo l').univ.etaA x).left ≫ ν.φ = r ≫ ((Xo l).univ.etaA x).left) →
    r ≫ a l h = a l' h' ∧ ν.φ ≫ (m l h).φ = (m l' h').φ
  sym : ∀ l h (r : (Xo l).X ≅ (Xo l).X) (ν : SABMap (Xo l).univ.t (Xo l).univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La)
    (σ : KA l ≃+* KA l), σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ (Xo l).s = (Xo l).s ≫ spMap σ.toRingHom →
    (∀ x, ((Xo l).univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ ((Xo l).univ.etaA x).left) →
    ∃ ρ : Z ≅ Z, a l h ≫ ρ.hom = r.hom ≫ a l h
  U : Z.Opens
  U_eq : (U : Set Z) = abLocus t.G
  MM : Scheme.{0}
  sM : MM ⟶ Sp (RZ H n N)
  tM : SAB H MM
  lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)
  MM_red : IsReduced MM
  MM_flat : Flat sM
  MM_ab : IsProper tM.G.hom
  u : U.toScheme ⟶ MM
  u_over : u ≫ sM = U.ι ≫ s
  u_fin : IsFinite u
  u_surj : Surjective u
  u_gen : ∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)
  tU : SAB H U.toScheme
  mU : SABMap tU t U.ι
  mM : SABMap tU tM u
  lev_eq : ∀ l h (a' : (Xo l).X ⟶ U.toScheme) (x : D.La) (y : (Xo l).X ⟶ tU.G.left), a' ≫ U.ι = a l h →
    y ≫ mU.φ = ((Xo l).univ.etaA x).left ≫ (m l h).φ → y ≫ mM.φ = a' ≫ u ≫ (lev x).left
  sieg : ∀ p : ℕ, p.Prime → p ≠ n → ∃ (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N)
    (bas : (Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) ⊕ Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤ) ≃ₗ[ℤ] D.La),
    (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) ∧
    ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p N →+* O) (b : RZ H n N →+* O), Function.Injective i →
      IsInc (ZP p N).subtype i z → IsInc (RZ H n N).subtype i b →
      ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ MM) (tT : SAB H T) (ν : SABMap tT tM f)
        (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsPullback f sT sM (spMap b) →
        (∀ x, (levT x).left ≫ ν.φ = f ≫ (lev x).left) →
        ∃ w : T ⟶ pullback Ag.s (spMap z), SiegData sT tT levT Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w

def AuxiliaryInertOddPrime (H : Host E) (n : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ ¬ IsSquare (-(H.d : ZMod n)) ∧ ¬ (n : ℤ) ∣ NumberField.discr E

structure BaseModel {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ} (T : Top Xo n N) (l₀ : Level H) where
  A_one : l₀.A = 1
  β : RZ H (n * l₀.M) 1 →+* KA l₀
  β_inc : IsInc (RZ H (n * l₀.M) 1).subtype (KA l₀).val.toRingHom β
  C : Cpt (Xo l₀).s (Xo l₀).univ.t β
  good : Good C.t
  acts : ∀ (r : (Xo l₀).X ≅ (Xo l₀).X) (ν : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La),
    r.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν.φ = r.hom ≫ ((Xo l₀).univ.eta x).left) →
    C.ExtendsAut r ν
  l₁ : Level H
  M_eq : l₁.M = l₀.M
  Mb_eq : l₁.Mb = l₀.Mb
  A_eq : l₁.A = N
  β₁ : RZ H (n * l₀.M) N →+* KA l₁
  β₁_inc : IsInc (RZ H (n * l₀.M) N).subtype (KA l₁).val.toRingHom β₁
  C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁
  b : RZ H (n * l₀.M) 1 →+* RZ H (n * l₀.M) N
  b_inc : IsInc (RZ H (n * l₀.M) 1).subtype (RZ H (n * l₀.M) N).subtype b
  r : (Xo l₁).X ⟶ (Xo l₀).X
  ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r
  lev : LevComp (Xo l₁).univ (Xo l₀).univ r ν
  r_surj : Surjective r
  above : C₁.Above C b r ν
  b' : RZ H n N →+* RZ H (n * l₀.M) N
  b'_inc : IsInc (RZ H n N).subtype (RZ H (n * l₀.M) N).subtype b'
  q : C₁.X ⟶ T.Z
  q_over : q ≫ T.s = C₁.s ≫ spMap b'
  q_fin : IsFinite (pullback.lift q C₁.s q_over)
  qm : SABMap C₁.t T.t q
  q_j : C₁.j ≫ q = T.a l₁ A_eq
  q_φ : C₁.m.φ ≫ qm.φ = (T.m l₁ A_eq).φ

def Raises {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ} {T : Top Xo n N} {l₀ l : Level H} (B : BaseModel T l₀)
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model (Xo l) c β) : Prop :=
  ∃ (b : RZ H (n * l₀.M) 1 →+* O) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r),
    IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b ∧ LevComp Y.oF (Xo l₀).univ r ν ∧
    Nonempty ((ofModel Y).Above B.C b r ν)

def IsPrimeToPart (l₀ l : Level H) (p : ℕ) : Prop :=
  l₀.A = 1 ∧ l₀.M = l.M / p ^ l.M.factorization p ∧ l₀.Mb = l.Mb ⊔ Ideal.span {(l₀.M : 𝓞 E)}

structure System (Xo : ∀ l : Level H, Moduli D l) where
  n : Bool → ℕ
  J : Bool → ℕ
  aux : ∀ i, AuxiliaryInertOddPrime H (n i)
  J_pos : ∀ i, 1 ≤ J i
  T : ∀ i, Top Xo (n i) (n i ^ J i)
  B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀
  ch : ℕ → Bool
  ch_ne : ∀ p, n (ch p) ≠ p
  Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W
  raises : ∀ p W hp hW (i : Idx H p), ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
    Raises (B (ch p) l₀ h.1) (Y p W hp hW i)

end GlobalTheory.Models

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS

open Classical in
def rsT {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : Γ(Y, O) := if h : O ≤ O₀ then resG Y h s else 0

open Classical in
def pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens) : Γ(Z, O) :=
  if h : O ≤ f ⁻¹ᵁ O₀ then (f.appLE O₀ O h).hom s else 0
variable {K : Type} [Field K] {Y X : Scheme.{0}} {I : Type} {g : ℕ}

abbrev C1 (U : I → Y.Opens) : Type := ∀ i j, Γ(Y, U i ⊓ U j)

def IsCoc (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∀ i j k, rsT (c i j) (U i ⊓ U j ⊓ U k) + rsT (c j k) (U i ⊓ U j ⊓ U k) = rsT (c i k) (U i ⊓ U j ⊓ U k)

def IsCob (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∃ b : ∀ i, Γ(Y, U i), ∀ i j, c i j = rsT (b j) (U i ⊓ U j) - rsT (b i) (U i ⊓ U j)

def Cohom (f : Y ⟶ Y) (U : I → Y.Opens) (c c' : C1 U) : Prop :=
  ∃ b : ∀ i k, Γ(Y, U i ⊓ f ⁻¹ᵁ U k),
    (∀ i i' k, rsT (b i' k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) - rsT (b i k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) =
      rsT (c i i') (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k)) ∧
    ∀ i k k', rsT (b i k) (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') - rsT (b i k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') =
      pbT f (c' k k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k')

def lc (q : Y ⟶ Sp K) {U : I → Y.Opens} (c : Fin g → K) (φ : Fin g → C1 U) : C1 U :=
  fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j

def IsDerK {R : Type} [CommRing R] (x₀ : R →+* K) (D : R → K) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure LocDerK {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m ⁻¹ᵁ W')
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)

def IsInvDer {A₀ : Over (Sp K)} [GrpObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ W : A₀.left.Opens, Γ(A₀.left, W) → Γ(A₀.left, W)) : Prop :=
  ∀ (W : A₀.left.Opens) (f : Γ(A₀.left, W)),
    pbT ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) =
      pbT (snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) +
        constFn (R := DualNumber K) (fst (epsR K) A₀).left _ DualNumber.eps *
          pbT (snd (epsR K) A₀).left (dd W f) ((snd (epsR K) A₀).left ⁻¹ᵁ W)

structure KSCoc {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W : I → X.Opens)
    (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (d : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O))
    (θ : Fin g → C1 (fun i => m ⁻¹ᵁ W i)) : Prop where
  der : ∀ i, LocDerK q p m D (W i) (d i)
  diff : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, d j O f - d i O f = ∑ a, rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)

def IsDlog (m : Y ⟶ X) (L : LB X) (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O))
    (φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)) : Prop :=
  ∀ a i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ a i j = dd a _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))

def IsConstK (A' : Over (Sp (DualNumber K))) [GrpObj A'] (A₀ : Over (Sp K)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap K (DualNumber K))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS

def IsDer {R : Type} [CommRing R] (x₀ : R →+* ℂ) (D : R → ℂ) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure PtDer {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  add : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f + f') = δ W f + δ W f'
  mul : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f * f') = valAt' y W f * δ W f' + valAt' y W f' * δ W f
  res : ∀ W W' (h : W' ≤ W), ⊤ ≤ y ⁻¹ᵁ W' → ∀ f, δ W' (resG X h f) = δ W f

structure LocDer {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = resG Y (fun _ hy => h hy) (d W f)
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

def dom (m : A₀.left ⟶ X) (W : X.Opens) : Set (Fin g → ℂ) := {z | ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W}

def fn (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) : ℂ := valAt' ((u.ex z).left ≫ m) W f

structure GoodU (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop where
  ah : u.IsAH Hm χ
  tan₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v
  tan₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  endo : ∀ f : A₀ ⟶ A₀, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f
  sec : ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ

structure KSRel {R : Type} [CommRing R] (p : X ⟶ Sp R) (m : A₀.left ⟶ X) (D : R → ℂ) (Θ : Matrix (Fin g) (Fin g) ℂ)
    (s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  der : ∀ z, PtDer ((u.ex z).left ≫ m) (s z)
  base : ∀ z r, s z ⊤ (constFn p ⊤ r) = D r
  hol : ∀ W f, DifferentiableOn ℂ (fun z => s z W f) (dom u m W)
  per : ∀ (l : u.Λ) W f, ∀ z ∈ dom u m W,
    s (z + l) W f = s z W f + fderiv ℂ (fn u m W f) z (Θ.mulVec (star (l : Fin g → ℂ)))

def IsSymm (Hm Θ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ z w, hermForm Hm (Θ.mulVec (star z)) w = hermForm Hm (Θ.mulVec (star w)) z

def Comm (Θ : Matrix (Fin g) (Fin g) ℂ) (F : (Fin g → ℂ) → (Fin g → ℂ)) : Prop :=
  ∀ z, F (Θ.mulVec (star z)) = Θ.mulVec (star (F z))

def IsConst (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (A₀ : Over (Sp ℂ)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap ℂ (DualNumber ℂ))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

def SectionsHaveFiniteDimension (p : X ⟶ Sp K) (M : LB X) (r : ℕ) : Prop :=
  ∃ s : Fin r → M.Sec, ∀ t : M.Sec, ∃! a : Fin r → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j

def Vol (p : X ⟶ Sp K) (M : LB X) (g : ℕ) (δ : ℝ) : Prop :=
  ∃ h : ℕ → ℕ, (∀ e, SectionsHaveFiniteDimension p (lbPow M e) (h e)) ∧
    Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds δ)

def VAmp (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) : Prop :=
  (⨆ i, Out.nonzeroLocus (th i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (th i)) ∧
    ∃ r : σ → Γ(X, Out.nonzeroLocus (th i)),
      (∀ j k, resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG X (inf_le_left : Out.nonzeroLocus (th i) ⊓ M.U k ≤ Out.nonzeroLocus (th i)) (r j) *
          resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(X, Out.nonzeroLocus (th i)), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F

def MapDeg (ψ : X ⟶ Y) (D : ℕ) : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
    letI := (ψ.app U).hom.toAlgebra
    Module.rank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = (D : Cardinal)

def TorsBasis (A : Over (Sp K)) [GrpObj A] (k : ℕ) {m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) : Prop :=
  0 < k ∧ (∀ i, pt i ^ k = 1) ∧ ∀ y : Out.baseOver (Sp K) ⟶ A, y ^ k = 1 →
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y

def ActsBy {A : Over (Sp K)} [GrpObj A] {k m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) (f : A ⟶ A)
    (Mat : Matrix (Fin m) (Fin m) (ZMod k)) : Prop :=
  0 < k ∧ ∀ i, pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val)

def FormIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) : Prop :=
  IsMonHom s ∧ LBIso (abelian₂ P.A M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L)

def SymB {A : Over (Sp K)} [GrpObj A] (M : LB A.left) : Prop := LBIso M (M.pull (GrpObj.inv : A ⟶ A).left)

theorem SectionsHaveFiniteDimension.one_of_isIso (p : X ⟶ Sp K) [IsIso p] {M : LB X} [Unique M.ι] (hU : M.U default = ⊤)
    (hg : ∀ i j, M.g i j = 1) : SectionsHaveFiniteDimension p M 1 := by
  have hb := AbLaw.cst_bijective p hU
  refine ⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 (t.f default)
  refine ⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩
  · obtain rfl : j = default := Subsingleton.elim _ _
    rw [Fin.sum_univ_one, _root_.mul_one]
    exact ha.symm
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hb' default
    rw [Fin.sum_univ_one, _root_.mul_one] at this
    exact hb.1 (this.symm.trans ha.symm)

theorem SectionsHaveFiniteDimension.trivial_point (K : Type) [Field K] : SectionsHaveFiniteDimension (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 1 :=
  haveI : Unique (Out.Inh.trivLB (Sp K)).ι := inferInstanceAs (Unique PUnit)
  SectionsHaveFiniteDimension.one_of_isIso _ rfl fun _ _ => rfl

theorem Vol.trivial_point (K : Type) [Field K] : Vol (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 0 1 := by
  refine ⟨fun _ => 1, fun e => ?_, by simp⟩
  haveI : Unique (lbPow (Out.Inh.trivLB (Sp K)) e).ι := inferInstanceAs (Unique (PUnit → PUnit))
  exact SectionsHaveFiniteDimension.one_of_isIso _ (top_unique fun _ _ => Set.mem_iInter.2 fun _ => trivial)
    fun i j => Out.Inh.linComb_triv_g _ _ i j

theorem vAmp_iff_veryAmpleBy (p : X ⟶ Sp K) (M : LB X) {m : ℕ} (s : Fin (m + 1) → M.Sec) :
    VAmp p M s ↔ AbLaw.VeryAmpleBy p M s :=
  and_congr Iff.rfl (forall_congr' fun _ => and_congr Iff.rfl (exists_congr fun _ =>
    and_congr Iff.rfl (forall_congr' fun _ => exists_congr fun _ => eq_comm)))

theorem VAmp.comp_surjective {p : X ⟶ Sp K} {M : LB X} {σ τ : Type} {th : σ → M.Sec} (h : VAmp p M th)
    {e : τ → σ} (he : Function.Surjective e) : VAmp p M (fun i => th (e i)) := by
  refine ⟨(he.iSup_comp fun i => Out.nonzeroLocus (th i)).trans h.1, fun i => ⟨(h.2 (e i)).1, ?_⟩⟩
  obtain ⟨r, hr, hF⟩ := (h.2 (e i)).2
  refine ⟨fun j => r (e j), fun j k => hr (e j) k, fun f => ?_⟩
  obtain ⟨F, rfl⟩ := hF f
  obtain ⟨G, rfl⟩ := MvPolynomial.rename_surjective e he F
  exact ⟨G, MvPolynomial.eval₂_rename _ _ _ _⟩

theorem vAmp_comp_equiv (p : X ⟶ Sp K) (M : LB X) {σ τ : Type} (th : σ → M.Sec) (e : τ ≃ σ) :
    VAmp p M (fun i => th (e i)) ↔ VAmp p M th :=
  ⟨fun h => by simpa only [Equiv.apply_symm_apply] using h.comp_surjective e.symm.surjective,
    fun h => h.comp_surjective e.surjective⟩

theorem vAmp_iff_veryAmpleBy_equiv (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) {m : ℕ}
    (e : Fin (m + 1) ≃ σ) : VAmp p M th ↔ AbLaw.VeryAmpleBy p M (fun i => th (e i)) :=
  (vAmp_comp_equiv p M th e).symm.trans (vAmp_iff_veryAmpleBy p M _)

theorem VAmp.exists_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {σ : Type} [Finite σ] [Nonempty σ] {th : σ → M.Sec}
    (h : VAmp p M th) : ∃ (m : ℕ) (e : Fin (m + 1) ≃ σ), AbLaw.VeryAmpleBy p M (fun i => th (e i)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun hn => (hn ▸ e (Classical.arbitrary σ) : Fin 0).elim0
  exact ⟨m, e.symm, (vAmp_iff_veryAmpleBy_equiv p M th e.symm).1 h⟩

theorem MapDeg.finrank_eq {ψ : X ⟶ Y} {D : ℕ} (h : MapDeg ψ D) (U : Y.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (ψ.app U).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D :=
  (congrArg Cardinal.toNat (h U hU hne)).trans (Cardinal.toNat_natCast D)

theorem MapDeg.of_isFinite {ψ : X ⟶ Y} [IsFinite ψ] {D : ℕ}
    (h : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      letI := (ψ.app U).hom.toAlgebra
      Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D) : MapDeg ψ D := fun U hU hne => by
  letI := (ψ.app U).hom.toAlgebra
  haveI : Nonempty U := hne.to_subtype
  haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  exact (Module.finrank_eq_rank _ _).symm.trans (congrArg _ (h U hU hne))

theorem MapDeg.id_one (X : Scheme.{0}) : MapDeg (𝟙 X) 1 := fun U _ hne =>
  haveI : Nonempty U := hne.to_subtype
  (Module.rank_self Γ(X, U)).trans Nat.cast_one.symm

section Torsion
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}

theorem TorsBasis.pos (h : TorsBasis A k pt) : 0 < k := h.1

theorem TorsBasis.pow_eq_one (h : TorsBasis A k pt) (i : Fin m) : pt i ^ k = 1 := h.2.1 i

theorem TorsBasis.existsUnique (h : TorsBasis A k pt) {y : Out.baseOver (Sp K) ⟶ A} (hy : y ^ k = 1) :
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y := h.2.2 y hy

theorem ActsBy.comp_eq {f : A ⟶ A} {Mat : Matrix (Fin m) (Fin m) (ZMod k)} (h : ActsBy pt f Mat) (i : Fin m) :
    pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val) := h.2 i

end Torsion

theorem FormIs.isMonHom {P : Out.PolAV (Sp K)} {M : LB P.A.left} {s : P.A ⟶ P.A} (h : FormIs P M s) :
    IsMonHom s := h.1

end GlobalTheory.ZV
end
end

