module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.TotW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def TateWit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp ℂ) (o : GObj gb N s)
    (hX : SmoothOfRelativeDimension D.g o.A.hom) (hL) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ S) e, 0 < N → N.Coprime p →
    UnifAt (gfam o hX hL) (RingHom.id ℂ) ρ N D' t P x e → ∀ I : TIs o x, (∀ y, toUnit _ ≫ o.eta y = I.ev N y) →
    ∃ (f : ℕ → D.La →+ D'.La) (nu : ℕ → ℤ), IsWit D' f nu ∧ (∀ a, ∃ u, f N a = t a + N • u) ∧
      ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a))

def IsogAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ)) (e'' : _) (inc : D'.La →ₗ[D.O] D''.La) (d : ℕ),
      D.Cls N D'' t'' ∧ UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) e'' ∧ (∀ u, P'' (inc u) = P u) ∧
      (∀ z, (e'' z).left = (e z).left ≫ c.tot) ∧ d.Coprime p ∧ (∀ u'', ∃ u, inc u = d • u'') ∧
      ∃ (f : ℕ → D.La →+ D'.La) (nu : ℕ → ℤ) (f'' : ℕ → D.La →+ D''.La) (nu'' : ℕ → ℤ), IsWit D' f nu ∧ IsWit D'' f'' nu'' ∧ (∀ a, ∃ u, f N' a = t a + N' • u) ∧
        (∀ a, ∃ u, f'' N a = t'' a + N • u) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
          (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w

def HeckeCoord : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∀ (B : GlobalTheory.LKCx.Form G) (j : D'.La →+ VQ D) (h₁ : G.GAf) (M : AddSubgroup (VQ D)), IsPlace L B.β D' j → IsCoordA L (trivX B) N' D' t j h₁ →
    IsLocP D' j M → ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ)) (e'' : _) (inc : D'.La →ₗ[D.O] D''.La)
      (j'' : D''.La →+ VQ D), D.Cls N D'' t'' ∧ UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) e'' ∧ (∀ u, P'' (inc u) = P u) ∧
      (∀ z, (e'' z).left = (e z).left ≫ c.tot) ∧ (∀ u'', ∃ (d : ℕ) (u : D'.La), d ≠ 0 ∧ inc u = d • u'') ∧ (∀ u, j'' (inc u) = j u) ∧
      IsPlace L B.β D'' j'' ∧ IsCoordA L (trivX B) N D'' t'' j'' (h₁ * h⁻¹) ∧ IsLocP D'' j'' M

def OneAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t → ∀ (j : D'.La →+ VQ D) (a : G.GAf × Gr G 1), IsPlace L B.β D' j →
    IsCoordA L (trivX B) N' D' t j a.1 → IsLocP D' j (PD.lat a.2) → ∀ P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∃ e₁, UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D' t P (x ≫ c₁.q) e₁ ∧ ∀ z, (e₁ z).left = (e z).left ≫ c₁.tot

def FixFwd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e → x ≫ c₁.q = x ≫ c₂.q → ∃ y, Sees B {g | h * g ∈ L.KN N} a y

def FixGa : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∀ y, Sees B {g | h * g ∈ L.KN N} a y → ∃ (ga : D'.La →ₗ[D.O] D'.La) (H : Matrix (Fin D.g) (Fin D.g) ℂ), (∀ u, j (ga u) = actY L y⁻¹ (j u)) ∧ FixesPer D' P ga H ∧
      ∀ w, ∀ Q : VQ D →+ (Fin D.g → ℂ), (∀ u, Q (j u) = P u) → ∀ hQ : IsPerQ L B.β ρ Q, Q (actY L y⁻¹ w) = H *ᵥ Q w

def FixEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ y, Sees B {g | h * g ∈ L.KN N} a y → ∀ ga : D'.La →ₗ[D.O] D'.La, (∀ u, j (ga u) = actY L y⁻¹ (j u)) →
    ∀ P₁ P₂ (x₁ x₂ : Sp ℂ ⟶ X'.X) e₁ e₂, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P₁ x₁ e₁ → UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P₂ x₂ e₂ → (∀ u, P₂ (ga u) = P₁ u) →
      x₁ ≫ c₂.q = x₂ ≫ c₁.q ∧ ∀ z, (e₁ z).left ≫ c₂.tot = (e₂ z).left ≫ c₁.tot

def PwOver : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf) (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (k : ℕ),
    c.pw k ≫ (GlobalTheory.KS.pow X.univ.A k).hom = (GlobalTheory.KS.pow X'.univ.A k).hom ≫ c.q ∧
    (∀ i, c.pw k ≫ (GlobalTheory.KS.pr X.univ.A i).left = (GlobalTheory.KS.pr X'.univ.A i).left ≫ c.tot) ∧
    (∀ b : D.O, (X'.univ.act.act b).left ≫ c.tot = c.tot ≫ (X.univ.act.act b).left) ∧
    ∀ α : Fin k → 𝓞 D.F, c.tw α ≫ (GlobalTheory.KS.pow X.univ.A k).hom = (GlobalTheory.KS.pow X'.univ.A k).hom ≫ c.q ∧ ∀ i, c.tw α ≫ (GlobalTheory.KS.pr X.univ.A i).left =
      (GlobalTheory.KS.pr X'.univ.A i).left ≫ c.tot ≫ (X.univ.act.act (algebraMap (𝓞 D.F) D.O (α i))).left

def PowCorr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf) (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (S : Sheet X'.s X'.univ.A D' ρ),
    (∀ P, IsPeriod D' ρ P → ∀ (b : D.O) z, (S.ex P (ρ b *ᵥ z)).left = (S.ex P z).left ≫ (X'.univ.act.act b).left) →
    ∀ ga : D'.La →ₗ[D.O] D'.La, (∀ P₁ P₂, IsPeriod D' ρ P₁ → IsPeriod D' ρ P₂ → (∀ u, P₂ (ga u) = P₁ u) →
      S.u P₁ ≫ c₂.q = S.u P₂ ≫ c₁.q ∧ ∀ z, (S.ex P₁ z).left ≫ c₂.tot = (S.ex P₂ z).left ≫ c₁.tot) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), CorrEq S (c₁.pw k) (c₂.tw α) ga (diagAct (algebraMap (𝓞 D.F) D.O) ρ α) ∧
      ∀ P, IsPeriod D' ρ P → (∀ z z', (S.ex P z).left ≫ c₁.tot = (S.ex P z').left ≫ c₁.tot → z - z' ∈ P.range) →
        ∀ z z', S.pt k P z ≫ c₁.pw k = S.pt k P z' ≫ c₁.pw k → S.pt k P z = S.pt k P z'

def FixLoc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) → IsSigD D ρ t₀ →
    SmoothOfRelativeDimension (D.n - 1) X'.s → (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (U : Unif (gfamD X' hX' hL') (RingHom.id ℂ) ρ N' (D.Cls N')) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀)
      (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ)) (j : (U.Di i).La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsPeriod (U.Di i) ρ P →
      IsCoord L B PD RD N' (U.Di i) (U.t i) P j a → ∀ y, Sees B {g | h * g ∈ L.KN N} a y →
      ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
      ∃ Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ)), (∀ x, x ∈ Fx ↔ x.1 ≫ (GlobalTheory.KS.pow X'.univ.A k).hom = U.u i P ∧
          x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ Fx.Nonempty ∧
        ∀ At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ, (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x)) → (∀ x ∈ Fx, (1 - At x).det ≠ 0) ∧ ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t =
            wtFix L v t₀ α t (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v _ y a.2.1)

def PowSm : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (d g : ℕ), SmoothOfRelativeDimension d s → QuasiCompact s → IsSeparated s →
    ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ k : ℕ,
    SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) ∧ QuasiCompact ((GlobalTheory.KS.pow A k).hom ≫ s) ∧
      IsSeparated ((GlobalTheory.KS.pow A k).hom ≫ s) ∧ LocallyOfFiniteType ((GlobalTheory.KS.pow A k).hom ≫ s)

def HeckeFixedPointCMCycleClass : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ), IsStd D gb → ∀ (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N')
    (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X), (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → Etale (c₁.pw k) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
    SmoothOfRelativeDimension (D.n - 1 + k * D.g) (sZ X k) ∧
    ∃ (Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ))) (At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ),
      (∀ x, x ∈ Fx ↔ x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) ∧ (1 - At x).det ≠ 0) ∧
      {x : GlobalTheory.LKCx.AllPts G v (L.KN N') (KHT p G.m G.n 1 G.Fw) | ∃ y, Sees (Quot.out x.1) {g | h * g ∈ L.KN N} (Quot.out x.2) y}.Finite ∧
      (∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (L.KN N : Set G.GAf) a y → y = 1) ∧
      ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t =
        GlobalTheory.RootSumWeights.cxTotalM G v (wtFix L v t₀ α t) (L.KN N') ({g | h * g ∈ L.KN N}.indicator 1) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

def FixZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ), IsStd D gb → ∀ (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N')
    (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X), (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → Etale (c₁.pw k) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
    SmoothOfRelativeDimension (D.n - 1 + k * D.g) (sZ X k) ∧
    ∃ (Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ))) (At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ),
      (∀ x, x ∈ Fx ↔ x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) ∧ (1 - At x).det ≠ 0) ∧
      ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t = ((L.KN N').relIndex (GlobalTheory.HeckeCorr.heckeLevel (L.KN N) h⁻¹) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v (wtFix L v t₀ α t) (L.KN N) (Formalism.UG.dosetInd ℂ (L.KN N) h⁻¹) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∃ kp σ, IsFMat L kp σ

def FForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) kp σ, IsFMat L kp σ → ∃ A : Matrix (Fin G.n) (Fin G.n) G.F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj G.F))ᵀ = -A ∧
    (∀ u w, D.EF.baseChange ℚ u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u))) ∧
    ∀ c, A * σ (sh G c) = ((σ c).map (IsCMField.complexConj G.F))ᵀ * A

def SN : Prop :=
  ∀ (F K : Type) [Field F] [Field K] (n : ℕ) (τ : F →+* K) (ψ : Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) K),
    (∀ x : F, ψ (Matrix.scalar (Fin n) x) = Matrix.scalar (Fin n) (τ x)) →
    ∃ S : Matrix (Fin n) (Fin n) K, S.det ≠ 0 ∧ ∀ M, ψ M * S = S * M.map τ

def ArchSpan : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ),
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) => v.embedding (x i)) = ⊤ ∧
    Module.finrank ℝ (InfinitePlace F → Fin n → ℂ) = n * Module.finrank ℚ F ∧
    ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re

def ArchEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → Nonempty (ArchFrame L)

def SigB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKCx.Form G) (v : InfinitePlace G.F), (GlobalTheory.LKCx.herm G v B.β).IsHermitian ∧
    (sigPosH (G.gram_herm v) = 1 → (∃ z, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re) ∧ ∀ z x, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re →
      x ≠ 0 → hv (GlobalTheory.LKCx.herm G v B.β) x z = 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → ∀ x, x ≠ 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0)

def PerExt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), ∀ w, Q w = R (A.th w)

def JStruct : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    (∀ v, (GlobalTheory.LKCx.herm G v β).IsHermitian) → ∀ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), (∀ w, Q w = R (A.th w)) →
    ∃ J : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ, (∀ x : Arch G, R (fun v => J v *ᵥ x v) = Complex.I • R x) ∧
      ∀ v, IsPosJ (GlobalTheory.LKCx.herm G v β) (J v) (sgnV L v)

def JLine : Prop :=
  ∀ (n : ℕ) (M J : Matrix (Fin n) (Fin n) ℂ) (s : ℂ), M.IsHermitian → (s = 1 ∨ s = -1) → IsPosJ M J s →
    (∀ z, z ≠ 0 → J *ᵥ z = (s * Complex.I) • z → 0 < (hv M z z).re) ∧
    ((∀ x, x ≠ 0 → (hv M x x).re < 0) → J = -(s * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    ((∃ z, 0 < (hv M z z).re) → ∃ z, z ≠ 0 ∧ J *ᵥ z = (s * Complex.I) • z) ∧
    ∀ z, 0 < (hv M z z).re → (∀ x, x ≠ 0 → hv M x z = 0 → (hv M x x).re < 0) → J *ᵥ z = (s * Complex.I) • z →
      ∀ x, J *ᵥ x = (s * Complex.I) • ((2 * (hv M x z / hv M z z)) • z - x)

def HermOfJ : Prop :=
  ∀ (g : ℕ) (E : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ), (∀ x, E x x = 0) → (∀ x y, E (Complex.I • x) (Complex.I • y) = E x y) →
    (∀ x, x ≠ 0 → 0 < E (Complex.I • x) x) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm x y).im = E x y

def LineBasis : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), M.IsHermitian → 0 < (hv M z z).re →
    ∃ (i₀ : Fin n) (S : Matrix (Fin n) (Fin n) ℂ), S.det ≠ 0 ∧ S *ᵥ Pi.single i₀ 1 = z ∧ ∀ i, i ≠ i₀ → hv M (S *ᵥ Pi.single i 1) z = 0

def PlaceT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    (∀ v', sigPosH (G.gram_herm v') = 1 → v' = v) ∧ t₀ (D.ω : D.F) = D.ρc ∧ (starRingEnd ℂ) D.ρc ≠ D.ρc ∧
    ((sgnV L v = 1 ∧ ∀ x, v.embedding (L.e x) = t₀ x) ∨
      (sgnV L v = -1 ∧ (¬ ∀ x, v.embedding (L.e x) = t₀ x) ∧ ∀ x, (starRingEnd ℂ) (v.embedding (L.e x)) = t₀ x))

def TypeIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ i₀ : Fin G.n, ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ),
      (∀ x : Arch G, R (fun v' i => (if v' = v ∧ i = i₀ then 1 else -1) * (sgnV L v' * Complex.I) * x v' i) = Complex.I • R x) ∧
      ∀ (c : 𝓞 D.F) (x : Arch G), R (fun v' => v'.embedding (L.e (c : D.F)) • x v') = ρ (algebraMap (𝓞 D.F) D.O c) *ᵥ R x

def RPer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (A : ArchFrame L) (B : GlobalTheory.LKCx.Form G) (z : GlobalTheory.LKCx.PosV G v B.β),
    ∃ (Q : VQ D →+ (Fin D.g → ℂ)) (R : Arch G →ₗ[ℝ] (Fin D.g → ℂ)), IsPerQ L B.β ρ Q ∧ (∀ w, Q w = R (A.th w)) ∧
      R (Pi.single v (Complex.I • z.1)) = (sgnV L v * Complex.I) • R (Pi.single v z.1)

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRegSep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.regSep_of :
    UpperTheory.Gal.W2.RegSep := by
  intro p _ D G L v hv B a y hfix hreg
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv B.β B.sym B.trivR _ _
    B.trivAf.choose_spec.choose_spec y a.1.1 a.2 hfix hreg
end

