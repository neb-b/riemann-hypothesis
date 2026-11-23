module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def lin (φ : Pt R 1 d) (m : ℕ) : Matrix (Fin d) (Fin d) R :=
  fun i j => coeff (Finsupp.single ((0 : Fin 1), j) m) (φ i)

def bil (f : PS R 2 d) (m n : ℕ) : Matrix (Fin d) (Fin d) R :=
  fun i j => coeff (Finsupp.single ((0 : Fin 2), i) m + Finsupp.single ((1 : Fin 2), j) n) f

def AxOne (f : PS R 2 d) : Prop := ev (n := 1) ![0, pt R d 0] f = 1 ∧ ev (n := 1) ![pt R d 0, 0] f = 1

def ptPow (R : Type) [CommRing R] {n : ℕ} (d p : ℕ) (j : Fin n) : Pt R n d := fun i => X (j, i) ^ p

def rho (B : FB R d O) (a : O) : Matrix (Fin d) (Fin d) R := lin (B.A.act a) 1

def pow1 (B : FB R d O) (m : ℕ) : PS R 2 d :=
  ∏ n ∈ Finset.range m, ev (n := 2) ![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 0, pt R d 1] B.ph1

def pow2 (B : FB R d O) (m : ℕ) : PS R 2 d :=
  ∏ n ∈ Finset.range m, ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1), pt R d 1] B.ph2

def hw (B : FB R d O) (p : ℕ) : Matrix (Fin d) (Fin d) R := lin (B.A.act (p : O)) p

def am (B : FB R d O) (p : ℕ) : Matrix (Fin d) (Fin d) R := bil (pow1 B p) p 1

def rhoH (B : FB R d O) (a : O) : Module.End R ((Fin d → R) × (Fin d → R)) :=
  LinearMap.prod (Matrix.toLin' (rho B a) ∘ₗ LinearMap.fst R _ _)
    (Matrix.toLin' (rho B (star a)).transpose ∘ₗ LinearMap.snd R _ _ -
      Matrix.toLin' (bil (B.ad a) 1 1).transpose ∘ₗ LinearMap.fst R _ _)

def pairH (B : FB R d O) (y y' : (Fin d → R) × (Fin d → R)) : R :=
  y'.2 ⬝ᵥ y.1 - y.2 ⬝ᵥ y'.1 + y.1 ⬝ᵥ (bil B.sy 1 1).mulVec y'.1

def alpha (B : FB R d O) (p : ℕ) : (Fin d → R) →ₗ[R] (Fin d → R) × (Fin d → R) :=
  LinearMap.prod (Matrix.toLin' (hw B p)) (Matrix.toLin' (am B p).transpose)

def beta (B : FB R d O) (p : ℕ) : ((Fin d → R) × (Fin d → R)) →ₗ[R] (Fin d → R) :=
  Matrix.toLin' (hw B p).transpose ∘ₗ LinearMap.snd R _ _ -
    Matrix.toLin' (am B p - (hw B p).transpose * bil B.sy 1 1) ∘ₗ LinearMap.fst R _ _

structure IsMapOf {R₂ : Type} [CommRing R₂] (f : R →+* R₂) (B : FB R d O) (B₂ : FB R₂ d O) : Prop where

  F : ∀ i, B₂.G.F i = MvPowerSeries.map f (B.G.F i)

  act : ∀ a i, B₂.A.act a i = MvPowerSeries.map f (B.A.act a i)

  ph1 : B₂.ph1 = MvPowerSeries.map f B.ph1

  ph2 : B₂.ph2 = MvPowerSeries.map f B.ph2

  sy : B₂.sy = MvPowerSeries.map f B.sy

  ad : ∀ a, B₂.ad a = MvPowerSeries.map f (B.ad a)

structure IsIso (B B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) : Prop where

  c₁ : ∀ i, constantCoeff (φ i) = 0

  c₂ : ∀ i, constantCoeff (ψ i) = 0

  inv₁ : comp1 φ ψ = pt R (n := 1) d 0

  inv₂ : comp1 ψ φ = pt R (n := 1) d 0

  ax : AxOne lam

  law : comp1 φ (B₂.G.add (pt R (n := 2) d 0) (pt R d 1)) = B.G.add (comp1 φ (pt R d 0)) (comp1 φ (pt R d 1))

  act : ∀ a, comp1 φ (B₂.A.act a) = comp1 (B.A.act a) φ

  ph1 : B₂.ph1 * ev (n := 3) ![B₂.G.add (pt R d 0) (pt R d 1), pt R d 2] lam =
    ev (n := 3) ![pt R d 0, pt R d 2] lam * ev (n := 3) ![pt R d 1, pt R d 2] lam *
      ev (n := 3) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1), comp1 φ (pt R d 2)] B.ph1

  ph2 : B₂.ph2 * ev (n := 3) ![pt R d 0, B₂.G.add (pt R d 1) (pt R d 2)] lam =
    ev (n := 3) ![pt R d 0, pt R d 1] lam * ev (n := 3) ![pt R d 0, pt R d 2] lam *
      ev (n := 3) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1), comp1 φ (pt R d 2)] B.ph2

  sy : B₂.sy * lam = ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] B.sy *
    ev (n := 2) ![pt R d 1, pt R d 0] lam

  ad : ∀ a, B₂.ad a * ev (n := 2) ![pt R d 0, comp1 (B₂.A.act (star a)) (pt R d 1)] lam =
    ev (n := 2) ![comp1 (B₂.A.act a) (pt R d 0), pt R d 1] lam *
      ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (B.ad a)

def transH (φ ψ : Pt R 1 d) (lam : PS R 2 d) : ((Fin d → R) × (Fin d → R)) →ₗ[R] (Fin d → R) × (Fin d → R) :=
  LinearMap.prod (Matrix.toLin' (lin φ 1) ∘ₗ LinearMap.fst R _ _)
    (Matrix.toLin' (lin ψ 1).transpose ∘ₗ
      (LinearMap.snd R _ _ + Matrix.toLin' (bil lam 1 1).transpose ∘ₗ LinearMap.fst R _ _))

def ConjInj (B : FB R d O) (p : ℕ) : Prop := Function.Injective (alpha B p)

structure Family {K : Type} [Field K] (C : ACurve K) (p d : ℕ) (O : Type) [CommRing O] [StarRing O] where

  B : FB K d O

  Bi : ∀ i : C.I, FB (C.v i).valuationSubring d O

  BK : C.I → FB K d O

  Bk : ∀ i : C.I, FB (IsLocalRing.ResidueField (C.v i).valuationSubring) d O

  mapK : ∀ i, IsMapOf (C.v i).valuationSubring.subtype (Bi i) (BK i)

  mapk : ∀ i, IsMapOf (IsLocalRing.residue _) (Bi i) (Bk i)

  inj : ∀ i, ConjInj (Bk i) p

  φ : C.I → Pt K 1 d

  ψ : C.I → Pt K 1 d

  lam : C.I → PS K 2 d

  iso : ∀ i, IsIso B (BK i) (φ i) (ψ i) (lam i)

  ae : {i | ¬ ∀ a b, C.v i (lin (φ i) 1 a b) ≤ 1 ∧ C.v i (lin (ψ i) 1 a b) ≤ 1 ∧
    C.v i (bil (lam i) 1 1 a b) ≤ 1}.Finite

theorem rhoH_apply (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)) :
    rhoH B a y = ((rho B a).mulVec y.1,
      (rho B (star a)).transpose.mulVec y.2 - (bil (B.ad a) 1 1).transpose.mulVec y.1) := by
  simp [rhoH]

theorem alpha_apply (B : FB R d O) (p : ℕ) (u : Fin d → R) :
    alpha B p u = ((hw B p).mulVec u, (am B p).transpose.mulVec u) := by
  simp [alpha]

theorem beta_apply (B : FB R d O) (p : ℕ) (y : (Fin d → R) × (Fin d → R)) :
    beta B p y = (hw B p).transpose.mulVec y.2 -
      (am B p - (hw B p).transpose * bil B.sy 1 1).mulVec y.1 := by
  simp [beta, Matrix.toLin'_apply, Matrix.sub_mulVec]

theorem transH_apply (φ ψ : Pt R 1 d) (lam : PS R 2 d) (y : (Fin d → R) × (Fin d → R)) :
    transH φ ψ lam y = ((lin φ 1).mulVec y.1,
      (lin ψ 1).transpose.mulVec (y.2 + (bil lam 1 1).transpose.mulVec y.1)) := by
  simp only [transH, LinearMap.prod_apply, Function.prod_apply, LinearMap.add_apply, LinearMap.comp_apply,
    Matrix.toLin'_apply, LinearMap.fst_apply, LinearMap.snd_apply]

theorem rhoH_inr (B : FB R d O) (a : O) (φ : Fin d → R) :
    rhoH B a (0, φ) = (0, (rho B (star a)).transpose.mulVec φ) := by
  simp [rhoH_apply]

theorem rhoH_fst (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)) :
    (rhoH B a y).1 = (rho B a).mulVec y.1 := by
  rw [rhoH_apply]

theorem dotProduct_beta (B : FB R d O) (p : ℕ) (u : Fin d → R) (y : (Fin d → R) × (Fin d → R)) :
    u ⬝ᵥ beta B p y = pairH B (alpha B p u) y := by
  rw [beta_apply, alpha_apply]
  simp only [pairH, Matrix.sub_mulVec, dotProduct_sub, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
  have key : u ⬝ᵥ Matrix.vecMul ((bil B.sy 1 1).mulVec y.1) (hw B p) =
      Matrix.vecMul ((hw B p).mulVec u) (bil B.sy 1 1) ⬝ᵥ y.1 := by
    rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec]
  rw [key, dotProduct_comm u]
  ring

theorem beta_alpha_apply (B : FB R d O) (p : ℕ) (u : Fin d → R) :
    beta B p (alpha B p u) = ((hw B p).transpose * (am B p).transpose - am B p * hw B p +
      (hw B p).transpose * bil B.sy 1 1 * hw B p).mulVec u := by
  rw [alpha_apply, beta_apply]
  simp only [Matrix.sub_mul, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  abel

theorem bil_one_eq_zero {m : ℕ} (hm : m ≠ 0) (n : ℕ) : bil (1 : PS R 2 d) m n = 0 := by
  ext i j
  simp only [bil, MvPowerSeries.coeff_one, Matrix.zero_apply]
  apply ite_eq_right
  intro h
  have h0 := congrArg (fun f => f ((0 : Fin 2), i)) h
  simp at h0
  exact hm h0

theorem lin_pt_eq_one : lin (pt R (n := 1) d 0) 1 = 1 := by
  ext i j
  simp [lin, pt, MvPowerSeries.coeff_X, Matrix.one_apply, Finsupp.single_eq_single_iff]
  exact if_congr eq_comm rfl rfl

theorem IsMapOf.trans {R₂ R₃ : Type} [CommRing R₂] [CommRing R₃] {f : R →+* R₂} {g : R₂ →+* R₃} {B : FB R d O}
    {B₂ : FB R₂ d O} {B₃ : FB R₃ d O} (h : IsMapOf f B B₂) (h' : IsMapOf g B₂ B₃) : IsMapOf (g.comp f) B B₃ := by
  constructor
  · intro i
    simp only [h'.F, h.F, MvPowerSeries.map_comp, RingHom.comp_apply]
  · intro a i
    simp only [h'.act, h.act, MvPowerSeries.map_comp, RingHom.comp_apply]
  · simp only [h'.ph1, h.ph1, MvPowerSeries.map_comp, RingHom.comp_apply]
  · simp only [h'.ph2, h.ph2, MvPowerSeries.map_comp, RingHom.comp_apply]
  · simp only [h'.sy, h.sy, MvPowerSeries.map_comp, RingHom.comp_apply]
  · intro a
    simp only [h'.ad, h.ad, MvPowerSeries.map_comp, RingHom.comp_apply]

theorem ev_pt_self {n : ℕ} (a : Fin n → Pt R n d) (ha : ∀ j, a j = pt R d j) (f : PS R n d) : ev a f = f := by
  have hx : (fun q : Fin n × Fin d => a q.1 q.2) = MvPowerSeries.X := by
    funext q
    rw [ha]
    rfl
  show MvPowerSeries.subst (fun q : Fin n × Fin d => a q.1 q.2) f = f
  rw [hx, MvPowerSeries.subst_self]
  rfl

theorem germ_comp1_zero_point_left {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) : comp1 (pt R d 0) a = a := by
  funext i
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![a] : Fin 1 → Pt R n d) q.1 q.2) :=
    ⟨fun q => by
      rcases q with ⟨j, k⟩
      fin_cases j
      simp [ha], fun _ => Set.toFinite _⟩
  show MvPowerSeries.subst (fun q : Fin 1 × Fin d => (![a] : Fin 1 → Pt R n d) q.1 q.2) (MvPowerSeries.X ((0 : Fin 1), i)) = a i
  rw [MvPowerSeries.subst_X hs]
  rfl

section Gauge

open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

end Gauge

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTChart (A K : Type) [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (p R N : ℕ)
    (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] where

  om : Submodule A Ω
  om_lat : om.IsFullLattice K
  om_proj : Module.Projective A om

  ρΩ : 𝓞 E →+* Module.End K Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)
  alt : ∀ x, e x x = 0
  adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)
  e_surj : ∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ
  e_inj : ∀ x, e x = 0 → ∃ x', x = (p ^ R) • x'

  h : (Fin N → 𝓞 E) →+ Ω
  h_mem : ∀ x, h x ∈ om
  h_lin : ∀ (a : 𝓞 E) (x : Fin N → 𝓞 E), ∃ y ∈ om, h (a • x) = ρΩ a (h x) + (p ^ R) • y

namespace HTChart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

def om' : Submodule A Ω :=
  Submodule.span A (Set.range D.h) ⊔ D.om.map (((p : A) ^ R) • LinearMap.id)

def omHT (σ : E →+* K) : Submodule A Ω := eigQuot D.ρΩ σ D.om'

def q (σ : E →+* K) (x : Fin N → A) : Ω := ∑ i, x i • eigProj D.ρΩ σ (D.h (Pi.single i 1))

def gram (σ : E →+* K) (d : A) (i j : Fin N) : K :=
  ∑ k, algebraMap A K d * σ (dualInt E k) *
    ((D.e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : K)

def IsDualMap (σ : E →+* K) (d : A) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  ∀ (w : Module.Dual A (D.omHT (σ.comp c.toRingHom))) (j : Fin N)
    (y : D.omHT (σ.comp c.toRingHom)),
    (y : Ω) = eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single j 1)) →
      ∃ z : A, ∑ l, algebraMap A K (i w l) * D.gram σ d l j = algebraMap A K (w y + (p : A) ^ m * z)

def ExactMod (σ : E →+* K) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  (∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)),
    ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w') ∧
  (∀ x : Fin N → A, (∃ y ∈ D.omHT σ, D.q σ x = ((p : A) ^ m) • y) ↔
    ∃ w, ∃ x' : Fin N → A, x = i w + ((p : A) ^ m) • x') ∧
  ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y'

structure ReducesTo {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ N V Ω') (ι : D.om →ₛₗ[φ] Ω') : Prop where
  span_eq : Submodule.span O (Set.range ι) = P.om
  rank_eq : Module.finrank K Ω = Module.finrank C Ω'
  lin : ∀ (a : 𝓞 E) (x : D.om), ι ⟨D.ρΩ a x, D.om_stable a x x.2⟩ = P.ρΩ a (ι x)
  ht_eq : ∀ x, ∃ y ∈ P.om, ι ⟨D.h x, D.h_mem x⟩ = P.ht (P.tate x) + (p ^ R) • y
  e_eq : ∀ x y, ∃ z : O, P.e (P.tate x) (P.tate y) =
    algebraMap O C (((D.e x y).val : O) + (p : O) ^ R * z)

def HasTestPoints (κ : A) : Prop :=
  ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 →
    ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : Algebra O C)
      (v : Valuation C NNReal) (φ : A →+* O)
      (V Ω' : Type) (_ : AddCommGroup V) (_ : Module C V) (_ : Module O V) (_ : IsScalarTower O C V)
      (_ : AddCommGroup Ω') (_ : Module C Ω') (_ : Module O Ω') (_ : IsScalarTower O C Ω')
      (P : HTPoint C O c (φ κ) N V Ω') (ι : D.om →ₛₗ[φ] Ω'),
      v.Integers O ∧ Function.Injective φ ∧ (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1) ∧
        D.ReducesTo φ P ι

end HTChart

def GeneratesDiff {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E]
    [NumberField E] (σ : E →+* K) (d : A) : Prop :=
  Submodule.span A {algebraMap A K d} =
    Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
section
namespace GlobalTheory.CompanionTheory.Ar.Num

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
  [AddCommGroup V₂] [Module Ω V₂]

def IsLatFamily (x : (Σ k, ι k) → Ω) (Γ : (∀ k, ι k) → AddSubgroup V) : Prop :=
  (∀ s, mseg x s ≠ 0 → ∀ a ∈ chartRing o (mseg x) s, ∀ v ∈ Γ s, a • v ∈ Γ s) ∧
  ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∀ v ∈ Γ s, ∃ m : ℕ, (mseg x s / mseg x t) ^ m • v ∈ Γ t

def IsQuotHom (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (Γ : (∀ k, ι k) → AddSubgroup (V × V₁)) : Prop :=
  IsLatFamily o x Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v w, (v, w) ∈ Γ s → v ∈ A s ∧ w ∈ B s) ∧ (∀ v ∈ A s, ∃ w, (v, w) ∈ Γ s) ∧
    (∀ w, (0, w) ∈ Γ s ↔ w ∈ B' s) ∧ (∀ v ∈ A' s, (v, 0) ∈ Γ s)

def QuotEquiv (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  ∃ Γ, IsQuotHom o x A A' B B' Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ w ∈ B s, ∃ v, (v, w) ∈ Γ s)

def QuotExact (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (C C' : (∀ k, ι k) → AddSubgroup V₂) : Prop :=
  ∃ Γ Δ, IsQuotHom o x A A' B B' Γ ∧ IsQuotHom o x B B' C C' Δ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ c ∈ C s, ∃ b, (b, c) ∈ Δ s) ∧
    (∀ b, (b, 0) ∈ Δ s ↔ ∃ a, (a, b) ∈ Γ s)

def IsScaled (x : (Σ k, ι k) → Ω) (c : Ω) (A A' : (∀ k, ι k) → AddSubgroup V) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A' s ↔ ∃ e ∈ A s, v = c • e

def IsLine (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) (A : (∀ k, ι k) → AddSubgroup Ω) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A s ↔ ∃ r ∈ chartRing o (mseg x) s, v = r * (u * chartMon x s a)

def IsDualLat (x : (Σ k, ι k) → Ω) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (A : (∀ k, ι k) → AddSubgroup V)
    (B : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  Function.Bijective β.flip ∧
    ∀ s, mseg x s ≠ 0 → ∀ w, w ∈ B s ↔ ∀ v ∈ A s, β v w ∈ chartRing o (mseg x) s

def TrivFlagMod (ϖ : o) (x : (Σ k, ι k) → Ω) (N : ℕ) (b : Fin N → K → ℤ) : Prop :=
  ∃ g : (∀ k, ι k) → Matrix (Fin N) (Fin N) Ω,
    (∀ s, mseg x s ≠ 0 → (∀ i j, g s i j ∈ chartRing o (mseg x) s) ∧
      ∃ h ∈ chartRing o (mseg x) s, ∃ r ∈ chartRing o (mseg x) s,
        (g s).det * h = 1 + algebraMap o Ω ϖ * r) ∧
    ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∃ (m : ℕ) (U Z : Matrix (Fin N) (Fin N) Ω),
      (∀ i j, U i j ∈ chartRing o (mseg x) t) ∧ (∀ i j, Z i j ∈ chartRing o (mseg x) t) ∧
      (∀ i j, j < i → U i j = 0) ∧
      (∀ i, U i i = (mseg x s / mseg x t) ^ m * (chartMon x s (b i) / chartMon x t (b i))) ∧
      (∀ i j, (mseg x s / mseg x t) ^ m * g s i j ∈ chartRing o (mseg x) t) ∧
      (mseg x s / mseg x t) ^ m • g s = g t * U + algebraMap o Ω ϖ • Z

end GlobalTheory.CompanionTheory.Ar.Num
end

