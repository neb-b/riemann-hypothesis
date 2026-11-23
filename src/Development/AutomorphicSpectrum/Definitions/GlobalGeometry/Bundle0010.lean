module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ImaginaryRootConj
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeCptTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem labelEmb_inl_rt (c : Coeff l) (τ : CMType H) : ((labelEmb c (.inl τ) H.rt : c.F) : ℂ) = H.rt0 := τ.2

theorem imaginary_root_conj (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne
      · exact h
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem labelEmb_inr_rt (c : Coeff l) (τ : CMType H) : ((labelEmb c (.inr τ) H.rt : c.F) : ℂ) = -H.rt0 := by
  show τ.1 ((H.bar H.rt : 𝓞 E) : E) = _
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, τ.2, imaginary_root_conj]

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω} (𝔐 : GlobalTheory.CompanionTheory.Ar.HodgeCpt Y S y)

theorem V_isVB (s) : (𝔐.V s).IsVB (labelRk D s) (𝔐.Vgen s) := 𝔐.vb s


theorem flagStep_top {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ} (b : Fin r → F) :
    flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

theorem span_span_regAt {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (q : Cpt ξ) {F : Type} [AddCommGroup F]
    [Module Ω F] (s : Set F) :
    Submodule.span Ω (Submodule.span (regAt ξ q) s : Set F) = Submodule.span Ω s :=
  Submodule.span_span_of_tower _ _ _

theorem flag_span (Fl : 𝔐.Flag) (s) : Submodule.span Ω (Set.range (Fl.b s)) = 𝔐.Vgen s := by
  obtain ⟨U, hU, b, hb, hfr⟩ := V_isVB 𝔐 s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
  obtain ⟨U', hU', b', hb', hfr'⟩ := Fl.sub s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
  have h1 := (hfr _ trivial hU).2
  have h2 := (hfr' _ trivial hU').2
  have h3 := congrArg (fun N : Submodule (regAt 𝔐.ξ ⟨genPt 𝔐.ξ, specializes_rfl⟩) 𝔐.Li =>
    Submodule.span Ω (N : Set 𝔐.Li)) (h2.symm.trans h1)
  have h4 := (span_span_regAt _ _).symm.trans (h3.trans (span_span_regAt _ _))
  rw [← flagStep_top, ← hb', flagStep_top, ← hb, h4]

end GlobalTheory.CompanionTheory.Ar.HodgeCptTest
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

def IsCp {Ω : Type} [CommRing Ω] (p : ℕ) (κ : Ω) : Prop :=
  if p = 2 then κ = 4 else ∃ ζ : Ω, IsPrimitiveRoot ζ p ∧ κ = ζ - 1

abbrev cmConj (E : Type) [Field E] [NumberField E] [IsCMField E] : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

abbrev omP (p : ℕ) : Lat 𝔐.ξ (Module.Dual Ω 𝔐.Li) := 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)

def HTFree (p : ℕ) : Prop :=
  (omP 𝔐 p).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((omP 𝔐 p).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q} (labelRk D s) ⊤

def OverZp (p : ℕ) (q : Cpt 𝔐.ξ) : Prop := ∀ r : ℕ, r.Prime → InFibre 𝔐.ξ r q → r = p

structure IsHTFamily (p : ℕ) (o : Type) [CommRing o] [Algebra o Ω]
    (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)) : Prop where
  act : ∀ s (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), (Dc s).ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)
  e_eq : ∀ s t, (Dc s).e = (Dc t).e
  om_iff : ∀ s w, w ∈ (Dc s).om ↔ ∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q
  om_loc : ∀ s q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q →
    𝔐.M.omLat q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om : Set (Module.Dual Ω 𝔐.Li))
  om'_loc : ∀ s q, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q →
    omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om' : Set (Module.Dual Ω 𝔐.Li))
  glue : ∀ s t q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q →
    ∀ x, ∃ w ∈ 𝔐.M.omLat q, (Dc s).h x = (Dc t).h x + (p ^ 𝔐.R p) • w

def Sandwich (p : ℕ) (κ : Ω) : Prop :=
  ∀ q, InFibre 𝔐.ξ p q → κ ∈ regAt 𝔐.ξ q ∧ omP 𝔐 p q ≤ 𝔐.M.omLat q ∧ (∀ w ∈ 𝔐.M.omLat q, κ • w ∈ omP 𝔐 p q) ∧
    ∀ s, 𝔐.dR s q ≤ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q ∧
      ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q, κ • e ∈ 𝔐.dR s q

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

abbrev under {Xo : Moduli D l} {c : Coeff l} {T : Scheme.{0}} (y : T ⟶ Xo.XF c) : T ⟶ Xo.X := y ≫ pullback.fst _ _

abbrev Vecs {Xo : Moduli D l} {c : Coeff l} {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) : Type :=
  Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)

abbrev FrameFn (Xo : Moduli D l) (c : Coeff l) : Type 1 :=
  ∀ (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), Vecs y D.p → Vecs y D.q → F

variable {Xo : Moduli D l} {c : Coeff l}

def IsFramed (U : Set (Xo.XF c)) (τ : E →+* ℂ) {F : Type} [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c)
    (v : Vecs y D.p) (w : Vecs y D.q) : Prop :=
  y ≫ pullback.snd _ _ = spMap β ∧ Set.range y ⊆ U ∧
    IsEigFrame Xo.univ.t.act (under y) (β.comp (tauIn c τ)) v ∧
    IsEigFrame Xo.univ.t.act (under y) (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w

structure IsLineFn (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) : Prop where
  ne : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w ≠ 0
  chg : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w v' w' (A : Matrix (Fin D.p) (Fin D.p) F)
    (B : Matrix (Fin D.q) (Fin D.q) F), IsFramed U τ β y v w → IsFramed U τ β y v' w' →
    (∀ i, IsComb (A i) v (v' i)) → (∀ j, IsComb (B j) w (w' j)) → φ F y v' w' * A.det = φ F y v w * B.det
  nat : ∀ (F F' : Type) [Field F] [Field F'] (f : F →+* F') (β : c.F →+* F) y v w (y' : Sp F' ⟶ Xo.XF c) v' w',
    IsFramed U τ β y v w → y' = spMap f ≫ y → (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) →
    (∀ j, (w' j).left = spMap (dualMap f) ≫ (w j).left) → φ F' y' v' w' = f (φ F y v w)

def IsConstMul (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) : Prop :=
  ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ)
    (Fm B : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ),
    IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed U τ (algebraMap c.F ℂ) y v w →
    (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
    (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
    (∀ a, tyPart ty τ (∑ m, C a m • P (e m)) = V a) →
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ) (P (e n)) = ∑ j, B j n • W j) →
    (∀ j n, ∑ m, Fm j m * τ (sesq (FU.Di i) (e m) (e n)) = B j n) →
    φ ℂ y v w * (Matrix.fromRows C Fm).det = ρ

structure IsFlatGen (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) : Prop where
  mem : ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
    y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U
  line : IsLineFn U τ φ
  flat : ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), LinearIndependent (𝓞 E) e ∧ IsConstMul U τ φ FU i e ρ

def HasInfNorm (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ) : Prop :=
  ∀ (y : Sp ℂ ⟶ Xo.XF c) v w (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed U τ s y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ →
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ →
    Real.log ‖φ ℂ y v w‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t

def IsIntFrame {V K : Type} [CommRing V] [Field K] [Algebra V K] {y : Sp K ⟶ Xo.XF c} {t : SAB H (Sp V)}
    {tK : SAB H (Sp K)} (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK t (spMap (algebraMap V K)))
    (σ : 𝓞 E →+* K) {n : ℕ} (v : Vecs y n) : Prop :=
  ∃ (σV : 𝓞 E →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ t.G)), (algebraMap V K).comp σV = σ ∧
    IsEigFrame t.act (𝟙 (Sp V)) σV vV ∧ ∀ a, ∃ u : Sp (DualNumber K) ⟶ tK.G.left,
      u ≫ m.φ = (v a).left ∧ u ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (vV a).left

def HasFinNorm (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (j : K →+* ℂ_[p]) (β : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (T : SAB H (Sp V))
    (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))),
    (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp β = κ → IsFramed U τ β y v w →
    IsIntFrame m m' (β.comp (tauIn c τ)) v → IsIntFrame m m' (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w →
    Real.log ‖j (φ K y v w)‖ = t

def HasNorms (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) : Prop :=
  (∀ s, HasInfNorm U τ φ s (N.inf s)) ∧ ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ
    (N.fin p κ + D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖))

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def overPrime (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) : Set (Cpt ξ) :=
  {q | ∀ p' : ℕ, p'.Prime → p' ≠ p → ¬ InFibre ξ p' q}

def IsLatFlagPair {E : Type} [AddCommGroup E] [Module Ω E] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type}
    (y : (Σ k, J k) → Ω) (T : Set (Cpt ξ)) (L L' : Lat ξ E) {r : ℕ} (b : Fin r → E) (Q : LocPair J ℤ (Fin r)) : Prop :=
  L.IsFlagVBOn T b ∧ L'.IsFlagVBOn T b ∧ ∀ i, ∃ e e' : Ω,
    (L.gr b i).IsDegOn T y (Q.x i) e ∧ (L'.gr b i).IsDegOn T y (Q.x' i) e' ∧
    (∃ bf bg : K → ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (Q.f i) bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (Q.g i) bg ∧ (fun k => (bf k : ℤ) - bg k) = Q.x i - Q.x' i) ∧
    aeval y (Q.g i) ≠ 0 ∧ aeval y (Q.f i) = e' / e * aeval y (Q.g i)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def IsFrobLabels (c : Coeff l) (p : ℕ) (φ : Equiv.Perm (CMType H ⊕ CMType H)) : Prop :=
  ∀ n : Ideal (𝓞 c.F), n.IsPrime → (p : 𝓞 c.F) ∈ n → ∀ s (a : 𝓞 E) (u v : 𝓞 c.F),
    (u : c.F) = labelEmb c (φ s) a → (v : c.F) = labelEmb c s a → u - v ^ p ∈ n

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

namespace HodgeCpt

def VAt (𝔐 : HodgeCpt Y S y) (S₀ : Finset ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li :=
  Lat.patch S₀ (𝔐.dR s) fun p => 𝔐.HT p s

def shrink (𝔐 : HodgeCpt Y S y) (S₀ : Finset ℕ) (h : S₀ ⊆ S)
    (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) : HodgeCpt Y S₀ y :=
  { 𝔐 with
    S_prime := fun p hp => 𝔐.S_prime p (h hp)
    R_ge := fun p hp => 𝔐.R_ge p (h hp)
    tors := fun p hp => 𝔐.tors p (h hp)
    vb := hvb }

def Flag.shrink {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S)
    (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s))
    (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) : (𝔐.shrink S₀ h hvb).Flag :=
  @Flag.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (𝔐.shrink S₀ h hvb) Fl.b hsub Fl.Li₀ Fl.acg Fl.mod Fl.M₀ Fl.j
    Fl.j_pt Fl.V₀ Fl.V₀_mem Fl.deg Fl.generic

def Flag.TwoLevels [DecidableEq K] {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) (S₀ : Finset ℕ)
    (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))) : Prop :=
  ∃ (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s))
    (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (e₀ e : CMType H × Fin (D.p + D.q) → Ω),
    (Fl.shrink S₀ h hvb hsub).RootLines T.x e₀ ∧ Fl.RootLines T.x' e ∧
    (∀ r, aeval y (T.f r) = e r / e₀ r * aeval y (T.g r)) ∧
    T.IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn)

end HodgeCpt

end

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open AlgebraicGeometry CategoryTheory NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def rootOnFund {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (r a : Ψ × Fin N) : ℤ :=
  if a.1 = r.1 then (if (a.2 : ℕ) + 1 = r.2 then 1 else 0) - (if a.2 = r.2 then 1 else 0) else 0

def fundOnRoot {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (a r : Ψ × Fin N) : ℤ :=
  if r.1 = a.1 ∧ r.2 ≤ a.2 then -1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


open Classical in
structure HodgeTie (Y : Model Xo c β) (S : Finset ℕ) (n : ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) where

  A : HodgeCpt Y S M.y

  Fl : A.Flag

  e : CMType H × Fin (D.p + D.q) → M.Ω
  roots : Fl.RootLines M.xdeg e

  sing : CMType H × Fin (D.p + D.q) → HermLine M.ι
  sing_deg : ∀ r, (sing r).a = M.xdeg r
  hodge : ∀ r, Fl.IsHodgeLine r (e r) (sing r)

  Sy : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (CMType H × Fin (D.p + D.q))

  Re : PB.Realis Sy M.P
  alg : AlgOver Re
  ref_deg : ∀ a, (Re.ref a).a = (Top.combLine sing (fundOnRoot a)).a
  sing_eq : ∀ a x, Re.π x ∉ ReciprocityTheory.AnForm.P.bdry Sy.s →
    Real.log ((Top.combLine sing (fundOnRoot a)).h (Re.R.lift x x)) =
      Real.log ((Re.ref a).h (Re.R.lift x x)) + Sy.ph a (Re.π x)
  line_eq : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ r, ∀ z ∈ mcPts M.P,
    (M.x t r).h z = (Top.combLine (fun a => Re.line a t) (rootOnFund r)).h z
  δ_eq : M.δ = n * Fl.deg
  discr : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S
  ht_vb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn
    {q | InFibre A.ξ p q} (labelRk D s) ⊤

def IsImageCpt {Y : Model Xo c β} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K]
    [Fintype K'] {J : K → Type} {J' : K' → Type} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (Φ : Xo.X ≅ Xo.X) (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') : Prop :=
  ∃ (x : Sp A.Ω₀ ⟶ Xo.XF c) (x' : Sp A'.Ω₀ ⟶ Xo.XF c) (ψ : A'.Ω₀ ≃+* A.Ω₀),
    A.ξ₀ = x ≫ Y.j ∧ A'.ξ₀ = x' ≫ Y.j ∧
    spMap ψ.toRingHom ≫ x' ≫ Limits.pullback.fst _ _ = x ≫ Limits.pullback.fst _ _ ≫ Φ.hom ∧
    spMap ψ.toRingHom ≫ x' ≫ Limits.pullback.snd _ _ = x ≫ Limits.pullback.snd _ _ ∧
    spMap A.fn ≫ x ≫ Limits.pullback.snd _ _ = spMap A.cst ∧
    spMap A'.fn ≫ x' ≫ Limits.pullback.snd _ _ = spMap A'.cst

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

