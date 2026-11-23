module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def SharpRef (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X) : Prop :=
  ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
    (∀ a, IsMonHom (pr a)) ∧
    (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
    w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
    ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b

def IsThetaTerms (D : DegPre V₁) (N₁ : ℕ) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) : Prop :=
  ∃ (th : Fam D (FractionRing V₁) 1) (g : C → GtPtF D (FractionRing V₁)) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
    (w : ∀ c, Frm D (FractionRing V₁) 1 (g c).b),
    (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) ∧
    (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
    (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V₁ (FractionRing V₁) (T mu c))) ∧
    ∃ c, T 0 c = 1

section Real

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  (X₁ : Setup F W i) (z₁ : X₁.M.Z) {N₁ : ℕ} (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁))

def HasTraits : Prop :=
  ∀ (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V), IsLocalHom ev →
    jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b)

def IsChartMember [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ Z) {m : ℕ} (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X)
    (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k = ρ (t (h k)) ∧ ∀ a b, Φ.δ y k a b = δ (h k) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (e₈ : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e₈ ∧
      IsThetaTerms D N₁ e₈ fun mu c => Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) fun a => e.symm (mu a)

end Real

def Elements {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) (φ : InvFun O) (d : ℕ)
    (ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  ∃ (O' : Subring (Φ.V y)) (g₀ : Φ.V y) (b : Fin (Φ.m y) → ℕ), (∀ h ∈ O', ev h ∈ k₀ ∧ (h ∈ maximalIdeal (Φ.V y) → ev h = 0)) ∧
    (∀ k, (b k : ℝ) = d * φ.evalZ (Φ.δ y k)) ∧ Associated g₀ (∏ k, Φ.t y k ^ b k) ∧
    ∀ (D l : ℕ) (a : Fin l × Fin s → Φ.X y), Dominant bar φ (D * d) N₁ W ga a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ h ∈ O',
      h * g₀ ^ D - Φ.coefT y a c * Φ.monoT y a ∈
        Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e

def Values {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  (∀ k, ev (Φ.t y k) = 0) ∧
  (∀ mu c c', IsUnit (Φ.u y mu c') → ∃ r ∈ k₀, ev (Φ.u y mu c) = r * ev (Φ.u y mu c')) ∧
  ∀ lam : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ, (∀ k, lam (Φ.δ y k) = 0) →
    ∃ (l l' M : ℕ) (a : Fin l × Fin s → Φ.X y) (a' : Fin l' × Fin s → Φ.X y) (c : Fin l → Φ.Q) (c' : Fin l' → Φ.Q), 1 ≤ M ∧
      IsUnit (Φ.coefT y a c) ∧ IsUnit (Φ.coefT y a' c') ∧ (∀ β ∈ balForms bar (Φ.X y), lin W a β - lin W a' β = M * lam β) ∧
      ∃ r ∈ k₀, ev (Φ.coefT y a c) = r * ev (Φ.coefT y a' c')

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {F : SFam g n ζ}

def OrdGe (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def OrdEq (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def ThroughU {X : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (c : X ⟶ F.X) (T : Trait F) (ξ : Sp T.V ⟶ M.Z) : Prop :=
  ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ ξ₀ ≫ u₀ ≫ c = T.y

variable {M}

variable (M)

end Ord

def TraitExtSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (T : Trait F) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
        f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def TraitUniqSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T T' : Trait F) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (f : T.V →+* W) (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W)
    (fK' : FractionRing T'.V →+* FractionRing W), GlobalTheory.Mum.Base W → IsDiscreteValuationRing W →
    Function.Injective f → Function.Injective f' → IsLocalHom f → IsLocalHom f' →
    (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) →
    spMap fK ≫ T.y = spMap fK' ≫ T'.y → ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) →
      Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.D.toPre.X ≃+ T'.D.toPre.X, ∀ a b, (m : ℤ) * T.β a b = m' * T'.β (e a) (e b)

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop
open scoped ENNReal

namespace GlobalTheory.CovHt

def cost {K : Type} [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ) : ℝ :=
  ((e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) + ∑ σ, t σ) / (Module.finrank ℚ K : ℝ)

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def depthOn (Z : Comp Xo c) (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latOn U Z G, v (w : Rul Xo c)

def smallL (Z : Comp Xo c) (G : WTZ E) (τ : ℕ) (t : ℝ) : Set (cuspOn U Z (τ • G)) :=
  {f | (∀ la, ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) ∧
    ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      ENNReal.ofReal (homN (U σ) x (τ • G) f ⟨y.1, y.2.1⟩) ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * τ * t)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ τ}

def volL (a : ℕ) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (Module.finrank ℚ c.F) a fun τ => (smallL U x V dict Z G τ t).encard

def FinBd (Z : Comp Xo c) (G : WTZ E) (a : ℕ) (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, (∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤) →
    (a : EReal) * depthOn U Z G v ≤ v θ + ((a * e la : ℝ) : EReal)

def NoBase (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, ∀ G' : WTZ E, ∀ f ∈ cuspOn U Z G', v f ≠ ⊤ → ∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤

def InfBd (Z : Comp Xo c) (G G₀ : WTZ E) (a : ℕ) (θ : Rul Xo c) (t : (c.F →+* ℂ) → ℝ) : Prop :=
  (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) ∧
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    ENNReal.ofReal (homN (U σ) x G₀ θ ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * a * t σ)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ a

def Carries (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (θ : Rul Xo c) : Prop :=
  θ ∈ secZ Xo c (exOf Dw ((8 : ℤ) • (u - u')) 0) ∧ genVal Z θ ≠ 0 ∧
    ∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((8 * k) • wtOf Dw u' 0), θ ^ k * f ∈ cuspOn U Z ((8 * k) • wtOf Dw u 0)

def Mult (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc : ℝ) : Prop :=
  NoBase U Z (wtOf Dw u 0) ∧ ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ),
    Carries U Z u u' θ ∧ FinBd U Z (wtOf Dw u 0) 8 θ e ∧
    InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc

def l1 (u : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ i, |(u τ i : ℝ)|


variable (E) in
def htEx (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) + 40 * ((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))


variable (Xo c) in
def HTCmp : Prop := ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
  ∀ v ∈ (recVals Xo c).1 la, ∃ w ∈ (htVals Xo c).1 la, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0),
    w f ≤ v f + (((vLa la (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal)


variable (l) in
def htCost (B : ℝ) : ℝ := ∑ᶠ p ∈ htPrimes l B, htEx E p * Real.log p

def WtGap (u : AllWt.Weight Dw) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ, StrictAnti (u τ)) ∧ ∀ τ (a b : Fin (Dw.p + Dw.q)), Dw.p ≤ (a : ℕ) → a ≠ b → g ≤ |(u τ a : ℝ) - u τ b|

def bndB (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  4 * (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (1 + (⨆ k : Psi H × Fin (Dw.p + Dw.q), |(u k.1 k.2 : ℝ)|) / g)

def errX (s : ℝ) (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  (Real.log (bndB u g) + s) * l1 u + (Dw.q : ℝ) * ∑ τ, ((⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ))

def MeanGe (u : AllWt.Weight Dw) (B X : ℝ) : Prop :=
  ∃ sl : Comp Xo c → ℝ, (∀ Z, (sl Z : EReal) ≤ compVolSlope U x 8 (mixVals Xo c B) Z u) ∧
    -X ≤ (∑ᶠ Z, sl Z) / (Nat.card (Comp Xo c) : ℝ)

def MeanAll (s C : ℝ) : Prop := ∀ (u : AllWt.Weight Dw) (g : ℝ), WtGap u g → MeanGe U x u (bndB u g) (C * errX s u g)

end Generic

def ell (D : D7) : ℝ := Real.log D.host.rdE + |dlogL D 1|

section One

open MvPolynomial Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs

variable {D : D7} (Y : ShimX D.what₂.Tau)

def DeRhamMinusHodgeTateGoodPrimesAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ Y.lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau Y.N + 1 → ∀ Q : MvPolynomial (Vm D.what₂.Tau Y.N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
    Y.arMix Sx R p ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * collapse D _ Q)) -
        Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * collapse D _ Q) / ((p : ℝ) - 1))

def DeRhamHodgeTateDifferenceKilledAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    Y.arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

end One



section Obj

open GlobalTheory.Mean4 GlobalTheory.Mean4O Formalism.BasicNotions.DV


structure HypothesesH : Prop where
  sieg : GlobalTheory.Published.SiegelToroidalIntegral
  fan : GlobalTheory.Published.ToroidalChartsForFan
  charts : GlobalTheory.Published.ToroidalCharts
  deg : GlobalTheory.Published.ArDegree

end Obj

end GlobalTheory.CovHt

end
end

