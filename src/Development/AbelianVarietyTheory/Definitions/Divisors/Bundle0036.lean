module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Formalism.RealPlaceAnalysis.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

namespace GlobalTheory.LowRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def AdelC (F : Face D A) : Prop :=
  GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (b : ℝ), Sizes D i b → ∀ t : T, PrimeToHost R t →
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s →
  ∀ P : LevelP R.Pg D.R.r ℂ, IsLocalLevel P →
  ∀ (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), IsConjChars R i t s cμ cη m →
  ∀ ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ),
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω →
  ∀ BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) →
  ∀ f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ,
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f →
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) →
  ∀ c : CoefA (Vc D i), c.Is →
  ∀ io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io →
  ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))),
    IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)) ν 𝓕 →
  ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y →
  ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
    HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y) →
    (∃ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th) ∧
    ∀ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th →
      ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ t P ev, th (adjLev P th x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l

def LiftIsCuspC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f c io =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ φ ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)),
      ∃ U ∈ R.Wall i σ, ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)), U (fun ρ => v ρ) g =
        Lift.thetaPInt ν 𝓕 (fun g h f => Datum.thetaKO ω h g f) (ptAt R i σ BW f) io (c.ext φ) (PiTensorProduct.tprod ℂ v) g


open Datum in
def FiniteZetaC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P _ ω _ f _ _ =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ,
        (∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2)) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (eulerOff D (finS R t) x / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))

def FormalDegreeUpperC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i _ σ _ _ _ _ _ _ _ =>
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ (ρ : D.what₂.Tau) (mR : Measure (Upq (Wc D i) ρ)), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ 0 < ∫ b, k b ∂mR ∧
        Real.log (∫ b, k b ∂mR)⁻¹ ≤
          2 + (D.R.r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (D.R.r : ℝ) ^ 2 * D.R.nV * ((degAt D i σ ρ : ℝ) + 2))

def GalOut (i : Fin D.R.m) (ph : ℂ) : Prop :=
    (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) ∧
    (∀ gramR c0R c0L,
      Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
      ∀ σ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i)) ∧
    ∀ σ, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK ((starRingEnd ℂ).comp σ) ∧
      ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
        starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ

def StdV (D : D7) : Prop := ∀ i : Fin D.R.m, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)

end

def ConjRatLift5 : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    GlobalTheory.Core5 R F → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) →
    ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
     GalOut R i ph

end GlobalTheory.LowRow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def toSub {G : Type} [Group G] (H : Subgroup G) (g : G) : H := if h : g ∈ H then ⟨g, h⟩ else 1

def trOn {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (L : V →ₗ[ℂ] V) : ℂ :=
  if h : ∀ v ∈ M, L v ∈ M then LinearMap.trace ℂ M (L.restrict h) else 0

def hint {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) : ℂ :=
  (((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out

def IsMu (μ : HChar E) (e : InfinitePlace E → ℤ) : Prop :=
  μ.IsUnitary ∧ (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) ∧
    (∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1)) ∧ (∀ v, Odd (e v)) ∧
    ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v

def blk {a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw n w :=
  let M := Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
    (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)
  if hM : IsUnit M then hM.unit else 1

def intMat (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
  Subgroup.closure {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}

def ct {a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
    hint (intMat a b w) fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)

def ctMu {a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
    ct h w (fun y => f (toSub _ y)) m

def iwGL (n : ℕ) (w : Pl E) : Subgroup (GLw n w) := GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)

def tdiag {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) : GLw n w :=
  GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) fun i => ϖ ^ a i

def dcos (n : ℕ) (w : Pl E) (t : GLw n w) : GLw n w → ℂ :=
  fun y => if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

def IsUnifAt {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) : Prop := ordL (ϖ : w.adicCompletion E) = 1 ∧ cj w ϖ = ϖ

def IsWitt (n : ℕ) (w : Pl E) (b : GLw n w) : Prop :=
  b ∈ GlobalTheory.LFun.KGL w (n := n) ∧ (b.val.map (cj w))ᵀ * b.val = antiJ (w.adicCompletion E) n

def iwU (n : ℕ) (w : Pl E) (b : GLw n w) : Subgroup (UL n w) :=
  ((iwGL n w).map (MulAut.conj b).toMonoidHom).subgroupOf (UL n w)

def wexp (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < n / 2 then l ⟨i, h⟩ else if h' : n - 1 - i.val < n / 2 then -l ⟨_, h'⟩ else 0

def Cone {m : ℕ} (l : Fin m → ℤ) : Prop := (∀ i j : Fin m, (j : ℕ) = i + 1 → 2 ≤ l i - l j) ∧ ∀ i, 2 ≤ l i

def fU (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) : UL n w → ℂ :=
  fun γ => if ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 then 1 else 0

def qh (w : Pl E) : ℂ := (Real.sqrt (qV E w : ℝ) : ℝ)

def dlt (n : ℕ) (w : Pl E) (l : Fin (n / 2) → ℤ) : ℂ := qh w ^ (∑ i : Fin (n / 2), ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)

def vRes (n a : ℕ) (l : Fin (n / 2) → ℤ) (s : Finset (Fin (n / 2))) : ℤ :=
  -2 * (∑ i ∈ s, ∑ j ∈ sᶜ, max (l i) (l j)) -
    (if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, l j else ∑ j ∈ s, l j) else 0)

def HasVals {w : Pl E} (Q : (w.adicCompletion E)[X]) (a : Fin n → ℤ) : Prop :=
  ∃ u : Fin n → w.adicCompletion E, Q = ∏ i, (X - C (u i)) ∧ ∀ i, u i ≠ 0 ∧ ordL (u i) = a i

def pw {m : ℕ} (y : Fin m → ℂˣ) (l : Fin m → ℤ) : ℂ := ∏ i, ((y i ^ l i : ℂˣ) : ℂ)

def SatUL {w : Pl E} (b : GLw n w) (ϖ : w.adicCompletion E) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (p : UL n w ≃* GU (cj w) n) (σ' : SmIrr (GU (cj w) n)), (∀ x, (p x).1 = b⁻¹ * x.1 * b) ∧
    GlobalTheory.LFun.HasSatU ϖ q σ'.ρ α ∧ Nonempty (σ.ρ.Equiv (σ'.ρ.comp p.toMonoidHom))

def UE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (GL (Fin n) E) :=
  UJ (IsCMField.complexConj E).toRingEquiv.toRingHom 1

def finPt (γ : UE E n) : finU (E := E) (n := n) := toSub _ (toSub _ (finGL E n (ratF E n γ.1)))

def ratFinU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (finU (E := E) (n := n)) :=
  (((UE E n).map ((finGL E n).comp (ratF E n))).comap (UA E n).subtype).comap (finU (E := E) (n := n)).subtype

def locPt (w : Pl E) (γ : UE E n) : UL n w := toSub _ (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)

def globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Subgroup (finU (E := E) (n := n)) :=
  ⨅ w ∈ S, ((K' w).map (UL n w).subtype).comap ((cLoc w).comp (finU (E := E) (n := n)).subtype)

def globFn (S : Set (Pl E)) (f : ∀ w : Pl E, UL n w → ℂ) (x : finU (E := E) (n := n)) : ℂ := ∏ᶠ w ∈ S, f w (toSub _ (cLoc w x.1))

def RF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Representation ℂ (finU (E := E) (n := n)) (UA E n → ℂ) :=
  (RU E n).comp (finU (E := E) (n := n)).subtype

def forms (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (UA E n → ℂ) :=
  ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)),
    π ⊓ fixed (RF E n) (globLev S K')

def hop (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) :
    (UA E n → ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
  levOp (RF E n) (globLev S (KL n)) (globLev S K') (globFn S f) LinearMap.id

def dimW (lam : InfinitePlace E → DomWeight n) : ℂ :=
  ∏ v, LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (lam v) 1)

def geomURat (lam : InfinitePlace E → DomWeight n) (orb : UE E n → ℂ) : ℂ :=
  ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then
    mass (MonoidHom.id _) (ratFinU E n) (finPt c.rep) * chW lam c.rep.1.val.charpoly * orb c.rep else 0

def nfac {k : Type} [Field k] (P : k[X]) : ℕ := Multiset.card (UniqueFactorizationMonoid.normalizedFactors P)

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ReadsOnlyOmegaFree
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

open Classical

theorem rank_W_le_V : (Wc D i).rank ≤ (Vc D i).rank :=
  (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)

theorem readsOnly_omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    ReadsOnly (R.Pg ∪ Q) (omegaFree R i Q ξR y₀) := by
  intro y y' h
  have hg : ∀ PP ∈ R.Pg, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_left _ hp)
  have hq : ∀ PP ∈ Q, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_right _ hp)
  unfold omegaFree
  congr 1
  · exact if_congr ⟨fun H PP hp => (hg PP hp) ▸ H PP hp, fun H PP hp => (hg PP hp).symm ▸ H PP hp⟩ rfl rfl
  · by_cases H : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det
    · have H' : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun PP hp => (hq PP hp) ▸ H PP hp
      rw [dite_eq_left H, dite_eq_left H']
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (H PP.1 PP.2).unit = (H' PP.1 PP.2).unit := by
        ext; simp [hq PP.1 PP.2]
      rw [this]
    · have H' : ¬ ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun H' =>
        H fun PP hp => (hq PP hp).symm ▸ H' PP hp
      rw [dite_eq_right H, dite_eq_right H']

end GlobalTheory.OnCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

def Le (B A : HermLB p) : Prop :=
  ∃ P : Pair p, P.L = A ∧ P.A = B ∧ (1 : X.functionField) ∈ P.Bl 1 (-1) 1


omit [IsIntegral X] in
def HtNef (M : HermLB p) (D : ℕ) : Prop :=
  M.SemiPos D ∧ ∀ h : X → ℝ, M.IsArithHeight h → ∀ x, 0 ≤ h x

def Total {J : Type} (f : J → X.functionField) : Prop :=
  (∀ j, f j ≠ 0) ∧ ∀ (x : X) (j l : J), RegAt x (f j / f l) ∨ RegAt x (f l / f j)

def SmallFam (B : HermLB p) {J : Type} (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ β : B.B.ι → X.functionFieldˣ, IsRatSec B.B β ∧
    (∀ (x : X) c, x ∈ B.B.U c → ∀ j, RegAt x (f j * (β c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (B.B.U c) → ∀ j,
      ‖ratVal (f j * (β c : X.functionField)) y‖ * Real.exp (-(B.φ σ).φ c y / 2) ≤ Real.exp (-w j)

def IsFS (M : HermLB p) {J : Type} [Fintype J] (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c, x ∈ M.B.U c → (∀ j, RegAt x (f j * (ρ c : X.functionField))) ∧ ∃ j, UnitAt x (f j * (ρ c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (M.B.U c) →
      (M.φ σ).φ c y = Real.log (∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j))

structure IsModel {Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField) : Prop where

  gen : π (genericPoint Y) = genericPoint X

  deg : π.residueDegree (genericPoint Y) = 1

  compat : ∀ (y : Y) (a : X.presheaf.stalk (π y)),
    φ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a)

def boxFam {K J : Type} [Field K] {D : ℕ} (e : J → K) (x : Fin D → K) : J × Finset (Fin D) → K :=
  fun c => e c.1 * ∏ i ∈ c.2, x i

def shiftA (P : Pair p) (u : ℝ) : Pair p :=
  ⟨P.L, P.A.shift (fun _ => u) fun _ => rfl, P.r, P.r', P.hr, P.hr'⟩

def GenAt (P : Pair p) (c : ℕ) : Prop :=
  ∃ (n : ℕ) (v : Fin n → X.functionField), (∀ i, v i ∈ P.H 0 c) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (v i) ≠ 0

def Regime (P : Pair p) (D : ℕ) : Prop :=
  ∃ α β : ℝ, ∀ t : ℝ, 0 ≤ t →
    Tendsto (fun m : ℕ => P.lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + β * t))

def bound (D q : ℕ) (b g : ℝ) : ℝ :=
  let Δ := Real.log ((q : ℝ) / 2)
  let α := (b + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ)
  let β := (D + 1) * g / (2 * ((D + 1).factorial * Δ))
  Real.log q * (α + β * Real.log ((α + 2 * β + 1) ^ 2))

def AmpleHS : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a : ℝ), IsAmpleLB P.L.B → P.L.SemiPos D → P.L.IsSelfInter a →
      ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
        Tendsto (fun m : ℕ => P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
          (𝓝 ((a + ((D : ℝ) + 1) * t * gdeg P.L D) / ((D + 1).factorial : ℝ)))

def SemiPull : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.SemiPos D → (L.pull π hπ).SemiPos E

theorem shiftA_H (P : Pair p) (u : ℝ) (a b : ℤ) : (shiftA P u).H a b = P.H a b := rfl

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.WigAlg

def cx {E : Type} [Field E] {a : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (τ : E →+* ℂ) (φ : Lie E a → N)
    (i j : Fin a) : N :=
  (1 / 2 : ℂ) • (φ (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • φ (toL (Matrix.single i j (atEmb τ Complex.I))))

end GlobalTheory.WigAlg

end
end

