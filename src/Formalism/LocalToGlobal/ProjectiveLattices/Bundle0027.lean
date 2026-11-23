module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Models

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adel_leftInv_of_inv {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hm : MuUnit V dict mu)
    (hP : ∀ g, ∀ γ' ∈ (X (dict g).1).Γ, P (dict g).1 (lact γ' (dict g).2) = P (dict g).1 (dict g).2) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  exact congrArg (mu g * ·) (hP g γ' hγ')

theorem adel_leftInv_of_chi {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g :=
  adel_leftInv_of_inv V dict mu P hd hm fun g γ' hγ' => by
    rw [hΓ _ γ' hγ' _ (hdom g), hχ _ γ' hγ', one_mul]

end Models

section Readings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdInvG (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
    rdU U f k (lact γ x) = rdU U f k x

def SecGen (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ k, ∃ b m, Dom b m ∧
    (∃ f ∈ sec Xo c b m, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0) ∧
    (∃ f ∈ sec Xo c (a + b) (n + m), ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0)

variable (U : Unf Xo c σ r)

theorem rdU_lact (hU : IsUnf U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (k : U.Comp) :
    ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, rdU U f k (lact γ x) = (U.X k).χ (laU U a n k) γ * rdU U f k x :=
  (hU.2.2.2.2.1 a n hdn f hf k).2.2

variable {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
  (Kf : Subgroup (GA D V)) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)

theorem rdU_leftInv (hU : IsUnf U) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu (rdU U f) (γ * g) = adel V dict mu (rdU U f) g :=
  adel_leftInv_of_chi V dict mu (laU U a n) (rdU U f) hd.1 hd.2.2.2.1 hm (rdU_lact U hU hdn hf) hχ

end Readings

namespace Core

variable {D : D7} (T : Core D)

end Core

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parameterOfRecord (D : D7) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) : Par D where
  H := hostOf D (unramBridge D.host.E (cmUnram_conj D))
  l := levelG D (hU := unramBridge D.host.E (cmUnram_conj D))
  c := coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz
  Dw := datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat
  Xo := fun j => Classical.choice (hN D.host.E (hostOf D (unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat j) (levelG D (hU := unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift_pq_pos D (unramBridge D.host.E (cmUnram_conj D)) hDat j))
  eO := eOf D hF

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def kfW (V : HSp D) (N : ℕ) : Subgroup (GA D V) := Subgroup.closure (levSet V N)

def LevGrp (V : HSp D) (N : ℕ) : Prop := ∀ k ∈ kfW V N, k ∈ levSet V N

section One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdIndep1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))

def HolFD1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional ℂ (holSub U.X (laU U a n))

def RdDomInj1 (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, rdU U f ∈ holSub U.X (laU U a n) →
    (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0

def AdelMeas1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), IsHolCusp U.X la P →
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V)

def AeDom1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), P ∈ holSub U.X la →
    onQ V (adel V dict mu P) =ᵐ[muQ1 V] 0 → ∀ k, ∀ x ∈ (U.X k).dom, P k x = 0

end One

abbrev PkgT (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Type 1 :=
  Σ U : Unf (Q.Xo j) Q.c σ D.R.r, (GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) × (GA D (D.sp.W j) → ℂ)

structure PkgOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (U : Unf (Q.Xo j) Q.c σ D.R.r)
    (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (mu : GA D (D.sp.W j) → ℂ) : Prop where

  unf : IsUnf U

  unTest : ∀ k x, FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) (U.un k x)

  chiTriv : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1

  dictU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) dict (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) th hr

  xiAbs : ∀ k (τ : D.host.E →+* ℂ), ‖τ (U.X k).ξ0‖ = xiR D

  muUnit : MuUnit (D.sp.W j) dict mu
  muCont : Continuous mu

  rdIndep : RdIndep1 U
  holFD : HolFD1 U

  rdDomInj : RdDomInj1 U

  adelMeas : AdelMeas1 U (D.sp.W j) dict mu

  aeDom : AeDom1 U (D.sp.W j) dict mu

  latZ : FJ.LatZ U.X (WeightFamilies.rho D j)
  cuNe : FJ.CuNeF U.X (WeightFamilies.rho D j)
  expo : FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

def FamOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)), IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty →
    Nonempty (FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) ty)

def HalfPb (Q : Par D) : Prop :=
  ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧
    Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

structure LawsRest (Q : Par D) : Prop where

  evalWD : ∀ j, InR D j → EvalWD (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z)

  wtField : ∀ j, InR D j → WtField (Q.Xo j) Q.c
  intDiagUnit : ∀ j, InR D j → IntDiagUnit (Q.Xo j) Q.c

  algPtLa : ∀ j, InR D j → AlgPtLa (Q.Xo j) Q.c
  intFrExt : ∀ j, InR D j → IntFrExt (Q.Xo j) Q.c

  m5 : SiegelSpaceAlgebra (E := D.host.E)

  volTie : VolTieG D

  levGrp : ∀ j, InR D j → LevGrp (D.sp.W j) (D.host.g 0 * D.host.g 1)

  half : HalfPb Q

  pkg : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ → ∃ U dict mu, PkgOK Q j σ U dict mu

  dataAll : ∀ j σ, Nonempty (PkgT Q j σ)

section Build

variable {Q : Par D}

theorem pkgEx (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : ∃ p : PkgT Q j σ, InR D j → GoodEmb Q.c σ → PkgOK Q j σ p.1 p.2.1 p.2.2 := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · obtain ⟨U, dict, mu, h⟩ := hRs.pkg j hj σ hσ (hfam j hj σ hσ)
      exact ⟨⟨U, dict, mu⟩, fun _ _ => h⟩
    · exact ⟨Classical.choice (hRs.dataAll j σ), fun _ h => absurd h hσ⟩
  · exact ⟨Classical.choice (hRs.dataAll j σ), fun h => absurd h hj⟩

def pkgOf (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : PkgT Q j σ := (pkgEx hRs hfam j σ).choose

end Build

theorem datHolds (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions

variable {D : D7}

structure LawsPi (T : Core D) (Dd : DepData D.host.E) : Prop where

  page : Dd.Q.g1 = D.host.g 0 ∧ Dd.Q.g2 = D.host.g 1 ∧ Dd.Q.q1 = D.host.q ∧ Dd.Q.dd = D.host.d ∧ Dd.Q.f = D.R.f ∧
    Dd.Q.r = D.R.r
  tPos : TPos Dd

  sm : Dd.Q.sm = D.host.small

  wts : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j

  piSplit : PiSplit (H := T.Q.H) Dd
  piHalf : PiHalf T.Q.l Dd

structure LawsDep (T : Core D) [StarRing (𝓞 D.host.E)] : Prop where

  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a

  chartEx : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c
  chartIndep : ∀ j, InR D j → ChartIndep (T.Q.Xo j) T.Q.c

def NuFinAt (T : Core D) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)] : Prop :=
  ∀ j, InR D j → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nuWAt (Xo := T.Q.Xo j) Dd la j ≠ ⊤

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def CUnit (c : Comp → ℂ) : Prop := ∀ k, ‖c k‖ = 1

def muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) : GA D V → ℂ :=
  fun g => c (dict g).1 * mu g

theorem adel_muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (P : FDSec X) (g : GA D V) :
    adel V dict (muPin V dict mu c) P g = c (dict g).1 * mu g * P (dict g).1 (dict g).2 := rfl

def MuVal (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) : Prop :=
  (∀ g, ∃ x, IsDetRoot V g x) ∧ ∀ g x, IsDetRoot V g x → mu g = ((χ x : Circle) : ℂ)

theorem MuVal.norm {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) (g : GA D V) :
    ‖mu g‖ = 1 := by
  obtain ⟨x, hx⟩ := h.1 g
  rw [h.2 g x hx]
  first
    | exact Circle.norm_coe _
    | exact Circle.abs_coe _
    | exact mem_sphere_zero_iff_norm.mp (χ x).2

def FinUnit (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D

def MuConj {K : Type} [Field K] (σ₀ σ : K →+* ℂ) (χ₀ χσ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x, FinUnit x → ∃ y : K, ((χ₀ x : Circle) : ℂ) = σ₀ y ∧ ((χσ x : Circle) : ℂ) = σ y

def CEquiv (V : HSp D) {K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C] [Module K C]
    {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) : Prop :=
  (∃ c' : Comp → ℂ, CUnit c' ∧ EquivariantFiniteGroup V σ rd dict (muPin V dict mu c') ρ chi ℓ) →
    EquivariantFiniteGroup V σ rd dict (muPin V dict mu c) ρ chi ℓ

end Char

section Dict

variable {D : D7}

def finVec (V : HSp D) (v : Fin V.rank → D.host.E) : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => (1 : Af D.host.F) ⊗ₜ v i

def gLat (V : HSp D) (g : GA D V) : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  (finHom V g).1.mulVec '' (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def latG (V : HSp D) (g : GA D V) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v, finVec V v ∈ gLat V g ∧ w = a • v}

def latGHat (V : HSp D) (g : GA D V) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ z ∈ gLat V g,
    w = fun i => ((1 : Af D.host.F) ⊗ₜ a) * z i}

def LatEmb (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG V 1

def LatIsom (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

def ModelW (V : HSp D) {r : ℕ} (hr : V.rank = r) (X : Data D.host.E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose ∧ X.ξ0 = -D.host.xi0

def IsOrthogonalFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}


open Classical in
def DictLat (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → D.host.E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → D.host.E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1

end Dict

structure CoreJ (D : D7) : Type 1 extends Core D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)

namespace CoreJ

variable {D : D7} (T : CoreJ D)

def phiJ (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) (rdU (T.U j σ) f)

theorem phiJ_apply (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D (T.V j σ)) :
    T.phiJ j σ a f g = T.cE j σ (T.dict j σ g).1 * T.toCore.phiAd j σ a f g := by
  have h1 : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) g =
      T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := rfl
  simp only [phiJ, Core.phiAd, Pi.smul_apply, smul_eq_mul, adel_muPin, h1]
  ring

end CoreJ

def halfVec {D : D7} (V : HSp D) (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * z i

def KfHalf {D : D7} (V : HSp D) (Kf : Subgroup (GA D V)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ b ∈ Mh, ∀ z ∈ latHat V, ∃ y ∈ latHat V,
    (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y

def AdPin {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (ι₀ : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  ∃ (hr : (T.V j σ).rank = D.R.r)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1))
    (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
    (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (T.V j σ) ι ∧ LatIsom (T.V j σ) (T.Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat (T.U j σ) (T.V j σ) hr (T.dict j σ) ι e F ik φ th x₀

structure LawsJ {D : D7} (T : CoreJ D) : Prop extends LawsM T.toCore where

  cUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (T.cE j σ)

  muVal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuVal (T.V j σ) (T.chiW j σ) (T.mu j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuConj T.σ₀ σ (T.chiW j T.σ₀) (T.chiW j σ)

  intAll : ∀ j, InR D j → IntAll (T.Q.Xo j) T.Q.c

  modelW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ hr : (T.V j σ).rank = D.R.r,
    ∀ k, ModelW (T.V j σ) hr ((T.U j σ).X k)

  familyUniformisationBasePointOrthogonal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (T.x₀ j σ)

  kfHalf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    KfHalf (T.V j σ) (T.Kf j σ) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

  adPin : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → AdPin T.toCore j σ (T.x₀ j σ) (T.iota j)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
section
noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Formalism.L2.Pj (Rul)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

variable (Xo c)

theorem intAll_iff : PjFree.IntAll Xo c ↔ Formalism.L2.Pj.IntAll Xo c := Iff.rfl

end Formalism.L2.PjFree
end
end

