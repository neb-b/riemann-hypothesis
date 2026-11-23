module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevDatum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Set (Fin S.rank → D.host.E))
    (ΛT : Set (Fin T.rank → D.host.E)) (N : ℕ) (k : Subfield ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (Φ : WO S T → ℂ),
    IsIdemSum e P ∧ (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    (∀ t, Φ t ≠ 0 → t ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e t) ∧
    (∀ u ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e u → ∀ t, Φ (t + N • u) = Φ t) ∧
    (∀ t, Φ t ∈ k) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f

def RayIn (D : D7) (N : ℕ) (k : Subfield ℂ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra D.host.K L) (_ : IsAbelianGalois D.host.K L),
    GlobalTheory.FieldSize.IsRay L (Ideal.span {((N : ℕ) : 𝓞 D.host.K)}) ∧
      ∃ j : L →+* ℂ, j.comp (algebraMap D.host.K L) = D.host.φ₀.comp (algebraMap D.host.K D.host.E) ∧ ∀ x, j x ∈ k

def IsAuxiliarySplitSquarefreeLevel (D : D7) (M pd : ℕ) : Prop :=
  Odd pd ∧ Squarefree pd ∧ (∀ p : ℕ, p.Prime → p ∣ pd → jacobiSym (-(D.host.d : ℤ)) p = 1) ∧ Nat.Coprime pd M ∧
    Nat.Coprime pd (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK)

def IsTwist (pd : ℕ) {k : Type} [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle) : Prop :=
  ChrEq δc δ ∧ (∃ n : ℕ, 0 < n ∧ δ.OrderDvd n) ∧ δ.TrivOn D.host.F ∧ (∀ v, δ.TameAt v) ∧
    (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((pd : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal → δ.UnrAt v) ∧ δ.ValuesIn 0 σ

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Real

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def SmallIn {k : Type} [Field k] (σ : k →+* ℂ) : Prop :=
  (R.C.mu0 i).ValuesIn 0 σ ∧ R.C.eta.ValuesIn (1 / 2) σ

def ratVec (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (k : Subfield ℂ) : Submodule k (R.cV i).W :=
  Submodule.span k {w | ∃ v : VsV D i D.what₂.LL,
    (∀ m, D.what₂.embLL (AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) m) ∈ k) ∧ w = c0 v}

def harmVec (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) (f : WO (Vc D i) (Wc D i) → ℂ) :
    WO (Vc D i) (Wc D i) → ℂ :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f
    (R.ioP i (PiTensorProduct.tprod ℂ u) w)

end Real

section Cover

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ}
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (C : Cover T ((i : ℕ) + 1) σ)

def GoodCover (n : ℕ) : Prop :=
  C.IsUnif ∧ (∀ a, Formalism.L2.Pj.Dom a n → C.IsPinned a n) ∧ IsAuxiliarySplitSquarefreeLevel D T.Q.l.M C.d.pd ∧ SmallIn R i C.σ₂ ∧
    RayIn D (T.Q.l.M * C.d.pd) C.σ₂.fieldRange

def IsRat (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (φ : GA D (Wc D i) → ℂ) : Prop :=
  ∃ φ' ∈ C.ratForms (wtA κ) κ.n, castDict hV φ' = φ

def SeriesRatOn (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ)
    (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (ph : ℂ) : Prop :=
  ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
    IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
    ∀ w ∈ ratVec R i c0 C.σ₂.fieldRange,
      IsRat T i hV C κ (fun g => ph * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)) ∧
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
        (∀ dd : GA D (Wc D i) → ℂ, MuVal (Wc D i) δc dd →
          IsRat T i hV C κ (fun g => dd g * (ph * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)))) ∧
        ∀ om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ),
          IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
            (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om →
          IsRat T i hV C κ (fun g => ph * thetaKO om s g (harmVec R i u w f))

end Cover

def SeriesRat : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → VStd D i →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
        SeriesRatOn T R i hV C (κ i) u (c0L i) ph

theorem auxiliarySplitSquarefreeLevel_one (M : ℕ) : IsAuxiliarySplitSquarefreeLevel D M 1 :=
  ⟨odd_one, squarefree_one, fun _ hp h => absurd (Nat.dvd_one.1 h) hp.ne_one, Nat.coprime_one_left _, Nat.coprime_one_left _⟩

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevelFn {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) (N : ℕ) (Φ : Mx D m n → ℂ) : Prop :=
  (∀ t, Φ t ≠ 0 → t ∈ Λ ∧ IsHalf e t) ∧ ∀ u ∈ Λ, IsHalf e u → ∀ t, Φ (t + N • u) = Φ t

def IntVal {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) (S : Set (HeightOneSpectrum (𝓞 L))) (z : ℂ) : Prop :=
  ∃ a : L, σ a = z ∧ ∀ la ∈ S, la.valuation L a ≤ 1

def OverPrime {L : Type} [Field L] [NumberField L] (l : ℕ) (S : Set (HeightOneSpectrum (𝓞 L))) : Prop :=
  ∀ la ∈ S, ((l : ℕ) : 𝓞 L) ∈ la.asIdeal

def below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    (S : Set (HeightOneSpectrum (𝓞 L))) : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ la ∈ S, p.asIdeal = la.asIdeal.comap (RingOfIntegers.mapRingHom φ)}

def UnramAt {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    (S : Set (HeightOneSpectrum (𝓞 L))) : Prop :=
  ∀ la ∈ S, ¬ (la.asIdeal.comap (RingOfIntegers.mapRingHom φ)).map (RingOfIntegers.mapRingHom φ) ≤ la.asIdeal ^ 2

structure IsTwist {L : Type} [Field L] (σ : L →+* ℂ) (p : ℕ) (xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ) : Prop where
  rat : ∀ (x : (GlobalTheory.FinalJoin.AfE D)ˣ) (a : D.host.E), (x : GlobalTheory.FinalJoin.AfE D) = 1 ⊗ₜ a → GlobalTheory.FinalJoin.NormOne x → xi x = 1
  cond : ∀ x, GlobalTheory.FinalJoin.NormOne x → GlobalTheory.FinalJoin.CongOne p x → xi x = 1
  val : ∀ x, GlobalTheory.FinalJoin.NormOne x → ∃ a : L, σ a = ((xi x : ℂˣ) : ℂ)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Series

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev lattice₂ : AddSubgroup (WO (Vc D i) (Wc D i)) := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True

def IsLevelVec (N : ℕ) (Φ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ (∀ PP ∈ P, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    IsLevelFn (cA D e) (lattice₂ R i) N Φ ∧
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e) (lattice₂ R i) 1 (R.vacP i) Φ f

def series (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (s : GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) (w : (R.cV i).W)
    (g : GA D (Wc D i)) : ℂ :=
  thetaKO (R.ωP i A.μ0) s g
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f
      (R.ioP i (PiTensorProduct.tprod ℂ u) w))

def IsCoefMap (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧
    CoefficientBaseChange R i D.what₂.embLL (RingHom.id ℂ) (c0L i) c0

end Series

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
  (κ : WeightFamilies.Wt D ((i : ℕ) + 1))


omit [Algebra T.Q.c.F D.what₂.LL] in
def IsTowerCover (l : ℕ) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  C.IsUnif ∧ Squarefree C.d.pd ∧ Nat.Coprime C.d.pd l ∧
    Nat.Coprime C.d.pd (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK)


variable {T i} in
def FieldBig (Lat : Submodule ℤ (VsV D i ℂ)) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) C.σ₂ ∧
    (∀ v ∈ Lat, ∀ m, ∃ a, C.σ₂ a = AddMonoidAlgebra.coeff (v : Pol ℂ D.what₂.Tau (Vc D i).rank) m) ∧
    ∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M

def SerIntAt (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ)
    (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ l : ℕ, l.Prime → ∀ s ∈ GfC (Vc D i), ∀ Lat : Submodule ℤ (VsV D i ℂ), Lat.FG →
    ∃ c : ℕ, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, IsTowerCover T i l C → (∀ a, Dom a κ.n → C.IsPinned a κ.n) →
      FieldBig R Lat C → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), OverPrime l S →
        ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, IsTwist C.σ₂ C.d.pd xi →
          ∀ Φ f : WO (Vc D i) (Wc D i) → ℂ, IsLevelVec R i C.d.l₂.M Φ f → (∀ t, IntVal C.σ₂ S (Φ t)) →
            ∀ v ∈ Lat, ∃ φ ∈ C.intForms (wtA κ) κ.n S, ∀ g : GA D (Wc D i),
              castDict hV φ g = (l : ℂ) ^ c *
                (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) * series R i u s f (c0 v) g))


omit [Algebra T.Q.c.F D.what₂.LL] in
def DescIntAt : Prop :=
  ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, IsTowerCover T i l C → C.IsPinned (wtA κ) κ.n →
    ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), OverPrime l S → UnramAt C.inc S →
      ∀ φ ∈ C.intForms (wtA κ) κ.n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → ℂ) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)),
          (∀ a, IntVal C.σ₂ S (x a)) ∧ (∀ a, ψ a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n (below C.inc S)) ∧
            φ = ∑ a, x a • ψ a

def SerInt : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
      (∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
        ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, IsCoefMap R i c0 → SerIntAt T R i (κ i) hV u c0) ∧
      DescIntAt T i (κ i)

end GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries
end
end

