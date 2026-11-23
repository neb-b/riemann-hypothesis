module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RationalFormValues
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev lamV (D : D7) (i : Fin D.R.m) : D.what₂.Tau → DomWeight (Vc D i).rank :=
  fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ

def IsCoefExt {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (ι : K →+* K')
    {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) (c' : VV K' lam →ₛₗ[σ'] W) : Prop :=
  ∀ (v : VV K lam) (v' : VV K' lam), (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) → c' v' = c₀ v

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def formFn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : A.fam.amb.FL i t) : Bridge.Gf (Vc D i) → (R.cV i).W :=
  (R.HV i t).e (R.jV i t x)

def ValuesIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {K' : Type} [Field K'] {σ' : K' →+* ℂ}
    (c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W) : Prop :=
  ∀ (x : A.fam.amb.FL i t) (h : Bridge.Gf (Vc D i)), ∃ v : VV K' (lamV D i), c' v = formFn R i t x h

def RationalValuesAt (R : RealDat D A Ks) : Prop :=
  ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (lamV D i) →ₛₗ[D.what₂.embLL] (R.cV i).coef.W),
    Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (lamV D) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (t : T) (K' : Type) [Field K'] (ι : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp ι = D.what₂.embLL →
      ∀ c' : VV K' (lamV D i) →ₛₗ[σ'] (R.cV i).W, IsCoefExt (W := (R.cV i).W) ι (lamV D i) (c0L i) c' → ValuesIn R i t c'

end Row

def RationalValues : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → RationalValuesAt R

end GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SublevelSplitting
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def matF (V : HSp D) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Units.val (h : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))

def compAtPl (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (matF V h).map (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E))


variable (D) in
def IsSplitPl (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 D.host.E), P ≠ P' ∧ P.under (𝓞 D.host.F) = v ∧ P'.under (𝓞 D.host.F) = v

def SuppSplitOff (V : HSp D) (bad : ℕ) (h : Bridge.Gf V) : Prop :=
  ∃ Sp : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v ∈ Sp, IsSplitPl D v ∧ (bad : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, v ∉ Sp → compAtPl V v h = 1

def IsTransl (V : HSp D) (Λ : Lat V) (h : Bridge.Gf V) (L : Lat V) : Prop :=
  ∀ x : Fin V.rank → D.host.E, x ∈ L ↔
    (matF V h⁻¹).mulVec (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))

def IsOpenLev (V : HSp D) (J' : Subgroup (Bridge.Gf V)) : Prop :=
  IsOpen ((J'.comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V))

def IsSubLev (V : HSp D) (J J' : Subgroup (Bridge.Gf V)) (vol : ℝ) : Prop :=
  J' ≤ J ∧ J'.relIndex J ≠ 0 ∧ IsOpenLev V J' ∧ vol = ((J'.relIndex J : ℕ) : ℝ)⁻¹

def IsAdReps (V : HSp D) (Λ : Lat V) (J' : Subgroup (Bridge.Gf V)) (bad : ℕ) {n : ℕ} (h : Fin n → Bridge.Gf V)
    (Lh : Fin n → Lat V) (gam : Fin n → ℕ) : Prop :=
  Bridge.IsReps (Bridge.ratF V) J' h ∧ (∀ a, SuppSplitOff V bad (h a)) ∧ (∀ a, IsTransl V Λ (h a) (Lh a)) ∧
    ∀ a, Finite (Bridge.stab (Bridge.ratF V) J' (h a)) ∧ gam a = Nat.card (Bridge.stab (Bridge.ratF V) J' (h a))

def IsLatReps (V : HSp D) (Λ : Lat V) (bad : ℕ) {n : ℕ} (Lh : Fin n → Lat V) : Prop :=
  (∀ a, Submodule.IsLattice D.host.E (Lh a) ∧ Formalism.L2.Herm.dualL D.sp.cm V (Lh a) = Lh a ∧
    ∃ M : ℕ, 0 < M ∧ M.Coprime bad ∧ (∀ x ∈ Λ, (M : D.host.E) • x ∈ Lh a) ∧ ∀ x ∈ Lh a, (M : D.host.E) • x ∈ Λ) ∧
  ∀ (g : Bridge.Gf V) (L : Lat V), IsTransl V Λ g L →
    ∃ (a : Fin n) (γ : GL (Fin V.rank) D.host.E), γ ∈ UR D.sp.cm V.gram ∧
      ∀ x, x ∈ Lh a ↔ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x ∈ L

variable {T : Type}

def levJ (L : LevCh D T) (i : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J

def IsBad (L : LevCh D T) (t : T) (bad : ℕ) : Prop :=
  0 < bad ∧ ∀ PP : Pl D.host.E, PP ∈ L.Pg ∨ PP ∈ L.Q t → (bad : 𝓞 D.host.E) ∈ PP.asIdeal

def RepsAt (L : LevCh D T) (i : Fin D.R.m) (t : T) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (h : Fin n → Bridge.Gf (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ) (Lh : Fin n → Lat (Vc D i))
    (gam : Fin n → ℕ) (vol : ℝ),
    IsBad L t bad ∧ N ∣ bad ∧ IsSubLev (Vc D i) (levJ L i t) J' vol ∧
      IsAdReps (Vc D i) (L.ΛV i) J' bad h Lh gam ∧ IsLatReps (Vc D i) (L.ΛV i) bad Lh

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowAt (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → RealDat.models_vpos (D := D) →
    ∀ (i : Fin D.R.m) (t : T) (N : ℕ), 0 < N → RepsAt R.toLevCh i t N

end Row

def Row : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), RowAt R

end GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistCoverDesign
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR.Links
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)

variable {D : D7}

abbrev Place (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

abbrev ModHost (D : D7) : Type := ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E

def PrimeToAA (D : D7) (P : Place D) : Prop := FractionalIdeal.count D.host.E P D.host.AA = 0

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro hz
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at hz
  rcases mul_eq_zero.mp hz with h1 | h1
  · rw [FractionalIdeal.coeIdeal_eq_zero] at h1
    unfold Formalism.BasicNotions.Host.ccE at h1
    rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h1
    exact D.host.ccK_ne_bot h1
  · rw [inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero] at h1
    have h2 := D.host.𝔟_spec.2
    rw [h1] at h2
    simp at h2

end GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign
end
end

