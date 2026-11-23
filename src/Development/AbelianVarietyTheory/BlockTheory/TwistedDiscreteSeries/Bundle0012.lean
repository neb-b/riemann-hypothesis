module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.LocalRingCardinality.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PositiveRowsTuple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def dimQ (b : Bool) : ℕ := (lv (F.fc (R.toCx F).zs) b).dQ A.μ0

theorem dimQ_eq (b : Bool) :
    dimQ R F b = Module.finrank D.what₂.LL ((A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0)) := by
  cases b <;> rfl

theorem pos_iff (b : Bool) : (lv (F.fc (R.toCx F).zs) b).Pos ↔ 0 < dimQ R F b := Iff.rfl

theorem pos_iff_ne_bot (b : Bool) :
    (lv (F.fc (R.toCx F).zs) b).Pos ↔ (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ := by
  rw [pos_iff, dimQ_eq, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

end

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

section Abstract

variable {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E]

def HasRationalTest (σ : K →+* ℂ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ e ∈ S, ∀ a, ∃ z : K, σ z = ψ a e

end Abstract

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

end Interface

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowTestModel (R : RealDat D A Ks) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (R.HE.H →ₗ[ℂ] ℂ)), (∀ e : R.HE.H, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : T) (x : A.fam.amb.FR t) (a : Fin n), ∃ z : D.what₂.LL, D.what₂.embLL z = ψ a (R.Th t (R.jX t x))

def twFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E →ₗ[ℂ] ℂ) : Tw s E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.out x))
  map_add' x y := by rw [Tw.out_add, map_add (f := _), map_add (f := _)]
  map_smul' z x := by rw [Tw.out_smul, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

def untwFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Tw s E →ₗ[ℂ] ℂ) : E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.mkL s E x))
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' z x := by rw [map_smulₛₗ, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

theorem test_tw_iff {K E : Type} [Field K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {σ σ' : K →+* ℂ}
    (h : ∀ a, σ' a = cj s (σ a)) {ι : Type} {X : ι → Type} (v : ∀ t, X t → E) :
    (∃ (n : ℕ) (ψ : Fin n → (Tw s E →ₗ[ℂ] ℂ)), (∀ e : Tw s E, (∀ a, ψ a e = 0) → e = 0) ∧
      ∀ t x a, ∃ z : K, σ' z = ψ a (Tw.mk s (v t x))) ↔
    (∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ t x a, ∃ z : K, σ z = ψ a (v t x)) := by
  constructor
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => untwFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    refine ⟨z, ?_⟩
    have := congrArg (cj s) ((h z).symm.trans hz)
    rw [cj_cj] at this
    exact this
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => twFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    exact ⟨z, (h z).trans (congrArg (cj s) hz)⟩

end Concrete

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


theorem gap {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) {n : ℕ} (hn : n < Rk.r) :
    ((Rk.t : ℚ) + 3) / 2 ≤ |Formalism.L2.NTheta.lamAt h n + h.e j| := by
  have hk := Rk.m_add_three_le_k
  have hj := j.2
  have mono : ∀ a d : ℕ, a + d < Rk.r → Formalism.L2.NTheta.lamAt h (a + d) ≤ Formalism.L2.NTheta.lamAt h a := by
    intro a d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (a + d) hd).le.trans (ih (by omega))
  have val : ∀ (c : ℕ) (hc : c < Rk.m), Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
    intro c hc
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    simp
  unfold Ranks.r at hn mono
  by_cases hle : n ≤ Rk.k - 1 + j
  · have h1 := mono n (Rk.k - 1 + j - n) (by omega)
    rw [show n + (Rk.k - 1 + j - n) = Rk.k - 1 + j by omega, val j hj] at h1
    have h2 := h.gap_be j
    exact le_trans (by simp only [Fin.eta] at h1; linarith) (le_abs_self _)
  · have hj1 : (j : ℕ) + 1 < Rk.m := by omega
    have h1 := mono (Rk.k - 1 + (j + 1)) (n - (Rk.k - 1 + (j + 1))) (by omega)
    rw [show Rk.k - 1 + (j + 1) + (n - (Rk.k - 1 + (j + 1))) = n by omega, val _ hj1] at h1
    have h2 := h.gap_eb j hj1
    exact le_trans (by linarith) (neg_le_abs _)

theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push_neg at hc
    apply h
    have hle : v.asIdeal ≤ (P.under (𝓞 D.host.F)).asIdeal := by
      intro x hx
      obtain ⟨y, hy, hyP⟩ := hc x hx
      have : y = algebraMap _ _ x := RingOfIntegers.ext hy
      subst this
      exact hyP
    have := v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top hle
    rwa [show P.under (𝓞 D.host.F) = v from HeightOneSpectrum.ext this.symm]

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaMultiplicity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernelP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (Φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g Φ

def IsThetaMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, y x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP : LinearMap.range (R.extV i t) →ₗ[ℂ] (LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ)),
      Lift.IsThetaP (R.νV i t) (R.fdV i t) (kernelP R i t) (R.ptP i t) (R.ioP i) (LinearMap.range (R.extV i t)) thP ∧
      ∀ (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
          thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

end

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeOK (D : D7) : Prop := 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def transl (R : RealDat D A Ks) (i : Fin D.R.m) (g : G) :
    MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g))

def thetaTranslates (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (MMap (R.MW i (sg0 D A))) :=
  {y | ∃ (g : G) (x : (R.HV i t).H), y = transl R i g (R.thF i t x)}

def SpanAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  Submodule.span ℂ (thetaTranslates R i t) = R.Wall i (sg0 D A)

def goodModel (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def GoodRangeAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  LinearMap.range (R.thG i t) = goodModel R i

theorem range_eq_comap_iff {X H M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H] [AddCommGroup M]
    [Module ℂ M] (e : H →ₗ[ℂ] M) (f : X →ₗ[ℂ] H) (p : X →ₗ[ℂ] M) (U : Submodule ℂ M) (hinj : Function.Injective e)
    (hle : U ≤ LinearMap.range e) (hc : ∀ x, e (f x) = p x) :
    LinearMap.range f = U.comap e ↔ LinearMap.range p = U := by
  have hcomp : e ∘ₗ f = p := LinearMap.ext hc
  rw [← hcomp, LinearMap.range_comp]
  constructor
  · intro h
    rw [h, Submodule.map_comap_eq_self hle]
  · intro h
    rw [← h, Submodule.comap_map_eq_of_injective hinj]


set_option maxHeartbeats 1000000 in
theorem goodRangeAt_iff {R : RealDat D A Ks} (hW : R.models_HW) (hG : R.thP_thG) (i : Fin D.R.m) (t : T) :
    GoodRangeAt R i t ↔
      LinearMap.range (postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) ∘ₗ R.thF i t) = R.Wat i (sg0 D A) R.triv :=
  range_eq_comap_iff (R.HW i (sg0 D A)).e (R.thG i t) _ (R.Wat i (sg0 D A) R.triv) (hW i (sg0 D A)).1
    (le_of_le_of_eq inf_le_left (hW i (sg0 D A)).2.1.symm) (fun x => hG i t x)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)

def LiftsTo (κ : (levEnv V β L).Q) (g₀ : G0 L.Pg L.r) : Prop :=
  rTup β L (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf V) : GL _ _)) = g₀

def IsTranslate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (g₀ : G0 L.Pg L.r) (F F' : Bridge.Gf V → W) : Prop :=
  (∃ κ, LiftsTo V β L κ g₀) ∧
    ∀ κ, LiftsTo V β L κ g₀ → ∀ h, F' h = ((((levEnv V β L).ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : Bridge.Gf V))

def IsTransRep {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r)
    (M : HMod (Bridge.Gf V → W)) (ρ : Representation ℂ G M.H) : Prop :=
  ∀ g x, IsTranslate V β L (eG g) (M.e x) (M.e (ρ g x))

variable {V β L}

end Space

def Commutes {G E E' : Type} [Group G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (f : E →ₗ[ℂ] E') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


end GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilSignShift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NcGapGt (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h < |((x.1 - y.1 : ℚ) : ℝ)|

def NcGapGe (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |((x.1 - y.1 : ℚ) : ℝ)|

def minSig (S : SPar) : ℕ :=
  min (S.filter fun x => x.2 = true).card (S.filter fun x => x.2 = false).card

def shiftPar (c : ℚ) (S : SPar) : SPar := S.image fun x => (x.1 + c, x.2)

variable (D : D7)

def alV (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i - 1 / 2 else -(D.hc τ).e i

def alW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i else -(D.hc τ).e i - 1 / 2

def lamS (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alW D i τ) (parA (Ptw D) i τ)

def lamT (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alV D i τ) (parA (Ptw D) ((i : ℕ) + 1) τ)

def StepGap (i : Fin D.R.m) : Prop :=
  ∀ τ, NcGapGt (lamS D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGt (lamT D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGe (lamS D i τ) (120 * (D.R.rankY i : ℝ) * (minSig (lamS D i τ) : ℝ) ^ ((3 : ℝ) / 2))

variable {D}

def StepWeil (ψ : AddChar (AF D.host.F) ℂ) (i : Fin D.R.m) (V W : HSp D)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop :=
  ∃ χV χW : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χV χW ω ∧
    ∀ τ, HasInfExp D χV τ (alV D i τ) ∧ HasInfExp D χW τ (alW D i τ)

def VacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f

def fockOf {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f

end GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

end
end

