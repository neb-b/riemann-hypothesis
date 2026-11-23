module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ChiGrid
open GlobalTheory.SqTop (twPl Qn)
open GlobalTheory.Square (IsAwayUnit)
open GlobalTheory.RowTest (LocIn NumbersIn)

namespace GlobalTheory.KappaArith

theorem isAwayUnit_of_pow_eq_one {K : Type} [Field K] (m : ℕ) {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsAwayUnit m z := by
  have hint : IsIntegral ℤ z :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hz]⟩
  let a : 𝓞 K := ⟨z, hint⟩
  have ha : (a : K) = z := rfl
  refine ⟨a, 0, 0, ⟨a ^ (n - 1), ?_⟩, by simp [ha]⟩
  rw [pow_zero]
  apply RingOfIntegers.ext
  have e1 : ((a * a ^ (n - 1) : 𝓞 K) : K) = z * z ^ (n - 1) := by rw [← ha]; norm_cast
  rw [e1, ← pow_succ', Nat.sub_add_cancel hn, hz]
  rfl

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)

def AwayIm (D : D7) (m : ℕ) (z : ℂ) : Prop := ∃ ζ : D.what₂.LL, IsAwayUnit m ζ ∧ D.what₂.embLL ζ = z

theorem awayIm_one (m : ℕ) : AwayIm D m 1 := ⟨1, IsAwayUnit.one m, map_one _⟩

theorem AwayIm.mul {m : ℕ} {z z' : ℂ} (h : AwayIm D m z) (h' : AwayIm D m z') : AwayIm D m (z * z') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

theorem AwayIm.prod {m : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, AwayIm D m (f i)) :
    AwayIm D m (∏ i ∈ s, f i) :=
  Finset.prod_induction f (AwayIm D m) (fun _ _ => AwayIm.mul) (awayIm_one m) h

theorem awayIm_val {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (x : (w.adicCompletion D.host.E)ˣ) :
    AwayIm D m ((Lc.xiH t).loc w x : ℂ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨ζ, hζ⟩ := hx w x
  have h1 : ((Lc.xiH t).loc w x) ^ n = 1 := by
    have : ((Lc.xiH t) ^ n).loc w x = 1 := by rw [show (Lc.xiH t) ^ n = 1 from ho]; rfl
    exact this
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.KappaArith

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomIPData

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def alphaB (L : LevCh D T) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle := L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)

def betaB (G : GridData L sc) (i j : Fin D.R.m) : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)


open Classical in
def sfB (G : GridData L sc) (t : T) : Finset (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D) :=
  (locPl G t).image fun w => w.under (𝓞 D.host.F)

theorem isBottomTri_is {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) :
    X.Is W.ψ W.θ (alphaB L i j) (fun _ => betaB G i j) (fun t => SqNum.nuH G t i j) (locPl G) := h.is

theorem gbig_mono {Q Q' : GP} (h : GBig Q) (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ), Q G μ₀ C x b → Q' G μ₀ C x b) : GBig Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  exact ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => H _ _ _ _ _ (h C hC D large₂ he hx hR T Lc μ₀ hL G)⟩

theorem gbig_and {Q Q' : GP} (h : GBig Q) (h' : GBig Q') : GBig fun G μ₀ C x b => Q G μ₀ C x b ∧ Q' G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C0', x₀', h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C0', max x₀ x₀', fun C hC D large₂ he hx hR T Lc μ₀ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G,
      h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G⟩⟩

end GlobalTheory.BottomIPData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelsExt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ModC (R : RealDat D A Ks) : Prop :=
  R.models_HX ∧ R.models_HV ∧ R.models_jX ∧ R.models_jV ∧ R.models_νY ∧ R.models_νY' ∧ R.models_νX ∧ R.models_νV

def KerC (R : RealDat D A Ks) : Prop :=
  R.chain_ωY ∧ R.chain_ωX ∧ R.chain_vY ∧ R.chain_vX ∧ R.thP_ωP ∧ R.thP_vP

variable {R : RealDat D A Ks} {V : NewLev D N} {X : NewFam A N}

def FamC (Y : NewReal R V X) : Prop :=
  (extR R Y).grp_red_R ∧ (extR R Y).grp_red_L ∧ TieExt R Y ∧ (extR R Y).fam_roots ∧ RealDat.fam_degR (A := extA A X) ∧
    RealDat.fam_degL (A := extA A X) ∧ (extR R Y).fam_muVal


set_option maxHeartbeats 2000000 in
def updM (Y : NewReal R V X) (HX : type_of% Y.HX) (HV : type_of% Y.HV)
    (jX : ∀ n, (extA A X).fam.amb.FR (.inr n) →ₛₗ[D.what₂.embLL] (HX n).H)
    (jV : ∀ i n, (extA A X).fam.amb.FL i (.inr n) →ₛₗ[D.what₂.embLL] (HV i n).H)
    (νY : type_of% Y.νY) (fdY : type_of% Y.fdY) (νX : type_of% Y.νX) (fdX : type_of% Y.fdX) (νV : type_of% Y.νV)
    (fdV : type_of% Y.fdV) : NewReal R V X :=
  { Y with
    HX := HX, HV := HV, jX := jX, jV := jV, νY := νY, fdY := fdY, νX := νX, fdX := fdX, νV := νV, fdV := fdV,
    ioX := fun _ => 0, Th := fun _ => 0, thF := fun _ _ => 0, thG := fun _ _ => 0 }


set_option maxHeartbeats 2000000 in
def updK (Y : NewReal R V X) (ωY : type_of% Y.ωY) (ωX : type_of% Y.ωX) (ωP : type_of% Y.ωP) (vY : type_of% Y.vY)
    (vX : type_of% Y.vX) (vP : type_of% Y.vP) : NewReal R V X :=
  { Y with ωY := ωY, ωX := ωX, ωP := ωP, vY := vY, vX := vX, vP := vP }


set_option maxHeartbeats 2000000 in
def updL (Y : NewReal R V X) (ioY : type_of% (extR R Y).ioY) (ioX : type_of% (extR R Y).ioX) (Th : type_of% (extR R Y).Th)
    (thF : type_of% (extR R Y).thF) (thG : type_of% (extR R Y).thG) : NewReal R V X :=
  { Y with
    ioY := fun n => ioY (.inr n), ioX := fun n => ioX (.inr n), Th := fun n => Th (.inr n),
    thF := fun i n => thF i (.inr n), thG := fun i n => thG i (.inr n) }

set_option maxHeartbeats 2000000 in
theorem isModels_ext (hM : R.IsModels) (Y : NewReal R V X) (h : ModC (extR R Y)) : (extR R Y).IsModels := by
  refine ⟨?_, hM.vpos, ?_, ?_, ?_, h.1, h.2.1, ?_, ?_, ?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hM.inf :))
  · exact (by with_unfolding_all exact (hM.cX :))
  · exact (by with_unfolding_all exact (hM.cV :))
  · exact (by with_unfolding_all exact (hM.prX :))
  · exact (by with_unfolding_all exact (hM.HE :))
  · exact (by with_unfolding_all exact (hM.HW :))
  · exact (by with_unfolding_all exact (hM.gE :))
  · exact (by with_unfolding_all exact (hM.gW :))
  · exact (by with_unfolding_all exact (hM.ν0 :))
  · exact (by with_unfolding_all exact (hM.νW :))
  · exact (by with_unfolding_all exact (hM.BV :))
  · exact (by with_unfolding_all exact (hM.order :))

set_option maxHeartbeats 2000000 in
theorem isFam_ext (hF : R.IsFam) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsFam := by
  refine ⟨?_, ?_, h.2.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, ?_⟩
  · obtain ⟨g, c, c', ht⟩ := hF.tie
    have h1 := h.2.2.1 g c c' ht
    refine ⟨g, ?_, ?_, ?_⟩
    · exact (by with_unfolding_all exact (c :))
    · exact (by with_unfolding_all exact (c' :))
    · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (hF.Sb :))
  · exact (by with_unfolding_all exact (hF.pl_onto :))
  · exact (by with_unfolding_all exact (hF.etaVal :))

set_option maxHeartbeats 2000000 in
theorem isGrp_ext {F : Face D A} (hG : R.IsGrp F) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsGrp (extF F X) := by
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hG.levels :))
  · exact (by with_unfolding_all exact (hG.record :))
  · exact (by with_unfolding_all exact (hG.chiW :))


set_option maxHeartbeats 2000000 in
theorem models_stage (hM : R.IsModels) (Y : NewReal R V X) (h : FamC Y) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') := by
  choose HX jX h1 h2 using fun n => exists_modX (extR R Y) (.inr n)
  choose HV jV h3 h4 using fun i n => exists_modV (extR R Y) i (.inr n)
  choose νY fdY h5 h6 using fun n j => exists_measY (extR R Y) (.inr n) j
  choose νX fdX h7 using fun n => exists_measX (extR R Y) (.inr n)
  choose νV fdV h8 using fun i n => exists_measV (extR R Y) hM.vpos i (.inr n)
  refine ⟨updM Y HX HV jX jV νY fdY νX fdX νV fdV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.HX t :))
    · exact (by with_unfolding_all exact (h1 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.HV i t :))
    · exact (by with_unfolding_all exact (h3 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.jX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.jV i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY t :))
    · exact (by with_unfolding_all exact (h5 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY' t :))
    · exact (by with_unfolding_all exact (h6 n _ rfl :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νX t :))
    · exact (by with_unfolding_all exact (h7 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.νV i t :))
    · exact (by with_unfolding_all exact (h8 i n :))


set_option maxHeartbeats 2000000 in
theorem ker_stage (hc : R.IsChain) (hp : R.IsThP) (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y)
    (hm : ModC (extR R Y)) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') ∧ KerC (extR R Y') := by
  have hψ : IsStdChar D (extR R Y).ψ (-1) := (hc.ωX A.μ0).std
  choose ωY vY h1 using fun n k => exists_kerY (R := extR R Y) hL hψ (.inr n) k ((by with_unfolding_all exact (fun hk => (hc.vY A.μ0 k hk).1 :)))
  choose ωX vX h2 h3 using fun n => exists_kerX (R := extR R Y) hL hψ (.inr n) ((by with_unfolding_all exact ((hc.vX A.μ0).1 :)))
  choose ωP vP h4 h5 using fun i n => exists_kerP (R := extR R Y) hL hψ i (.inr n) ((by with_unfolding_all exact ((hp.vP i A.μ0).1 :)))
  refine ⟨updK Y ωY ωX ωP vY vX vP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h :))
  · exact (by with_unfolding_all exact (hm :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).1 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).2 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vX t :))
    · exact (by with_unfolding_all exact (h3 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.ωP i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.vP i t :))
    · exact (by with_unfolding_all exact (h5 i n :))

set_option maxHeartbeats 2000000 in
theorem isChain_updL (hc : R.IsChain) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with ioY := ioY, ioX := ioX, Th := Th } : RealDat D (extA A X) Ks).IsChain) :
    (extR R (updL Y ioY ioX Th thF thG)).IsChain := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.ωY :))
  · exact (by with_unfolding_all exact (h.ωX :))
  · exact (by with_unfolding_all exact (h.vY :))
  · exact (by with_unfolding_all exact (h.vX :))
  · exact (by with_unfolding_all exact (h.ptY :))
  · exact (by with_unfolding_all exact (h.ptX :))
  · exact (by with_unfolding_all exact (h.ItY :))
  · exact (by with_unfolding_all exact (h.ItX :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioY t :))
    · exact (by with_unfolding_all exact (h.ioY (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioX t :))
    · exact (by with_unfolding_all exact (h.ioX (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.Th t :))
    · exact (by with_unfolding_all exact (h.Th (.inr n) :))

set_option maxHeartbeats 2000000 in
theorem isThP_updL (hp : R.IsThP) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with thF := thF, thG := thG } : RealDat D (extA A X) Ks).IsThP) :
    (extR R (updL Y ioY ioX Th thF thG)).IsThP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.ωP :))
  · exact (by with_unfolding_all exact (h.vP :))
  · exact (by with_unfolding_all exact (h.pt_theta :))
  · exact (by with_unfolding_all exact (h.ioP :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF_mem i t :))
    · exact (by with_unfolding_all exact (h.thF_mem i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF i t :))
    · exact (by with_unfolding_all exact (h.thF i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thG i t :))
    · exact (by with_unfolding_all exact (h.thG i (.inr n) :))


set_option maxHeartbeats 2000000 in
theorem core_ext (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y) :
    ∃ Y' : NewReal R V X, GlobalTheory.Hk3.Core (extR R Y') (extF F X) ∧ TieExt R Y' := by
  obtain ⟨Y1, f1, m1⟩ := models_stage hC.models Y h
  obtain ⟨Y2, f2, m2, k2⟩ := ker_stage hC.chain hC.thP hL Y1 f1 m1
  have hF := isFam_ext hC.fam Y2 f2
  have hM := isModels_ext hC.models Y2 m2
  have e1 := GlobalTheory.ConjExt.exists_chain (R := extR R Y2) h₁ h₂ h₃ h₄ hP hL (isGrp_ext hC.grp Y2 f2).record hF hM k2.1 k2.2.1 k2.2.2.1
    k2.2.2.2.1 (.inl A.μ0) ((by with_unfolding_all exact (hC.chain.ItY A.μ0 :))) ((by with_unfolding_all exact (hC.chain.ItX A.μ0 :)))
  have e2 := GlobalTheory.ConjExt.exists_thP (R := extR R Y2) h₃ hL hF hM k2.2.2.2.2.1 k2.2.2.2.2.2 (.inl A.μ0)
    ((by with_unfolding_all exact (fun i => hC.thP.ioP i A.μ0 :)))
  obtain ⟨ioY, ioX, Th, c3⟩ := e1
  obtain ⟨thF, thG, p3⟩ := e2
  have f3 : FamC (updL Y2 ioY ioX Th thF thG) := (by with_unfolding_all exact (f2 :))
  have m3 : ModC (extR R (updL Y2 ioY ioX Th thF thG)) := (by with_unfolding_all exact (m2 :))
  exact ⟨updL Y2 ioY ioX Th thF thG, ⟨hL, isGrp_ext hC.grp _ f3, isFam_ext hC.fam _ f3, isModels_ext hC.models _ m3,
    isChain_updL hC.chain Y2 _ _ _ _ _ c3, isThP_updL hC.thP Y2 _ _ _ _ _ p3⟩, f3.2.2.1⟩

end GlobalTheory.TupExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedClosedFibreProperCompleteLocalNoet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedFibreConn


open Classical in
theorem idem_eq_of_basicOpen {X : Scheme.{0}} {e e' : Γ(X, ⊤)} (he : e * e = e) (he' : e' * e' = e')
    (h : (X.basicOpen e : Set X) = X.basicOpen e') : e = e' := by
  have key : ∀ (a : Γ(X, ⊤)) (x : X) (hx : x ∈ (⊤ : X.Opens)), a * a = a →
      (X.presheaf.germ ⊤ x hx).hom a = if x ∈ X.basicOpen a then 1 else 0 := by
    intro a x hx ha
    have hg : (X.presheaf.germ ⊤ x hx).hom a * (X.presheaf.germ ⊤ x hx).hom a = (X.presheaf.germ ⊤ x hx).hom a := by
      rw [← map_mul, ha]
    split_ifs with hxa
    · have hu := (X.mem_basicOpen a x hx).1 hxa
      exact hu.mul_left_cancel (hg.trans (_root_.mul_one _).symm)
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((X.presheaf.germ ⊤ x hx).hom a) with h1 | h1
      · exact absurd ((X.mem_basicOpen a x hx).2 h1) hxa
      · have h0 : (X.presheaf.germ ⊤ x hx).hom a * (1 - (X.presheaf.germ ⊤ x hx).hom a) = 0 := by
          rw [mul_sub, _root_.mul_one, hg, sub_self]
        exact h1.mul_left_eq_zero.1 h0
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' fun x hx => ?_
  change (X.presheaf.germ ⊤ x hx).hom e = (X.presheaf.germ ⊤ x hx).hom e'
  rw [key e x hx he, key e' x hx he']
  have : (x ∈ X.basicOpen e) ↔ (x ∈ X.basicOpen e') := by
    change x ∈ (X.basicOpen e : Set X) ↔ x ∈ (X.basicOpen e' : Set X); rw [h]
  simp only [this]

theorem eq_zero_of_germ_closedFibre {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : X ⟶ Sp A)
    (hf : IsClosedMap f) (t : Γ(X, ⊤))
    (h : ∀ x, f x = closedPoint A → (X.presheaf.germ ⊤ x trivial).hom t = 0) : t = 0 := by
  let Z : Set X := {y | (X.presheaf.germ ⊤ y trivial).hom t = 0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨W, hW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq X.presheaf y (show y ∈ (⊤ : X.Opens) from trivial) (show y ∈ (⊤ : X.Opens) from trivial) t 0
      (hy.trans (map_zero _).symm)
    refine ⟨W, fun y' hy' => ?_, W.isOpen, hW⟩
    have e₁ := TopCat.Presheaf.germ_res_apply X.presheaf iU y' hy' t
    have e₂ := TopCat.Presheaf.germ_res_apply X.presheaf iV y' hy' 0
    exact e₁.symm.trans ((congrArg _ e').trans (e₂.trans (map_zero _)))
  have hall : ∀ y, y ∈ Z := by
    by_contra hne
    obtain ⟨y, hy⟩ := not_forall.1 hne
    have hc : IsClosed (f '' Zᶜ) := hf _ hZ.isClosed_compl
    obtain ⟨y', hy', e⟩ := (IsLocalRing.specializes_closedPoint (R := A) (f y)).mem_closed hc ⟨y, hy, rfl⟩
    exact hy' (h y' e)
  exact TopCat.Presheaf.section_ext X.sheaf ⊤ t 0 fun y hy => (hall y).trans (map_zero _).symm

theorem thick_apply_eq (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ)
    (z : Spec (CommRingCat.of (A ⧸ maximalIdeal A ^ (e + 1)))) : thick A (maximalIdeal A) e z = closedPoint A := by
  apply PrimeSpectrum.ext
  show Ideal.comap _ _ = maximalIdeal A
  have := z.isPrime
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ z.asIdeal).ne_top) fun x hx => ?_
  show (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom x ∈ z.asIdeal
  refine z.2.mem_of_pow_mem (e + 1) ?_
  rw [← map_pow, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx _)]
  exact z.asIdeal.zero_mem

theorem isPreconnected_closedFibre : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A], IsAdicComplete (maximalIdeal A) A → ∀ (X : Scheme.{0}) (f : X ⟶ Sp A), IsProper f → PreconnectedSpace X → _root_.IsPreconnected {x : X | f x = closedPoint A} := by
  intro A _ _ _ hA X f hf hX
  haveI := hf
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_clopen]
  intro C hC
  let Y : Over (Sp A) := Over.mk f
  have hfst : ∀ e (y : (thickObj A (maximalIdeal A) e Y).left),
      f (pullback.fst Y.hom (thick A (maximalIdeal A) e) y) = closedPoint A := by
    intro e y
    rw [← Scheme.Hom.comp_apply]
    change (pullback.fst Y.hom (thick A (maximalIdeal A) e) ≫ Y.hom) y = _
    rw [pullback.condition, Scheme.Hom.comp_apply]
    exact thick_apply_eq A e _
  let D : ∀ e, Set (thickObj A (maximalIdeal A) e Y).left := fun e =>
    {y | (⟨pullback.fst Y.hom (thick A (maximalIdeal A) e) y, hfst e y⟩ : {x : X | f x = closedPoint A}) ∈ C}
  have hD : ∀ e, IsClopen (D e) := fun e =>
    hC.preimage ((pullback.fst Y.hom (thick A (maximalIdeal A) e)).continuous.subtype_mk (fun y => hfst e y))
  choose g hg hgD using fun e => GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen _ (D e) (hD e)
  have hcomp : ∀ e, thickMap A (maximalIdeal A) e Y ≫ pullback.fst Y.hom (thick A (maximalIdeal A) (e + 1)) =
      pullback.fst Y.hom (thick A (maximalIdeal A) e) := fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hcompat : ∀ e, (thickMap A (maximalIdeal A) e Y).appTop.hom (g (e + 1)) = g e := by
    intro e
    refine idem_eq_of_basicOpen (by rw [← map_mul, hg]) (hg e) ?_
    rw [← Scheme.preimage_basicOpen_top, hgD e]
    ext y
    change thickMap A (maximalIdeal A) e Y y ∈ ((thickObj A (maximalIdeal A) (e + 1) Y).left.basicOpen (g (e + 1)) : Set _) ↔ y ∈ D e
    rw [hgD (e + 1)]
    simp only [D, Set.mem_setOf_eq, ← Scheme.Hom.comp_apply, hcomp]
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.FormalFunctions.exists_of_thick A (maximalIdeal A) hA Y hf g hcompat
  haveI : IsProper Y.hom := hf
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have ht : s * s - s = 0 := by
    refine eq_zero_of_germ_closedFibre f f.isClosedMap _ fun x hx => ?_
    refine GlobalTheory.FormalValue.germ_eq_zero_of_thickenings (maximalIdeal A) Y ⊤ (s * s - s) (fun e => ?_) x trivial ?_
    · change (pullback.fst Y.hom (thick A (maximalIdeal A) e)).appTop.hom (s * s - s) = 0
      rw [map_sub, map_mul, hs e, hg e, sub_self]
    · change maximalIdeal A ≤ (f x).asIdeal
      rw [hx]; exact le_rfl
  have hs2 : s * s = s := sub_eq_zero.1 ht
  have hB : IsClopen (X.basicOpen s : Set X) :=
    ⟨GlobalTheory.PairingLocus.isClosed_basicOpen (X := X) hs2, (X.basicOpen s).isOpen⟩
  have hne : (maximalIdeal A ^ (0 + 1)) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal A).ne_top
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨z₀⟩ : Nonempty (PrimeSpectrum (A ⧸ maximalIdeal A ^ (0 + 1))) := inferInstance
  have hC' : C = {c | c.1 ∈ (X.basicOpen s : Set X)} := by
    ext c
    obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.hom) (g := thick A (maximalIdeal A) 0)
      c.1 z₀ (c.2.trans (thick_apply_eq A 0 z₀).symm)
    have e1 : c ∈ C ↔ y ∈ D 0 := by
      change c ∈ C ↔ (⟨_, hfst 0 y⟩ : {x : X | f x = closedPoint A}) ∈ C
      rw [show (⟨_, hfst 0 y⟩ : {x : X | f x = closedPoint A}) = c from Subtype.ext hy]
    rw [e1, ← hgD 0, ← hs 0, ← Scheme.preimage_basicOpen_top]
    change pullback.fst Y.hom (thick A (maximalIdeal A) 0) y ∈ X.basicOpen s ↔ _
    rw [hy]; rfl
  rcases isClopen_iff.1 hB with h | h
  · left; rw [hC', h]; rfl
  · right; rw [hC', h]; rfl

end GlobalTheory.ClosedFibreConn
end

