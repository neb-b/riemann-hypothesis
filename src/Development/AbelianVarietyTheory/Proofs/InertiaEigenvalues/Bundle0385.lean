module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFreeLatticeEqWachLatticeInvertX
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorRingPsiOperatorExistsOfGood

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedIsCrysDual
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDual

theorem tied_isCrys_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ.dual := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ hρ
  have := LL.2
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  have hf : GlobalTheory.RegularRing.FracInv (P.PD K) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit (P.PD K) := by
    intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← e ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  exact GlobalTheory.RegularRing.dualCrys (P.PD K) ↥LL.1 hf hu V ρ hρ

end GlobalTheory.Per.TiedDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatio
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.InfType

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : Formalism.L2.Host.HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : Formalism.L2.Host.HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  classical
  have hp : ∀ s : Finset (InfinitePlace L),
      (∏ w ∈ s, (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w).comp (atInf w)) k =
        ∏ w ∈ s, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (atInf w k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hws ih => simp [hws, ih, MonoidHom.mul_apply]
  rw [hp, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    starRingEnd ℂ z / ((‖starRingEnd ℂ z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [Complex.norm_conj, inv_div, div_eq_div_iff h1 hz, ← sq, ← Complex.mul_conj', mul_comm]

theorem delAt_inf {D : D7} (C : CharFrame D) (l : ℕ) (k : D.host.Eˣ) : (C.delAt l).inf k = 1 := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, hn, h⟩ := C.isDel'.fin
    exact inf_eq_one hn h k
  · obtain ⟨n, hn, h⟩ := C.isDel.fin
    exact inf_eq_one hn h k

theorem toricLam0_hasInfinityType_conjRatio (D : D7) (Z : LamDat D) (hZ : Z.Ok) (l : ℕ) (j a : Fin D.R.m) (s : ℕ)
    (hs : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1) :
    (∀ g, 1 ≤ Z.kap j a s g) ∧
      GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  have he : ∀ g, ∃ z : ℤ, eExp D j g = z := fun g => (D.hc _).e_int j
  choose e he using he
  have hpos : ∀ g, 1 ≤ e g + Z.c a g - s := fun g => by
    have h := hZ.big j a g
    rw [he] at h
    have h' : (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 < e g + Z.c a g := by exact_mod_cast h
    omega
  have hk : ∀ g, (Z.kap j a s g : ℤ) = e g + Z.c a g - s := fun g => by
    unfold LamDat.kap
    rw [he, Int.floor_intCast]
    exact Int.toNat_of_nonneg (by have := hpos g; omega)
  refine ⟨fun g => by have := hk g; have := hpos g; omega, fun k => ?_⟩
  obtain ⟨n, hn, h1⟩ := (Z.C.isMu0 j).inf
  obtain ⟨n', hn', h2⟩ := (hZ.aux a).inf
  unfold LamDat.lam0
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, delAt_inf, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, h1 k, h2 k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hz : embPsi D.host g (k : D.host.E) ≠ 0 := by simp
  have hu : embPsi D.host g (k : D.host.E) / ((‖embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)
  have e1 : n g = 2 * -(e g) := by
    have := hn g
    simp only [he] at this
    exact_mod_cast this
  have e2 : n' g = 2 * Z.c a g := by
    have := hn' g
    beta_reduce at this
    exact_mod_cast this
  have e3 : phi D.host g (k : D.host.E) = starRingEnd ℂ (embPsi D.host g (k : D.host.E)) := rfl
  rw [e3, conj_div_norm hz, inv_zpow', ← zpow_neg, ← zpow_add₀ hu, e1, e2]
  congr 1
  beta_reduce
  rw [hk]
  ring

end GlobalTheory.LamTie.InfType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem delAt_unitary_triv {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary ∧ (C.delAt l).TrivOn D.host.F := by
  unfold CharFrame.delAt
  split_ifs
  · exact ⟨C.isDel'.unitary, C.isDel'.triv⟩
  · exact ⟨C.isDel.unitary, C.isDel.triv⟩

theorem toricLam0_unitary_trivOnMaxRealSubfield : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m),
    (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  intro D Z h l j a
  have hd := delAt_unitary_triv Z.C l
  exact ⟨((Z.C.isMu0 j).unitary.mul hd.1).mul (h.aux a).unitary.inv,
    ((Z.C.isMu0 j).triv.mul hd.2).mul (h.aux a).triv.inv⟩

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

def tup {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) : Fin m → Matrix (Fin a) (Fin a) (Om l) :=
  fun k => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))

def latL {m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (⋃ k, (fun x => Pi.single k ((l : Om l) ^ M • x)) '' (t k : Set (Matrix (Fin a) (Fin a) (Om l))))

def latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (Set.range (tup ρs)) ⊔ latL t M

def Carries (r : Γ →* GL (Fin a) (Om l)) {d d' m : ℕ} (b : Fin d → Matrix (Fin a) (Fin a) (Om l))
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ)
    (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (P : Matrix (Fin d) (Fin d') ℤ_[l]) (N : ℕ) : Prop :=
  ∀ (z : Fin d' → ℤ_[l]) (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ latL t M →
    ∑ s, zOm l (z s) • bb s = (F.sum fun g c => zOm l c • tup ρs g) + y →
    ∃ w : Fin d → ℤ_[l], ∑ i, zOm l ((P *ᵥ z) i) • b i =
      (F.sum fun g c => zOm l c • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) +
        (l : Om l) ^ N • ∑ i, zOm l (w i) • b i

theorem zOm_smul {α : Type} [AddCommGroup α] [Module (Om l) α] [Module ℤ_[l] α] [IsScalarTower ℤ_[l] (Om l) α]
    (c : ℤ_[l]) (x : α) : zOm l c • x = c • x := by
  rw [← algebraMap_smul (Om l) c x]
  congr 1

theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l))]
  exact (PadicAlgCl.norm_extends l (l : ℚ_[l])).trans Padic.norm_p

theorem norm_zOm_le (c : ℤ_[l]) : ‖zOm l c‖ ≤ 1 := by
  simp only [zOm, RingHom.comp_apply]
  exact (PadicAlgCl.norm_extends l _).trans_le (PadicInt.norm_le_one c)

theorem tup_mem_latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (M : ℕ) (g : Γ) : tup ρs g ∈ latT ρs t M :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨g, rfl⟩)

theorem traceL : ∀ (l : ℕ) [Fact l.Prime] (a d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), ∃ K : ℕ, ∀ w : Fin d → ℤ_[l], ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ (l : ℝ) ^ K := by
  intro l _ a d b
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ i, ‖(b i).trace‖) (show (1 : ℝ) < l by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine ⟨K, fun w => ?_⟩
  rw [Matrix.trace_sum]
  refine (norm_sum_le _ _).trans (le_trans ?_ hK.le)
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_zOm_le _)

end GlobalTheory.TraceConjugationCover

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem stepSub_holds : StepSub := by
  intro D i r ρ hr π hd Xs hπ
  obtain ⟨e, he⟩ := hd
  exact subTw_blocks D i r ρ hr π e he Xs hπ

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitGenExists
section
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem unitGen_exists : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∃ e, Formalism.MainNotions.WachCoordinates.Br.UnitGen ((HW l).W K s LL h) e := by
  intro D HW F l _ K s LL h
  obtain ⟨e, -, -, -, -, hN, -, hφ, hγ, hfree⟩ := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  exact ⟨e, hN, hφ, hγ, hfree⟩

end GlobalTheory.WachUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

section General

def rect {Λ B : Type} [CommRing Λ] [AddCommGroup B] [Module Λ B] {r a : ℕ} (Z : Matrix (Fin r) (Fin a) Λ) (x : Fin a → B) :
    Fin r → B := fun c => ∑ j, Z c j • x j

abbrev what₂ {Λ μ ν : Type} [CommRing Λ] (Z : μ → ν → Λ) : Submodule Λ (ν → Λ) := Submodule.span Λ (Set.range Z)

def Cob {Γ Λ M : Type} [Group Γ] [CommRing Λ] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ Γ M) (f : Γ → M) : Prop :=
  ∃ m, ∀ g, f g = ρ g m - m

variable (Λ : Type) [CommRing Λ] {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [AddCommGroup Y'] [Module Λ Y'] {n : ℕ}

def Bal (β : Y →+ Y' →+ ZMod n) : Prop := ∀ (a : Λ) y y', β (a • y) y' = β y (a • y')

def Perf (β : Y →+ Y' →+ ZMod n) : Prop :=
  Bal Λ β ∧ (∀ y, (∀ y', β y y' = 0) → y = 0) ∧ ∀ y', (∀ y, β y y' = 0) → y' = 0

def vecPair (r : ℕ) (β : Y →+ Y' →+ ZMod n) : (Fin r → Y) →+ (Fin r → Y') →+ ZMod n :=
  ∑ c : Fin r, ((β.comp (Pi.evalAddMonoidHom (fun _ => Y) c)).flip.comp (Pi.evalAddMonoidHom (fun _ => Y') c)).flip

theorem vecPair_apply (r : ℕ) (β : Y →+ Y' →+ ZMod n) (x : Fin r → Y) (y : Fin r → Y') :
    vecPair r β x y = ∑ c, β (x c) (y c) := by
  simp [vecPair]

def CupB {Γ M M' : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [AddCommGroup M'] (χ : Γ → ZMod n)
    (act : Γ → M' → M') (P : M →+ M' →+ ZMod n) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → ZMod n, IsLocallyConstant f ∧ ∀ g h, P (x g) (act g (y h)) = χ g * f h - f (g * h) + f g

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def Kills (A : Type) [CommRing A] [Algebra (X.O0 i) A] : Prop := ∀ x ∈ idl i, algebraMap (X.O0 i) A x = 0

section Coef

variable {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)

def SelC (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] (Q : Finset (PlE D.host))
    (f : GE N → Fin D.R.r → Y) : Prop :=
  ∃ z : Z1 (repOn (Tgl i s) κ Y), z.1 = f ∧ Submodule.Quotient.mk z ∈ selOn bkP i (Tgl i s) κ Y Q

def Univ (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ) (Z : GE N → Matrix (Fin D.R.r) (Fin a) Λ) : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y],
    (∀ x : Fin a → Y, matAct Φ x = 0 → SelC bkP i s κ Y Q fun g => rect (Z g) x) ∧
    (∀ x : Fin a → Y, matAct Φ x = 0 → Cob (repOn (Tgl i s) κ Y) (fun g => rect (Z g) x) → x = 0) ∧
    ∀ f, SelC bkP i s κ Y Q f → ∃ x : Fin a → Y, matAct Φ x = 0 ∧
      Cob (repOn (Tgl i s) κ Y) fun g => f g - rect (Z g) x

variable (ρ : GE N →* GL (Fin D.R.r) (X.O0 i))

section Dual

variable {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y]
  [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1)))
  (Q : Finset (PlE D.host))

def DualSel (y : Z1 (repOn ρ κ⁻¹ Y')) : Prop :=
  (∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 v), y.1 τ = 0) ∧
  (∀ v, v ∈ Spl i ∨ v ∈ Q → ∃ m, ∀ g ∈ DecV N v, y.1 g = repOn ρ κ⁻¹ Y' g m - m) ∧
  ∀ v ∈ placesOver D.host.E (X.l i), ∀ x : Z1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype),
    Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) κ Y v →
    CupB (fun g : DecV N v => ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g.1 : (ZMod (X.l i ^ (nu X i + 1)))ˣ) :
        ZMod (X.l i ^ (nu X i + 1))))
      (fun g m => repOn ρ κ⁻¹ Y' g.1 m) (vecPair D.R.r β) x.1 (fun g => y.1 g.1)

def DualCl : Set (H1 (repOn ρ κ⁻¹ Y')) := {c | ∃ y, DualSel bkP i s κ ρ β Q y ∧ c = Submodule.Quotient.mk y}

end Dual

def OrderFormula (Q : Finset (PlE D.host)) : Prop :=
  ∀ (Y Y' : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] [Finite Y']
    (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Perf Λ β →
    Finite (DualCl bkP i s κ ρ β Q) ∧ Nat.card (selOn bkP i (Tgl i s) κ Y Q) =
      Nat.card (DualCl bkP i s κ ρ β Q) * ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype))

def NoInvDual : Prop := ∀ (Y' : Type) [AddCommGroup Y'] [Module Λ Y'] (m : Fin D.R.r → Y'),
  (∀ g, repOn ρ κ⁻¹ Y' g m = m) → m = 0

def LocCountFin : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y],
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ Y v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype))) *
        Nat.card Y ^ (D.R.f * D.R.r)


omit [Algebra (X.O0 i) Λ] in
def IsChar {M : ℕ} {ι : Type} [Fintype ι] (ξ : ι → Λ) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ g, ((κ g : Λˣ) : Λ) * ∏ q, (1 + ξ q) ^ (Multiplicative.toAdd (d q g)).val = 1

def bform (x y : GE N → Fin D.R.r → Λ) (h : GE N) : Λ := x h ⬝ᵥ y h - x (cConj X h) ⬝ᵥ y (cConj X h)

end Coef

def NewPl (M : ℕ) (L : Subgroup (GE N)) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N) : Prop :=
  (∀ v, Over p v → v ∉ X.S0 i) ∧ IsSplitPl D.host p ∧ normV p % (2 * X.l i ^ M) = 1 ∧ DecV N p ≤ L ∧
    IsOpen (d.ker : Set (GE N)) ∧ IsFrob (N.plOm.1 p) (normV p) σ ∧ γ ∈ Ine (F := D.host.E) (N.plOm.1 p) ∧
    d γ = Multiplicative.ofAdd 1


variable (X) in
def two (g : GE N) : Bool → GE N := fun b => if b then cConj X g else g

end GlobalTheory.NewPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleMapFrobeniusGaloisEquivariantStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_etale_map_frobenius_galois_equivariant : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; IoLaws E := by
  first | exact @GlobalTheory.NL.ioLaws | exact GlobalTheory.NL.ioLaws | (intros; apply GlobalTheory.NL.ioLaws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleModuleFrobeniusBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachEtaleModule_frobenius_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  first | exact @GlobalTheory.EtaleFrob.phi_basis | exact GlobalTheory.EtaleFrob.phi_basis | (intros; apply GlobalTheory.EtaleFrob.phi_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFreeLatticeEqWachLatticeInvertXStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFreeLattice_eq_wachLattice_invert_X : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ N₁ : Submodule (AA K LL) (W.DD T), FreeA W T N₁ → IsBaseChange W.EE N₁.subtype → (∀ x ∈ N₁, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ N₁) → (∀ y ∈ N₁, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T N₁) → ∃ a : ℕ, (∀ x ∈ N₁, W.X ^ a • x ∈ W.N T) ∧ ∀ x ∈ W.N T, W.X ^ a • x ∈ N₁ := by
  first | exact @GlobalTheory.NL.InvX.main | exact GlobalTheory.NL.InvX.main | (intros; apply GlobalTheory.NL.InvX.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFrobeniusFlatCrystallineStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFrobenius_flat_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ z : Fin l → W.DD T, (∀ j, z j ∈ W.N T) → ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) • W.φD T (z j) = 0 → ∀ j, z j = 0 :=
  @GlobalTheory.NL.PhiFlat.main
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorRingPsiOperatorExistsOfGoodStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ ψ : W.EE →ₗ[↥(OL LL)] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧ (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧ ∀ j < l, ∀ a, ψ (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ j * W.φE a) = if j = 0 then a else 0 := by
  first | exact @GlobalTheory.psiE_exists | exact GlobalTheory.psiE_exists | (intros; apply GlobalTheory.psiE_exists <;> assumption)
end

