module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

variable {l : ℕ} [Fact l.Prime]

theorem FilD_anti {a b : ℤ} (h : a ≤ b) : Per.FilD l b ≤ Per.FilD l a := by
  obtain ⟨k, rfl⟩ := Int.le.dest h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans ?_ ih
    have := (GlobalTheory.MemLoc.filD_laws l).1 (a + k)
    simpa [add_assoc] using this

theorem alg_mem_FilD_iff (n : ℕ) (y : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n :=
  (GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 n y

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem tmul_mem_filO {C : GlobalTheory.MemLoc.Core l} {n : ℤ} {β : Per.Bcris l} (h : C.ι β ∈ Per.FilD l n) :
    (1 : O) ⊗ₜ[ℤ_[l]] β ∈ filO O C n :=
  Submodule.subset_span ⟨β, h, rfl⟩

theorem filO_anti {C : GlobalTheory.MemLoc.Core l} {a b : ℤ} (h : a ≤ b) : filO O C b ≤ filO O C a :=
  Submodule.span_mono fun _ ⟨β, hβ, hx⟩ => ⟨β, FilD_anti h hβ, hx⟩

theorem mul_mem_filO {C : GlobalTheory.MemLoc.Core l} {a b : ℤ} {x y : OB l O} (hx : x ∈ filO O C a)
    (hy : y ∈ filO O C b) : x * y ∈ filO O C (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨β', hβ', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      refine tmul_mem_filO ?_
      rw [map_mul]
      exact (GlobalTheory.MemLoc.filD_laws l).2.2.1 a b _ _ hβ hβ'
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul o y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | smul o x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o h

theorem toOB_tmul_mem_filO {C : GlobalTheory.MemLoc.Core l} {n : ℕ} {c : Per.Acris l} (h : C.j c ∈ Per.FilP l n) :
    toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] c) ∈ filO O C n := by
  refine tmul_mem_filO ?_
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) c) ∈ _
  rw [C.ι_j]
  exact (alg_mem_FilD_iff n _).2 h

theorem toOB_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) : toOB l O x ∈ filO O C 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul o c =>
    have : (o ⊗ₜ[ℤ_[l]] c : OCr l O) = o • ((1 : O) ⊗ₜ[ℤ_[l]] c) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ o (toOB_tmul_mem_filO (n := 0) (GlobalTheory.BdRQuot.mem_filtration_zero _))
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem isUnit_l_BdRp : IsUnit (l : Per.BdRp l) := by
  refine (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ ?_
  rw [map_natCast]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem mem_filO_of_pow_mul {C : GlobalTheory.MemLoc.Core l} {n : ℤ} {s : ℕ} {x : OB l O}
    (h : (l : OB l O) ^ s * x ∈ filO O C n) : x ∈ filO O C n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.MemLoc.isUnit_l_Bcris l).exists_right_inv
  have hι : C.ι u ∈ Per.FilD l 0 := by
    obtain ⟨v, hv⟩ := (isUnit_l_BdRp (l := l)).exists_right_inv
    have h1 : C.ι u = algebraMap (Per.BdRp l) (Per.BdR l) v := by
      have h2 : C.ι (l : Per.Bcris l) * C.ι u = 1 := by rw [← map_mul, hu, map_one]
      have h3 : (algebraMap (Per.BdRp l) (Per.BdR l) (l : Per.BdRp l)) * algebraMap _ _ v = 1 := by
        rw [← map_mul, hv, map_one]
      rw [map_natCast] at h2
      rw [map_natCast] at h3
      calc C.ι u = (algebraMap (Per.BdRp l) (Per.BdR l) v * (l : Per.BdR l)) * C.ι u := by
            rw [mul_comm (algebraMap _ _ v), h3, one_mul]
        _ = _ := by rw [mul_assoc, h2, mul_one]
    rw [h1]
    exact (mem_FilD_zero_iff _).2 ⟨v, rfl⟩
  have hU : ((1 : O) ⊗ₜ[ℤ_[l]] u) ^ s ∈ filO O C 0 := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    refine tmul_mem_filO ?_
    rw [map_pow]
    have hk : ∀ k : ℕ, C.ι u ^ k ∈ Per.FilD l 0 := fun k => by
      induction k with
      | zero => rw [pow_zero]; exact (GlobalTheory.MemLoc.filD_laws l).2.1
      | succ k ih => rw [pow_succ]; simpa using (GlobalTheory.MemLoc.filD_laws l).2.2.1 0 0 _ _ ih hι
    exact hk s
  have h1 : ((1 : O) ⊗ₜ[ℤ_[l]] u) ^ s * ((l : OB l O) ^ s * x) = x := by
    have h2 : ((1 : O) ⊗ₜ[ℤ_[l]] u) * (l : OB l O) = 1 := by
      rw [show (l : OB l O) = (1 : O) ⊗ₜ[ℤ_[l]] (l : Per.Bcris l) from
        (map_natCast (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) l).symm,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, hu]
      rfl
    rw [← mul_assoc, ← mul_pow, h2, one_pow, one_mul]
  rw [← h1]
  simpa using mul_mem_filO hU h

theorem j_mem_FilP_of_approx (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : Per.Acris l)
    (h : ∀ r : ℕ, ∃ y z : Per.Acris l, x = y + (l : Per.Acris l) ^ r * z ∧ C.j y ∈ Per.FilP l m) :
    C.j x ∈ Per.FilP l m := by
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  obtain ⟨a, ha⟩ := hN x
  have hq : Ideal.Quotient.mk (Per.kerP l ^ m) (algebraMap (Per.Ainf l) (Per.AinfP l) a) = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    obtain ⟨b, hb⟩ := hN z
    refine ⟨b, ?_⟩
    have hy' : Per.ev l m (C.j y) = 0 := (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hy
    rw [← ha, ← hb, hxyz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, hy']
    ring
  have h1 : Per.ev l m (C.j x) = 0 := by
    rw [← ha, map_mul, map_pow, map_natCast] at hq
    exact ((GlobalTheory.MemLoc.CrisMap.unit_l l m).pow N).mul_right_eq_zero.1 hq
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).2 h1

end GlobalTheory.BKGal.TaylorFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientToDivisibleQuotientMemCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevelCocycle

theorem ioL_actQ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (g : G)
    (x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    GlobalTheory.BKFinLevel.ioL L ϖ r (actQ L _ hI g x) = actD L g (GlobalTheory.BKFinLevel.ioL L ϖ r x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    simp only [actQ, Submodule.mapQ_apply, GlobalTheory.BKFinLevel.ioL_mk, actD, actT]
    congr 1
    simp only [LinearMap.coe_restrictScalars, map_smul]
    rfl

theorem ioL_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ r hI c hc
  refine ⟨hc.1.comp _, fun g h => ?_⟩
  simp only [hc.2 g h, map_add (f := _), ioL_actQ]

end GlobalTheory.BKFinLevelCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.RedLocConst

theorem mem_span_smul_top' {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem redT_mem_Z1Q : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI a
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL (ϖ ^ r) with hcdef
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (pow_ne_zero _ hϖ.ne_zero)
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hc).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = ϖ ^ r • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = ϖ ^ r • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) a) g) =
      Submodule.Quotient.mk (evT LA g a) := fun g => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g0
    refine ⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)),
      hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩
    · show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)
      rw [sub_self]; exact ⟨0, LA.T.zero_mem, smul_zero c⟩
    · intro g hg
      rw [hval, hval, Submodule.Quotient.eq, hmem]
      exact hg
  · intro g h
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

end GlobalTheory.RedLocConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.CoefDescent

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {E E' : Type} [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
    {O O' : Type} [CommRing O] [Algebra O E] [CommRing O'] [Algebra O' E']

theorem blochKatoCocycle_comp_equivariant_map
    {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
    [Module O V] [IsScalarTower O E V] {ρ : Representation E G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul E V]
    {V' : Type} [AddCommGroup V'] [Module E' V'] [Module Qp V'] [IsScalarTower Qp E' V']
    [Module O' V'] [IsScalarTower O' E' V'] {ρ' : Representation E' G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul E' V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O') ρ') (φ : V →ₗ[Qp] V')
    (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (hc : Continuous φ) (hT : ∀ x ∈ L.T, φ x ∈ L'.T)
    (c : G → V) (h : c ∈ latticeFiniteCocycles PD L) : (fun g => φ (c g)) ∈ latticeFiniteCocycles PD L' := by
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, -, x, hx⟩ := h
  have hz : (fun g => φ (c g)) ∈ continuousCocycles ρ' := by
    refine ⟨hc.comp hc1, fun g h => ?_⟩
    change φ (c (g * h)) = φ (c g) + ρ' g (φ (c h))
    rw [hc2, map_add (f := _), he]
  refine ⟨⟨hz, fun g _ => hT _ (hc3 g (Set.mem_univ g))⟩, hz, LinearMap.rTensor B φ x, fun g => ?_⟩
  have key : ∀ y : V ⊗[Qp] B, LinearMap.rTensor B φ (actVB PD ρ g y) =
      actVB PD ρ' g (LinearMap.rTensor B φ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← key, ← map_sub, ← hx, LinearMap.rTensor_tmul]

theorem liftF_of_retract
    {V₁ : Type} [AddCommGroup V₁] [Module E V₁] [Module Qp V₁] [IsScalarTower Qp E V₁]
    [Module O V₁] [IsScalarTower O E V₁] {ρ₁ : Representation E G V₁}
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul E V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module E V₂] [Module Qp V₂] [IsScalarTower Qp E V₂]
    [Module O V₂] [IsScalarTower O E V₂] {ρ₂ : Representation E G V₂}
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul E V₂]
    {W₁ : Type} [AddCommGroup W₁] [Module E' W₁] [Module Qp W₁] [IsScalarTower Qp E' W₁]
    [Module O' W₁] [IsScalarTower O' E' W₁] {σ₁ : Representation E' G W₁}
    [TopologicalSpace W₁] [ContinuousAdd W₁] [ContinuousConstSMul E' W₁]
    {W₂ : Type} [AddCommGroup W₂] [Module E' W₂] [Module Qp W₂] [IsScalarTower Qp E' W₂]
    [Module O' W₂] [IsScalarTower O' E' W₂] {σ₂ : Representation E' G W₂}
    [TopologicalSpace W₂] [ContinuousAdd W₂] [ContinuousConstSMul E' W₂]
    {L₁ : Lattice (O := O) ρ₁} {L₂ : Lattice (O := O) ρ₂}
    {M₁ : Lattice (O := O') σ₁} {M₂ : Lattice (O := O') σ₂}
    (F : LatHom L₁ L₂) (F' : LatHom M₁ M₂)
    (ι : V₂ →ₗ[Qp] W₂) (R₁ : W₁ →ₗ[Qp] V₁) (R₂ : W₂ →ₗ[Qp] V₂)
    (ιe : ∀ g x, ι (ρ₂ g x) = σ₂ g (ι x)) (ιc : Continuous ι) (ιT : ∀ x ∈ L₂.T, ι x ∈ M₂.T)
    (R₁e : ∀ g x, R₁ (σ₁ g x) = ρ₁ g (R₁ x)) (R₁c : Continuous R₁) (R₁T : ∀ x ∈ M₁.T, R₁ x ∈ L₁.T)
    (R₂e : ∀ g x, R₂ (σ₂ g x) = ρ₂ g (R₂ x)) (R₂T : ∀ x ∈ M₂.T, R₂ x ∈ L₂.T)
    (hret : ∀ x, R₂ (ι x) = x) (hF : ∀ x, R₂ (F'.f x) = F.f (R₁ x))
    (e : ℕ) (h : F'.LiftF PD e) : F.LiftF PD e := by
  intro c hc
  have h1 := h _ (blochKatoCocycle_comp_equivariant_map PD L₂ M₂ ι ιe ιc ιT c hc)
  obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨y, hy, rfl⟩, hsum⟩ := Submodule.mem_sup.1 h1
  refine Submodule.mem_sup.2 ⟨_, ⟨_, blochKatoCocycle_comp_equivariant_map PD M₁ L₁ R₁ R₁e R₁c R₁T d hd, rfl⟩, _,
    ⟨R₂ y, R₂T y hy, rfl⟩, ?_⟩
  funext g
  have h2 := congrArg R₂ (congrFun hsum g)
  change R₂ (F'.f (d g) + (σ₂ g y - y)) = R₂ (((PD.p : O') ^ e) • ι (c g)) at h2
  change F.f (R₁ (d g)) + (ρ₂ g (R₂ y) - R₂ y) = ((PD.p : O) ^ e) • c g
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, hret, map_add (f := _), map_sub, hF, R₂e] at h2
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, h2]

end General

section Maps
variable {Qp E E' : Type} [Field Qp] [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
  {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module Qp V'] [IsScalarTower Qp E V']
  {k k' : ℕ}

def emb (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) : V →ₗ[Qp] (Fin k → E') :=
  LinearMap.pi fun i => j.toLinearMap ∘ₗ (b.coord i).restrictScalars Qp

theorem emb_apply (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (v : V) (i : Fin k) :
    emb j b v i = j (b.repr v i) := rfl

def ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) : (Fin k → E') →ₗ[Qp] V :=
  (b.equivFun.symm.toLinearMap.restrictScalars Qp) ∘ₗ LinearMap.compLeft r (Fin k)

theorem ret_apply (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') :
    ret r b w = ∑ i, r (w i) • b i := by
  simp [ret, Module.Basis.equivFun_symm_apply]

theorem repr_ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') (i : Fin k) :
    b.repr (ret r b w) i = r (w i) := by
  rw [ret_apply]; simp [Finsupp.single_apply]

theorem ret_emb (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x) (h1 : r 1 = 1)
    (b : Module.Basis (Fin k) E V) (v : V) : ret r b (emb j b v) = v := by
  refine b.ext_elem fun i => ?_
  have := hr (b.repr v i) 1
  rw [mul_one, h1, mul_one] at this
  rw [repr_ret, emb_apply, this]

theorem emb_map (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (v : V) :
    emb j b' (f v) = ((LinearMap.toMatrix b b' f).map j).mulVec (emb j b v) := by
  funext i
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f v) i
  rw [emb_apply, ← this]
  simp [Matrix.mulVec, dotProduct, emb_apply]

theorem ret_map (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x)
    (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (w : Fin k → E') :
    ret r b' (((LinearMap.toMatrix b b' f).map j).mulVec w) = f (ret r b w) := by
  refine b'.ext_elem fun i => ?_
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f (ret r b w)) i
  rw [repr_ret, ← this]
  simp [Matrix.mulVec, dotProduct, repr_ret, hr]

end Maps


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem liftF_descends : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {K₀ K B BdR : Type} [Field K₀] [Field K] [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B] [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR] (PD : PeriodData G ℚ_[l] K₀ K B BdR) (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1), (∀ a x, r (incl hL a * x) = a * r x) → r 1 = 1 → (∀ x ∈ OL LL', r x ∈ OL LL) → Continuous r → ∀ e : ℕ, (extHom hL hb₁ hb₂ F).LiftF PD e → F.LiftF PD e := by
  intro l _ G _ _ K₀ K B BdR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PD LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr h1
    hint hrc e h
  have hincl : Continuous (incl hL) := continuous_subtype_val.subtype_mk _
  have retT : ∀ {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ} {b : Module.Basis (Fin k) ↥LL.1 T.V},
      IsLatBasis T b → ∀ x ∈ intVec LL' k, ret r b x ∈ T.L.T := by
    intro T k b hb x hx
    rw [ret_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := T.L.T.smul_mem (⟨r (x i), hint _ (hx i)⟩ : ↥(OL LL)) (hb.1 i)
    rwa [← algebraMap_smul ↥LL.1] at this
  refine liftF_of_retract PD F (extHom hL hb₁ hb₂ F) (emb (incl hL) b₂) (ret r b₁) (ret r b₂)
    (fun g x => emb_map (incl hL) b₂ b₂ (T₂.ρ g) x) ?_ ?_
    (fun g x => ret_map (incl hL) r hr b₁ b₁ (T₁.ρ g) x) ?_ (retT hb₁)
    (fun g x => ret_map (incl hL) r hr b₂ b₂ (T₂.ρ g) x) (retT hb₂)
    (ret_emb (incl hL) r hr h1 b₂) (fun x => ret_map (incl hL) r hr b₁ b₂ F.f x) e h
  · exact continuous_pi fun i => hincl.comp (IsModuleTopology.continuous_of_linearMap (b₂.coord i))
  · intro x hx i
    exact incl_integral hL (hb₂.2 x hx i)
  · have hc : Continuous (b₁.equivFun.symm.toLinearMap) := IsModuleTopology.continuous_of_linearMap _
    exact hc.comp (continuous_pi fun i => hrc.comp (continuous_apply i))

end GlobalTheory.CoefDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfMutualSpanOfIndep
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem linIndep_of_mutual_span_of_indep :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)),
      (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W),
        (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) →
        (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) →
        (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) →
        ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro R W _ _ act hmul hone ι _ _ b f hb hf hbf d hd
  letI : Module R W :=
    { smul := fun r w => act r w
      one_smul := hone
      mul_smul := fun r s w => hmul r s w
      smul_zero := fun r => map_zero (act r)
      smul_add := fun r x y => map_add (act r) x y
      add_smul := fun r s w => by
        show act (r + s) w = act r w + act s w
        rw [map_add (f := _), AddMonoidHom.add_apply]
      zero_smul := fun w => by
        show act 0 w = 0
        rw [map_zero, AddMonoidHom.zero_apply] }
  have hs : ∀ (r : R) (w : W), act r w = r • w := fun _ _ => rfl
  simp only [hs] at hb hf hbf hd
  choose P hP using hf
  choose Q hQ using hbf
  have expand : ∀ c : ι → R,
      ∑ i, c i • f i = ∑ k, (Matrix.vecMul c (Matrix.of P)) k • b k := by
    intro c
    simp only [hP, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Matrix.of_apply,
      Finset.sum_smul]
    rw [Finset.sum_comm]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext k k'
    have h0 : ∑ k'', ((Matrix.vecMul (Q k) (Matrix.of P)) k'' - (1 : Matrix ι ι R) k k'') • b k''
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← expand, ← hQ, Matrix.one_apply,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    have := hb _ h0 k'
    rw [sub_eq_zero] at this
    rw [← this, Matrix.mul_apply]
    simp [Matrix.vecMul, dotProduct]
  have hPQ : Matrix.of P * Matrix.of Q = 1 := mul_eq_one_comm.mp hQP
  have he : Matrix.vecMul d (Matrix.of P) = 0 := by
    rw [expand] at hd
    funext k
    exact hb _ hd k
  have : d = 0 := by
    rw [← Matrix.vecMul_one d, ← hPQ, ← Matrix.vecMul_vecMul, he, Matrix.zero_vecMul]
  intro i
  rw [this]
  rfl

end GlobalTheory
end

