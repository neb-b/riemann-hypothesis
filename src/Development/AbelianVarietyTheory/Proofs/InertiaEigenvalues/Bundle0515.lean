module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0473
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerReductionH1Eq
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.ReductionH1Kernel

section Gen
variable {G : Type} [Group G] [TopologicalSpace G]
    {LL : Type} [Field LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V}

theorem smul_H1Q_eq_zero (L : Lattice (O := O) ρ) (b : O)
    (hI : StableSub L (Ideal.span {b} • ⊤ : Submodule O ↥L.T)) (z : QuotientCohomology L _ hI) : b • z = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H w =>
    have hw : b • w = 0 := by
      apply Subtype.ext
      funext g
      show b • w.1 g = 0
      obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (w.1 g)
      rw [← ht, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, hw, Submodule.Quotient.mk_zero]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem cob_mem_Z1T (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) :
    (fun g => ρ g x - x) ∈ latticeCocycles L := by
  refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩
  · simp_rw [sub_eq_add_neg]
    exact (hρ x).add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel

theorem ker_red_gen (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (b : O)
    (hb : algebraMap O LL b ≠ 0) (hI : StableSub L (Ideal.span {b} • ⊤ : Submodule O ↥L.T))
    (hZ : ∀ d : ↥(latticeCocycles L), redT L _ d ∈ quotientCocycles L _ hI) :
    ∃ f : LatticeCohomology L →ₗ[O] QuotientCohomology L _ hI, LinearMap.ker f = (Ideal.span {b} • ⊤ : Submodule O (LatticeCohomology L)) ∧
      ∀ d : ↥(latticeCocycles L), ∃ h : redT L _ d ∈ quotientCocycles L _ hI,
        f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT L _ d, h⟩ := by
  let g0 : ↥(latticeCocycles L) →ₗ[O] ↥(quotientCocycles L _ hI) := (redT L _).codRestrict _ hZ
  have hB : (latticeCoboundaries L).comap (latticeCocycles L).subtype ≤
      ((BQ L _ hI).comap (quotientCocycles L _ hI).subtype).comap g0 := by
    intro d hd
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hd
    obtain ⟨x, hx, hxd⟩ := hd
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply]
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    funext g
    show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) - Submodule.Quotient.mk ⟨x, hx⟩ =
      Submodule.Quotient.mk (evT L g d)
    rw [show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) =
      Submodule.Quotient.mk (actT L g ⟨x, hx⟩) from rfl, ← Submodule.Quotient.mk_sub]
    congr 1
    apply Subtype.ext
    show ρ g x - x = (d : _ → V) g
    rw [← hxd]; rfl
  let f : LatticeCohomology L →ₗ[O] QuotientCohomology L _ hI := Submodule.mapQ _ _ g0 hB
  refine ⟨f, ?_, fun d => ⟨hZ d, rfl⟩⟩
  have hkill := smul_H1Q_eq_zero L b hI
  apply le_antisymm
  · intro z hz
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective ((latticeCoboundaries L).comap (latticeCocycles L).subtype) z
    rw [LinearMap.mem_ker] at hz
    change Submodule.Quotient.mk (g0 d) = (0 : QuotientCohomology L _ hI) at hz
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at hz
    obtain ⟨y, hy⟩ := hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {b} • ⊤ : Submodule O ↥L.T) y
    have hg : ∀ g, ∃ t : ↥L.T, evT L g d - (actT L g x - x) = b • t := by
      intro g
      have h1 := congrFun hy g
      change actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x =
        Submodule.Quotient.mk (evT L g d) at h1
      rw [show actQ L _ hI g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (actT L g x) from rfl,
        ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h1
      rw [← GlobalTheory.RedLocConst.mem_span_smul_top', ← neg_sub]
      exact neg_mem h1
    choose t ht using hg
    let cx : ↥(latticeCocycles L) := ⟨_, cob_mem_Z1T L hρ x⟩
    have h2 : ∀ g, (d : _ → V) g - (ρ g x - x) = algebraMap O LL b • ((t g : ↥L.T) : V) := by
      intro g
      rw [algebraMap_smul]
      exact congrArg Subtype.val (ht g)
    have hd'Z : (fun g => ((t g : ↥L.T) : V)) ∈ latticeCocycles L := by
      have hfun : (fun g => ((t g : ↥L.T) : V)) =
          (algebraMap O LL b)⁻¹ • ((d : _ → V) - (cx : _ → V)) := by
        funext g
        show _ = (algebraMap O LL b)⁻¹ • ((d : _ → V) g - (ρ g x - x))
        rw [h2, inv_smul_smul₀ hb]
      refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_pi.2 fun g _ => (t g).2⟩
      rw [hfun]
      exact (continuousCocycles ρ).smul_mem _ ((continuousCocycles ρ).sub_mem (Submodule.mem_inf.1 d.2).1 (Submodule.mem_inf.1 cx.2).1)
    have hdec : d = b • (⟨_, hd'Z⟩ : ↥(latticeCocycles L)) + cx := by
      apply Subtype.ext
      funext g
      show (d : _ → V) g = b • ((t g : ↥L.T) : V) + (ρ g x - x)
      rw [← algebraMap_smul LL b, ← h2, sub_add_cancel]
    have hcx : (Submodule.Quotient.mk cx : LatticeCohomology L) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, x.2, rfl⟩
    rw [hdec, Submodule.Quotient.mk_add, hcx, add_zero, Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top
  · rw [Submodule.smul_le]
    intro a ha z _
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [LinearMap.mem_ker, map_smul, mul_smul, hkill, smul_zero]

end Gen

theorem redT_mem_Z1Q_of_ne (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ)
    (b : O) (hb : algebraMap O LL b ≠ 0)
    (hI : StableSub LA (Ideal.span {b} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)) :
    redT LA _ a ∈ quotientCocycles LA _ hI := by
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL b with hcdef
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hb).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = b • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [GlobalTheory.RedLocConst.mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = b • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) a) g) =
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
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

theorem ker_reduction_H1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), ∃ f : LatticeCohomology LA →ₗ[O] QuotientCohomology LA _ hI, LinearMap.ker f = (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA)) ∧ ∀ d : ↥(latticeCocycles LA), ∃ h : redT LA _ d ∈ quotientCocycles LA _ hI, f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT LA _ d, h⟩ := by
  intro l _ P K LL _ _ _ O _ _ hO A LA r hI
  have hb : algebraMap O LL (((l : ℕ) : O) ^ r) ≠ 0 := by
    rw [map_pow, map_natCast]
    refine pow_ne_zero _ ?_
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact ker_red_gen LA A.cont _ hb hI (redT_mem_Z1Q_of_ne l K LL O hO A LA _ hb hI)

end GlobalTheory.ReductionH1Kernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerTowerGaloisPreservesBreuilKisinModule
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.GKinfStable
variable {l : ℕ} [hl : Fact l.Prime]

theorem map_field_le (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l)
    {x : Om l} (hx : x ∈ (ϖ.field a).1) : g x ∈ (ϖ.field a).1 := by
  have hd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have := ϖ.isGalois_field a hd
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g) ⟨x, hx, rfl⟩

theorem conj_mem (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∀ h ∈ GK (ϖ.field a), g⁻¹ * h * g ∈ GK (ϖ.field a) := by
  intro h hh
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh (g x) (map_field_le a e ϖ he g hx)
  simp only [AlgEquiv.mul_apply, h1]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem res_exists (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (he : e + 1 = l ^ a) (g : GQ l) :
    ∃ σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a)),
      ∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l) := by
  let F := (ϖ.field a).1
  let φ : ↥F →ₐ[ℚ_[l]] ↥F :=
    { toFun := fun y => ⟨g y, map_field_le a e ϖ he g y.2⟩
      map_one' := Subtype.ext (map_one g : g (1 : Om l) = 1)
      map_mul' := fun y z => Subtype.ext (map_mul g (y : Om l) (z : Om l))
      map_zero' := Subtype.ext (map_zero g : g (0 : Om l) = 0)
      map_add' := fun y z => Subtype.ext (map_add g (y : Om l) (z : Om l))
      commutes' := fun q => Subtype.ext (g.commutes q) }
  refine ⟨{ toFun := fun x => ⟨φ x, x.2.map (φ.restrictScalars ℤ_[l])⟩
            map_one' := Subtype.ext (map_one φ : φ (1 : ↥F) = 1)
            map_mul' := fun y z => Subtype.ext (map_mul φ (y : ↥F) (z : ↥F))
            map_zero' := Subtype.ext (map_zero φ : φ (0 : ↥F) = 0)
            map_add' := fun y z => Subtype.ext (map_add φ (y : ↥F) (z : ↥F)) }, fun x => rfl⟩

theorem kappa_act {LL : FinExt l} (T : QLat LL) (g : Gl l) (z : letI := zlLat T; WCb l ⊗[ℤ_[l]] ↥T.L.T) :
    letI := zlLat T
    TWact (galOW (↥(OL LL)) (sQ l g)) T g (kappa T z) =
      kappa T (TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) z) := by
  letI := zlLat T
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actZ_mul_apply {LL : FinExt l} (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T g (actZ T h x) = actZ T (g * h) x :=
  Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g h) (x : T.V)).symm

theorem actZ_one_apply {LL : FinExt l} (T : QLat LL) (x : ↥T.L.T) :
    letI := zlLat T
    actZ T 1 x = x :=
  Subtype.ext (LinearMap.congr_fun (map_one T.ρ) (x : T.V))

end GlobalTheory.GKinfStable


open GlobalTheory.GKinfStable in
theorem GlobalTheory.GKinfStable.main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  intro BS l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK g γ hcov v hv
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := ↥LL.1)
  choose σ hσ using res_exists (l := l) a e ϖ he (sQ l g)
  choose ψ hψ using _root_.GlobalTheory.BKGal.covers_ringEndo a e ϖ LL (sQ l g) γ hcov
  choose H hH using _root_.GlobalTheory.BKGal.PrismTwist.hom_restrict a e ϖ (sQ l g) σ hσ ψ hψ
  letI := zlLat T
  obtain ⟨E, j, hR, hiff⟩ := hBK
  let ρg : ↥T.L.T ≃ₗ[ℤ_[l]] ↥T.L.T :=
    LinearEquiv.ofLinear (actZ T g) (actZ T g⁻¹)
      (LinearMap.ext fun x => (actZ_mul_apply T g g⁻¹ x).trans
        ((congrArg (fun k => actZ T k x) (mul_inv_cancel g)).trans (actZ_one_apply T x)))
      (LinearMap.ext fun x => (actZ_mul_apply T g⁻¹ g x).trans
        ((congrArg (fun k => actZ T k x) (inv_mul_cancel g)).trans (actZ_one_apply T x)))
  have hPR := _root_.GlobalTheory.Prism.PullGal.realises_pullback (ϖ.field a) E ↥T.L.T _ j hR (sQ l g) σ hσ
    (conj_mem (l := l) a e ϖ he (sQ l g)) ρg (fun h h' hh x => by
      have e2 : g * inclG (ϖ.field a) h' = inclG (ϖ.field a) h * g := by
        rw [show inclG (ϖ.field a) h' = g⁻¹ * inclG (ϖ.field a) h * g from Subtype.ext hh]
        group
      exact (actZ_mul_apply T g _ x).trans ((congrArg (fun k => actZ T k x) e2).trans
        (actZ_mul_apply T _ g x).symm))
  choose gH j' hgH hR' hj' using hPR
  have hBS := (BS l (ϖ.field a) (ainfObj _) (ainfId _) (isAinf_ainfObj _)).2 ↥T.L.T ↥T.L.T _ _
    (E.pullback σ) E j' j hR' hR LinearMap.id (fun _ _ => rfl)
  choose u hu using hBS.exists
  have hx := (hiff (I.j (toW (thetaW a LL) ϖ P v))).2 ⟨v.1, hv, rfl⟩
  choose x hx using hx
  have hm := (hiff (kappa T (j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x)))))).1 ⟨_, rfl⟩
  choose m' hm' hm'eq using hm
  have e1 : gH.comp (ϖ.toAinf a) = ((ϖ.toAinf a).restrict σ).comp H :=
    Hom.ext' (RingHom.ext fun y => by
      change gH.f (ϖ.ev a y) = ϖ.ev a (H.f y)
      rw [hH]
      exact (hgH _).trans (hψ y).symm)
  have key : TensorProduct.map (galW l (sQ l g)).toLinearMap (actZ T g) (j (E.tr (ϖ.toAinf a) x)) =
      j (E.tr (ϖ.toAinf a) (u.u (ϖ.prism a) (E.tr H x))) := by
    have h2 : j (u.u (ainfObj _) ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x))) =
        j' ((E.pullback σ).tr (ϖ.toAinf a) (E.tr H x)) := by
      refine (hu _).trans ?_
      exact LinearMap.lTensor_id_apply _ _ _
    refine (hj' (E.tr (ϖ.toAinf a) x)).symm.trans ?_
    refine Eq.trans ?_ ((congrArg j (u.u_tr (ϖ.toAinf a) (E.tr H x))).symm.trans h2).symm
    refine congrArg j' ?_
    refine ((E.tr_comp _ _ x).symm).trans ?_
    refine (congrArg (fun f => E.tr f x) e1).trans ?_
    exact E.tr_comp _ _ x
  refine ⟨⟨m', mem_ME_of_mem_M hm'⟩, hm', ?_⟩
  apply I.j.injective
  refine (Ident.j_act _ _ _ _).trans ?_
  refine Eq.trans ?_ hm'eq
  refine (congrArg (TWact (galOW (↥(OL LL)) (sQ l g)) T g) hx).trans ?_
  exact (kappa_act T g _).trans (congrArg _ key)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicDescentStepToOE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DescentStep

variable {l : ℕ} [Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem constantCoeff_frobW (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (frobW l w) =
      WittVector.constantCoeff (p := l) (R := Cb l) w ^ l := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (frobenius (Cb l) l) w).coeff 0 = _
  rw [WittVector.map_coeff, frobenius_def]

theorem constantCoeff_galW (g : GQ l) (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (galW l g w) =
      autCb l (galTilt l g) (WittVector.constantCoeff (p := l) (R := Cb l) w) := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (autCb l (galTilt l g)).toRingHom w).coeff 0 = _
  rw [WittVector.map_coeff]
  rfl

end GlobalTheory.BSP.DescentStep


open GlobalTheory.BSP.DescentStep in
theorem GlobalTheory.BSP.BK.descent_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x b : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∃ v x' b' : κ → WCb l, (∀ j, v j ∈ bk.OE) ∧ (∀ j, b' j ∈ bk.OE) ∧ (∀ j, x j = v j + ((l : ℕ) : WCb l) * x' j) ∧ (∀ j, x' j = ∑ i, frobW l (x' i) * c i j + b' j) ∧ ∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x' j) = x' j := by
  intro l _ K bk κ _ x b c hc hb hx hg
  haveI : PerfectRing (Cb l) l := perfectRing_Cb
  obtain ⟨sat, -, hφ, hfix, -⟩ := _root_.GlobalTheory.OEStable.main l K bk
  set cc := WittVector.constantCoeff (p := l) (R := Cb l) with hcc
  have hmemc : ∀ w ∈ bk.OE, cc w ∈ bk.OE.map cc := fun w hw => Subring.mem_map.2 ⟨w, hw, rfl⟩
  have key : ∀ j, cc (x j) ∈ bk.OE.map cc := by
    refine GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation l K bk κ (fun j => cc (x j)) ?_ ?_
    · intro g hgf j
      have h1 := congrArg cc (hg g hgf j)
      rw [constantCoeff_galW] at h1
      exact h1
    · intro T _ i₁ i₂ h12
      refine ⟨fun i j => i₁ (cc (c i j)), fun j => ?_⟩
      have e1 : ∀ i' : Cb l →+* T,
          i' (cc (x j)) = ∑ i, i' (cc (x i)) ^ l * i' (cc (c i j)) + i' (cc (b j)) := by
        intro i'
        conv_lhs => rw [hx j]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [RingHom.map_add cc, map_sum cc, RingHom.map_add i', map_sum i']
        refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
        rw [RingHom.map_mul cc, RingHom.map_mul i', constantCoeff_frobW, RingHom.map_pow i']
      have e2 : ∀ i, i₂ (cc (c i j)) = i₁ (cc (c i j)) := fun i => (h12 _ (hmemc _ (hc i j))).symm
      rw [e1 i₁, e1 i₂, ← h12 _ (hmemc _ (hb j))]
      simp_rw [e2]
      rcases subsingleton_or_nontrivial T with hT | hT
      · exact Subsingleton.elim _ _
      · haveI : CharP T l := charP_of_injective_ringHom i₁.injective l
        simp_rw [sub_pow_char, sub_mul, Finset.sum_sub_distrib]
        ring
  choose v hv hvx using fun j => Subring.mem_map.1 (key j)
  have hker : ∀ j, x j - v j ∈ RingHom.ker cc := fun j => by
    rw [RingHom.mem_ker, map_sub, hvx j, sub_self]
  rw [hcc, WittVector.ker_constantCoeff] at hker
  choose x' hx' using fun j => Ideal.mem_span_singleton'.1 (hker j)

  set b' : κ → WCb l := fun j => x' j - ∑ i, frobW l (x' i) * c i j with hb'
  have hlb : ∀ j, ((l : ℕ) : WCb l) * b' j = b j - v j + ∑ i, frobW l (v i) * c i j := by
    intro j
    have h3 : ∀ i, ((l : ℕ) : WCb l) * (frobW l (x' i) * c i j) = (frobW l (x i) - frobW l (v i)) * c i j := by
      intro i
      rw [← map_sub, ← hx' i, map_mul, map_natCast]
      ring
    simp only [hb', mul_sub, Finset.mul_sum, h3]
    rw [mul_comm, hx' j]
    conv_lhs => rw [hx j]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hb'mem : ∀ j, b' j ∈ bk.OE := fun j => sat _ (by
    rw [hlb j]
    refine bk.OE.add_mem (bk.OE.sub_mem (hb j) (hv j)) (bk.OE.sum_mem fun i _ => bk.OE.mul_mem (hφ _ (hv i)) (hc i j)))
  refine ⟨v, x', b', hv, hb'mem, fun j => ?_, fun j => ?_, fun g hgf j => ?_⟩
  · linear_combination (hx' j).symm
  · simp only [hb']
    ring
  · have h5 : galW l (g : GQ l) (x' j * ((l : ℕ) : WCb l)) = x' j * ((l : ℕ) : WCb l) := by
      rw [hx' j, map_sub, hg g hgf j, hfix g hgf _ (hv j)]
    rw [map_mul, map_natCast] at h5
    have h4 : (galW l (g : GQ l) (x' j) - x' j) * ((l : ℕ) : WCb l) = 0 := by
      linear_combination h5
    exact sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ h4)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  first | exact @GlobalTheory.RedLocConst.redT_mem_Z1Q | exact GlobalTheory.RedLocConst.redT_mem_Z1Q | (intros; apply GlobalTheory.RedLocConst.redT_mem_Z1Q <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPrimeToPartFbar
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

private theorem pow_pow_factorization_mul_inv_val_eq_self {K : Type} [Field K] {l : ℕ} [Fact l.Prime] [CharP K l] (y : K) (n : ℕ)
    (hy : y ^ n = 1) :
    y ^ (l ^ n.factorization l * (((l ^ n.factorization l : ℕ) : ZMod (n / l ^ n.factorization l))⁻¹).val) = y := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [ZMod.val_one_eq_one_mod]
  set q := l ^ n.factorization l with hq_def
  set m := n / q with hm_def
  have hnqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hm0 : m ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hnqm
    omega
  haveI : NeZero m := ⟨hm0⟩
  have hcop : Nat.Coprime q m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
  have hym : y ^ m = 1 := by
    have h1 : (y ^ m) ^ q = 1 := by rw [← pow_mul, mul_comm, hnqm, hy]
    have h2 : (y ^ m - 1) ^ q = 0 := by
      rw [hq_def, sub_pow_char_pow, ← hq_def, h1, one_pow, sub_self]
    have hq0 : q ≠ 0 := pow_ne_zero _ hl.ne_zero
    exact sub_eq_zero.1 ((pow_eq_zero_iff hq0).1 h2)
  have hmod : q * ((q : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one q hcop
  have hdvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
  have hmod' := hmod.of_dvd hdvd
  calc y ^ (q * ((q : ZMod m)⁻¹).val) = y ^ ((q * ((q : ZMod m)⁻¹).val) % orderOf y) := (pow_mod_orderOf _ _).symm
    _ = y ^ (1 % orderOf y) := by rw [hmod']
    _ = y := by rw [pow_mod_orderOf, pow_one]

theorem map_primeToPart_fbar {g l : ℕ} [Fact g.Prime] [Fact l.Prime] {K : Type} [Field K] [CharP K l]
    (ι : Formalism.CyclotomicNorms.Fbar g →* K) (x : Formalism.CyclotomicNorms.Fbar g) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow]
  exact pow_pow_factorization_mul_inv_val_eq_self _ _ (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end GlobalTheory.TypeLeaf
end
end

