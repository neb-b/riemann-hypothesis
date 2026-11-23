module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FilStable

theorem ι_σB {l : ℕ} [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (g : Per.Gq l) (β : Per.Bcris l) :
    C.ι (Per.σB g β) = Per.σD g (C.ι β) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := C.ι.comp (Per.σB g)) (g := (Per.σD g).comp C.ι) fun x => ?_) β
  have h1 : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (GlobalTheory.MemLoc.sigA g x) :=
    GlobalTheory.CrisMaps.σB_sigA g x
  change C.ι (Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x)) =
    Per.σD g (C.ι (algebraMap (Per.Acris l) (Per.Bcris l) x))
  rw [h1, C.ι_j, C.ι_j, GlobalTheory.MemLoc.FilLaws.σD_alg, GlobalTheory.MemLoc.CrisUnique.equivariant C.j_cris]

theorem fil_zero_stable : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (C : GlobalTheory.MemLoc.Core l), ∀ v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}, actB (sQ l) T g v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g C v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨β, x, hβ, rfl⟩ := hw
    refine Submodule.subset_span ⟨Per.σB (sQ l g) β, T.actT g x, ?_, ?_⟩
    rotate_left 1
    · simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, galOB,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    · rw [ι_σB]
      exact (GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.1 _ 0 _ hβ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BKGal.FilStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariant
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.BKGal.JumpDR

theorem cB_gal {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (g : Gl l) (b : Per.Bcris l) :
    cB Td (Per.σB (sQ l g) b) = Pl.actQdR (sQ l g) (cB Td b) := by
  have h1 : Td.eB.symm (Per.σB (sQ l g) b) = Pl.actQ (sQ l g) (Td.eB.symm b) := by
    apply Td.eB.injective
    rw [RingEquiv.apply_symm_apply, Td.actB, RingEquiv.apply_symm_apply]
  have h2 := (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).ι_comm g (Td.eB.symm b)
  rw [Pl.PD_ι, Pl.PD_ι, Pl.PD_actB, Pl.PD_actdR] at h2
  change Pl.ιB (Td.eB.symm (Per.σB (sQ l g) b)) = Pl.actQdR (sQ l g) (Pl.ιB (Td.eB.symm b))
  rw [h1]; exact h2

theorem X_equivariant (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)
    (hX : ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T),
      X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (g : Gl l) (b : TW (OB l ↥(OL LL)) T) :
    X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul u x =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add (f := _), hu, hv]
    | tmul o b =>
      have e1 : actB (sQ l) T g ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.σB (sQ l g) b) ⊗ₜ[↥(OL LL)] T.actT g x := rfl
      rw [e1, hX, hX]
      have e2 : ((T.actT g x : ↥T.L.T) : T.V) = T.ρ g (x : T.V) := rfl
      rw [e2, cB_gal]
      show _ = (T.ρ g ((o : ↥LL.1) • (x : T.V))) ⊗ₜ[ℚ_[l]] ((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actdR g (cB Td b))
      rw [map_smul, Pl.PD_actdR]
      rfl

end GlobalTheory.BKGal.JumpDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfBkADimOfFontCore
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

theorem blochKatoDim_of_bkADim_of_fontCore (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (h1 : LocalSituation.bkADim (P.PD K)) (h2 : LocalSituation.fontCore (P.PD K))
    (hO : GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL)) : BlochKatoDim (P.PD K) ↥LL.1 := by
  unfold LocalSituation.bkADim at h1
  unfold LocalSituation.fontCore at h2
  unfold BlochKatoDim
  intro hs V _ _ _ _ _ _ _ _ _ ρ hc hcrys
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := V, ρ := ρ, cont := hc, modO := Module.compHom V (algebraMap ↥(OL LL) ↥LL.1),
      towO := by
        letI : Module ↥(OL LL) V := Module.compHom V (algebraMap ↥(OL LL) ↥LL.1)
        exact ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩ }
  have hF := h2 ↥LL.1 ↥(OL LL) hO A
  have hE := h1 ↥LL.1 ↥(OL LL) hO A (hF.2.2 hcrys)
  have hfin := hF.2.1.1
  dsimp only [A] at hE hfin
  obtain ⟨e1, e2⟩ := DeRhamSplit.main l P K LL hs V ρ hfin
  rw [hE, e1, e2 0]
  push_cast [Finset.sum_sub_distrib]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoQuotientOfDivisibleImageMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevelKer

theorem mk_eq_of_smul {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (π : LL) (hπ : π ≠ 0)
    (hpr : ∀ v : V, π ^ r • v = ϖ ^ r • v) (u v w : V) (hu : u ∈ L.T) (hv : v ∈ L.T)
    (hvw : π⁻¹ ^ r • u - w ∈ L.T) (hyw : v = π ^ r • w) :
    (Submodule.Quotient.mk (⟨v, hv⟩ : ↥L.T) : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) =
      Submodule.Quotient.mk ⟨u, hu⟩ := by
  rw [Submodule.Quotient.eq]
  have ht : (⟨v, hv⟩ : ↥L.T) - ⟨u, hu⟩ = ϖ ^ r • (-(⟨_, hvw⟩ : ↥L.T)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg]
    rw [← hpr, smul_neg, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul, hyw]
    abel
  rw [ht]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem hfQ_of_ioL_mem_HfD : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI c hc
  obtain ⟨π, hπdef⟩ : ∃ π : LL, π = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hπ : π ≠ 0 := by
    obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, -, -⟩ := hO
    haveI := hDom; haveI := hDVR; haveI := hFr
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  clear hO

  obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨xq, rfl⟩, hsum⟩ := Submodule.mem_sup.1 hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xq
  obtain ⟨w, hwdef⟩ : ∃ w : ↥(GK K) → A.V, w = z + fun g => A.ρ g x - x := ⟨_, rfl⟩
  have hcob : (fun g => A.ρ g x - x) ∈ finiteCocycles (P.PD K) A.ρ := by
    refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[ℚ_[l]] (1 : _), fun g => ?_⟩
    · simp_rw [sub_eq_add_neg]
      exact (A.cont x).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · simp [actVB, sub_tmul]
  have hw : w ∈ finiteCocycles (P.PD K) A.ρ := hwdef ▸ (finiteCocycles (P.PD K) A.ρ).add_mem hz hcob

  choose ch hch using fun g => Submodule.Quotient.mk_surjective _ (c g)

  have hpt : ∀ g, (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g ∈ LA.T := by
    intro g
    have key : GlobalTheory.BKFinLevel.ioL LA ϖ r (c g) = Submodule.Quotient.mk (p := LA.T) (w g) :=
      by rw [← congrFun hsum g, hwdef]; rfl
    have h2 : (Submodule.Quotient.mk (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) : A.V ⧸ LA.T) =
        Submodule.Quotient.mk (w g) :=
      hπdef ▸ (GlobalTheory.BKFinLevel.ioL_mk LA ϖ r (ch g)).symm.trans ((congrArg _ (hch g)).trans key)
    exact (Submodule.Quotient.eq _).1 h2
  obtain ⟨y, hydef⟩ : ∃ y : ↥(GK K) → A.V, y = fun g => π ^ r • w g := ⟨_, rfl⟩
  have hyf : y ∈ finiteCocycles (P.PD K) A.ρ := by
    have h := (finiteCocycles (P.PD K) A.ρ).smul_mem (π ^ r) hw
    subst hydef; exact h
  have hpr : ∀ v : A.V, π ^ r • v = ϖ ^ r • v := fun v => by
    rw [hπdef, ← map_pow, algebraMap_smul]
  have hyT : ∀ g, y g ∈ LA.T := by
    intro g
    have : y g = ((ch g : ↥LA.T) : A.V) - ϖ ^ r • ((π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g) := by
      rw [← hpr, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul]
      simp [hydef]
    rw [this]
    exact LA.T.sub_mem (ch g).2 (LA.T.smul_mem _ (hpt g))
  have hyZ : y ∈ latticeCocycles LA := ⟨hyf.1, fun g _ => hyT g⟩
  refine Submodule.mem_sup_left ⟨⟨y, hyZ⟩, ⟨hyZ, hyf⟩, ?_⟩
  funext g
  have e : (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ⟨y, hyZ⟩) g =
      Submodule.Quotient.mk (⟨y g, hyT g⟩ : ↥LA.T) := rfl
  rw [e, ← hch g]
  exact mk_eq_of_smul LA ϖ r π hπ hpr _ _ (w g) (ch g).2 (hyT g) (hpt g) (by rw [hydef])

end GlobalTheory.BKFinLevelKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoReductionsOrthogonalModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKOrthRed

section Gen

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem liftQ_eq (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (v : V) (hv : v ∈ L.T) :
    ∃ t : ↥L.T, Formalism.MainNotions.LocalSituation.liftQ L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
      (Submodule.Quotient.mk ⟨v, hv⟩) = v + (algebraMap O LL ϖ) ^ r • (t : V) := by
  have hs := (Submodule.Quotient.mk_surjective (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
    (Submodule.Quotient.mk ⟨v, hv⟩)).choose_spec
  obtain ⟨t, ht⟩ := (mem_span_smul_top L _ _).1 ((Submodule.Quotient.eq _).1 hs)
  refine ⟨t, ?_⟩
  have h2 := congrArg (fun x : ↥L.T => (x : V)) ht
  simp only [Submodule.coe_sub, Submodule.coe_smul] at h2
  unfold Formalism.MainNotions.LocalSituation.liftQ
  rw [← map_pow, algebraMap_smul, ← h2]
  abel

end Gen

section Gal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

theorem hfQ_lift {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T)
    (hI : StableSub LA I) (c : G → ↥LA.T ⧸ I) (hc : c ∈ HfQ PD LA I hI) :
    ∃ a : G → A.V, a ∈ finiteCocycles PD A.ρ ∧ ∀ g, ∃ h : a g ∈ LA.T, c g = Submodule.Quotient.mk ⟨a g, h⟩ := by
  rw [HfQ, Submodule.mem_sup] at hc
  obtain ⟨y, hy, z, hz, rfl⟩ := hc
  obtain ⟨a0, ha0, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨xh, rfl⟩ := Submodule.Quotient.mk_surjective I x
  refine ⟨(a0 : G → A.V) + cob A.ρ (xh : A.V), (finiteCocycles PD A.ρ).add_mem ha0.2 (Formalism.MainNotions.BlochKatoDuality.Br.coboundary_mem_finite_cocycles PD A _),
    fun g => ⟨LA.T.add_mem (a0.2.2 g trivial) (LA.T.sub_mem (LA.stable g _ xh.2) xh.2), ?_⟩⟩
  show Submodule.Quotient.mk (evT LA g a0) + (actQ LA I hI g (Submodule.Quotient.mk xh) - Submodule.Quotient.mk xh) = _
  rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
  congr 1

end Gal

theorem cupQ_cobO_of_bkA : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  intro l _ P K hA LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI' c hc c' hc'
  have hA' := hA LL O hO
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  obtain ⟨a, ha, hag⟩ := hfQ_lift (P.PD K) LA _ hI c hc
  obtain ⟨b, hb, hbg⟩ := hfQ_lift (P.PD K) LA' _ hI' c' hc'
  obtain ⟨f, hf, hfd1⟩ := ((hA' A A' m hDR hd.1).1 a ha.1).1 ha b hb
  set s : LL := (algebraMap O LL ϖ)⁻¹ ^ r with hs
  have hcob : CobL (P.PD K) (fun x => s * cupL A'.ρ m a b x) := by
    refine ⟨s • f, continuous_const.mul hf, ?_⟩
    rw [map_smul, hfd1]
    rfl
  have hred := Formalism.MainNotions.BlochKatoDuality.Br.red_cob (P.PD K) hopen L1 hL1 _ hcob
  refine (Formalism.MainNotions.BlochKatoDuality.Br.cobO_congr (P.PD K) L1 _ _ ?_).2 hred
  rintro ⟨g, h⟩
  obtain ⟨hag1, hcg⟩ := hag g
  obtain ⟨hbh1, hch⟩ := hbg h
  obtain ⟨t, ht⟩ := liftQ_eq LA ϖ r (a g) hag1
  obtain ⟨t', ht'⟩ := liftQ_eq LA' ϖ r (b h) hbh1
  obtain ⟨u1, hu1⟩ := (hd.2 _).1 (LA'.stable g _ hbh1) t t.2
  obtain ⟨u2, hu2⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) (a g) hag1
  obtain ⟨u3, hu3⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) t t.2
  have ho : ∃ o : O, algebraMap O LL o = s * (algebraMap O LL ϖ) ^ r := by
    rw [hs, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
    · exact ⟨0 ^ r, by rw [h0, inv_zero, zero_mul, map_pow, map_zero]⟩
    · exact ⟨1, by rw [inv_mul_cancel₀ h0, one_pow, map_one]⟩
  obtain ⟨o, ho⟩ := ho
  rw [Submodule.Quotient.eq, hL1]
  refine ⟨o * (u1 + u2 + ϖ ^ r * u3), ?_⟩
  show _ = s * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c g)) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h))) - s * m (a g) (A'.ρ g (b h))
  rw [hcg, hch, ht, ht']
  simp only [Algebra.linearMap_apply, map_mul, map_add (f := _), map_pow, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [← hu1, ← hu2, ← hu3, ho]
  ring

end GlobalTheory.BKOrthRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEOfIsBlockSum
section
noncomputable section

namespace GlobalTheory.BlockEnl

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.BlockJumps GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount GlobalTheory.HTW.SumJumps GlobalTheory.Cmp.SmallJumps

theorem multV_oneByOne {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [Algebra.IsSeparable Qp K] [FiniteDimensional Qp LL]
    (hF : IsField BdR) (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (σ : Representation LL G (Fin 1 → LL)) (e : ℕ)
    (he : ∀ g u c, σ g u c = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e * u c)
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD σ τ a = if a = e then 1 else 0 := by
  let χ : Fin 1 → G →* LLˣ := fun _ => ((cycLL PD LL)⁻¹) ^ e
  have hχ : ∀ c g, ((χ c g : LLˣ) : LL) = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e := fun c g => by
    simp [χ, cycLL]
  have hσ : σ = diagRep χ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun c => ?_
    rw [he, diagRep_apply, hχ c]
  rw [hσ, multV_diagRep PD hF, Fin.sum_univ_one]
  exact multV_twist PD hs (Formalism.WeaklyAdmissibleFiltrations.charRep (χ 0)) e (fun g x => by rw [← hχ 0]; rfl) τ a

theorem twistM_one_apply {O Γ : Type} [CommRing O] [Group Γ] (χ : Γ →* Oˣ) (g : Γ) :
    twistM (1 : Γ →* Matrix (Fin 1) (Fin 1) O) χ g 0 0 = ((χ g : Oˣ) : O) := by
  simp [twistM]


set_option maxHeartbeats 1000000 in
theorem blockE_of_isBlockSum (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π) : BlockE D i r ρ π := by
  obtain ⟨e, he⟩ := hB
  intro w hw L' hL τ
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥L'.1 := L'.2
  let s : Br.G D.nbr i w hw → Formalism.MainNotions.N.GE D.nd := fun g => decS D.nd w (Br.iota D.nbr i w hw g)
  let j := inc D i w hw L' hL
  let f := j.comp (Br.toLLK (D.nbr i w hw))
  have hf : ∀ c, f (toK D.nd i c) = j ((D.nbr i w hw).toLL c) :=
    fun c => congrArg j (Br.toLLK_alg (D.nbr i w hw) c)
  have hχ0 : ∀ (c : ℕ), c + 1 ≤ D.R.t → ∀ g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i (c + 1) g =
      (epsU D.nd i g)⁻¹ ^ c := fun c hc g => by
    have h := D.nd.chi_def i (c + 1) (by omega) hc
    change (D.nd.chi i 1)⁻¹ g * D.nd.chi i (c + 1) g = _
    rw [h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl
  have hχ : ∀ (c : Fin D.R.t) g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i ((c : ℕ) + 1) g =
      (epsU D.nd i g)⁻¹ ^ (c : ℕ) := fun c g => hχ0 c c.2 g
  have hε : ∀ g, j ((D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i)) =
      algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
    intro g
    have h1 : (D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i) =
        algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
      rw [Br.PD, (D.loc _).PD_χ, ← cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
      exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)
    rw [h1]
    exact (IntermediateField.inclusion hL).commutes _
  have hM : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) g v,
      matRep (locE D i w hw L' hL M) g v = ((mapM (toK D.nd i) M (s g)).map f).mulVec v := fun M g v => by
    rw [show (mapM (toK D.nd i) M (s g)).map f = locE D i w hw L' hL M g from
      Matrix.ext fun a b => hf _]
    rfl
  have hs : ∃ x ∈ (Br.PD D.loc D.nbr i w hw).Fil (-1),
      (Br.PD D.loc D.nbr i w hw).ι (Br.PD D.loc D.nbr i w hw).t * x = 1 := by
    obtain ⟨x, hx, hx1⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one (D.locT (D.nd.l i))
    refine ⟨x, ?_, by rw [Br.PD, (D.loc _).PD_ι, (D.loc _).period_datum_t_eq, hx1]⟩
    exact ((D.locT _).fil _ _ _).2 (((D.locT _).fil _ _ _).1 hx)
  have hpow : ∀ g (n : ℕ), f (toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ n : (D.nd.O i)ˣ) : D.nd.O i)) =
      (algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹ ^ n := fun g n => by
    rw [hf, Units.val_pow_eq_pow_val, map_pow, map_pow, map_units_inv, map_inv₀, hε]
  refine ⟨fun a => ?_, fun c hc a => ?_⟩
  · obtain ⟨e', he'⟩ := split_map f (fun g => mapM (toK D.nd i) (rTwO D.nd i r π) (s g))
      (fun g => mapM (toK D.nd i) (WpO D.nd i ρ π) (s g))
      (fun g c => toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ (c : ℕ) : (D.nd.O i)ˣ) : D.nd.O i)) e (fun g u => by
        have h1 : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) v,
            (mapM (toK D.nd i) (twistM M (chiU D.nd i 1)⁻¹) (s g)).mulVec v =
              toK D.nd i (((chiU D.nd i 1)⁻¹ (s g) : (D.nd.O i)ˣ) : D.nd.O i) •
                (mapM (toK D.nd i) M (s g)).mulVec v := fun M v => by
          rw [← Matrix.smul_mulVec]
          congr 1
          ext a b
          exact map_mul (toK D.nd i) _ _
        rw [rTwO, WpO, h1, h1, map_smul, he]
        refine Prod.ext rfl (funext fun c => ?_)
        simp only [← hχ, Units.val_mul, map_mul, mul_assoc]
        rfl)
    obtain ⟨J, h1, h2⟩ := jumps_of_split (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs
      (matRep (locE D i w hw L' hL (rTwO D.nd i r π))) (matRep (locE D i w hw L' hL (WpO D.nd i ρ π))) e'
      (fun g u => by
        rw [hM, hM, he']
        exact Prod.ext rfl (funext fun c => congrArg (· * (e' u).2 c) (hpow g c))) τ
    rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
    push_cast
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    rw [multV_oneByOne (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs _ n
      (fun g u b => ?_) τ a, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [hM, ← hpow, ← hχ0 n hc2, Subsingleton.elim b 0]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue]
    congr 1
    change f (toK D.nd i (chiRatO D.nd i (n + 1) (s g) 0 0)) = _
    rw [chiRatO, twistM_one_apply, MonoidHom.mul_apply, mul_comm]

end GlobalTheory.BlockEnl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopePointFactorsThroughSectionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 → ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O → ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧ s.comp En.inr = (ainfHom K g).comp bk.ι ∧ ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  first | exact @GlobalTheory.BSP.envPoint_factors | exact GlobalTheory.BSP.envPoint_factors | (intros; apply GlobalTheory.BSP.envPoint_factors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  first | exact @GlobalTheory.BKCoord.main | exact GlobalTheory.BKCoord.main | (intros; apply GlobalTheory.BKCoord.main <;> assumption)
end

