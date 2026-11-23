module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem isLogJ_pow {e : Per.Fl l} (hJ : InJ (Per.tm e - 1)) {y : Per.Acris l} (hy : IsLogJ (Per.tm e - 1) y) :
    ∀ m : ℕ, IsLogJ (Per.tm (e ^ m) - 1) ((m : Per.Acris l) * y)
  | 0 => by simpa using (isLogJ_zero : IsLogJ (l := l) 0 0)
  | m + 1 => by
    have h := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ (inJ_pow hJ m) hJ (isLogJ_pow hJ hy m) hy
    have e1 : Per.tm (e ^ (m + 1)) - 1 = (Per.tm (e ^ m) - 1) + (Per.tm e - 1) +
        (Per.tm (e ^ m) - 1) * (Per.tm e - 1) := by
      rw [pow_succ, show Per.tm (e ^ m * e) = Per.tm (e ^ m) * Per.tm e from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [e1]
    convert h using 1
    push_cast
    ring

theorem iter_mul (a b : Per.Fl l) (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] (a * b) =
    ((frobeniusEquiv (Per.Fl l) l).symm)^[m] a * ((frobeniusEquiv (Per.Fl l) l).symm)^[m] b := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]

theorem iter_one (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] 1 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem rootT_mul (a b : Per.Fl l) (m : ℕ) : rootT (a * b) m = rootT a m * rootT b m := by
  simp only [rootT, iter_mul, map_mul]

theorem rootT_one (m : ℕ) : rootT (1 : Per.Fl l) m = 1 := by
  simp only [rootT, iter_one, map_one]

theorem exists_gal_log (C : Core l) (x : Per.Fl l) (hx : IsUnit x) (g : GQ l) (c : ℤ_[l])
    (H : ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) :
    ∃ e : Per.Fl l, e.untilt = 1 ∧ Per.σF g x = x * e ∧
      IsLogA e (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t) := by
  obtain ⟨v, hv⟩ := hx.exists_left_inv
  have hxe : Per.σF g x = x * (v * Per.σF g x) := by rw [← mul_assoc, mul_comm x v, hv, one_mul]
  have hre : ∀ m, rootT (v * Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := by
    intro m
    have hu : IsUnit (rootT x m) := by
      have h1 := congrArg (fun z => rootT z m) hv
      simp only [rootT_mul, rootT_one] at h1
      exact ⟨⟨rootT x m, rootT v m, by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    apply hu.mul_left_cancel
    rw [← rootT_mul, ← hxe, H m, mul_comm]
  have he1 : (v * Per.σF g x).untilt = 1 := by
    have := hre 0
    simp only [rootT, Function.iterate_zero, id] at this
    rw [this, TAct.eps_untilt C, one_pow]
  have hr : ∀ m, (rootT (v * Per.σF g x) m : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (C.ζ m ^ (PadicInt.toZModPow m c).val) := by
    intro m
    rw [hre m, SubmonoidClass.coe_pow, C.ε_root m, map_pow]
  obtain ⟨y, hy⟩ := Model.exists_isLogA he1
  exact ⟨_, he1, hxe, GlobalTheory.Pst.NoLog.log_eq C _ c y hr hy ▸ hy⟩

theorem map_inv_units {R : Type} [CommRing R] (f : R →+* R) (u : Rˣ) (h : f u = u) :
    f (↑u⁻¹ : R) = ↑u⁻¹ := by
  have h1 := congrArg f (Units.inv_mul u)
  rw [map_mul, h, map_one] at h1
  calc f (↑u⁻¹ : R) = f ↑u⁻¹ * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem exists_log_unit : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  intro l _ C x hx
  obtain ⟨ω, x₁, N, hxω, hJ, hω⟩ := GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split l x hx
  obtain ⟨y, hy⟩ := _root_.GlobalTheory.LogU.exists_isLogJ l _ hJ
  have hpow := isLogJ_pow hJ hy
  obtain ⟨u, hu⟩ := (isUnit_l_Bcris l).pow N
  have hωu : IsUnit ω := isUnit_of_mul_isUnit_left (hxω ▸ hx)
  refine ⟨↑u⁻¹ * algebraMap (Per.Acris l) (Per.Bcris l) y, ?_, fun g c H => ?_⟩
  · have h2 := isLogJ_extends (GlobalTheory.CrisMaps.phiA_extends l) hy
    have h3 : Per.φA l (Per.tm (x₁ ^ l ^ N) - 1) = Per.tm ((x₁ ^ l ^ N) ^ l) - 1 := by
      rw [map_sub, map_one, show Per.φA l (Per.tm (x₁ ^ l ^ N)) = Per.tm ((x₁ ^ l ^ N) ^ l) from
        GlobalTheory.RingIface.phiA_teich l _]
    rw [h3] at h2
    have h1 : GlobalTheory.MemLoc.phiA l y = (l : Per.Acris l) * y := isLogJ_unique h2 (hpow l)
    have hφY : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) y := by
      have : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
          algebraMap _ _ (GlobalTheory.MemLoc.phiA l y) :=
        GlobalTheory.CrisMaps.φB_phiA l y
      rw [this, h1, map_mul, map_natCast]
    have hφu : Per.φB l (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    rw [map_mul, hφu, hφY]
    ring
  · obtain ⟨e, he1, hgx, hle⟩ := exists_gal_log C x hx g c H
    have hgω : Per.σF g ω = ω := hω g e he1 hgx
    have hgx₁ : Per.σF g x₁ = x₁ * e := by
      apply hωu.mul_left_cancel
      rw [← mul_assoc, ← hxω, ← hgx, hxω, map_mul, hgω]
    have hge₁ : Per.σF g (x₁ ^ l ^ N) = x₁ ^ l ^ N * e ^ l ^ N := by rw [map_pow, hgx₁, mul_pow]
    have hle' := TAct.logA_pow C.j_cris he1 hle (l ^ N)
    have hsum := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ hJ (inJ_mu (e := e ^ l ^ N) (by rw [map_pow, he1, one_pow])) hy hle'
    have hσ := isLogJ_extends (GlobalTheory.CrisMaps.sigA_extends g) hy
    have hw : Per.σA g (Per.tm (x₁ ^ l ^ N) - 1) = (Per.tm (x₁ ^ l ^ N) - 1) + mu (e ^ l ^ N) +
        (Per.tm (x₁ ^ l ^ N) - 1) * mu (e ^ l ^ N) := by
      rw [map_sub, map_one, show Per.σA g (Per.tm (x₁ ^ l ^ N)) = Per.tm (Per.σF g (x₁ ^ l ^ N)) from
        GlobalTheory.RingIface.sigA_teich l g _, hge₁, mu,
        show Per.tm (x₁ ^ l ^ N * e ^ l ^ N) = Per.tm (x₁ ^ l ^ N) * Per.tm (e ^ l ^ N) from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [hw] at hσ
    have hy' := isLogJ_unique hσ hsum
    have hσY : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        algebraMap _ _ (GlobalTheory.MemLoc.sigA g y) :=
      GlobalTheory.CrisMaps.σB_sigA g y
    have hσu : Per.σB g (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    have hul : (↑u⁻¹ : Per.Bcris l) * ((l ^ N : ℕ) : Per.Bcris l) = 1 := by
      rw [Nat.cast_pow, ← hu, Units.inv_mul]
    rw [map_mul, hσu, hσY, hy', map_add (f := _), map_mul, map_mul, map_natCast]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA l c, GlobalTheory.RingIface.aB_eq_alg l (Per.zA l c)]
    simp only [Core.tB]
    linear_combination (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) *
      algebraMap (Per.Acris l) (Per.Bcris l) C.t) * hul

end GlobalTheory.LogU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TwistDR

theorem exists_unit_of_span {k F R : Type} [Field k] [Infinite k] [Field F] [CommRing R] [Algebra F R]
    [Module k R] [Module.Finite F R] (hk : ∀ (c : k) (x : R), ∃ r : R, c • x = r * x)
    (U : Submodule k R) (hU : Submodule.span F (U : Set R) = ⊤) : ∃ d ∈ U, IsUnit d := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite F R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let S : MaximalSpectrum R → Submodule k U := fun m =>
    { carrier := {x | (x : R) ∈ m.asIdeal}
      add_mem' := fun ha hb => m.asIdeal.add_mem ha hb
      zero_mem' := m.asIdeal.zero_mem
      smul_mem' := fun c x hx => by
        obtain ⟨r, hr⟩ := hk c x
        change c • (x : R) ∈ m.asIdeal
        rw [hr]
        exact m.asIdeal.mul_mem_left r hx }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : Submodule.span F (U : Set R) ≤ m.asIdeal.restrictScalars F :=
      Submodule.span_le.2 fun x hx => (hm ▸ Submodule.mem_top : (⟨x, hx⟩ : U) ∈ S m)
    exact h1 (hU ▸ Submodule.mem_top)
  have h2 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 h2
  refine ⟨x, x.2, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hx
  exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR (ρ : Representation LL G V) (x : V ⊗[Qp] BdR) :
    x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, sub_eq_zero]

def tw (χ : G → LL) (g : G) : BdR ⊗[Qp] LL →ₗ[Qp] BdR ⊗[Qp] LL :=
  TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) (LinearMap.mulLeft Qp (χ g))

theorem tw_tmul (χ : G → LL) (g : G) (b : BdR) (c : LL) :
    tw PD χ g (b ⊗ₜ[Qp] c) = PD.actdR g b ⊗ₜ[Qp] (χ g * c) := rfl

theorem tw_smul (χ : G → LL) (g : G) (b : BdR) (w : BdR ⊗[Qp] LL) :
    tw PD χ g (b • w) = PD.actdR g b • tw PD χ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [tw_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

def twInv (χ : G → LL) : Submodule K (BdR ⊗[Qp] LL) where
  carrier := {x | ∀ g, tw PD χ g x = x}
  add_mem' ha hb g := by rw [map_add (f := _), ha g, hb g]
  zero_mem' g := map_zero _
  smul_mem' c x hx g := by
    rw [← algebraMap_smul BdR c x, tw_smul, AlgEquiv.commutes, hx g]

theorem finrank_twInv [FiniteDimensional Qp LL] (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank K ↥(twInv PD χ) = finrank Qp LL := by
  haveI := PD.finK
  let e : (Fin 1 → LL) ⊗[Qp] BdR ≃ₗ[Qp] BdR ⊗[Qp] LL :=
    ((LinearEquiv.funUnique (Fin 1) Qp LL).rTensor BdR).trans (TensorProduct.comm Qp LL BdR)
  have he : ∀ g x, e (actVdR PD ν g x) = tw PD χ g (e x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [e, actVdR, tw_tmul, hν]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hm : ((DdR PD ν).restrictScalars Qp).map (e : _ →ₗ[Qp] _) = (twInv PD χ).restrictScalars Qp := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.restrictScalars_mem, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [← he, e.injective.eq_iff]
  have h1 : finrank Qp ↥(twInv PD χ) = finrank Qp ↥(DdR PD ν) := by
    have := LinearEquiv.finrank_map_eq e ((DdR PD ν).restrictScalars Qp)
    rw [hm] at this
    exact this
  have : Module.Free LL ↥(DdR PD ν) := Module.Free.of_divisionRing LL _
  rw [← Module.finrank_mul_finrank Qp K ↥(twInv PD χ), ← Module.finrank_mul_finrank Qp LL ↥(DdR PD ν), h,
    finrank_fintype_fun_eq_card, Fintype.card_fin, mul_one, mul_comm (finrank Qp LL)] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem exists_unit [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR) (χ : G → LL)
    (h : finrank K ↥(twInv PD χ) = finrank Qp LL) : ∃ d ∈ twInv PD χ, IsUnit d := by
  letI : Field BdR := hB.toField
  haveI : Infinite K := Infinite.of_injective _ (algebraMap Qp K).injective
  have hpos : 0 < finrank Qp LL := finrank_pos
  haveI : Module.Finite K ↥(twInv PD χ) := Module.finite_of_finrank_pos (h ▸ hpos)
  refine exists_unit_of_span (F := BdR) (fun c x => ⟨algebraMap K _ c, Algebra.smul_def c x⟩) _ ?_
  let v := Module.finBasisOfFinrankEq K _ h
  have h1 : LinearIndependent K fun i => (v i : BdR ⊗[Qp] LL) :=
    v.linearIndependent.map' (twInv PD χ).subtype (twInv PD χ).ker_subtype
  have h2 : LinearIndependent BdR fun i => (v i : BdR ⊗[Qp] LL) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    refine GlobalTheory.RegularRing.linearIndepOn_of_invariant (fun g b => PD.actdR g b)
      (fun g => (tw PD χ g).toAddMonoidHom) (tw_smul PD χ) ?_ _ (fun g i => (v i).2 g) s
      (h1.linearIndepOn _)
    intro b b' hb hg
    obtain ⟨c, hc⟩ := PD.invdR (b' / b) fun g => by
      have h3 : PD.actdR g b ≠ 0 := (map_ne_zero _).2 hb
      rw [map_div₀, div_eq_div_iff h3 hb]
      linear_combination hg g
    exact ⟨c, by rw [hc, div_mul_cancel₀ _ hb]⟩
  haveI : Nonempty (Fin (finrank Qp LL)) := ⟨⟨0, hpos⟩⟩
  rw [eq_top_iff, ← h2.span_eq_top_of_card_eq_finrank (by simp)]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact (v i).2


variable (V) in
def mulR : BdR ⊗[Qp] LL →ₗ[Qp] (V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR) :=
  TensorProduct.lift (LinearMap.mk₂ Qp
    (fun b c => c • AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b))
    (fun b b' c => by ext; simp [add_mul, tmul_add])
    (fun q b c => by ext; simp [smul_comm q c])
    (fun b c c' => add_smul _ _ _)
    (fun q b c => smul_assoc _ _ _))

theorem mulR_tmul (b : BdR) (c : LL) (v : V) (b' : BdR) :
    mulR V (b ⊗ₜ[Qp] c) (v ⊗ₜ[Qp] b') = (c • v) ⊗ₜ[Qp] (b * b') := by
  simp [mulR, smul_tmul']

theorem mulR_one (x : V ⊗[Qp] BdR) : mulR V (1 : BdR ⊗[Qp] LL) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [Algebra.TensorProduct.one_def, mulR_tmul, one_smul, one_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mulR_mul (d d' : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    mulR V (d * d') x = mulR V d (mulR V d' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ =>
      induction d' using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add (f := _), LinearMap.add_apply, hx, hy]
      | tmul b₂ c₂ => simp only [Algebra.TensorProduct.tmul_mul_tmul, mulR_tmul, mul_smul, mul_assoc]

theorem act_mulR (ρ ρ' : Representation LL G V) (χ : G → LL) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (g : G) (d : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ' g (mulR V d x) = mulR V (tw PD χ g d) (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ => simp [mulR_tmul, tw_tmul, actVdR, hρ, mul_smul]

theorem finrank_DdR_twist [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank LL ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) := by
  obtain ⟨_, hd, d, rfl⟩ := exists_unit PD hB χ (finrank_twInv PD ν χ hν h)
  let e : V ⊗[Qp] BdR ≃ₗ[LL] V ⊗[Qp] BdR := LinearEquiv.ofLinear (mulR V d.1) (mulR V d⁻¹.1)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.mul_inv, mulR_one, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.inv_mul, mulR_one, LinearMap.id_apply])
  have he : ∀ g x, actVdR PD ρ' g (e x) = e (actVdR PD ρ g x) := fun g x => by
    change actVdR PD ρ' g (mulR V d.1 x) = mulR V d.1 _
    rw [act_mulR PD ρ ρ' χ hρ, hd g]
  have hm : (DdR PD ρ).map (e : _ →ₗ[LL] _) = DdR PD ρ' := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_DdR, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [he, e.injective.eq_iff]
  rw [← hm, LinearEquiv.finrank_map_eq]

end Generic

theorem isDR_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsDR (P.PD K) ν → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ') := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ h
  haveI := LL.2
  unfold IsDR
  rw [finrank_DdR_twist (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ ρ' ν χ hν hρ h]

end GlobalTheory.TwistDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittResidueFieldInRingOfIntegers
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Res

open IsLocalRing

theorem exists_teich {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] (x : O) :
    ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ t - x ∈ maximalIdeal O := by
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  obtain ⟨t, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal O)
    (Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X)
    (Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq)) x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue O _)
      simp [Polynomial.derivative_X_pow, FiniteField.cast_card_eq_zero])
  exact ⟨t, by simpa [sub_eq_zero] using h1, h2⟩

theorem sol_mem_range {O F : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] [Field F] (f : O →+* F) (hf : Function.Injective f) (y : F)
    (hy : y ^ Fintype.card (ResidueField O) = y) : ∃ t, f t = y := by
  classical
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  have : ∀ r : ResidueField O, ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ residue O t = r := fun r => by
    obtain ⟨x, rfl⟩ := residue_surjective r
    obtain ⟨t, h1, h2⟩ := exists_teich x
    exact ⟨t, h1, by rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]⟩
  choose t h1 h2 using this
  have hinj : Function.Injective fun r => f (t r) := fun r s h => by
    rw [← h2 r, ← h2 s, hf h]
  set P : Polynomial F := Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero hq
  have hd : P.natDegree = Fintype.card (ResidueField O) := Polynomial.natDegree_X_pow_sub_X (R := F) hq
  have hm : ∀ z : F, z ^ Fintype.card (ResidueField O) = z → z ∈ P.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, hz]
  have hs : Finset.univ.image (fun r => f (t r)) = P.roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hz
      exact hm _ (by rw [← map_pow, h1])
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hd]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  obtain ⟨r, -, hr⟩ := Finset.mem_image.1 (hs ▸ hm y hy)
  exact ⟨_, hr⟩

theorem exists_witt_residue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (a : ℕ) (_ : NeZero a) (w : Wq l a →ₐ[ℤ_[l]] ↥(OL K)), Kunr l a ≤ K.1 ∧ (∀ c, intToOC K (w c) = Per.θ l (wA l a c)) ∧ ∀ x : ↥(OL K), ∃ c, ¬ IsUnit (x - w c) := by
  intro l hl K
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hfin : Module.Finite ℤ_[l] ↥(OL K) := finite_OL K
  have hfin' : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥K.1) := hfin
  have hdvr : IsDiscreteValuationRing ↥(OL K) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥K.1
  have hfa := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥K.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥K.1
  have hc : IsAdicComplete (maximalIdeal ↥(OL K)) ↥(OL K) :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _
  have hF : Finite (ResidueField ↥(OL K)) :=
    ResidueField.finite_of_finite (R := ℤ_[l]) (Finite.of_equiv _ PadicInt.residueField.symm.toEquiv)
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have hch : CharP (ResidueField ↥(OL K)) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue ↥(OL K)), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] ↥(OL K)),
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff]
    exact PadicInt.p_nonunit
  obtain ⟨a, -, ha⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  have hne : NeZero (a : ℕ) := ⟨a.ne_zero⟩
  let f : ↥(OL K) →+* Om l := K.1.val.toRingHom.comp (OL K).val.toRingHom
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hle : Kunr l a ≤ K.1 := IntermediateField.adjoin_le_iff.2 fun y hy => by
    obtain ⟨t, rfl⟩ := sol_mem_range f hf y (by rw [ha]; exact hy)
    exact (t : ↥K.1).2
  have : HasUnr a K := ⟨hle⟩
  refine ⟨a, hne, thetaW a K, hle, intToOC_thetaW a K, fun x => ?_⟩
  obtain ⟨t, h1, h2⟩ := exists_teich x
  rw [ha] at h1
  suffices ∃ c, thetaW a K c = t by
    obtain ⟨c, rfl⟩ := this
    exact ⟨c, fun h => h2 (by simpa using h.neg)⟩
  rcases eq_or_ne t 0 with rfl | h0
  · exact ⟨0, map_zero _⟩
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h3 := one_lt_pow_l l a
  have : NeZero (l ^ (a : ℕ) - 1) := ⟨by omega⟩
  obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one (ξ := f t) (by
    rw [← map_pow, ← map_one f]
    congr 1
    exact mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h3.le, one_mul, h1]))
  refine ⟨WittVector.teichmuller l z ^ k, intToOC_injective K ?_⟩
  rw [intToOC_thetaW, map_pow, map_pow, wA_teich, WittVector.fontaineTheta_teichmuller]
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
  exact (map_pow (algebraMap (Om l) ℂ_[l]) ω k).symm.trans (congrArg _ hk)

end GlobalTheory.BSP.Res
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatumStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H1_period_datum : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), TateFiniteness (P.PD K) := by
  first | exact @GlobalTheory.TateFiniteH1.tate_finH1 | exact GlobalTheory.TateFiniteH1.tate_finH1 | (intros; apply GlobalTheory.TateFiniteH1.tate_finH1 <;> assumption)
end

