module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphOpsModel

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sphOp_rep {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  rw [dite_eq_left h]
  exact h.choose_spec

theorem heckeOn_rep_of_not (M : DSModel V S) {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) (U : MMap M) :
    heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
  ext v g
  unfold GlobalTheory.Hk3.rep
  rw [dite_eq_right h, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
  rfl

theorem postOn_single (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  rw [GlobalTheory.LevOp.postOn_hk, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
    one_smul]

section Model

variable {M : DSModel V S} {HM : HMod (MMap M)} {P : Pl D.host.E} {h : (List ℤ →₀ ℂ) → Module.End ℂ HM.H}

theorem op_eq_sum (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    (c : List ℤ →₀ ℂ) : h c = c.sum fun d z => z • h (Finsupp.single d 1) := by
  refine LinearMap.ext fun x => inj ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hh, GlobalTheory.LevOp.postOn_hk, Finsupp.sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, map_smul, hh, postOn_single]

theorem op_single_of_not (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    {d : List ℤ} (hd : ¬ IsLab V P d) : h (Finsupp.single d 1) = 0 := by
  refine LinearMap.ext fun x => inj ?_
  rw [hh, postOn_single, heckeOn_rep_of_not M hd, LinearMap.zero_apply, map_zero]

theorem op_eigen (inj : Function.Injective HM.e) (hh : ∀ c x, HM.e (h c x) = postOn M (hk V P c) (HM.e x))
    {a : List ℤ → ℂ} {x : HM.H} (hx : ∀ d, IsLab V P d → h (Finsupp.single d 1) x = a d • x) (c : List ℤ →₀ ℂ) :
    h c x = evC V P a c • x := by
  rw [op_eq_sum inj hh, evC, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply]
  split_ifs with hd
  · rw [hx d hd, mul_smul]
  · rw [op_single_of_not inj hh hd, LinearMap.zero_apply, smul_zero, zero_smul]

end Model

theorem exists_ops (θ : InfFam D) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (a : ℂ) (ok : Pl D.host.E → Prop)
    (hM : HM.Is (Mult θ M (J : Set (GA D V)) χ) fun T T' => a * ipM M μ 𝓕 T T') (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hS : SchurMult θ M (J : Set (GA D V)) χ μ 𝓕)
    (hfull : ∀ P, ok P → ∀ d B, Hecke₂ V (J : Set (GA D V)) χ ∅ P d B ↔ SphOp V P d B)
    (hkeep : ∀ P, ok P → ∀ c, ∀ U ∈ Mult θ M (J : Set (GA D V)) χ, postOn M (hk V P c) U ∈ Mult θ M (J : Set (GA D V)) χ) :
    ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ HM.H,
      (∀ P, ok P → ∀ c x, HM.e (h P c x) = postOn M (hk V P c) (HM.e x)) ∧ NormalFam ok h := by
  obtain ⟨inj, hr, hip⟩ := hM
  have hmem : ∀ x, HM.e x ∈ Mult θ M (J : Set (GA D V)) χ := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hex : ∀ P c, ∃ h : Module.End ℂ HM.H, ok P → ∀ x, HM.e (h x) = postOn M (hk V P c) (HM.e x) := fun P c => by
    by_cases hP : ok P
    · obtain ⟨h, hh⟩ := exists_lift HM.e inj (postOn M (hk V P c)) fun x => hr ▸ hkeep P hP c _ (hmem x)
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose h hh using hex
  have hh' : ∀ P, ok P → ∀ c x, HM.e (h P c x) = postOn M (hk V P c) (HM.e x) := fun P hP c => hh P c hP
  have hdual : ∀ P, ok P → ∀ d, IsLab V P d → IsLab V P (dualLab d) := fun P hP d ⟨B, hB⟩ => by
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (GlobalTheory.HeckeAdjoint.realUnif D P) ((hfull P hP d B).2 hB)
    exact ⟨B', (hfull P hP _ B').1 hB'⟩
  refine ⟨h, hh', fun P P' hP hP' c c' => ?_, fun P hP c => ?_⟩
  · rw [op_eq_sum inj (hh' P hP) c, op_eq_sum inj (hh' P' hP') c']
    refine Commute.sum_left _ _ _ fun d _ => Commute.sum_right _ _ _ fun d' _ => ?_
    refine Commute.smul_left (Commute.smul_right ?_ _) _
    by_cases hd : IsLab V P d
    · by_cases hd' : IsLab V P' d'
      · refine LinearMap.ext fun x => inj ?_
        rw [Module.End.mul_apply, Module.End.mul_apply, hh' P hP, hh' P' hP', hh' P' hP', hh' P hP]
        simp only [postOn_single]
        exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (GlobalTheory.HeckeAdjoint.realUnif D P)
          ((hfull P hP d _).2 (sphOp_rep hd)) ((hfull P' hP' d' _).2 (sphOp_rep hd'))
          (((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v)
      · rw [op_single_of_not inj (hh' P' hP') hd']
        exact Commute.zero_right _
    · rw [op_single_of_not inj (hh' P hP) hd]
      exact Commute.zero_left _
  · have key : ∀ d, LinearMap.adjoint (h P (Finsupp.single d 1)) = h P (Finsupp.single (dualLab d) 1) := fun d => by
      by_cases hd : IsLab V P d
      · symm
        rw [LinearMap.eq_adjoint_iff]
        intro x y
        rw [hip, hip, hh' P hP, hh' P hP, postOn_single, postOn_single]
        refine congrArg (a * ·) (_root_.GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab D V S θ M J χ ∅ μ 𝓕 hθ hμ h𝓕 hS P (dualLab d) _ _
          ((hfull P hP _ _).2 (sphOp_rep (hdual P hP d hd))) ?_ _ (hmem x) _ (hmem y) ?_ ?_)
        · rw [dualLab_dualLab]
          exact (hfull P hP _ _).2 (sphOp_rep hd)
        · rw [← postOn_single]
          exact hkeep P hP _ _ (hmem x)
        · rw [← postOn_single]
          exact hkeep P hP _ _ (hmem y)
      · have hd' : ¬ IsLab V P (dualLab d) := fun h' => hd (dualLab_dualLab d ▸ hdual P hP _ h')
        rw [op_single_of_not inj (hh' P hP) hd, op_single_of_not inj (hh' P hP) hd', map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [op_eq_sum inj (hh' P hP) c, op_eq_sum inj (hh' P hP) (dualC _), dualC,
      Finsupp.sum_mapDomain_index (h := fun d (z : ℂ) => z • h P (Finsupp.single d 1)) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _),
      Finsupp.sum_mapRange_index (h := fun d (z : ℂ) => z • h P (Finsupp.single (dualLab d) 1)) (fun _ => zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [LinearEquiv.map_smulₛₗ, key]
    rfl

theorem parts_of_projector {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ok : Pl D.host.E → Prop) (lab : Pl D.host.E → List ℤ → Prop) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hN : NormalFam ok h) (p : Module.End ℂ H) (hp : p * p = p) (he : ∀ P, ok P → ∀ cc, Commute (h P cc) p)
    (W : (Pl D.host.E → List ℤ → ℂ) → Submodule ℂ H)
    (hW : ∀ c x, x ∈ W c ↔ p x = x ∧ ∀ P d, ok P → lab P d → h P (Finsupp.single d 1) x = c P d • x) :
    (⨆ c, W c) = LinearMap.range p ∧
      ∀ c (g : Module.End ℂ H), Commute p g → (∀ P, ok P → ∀ cc, Commute (h P cc) g) → (W c).map g ≤ W c := by
  refine ⟨le_antisymm (iSup_le fun c x hx => ⟨x, ((hW c x).1 hx).1⟩) ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition
      (fun j : {j : Pl D.host.E × List ℤ // ok j.1} => h j.1.1 (Finsupp.single j.1.2 1))
      (fun j k => hN.1 _ _ j.2 k.2 _ _) (fun j => ⟨⟨(j.1.1, dualLab j.1.2), j.2⟩, by
        rw [hN.2 _ j.2, dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single, star_one]⟩)
    rw [LinearMap.range_eq_map, ← h2, Submodule.map_iSup]
    refine iSup_le fun y => ?_
    classical
    refine le_iSup_of_le (fun P d => if hP : ok P then y ⟨(P, d), hP⟩ else 0) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [h1, SetLike.mem_coe, Submodule.mem_iInf] at hx
    refine (hW _ _).2 ⟨LinearMap.congr_fun hp x, fun P d hP _ => ?_⟩
    have h3 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d), hP⟩)
    have h4 : h P (Finsupp.single d 1) (p x) = p (h P (Finsupp.single d 1) x) := LinearMap.congr_fun (he P hP _).eq x
    rw [dite_eq_left hP, h4, ← map_smul]
    exact congrArg _ h3
  · rintro c g hg hg' _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := (hW c x).1 hx
    refine (hW _ _).2 ⟨?_, fun P d hP hd => ?_⟩
    · have h4 : p (g x) = g (p x) := LinearMap.congr_fun hg.eq x
      rw [h4, h1]
    · have h4 : h P (Finsupp.single d 1) (g x) = g (h P (Finsupp.single d 1) x) := LinearMap.congr_fun (hg' P hP _).eq x
      rw [h4, h2 P d hP hd, map_smul]

theorem sphericalOperators_forms_on_rank_space_normal_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i, ∃ h, IsOpsW R i h ∧ NormalFam (Good R A.μ0) h ∧ (∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g)) ∧ (⨆ c, Wcc R SF i c) = LinearMap.range (eH R i) ∧ (∀ c g, (Wcc R SF i c).map (R.gW i (sg0 D A) g) ≤ Wcc R SF i c) ∧ (∀ c P, Good R A.μ0 P → ∀ cc, ∀ x ∈ Wcc R SF i c, h P cc x = evC (Wc D i) P (c P) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, eH R i x = x → (∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x) → x ∈ Wcc R SF i c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have hM := hC.models.HW i (sg0 D A)
  have inj : Function.Injective (R.HW i (sg0 D A)).e := hM.1
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hM.2.1 ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  obtain ⟨e1, e2, e3, -⟩ := _root_.GlobalTheory.Hk3.eH_laws R F hC hX i
  obtain ⟨h, hh, hN⟩ := exists_ops R.θ (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv))
    (levChi _ (R.βW i) (R.datWp i R.triv)) (R.νW i) (R.fdW i) (R.HW i (sg0 D A)) _ (Good R A.μ0) hM hC.models.inf
    (hC.models.νW i).1.1 (hC.models.νW i).2 (hS.2.2 i)
    (fun P hP d B => ((hlev P hP).2.1 ∅ d B).trans (and_iff_right GlobalTheory.LevOp.offS_empty))
    (fun P hP c => (hlev P hP).2.2.2.2 _ R.θ _ c hC.models.inf)
  have hg : ∀ P, Good R A.μ0 P → ∀ cc g, Commute (h P cc) (R.gW i (sg0 D A) g) := fun P hP cc g => by
    refine LinearMap.ext fun x => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hh P hP, hC.models.gW, hC.models.gW, hh P hP]
    refine MultilinearMap.ext fun v => ((hlev P hP).2.2.2.1 cc (R.eG g) _ fun k hk y => ?_).symm
    rw [hlv x v k ((hlev P hP).1 k hk).1, ((hlev P hP).1 k hk).2, one_mul]
  have he : ∀ P, Good R A.μ0 P → ∀ cc, Commute (h P cc) (eH R i) := fun P hP cc =>
    Commute.sum_right _ _ _ fun g _ => (hg P hP cc g).smul_right _
  have hW : ∀ (c : Pl D.host.E → List ℤ → ℂ) x, x ∈ Wcc R SF i c ↔ eH R i x = x ∧
      ∀ P d, Good R A.μ0 P → IsLab (Wc D i) P d → h P (Finsupp.single d 1) x = c P d • x := fun c x => by
    unfold Wcc
    rw [Submodule.mem_comap, Submodule.mem_inf, e3, mem_partFull]
    refine and_congr_right fun _ => ⟨fun hx P d hP hd => inj ?_, fun hx => ⟨hmem x, fun P d B hB v => ?_⟩⟩
    · rw [hh P hP, postOn_single, map_smul]
      exact MultilinearMap.ext fun v => hx.2 P d _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩) v
    · have hP : Good R A.μ0 P := by
        obtain ⟨_, _, _, _, ho, _⟩ := hB
        exact (hoff SF hSF P).1 ho
      have hd : IsLab (Wc D i) P d := ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩
      have h1 := congrArg (R.HW i (sg0 D A)).e (hx P d hP hd)
      rw [hh P hP, postOn_single, map_smul] at h1
      rw [GlobalTheory.SphericalOps.labelUnique (J := levG _ (R.βW i) (R.datWp i R.triv)) (GlobalTheory.HeckeAdjoint.realUnif D) P d B _ hB
        (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩) _ (hlv x v)]
      exact congrArg (fun U => U v) h1
  obtain ⟨h1, h2⟩ := parts_of_projector (Good R A.μ0) (IsLab (Wc D i)) h hN (eH R i) e1 he (Wcc R SF i) hW
  refine ⟨h, hh, hN, hg, h1, fun c g => h2 c _ (e2 g) fun P hP cc => hg P hP cc g, ?_, fun c x h1 h2 => (hW c x).2 ⟨h1, h2⟩⟩
  intro c P hP cc x hx
  exact op_eigen inj (hh P hP) (fun d hd => ((hW c x).1 hx).2 P d hP hd) cc

end GlobalTheory.SphOpsModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOffLevels

open GlobalTheory.IdemSupport GlobalTheory.ResLoc Formalism.L2.JoinChr

theorem exists_glue {A : Type} [CommRing A] {e : A} (he : e * e = e) (x : Aˣ) :
    ∃ y : Aˣ, (y : A) = e * (x : A) + (1 - e) ∧ e * ((y : A) - 1) = (y : A) - 1 := by
  have hxx : (x : A) * ((x⁻¹ : Aˣ) : A) = 1 := Units.mul_inv x
  refine ⟨⟨e * (x : A) + (1 - e), e * ((x⁻¹ : Aˣ) : A) + (1 - e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · change e * (e * (x : A) + (1 - e) - 1) = e * (x : A) + (1 - e) - 1
    linear_combination ((x : A) - 1) * he

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_part {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (hu : χ.UnrAt P)
    {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D} (hd : IsDelta Φ P e) (hpl : IsPlIdem D e P)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ c y = 1 := by
  obtain ⟨d0, d1, d2⟩ := id hd
  have he : e * e = e := hpl.1
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨y, hy, hsupp⟩ := exists_glue he x
  have hyP : Φ (y : AE D) P = Φ (x : AE D) P := by
    rw [hy, ev_add, ev_mul, d1, one_mul, ev_sub, ev_one, d1, sub_self, add_zero]
  have hv : Valued.v (Φ (x : AE D) P) = 1 := by
    have a : Valued.v (Φ (x : AE D) P) ≤ 1 := (hΦ.int _).1 h1 P
    have b : Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) ≤ 1 := (hΦ.int _).1 h2 P
    have ab : Valued.v (Φ (x : AE D) P) * Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    refine le_antisymm a ?_
    rw [← ab]
    exact mul_le_of_le_one_right' b
  have hy1 : Valued.v (Φ (y : AE D) P) = 1 := by rw [hyP, hv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (y : AE D) P) (fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1)
  rw [hy1] at k1
  rw [← k1, mul_one] at k2 k3
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨z, hz, hz'⟩ := exists_units_quot y l hl
  have hyz : Φ (y : AE D) P = Φ (z : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hz'
  have hcz : c z = 1 := by
    refine hker P z (map_eq_one_of_supp (infPart D) d0 hsupp hz')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hsupp hz') ?_ ?_
    · rwa [hyz, map_mul, val_alg, ← k1, mul_one] at hy1
    · rwa [hyz, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcl : c l = 1 := by
    have e1 := hc.2 P e hpl k l hl
    have e2 : χ.locK P k = 1 := by
      refine hu (Formalism.L2.Host.atFin P k) ?_
      change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [val_alg]
      exact k1.symm
    rw [e2, Units.val_one] at e1
    exact Circle.ext e1
  exact ⟨y, hy, by rw [hz, map_mul, hcz, hcl, one_mul]⟩

theorem unrPl_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (h : χ.UnrAt P)
    (h' : χ.UnrAt (Formalism.DivisionValues.conjPl P)) : UnrPl P c := by
  intro e f hp x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd : IsDelta Φ P e := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, ⟨v, ε, hε, he⟩, ht⟩
  · have hc' : Formalism.IndefR.Lev.IsConjPl P (Formalism.DivisionValues.conjPl P) := GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl
    have hi' : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) :=
      (supported_group_and_prime_idempotents (D.sp.V 0)).2.2.2 P _ e hi hc'
    have hd' : IsDelta Φ (Formalism.DivisionValues.conjPl P) (cA D e) := delta_of_isIdemAt hΦ hi'
    have pl : ∀ {w : Pl D.host.E} {a : AE D}, Formalism.L2.NTheta.IsIdemAt a w → IsPlIdem D a w := fun ha => by
      obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := ha
      exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
    obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd (pl hi) x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_part hc h' hΦ hd' (pl hi') x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd ⟨delta_idem hΦ hd, ⟨v, ε, hε, Or.inr he⟩, ht⟩ x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

theorem unrPl_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → ∀ t P, Good R t P → UnrPl P R.eta ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → UnrPl P (R.toLevCh.mu t j) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL t P hP
  obtain ⟨hg, hc, -⟩ := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t P hP
  have hg' := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t _ hc
  have hμ : ∀ w, Good R t w → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ∀ k, (hk : k < D.R.m) →
      (R.C.mu0 ⟨k, hk⟩).UnrAt w ∧ (R.xiH t).UnrAt w := fun w hw hgw k hk => by
    refine ⟨(R.C.isMu0 _).unr w fun i hi => ?_, ?_⟩
    · have hi' : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hi
      refine hgw ?_
      rw [Nat.cast_mul]
      fin_cases i
      · exact Ideal.mul_mem_right _ _ hi'
      · exact Ideal.mul_mem_left _ _ hi'
    · by_contra h
      rcases (hL.Q_ram t w).1 h with h | ⟨PP, h, hc⟩
      · exact (hw w (Or.inr h)).1 rfl
      · exact (hw PP (Or.inr h)).2 hc
  refine ⟨unrPl_of_chrEq hL.eta (R.C.isEta.unr _) (R.C.isEta.unr _), fun j h1 h2 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have a := unrPl_of_chrEq (hL.mu0 ⟨k, h2⟩) (hμ P hP hg k h2).1 (hμ _ hc hg'.1 k h2).1
  have b := unrPl_of_chrEq (hL.xi t) (hμ P hP hg k h2).2 (hμ _ hc hg'.1 k h2).2
  intro e f h x x1 x2 x3
  show R.mu0 (k + 1) x * R.xi t x = 1
  rw [a e f h x x1 x2 x3, b e f h x x1 x2 x3, one_mul]

end GlobalTheory.UnrOffLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumPhaseSubTraceMemIntegers
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.VacPhase

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_mul' (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' (σ : L →+* L) {a : ℕ} : Formalism.UG.cT σ (1 : Matrix (Fin a) (Fin a) L) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

theorem cT_sub' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A - B) = Formalism.UG.cT σ A - Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  change Valued.v (σ (A j i)) ≤ 1
  rw [hσ]; exact h

theorem locH_sub_trace_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  intro L _ _ σ δ hσ hδ n n' JS a k JT E y hJ hP hT hSD hE hAiE hEA hk hKi hyA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJdef
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  set T : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hTdef
  set K : Matrix (Fin n) (Fin n) L := (k : Matrix (Fin n) (Fin n) L) with hKdef
  set Ki : Matrix (Fin n) (Fin n) L := ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hKidef
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hAdef
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAidef
  have hPJ : P * J = 1 := by rw [hPdef, hJdef]; exact JS.inv_mul
  have hJP : J * P = 1 := by rw [hPdef, hJdef]; exact JS.mul_inv
  have hKKi : K * Ki = 1 := by rw [hKdef, hKidef]; exact k.mul_inv
  have hAAi : A * Ai = 1 := by rw [hAdef, hAidef]; exact a.mul_inv
  set R : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ Ki * J with hRdef
  set Z : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ y * T * y with hZdef

  have h1 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) = δ * Matrix.trace ((R - 1) * Z) := by
    unfold GlobalTheory.Hk3.locH
    have : ((y * (Ki - 1)).map σ)ᵀ = Formalism.UG.cT σ (Ki - 1) * Formalism.UG.cT σ y := cT_mul' σ y (Ki - 1)
    rw [← hPdef, ← hTdef, this, cT_sub', cT_one']
    congr 1
    rw [hRdef, hZdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J P, hJP, Matrix.one_mul]
  have h2 : δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) = δ * Matrix.trace (E * Z) := by
    rw [hZdef]; simp only [Matrix.mul_assoc]

  have hR : R * (1 - E) = 1 := by
    have hcK : Formalism.UG.cT σ K * J = J * (1 - E) := by
      rw [hk, cT_add', cT_one', Matrix.add_mul, hE, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    rw [hRdef, Matrix.mul_assoc, ← hcK, ← Matrix.mul_assoc, Matrix.mul_assoc P, ← cT_mul', hKKi, cT_one', Matrix.mul_one, hPJ]
  have hR' : (1 - E) * R = 1 := mul_eq_one_comm.mp hR
  have hRE : R - 1 - E = E * R * E := by
    have e1 : R - 1 = R * E := by
      have := hR; rw [Matrix.mul_sub, Matrix.mul_one] at this
      rw [← this]; abel
    have e2 : R - 1 = E * R := by
      have := hR'; rw [Matrix.sub_mul, Matrix.one_mul] at this
      rw [← this]; abel
    calc R - 1 - E = (R - 1) * E := by rw [Matrix.sub_mul, Matrix.one_mul, e1]
      _ = E * R * E := by rw [e2]
  have h3 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) - δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) =
      δ * Matrix.trace (R * (E * Z * E)) := by
    rw [h1, h2, ← mul_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, hRE]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm E]
    simp only [Matrix.mul_assoc]
  rw [h3]

  have hRint : ∀ i j, R i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hP (cT_int σ hσ hKi)) hJ
  have hy' : Formalism.UG.cT σ y = Formalism.UG.cT σ Ai * Formalism.UG.cT σ (y * A) := by
    rw [← cT_mul', Matrix.mul_assoc, hAAi, Matrix.mul_one]
  have hW : E * Z * E = ((E * A) * (Ai * P * Formalism.UG.cT σ Ai) * Formalism.UG.cT σ (y * A)) * T * ((y * A) * (Ai * E)) := by
    rw [hZdef, hy']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A Ai, hAAi, Matrix.one_mul, ← Matrix.mul_assoc A Ai E, hAAi, Matrix.one_mul]
  have hWint : ∀ i j, (E * Z * E) i j ∈ Formalism.UG.intL L := by
    rw [hW]
    exact mul_int (mul_int (mul_int (mul_int hEA hSD.2) (cT_int σ hσ hyA)) hT) (mul_int hyA hAiE)
  refine Subring.mul_mem _ hδ ?_
  exact Subring.sum_mem _ fun i _ => mul_int hRint hWint i i

end GlobalTheory.Hk3.VacPhase

end
end

