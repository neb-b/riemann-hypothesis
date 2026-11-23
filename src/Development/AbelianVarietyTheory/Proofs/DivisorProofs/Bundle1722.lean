module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.AbsHalfConj

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {a : L} {b : L'} (h : Valued.v a = Valued.v b) : ordL a = ordL b := by
  unfold ordL
  by_cases ha : Valued.v a = 0
  · rw [dite_eq_left ha, dite_eq_left (h ▸ ha)]
  · rw [dite_eq_right ha, dite_eq_right (h ▸ ha)]
    congr 2
    exact WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, WithZero.coe_unzero, h])

theorem absHalf_conjPl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ x : E, absHalf u (algebraMap E (u.adicCompletion E) x) = absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
  intro E _ _ _ w u hne hund x
  have hcu : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w u :=
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w u).1 hund).resolve_left hne
  have hv : Valued.v (algebraMap E (u.adicCompletion E) x) =
      Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
    have h1 : Valued.v (algebraMap E (u.adicCompletion E) x) = u.valuation E x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) =
        w.valuation E (IsCMField.complexConj E x) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    have := hcu (IsCMField.complexConj E x)
    simp only [AlgEquiv.coe_ringEquiv, IsCMField.complexConj_apply_apply] at this
    exact this
  have hq : qV E u = qV E w := by
    unfold qV
    rw [eq_conjSrc hcu, GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc]
  unfold absHalf
  rw [ordL_congr hv, hq]

end GlobalTheory.BCT.AbsHalfConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open Filter Topology

noncomputable section

namespace GlobalTheory.PureGlue

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_slice (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (z : κ → Af F) :
    ∃ f : SInf F κ, ∀ a : κ → AF F, (∀ i, (a i).2 = z i) → Φ a = f (fun i => evI F (a i)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, -, rfl⟩ := hΦ
    refine ⟨g z • f, fun a ha => ?_⟩
    have h : (fun i => (a i).2) = z := funext ha
    show f _ * g (fun i => (a i).2) = _
    rw [h, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]
    rfl
  | zero => exact ⟨0, fun a _ => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨f1, hf1⟩ := h1
    obtain ⟨f2, hf2⟩ := h2
    exact ⟨f1 + f2, fun a ha => by simp [hf1 a ha, hf2 a ha]⟩
  | smul c Φ _ h =>
    obtain ⟨f1, hf1⟩ := h
    exact ⟨c • f1, fun a ha => by simp [hf1 a ha]⟩

theorem isLocallyConstant_fin (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (b : κ → Ainf F) :
    IsLocallyConstant (fun z : κ → Af F => Φ (fun i => (b i, z i))) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    exact (IsLocallyConstant.const (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (b i))).mul hg.1
  | zero => exact IsLocallyConstant.const 0
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.comp (fun t => c • t)

def hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) : Af F :=
  g + ∑ v ∈ S, singleFin v (evalV F v y - evalV F v g)

theorem evalV_hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (hyb S y g) = if u ∈ S then evalV F u y else evalV F u g := by
  unfold hyb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum]
  split_ifs with hu
  · rw [Finset.sum_eq_single u (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h),
      evalV_singleFin_self]
    abel
  · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (by rintro rfl; exact hu hv) _), add_zero]

theorem hyb_insert {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (y g : Af F) :
    hyb (insert v S) y g = hyb S y g + singleFin v (evalV F v y - evalV F v g) := by
  unfold hyb
  rw [Finset.sum_insert hv]
  abel

theorem hyb_empty (y g : Af F) : hyb ∅ y g = g := by simp [hyb]

theorem tendsto_hyb (y g : Af F) : Tendsto (fun S => hyb S y g) atTop (𝓝 y) :=
  GlobalTheory.AdelicLimit.tendsto_finAdele _ y g
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_pos hv] at h; exact h)
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_neg hv] at h; exact h)

end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue
variable {F : Type} [Field F] [NumberField F]
theorem liftV_fst (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl
theorem liftV_snd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).2 = singleFin v a := rfl
theorem fst_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).1 = p.1 := by
  change p.1 - (GlobalTheory.LatVac.liftV v a).1 + (GlobalTheory.LatVac.liftV v b).1 = p.1
  rw [liftV_fst, liftV_fst, sub_zero, add_zero]
theorem snd_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).2 = p.2 - singleFin v a + singleFin v b := by
  change p.2 - (GlobalTheory.LatVac.liftV v a).2 + (GlobalTheory.LatVac.liftV v b).2 = _
  rw [liftV_snd, liftV_snd]
end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue

open scoped Classical

theorem eq_pure_of_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  intro F _ _ κ _ vac hvac hcof Φ hΦ hsl
  set T0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1} with hT0
  have hT0f : T0.Finite := hcof
  have hex : ∀ v, ∃ ζ : κ → Fv F v, vac v ζ ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact hvac v (funext h)
  let ζ : ∀ v, κ → Fv F v := fun v => if v ∈ T0 then (hex v).choose else 0
  have hζ1 : ∀ v, v ∉ T0 → vac v (ζ v) = 1 := by
    intro v hv
    have h : vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := not_not.1 hv
    simp only [ζ, if_neg hv]
    rw [h, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
      fun i => zero_mem _)]
    rfl
  have hζ : ∀ v, vac v (ζ v) ≠ 0 := by
    intro v
    by_cases hv : v ∈ T0
    · simp only [ζ, if_pos hv]
      exact (hex v).choose_spec
    · rw [hζ1 v hv]
      exact one_ne_zero
  let ξ0 : κ → Af F := fun i => ∑ v ∈ hT0f.toFinset, singleFin v (ζ v i)
  have hξ0 : ∀ v i, evalV F v (ξ0 i) = ζ v i := by
    intro v i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ξ0, map_sum]
    by_cases hv : v ∈ T0
    · rw [Finset.sum_eq_single v (fun u _ hu => evalV_singleFin_ne (Ne.symm hu) _)
        (fun h => absurd (hT0f.mem_toFinset.2 hv) h), evalV_singleFin_self]
    · rw [Finset.sum_eq_zero (fun u hu => evalV_singleFin_ne
        (by rintro rfl; exact hv (hT0f.mem_toFinset.1 hu)) _)]
      simp [ζ, hv]
  set c : ℂ := ∏ v ∈ hT0f.toFinset, vac v (ζ v) with hcdef
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hζ v
  obtain ⟨f0, hf0⟩ := exists_slice Φ hΦ ξ0
  refine ⟨c⁻¹ • f0, ?_⟩
  funext x
  have hev : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : AF F), evFin F v a = evalV F v a.2 := fun _ _ => rfl
  let P : Finset (HeightOneSpectrum (𝓞 F)) → κ → AF F := fun S i => ((x i).1, hyb S (x i).2 (ξ0 i))
  have key : ∀ S, Φ (P S) * ∏ v ∈ S, vac v (ζ v) =
      Φ (P ∅) * ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
      let y : κ → AF F := fun k => P S k - GlobalTheory.LatVac.liftV v (ζ v k)
      have hy : ∀ k, evFin F v (y k) = 0 := by
        intro k
        simp only [y, map_sub, GlobalTheory.LatVac.evFin_liftV]
        rw [hev]
        change evalV F v (hyb S (x k).2 (ξ0 k)) - ζ v k = 0
        rw [evalV_hyb, if_neg hv, hξ0, sub_self]
      obtain ⟨a, ha⟩ := hsl v y hy
      have e1 : P S = y + fun k => GlobalTheory.LatVac.liftV v (ζ v k) := by
        funext k
        simp [y]
      have e2 : P (insert v S) = y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k)) := by
        funext k
        have hk : (y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k))) k =
            P S k - GlobalTheory.LatVac.liftV v (ζ v k) + GlobalTheory.LatVac.liftV v (evFin F v (x k)) := rfl
        rw [hk]
        refine Prod.ext ?_ ?_
        · rw [fst_sub_add]
        · rw [snd_sub_add]
          show hyb (insert v S) (x k).2 (ξ0 k) =
            hyb S (x k).2 (ξ0 k) - singleFin v (ζ v k) + singleFin v (evFin F v (x k))
          rw [hyb_insert hv, hξ0, map_sub, hev]
          abel
      have h1 := ha (ζ v)
      have h2 := ha (fun i => evFin F v (x i))
      rw [← e1] at h1
      rw [← e2] at h2
      rw [Finset.prod_insert hv, Finset.prod_insert hv]
      linear_combination (vac v (ζ v) * ∏ u ∈ S, vac u (ζ u)) * h2 -
        (vac v (fun i => evFin F v (x i)) * ∏ u ∈ S, vac u (ζ u)) * h1 + vac v (fun i => evFin F v (x i)) * ih
  have hlc := isLocallyConstant_fin Φ hΦ (fun i => (x i).1)
  have ht : Tendsto (fun S => fun i => hyb S (x i).2 (ξ0 i)) atTop (𝓝 (fun i => (x i).2)) :=
    tendsto_pi_nhds.2 fun i => tendsto_hyb (x i).2 (ξ0 i)
  have hev1 : ∀ᶠ S in atTop, Φ (P S) = Φ x :=
    ht ((hlc.isOpen_fiber (Φ x)).mem_nhds rfl)
  have hxi : ∀ᶠ v in Filter.cofinite, ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (x i).2.2.mono fun v hv => hv
  set S0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F)} with hS0
  have hS0f : S0.Finite := hcof.and hxi
  have hev2 : ∀ᶠ S in atTop, hS0f.toFinset ∪ hT0f.toFinset ≤ S := Filter.eventually_ge_atTop _
  obtain ⟨S, hS1, hS2⟩ := (hev1.and hev2).exists
  have k := key S
  rw [hS1] at k
  have hcS : ∏ v ∈ S, vac v (ζ v) = c := by
    symm
    refine Finset.prod_subset (fun v hv => hS2 (Finset.mem_union_right _ hv)) ?_
    intro v _ hv
    exact hζ1 v (fun h => hv (hT0f.mem_toFinset.2 h))
  have hfp : ∏ᶠ v, vac v (fun i => evFin F v (x i)) = ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    apply hv
    show vac v (fun i => evFin F v (x i)) = 1
    have hn : v ∉ S0 := fun h => hvS (hS2 (Finset.mem_union_left _ (hS0f.mem_toFinset.2 h)))
    have h' := not_not.1 hn
    rw [h'.1, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈
      {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h'.2)]
    rfl
  have hP0 : Φ (P ∅) = f0 (fun i => evI F (x i)) :=
    hf0 (P ∅) (fun i => by simp [P, hyb_empty])
  rw [hcS] at k
  show Φ x = (c⁻¹ • f0) (fun i => evI F (x i)) * ∏ᶠ v, vac v fun i => evFin F v (x i)
  rw [SchwartzMap.smul_apply, smul_eq_mul, hfp, ← hP0, mul_assoc, ← k, mul_comm (Φ x), ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.PureGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzPointValuesAdmitted
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU.PointVal

theorem adelicSchwartz_pointValues_admitted_alt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], (∀ x : κ → AF F, (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ) ∧ (∃ φ ∈ schA F κ, φ 0 = 1) ∧ (∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ) ∧ ∀ (w w' : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ), schr ψ w (schr ψ w' φ) = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  intro F _ _ ψ hψ κ _
  have h3 : ∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ := fun w φ hφ => GlobalTheory.ConeMeasV.schr_mem_schA hψ w hφ
  refine ⟨?_, ?_, h3, ?_⟩
  · intro x g _
    refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
    simp [pureA, mul_comm]
  · obtain ⟨φ, hφ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F κ
    have : ∃ ξ : κ → F, φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (by simp [thetaSum, h])
    obtain ⟨ξ, hξ⟩ := this
    refine ⟨(φ (fun i => algebraMap F (AF F) (ξ i)))⁻¹ • schr ψ ((fun i => algebraMap F (AF F) (ξ i)), 0) φ,
      Submodule.smul_mem _ _ (h3 _ φ hφ), ?_⟩
    simp [schr, hξ]
  · intro w w' φ
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
    congr 2
    simp only [add_dotProduct, dotProduct_add]
    have h2 : (2 : AF F) * ⅟(2 : AF F) = 1 := mul_invOf_self 2
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

end GlobalTheory.TowU.PointVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceMemSpanPureTensorsStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartzSpace_mem_span_pureTensors : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    Φ ∈ Submodule.span ℂ {Ψ : (κ → AF F) → ℂ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
      GlobalTheory.RatWeilOp.IsFam φ ∧ Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} := by
  first | exact @GlobalTheory.SchASpan.mem_span_pure | exact GlobalTheory.SchASpan.mem_span_pure | (intros; apply GlobalTheory.SchASpan.mem_span_pure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSplittingsDifferByCharacterStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_splittings_differ_by_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  first | exact @GlobalTheory.HoweD.SplitScalar.splittings_differ_by_character | exact GlobalTheory.HoweD.SplitScalar.splittings_differ_by_character | (intros; apply GlobalTheory.HoweD.SplitScalar.splittings_differ_by_character <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTopVertexClassesLeClassNumberBoundNormPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


set_option maxHeartbeats 2000000 in
theorem finCl_mk_eq_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (a b : GfC V) :
    DoubleCoset.mk (ratFin V) (K.comap (finG V)) a = DoubleCoset.mk (ratFin V) (K.comap (finG V)) b ↔
      (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V a.1) :
        Cl D.sp.cm V.gram K) = DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V b.1) := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    have hγ' : finG V γ ∈ (GQ V).map (Lev.finE V) := hγ
    obtain ⟨γ0, hγ0, e0⟩ := hγ'
    refine ⟨GlobalTheory.DefFree.finU V γ.1, ?_, GlobalTheory.DefFree.finU V k.1, ?_, ?_⟩
    · have : GlobalTheory.DefFree.finU V γ.1 = GlobalTheory.DefFree.finU V γ0 := Subtype.ext e0.symm
      rw [this]
      exact GlobalTheory.DefFree.AdelCls.rat_mem V γ0 hγ0
    · exact Subgroup.mem_subgroupOf.2 hk
    · simp only [Subgroup.coe_mul, map_mul]
  · rintro ⟨q, hq, k, hk, e⟩
    have hq' : q ∈ (GQ V).map (GlobalTheory.DefFree.finU V) := by rw [GlobalTheory.DefFree.AdelCls.map_rat]; exact hq
    obtain ⟨γ0, hγ0, rfl⟩ := hq'
    obtain ⟨γ1, hγ1, e1⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V (GlobalTheory.DefFree.finU V γ0)
    obtain ⟨κ, hκ, e2⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V k
    refine ⟨⟨γ1, hγ1⟩, ?_, ⟨κ, hκ⟩, ?_, ?_⟩
    · refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨γ0, hγ0, ?_⟩)
      exact (congrArg Subtype.val e1).symm
    · refine Subgroup.mem_comap.2 ?_
      have := Subgroup.mem_subgroupOf.1 hk
      rw [← e2] at this
      exact this
    · apply Subtype.ext
      have hx : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GinfC V := by
        rw [← GlobalTheory.DefFree.AdelCls.finU_eq_one_iff, MonoidHom.map_mul, MonoidHom.map_inv, MonoidHom.map_mul, MonoidHom.map_mul,
          e1, e2, e]
        exact inv_mul_cancel _
      have hy : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).inv_mem b.2) ((GfC V).mul_mem ((GfC V).mul_mem hγ1 a.2) hκ)
      exact inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hy hx)

theorem card_finCl_eq (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    Nat.card (FinCl V K) = Nat.card (Cl D.sp.cm V.gram K) := by
  let f : FinCl V K → Cl D.sp.cm V.gram K := Quotient.lift
    (fun x : GfC V => (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V x.1) :
      Cl D.sp.cm V.gram K))
    (fun a b h => (finCl_mk_eq_iff V K a b).1 ((DoubleCoset.eq'').2 h))
  refine Nat.card_eq_of_bijective f ⟨fun c c' h => ?_, fun c => ?_⟩
  · induction c using Quotient.inductionOn with | h a => ?_
    induction c' using Quotient.inductionOn with | h b => ?_
    exact (finCl_mk_eq_iff V K a b).2 h
  · induction c using Quotient.inductionOn with | h x => ?_
    obtain ⟨h, hh, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V x
    exact ⟨DoubleCoset.mk _ _ (⟨h, hh⟩ : GfC V), by
      show (DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V h) : Cl D.sp.cm V.gram K) = _
      rw [e]⟩

theorem card_clPlus_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U →
    (Nat.card G.ClPlus : ℝ) ≤ hBd D (G.V (.top 0)).rank * (Ideal.absNorm G.modul : ℝ) ^ ((G.V (.top 0)).rank ^ 2) := by
  intro D T L sc G U hS
  have h := _root_.GlobalTheory.FrameTransport.finCl_card_le G hS (.top 0) (Nat.zero_le _) G.modul (G.pl.modul_ne_bot sc) G.Kplus le_rfl
  rw [card_finCl_eq] at h
  exact h

end GlobalTheory.ClassCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondingLatticesBlockLattice
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_blockLat : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  intro k k' _ _ _ _ _ _ _ _ j D D₂ _ _ hj cD ϖ ϖ₂ hϖ hϖ₂ e P P₂ hP x
  have hu : valuation k' (j (ϖ : k)) = valuation k' (ϖ₂ : k') := by
    have h1 := isUnif_map hj hϖ
    exact h1.trans hϖ₂.symm
  have hb : ∀ c : D₂, valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k') =
      valuation k' (j (blockUnits ϖ e P (cD c) : kˣ)) := by
    intro c
    by_cases hc : c ∈ P₂
    · have hc' : cD c ∈ P := (hP c).1 hc
      simp only [blockUnits, if_pos hc, if_pos hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
        map_pow, hu]
    · have hc' : cD c ∉ P := fun h => hc ((hP c).2 h)
      simp [blockUnits, hc, hc']
  show (∀ c, valuation k' (j (x (cD c))) ≤ valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k')) ↔
    ∀ d, valuation k (x d) ≤ valuation k ((blockUnits ϖ e P d : kˣ) : k)
  simp only [hb, val_le_iff hj]
  exact ⟨fun h d => by simpa using h (cD.symm d), fun h c => h (cD c)⟩

end GlobalTheory.PureMatch.Transport
end
end

