module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarAdelicUnitaryProductRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdelicHaarProd

theorem haar_prod : ∀ (D : D7) (V : HSp D) (μf : Measure (GfC V)), μf.IsHaarMeasure → ∃ (μR : Measure (GA D V)) (μi : Measure (GinfC V)), μR.IsHaarMeasure ∧ ∀ (S : Set (GinfC V)) (E : Set (GfC V)), μR {h | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = μi S * μf E := by
  intro D V μf hμf
  obtain ⟨hLC, hSC, hT2, hB, hTG, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hi := GlobalTheory.AdelicSplit.isClosed_GinfC' V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  let e := GlobalTheory.AdelicSplit.splitEquiv V
  let μi : Measure (GinfC V) := Measure.haar
  haveI : SFinite μf := inferInstance
  refine ⟨Measure.map e (μi.prod μf), μi, ContinuousMulEquiv.isHaarMeasure_map _ e, fun S E => ?_⟩
  have hset : {h : GA D V | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = e '' (S ×ˢ E) := by
    ext h
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      exact ⟨(a, k), ⟨ha, hk⟩, rfl⟩
    · rintro ⟨p, ⟨ha, hk⟩, rfl⟩
      exact ⟨p.1, ha, p.2, hk, rfl⟩
  rw [hset]
  rw [show (Measure.map e (μi.prod μf)) = Measure.map (e.toHomeomorph.toMeasurableEquiv) (μi.prod μf) from rfl]
  rw [MeasurableEquiv.map_apply]
  rw [show (e.toHomeomorph.toMeasurableEquiv) ⁻¹' (e '' (S ×ˢ E)) = S ×ˢ E from e.toEquiv.preimage_image _]
  exact Measure.prod_prod S E

end GlobalTheory.AdelicHaarProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarFinitePointsFourierJacobiBessel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarExist

theorem haar_exists : ∀ (D : D7) (V : HSp D), (∃ μ : Measure (GfC V), μ.IsHaarMeasure) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∃ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∃ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure := by
  intro D V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨⟨Measure.haar, inferInstance⟩, fun V₀ ρ d => ⟨?_, fun A L o => ?_⟩⟩
  · have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
    have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩
  · have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
    have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩

end GlobalTheory.HaarExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermitianLineVectorPrescribedNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HermLine

abbrev signLine (D : D7) (p q : ℕ) : HSp D :=
  Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral (p + q) (fun i => decide (p ≤ (i : ℕ))) p q

theorem signLine_norm (D : D7) (c : D.host.E) (p q : ℕ) (h : p + q = 1) :
    star (fun _ : Fin (signLine D p q).rank => c) ⬝ᵥ (signLine D p q).gram *ᵥ (fun _ : Fin (signLine D p q).rank => c) =
      (Examples₂.sgn (decide (p ≤ 0)) : D.host.E) * (c * star c) := by
  obtain ⟨i0, hi⟩ : ∃ i0 : Fin (p + q), (i0 : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have huniq : ∀ i : Fin (p + q), i = i0 := fun i => Fin.ext (by omega)
  show ∑ i : Fin (p + q), star c * ∑ j : Fin (p + q), (signLine D p q).gram i j * c = _
  have hsum : ∀ f : Fin (p + q) → D.host.E, ∑ i, f i = f i0 := by
    intro f
    rw [Finset.sum_eq_single i0 (fun b _ hb => absurd (huniq b) hb) (by simp)]
  rw [hsum, hsum, Examples₂.stdSpace_gram_apply, if_pos rfl, hi]
  ring

theorem exists_line_vec (D : D7) (c : D.host.E) (ε : ℤˣ) (hc : c ≠ 0) :
    ∃ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ ∧ L.SigOK ∧
      star ζ ⬝ᵥ L.gram *ᵥ ζ = ((ε : ℤ) : D.host.E) * (c * star c) ∧
      ∀ τ, L.sig τ = if ε = 1 then (1, 0) else (0, 1) := by
  have hcc : c * star c ≠ 0 := mul_ne_zero hc (star_ne_zero.2 hc)
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have hn := signLine_norm D c 1 0 rfl
    simp only [Examples₂.sgn, zero_add, nonpos_iff_eq_zero, one_ne_zero, decide_false, Bool.false_eq_true,
      if_false, one_mul] at hn
    refine ⟨signLine D 1 0, fun _ => c, ⟨rfl, ?_⟩, GlobalTheory.Ker.Inhab.sigOK_std D 1 0, ?_, fun τ => ?_⟩
    · rw [hn]; exact hcc
    · rw [hn]; simp
    · simp; rfl
  · have hn := signLine_norm D c 0 1 rfl
    simp only [Examples₂.sgn, le_refl, decide_true, if_true] at hn
    refine ⟨signLine D 0 1, fun _ => c, ⟨rfl, ?_⟩, GlobalTheory.Ker.Inhab.sigOK_std D 0 1, ?_, fun τ => ?_⟩
    · rw [hn, neg_one_mul]; exact neg_ne_zero.2 hcc
    · rw [hn]; simp
    · rw [if_neg (by decide)]; rfl

end GlobalTheory.HermLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleChangeFinitelyManySplitPlaces
section
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.IdeleChange

open GlobalTheory.FinPl.FrameLat

variable {D : D7}

theorem idAt_le_idOff {x y : Pl D} (hxy : x ≠ y) : idAt D (· = x) ≤ idOff D (· = y) := by
  intro a ha
  unfold idOff
  rw [Submodule.mem_iInf]
  rintro ⟨w, rfl⟩
  exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 ha).2 ⟨w, fun e => hxy e.symm⟩

theorem mul_eq_zero_of_ne {x y : Pl D} (hxy : x ≠ y) {a b : AE D} (ha : a ∈ idAt D (· = x))
    (hb : b ∈ idAt D (· = y)) : a * b = 0 := by
  obtain ⟨⟨ε, -, -, -, h1, h2⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = y)
  have hb' := (h1 b).1 hb
  have ha' := (h2 a).1 (idAt_le_idOff hxy ha)
  calc a * b = a * (ε * b) := by rw [hb']
    _ = (ε * a) * b := by ring
    _ = 0 := by rw [ha', zero_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 2000000 in
theorem exists_change_one (q : SplitPt D k) (h : D.host.E) (hh : h ≠ 0) (hs : star h = h) (m : (AE D)ˣ) :
    ∃ m' : (AE D)ˣ, (∀ x, x ≠ q.v → ∀ a ∈ idAt D (· = x),
        (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧
      ∀ a ∈ idAt D (· = q.v), (m' : AE D) * cA D (m' : AE D) * incA D h * a = a := by
  have ht0 : q.pr (incA D h) ≠ 0 := by
    intro e
    exact hh ((map_eq_zero_iff (q.pr.comp (incA D)) (q.pr.comp (incA D)).injective).1 e)
  obtain ⟨t, ht⟩ : ∃ t : k, t = q.pr (incA D h) := ⟨_, rfl⟩
  rw [← ht] at ht0
  obtain ⟨s, hsdef⟩ : ∃ s : k, s = t⁻¹ := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = q.e + cA D q.e := ⟨_, rfl⟩
  have hf : ∀ b ∈ idAt D (· = q.v), f * b = b := fun b hb => by rw [hfdef]; exact (idem_iff q b).1 hb
  have hfm : f ∈ idAt D (· = q.v) := by rw [hfdef]; exact sum_mem_idAt q
  have hff : f * f = f := hf _ hfm
  have hcf : cA D f = f := by rw [hfdef, map_add (f := _), cA_cA, add_comm]
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hce : cA D q.e * q.e = 0 := cAe_mul_e q
  have hcee : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, q.split.1]
  have hsc : ∀ c, q.sec c * cA D q.e = 0 := fun c => by
    linear_combination (-(cA D q.e)) * e_mul_sec q c + q.sec c * hec
  have hcem : cA D q.e ∈ idAt D (· = q.v) := by rw [← sec_one]; exact csec_mem_idAt (p := q) 1
  obtain ⟨u, hudef⟩ : ∃ u : AE D, u = q.sec s + cA D q.e := ⟨_, rfl⟩
  obtain ⟨u', hu'def⟩ : ∃ u' : AE D, u' = q.sec t + cA D q.e := ⟨_, rfl⟩
  have hu : u ∈ idAt D (· = q.v) := by rw [hudef]; exact add_mem (sec_mem_idAt q _) hcem
  have hu' : u' ∈ idAt D (· = q.v) := by rw [hu'def]; exact add_mem (sec_mem_idAt q _) hcem
  have hcu : cA D u ∈ idAt D (· = q.v) := by
    rw [hudef, map_add (f := _), cA_cA]; exact add_mem (csec_mem_idAt (p := q) _) (e_mem_idAt q)
  have hst : q.sec s * q.sec t = q.e := by rw [← sec_mul, hsdef, inv_mul_cancel₀ ht0, sec_one]
  have huu : u * u' = f := by
    have h1 := hsc s
    have h2 : cA D q.e * q.sec t = 0 := by rw [mul_comm]; exact hsc t
    rw [hudef, hu'def, hfdef]
    linear_combination hst + h1 + h2 + hcee
  have hmm : (m : AE D) * ((m⁻¹ : (AE D)ˣ) : AE D) = 1 := m.mul_inv
  obtain ⟨mi, hmi⟩ : ∃ mi : AE D, mi = ((m⁻¹ : (AE D)ˣ) : AE D) := ⟨_, rfl⟩
  rw [← hmi] at hmm
  obtain ⟨w, hw⟩ : ∃ w : AE D, w = (m : AE D) * (1 - f) + u := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : AE D, w' = mi * (1 - f) + u' := ⟨_, rfl⟩
  have hww : w * w' = 1 := by
    rw [hw, hw']
    linear_combination (1 - f) ^ 2 * hmm + hff - (m : AE D) * hf _ hu' - mi * hf _ hu + huu
  have hcw : cA D w = cA D (m : AE D) * (1 - f) + cA D u := by
    rw [hw, map_add (f := _), map_mul, map_sub, map_one, hcf]
  refine ⟨Units.mkOfMulEqOne w w' hww, fun x hx a ha => ?_, fun a ha => ?_⟩
  · have hfa : f * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hfm ha
    have hua : u * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hu ha
    have hcua : cA D u * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hcu ha
    rw [Units.val_mkOfMulEqOne, hcw, hw]
    constructor
    · linear_combination (-(m : AE D)) * hfa + hua
    · linear_combination (-(cA D (m : AE D))) * hfa + hcua
  · rw [Units.val_mkOfMulEqOne]
    have hb : incA D h * a ∈ idAt D (· = q.v) := Ideal.mul_mem_left _ _ ha
    have hwa : ∀ b ∈ idAt D (· = q.v), w * b = u * b := fun b hb => by
      rw [hw]
      linear_combination (-(m : AE D)) * hf b hb
    have hcwa : ∀ b ∈ idAt D (· = q.v), cA D w * b = cA D u * b := fun b hb => by
      rw [hcw]
      linear_combination (-(cA D (m : AE D))) * hf b hb
    have hc2 : cA D u * (incA D h * a) ∈ idAt D (· = q.v) := Ideal.mul_mem_left _ _ hb
    have hA : q.sec s * incA D h = q.e := by
      rw [sec_mul_right, ← ht, hsdef, inv_mul_cancel₀ ht0, sec_one]
    have hB : cA D (q.sec s) * incA D h = cA D q.e := by
      have e0 : incA D h = cA D (incA D h) := by rw [cA_incA, hs]
      rw [e0, ← map_mul, hA]
    have hC1 : cA D q.e * cA D (q.sec s) = cA D (q.sec s) := by rw [← map_mul, e_mul_sec]
    have hD : q.sec s * q.e = q.sec s := by rw [mul_comm, e_mul_sec]
    have hkey : u * cA D u * incA D h = f := by
      rw [hudef, hfdef, map_add (f := _), cA_cA]
      linear_combination (incA D h) * ((-(q.sec s)) * hC1 + (cA D (q.sec s)) * hsc s + hD + hce + hC1) + hA + hB
    calc w * cA D w * incA D h * a = w * (cA D w * (incA D h * a)) := by ring
      _ = u * (cA D u * (incA D h * a)) := by rw [hcwa _ hb, hwa _ hc2]
      _ = (u * cA D u * incA D h) * a := by ring
      _ = a := by rw [hkey, hf a ha]

theorem exists_change_list {ι : Type} (p : ι → SplitPt D k) (hp : Function.Injective fun i => (p i).v) (h : D.host.E)
    (hh : h ≠ 0) (hs : star h = h) (m : (AE D)ˣ) (l : List ι) :
    ∃ m' : (AE D)ˣ, (∀ x, (∀ i ∈ l, x ≠ (p i).v) → ∀ a ∈ idAt D (· = x),
        (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧
      ∀ i ∈ l, ∀ a ∈ idAt D (· = (p i).v), (m' : AE D) * cA D (m' : AE D) * incA D h * a = a := by
  induction l with
  | nil => exact ⟨m, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ hi => absurd hi List.not_mem_nil⟩
  | cons i l ih =>
    obtain ⟨m₁, hA₁, hB₁⟩ := ih
    obtain ⟨m₂, hA₂, hB₂⟩ := exists_change_one (p i) h hh hs m₁
    refine ⟨m₂, fun x hx a ha => ?_, fun j hj a ha => ?_⟩
    · have e2 := hA₂ x (hx i List.mem_cons_self) a ha
      have e1 := hA₁ x (fun j hj => hx j (List.mem_cons_of_mem _ hj)) a ha
      exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩
    · by_cases e : j = i
      · subst e; exact hB₂ a ha
      · have hj' : j ∈ l := (List.mem_cons.1 hj).resolve_left e
        have hne : (p j).v ≠ (p i).v := fun e' => e (hp e')
        have hb : incA D h * a ∈ idAt D (· = (p j).v) := Ideal.mul_mem_left _ _ ha
        have e1 := (hA₂ _ hne _ hb).2
        have hc : cA D (m₁ : AE D) * (incA D h * a) ∈ idAt D (· = (p j).v) := Ideal.mul_mem_left _ _ hb
        have e2 := (hA₂ _ hne _ hc).1
        calc (m₂ : AE D) * cA D (m₂ : AE D) * incA D h * a = (m₂ : AE D) * (cA D (m₂ : AE D) * (incA D h * a)) := by ring
          _ = (m₁ : AE D) * (cA D (m₁ : AE D) * (incA D h * a)) := by rw [e1, e2]
          _ = (m₁ : AE D) * cA D (m₁ : AE D) * incA D h * a := by ring
          _ = a := hB₁ j hj' a ha

end GlobalTheory.FinPl.IdeleChange


open GlobalTheory.FinPl.IdeleChange in
theorem GlobalTheory.FinPl.exists_idele_change_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ h : D.host.E, h ≠ 0 → star h = h → ∀ m : (AE D)ˣ, ∃ m' : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧ ∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP h hh hs m
  obtain ⟨m', hA, hB⟩ := exists_change_list p hP.inj h hh hs m I
  refine ⟨m', fun x hx a ha => hA x (fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)) a ha, fun x hx a ha => ?_⟩
  obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
  rw [hB i (hP.all i) a ha]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearMapVaryPureTensorFactorSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.VarySplitFactor.exists_linearMap_pure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (Φ₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))), ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → x (.inl v) = Tm (onHalf φ S T BS BT e Φ₀.1) → ∃ T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ] (WO S T → ℂ), T₀ Φ₀ = f ∧ (∀ u, ∃ x' : Place D → WO S T → ℂ, (∀ p, p ≠ .inl v → x' p = x p) ∧ x' (.inl v) = Tm (onHalf φ S T BS BT e u.1) ∧ IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (T₀ u)) ∧ ∀ g h, gAt S (.inl v) g = g → gAt T (.inl v) h = h → ∀ a b, IsDetAt e S g a → IsDetAt e T h b → ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)), u'.1 = linOm v (grpCo φ S BS g) (grpCo φ T BT h) u.1 → om (g, h) (T₀ u) = ((splitFacO χS χT a b : Circle) : ℂ) • T₀ u' := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW _hθ hB hC x f hx v φ e he BS BT Φ₀ Tm hT hxv
  classical
  have hcoord := GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hsplit := GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕
    hW hB hC v e e he.1 he.2.1 (Or.inl rfl) T.rank S.rank (mapCo φ S T BS BT) hcoord.1 Tm hT
  have honHalf : ∀ Φ, onHalf φ S T BS BT e Φ = pull e (mapCo φ S T BS BT) Φ := fun Φ => rfl
  let xf : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →
      Place D → WO S T → ℂ :=
    fun u => Function.update x (.inl v) (Tm (onHalf φ S T BS BT e u.1))
  have hres : ∀ u, IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (xf u) := by
    intro u
    refine ⟨fun p => ?_, ?_⟩
    · by_cases hp : p = .inl v
      · subst hp
        simp only [xf, Function.update_self]
        rw [honHalf]
        exact hsplit.1.mapsTo u.2
      · simp only [xf, Function.update_of_ne hp]
        exact hx.1.1 p
    · apply (hx.1.2.union (Set.finite_singleton (Sum.inl v : Place D))).subset
      intro p hp
      by_cases h : p = .inl v
      · exact Or.inr h
      · left
        simpa [xf, Function.update_of_ne h] using hp
  have hEU := fun u => GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕
    hB hC (xf u) (hres u)
  let F := fun u => (hEU u).exists.choose
  have hF : ∀ u, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (xf u) (F u) :=
    fun u => (hEU u).exists.choose_spec
  have huniq : ∀ y f1 f2, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f1 →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f2 → f1 = f2 := fun y f1 f2 h1 h2 =>
    (GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC y h1.1).unique
      h1 h2
  have hlin := (GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1
  have hscale : ∀ (y z : Place D → WO S T → ℂ) (g : WO S T → ℂ) (q : Place D) (c : ℂ),
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → z p = y p) → z q = c • y q →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • g) := by
    intro y z g q c hy hz hzq
    have := hlin y y z g g q (c - 1) hy hy (fun _ _ => rfl) hz
      (by rw [hzq, sub_smul, one_smul, sub_add_cancel])
    rwa [sub_smul, one_smul, sub_add_cancel] at this
  have hOnAdd : ∀ (Φ Ψ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (Φ + Ψ) = onHalf φ S T BS BT e Φ + onHalf φ S T BS BT e Ψ := by
    intro Φ Ψ
    funext t
    simp only [onHalf, Pi.add_apply]
    split_ifs <;> simp
  have hOnSmul : ∀ (c : ℂ) (Φ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (c • Φ) = c • onHalf φ S T BS BT e Φ := by
    intro c Φ
    funext t
    simp only [onHalf, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  let T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ]
      (WO S T → ℂ) :=
    { toFun := F
      map_add' := by
        intro u u'
        have hz := hlin (xf u) (xf u') (xf (u + u')) (F u) (F u') (.inl v) 1 (hF u) (hF u')
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_add]
            rw [hOnAdd, map_add (f := _), one_smul])
        rw [one_smul] at hz
        exact huniq _ _ _ (hF (u + u')) hz
      map_smul' := by
        intro c u
        have hz := hscale (xf u) (xf (c • u)) (F u) (.inl v) c (hF u)
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_smul]
            rw [hOnSmul, map_smul])
        exact huniq _ _ _ (hF (c • u)) hz }
  have hT₀ : ∀ u, T₀ u = F u := fun u => rfl
  refine ⟨T₀, ?_, fun u => ⟨xf u, fun p hp => by simp only [xf, Function.update_of_ne hp],
    by simp only [xf, Function.update_self], hF u⟩, ?_⟩
  · rw [hT₀]
    have hxx : xf Φ₀ = x := by
      simp only [xf]
      rw [← hxv]
      exact Function.update_eq_self _ _
    exact huniq _ _ _ (hF Φ₀) (hxx ▸ hx)
  · intro g h hg hh a b ha hb u u' hu'
    have laws := GlobalTheory.PlaceComponent.gAt_laws D
    have hgp : ∀ p, p ≠ Sum.inl v → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact ((laws.1 S (.inl v) g).2.2 p hp)
    have hhp : ∀ p, p ≠ Sum.inl v → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact ((laws.1 T (.inl v) h).2.2 p hp)
    have hsupp : ∀ (V : HSp D) (k : GA D V), gAt V (.inl v) k = k → SuppAt e V k := by
      intro V k hk i j
      have hm := (laws.1 V (.inl v) k).1
      rw [hk] at hm
      have key : Formalism.L2.Theta.mt V k - 1 =
          idem D (Sum.inl v) • (Formalism.L2.Theta.mt V k - 1) := by
        conv_lhs => rw [hm]
        rw [smul_sub, sub_smul, one_smul]
        abel
      rw [he.2.1]
      have := congrFun (congrFun key i) j
      rw [Matrix.smul_apply, smul_eq_mul] at this
      exact this.symm
    have hom := GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hC
      (xf u) (F u) (hF u) g h
    have hact := hsplit.2 g h (hsupp S g hg) (hsupp T h hh) a b ha hb
      (grpCo φ S BS g) (grpCo φ T BT h) (hcoord.2 g h) u.1 u.2
    have hz := hscale (xf u') (fun p => om (gAt S p g, gAt T p h) (xf u p)) (F u') (.inl v)
      ((splitFacO χS χT a b : Circle) : ℂ) (hF u')
      (fun p hp => by
        simp only [xf, Function.update_of_ne hp, hgp p hp, hhp p hp]
        have h11 : ((1 : GA D S), (1 : GA D T)) = 1 := rfl
        rw [h11, map_one]; rfl)
      (by
        simp only [xf, Function.update_self, hg, hh]
        rw [honHalf, hact, honHalf, hu'])
    exact huniq _ _ _ hom hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumPartialProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PartialIdemSum

theorem mul_sum_of_isIdemAt {D : D7} {x : AE D} {P : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x P) (S : Finset (Formalism.L2.DIV.Pl D.host.E)) (f : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P' ∈ S, Formalism.L2.NTheta.IsIdemAt (f P') P') :
    x * ∑ P' ∈ S, f P' = if P ∈ S then x else 0 := by
  rw [Finset.mul_sum]
  split_ifs with hP
  · rw [Finset.sum_eq_single P]
    · have h1 := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P) P P hx (hf P hP)).1 rfl
      rw [← h1]; exact hx.1.1
    · intro P' hP' hne
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 (Ne.symm hne)
    · intro h; exact absurd hP h
  · refine Finset.sum_eq_zero fun P' hP' => ?_
    refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 ?_
    rintro rfl; exact hP hP'

theorem sum_mul_sum_of_subset {D : D7} (S S' : Finset (Formalism.L2.DIV.Pl D.host.E)) (f g : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P ∈ S, Formalism.L2.NTheta.IsIdemAt (f P) P) (hg : ∀ P ∈ S', Formalism.L2.NTheta.IsIdemAt (g P) P) (hS : S ⊆ S') :
    (∑ P ∈ S, f P) * ∑ P ∈ S', g P = ∑ P ∈ S, f P := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [mul_sum_of_isIdemAt (hf P hP) S' g hg, if_pos (hS hP)]

end GlobalTheory.PartialIdemSum
end

