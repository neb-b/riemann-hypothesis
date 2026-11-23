module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.IdVGen

open GlobalTheory.SemiLocalFrame

theorem exists_gen_semiLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      b⁻¹ * z ∈ semiLoc E v := by
  have hfg : (Submodule.span (semiLoc E v) ((𝔟 : Submodule (𝓞 E) E) : Set E)).FG := by
    obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟
    exact ⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal
    (⟨_, FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (semiLoc E v)⁰ E)).principal
  have hb' : ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      ∃ a : semiLoc E v, a • b = z := fun z => by
    rw [← Submodule.mem_span_singleton, ← hb]
    exact (mem_span_semiLoc_iff v (𝔟 : Submodule (𝓞 E) E) z).symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine h𝔟 (FractionalIdeal.eq_zero_iff.2 fun z hz => ?_)
    obtain ⟨a, ha⟩ := (hb' z).1 ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, by simpa using hz⟩
    rw [← ha, smul_zero]
  refine ⟨b, hb0, fun z => (hb' z).trans ⟨?_, fun h => ⟨⟨_, h⟩, ?_⟩⟩⟩
  · rintro ⟨a, rfl⟩
    have : b⁻¹ * (a • b) = a := by
      change b⁻¹ * ((a : E) * b) = a
      field_simp
    rw [this]; exact a.2
  · change b⁻¹ * z * b = z
    field_simp

theorem exists_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ (∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) * b ∈ 𝔟) ∧
      ∀ c ∈ 𝔟, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∃ o : 𝓞 E,
        algebraMap F E (t : F) * (b⁻¹ * c) = algebraMap (𝓞 E) E o := by
  obtain ⟨b, hb0, hb⟩ := exists_gen_semiLoc v h𝔟
  have hone : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  refine ⟨b, hb0, ?_, fun c hc => ?_⟩
  · obtain ⟨t, ht, h⟩ := (hb b).2 (by rw [inv_mul_cancel₀ hb0]; exact one_mem _)
    exact ⟨t, ht, by rw [← smul_eq]; exact h⟩
  · have h1 := (hb c).1 ⟨1, hone, by rw [map_one, one_smul]; exact hc⟩
    obtain ⟨t, ht, h⟩ := exists_of_mem_semiLoc v h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h
    exact ⟨t, ht, o, by rw [← smul_eq, ho]⟩

variable {D : D7}

theorem inv_mem_integers {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (t : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation D.host.F (t : D.host.F) = 1 := by
    simpa using (v.valuation_eq_one_iff_notMem (K := D.host.F)).2 hv
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : D.host.F)⁻¹)
  have h3 : v.valuation D.host.F (t : D.host.F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

theorem smul_inv_mem {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (t : D.host.F)⁻¹ • α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w ((t : D.host.F)⁻¹ • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => by rw [map_smul, h0 w hw, smul_zero]⟩
  by_cases hw : w = v
  · subst hw
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (inv_mem_integers hv) (hα w)
  · rw [map_smul, h0 w hw, smul_zero]
    exact zero_mem _

theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  have : c • pairA F 0 α = ((c • (0 : Ainf F), c • α) : Ainf F × Af F) := rfl
  rw [this, smul_zero]; rfl

theorem tmul_eq_of_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : F) (hc : c ≠ 0)
    (α : Af F) (z : E) : pairA F 0 α ⊗ₜ[F] z = pairA F 0 (c⁻¹ • α) ⊗ₜ[F] (algebraMap F E c * z) := by
  rw [pairA_smul, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem tmul_eq {v : Pl D} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal) (α : Af D.host.F) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z =
      pairA D.host.F 0 ((t : D.host.F)⁻¹ • α) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) * z) := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  exact tmul_eq_of_ne _ hF α z

theorem gen_mem_idAt {v : Pl D} {α : Af D.host.F} (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z ∈ idAt D (· = v) := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf]
  refine ⟨?_, fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] z = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show evalV D.host.F w.1 α ⊗ₜ[D.host.F] z = 0
    rw [h0 w.1 w.2, TensorProduct.zero_tmul]

theorem gen_mem_intAt {v : Pl D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E o ∈ intAt D (· = v) :=
  ⟨gen_mem_idAt h0 _, AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩⟩

theorem intAt_zero' (v : Pl D) : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (finPart D) a b]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg (finPart D) a]; exact neg_mem ha.2⟩

theorem incA_mul_tmul (y : AF D.host.F) (e z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem idV_gen : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ x : D.host.E, x ≠ 0 ∧
    ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, ⟨t₀, ht₀, hx𝔞⟩, hc⟩ := exists_gen v h𝔞
  refine ⟨x, hx0, fun s => ⟨fun hs => ?_, fun ⟨h1, _⟩ => ?_⟩⟩
  · unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
      obtain ⟨t, ht, o, ho⟩ := hc c hc'
      obtain ⟨h1, h2⟩ := smul_inv_mem ht hα h0
      refine ⟨?_, gen_mem_idAt h0 c⟩
      rw [incA_mul_tmul, tmul_eq ht α (x⁻¹ * c), ho]
      exact gen_mem_intAt h1 h2 o
    | zero => exact ⟨by rw [mul_zero]; exact intAt_zero' v, zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨by rw [mul_add]; exact intAt_add' ha.1 hb.1, add_mem ha.2 hb.2⟩
    | neg a _ ha => exact ⟨by rw [mul_neg]; exact intAt_neg' ha.1, neg_mem ha.2⟩
  · have h3 : incA D x⁻¹ * s ∈ idV (1 : FI D) v := (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 h1
    have key : ∀ y ∈ idV (1 : FI D) v, incA D x * y ∈ idV 𝔞 v := by
      intro y hy
      unfold idV at hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc'
        obtain ⟨h1', h2'⟩ := smul_inv_mem ht₀ hα h0
        apply AddSubgroup.subset_closure
        refine ⟨_, h1', h2', algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o),
          ?_, ?_⟩
        · have := (𝔞 : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx𝔞
          rw [Algebra.smul_def] at this
          have e : algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o) =
              algebraMap (𝓞 D.host.E) D.host.E o * (algebraMap D.host.F D.host.E (t₀ : D.host.F) * x) := by ring
          rw [e]; exact this
        · rw [incA_mul_tmul, tmul_eq ht₀ α]
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul] at this

end GlobalTheory.IdVGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameImageTrivialOffLevelPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.FrameTriv

theorem frame_trivial_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (δ : TC.GA B (B.R.N j)), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ w : HeightOneSpectrum (𝓞 B.fields.E), (w ∈ (B.primes X).vGs ∨ w ∈ I.SQ ∨ (w ∈ (B.primes X).vT u ∧ w ≠ v.1)) →
      ∀ r r', adAt B.host.F w ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
  intro B X I hI _ l Z u a k _ _ _ _ ι p β Q L _ j hj i v hidem g δ hδ w hw r r'
  classical
  have hPr : (B.primes X).Ok := l.pr
  have hv : (p i).v = v.1.under (𝓞 B.host.F) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under (p i) hidem
  have hvT : v.1 ∈ (B.primes X).vT u := v.2
  have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := T_mem_vT hPr u ⟨v.1, hvT⟩
  have hne : w.under (𝓞 B.host.F) ≠ (p i).v := by
    intro hwv
    rw [hv] at hwv
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have h1 : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (w.under (𝓞 B.host.F)).asIdeal := by
        rw [hwv]
        show algebraMap _ (𝓞 B.fields.E) _ ∈ v.1.asIdeal
        rw [map_natCast]
        exact hTv
      have h2 : algebraMap _ (𝓞 B.fields.E) (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ w.asIdeal := h1
      rwa [map_natCast] at h2
    rcases hw with h | h | ⟨h, hwne⟩
    · exact Formalism.L2.Col.T_notMem_vGs hPr u ⟨w, h⟩ hTw
    · have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI h).2
      have e := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) w (hPr.T_prime u)).2 hTw
      refine hg.2.2 ?_
      rw [e]
      exact hI.T_mem u
    · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (D := I.rec7 l Z) hwv with e | e
      · exact hwne e
      · have hT0 : (B.primes X).piT u ≠ 0 := fun h0 => by
          have := hPr.piT_norm u
          rw [h0, zero_mul] at this
          exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
        have a1 : (B.primes X).piT u ∈ v.1.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 hvT
        have a2 : (B.primes X).piT u ∈ w.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 h
        rw [e] at a2
        have a3 : B.fields.conjO ((B.primes X).piT u) ∈ v.1.asIdeal := (Formalism.L2.Col.mem_conjP _ _).1 a2
        obtain ⟨x, y, hxy⟩ := hPr.piT_cop u
        have : (1 : 𝓞 B.fields.E) ∈ v.1.asIdeal := by
          rw [← hxy]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a3)
        exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hb : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ = 1 :=
    GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one (I.rec7 l Z) k (p i) ((I.rec7 l Z).sp.X j) _ (β j i) g _ (rankN (I.rec7 l Z) j hj) δ hδ _ hne
  have hb' : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ⁻¹ = 1 := by
    rw [map_inv, hb, inv_one]
  have h2 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
    have := congrArg (fun x : GL (Fin (B.R.N j)) _ => x.1 r r') hb'
    simp only [Units.val_one, Matrix.one_apply] at this
    exact this
  have h3 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r' - if r = r' then 1 else 0) = 0 := by
    rw [map_sub, h2]
    split_ifs <;> simp
  have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff B.host.F B.host.E _ _).1.1 h3 w rfl
  rw [map_sub, sub_eq_zero] at h4
  rw [h4]
  split_ifs <;> simp

end GlobalTheory.AdForm.FrameTriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameVectorLatticeCriterion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem mulVec_sec_split {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {n : ℕ} (g : Matrix (Fin n) (Fin n) (AE D)) (w : Fin n → k) :
    g *ᵥ (fun i => q.sec (w i)) = fun i => q.sec ((g.map q.pr *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := GlobalTheory.LocMod.PinEx.sec_mul q (q.pr (g i j)) (w j)
  have h2 := q.sec_pr (g i j)
  have h3 : q.e * q.sec (w j) = q.sec (w j) := by
    have := q.sec_pr (q.sec (w j))
    rw [q.pr_sec] at this
    exact this.symm
  rw [← h1, h2, mul_assoc, mul_left_comm, h3]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch


end GlobalTheory.Core.Mi.LatMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOConstMul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatUnitPf

theorem idAt_mul_idOff {D : D7} (P : Pl D → Prop) (a b : AE D) (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) : a * b = 0 := by
  have h1 : a * b ∈ idAt D P := Ideal.mul_mem_right _ _ ha
  have h2 : a * b ∈ idOff D P := Ideal.mul_mem_left _ _ hb
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at h1
  rw [idOff, Ideal.mem_iInf] at h2
  obtain ⟨hinf, hfin⟩ := h1
  rw [RingHom.mem_ker] at hinf
  apply GlobalTheory.LatVac.eq_zero_of_parts
  · exact hinf
  · apply GlobalTheory.SelfDualAt.eq_zero_of_compFin
    intro w
    by_cases hw : P w
    · have := h2 ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this
    · have := hfin ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this

end GlobalTheory.FinPl.FlatUnitPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralEntriesOfCarriesStandardLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KJStdInt

theorem carries_std_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  intro F E _ _ _ _ _ n k hk
  letI : StarRing E := starRingOfComm
  have hm : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F,
      z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
    fun z => Formalism.L2.Col.mem_latS_std z
  have hs : ∀ j : Fin n, (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine (hm _).2 fun i => ?_
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact Subring.zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h1 : (k⁻¹).1 *ᵥ (k.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ∈
        Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hs j
    have h2 := (hm _).1 ((hk _).2 h1) i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hm _).1 ((hk _).1 (hs j)) i
    rwa [Matrix.mulVec_single_one] at h2

end GlobalTheory.KJStdInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFiniteAdeleOfSplitPlaceComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem GlobalTheory.IntPlaces.mem_of_idem_sum {R : Type} [CommRing R] {n : ℕ} (S : Set R) (hS0 : (0 : R) ∈ S)
    (E : Fin n → R) (hEE : ∀ i, E i * E i = E i) (hE : ∀ i j, i ≠ j → E i * E j = 0) (G : Fin n → R → Prop)
    (hint : ∀ i z, z ∈ S ↔ (1 - E i) * z ∈ S ∧ G i z) (hG : ∀ i j z, i ≠ j → G i z → G i ((1 - E j) * z)) :
    ∀ z, (∑ i, E i) * z = z → (∀ i, G i z) → z ∈ S := by
  have key : ∀ s : Finset (Fin n), ∀ z, (∑ i ∈ s, E i) * z = z → (∀ i ∈ s, G i z) → z ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz _
      rw [Finset.sum_empty, zero_mul] at hz
      rw [← hz]
      exact hS0
    | insert a s ha ih =>
      intro z hz hzi
      rw [Finset.sum_insert ha] at hz
      refine (hint a z).2 ⟨?_, hzi a (Finset.mem_insert_self a s)⟩
      have hET : E a * ∑ i ∈ s, E i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hE a i fun h => ha (h ▸ hi)
      have hw : (1 - E a) * z = (∑ i ∈ s, E i) * z := by
        calc (1 - E a) * z = (1 - E a) * ((E a + ∑ i ∈ s, E i) * z) := by rw [hz]
          _ = (∑ i ∈ s, E i) * z := by linear_combination (-z) * hEE a + (-z) * hET
      refine ih _ ?_ fun i hi => ?_
      · linear_combination (-1 : R) * hw + (-z) * hET
      · exact hG i a z (fun h => ha (h ▸ hi)) (hzi i (Finset.mem_insert_of_mem hi))
  exact fun z hz hzi => key Finset.univ z hz fun i _ => hzi i


open GlobalTheory.IdemSupport in
theorem GlobalTheory.IntPlaces.mem_intAf_of_split : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n k _ _ _ _ q P hI hP π' hπ hint z0 hz0 hzi0
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd : ∀ i, IsDelta ((GlobalTheory.StdFrames.toAd D).comp (Formalism.IndefR.Datum.toEAf D)) (P i) (q i).e :=
    fun i => delta_of_isIdemAt hΦ (hI i)
  have horth : ∀ i j, i ≠ j → (q i).e * (q j).e = 0 := by
    intro i j hij
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P i
    · rw [(hd j).2.2 Q (fun h => hij (hP (hQ.symm.trans h))), mul_zero]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hidem : ∀ i, (q i).e * (q i).e = (q i).e := by
    intro i
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul]) fun Q => ?_
    rw [ev_mul]
    by_cases hQ : Q = P i
    · rw [hQ, (hd i).2.1, mul_one]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hpr : ∀ i j, i ≠ j → π' i (Formalism.IndefR.Datum.toEAf D (q j).e) = 0 := by
    intro i j hij
    rw [hπ, ← (q i).pr_sec ((q i).pr (q j).e), (q i).sec_pr, horth i j hij, map_zero]
  refine GlobalTheory.IntPlaces.mem_of_idem_sum (Formalism.L2.Herm.intAf D.host.F D.host.E : Set _) (zero_mem _)
    (fun i => Formalism.IndefR.Datum.toEAf D (q i).e) (fun i => by rw [← RingHom.map_mul, hidem])
    (fun i j hij => by rw [← RingHom.map_mul, horth i j hij, RingHom.map_zero]) (fun i z => π' i z ∈ 𝒪[k i])
    hint (fun i j z hij hz => ?_) z0 (by rw [show (∑ i, Formalism.IndefR.Datum.toEAf D (q i).e) = Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) from
      (map_sum (Formalism.IndefR.Datum.toEAf D).toAddMonoidHom (fun i => (q i).e) Finset.univ).symm]; exact hz0) hzi0
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hpr i j hij, sub_zero, one_mul]
  exact hz
end

