module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLiftUniqueAndBaseDatum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLiftUniqueAndBaseDatumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateLift_unique_and_baseDatum : (∀ {D : D7} {G : Type} [Group
    G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field
    Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H) (c' : CoefA (Vc D i)) (c₁'
    : VsV D i D.what₂.LL →ₛₗ[σ] c'.W) (H' : HMod (Bridge.Gf (Vc D i) → c'.W)) (j'
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H'.H), IsConjForms R i σ (c0L i) c c₁ H j → IsConjForms R i σ (c0L
    i) c' c₁' H' j' → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) →
    ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D
    i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP
    : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (ω'
    : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀' f' : WO (Vc D
    i) (Wc D i) → ℂ) (B' : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io'
    : LowT (R.MW i σ) →ₗ[ℂ] c'.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP'
    : LinearMap.range (c'.ext ∘ₗ H'.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → LiftData R i σ μ' η' c' H' ω' f₀' f' B' io' thP' → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x v, thP' ((c'.ext
    ∘ₗ H'.e).rangeRestrict (j' x)) v = κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) v) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T
    : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁
    : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i
    A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i
    A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ
    : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW
    i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A :=
    A) σ g • R.gW i σ g y) v) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R
    : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) +
    1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i
    σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O
    i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f
    : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ)
    : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f)) ∧ (∀ {D : D7} {G : Type} [Group
    G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra
    T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw
    : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ
    : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i
    : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O
    : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O
    i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i
    (sg0 D
    A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n
    : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O
    i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k
    : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D
    A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k))) := by
  first | exact @GlobalTheory.GalLift.lift_and_base_five | exact GlobalTheory.GalLift.lift_and_base_five | (intros; apply GlobalTheory.GalLift.lift_and_base_five <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineLatticeLinkOfBlockData
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpLink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cj_cj (τ : E →+* PadicAlgCl l) : cj (cj τ) = τ := by
  ext x; simp [cj, IsCMField.complexConj_apply_apply]

theorem cj_injective : Function.Injective (cj : (E →+* PadicAlgCl l) → (E →+* PadicAlgCl l)) := fun a b h => by
  rw [← cj_cj a, h, cj_cj]


open Classical in
def glue {ι X : Type} [Inhabited X] (inc : ι → (E →+* PadicAlgCl l)) (f g : ι → X) (i : E →+* PadicAlgCl l) : X :=
  if h : ∃ τ, inc τ = i then f h.choose else if h' : ∃ τ, cj (inc τ) = i then g h'.choose else default

theorem glue_inc {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (inc τ) = f τ := by
  have h : ∃ τ', inc τ' = inc τ := ⟨τ, rfl⟩
  rw [glue, dite_eq_left h]
  exact congrArg f (hH.1 h.choose_spec)

theorem glue_cj {ι X : Type} [Inhabited X] {inc : ι → (E →+* PadicAlgCl l)} (hH : IsHalf inc) (f g : ι → X) (τ : ι) :
    glue inc f g (cj (inc τ)) = g τ := by
  have h : ¬ ∃ τ', inc τ' = cj (inc τ) := fun ⟨τ', h'⟩ => hH.2.1 τ τ' h'.symm
  have h' : ∃ τ', cj (inc τ') = cj (inc τ) := ⟨τ, rfl⟩
  rw [glue, dite_eq_right h, dite_eq_left h']
  exact congrArg g (hH.1 (cj_injective h'.choose_spec))

def labels {ι : Type} (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (mu : ι → ℕ → ℕ) :
    Formalism.CohomologicalDescent.WorkedExample.Labels (E →+* PadicAlgCl l) P.Nr where
  cc := cj
  Φ := Set.range inc
  U := glue inc (fun τ a => W.U P τ (a : ℕ)) (fun τ a => (h0 P : ℤ) - W.U P τ ((Fin.rev a : Fin P.Nr) : ℕ))
  U' := glue inc (fun τ a => Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) (a : ℕ))
    (fun τ a => (h0 P : ℤ) - Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ) ((Fin.rev a : Fin P.Nr) : ℕ))
  bot := glue inc (fun τ => W.bot P τ) (fun τ => (h0 P : ℤ) - (W.bot P τ + (P.t : ℤ) - 1))

theorem U_block {ι : Type} {P : Par} {W : Wts ι} (hOk : W.Ok P) (τ : ι) (s : ℕ) (hs : s < P.t) :
    W.U P τ (kc P + W.j τ + P.t - 1 - s) = W.bot P τ + (s : ℤ) := by
  have h1 := hOk.block τ (kc P + W.j τ + P.t - 1 - s) (by omega) (by omega)
  have h2 := hOk.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)
  simp only [Wts.bot, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, h1, h2]
  omega

theorem latticeLink_of_blockFor : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (ι : Type) (inc : ι → (E →+* PadicAlgCl l)), IsHalf inc → ∃ (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool), ∀ (P : Par) (W : Wts ι), P.Hyp → W.Ok P → (∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)) → ∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc ι inc hH
  obtain ⟨σ, hσF, hσc⟩ := _root_.GlobalTheory.FrobEmb.exists_frobPerm E l hdisc
  choose hf hb using hH.2.2
  classical
  set fr : ℕ → ι → ι := fun _ τ => hf (σ (inc τ)) with hfr
  set cjj : ℕ → ι → Bool := fun _ τ => decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) with hcjj
  refine ⟨fr, cjj, ?_⟩
  intro P W hP hOk hbox mu hLk hBF τ
  obtain ⟨ep, J, bot, hep, hBP, hJ⟩ := hBF
  have hall : ∀ i, ∃ τ', i = ep (inc τ') ∨ i = ep (cj (inc τ')) := by
    intro i
    rcases hep with rfl | rfl
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inl h⟩
      · exact ⟨hf i, Or.inr h⟩
    · rcases hb i with h | h
      · exact ⟨hf i, Or.inr (by rw [cj_cj]; exact h)⟩
      · exact ⟨hf i, Or.inl h⟩
  have hUN : ∀ τ' (a : Fin P.Nr), 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ∧
      Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') a ≤ (h0 P : ℤ) := by
    intro τ' a
    have h1 := ((hLk τ').2.2.1 a).2
    have ha := a.2
    have h2 := hbox τ' 0 (by omega)
    simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN] at h2 ⊢
    constructor <;> omega
  have hJb : ∀ i a, 0 ≤ J i a ∧ J i a ≤ (h0 P : ℤ) := by
    intro i a
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [((hJ τ').1 a).1]; exact hUN τ' a
    · rw [((hJ τ').1 a).2]
      have := hUN τ' (Fin.rev a)
      constructor <;> linarith [this.1, this.2]
  have hbb : ∀ i (s : Fin P.t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h0 P : ℤ) := by
    intro i s
    have hs := s.2
    have hr := hOk.what₂
    obtain ⟨τ', h | h⟩ := hall i <;> subst h
    · rw [(hJ τ').2.1]
      have e := U_block hOk τ' s hs
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - s) (by have := hr τ'; omega)
      rw [e] at b; exact b
    · rw [(hJ τ').2.2]
      have e := U_block hOk τ' (P.t - 1 - s) (by omega)
      have b := hbox τ' (kc P + W.j τ' + P.t - 1 - (P.t - 1 - s)) (by have := hr τ'; omega)
      rw [e] at b
      constructor <;> omega
  obtain ⟨O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, kap, ζ, em, jj, hN⟩ :=
    _root_.GlobalTheory.WachBlock.wach_inputs hBS E Ω l hl2 hdisc σ hσF P.Nr P.t (h0 P) J bot hJb hbb hBP
  have hn : kc P + (reFr W fr cjj).j τ + P.t + (reFr W fr cjj).q τ = P.Nr := hOk.what₂ τ
  unfold LatticeLink
  rw [hn]
  refine ⟨E →+* PadicAlgCl l, inferInstance, σ, ‹_›, O', F, L', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, I, ‹_›, Wl, u, c,
    labels inc P W mu, fun _ => 1 - (P.Nr : ℤ), ep, J, bot, kap, ζ, em, jj, inc, ?_⟩
  refine ⟨?_, ?_, ?_, hN, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨cj_cj, fun i => hσc i, ?_, ?_, ?_, ?_⟩
    · intro i
      rcases hb i with h | h
      · exact Or.inl ⟨hf i, h.symm⟩
      · exact Or.inr ⟨hf i, by show inc (hf i) = cj i; rw [← cj_cj (inc (hf i)), ← h]⟩
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj, Fin.rev_rev, sub_sub_cancel]
    · intro i
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH, glue_cj hH]
      · simp only [labels, glue_inc hH, glue_cj hH, cj_cj]; ring
  ·
    rintro _ ⟨τ', rfl⟩
    have hr := hOk.what₂ τ'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := hOk.anti τ' a b hab'.le b.2
      simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro a b hab
      have hab' : (a : ℕ) < b := hab
      have h1 := (hLk τ').1 hab.le
      simp only [Formalism.CohomologicalDescent.LD.res] at h1
      simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      omega
    · intro s
      have hs := s.2
      refine ⟨⟨kc P + W.j τ' + P.t - 1 - s, by omega⟩, ?_⟩
      simp only [labels, glue_inc hH]
      exact U_block hOk τ' s hs
    · have hp := congrArg (Polynomial.map (ZMod.castHom (dvd_refl l) F)) (hLk τ').2.2.2
      simp only [Polynomial.map_prod, Polynomial.map_add (f := _), Polynomial.map_X, Polynomial.map_C] at hp
      simp only [map_intCast] at hp
      have e1 : ∀ a : Fin P.Nr, (((W.U P τ' (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((W.lam τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      have e2 : ∀ a : Fin P.Nr, (((Formalism.CohomologicalDescent.UnitNormBounds.UN P.Nr (mu τ') (a : ℕ) + (1 - (P.Nr : ℤ)) : ℤ) : F)) =
          ((((mu τ' a : ℤ) - ((a : ℕ) : ℤ) : ℤ)) : F) := by
        intro a; congr 1; simp only [Formalism.CohomologicalDescent.UnitNormBounds.UN]; ring
      simp only [labels, glue_inc hH, e1, e2]
      exact hp
  ·
    refine ⟨hep, fun i => ?_, fun i => ?_⟩
    · funext a
      obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact ((hJ τ').1 a).1
      · simp only [labels, glue_cj hH]; exact ((hJ τ').1 a).2
    · obtain ⟨τ', rfl | rfl⟩ : ∃ τ', i = inc τ' ∨ i = cj (inc τ') := ⟨hf i, hb i⟩
      · simp only [labels, glue_inc hH]; exact (hJ τ').2.1
      · simp only [labels, glue_cj hH]; exact (hJ τ').2.2
  · intro τ' a
    simp only [labels, glue_inc hH]
    rfl
  · intro τ'
    simp only [labels, glue_inc hH]
    rfl
  ·
    show σ (inc τ) = if decide (σ (inc τ) ≠ inc (hf (σ (inc τ)))) = true then cj (inc (hf (σ (inc τ))))
      else inc (hf (σ (inc τ)))
    by_cases h : σ (inc τ) = inc (hf (σ (inc τ)))
    · rw [decide_eq_false (not_not.mpr h), if_neg Bool.false_ne_true]; exact h
    · rcases hb (σ (inc τ)) with h' | h'
      · exact absurd h' h
      · rw [decide_eq_true h, if_pos rfl]; exact h'
  · intro a a' haa'
    obtain rfl : a = a' := Fin.ext haa'
    simp only [labels, glue_inc hH, Formalism.CohomologicalDescent.UnitNormBounds.UN, Formalism.CohomologicalDescent.LD.res]
  · have hs := (hLk τ).2.1
    have h2 : (∑ a : Fin P.Nr, (mu τ a : ℤ)) = ∑ a : Fin P.Nr, (W.lam τ a : ℤ) := by exact_mod_cast hs
    simp only [labels, glue_inc hH, Wts.U, Formalism.CohomologicalDescent.UnitNormBounds.UN, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith [h2]

end GlobalTheory.ExpLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumPhiASplitPlaceTransportEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem corr_smul_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := latCorr_smul hj cD h c c₂ hc

theorem corr_dual_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := GlobalTheory.T.dualLattice_correspondingLattices hj cD h

theorem primFrame_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff hj rA cD h Z

theorem corr_blockLat_of (hj : IsLocIso j) (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂)
    (e : ℕ) (P : Finset D) (P₂ : Finset D₂) (hP : ∀ c, c ∈ P₂ ↔ cD c ∈ P) :
    LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := _root_.GlobalTheory.PureMatch.Transport.latCorr_blockLat hj cD hϖ hϖ₂ e P P₂ hP

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem fFun_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z :=
  _root_.GlobalTheory.PureMatch.Transport.fFun_trM hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν Ψ Z

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem latCorr_latA (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ) :
    LatCorr j cD (latA ϖ e Λ) (latA ϖ₂ e Λ₂) := by
  refine corr_smul_of hj cD (corr_dual_of hj cD h) _ _ ?_
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, h1]

theorem trM_mem_matLat (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
  rw [mem_matLat, mem_matLat]
  refine ⟨fun H a => ?_, fun H r => (h (Z.row (rA r))).2 (H _)⟩
  obtain ⟨r, rfl⟩ := rA.surjective a
  exact (h (Z.row (rA r))).1 (H r)

theorem hasDepth_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ)
    (hϖ₂ : IsUnif ϖ₂) (e : ℕ) (Ξ : Matrix A D k → ℂ) (hΞ : HasDepth ϖ e Λ Ξ) :
    HasDepth ϖ₂ e Λ₂ (fun Y => Ξ (trM j.symm rA.symm cD.symm Y)) := by
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  have hs : LatCorr j cD (ϖ ^ e • Λ) (ϖ₂ ^ e • Λ₂) := corr_smul_of hj cD h _ _ (by
    simp only [Units.val_pow_eq_pow_val, map_pow]; rw [h1])
  refine ⟨fun Y hY => hΞ.1 _ fun hZ => hY ?_, fun Y W hW => ?_⟩
  · rw [← trM_trM_symm j rA cD Y]; exact (trM_mem_matLat rA cD h _).2 hZ
  · have hW' : trM j.symm rA.symm cD.symm W ∈ matLat A (ϖ ^ e • Λ) := by
      rw [← trM_mem_matLat rA cD hs, trM_trM_symm]; exact hW
    show Ξ (trM j.symm rA.symm cD.symm (Y + W)) = Ξ (trM j.symm rA.symm cD.symm Y)
    rw [show trM j.symm rA.symm cD.symm (Y + W) = trM j.symm rA.symm cD.symm Y + trM j.symm rA.symm cD.symm W by
      ext r c; simp]
    exact hΞ.2 _ _ hW'

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem phiA_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂)
    (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    phiA μ₂ σ₂ ν₂ ϖ₂ e Λ₂ Ψ (trM j rA cD Z) =
      phiA (pullMeas hj rA' μ₂) σ ν ϖ e Λ (fun Y => Ψ (trM j rA' cD Y)) Z := by
  classical
  unfold phiA
  rw [primFrame_corr hj rA cD (latCorr_latA hj cD h hϖ hϖ₂ e), fFun_corr hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν]

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch
open GlobalTheory.PureMatch.Transport GlobalTheory.FlipMatch

theorem mem_one_block_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T)
    (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) (c : (locGrid G t w).Cols i j) :
    c ∈ Assignment.one.block _ _ ↔ GlobalTheory.SquareFlipReach.colE t w e c ∈ blockV e := by
  rcases c with c | c
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]

theorem phiA_transport_split_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  intro D T L sc G μ₀ hL t i j e w hw v hv τ hτ n
  subst hτ
  have hjj := isLocIso_complEquiv τ hv
  have hO := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  have hO' := isOpen_map_invT hO.1 hO.2
  haveI := isHaarMeasure_haarVol hO'.1 hO'.2
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  have hc := corr_blockLat_of hjj (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hϖv (isUnif_unifAt _) n (blockV e)
      (Assignment.one.block _ _) (mem_one_block_iff t _ e)
  refine ⟨pullMeas hjj (rowB t (splitPrime τ) i j)
      (haarVol ((givenLevel G t (splitPrime τ) ((i : ℕ), (j : ℕ))).map invT)), inferInstance,
    (Equiv.sumCongr (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j).symm (rowB t (splitPrime τ) i j).symm).trans
      ((stdSplit ((locGrid G t (splitPrime τ)).rank_square i j)).trans (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e)),
    fun Ψ Z => ?_, fun Ξ hΞ => ?_⟩
  · exact phiA_trM hjj (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j) (rowB t (splitPrime τ) i j)
      (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) _ _ _ (fun s => by simp) _ _ (fun x => rfl) hϖv
      (isUnif_unifAt _) n hc Ψ Z
  · exact ⟨_, hasDepth_trM hjj (rowB t (splitPrime τ) i j) (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hc hϖv
      (isUnif_unifAt _) n Ξ hΞ, fun Y => by
        show Ξ (trM _ _ _ (trM (GlobalTheory.LFun.SplitTie.complEquiv τ hv) (rowB t (splitPrime τ) i j)
          (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) Y)) = Ξ Y
        rw [trM_symm_trM]⟩

end GlobalTheory.PureMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegralStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  first | exact @GlobalTheory.BetaInvIntegral.betaH_inv_integral | exact GlobalTheory.BetaInvIntegral.betaH_inv_integral | (intros; apply GlobalTheory.BetaInvIntegral.betaH_inv_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDiagonalIntegralMemSchwartzBruhatStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDiagonalIntegral_mem_schwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ₀ ∈ SB (κ ⊕ κ → Fv F v), ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
      (∀ w, diagW ψ μ Φ₀ w = U.indicator (fun _ => c) w) →
    ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
  first | exact @GlobalTheory.DiagWSB.diagW_mem_SB | exact GlobalTheory.DiagWSB.diagW_mem_SB | (intros; apply GlobalTheory.DiagWSB.diagW_mem_SB <;> assumption)
end

