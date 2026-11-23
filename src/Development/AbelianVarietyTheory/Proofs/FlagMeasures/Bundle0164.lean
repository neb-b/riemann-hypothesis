module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IteratedDerivLine
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Jet.Line

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem smooth_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth n ε _ _ ih hc.1) (rdSmooth n ε _ _ ih hc.2.1)

theorem word_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (rdLin n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem word_append (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w v : List (Fin n × Fin n)) :
    Eword ε (w ++ v) f = Eword ε w (Eword ε v f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Eword, ih]

def ZeroJet (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  SmoothOnG ε f ∧ ∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0

theorem one_mem : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]

theorem zeroJet_zero : ZeroJet ε (fun _ => 0) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, fun w => ?_⟩
  cases w with
  | nil => rfl
  | cons p w => rw [Eword_const]

theorem zeroJet_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, ZeroJet ε (F i)) : ZeroJet ε (fun g => ∑ i ∈ s, c i * F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zeroJet_zero
  | insert i s hi ih =>
    have e : (fun g => ∑ j ∈ insert i s, c j * F j g) = fun g => (∑ j ∈ s, c j * F j g) + c i * F i g := by
      funext g; rw [Finset.sum_insert hi, add_comm]
    rw [e]
    refine ⟨smooth_comb _ ih.1 (hF i).1, fun w => ?_⟩
    rw [word_comb _ ih.1 (hF i).1 w 1 one_mem, ih.2, (hF i).2]
    simp

theorem cpart1_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (c • Z) = c.re • cpart1 ε Z + (-c.im) • cpart2 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem cpart2_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (c • Z) = c.re • cpart2 ε Z + c.im • cpart1 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem rd_eq_sum {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    Rd X f g = ∑ p : Fin n × Fin n, X p.1 p.2 * Eab ε p.1 p.2 f g := by
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  have hE : ∀ Z, Ec ε Z f g =
      fderiv ℝ F g (g * cpart1 ε Z) + Complex.I * fderiv ℝ F g (g * cpart2 ε Z) := fun Z => by
    have hc := cpartMem n ε Z
    simp only [Ec, rdExt n ε f F U g _ hU hgU hg hF e hc.1, rdExt n ε f F U g _ hU hgU hg hF e hc.2.1]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Z => Ec ε Z f g
      map_add' := fun Y Z => by
        have h1 : cpart1 ε (Y + Z) = cpart1 ε Y + cpart1 ε Z := by
          simp only [cpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        have h2 : cpart2 ε (Y + Z) = cpart2 ε Y + cpart2 ε Z := by
          simp only [cpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        simp only [hE, h1, h2, Matrix.mul_add, map_add (f := _)]
        ring
      map_smul' := fun c Z => by
        simp only [hE, cpart1_smul, cpart2_smul, Matrix.mul_add, Matrix.mul_smul, map_add (f := _), map_smul,
          RingHom.id_apply, smul_eq_mul, Complex.real_smul]
        apply Complex.ext <;> simp <;> ring }
  have hc := (cpartMem n ε X).2.2.2 hX
  have h0 : Rd X f g = L X := by
    change _ = Ec ε X f g
    rw [hE, hc.1, hc.2, rdExt n ε f F U g _ hU hgU hg hF e hX]
    simp
  have h1 : X = ∑ p : Fin n × Fin n, X p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp
  rw [h0]
  conv_lhs => rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul]
  rfl

theorem zeroJet_rd {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : ZeroJet ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) : ZeroJet ε (Rd X f) := by
  refine ⟨rdSmooth n ε _ _ hf.1 hX, fun w => ?_⟩
  rw [Eword_congr ε (rd_eq_sum hf.1 hX) w 1 one_mem]
  refine (zeroJet_sum Finset.univ (fun p : Fin n × Fin n => X p.1 p.2) (fun p => Eab ε p.1 p.2 f)
    (fun p => ⟨smooth_word hf.1 [p], fun v => ?_⟩)).2 w
  have := hf.2 (v ++ [p])
  rwa [word_append] at this

theorem deriv_line (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => Rd X f (NormedSpace.exp ((t : ℂ) • X)) := by
  funext s
  simp only [Rd, ← oneParam n X s]
  rw [deriv_comp_const_add (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) s 0, add_zero]

theorem iteratedDeriv_line {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (j : ℕ) :
    ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ZeroJet ε f →
      iteratedDeriv j (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = 0 := by
  induction j with
  | zero =>
    intro f hf
    simpa [Eword] using hf.2 []
  | succ j ih =>
    intro f hf
    rw [iteratedDeriv_succ', deriv_line]
    exact ih _ (zeroJet_rd hf hX)

theorem vanish_of_zero_jet : ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → inG ε X → (∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0) → AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) Set.univ → f (NormedSpace.exp X) = 0 := by
  intro n ε f X hf hX hw hA
  have htop : analyticOrderAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun m => ?_
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)).2
      fun i _ => iteratedDeriv_line hX i f ⟨hf, hw⟩
  have h := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.1 htop) (Set.mem_univ 1)
  simpa using h

end GlobalTheory.Jet.Line
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KMapLowestKTypeSubspaceEqScalar
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KMapInto

section
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}

theorem comap_bot_or_top (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (W : Submodule ℂ H) (hW : IsKStableOn ε σ W) :
    (∀ s : S, T s ∈ W → s = 0) ∨ (∀ s : S, T s ∈ W) := by
  obtain ⟨_, hSst, hSirr, _, _⟩ := hS
  have hle : (W.comap T).map S.subtype ≤ S := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hst : IsKStableOn ε σ ((W.comap T).map S.subtype) := by
    rintro g hg _ ⟨s, hs, rfl⟩
    refine ⟨⟨σ g s, hSst g hg s s.2⟩, ?_, rfl⟩
    show T _ ∈ W
    rw [hT g hg s _ rfl]
    exact hW g hg _ hs
  rcases hSirr _ hle hst with h | h
  · left
    intro s hs
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := ⟨s, hs, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  · right
    intro s
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := by
      rw [h]
      exact s.2
    obtain ⟨t, ht, hts⟩ := hmem
    obtain rfl : t = s := Subtype.ext hts
    exact ht

theorem inj_or_zero (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s)) :
    (∀ s : S, T s = 0 → s = 0) ∨ (∀ s : S, T s = 0) := by
  have hbot : IsKStableOn ε σ (⊥ : Submodule ℂ H) := by
    intro g _ v hv
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  simpa only [Submodule.mem_bot] using comap_bot_or_top hS T hT ⊥ hbot

theorem range_isKType (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hinj : ∀ s : S, T s = 0 → s = 0) : IsKTypeOf ε σ Λ (LinearMap.range T) := by
  have hS' := hS
  obtain ⟨hfin, hSst, _, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS'
  have key : ∀ s : S, ∀ t ∈ Kset ε, ∀ c : ℂ, σ t (T s) = c • T s → σ t s = c • (s : H) := by
    intro s t ht c h
    have h2 : T (⟨σ t s, hSst t ht s s.2⟩ - c • s) = 0 := by
      rw [map_sub, map_smul, hT t ht s _ rfl, h, sub_self]
    exact congrArg Subtype.val (sub_eq_zero.mp (hinj _ h2))
  refine ⟨inferInstance, ?_, ?_, ⟨T ⟨v, hvS⟩, ⟨⟨v, hvS⟩, rfl⟩, ?_, ?_⟩, ?_⟩
  · rintro g hg _ ⟨s, rfl⟩
    exact ⟨⟨σ g s, hSst g hg s s.2⟩, hT g hg s _ rfl⟩
  · intro S' hle hst
    rcases comap_bot_or_top hS T hT S' hst with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨s, rfl⟩ := hle hx
      rw [h s hx, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨s, rfl⟩
      exact h s
  · intro h
    exact hv0 (congrArg Subtype.val (hinj _ h))
  · intro θ hθ
    rw [← hT _ hθ ⟨v, hvS⟩ ⟨_, hSst _ hθ v hvS⟩ rfl, ← map_smul]
    exact congrArg T (Subtype.ext (hvw θ hθ))
  · intro μ w hw hw0 hww
    obtain ⟨s, rfl⟩ := hw
    refine hdom μ s s.2 ?_ ?_
    · intro h
      apply hw0
      obtain rfl : s = 0 := Subtype.ext h
      exact map_zero T
    · intro θ hθ
      exact key s _ hθ _ (hww θ hθ)

theorem scalar_of_range_le (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hle : ∀ s, T s ∈ S) : ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  have hS' := hS
  obtain ⟨hfin, _, _, ⟨v, hvS, hv0, _⟩, _⟩ := hS'
  haveI : Nontrivial S := ⟨⟨⟨v, hvS⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (LinearMap.codRestrict S T hle)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hK : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s →
      (T - c • S.subtype) s' = σ k ((T - c • S.subtype) s) := by
    intro k hk s s' hs'
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, map_sub, map_smul,
      hT k hk s s' hs', hs']
  rcases inj_or_zero hS (T - c • S.subtype) hK with h | h
  · exfalso
    have e : T w = c • (w : H) := congrArg Subtype.val hw.apply_eq_smul
    refine hw.2 (h w ?_)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, e, sub_self]
  · intro s
    have hs := h s
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, sub_eq_zero] at hs
    exact hs

end

theorem kMap_lowKSub_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∀ T : lowKSub ε lam σ →ₗ[ℂ] H, (∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s)) → ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  intro n ε lam H _ _ _ σ _ hK T hT
  rcases inj_or_zero hK T hT with h | h
  · refine scalar_of_range_le hK T hT ?_
    intro s
    have hle : LinearMap.range T ≤ lowKSub ε lam σ := le_sSup (range_isKType hK T hT h)
    exact hle ⟨s, rfl⟩
  · exact ⟨0, fun s => by rw [h s, zero_smul]⟩

end GlobalTheory.KMapInto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralCompactLeQuotientMeasureBessel
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.LocEmb

variable {k r : ℕ}

theorem det_ne_zero_of_mem {g : Mat k r} (hg : g ∈ GG k r) : g.det ≠ 0 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH : (Hpk k r).det ≠ 0 := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact hH this.symm

theorem isClosed_GG : IsClosed (GG k r) := by
  show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem continuousOn_inv : ContinuousOn (fun b : Mat k r => b⁻¹) {b | b.det ≠ 0} := by
  have : (fun b : Mat k r => b⁻¹) = fun b => (b.det)⁻¹ • b.adjugate := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ContinuousOn.smul ((continuous_id.matrix_det).continuousOn.inv₀ fun b hb => hb)
    continuous_id.matrix_adjugate.continuousOn

end GlobalTheory.SgInf.LocEmb

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LocEmb
variable {k r : ℕ}

def quotSet (K : Set (Mt k r)) : Set (Mt k r) :=
  (fun p : Mt k r × Mt k r => ((Matrix.of p.1 : Mat k r) * (Matrix.of p.2 : Mat k r)⁻¹ : Mat k r)) '' (K ×ˢ K)

theorem isCompact_quotSet {K : Set (Mt k r)} (hK : IsCompact K)
    (hd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0) : IsCompact (quotSet K) := by
  refine (hK.prod hK).image_of_continuousOn ?_
  have hc1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have hc2' : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  have hc2 : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹) (K ×ˢ K) :=
    continuousOn_inv.comp hc2'.continuousOn fun p hp => hd p.2 hp.2
  exact hc1.continuousOn.mul hc2

end GlobalTheory.SgInf.LocEmb

theorem GlobalTheory.SgInf.lint_compact_le_quot : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r))
    (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS →
    IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F →
    (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  intro k r S μG μS ν K₀ hS hG hSH hU hQ hK₀
  set K : Set (Mt k r) := K₀ ∩ {x | (Matrix.of x : Mat k r) ∈ GG k r} with hKdef
  have hGc : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := LocEmb.isClosed_GG
  have hK : IsCompact K := hK₀.inter_right hGc
  have hKd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0 := fun x hx => LocEmb.det_ne_zero_of_mem hx.2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨μS (LocEmb.quotSet K), (_root_.GlobalTheory.SgInf.haarOn_locFinite_openPos k r S μS hS hSH).1 _ (LocEmb.isCompact_quotSet hK hKd), ?_⟩
  intro F hF hinv

  have hfib : ∀ x : Mt k r, ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
      μS (LocEmb.quotSet K) * F x := by
    intro x
    set A : Set (Mt k r) := {s | (Matrix.of s : Mat k r) ∈ S ∧
      (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K} with hA
    have h1 : ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
        ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := by
      refine lintegral_mono_ae ?_
      have hnull : μS {x | Matrix.of x ∉ S} = 0 := hSH.2.2.1
      filter_upwards [(ae_iff (p := fun s : Mt k r => (Matrix.of s : Mat k r) ∈ S)).2 hnull] with s hs'
      by_cases hsK : (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K
      · rw [Set.indicator_of_mem hsK, Set.indicator_of_mem (show s ∈ A from ⟨hs', hsK⟩)]
        exact le_of_eq (hinv _ hs' x)
      · rw [Set.indicator_of_notMem hsK]; simp
    have h2 : μS A ≤ μS (LocEmb.quotSet K) := by
      rcases A.eq_empty_or_nonempty with hAe | ⟨s₀, hs₀S, hs₀K⟩
      · rw [hAe, measure_empty]; simp
      set t : Mat k r := Matrix.of s₀ with ht
      have htS : t⁻¹ ∈ S := hS.2.2.2.2 _ hs₀S
      have hdx : (Matrix.of x : Mat k r).det ≠ 0 := by
        have := hKd _ hs₀K
        have h' : (Matrix.of (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r) : Mat k r) =
          (Matrix.of s₀ : Mat k r) * Matrix.of x := rfl
        rw [h', Matrix.det_mul] at this
        exact right_ne_zero_of_mul this
      have hsub : A ⊆ rmulM t⁻¹ ⁻¹' LocEmb.quotSet K := by
        intro s ⟨_, hsK⟩
        refine ⟨((fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r),
          (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r)), ⟨hsK, hs₀K⟩, ?_⟩
        show (Matrix.of s : Mat k r) * Matrix.of x * ((Matrix.of s₀ : Mat k r) * Matrix.of x)⁻¹ =
          (Matrix.of s : Mat k r) * t⁻¹
        rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of s : Mat k r),
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdx), Matrix.mul_one]
      calc μS A ≤ μS (rmulM t⁻¹ ⁻¹' LocEmb.quotSet K) := measure_mono hsub
        _ ≤ (μS.map (rmulM t⁻¹)) (LocEmb.quotSet K) :=
          Measure.le_map_apply (continuous_rmulM _).measurable.aemeasurable _
        _ = μS (LocEmb.quotSet K) := by rw [hU.1 _ htS]
    calc _ ≤ ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := h1
      _ ≤ F x * μS A := lintegral_indicator_const_le _ _
      _ ≤ F x * μS (LocEmb.quotSet K) := by gcongr
      _ = μS (LocEmb.quotSet K) * F x := mul_comm _ _
  have hnullG : μG {x | Matrix.of x ∉ GG k r} = 0 := hG.2.2.1
  calc ∫⁻ x in K₀, F x ∂μG = ∫⁻ x, K₀.indicator F x ∂μG :=
        (lintegral_indicator hK₀.isClosed.measurableSet F).symm
    _ ≤ ∫⁻ x, K.indicator F x ∂μG := by
        refine lintegral_mono_ae ?_
        filter_upwards [(ae_iff (p := fun x : Mt k r => (Matrix.of x : Mat k r) ∈ GG k r)).2 hnullG] with x hx'
        by_cases h0 : x ∈ K₀
        · rw [Set.indicator_of_mem h0, Set.indicator_of_mem (show x ∈ K from ⟨h0, hx'⟩)]
        · rw [Set.indicator_of_notMem h0]; simp
    _ = ∫⁻ x, (∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν :=
        hQ _ (hF.indicator hKm)
    _ ≤ ∫⁻ x, μS (LocEmb.quotSet K) * F x ∂ν := lintegral_mono hfib
    _ = μS (LocEmb.quotSet K) * ∫⁻ x, F x ∂ν := lintegral_const_mul _ hF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemExtIdSmulIff
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev.DualIdeal

theorem smul_dual_iff {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] (S : Subring A)
    (L : Submodule S V) (h : V → V → A) (hs : ∀ (a : A) x y, h x (a • y) = a * h x y)
    (hd : ∀ y, y ∈ L ↔ ∀ y' ∈ L, h y' y ∈ S) (t : S) (ht : IsUnit (t : A)) (y : V) :
    y ∈ (Ideal.span {t} : Ideal S) • L ↔ ∀ y' ∈ L, ∃ z ∈ (Ideal.span {t} : Ideal S), (z : A) = h y' y := by
  obtain ⟨u, hu⟩ := ht
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩ y' hy'
    refine ⟨t * ⟨_, (hd x).1 hx y' hy'⟩, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t), ?_⟩
    exact (hs t y' x).symm
  · intro H
    refine ⟨((u⁻¹ : Aˣ) : A) • y, (hd _).2 fun y' hy' => ?_, ?_⟩
    · obtain ⟨z, hz, e⟩ := H y' hy'
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [hs, ← e, Subring.coe_mul, ← hu, mul_comm (w : A), Units.inv_mul_cancel_left]
      exact w.2
    · show (t : A) • _ = y
      rw [← hu, smul_smul, Units.mul_inv, one_smul]

theorem hAf_smul (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I x (a • y) = a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

theorem mem_extId_smul_iff : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → ∀ y : Fin I.n → (I.E ⊗[I.F] Af I.F), y ∈ extId I 𝔞 • I.Lf ↔ ∀ y' ∈ I.Lf, ∃ z ∈ extId I 𝔞, (z : (I.E ⊗[I.F] Af I.F)) = hAf I y' y := by
  intro I 𝔞 h𝔞 y
  obtain ⟨⟨t, ht, e⟩, -⟩ := GlobalTheory.T.integralAdeleIdealOfIdeal_principal_and_inter I 𝔞 h𝔞
  rw [e]
  exact smul_dual_iff (IntAf I.F I.E) I.Lf (hAf I) (hAf_smul I) (_root_.GlobalTheory.AdelicLattice.adelicLattice_selfDual I) t ht y

end GlobalTheory.RowLev.DualIdeal
end

