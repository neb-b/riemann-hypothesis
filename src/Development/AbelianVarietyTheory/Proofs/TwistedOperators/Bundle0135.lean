module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingFiniteAdeleOfSPartAndIntegralPart
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuLR

open Filter
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem cofinite_le_principal_compl :
    cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff]; exact S.finite_toSet.compl_mem_cofinite


open Classical in
def jSP : SPart F S × OPart F S →
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  fun p => ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v), by
    rw [eventually_principal]
    intro v hv
    have hv' : v ∉ S := hv
    simp only [dif_neg hv']
    exact (p.2 ⟨v, hv'⟩).2⟩

def jSPinv : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] →
    SPart F S × OPart F S :=
  fun x => (fun v => x v.1, fun v => ⟨x v.1, x.2 v.2⟩)

theorem continuous_jSP : Continuous (jSP F S) := by
  rw [RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff]
  refine continuous_pi fun v => ?_
  by_cases h : v ∈ S
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => p.1 ⟨v, h⟩ := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact (continuous_apply _).comp continuous_fst
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)

theorem continuous_jSPinv : Continuous (jSPinv F S) := by
  have hc : Continuous (fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] =>
      (x : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F)) :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous
  refine Continuous.prodMk (continuous_pi fun v => (continuous_apply v.1).comp hc)
    (continuous_pi fun v => ((continuous_apply v.1).comp hc).subtype_mk _)

def jSPHomeo : SPart F S × OPart F S ≃ₜ
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] where
  toFun := jSP F S
  invFun := jSPinv F S
  left_inv p := by
    ext v
    · simp [jSP, jSPinv, v.2]
    · simp [jSP, jSPinv, v.2]
  right_inv x := by
    ext v
    by_cases h : v ∈ S <;> simp [jSP, jSPinv, h]
  continuous_toFun := continuous_jSP F S
  continuous_invFun := continuous_jSPinv F S

theorem jS_eq_comp : (jS F S : SPart F S × OPart F S → Af F) =
    RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl F S) ∘ jSP F S := by
  funext p; rfl

theorem isOpenEmbedding_jS : IsOpenEmbedding (jS F S) := by
  rw [jS_eq_comp]
  exact (RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F)) (cofinite_le_principal_compl F S)).comp
    (jSPHomeo F S).isOpenEmbedding

end GlobalTheory.ModuLR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.StepVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def gLoc {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (PP : Formalism.L2.DIV.Pl D.host.E)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero a y ∧ ∃ g : GL (Fin a) (Formalism.L2.DIV.kP PP),
      ((g : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr g ∈ H then
    ((c ⟨Formalism.L2.DIV.upperLeftBlock L.hr h.2.choose, h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ i ∈ Finset.range L.s,
        ((L.cg (i + 1) PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) h.2.choose) : ℂˣ) : ℂ)) *
      (((χ (Matrix.GeneralLinearGroup.det h.2.choose)) : ℂˣ) : ℂ)⁻¹
  else 0


open Classical in
def qLoc {a b : ℕ} (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero r y ∧ IsUnit (topL r y).det then ((ξ h.2.unit : ℂˣ) : ℂ) else 0

def IsRedMap {v : FinPl D} (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP) : Prop :=
  Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧
    (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧
    ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩


open Classical in
def viaRed {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ} (r : v.adicCompletionIntegers D.host.F →+* k)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) (Y : Matrix (Fin b) (Fin a) (Fv D.host.F v)) : ℂ :=
  if h : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F then ω (Matrix.of fun i j => r ⟨Y i j, h i j⟩) else 0


open Classical in
def locFn (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (PP : Formalism.L2.DIV.Pl D.host.E) (ω : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) : WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then ω (redM PP (frMapO S T βS βT x)) else 0

end GlobalTheory.StepVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrix
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCoordSB

theorem eventually_pow_nsmul_mem {K M : Type} [NormedField K] [AddCommGroup M] [Module K M] [TopologicalSpace M]
    [ContinuousSMul K M] {p : ℕ} (hp : ‖(p : K)‖ < 1) {C U : Set M} (hC : IsCompact C) (hU : U ∈ 𝓝 (0 : M)) :
    ∀ᶠ n in Filter.atTop, ∀ x ∈ C, p ^ n • x ∈ U := by
  have hsmul : ∀ᶠ c in 𝓝 (0 : K), ∀ x ∈ C, c • x ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    have ht : Filter.Tendsto (fun z : K × M => z.1 • z.2) (𝓝 ((0 : K), y)) (𝓝 (0 : M)) := (continuous_smul (M := K) (X := M)).tendsto' _ _ (by simp)
    exact ht hU
  have hpow : Filter.Tendsto (fun n : ℕ => (p : K) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  filter_upwards [hpow.eventually hsmul] with n hn x hx
  have hx' := hn x hx
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hx'

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have hloc : ∀ y, ∀ᶠ z in 𝓝 y, Φ z = Φ y := fun y => (h1.isOpen_fiber (Φ y)).mem_nhds rfl
  have hK : IsCompact (tsupport Φ) := h2
  have hA : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Filter.Tendsto (fun z : M × M => z.2 + z.1) (𝓝 ((0 : M), y)) (𝓝 y) := (show Continuous fun z : M × M => z.2 + z.1 from continuous_snd.add continuous_fst).tendsto' _ _ (by simp)
    have hs : Filter.Tendsto (fun z : M × M => z.2) (𝓝 ((0 : M), y)) (𝓝 y) := continuous_snd.tendsto _
    filter_upwards [hc.eventually (hloc y), hs.eventually (hloc y)] with z h h'
    exact h.trans h'.symm
  have hB : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x - u) = Φ x := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Filter.Tendsto (fun z : M × M => z.2 - z.1) (𝓝 ((0 : M), y)) (𝓝 y) := (show Continuous fun z : M × M => z.2 - z.1 from continuous_snd.sub continuous_fst).tendsto' _ _ (by simp)
    have hs : Filter.Tendsto (fun z : M × M => z.2) (𝓝 ((0 : M), y)) (𝓝 y) := continuous_snd.tendsto _
    filter_upwards [hc.eventually (hloc y), hs.eventually (hloc y)] with z h h'
    exact h.trans h'.symm
  filter_upwards [hA, hB] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ
  · exact hu x hx
  by_cases hxu : x + u ∈ tsupport Φ
  · simpa using (hu' (x + u) hxu).symm
  have h0 : Φ x = 0 := by
    by_contra h
    exact hx (subset_tsupport Φ h)
  have h0' : Φ (x + u) = 0 := by
    by_contra h
    exact hxu (subset_tsupport Φ h)
  rw [h0, h0']

variable {D : D7} {m n : ℕ} {a : AE D}

theorem isHalf_add {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x + y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_sub {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x - y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_nsmul {x : Mx D m n} (hx : IsHalf a x) (k : ℕ) : IsHalf a (k • x) := by
  induction k with
  | zero =>
    unfold IsHalf
    intro i j
    simp
  | succ k ih =>
    rw [succ_nsmul]
    exact isHalf_add ih hx

theorem isSBHalf_iff_pull : ∀ (D : D7) (S T : HSp D) (v : FinPl D) (m n : ℕ) (a : AE D) (Λ : AddSubgroup (WO S T)) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a Λ κ → (∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsSBHalf a Λ (pull a κ Φ)) ∧ ∀ Ψ, IsSBHalf a Λ Ψ → ∃ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), Ψ = pull a κ Φ := by
  intro D S T v m n a Λ κ hκ
  unfold IsCoord at hκ
  obtain ⟨hadd, hbij, hopen, hcpt⟩ := hκ
  have h0 : κ 0 = 0 := by simpa using hadd 0 0
  have hns : ∀ (k : ℕ) (t : WO S T), κ (k • t) = k • κ t := by
    intro k t
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hadd, ih]
  have hz : IsHalf a (0 : WO S T) := by
    unfold IsHalf
    intro i j
    simp
  have hO0 : κ '' {t | t ∈ Λ ∧ IsHalf a t} ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
    hopen.mem_nhds ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩
  refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
  ·
    obtain ⟨p, hp0, hp⟩ : ∃ p : ℕ, 0 < p ∧ ‖(p : Fv D.host.F v)‖ < 1 := by
      refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero ?_, ?_⟩
      · rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact v.ne_bot
      · have h := (NumberField.FinitePlace.norm_lt_one_iff_mem D.host.F v
          ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.F)).mpr (Ideal.absNorm_mem v.asIdeal)
        simpa using h
    have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
    obtain ⟨h1, h2⟩ := hΦ'
    have hU := eventually_invariant h1 h2
    have E1 := eventually_pow_nsmul_mem hp hcpt hU
    have E2 := eventually_pow_nsmul_mem hp h2 hO0
    obtain ⟨N, hN1, hN2⟩ := (E1.and E2).exists
    unfold IsSBHalf
    refine ⟨fun t ht => ?_, p ^ N, pow_pos hp0 N, fun u hu hhu t => ?_, fun t ht => ?_⟩
    · by_contra hh
      exact ht (by simp [pull, hh])
    · by_cases htH : IsHalf a t
      · have h' : IsHalf a (t + (p ^ N) • u) := isHalf_add htH (isHalf_nsmul hhu _)
        have hm : ∀ x, Φ (x + (p ^ N) • κ u) = Φ x := hN1 (κ u) ⟨u, ⟨hu, hhu⟩, rfl⟩
        simp only [pull, if_pos htH, if_pos h']
        rw [hadd, hns]
        exact hm (κ t)
      · have h' : ¬ IsHalf a (t + (p ^ N) • u) := by
          intro hc
          apply htH
          have hc' := isHalf_sub hc (isHalf_nsmul hhu (p ^ N))
          simpa using hc'
        simp only [pull, if_neg htH, if_neg h']
    · have htH : IsHalf a t := by
        by_contra hh
        exact ht (by simp [pull, hh])
      have hΦt : Φ (κ t) ≠ 0 := by simpa [pull, htH] using ht
      obtain ⟨s, ⟨hsΛ, hsH⟩, hs⟩ := hN2 (κ t) (subset_tsupport Φ hΦt)
      have hk : IsHalf a ((p ^ N) • t) := isHalf_nsmul htH _
      have hst : s = (p ^ N) • t := hbij.injOn hsH hk (by rw [hs, hns])
      rw [← hst]
      exact hsΛ
  · unfold IsSBHalf at hΨ
    obtain ⟨hsupp, k, hk0, hinv, hΛ⟩ := hΨ

    obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin m) (Fin n) (Fv D.host.F v) → WO S T,
        ∀ x, IsHalf a (g x) ∧ κ (g x) = x :=
      ⟨Function.invFunOn κ {t | IsHalf a t}, fun x =>
        ⟨Function.invFunOn_mem (hbij.surjOn (Set.mem_univ x)), Function.invFunOn_eq (hbij.surjOn (Set.mem_univ x))⟩⟩
    have hgk : ∀ t, IsHalf a t → g (κ t) = t := fun t ht => hbij.injOn (hg _).1 ht (hg _).2
    have : CharZero (Fv D.host.F v) :=
      charZero_of_injective_algebraMap (R := D.host.F) (algebraMap D.host.F (Fv D.host.F v)).injective
    have hkF : ((k : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    refine ⟨fun x => Ψ (g x), ?_, ?_⟩
    · show IsLocallyConstant (fun x => Ψ (g x)) ∧ HasCompactSupport (fun x => Ψ (g x))
      refine ⟨?_, ?_⟩
      · rw [IsLocallyConstant.iff_eventually_eq]
        intro x
        have hW : (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v) • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
          (isOpenMap_smul₀ hkF _ hopen).mem_nhds ⟨0, ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩, smul_zero _⟩
        have hc : Filter.Tendsto (fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x) (𝓝 x) (𝓝 0) :=
          (show Continuous fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x from
            continuous_id.sub continuous_const).tendsto' _ _ (by simp)
        filter_upwards [hc.eventually_mem hW] with y hy
        obtain ⟨w, ⟨u, ⟨huΛ, huH⟩, rfl⟩, hw0⟩ := hy
        have hw : (k : Fv D.host.F v) • κ u = y - x := hw0
        have hy' : y = x + κ (k • u) := by
          rw [hns, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), hw]
          abel
        have hgy : g y = g x + k • u := by
          rw [hy']
          apply hbij.injOn (hg _).1 (isHalf_add (hg x).1 (isHalf_nsmul huH k))
          rw [(hg _).2, hadd, (hg x).2]
        show Ψ (g y) = Ψ (g x)
        rw [hgy]
        exact hinv u huΛ huH (g x)
      · refine HasCompactSupport.intro
          (K := (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v)⁻¹ • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}))
          (hcpt.image (continuous_const_smul _)) ?_
        intro x hx
        by_contra hne
        apply hx
        have hm := hΛ (g x) hne
        have hmem : κ (k • g x) ∈ κ '' {t | t ∈ Λ ∧ IsHalf a t} := ⟨_, ⟨hm, isHalf_nsmul (hg x).1 k⟩, rfl⟩
        rw [hns, (hg x).2, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v)] at hmem
        exact ⟨_, hmem, inv_smul_smul₀ hkF x⟩
    · funext t
      by_cases ht : IsHalf a t
      · simp only [pull, if_pos ht]
        rw [hgk t ht]
      · simp only [pull, if_neg ht]
        by_contra hne
        exact ht (hsupp t hne)

end GlobalTheory.HalfCoordSB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SDFrameLattice

open NumberField GlobalTheory.PlaceModel

theorem mem_dualL_iff {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.dualL D.sp.cm V Λ ↔
      ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
  unfold Formalism.L2.Herm.dualL
  constructor
  · intro hy x hx
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb⟩ := RingHom.mem_range.mp (hz x hx)
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨b, hb⟩ := hz
      obtain ⟨a, ha⟩ := hw
      refine ⟨b + a, ?_⟩
      have e1 : ((b + a : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) + a := by push_cast; ring
      rw [e1, hb, ha, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, mul_add]
    | smul a z _ hz =>
      obtain ⟨b, hb⟩ := hz
      refine ⟨a * b, ?_⟩
      have e1 : ((a * b : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a * b := by first | (push_cast; ring) | push_cast | simp
      rw [e1, hb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · intro hy
    apply Submodule.subset_span
    intro x hx
    obtain ⟨b, hb⟩ := hy x hx
    exact RingHom.mem_range.mpr ⟨b, hb⟩

theorem isSelfDualC_of_isSDFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → IsSelfDualC V Λ := by
  intro D V β Λ N h
  obtain ⟨c, hc⟩ := h
  obtain ⟨-, hdual, hN, hin, hout⟩ := hc
  set M : ℕ := N ^ c with hM
  have hMpos : 0 < M := hN
  have hME : (M : D.host.E) ≠ 0 := by exact_mod_cast hMpos.ne'
  unfold IsSelfDualC
  refine ⟨?_, fun y => ?_⟩
  swap
  · have e : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ := hdual
    have key := mem_dualL_iff V Λ y
    rw [e] at key
    exact key
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] V.V :=
      V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)
    have hf : ∀ x, f x = ∑ i, x i • V.frame i := fun x => by simp [f]
    have hfinj : Function.Injective f := V.frame.equivFun.symm.injective
    have hL := V.standardTuple_isLattice
    let s : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := M • LinearMap.id
    have hs : ∀ x, s x = M • x := fun x => by simp [s]
    have hsinj : Function.Injective s := by
      intro x x' hxx
      rw [hs, hs] at hxx
      exact nsmul_right_injective hMpos.ne' hxx
    have hout' : ∀ x ∈ Λ, f (M • x) ∈ V.L0 := by
      intro x hx
      have h1 := hout x hx
      rw [Nat.cast_smul_eq_nsmul] at h1
      rw [hf]
      exact h1
    have hfg : Λ.FG := by
      refine Submodule.fg_of_fg_map_injective (f ∘ₗ s) (hfinj.comp hsinj) (Submodule.FG.of_le hL.fg ?_)
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.comp_apply, hs]
      exact hout' x hx
    exact Submodule.IsLattice.of_fg D.host.E hfg

end GlobalTheory.SDFrameLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeHeckeCharOfLocalComponents
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOfComponents

theorem isEtaTilde_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → IsEtaTilde D η := by
  intro D C η hc hres
  have hE := C.isEta

  have hInf : C.eta.HasInfQ (tauE D) (fun _ => (1 / 2 : ℚ)) := by
    refine ⟨fun _ => 1, fun _ => by norm_num, fun k => ?_⟩
    rw [hE.inf k]
    exact (Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)).symm
  have h1 : 1 ∈ intAE D := by
    apply AddSubgroup.subset_closure
    refine ⟨1, fun v => ?_, 1, rfl⟩
    simp [evalV, (v.adicCompletionIntegers D.host.F).one_mem]
  refine ⟨hc.1, ?_, hres, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D η C.eta _ hc hInf τ⟩

  intro x hx1 hx2 hx3
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D η C.eta hc ?_ 1 (fun P _ => hE.unr P) x ⟨hx1, hx2, hx3⟩
    ⟨finPart D (x : AE D) - 1, sub_mem hx2 h1, (one_nsmul _).symm⟩
  intro P y hy _
  exact hE.unr P y hy

end GlobalTheory.EtaTildeOfComponents
end

