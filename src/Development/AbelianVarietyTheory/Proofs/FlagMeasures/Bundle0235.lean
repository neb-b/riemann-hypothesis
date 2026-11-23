module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetImageBall
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SnMass
open scoped ENNReal

namespace GlobalTheory.GramExp

def Sgn {a : ℕ} (d : Fin a → ℂ) : Prop := ∀ i, d i = 1 ∨ d i = -1

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.diag_sq {a : ℕ} {d : Fin a → ℂ}
    (hd : _root_.GlobalTheory.GramExp.Sgn d) : Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]


open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H * H = 1) : _root_.PI.IsMatGroup (_root_.Formalism.QuantumDeterminants.UH H) := by
  unfold _root_.PI.IsMatGroup _root_.Formalism.QuantumDeterminants.UH
  have hdetH : H.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hH
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hunit : ∀ a : Matrix (Fin N) (Fin N) ℂ, aᴴ * H * a = H → IsUnit a.det := by
    intro a ha
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul] at this
    have h1 : aᴴ.det * a.det = 1 := by
      have : (aᴴ.det * a.det) * H.det = 1 * H.det := by linear_combination this
      exact mul_right_cancel₀ hdetH this
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · simp
  · intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hu := hunit a ha
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    have hc : (a⁻¹)ᴴ * aᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = ((a⁻¹)ᴴ * aᴴ) * H * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hc, hr, Matrix.one_mul, Matrix.mul_one]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.exp_cont {n : ℕ} :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous


open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.measurableSet_image_ball {X Y : Type} [PseudoMetricSpace X] [ProperSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X → Y}
    (hf : Continuous f) (x : X) (ρ : ℝ) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have hb : Metric.ball x ρ = ⋃ k : ℕ, Metric.closedBall x (ρ - 1 / ((k : ℝ) + 1)) := by
    ext y
    simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hb, Set.image_iUnion]
  exact MeasurableSet.iUnion fun k =>
    ((isCompact_closedBall x _).image hf).isClosed.measurableSet

end GlobalTheory.GramExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverOfNorm
section
namespace GlobalTheory.RankSplit

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

private lemma span_prime_isMaximal' {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
private lemma liesOver_span_of_prime_natCast_mem {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (P : Ideal A) [hP : P.IsPrime]
    (h : (p : A) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨(span_prime_isMaximal' hp).eq_of_le (Ideal.IsPrime.comap (algebraMap ℤ A)).ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
  simpa using h

theorem ncard_primesOver_of_norm {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  classical
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  haveI := span_prime_isMaximal' hp
  rw [← Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0,
    ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI hPm : P.IsMaximal := hPp.isMaximal hPne
  have hpP : (p : 𝓞 E) ∈ P := by
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using this
  obtain ⟨hn, hsq⟩ := h P hPm hpP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have he : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hpP
    · rw [hmap, Ideal.span_singleton_le_iff_mem]
      exact hsq
  have hf : Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    have h1 := Ideal.pow_inertiaDeg p P
    rw [hn] at h1
    exact (Nat.pow_eq_self_iff hp.one_lt).mp h1
  rw [he, hf]

theorem splitsF_of_norm : ∀ (D : D7) (p : ℕ), p.Prime →
    (∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((p : 𝓞 D.host.E) ∈ P) →
      Ideal.absNorm P = p ∧ (p : 𝓞 D.host.E) ∉ P ^ 2) → StandardLattice.SplitsF D p := by
  intro D p hp h
  have hE := ncard_primesOver_of_norm hp h
  have hF := GlobalTheory.ColClassCompare.ncard_primesOver_of_split (F := D.host.F) hp hE
  rw [GlobalTheory.ColClassCompare.finrank_F] at hF
  refine ⟨?_, fun v hv => (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) hp hE v.asIdeal hv).2⟩
  rw [← hF, ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1.asIdeal, v.1.isPrime, liesOver_span_of_prime_natCast_mem hp v.1.asIdeal v.2⟩
      invFun := fun P => ⟨⟨P.1, P.2.1, ?_⟩, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun P => rfl }
  · have := P.2.2
    have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot h0 P.1
  · have := P.2.2
    have h2 := (Ideal.mem_of_liesOver P.1 (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using h2

end GlobalTheory.RankSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDatumOrbitUnique
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.LocOver.OrbitUniq

open GlobalTheory.HL

section Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem change (g : Fin (r + 1) → S.V) (K : Subgroup S.GLV)
    (hon : ∀ n ∈ K, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, n (g j) = ∑ i, s i j • g i)
    (σ a b : S.GLV) (ha : a ∈ K) (hb : b ∈ K) (h : ∀ j, σ (a (g j)) = b (g j)) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, σ (g j) = ∑ i, s i j • g i := by
  obtain ⟨u, hu, hu'⟩ := hon _ (K.mul_mem hb (K.inv_mem ha))
  obtain ⟨w, -, hw⟩ := hon _ (K.inv_mem ha)
  refine ⟨u, hu, fun j => ?_⟩
  rw [← hu' j]
  have e1 : g j = a (a⁻¹ (g j)) := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  calc σ (g j) = σ (a (∑ i, w i j • g i)) := by rw [← hw j, ← e1]
    _ = ∑ i, w i j • b (g i) := by simp only [map_sum, map_smul, h]
    _ = b (a⁻¹ (g j)) := by rw [hw j, map_sum]; simp only [map_smul]
    _ = (b * a⁻¹) (g j) := rfl

end Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

theorem grp_e {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (x : V) :
    c.grp g (c.e x) = c.e (g x) := by
  show c.e (g (c.e.symm (c.e x))) = _
  simp

theorem grp_iso {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (hg : IsUnitary H g)
    (x y : S.V) : hf M.L S.Hm (c.grp g x) (c.grp g y) = hf M.L S.Hm x y := by
  obtain ⟨a, rfl⟩ := c.e.surjective x
  obtain ⟨b, rfl⟩ := c.e.surjective y
  have e := fun u v => c.h_eq u v
  simp only [Frames.h] at e
  rw [grp_e, grp_e, e, e, hg]

end GlobalTheory.LocOver.OrbitUniq

namespace GlobalTheory.LocOver

open GlobalTheory.HL GlobalTheory.LocOver.OrbitUniq

theorem orbit_over_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP d d' t h1 h2
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  have he := (orbit_reps_over M hM H r P).1
  obtain ⟨g1, hg1, d1, hd1, ht1⟩ := h1
  obtain ⟨g2, hg2, d2, hd2, ht2⟩ := h2
  suffices h12 : Datum.Rel d1 d2 from he.trans hd1 (he.trans h12 (he.symm hd2))
  obtain ⟨-, hNA, hNB, -⟩ := CoordUnip.transport M hM H r k P S c
  obtain ⟨-, -, -, hlat, -⟩ := CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, hRel, -⟩ := CoordDatum.transport M hM H r k P S c
  obtain ⟨hT, -, -⟩ := CoordTermWt.terms_correspond M hM H r k P S c
  obtain ⟨-, -, ⟨n1, hn1, hf1, -⟩, ⟨n1', hn1', hf1', -⟩, -⟩ := id ht1
  obtain ⟨-, -, ⟨m, hm, hfm, -⟩, ⟨m', hm', hfm', -⟩, -⟩ := id ht2
  obtain ⟨on1, on2, -⟩ := FrameOnto.unipotent_onto M.L r k S
  set G1 := c.grp g1 with hG1
  set G2 := c.grp g2 with hG2
  set σ : S.GLV := G2 * G1⁻¹ with hσ
  have hσG : ∀ x, σ (G1 x) = G2 x := fun x => by
    show (G2 * G1⁻¹ * G1) x = G2 x
    rw [inv_mul_cancel_right]
  have hσiso : ∀ x y, hf M.L S.Hm (σ x) (σ y) = hf M.L S.Hm x y := by
    intro x y
    obtain ⟨a, rfl⟩ := G1.surjective x
    obtain ⟨b, rfl⟩ := G1.surjective y
    rw [hσG, hσG, grp_iso c g2 hg2, grp_iso c g1 hg1]
  have rA : ∀ j, σ (c.grp n1 (S.f j)) = c.grp m (S.f j) := fun j => by
    have a1 := congrFun hf1 j
    have a2 := congrFun hfm j
    simp only [move] at a1 a2
    rw [c.f_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  have rB : ∀ j, σ (c.grp n1' (S.f' j)) = c.grp m' (S.f' j) := fun j => by
    have a1 := congrFun hf1' j
    have a2 := congrFun hfm' j
    simp only [move] at a1 a2
    rw [c.f'_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  obtain ⟨u, hu, hσf⟩ := change S S.f S.N on1 σ _ _ ((hNA n1).1 hn1) ((hNA m).1 hm) rA
  obtain ⟨u', hu', hσf'⟩ := change S S.f' S.N' on2 σ _ _ ((hNB n1').1 hn1') ((hNB m').1 hm') rB
  have hZ : cT M.L u * S.Zh * u' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S u u' a b, ← hσf, ← hσf', hσiso]
    rfl
  obtain ⟨st, hst, hsf, hsf'⟩ := ((FrameStab.stab_eq M.L r k S).2 u u' hu hu').1 hZ
  set η : S.GLV := st⁻¹ * σ with hη
  have hηf : ∀ j, η (S.f j) = S.f j := fun j => by
    show st⁻¹ (σ (S.f j)) = S.f j
    rw [hσf, ← hsf, ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hηf' : ∀ j, η (S.f' j) = S.f' j := fun j => by
    show st⁻¹ (σ (S.f' j)) = S.f' j
    rw [hσf', ← hsf', ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have fix : ∀ v ∈ S.ME, η v = v := by
    have : S.ME ≤ LinearMap.eqLocus (η : S.V →ₗ[E] S.V) LinearMap.id := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, -, rfl⟩
        exact hηf i
      · rintro _ ⟨i, -, rfl⟩
        exact hηf' i
    exact fun v hv => this hv
  have hσI : σ ∈ isomG M.L S.Hm := hσiso
  have hη0 : η ∈ S.H0 := by
    refine ⟨(isomG M.L S.Hm).mul_mem ((isomG M.L S.Hm).inv_mem hst.1.1.1) hσI, fun v => ⟨fun h => ?_, fun h => ?_⟩,
      fun v hv => ?_⟩
    · rwa [η.injective (fix _ h)] at h
    · rw [fix v h]; exact h
    · rw [fix v hv, sub_self]; exact zero_mem _
  have hI1 := (hT d1 _ ht1).1
  have hI2 := (hT d2 _ ht2).1
  have e1 : c.lat (move g1 t).abelian₂ = G1 • c.lat t.abelian₂ := hlat g1 t.abelian₂
  have e2 : c.lat (move g2 t).abelian₂ = G2 • c.lat t.abelian₂ := hlat g2 t.abelian₂
  have hA := (ComplAct.main M.L r k S (c.dat d1) _ hI1 η hη0).1
  have hB := (FrameAct.stabiliser_acts_on_terms M.L r k S _ _ hA st hst).1
  have e3 : st • η • c.lat (move g1 t).abelian₂ = c.lat (move g2 t).abelian₂ := by
    rw [e1, e2, smul_smul, smul_smul, hη, mul_inv_cancel_left, hσ, inv_mul_cancel_right]
  rw [e3] at hB
  have hd := (TermBasic.term_basic M.L r k S (c.dat d2) _ hI2).2.2.2.2.2.2.2 _ hB
  exact (hRel d1 d2).2 ⟨η, hη0, hd⟩

end GlobalTheory.LocOver
end
end

