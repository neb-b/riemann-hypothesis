module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TotalWeight

theorem natCast_pow_le_pow_of_exponent_le (q m a e e' : ℕ) (he : e ≤ e') (h1 : (1 : ℝ) ≤ (q : ℝ) ^ (m + a)) :
    (q : ℝ) ^ (e * m) ≤ ((q : ℝ) ^ (m + a)) ^ e' := by
  have h2 : (q : ℝ) ^ m ≤ (q : ℝ) ^ (m + a) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simpa using h1
      · simp [hm.ne']
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (Nat.le_add_right _ _)
  calc (q : ℝ) ^ (e * m) = ((q : ℝ) ^ m) ^ e := by rw [mul_comm, pow_mul]
    _ ≤ ((q : ℝ) ^ (m + a)) ^ e := pow_le_pow_left₀ (by positivity) h2 e
    _ ≤ _ := pow_le_pow_right₀ h1 he

theorem sumCls_one_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k)
    (h : ∃ d Λ, S.IsTerm d Λ) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  obtain ⟨d, Λ, hT⟩ := h
  obtain ⟨ha, hD, -, -, h1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : 0 ≤ S.vth := by
    unfold Frames.vth
    split_ifs <;> norm_num
  have hHp : S.Hp = (S.q : ℝ) ^ ((S.vth + S.vD).toNat + S.a.toNat) := by
    unfold Frames.Hp
    rw [← zpow_natCast]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (add_nonneg hth hD)]
    ring
  refine (GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans
    ((GlobalTheory.IntClsCount.main L r k S hD).trans ?_)
  have he : r * (r + 1) ≤ 3 * (r + 1) ^ 2 := by nlinarith
  rw [hHp] at h1 ⊢
  have key := ENNReal.ofReal_le_ofReal (natCast_pow_le_pow_of_exponent_le S.q _ _ _ _ he h1)
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at key
  exact key

end GlobalTheory.HL.TotalWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbits
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordAmp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ} {P : LocNG.FPair H r} {S : Frames M.L r k}

open scoped Pointwise ENNReal Classical in
private lemma tsum_transversal_eq_tsum_orbits_lemma {T X G R : Type*} [Group G] [MulAction G X]
    [AddCommMonoid R] [TopologicalSpace R] (St : Subgroup G)
    (rel : T → T → Prop) (A B : Set T) (hB : _root_.Formalism.MainNotions.S.LocNG.IsTransv rel A B) (ℓ : T → X) (term : X → Prop)
    (p : T → Prop) (Q : X → Prop)
    (hterm : ∀ t ∈ A, term (ℓ t)) (hsurj : ∀ Λ, term Λ → ∃ t ∈ A, ℓ t = Λ)
    (hrel : ∀ t t', rel t t' ↔ ∃ g ∈ St, ℓ t' = g • ℓ t)
    (hinv : ∀ Λ, term Λ → ∀ g ∈ St, term (g • Λ))
    (hpQ : ∀ t ∈ A, (p t ↔ Q (ℓ t))) (hQ : ∀ Λ, term Λ → ∀ g ∈ St, Q Λ → Q (g • Λ))
    (f : X → R) (hf : ∀ Λ, term Λ → ∀ g ∈ St, f (g • Λ) = f Λ)
    (val : T → R) (hval : ∀ t ∈ A, val t = f (ℓ t)) :
    ∑' t : {t // t ∈ B ∧ p t}, val t.1
      = ∑' o : MulAction.orbitRel.Quotient St X,
          if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0 := by
  obtain ⟨hBA, hcover, huniq⟩ := hB
  have key : ∀ Λ : X, ∃ g ∈ St,
      Quotient.out (Quotient.mk (MulAction.orbitRel St X) Λ) = g • Λ := fun Λ => by
    obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.mk_out (s := MulAction.orbitRel St X) Λ
    exact ⟨g, hg, hgx.symm⟩
  let toFun : {t // t ∈ B ∧ p t} →
      ↥{o : MulAction.orbitRel.Quotient St X | term (Quotient.out o) ∧ Q (Quotient.out o)} :=
    fun t => ⟨Quotient.mk _ (ℓ t.1), by
      obtain ⟨g, hg, he⟩ := key (ℓ t.1)
      have h1 := hterm _ (hBA t.2.1)
      show term (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
        ∧ Q (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
      rw [he]
      exact ⟨hinv _ h1 g hg, hQ _ h1 g hg ((hpQ _ (hBA t.2.1)).1 t.2.2)⟩⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ heq
      have h2 : Quotient.mk (MulAction.orbitRel St X) (ℓ t) = Quotient.mk _ (ℓ t') :=
        congrArg Subtype.val heq
      obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.exact h2
      have : rel t' t := (hrel t' t).2 ⟨g, hg, hgx.symm⟩
      exact Subtype.ext (huniq _ ht'.1 _ ht.1 this).symm
    · rintro ⟨o, ho⟩
      obtain ⟨t0, ht0A, ht0⟩ := hsurj _ ho.1
      obtain ⟨y, hyB, hy⟩ := hcover t0 ht0A
      obtain ⟨g, hg, hgy⟩ := (hrel y t0).1 hy
      have hyA := hBA hyB
      have hQy : Q (ℓ y) := by
        have := hQ (ℓ t0) (hterm _ ht0A) g⁻¹ (inv_mem hg) (by rw [ht0]; exact ho.2)
        rwa [hgy, inv_smul_smul] at this
      refine ⟨⟨y, hyB, (hpQ y hyA).2 hQy⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (ℓ y) = o
      rw [← Quotient.out_eq o, ← ht0, hgy]
      exact Quotient.sound ⟨⟨g⁻¹, inv_mem hg⟩, inv_smul_smul g _⟩
  let e := Equiv.ofBijective toFun hbij
  have hR : (∑' o : MulAction.orbitRel.Quotient St X,
      if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0)
      = ∑' o : ↥{o : MulAction.orbitRel.Quotient St X |
          term (Quotient.out o) ∧ Q (Quotient.out o)}, f (Quotient.out o.1) := by
    refine Eq.trans ?_ (tsum_subtype _ (fun o => f (Quotient.out o))).symm
    refine tsum_congr fun o => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hR, ← e.tsum_eq]
  refine tsum_congr fun t => ?_
  show val t.1 = f (Quotient.out (Quotient.mk _ (ℓ t.1)))
  obtain ⟨g, hg, he⟩ := key (ℓ t.1)
  rw [he, hf _ (hterm _ (hBA t.2.1)) g hg, hval _ (hBA t.2.1)]


open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in
theorem _root_.GlobalTheory.HL.CoordAmp.sums_eq (hM : M.OK) (c : _root_.GlobalTheory.HL.Coord P S)
    (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P)
    (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : Submodule M.L.O S.V → Prop)
    (hpQ : ∀ t, _root_.Formalism.MainNotions.S.LocNG.IsTermOver P d t → (p t ↔ Q (c.lat t.abelian₂)))
    (hQ : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St, Q Λ → Q (h • Λ)) :
    _root_.Formalism.MainNotions.S.LocNG.amp R d p = S.amp (c.dat d) Q ∧
      (∑' t : {t // t ∈ R.RT d ∧ p t}, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) Q := by
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨-, -, hbij, hlatg, -, hmu⟩ := _root_.GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, -, hSt, -⟩ := _root_.GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨hcorr, hex, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hB := R.hRT d
  have hrel : ∀ t t', _root_.Formalism.MainNotions.S.LocNG.TRel P t t' ↔ ∃ g ∈ S.St,
      c.lat t'.abelian₂ = g • c.lat t.abelian₂ := by
    intro t t'
    unfold _root_.Formalism.MainNotions.S.LocNG.TRel
    constructor
    · rintro ⟨s, hs, he⟩
      exact ⟨c.grp s, (hSt s).1 hs, by rw [he, hlatg]⟩
    · rintro ⟨g, hg, he⟩
      refine ⟨c.grp.symm g, (hSt _).2 (by simpa using hg), hbij.1 ?_⟩
      rw [hlatg, MulEquiv.apply_symm_apply, he]
  have hterm_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St, S.IsTerm (c.dat d) (g • Λ) :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).1
  have hom_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.om (c.dat d) (g • Λ) = S.om (c.dat d) Λ :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).2.1
  have hmu_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.mu (g • Λ) = S.mu Λ :=
    fun Λ h g hg => ((_root_.GlobalTheory.HL.volSt M.L r k S).1 Λ
      (_root_.GlobalTheory.HL.TermBasic.term_basic M.L r k S _ Λ h).1.1).2.2 g hg
  constructor
  · unfold _root_.Formalism.MainNotions.S.LocNG.amp _root_.GlobalTheory.HL.Frames.amp
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => (S.mu Λ : ℂ) * S.om (c.dat d) Λ)
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg, hom_inv Λ h g hg])
      (fun t => (_root_.Formalism.MainNotions.S.LocNG.mu P t : ℂ) * _root_.Formalism.MainNotions.S.LocNG.om P t)
      (fun t ht => by simp only [hmu t, (hcorr d t ht).2.1])
  · unfold _root_.GlobalTheory.HL.Frames.mass
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => ENNReal.ofReal (S.mu Λ))
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg])
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t))
      (fun t _ => by simp only [hmu t])


open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in
theorem _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P),
    _root_.Formalism.MainNotions.S.LocNG.amp R d (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H)) = S.amp (c.dat d)
        (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t) = S.amp (c.dat d)
        (S.BBzero (c.dat d)) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧
      (∑' t : R.RT d, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) (fun _ => True) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hcorr, -, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hBB : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St,
        (S.BBzero (c.dat d) (h • Λ)
          ↔ S.BBzero (c.dat d) Λ) :=
    fun Λ hΛ h hh => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ hΛ h hh).2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => (hcorr d t ht).2.2)
      (fun Λ hΛ h hh hq => by rwa [hBB Λ hΛ h hh])).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => by rw [(hcorr d t ht).2.2, not_not])
      (fun Λ hΛ h hh hq => (hBB Λ hΛ h hh).2 hq)).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).1
  · rw [← (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).2]
    exact ((Equiv.subtypeEquivRight (fun t => by simp)).tsum_eq
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))).symm

end GlobalTheory.HL.CoordAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbits
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSum

theorem tsum_reps_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ0, hκ⟩ := _root_.GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu M hM H r k P S c d0
  obtain ⟨-, -, hrel, -, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, -, hex⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  refine ⟨κ, hκ0, fun φ hφ hφ0 => ?_⟩

  have hmove : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm δ Λ) → ∃ Λ, S.IsTerm (h • δ) Λ := by
    rintro h hh δ ⟨Λ, hΛ⟩
    exact ⟨h • Λ, (GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh).1⟩

  have hψ0 : ∀ δ : S.Datum, (¬ ∃ Λ, S.IsTerm δ Λ) → ENNReal.ofReal (S.nu δ) * φ δ = 0 := by
    intro δ hδ
    rw [hφ0 δ hδ, mul_zero]
  have hterm : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1) =
      ENNReal.ofReal κ * (ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) := by
    intro d
    by_cases hd : ∃ Λ, S.IsTerm (c.dat d.1) Λ
    · obtain ⟨Λ, hΛ⟩ := hd
      rw [hκ d.1 Λ hΛ, ENNReal.ofReal_mul hκ0, mul_assoc]
    · rw [hφ0 _ hd, mul_zero, mul_zero, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1

  let A : Set R.RD := {a | ∃ Λ, S.IsTerm (c.dat a.1) Λ}
  have h1 : ∑' a : A, ENNReal.ofReal (S.nu (c.dat a.1.1)) * φ (c.dat a.1.1) =
      ∑' d : R.RD, ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1) := by
    refine tsum_subtype_eq_of_support_subset (f := fun d : R.RD => ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) ?_
    intro a ha
    by_contra hn
    exact ha (hψ0 _ hn)
  have hT : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ Λ, S.IsTerm (g • x) Λ :=
    fun g x hx => hmove g g.2 x hx
  have hι : ∀ a : A, ∃ Λ, S.IsTerm (c.dat a.1.1) Λ := fun a => a.2
  have hsurj : ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ a : A, ∃ g : S.H0, g • c.dat a.1.1 = x := by
    intro x hx
    obtain ⟨Λ, hΛ⟩ := hx
    obtain ⟨d, rfl⟩ := hex x Λ hΛ
    obtain ⟨y, hyR, hy⟩ := R.hRD.2.1 d (Set.mem_univ d)
    obtain ⟨h, hh, hhy⟩ := (hrel y d).1 hy
    have hTy : ∃ Λ, S.IsTerm (c.dat y) Λ := by
      have h' := hmove h⁻¹ (S.H0.inv_mem hh) _ ⟨Λ, hΛ⟩
      rwa [← hhy, inv_smul_smul] at h'
    exact ⟨⟨⟨y, hyR⟩, hTy⟩, ⟨h, hh⟩, hhy⟩
  have hinj : ∀ a b : A, (∃ g : S.H0, g • c.dat a.1.1 = c.dat b.1.1) → a = b := by
    rintro a b ⟨g, hg⟩
    have hr : LocNG.Datum.Rel a.1.1 b.1.1 := (hrel _ _).2 ⟨g, g.2, hg⟩
    exact Subtype.ext (Subtype.ext (R.hRD.2.2 _ a.1.2 _ b.1.2 hr))
  have hinv : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) →
      ENNReal.ofReal (S.nu (g • x)) * φ (g • x) = ENNReal.ofReal (S.nu x) * φ x := by
    rintro g x ⟨Λ, hΛ⟩
    show ENNReal.ofReal (S.nu ((g : S.GLV) • x)) * φ ((g : S.GLV) • x) = _
    rw [(GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S x Λ hΛ).2 g g.2, hφ g g.2 x]
  have h2 := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.H0) (X := S.Datum) (A := A)
    (fun a => c.dat a.1.1) (fun x => ∃ Λ, S.IsTerm x Λ) hT hι hsurj hinj).2
    (fun x => ENNReal.ofReal (S.nu x) * φ x) hinv
  rw [← h1, h2]
  show _ = ∑' o : MulAction.orbitRel.Quotient S.H0 S.Datum, ENNReal.ofReal (S.nu o.out) * φ o.out
  refine tsum_congr fun o => ?_
  split_ifs with ho
  · rfl
  · exact (hψ0 _ ho).symm

end GlobalTheory.HL.CoordSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTermCount_frameClass_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (j : ℕ), (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  first | exact @GlobalTheory.HL.TermCount.nT_cardI_le | exact GlobalTheory.HL.TermCount.nT_cardI_le | (intros; apply GlobalTheory.HL.TermCount.nT_cardI_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermStabilizerCommensurable
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocComm

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrel d τ hτ
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hrel
  obtain ⟨hUW, -, -, -, hAut, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, -, -, hStab, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨hTC, -, -⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have key : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.IsTerm (c.dat d) (c.lat τ.abelian₂) := fun d τ h => (hTC d τ h).1
  have eA : ∀ Λ, P.UW0 ⊓ LocNG.Aut Λ =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat Λ)).comap c.grp.toMonoidHom := by
    intro Λ
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rw [hUW, hAut]
  have eS : ∀ d : LocNG.Datum P, LocNG.Datum.Stab d =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom := by
    intro d
    ext g
    rw [Subgroup.mem_comap, hStab]
    rfl
  have rel : ∀ A B : Subgroup S.GLV,
      (A.comap c.grp.toMonoidHom).relIndex (B.comap c.grp.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective c.grp.surjective]
  have fixd : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂) ≤ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d) := by
    intro d τ h x hx
    obtain ⟨hx0, hxs⟩ := Subgroup.mem_inf.mp hx
    have ht := key d τ h
    have h1 := (_root_.GlobalTheory.HL.ComplAct.main M.L r k S _ _ ht x hx0).1
    rw [MulAction.mem_stabilizer_iff.mp hxs] at h1
    have h2 := (_root_.GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ ht).2.2.2.2.2.2.2 _ h1
    exact Subgroup.mem_inf.mpr ⟨hx0, MulAction.mem_stabilizer_iff.mpr h2⟩
  have volH := _root_.GlobalTheory.HL.Frames.stab_commensurable_invVol_smul M.L r k S
  have cLam : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂)) := by
    intro d τ h
    have := volH.1 _ (_root_.GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ (key d τ h)).1.1
    exact ⟨⟨this.1⟩, ⟨this.2.1⟩⟩
  have cDat : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
    intro d τ h
    obtain ⟨h1, h2⟩ := volH.2 _ _ (key d τ h)
    exact ⟨⟨h1⟩, ⟨h2⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [eA, eS]
    exact Subgroup.comap_mono (fixd d τ hτ)
  · rw [eA, eS, rel]
    exact ((cLam d τ hτ).symm.trans (cDat d τ hτ)).1.relIndex_ne_zero
  · intro d' τ' hτ'
    rw [eS, eS, rel]
    exact ((cDat d τ hτ).symm.trans (cDat d' τ' hτ')).1.relIndex_ne_zero

end GlobalTheory.HL.LocComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectEqOfLatticeEq
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocDefect

theorem bbne_of_lam_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → (LocNG.BBne (H := H) τ ↔ LocNG.BBne (H := H) τ') := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP d d' τ τ' hτ hτ' hL
  have hdd : d = d' := _root_.GlobalTheory.HL.LatUniq.datum_of_lattice M hM H r k P hk hP d d' τ τ' hτ hτ' hL
  subst hdd
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  have h := (GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1
  rw [(h d τ hτ).2.2, (h d τ' hτ').2.2, hL]

end GlobalTheory.HL.LocDefect
end

