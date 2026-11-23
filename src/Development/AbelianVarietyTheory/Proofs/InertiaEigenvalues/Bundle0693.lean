module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValLeOfNotMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.TwoBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem addVal_le_of_notMem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l x : O}
    (hx : x ∉ Ideal.span {l} * IsLocalRing.maximalIdeal O) :
    IsDiscreteValuationRing.addVal O x ≤ IsDiscreteValuationRing.addVal O l := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hlt.le
  by_cases hy : IsUnit y
  · rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hy, add_zero] at hlt
    exact lt_irrefl _ hlt
  · exact hx (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self l) hy)

noncomputable def bound (w e r k : ℕ) : ℕ := Nat.rec w (fun _ b => 2 * (e + 1) * b + 2 + 2 * r) k

theorem bound_succ (w e r k : ℕ) : bound w e r (k + 1) = 2 * (e + 1) * bound w e r k + 2 + 2 * r := rfl

theorem bound_step (w e r k : ℕ) : bound w e r k + 1 + 2 * r ≤ bound w e r (k + 1) := by
  rw [bound_succ]; nlinarith [Nat.zero_le (e * bound w e r k)]

theorem bound_mono (w e r : ℕ) : Monotone (bound w e r) :=
  monotone_nat_of_le_succ fun k => le_trans (by omega) (bound_step w e r k)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i} {M R n : ℕ} {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}

theorem NF_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NF bkP i s M d P c) :
    NF bkP i s M d P c' := fun Q hQ a Φ hΦ F hF =>
  (h Q hQ a Φ hΦ F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩

theorem NFit_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NFit bkP i s M d P c) :
    NFit bkP i s M d P c' := fun Q hQ a Φ hΦ =>
  (h Q hQ a Φ hΦ).imp id fun ⟨b, b', hb⟩ => ⟨b, b', fun F hF => (hb F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩⟩

theorem induct (hl : 0 < nu X i) {t R₀ : ℕ} (f : Fin t → X.Sig i) (hG : ∀ j, Grow bkP i (f j)) (hS : ∀ j, Step bkP i (f j))
    {H : Subgroup (GE N)} {S A : Finset (PlE D.host)} {L : Subgroup (GE N)} {z : GE N} {w e : ℕ}
    (he : IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e)
    (hM : bound w e D.R.r t ≤ X.l i ^ (M - nu X i - 1)) (h3 : nu X i + 2 ≤ M)
    (hd : AdmFam X i M H S d) (hLH : L ≤ H) (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : ∀ j, Small2 i (f j) M L z)
    (P₀ : Fin (R₀ + t) ⊕ Fin R₀ → PlE D.host) (h₀ : PiLocalization₂ i M d A L z P₀) (hF : ∀ j, NFit bkP i (f j) M d P₀ (w + 1)) :
    ∀ k, k ≤ t → ∃ P : Fin (R₀ + t) ⊕ Fin (R₀ + k) → PlE D.host, (∀ a, P (.inl a) = P₀ (.inl a)) ∧ PiLocalization₂ i M d A L z P ∧
      (∀ j, NFit bkP i (f j) M d P (bound w e D.R.r k + 1)) ∧
      ∀ j : Fin t, j.val < k → NF bkP i (f j) M d P (bound w e D.R.r k + 1) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨P₀, fun _ => rfl, h₀, hF, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨P, hP, hSt, hFit, hNF⟩ := ih (by omega)
    have hb : bound w e D.R.r (k + 1) ≤ X.l i ^ (M - nu X i - 1) := (bound_mono w e D.R.r hk).trans hM
    have hs := bound_step w e D.R.r k
    obtain ⟨P', hE, hSt', hN⟩ := hS ⟨k, hk⟩ hl M (R₀ + t) (R₀ + k) H S d A L z P (bound w e D.R.r k) e (by omega) he hb h3
      hd hLH hz (hL _) hSt (hFit _)
    have hg := fun j => hG j hl M (R₀ + t) (R₀ + k) d A L z P P' (bound w e D.R.r k + 1) (by omega) (hs.trans hb) h3 hz
      (hL j) hSt' hE
    refine ⟨P', fun a => (hE (.inl a)).trans (hP a), hSt', fun j => NFit_mono (by omega) ((hg j).2 (hFit j)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact NF_mono (by omega) ((hg j).1 (hNF j hj))
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      exact NF_mono (Nat.le_succ _) hN

theorem thmC_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → Start bkP i s ∧ Grow bkP i s ∧ Step bkP i s) → ThmC bkP := by
  intro D N X bkP hAB hCh hP i hl T hT
  obtain ⟨R₀, hR⟩ := hCh i T hT
  have : Finite (X.Sig i) := (X.finSig i).finite
  obtain ⟨t, f, -, hf⟩ := (Set.toFinite T).fin_param
  have hfT : ∀ j, f j ∈ T := fun j => hf ▸ Set.mem_range_self j
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hl0 : (X.l i : X.O0 i) ≠ 0 := fun h0 => by
    have h1 : (X.emb0 i) (X.l i : D.LL0) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (X.O0 i) (FractionRing (X.O0 i))), h0, map_zero]
    exact hp.ne_zero (Nat.cast_eq_zero.1 ((map_eq_zero _).1 h1))
  obtain ⟨e, he⟩ : ∃ e : ℕ, IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e := by
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 (pow_ne_zero (nu X i) hl0))
    exact ⟨e, he.symm⟩
  refine ⟨R₀ + t, bound (4 * D.R.r * R₀) e D.R.r t, bound (4 * D.R.r * R₀) e D.R.r t + nu X i + 3,
    fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hw : 4 * D.R.r * R₀ ≤ bound (4 * D.R.r * R₀) e D.R.r t := bound_mono (4 * D.R.r * R₀) e D.R.r (Nat.zero_le t)
  have hlt : 4 * D.R.r * R₀ + 2 < X.l i ^ M := lt_of_le_of_lt (by omega) (Nat.lt_pow_self (n := M) hp.one_lt)
  have hle : bound (4 * D.R.r * R₀) e D.R.r t ≤ X.l i ^ (M - nu X i - 1) :=
    le_trans (by omega) (Nat.lt_pow_self (n := M - nu X i - 1) hp.one_lt).le
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, hLi⟩ := GlobalTheory.ResSel.SmallSub.exists_small D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  have hh' : ∀ a, Fin.append h (fun _ : Fin t => (1 : GE N)) a ∈ L := fun a => by
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left]; exact hh a
    · rw [Fin.append_right]; exact L.one_mem
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A (R₀ + t)
    (Fin.append h fun _ => 1) (fun a => ⟨hLH (hh' a), hLζ _ (hh' a)⟩)
  choose φ g hφ hg using hFr
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh' a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hinj : Function.Injective (Sum.map id (Fin.castAdd t) : Fin (R₀ + t) ⊕ Fin R₀ → Fin (R₀ + t) ⊕ Fin (R₀ + t)) :=
    Function.injective_id.sumMap (Fin.castAdd_injective _ _)
  have h₀ : PiLocalization₂ i M d A L z (fun q : Fin (R₀ + t) ⊕ Fin R₀ => P (Sum.map id (Fin.castAdd t) q)) := by
    refine ⟨⟨fun q => hAux.1 _, fun q q' hq => hinj (hAux.2.1 _ _ hq), fun q => hAux.2.2 _⟩,
      fun a => ⟨fun v hv B hB => (hIne _ v hv B hB).trans hUL', fun σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hUL' hg⟩,
      fun a => ⟨dec_le_of_frob_mem (N.plOm.2 _) (hφ (Fin.castAdd t a)) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL _), fun b σ hσ => ?_⟩⟩
    have := hSt.2 (Fin.castAdd t a) b σ hσ
    simpa [Fin.ext_iff] using this
  have hc := hco (fun a => φ (Fin.castAdd t a)) (fun a => GlobalTheory.TwistDet.cConj X (φ (Fin.castAdd t a)))
    (fun a => ⟨hcj _, g (Fin.castAdd t a), by simpa using (hg (Fin.castAdd t a)).1⟩)
  rw [if_neg hl.ne'] at hc
  obtain ⟨P', hP', hSt', -, hNF⟩ := induct hl f (fun j => (hP i _ (hT _ (hfT j))).2.1) (fun j => (hP i _ (hT _ (hfT j))).2.2)
    he hle (by omega) hd hLH hz (fun j => ⟨hLs _ (hfT j), hLζ, hLi _ (hfT j)⟩) _ h₀
    (fun j => (hP i _ (hT _ (hfT j))).1 M (R₀ + t) R₀ d A L z _ _ _ (Nat.le_add_right _ _) hlt hz (hLs _ (hfT j)) h₀
      (fun a => ⟨hφ _, hcj _⟩) (hc _ (hfT j))) t le_rfl
  refine ⟨P', hSt'.1, ⟨fun a σ hσ => ?_, fun a b σ hσ => ?_⟩, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  · rw [hP' a] at hσ
    exact (hSt.1 a σ hσ).imp fun _ hg => hg.2
  · simpa [Fin.ext_iff] using (hSt'.2.2 a).2 b σ hσ
  · obtain ⟨j, rfl⟩ : s ∈ Set.range f := hf ▸ hs
    obtain ⟨m, hm, hu⟩ := hNF j j.2 Q hQ a Φ hΦ F hF
    exact ⟨m, Nat.lt_succ_iff.1 hm, addVal_le_of_notMem hu⟩

end GlobalTheory.StepTwo.TwoBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatible
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcDepth

theorem eq_pow_natDegree_of_dvd {p : ℂ[X]} (hp : p.Monic) {n : ℕ} (hd : p ∣ (X - 1) ^ n) :
    p = (X - 1) ^ p.natDegree := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at hd ⊢
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) n).1 hd
  have hpi := eq_of_monic_of_associated hp ((monic_X_sub_C (1 : ℂ)).pow i) hi
  rw [hpi, natDegree_pow, natDegree_X_sub_C, mul_one]

theorem prod_map_pow {α : Type*} (q : ℂ[X]) (f : α → ℕ) (s : Multiset α) :
    (s.map fun y => q ^ f y).prod = q ^ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, pow_add]

theorem fixed_ne_bot_iff_isTameWD : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc →
      ∀ x : IrrGL (k := w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  intro hDZC hDZI hEx hZel hGeo hBZ E Ω _ _ _ _ _ A w h rc hrc x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨a, ha, ε, -, hL⟩ := id hrc
  obtain ⟨m, hm⟩ := hEx _ x
  have hs : HasSupport x.rep (msupp m) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZel _ m x hm
  have hcp := GlobalTheory.T.central_character_rec_compatible hEx hZel hGeo hBZ E Ω A w h a ha _ rc hL x (msupp m) hs
  have hdy : ∀ y ∈ msupp m, (fixed y.rep (KOne (w.adicCompletion E) (Fin y.1)) ≠ ⊥ ↔ IsTameWD (rc y)) :=
    fun y hy => hDZC E Ω A w h rc hrc y (hs.isCusp hy)
  have htame : IsTameWD (rc x) ↔ ∀ y ∈ msupp m, IsTameWD (rc y) := by
    simp only [_root_.GlobalTheory.LlcTame.isTameWD_iff_charPol E Ω A w h]
    constructor
    · intro H y hy σ hσ
      have hdvd : (rc y).charPol σ ∣ (rc x).charPol σ := by
        rw [hcp σ]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)
      rw [H σ hσ] at hdvd
      have e := eq_pow_natDegree_of_dvd ((rc y).charPol_monic σ) hdvd
      rwa [WD.charPol_natDegree] at e
    · intro H σ hσ
      rw [hcp σ, Multiset.map_congr rfl (fun y hy => H y hy σ hσ), prod_map_pow]
      congr 1
      rw [hL.dim x, Multiset.map_congr rfl (fun y _ => hL.dim y), hs.sum_fst, Fintype.card_fin]
  rw [htame]
  constructor
  · intro hx y hy
    rw [← hdy y hy]
    obtain ⟨n, xs, hxs, hcs⟩ := hs
    have H := GlobalTheory.SmGL.depthZeroSupport _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hx)
    rw [← hxs] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨v, hv, hv0⟩ := H i
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  · intro H
    exact hDZI _ x (msupp m) hs fun y hy => (hdy y hy).2 (H y hy)

end GlobalTheory.LlcDepth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem extStep_holds : ExtStep := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c hρ hblk hdR h₁ h₂
  obtain ⟨K₁, hK₁, Q₁, hQ₁⟩ := h₁
  obtain ⟨K₂, hK₂, Q₂, hQ₂⟩ := h₂
  haveI := K₁.2
  haveI := K₂.2
  let K' : FinExt l := ⟨K₁.1 ⊔ K₂.1, inferInstance⟩
  have h1' : K₁.1 ≤ K'.1 := le_sup_left
  have h2' : K₂.1 ≤ K'.1 := le_sup_right
  have hK : K.1 ≤ K'.1 := hK₁.trans h1'
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  have hQ₁' : ∀ g : ↥(GK K'), ((ρ₁.comp ι) g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁ := fun g => hQ₁ ⟨g, GK_le h1' g.2⟩
  have hQ₂' : ∀ g : ↥(GK K'), ((ρ₂.comp ι) g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂ := fun g => hQ₂ ⟨g, GK_le h2' g.2⟩
  have hdR₂ : AdmDR P ρ₂ := (_root_.GlobalTheory.PMon.subQuot l P AI T a b K r ρ ρ₁ ρ₂ c hρ hblk hdR).2
  obtain ⟨hcr, hcc, hcoc⟩ := _root_.GlobalTheory.PMon.extCoc_rat_cont_cocycle l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PMon.hyodo_mat l P AI T (a × b) K' r (homRep (ρ₁.comp ι) (ρ₂.comp ι)) (homUnit Q₁ Q₂)
    (_root_.GlobalTheory.PMon.isRat_homRep_restrict l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk) (_root_.GlobalTheory.PMon.homUnit_period l P a b K' (ρ₁.comp ι) (ρ₂.comp ι) Q₁ Q₂ hQ₁' hQ₂')
    (extCoc (ρ₂.comp ι) (fun g => c (ι g))) hcr hcc hcoc
    (fun m => by
      obtain ⟨w, hw⟩ := _root_.GlobalTheory.PMon.extCoc_dies_in_BdR l P AI T a b K ρ ρ₁ ρ₂ c hblk hdR hdR₂ m
      exact ⟨w, fun g => hw (ι g)⟩)
  obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.PMon.extPeriodMatrix l P a b K' (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hblk (ι g))
    Q₁ Q₂ hQ₁' hQ₂' v hv
  exact ⟨K', hK, Q, fun g => hQ g⟩

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroInertiaOfLanglands
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

namespace GlobalTheory.DepthZeroBridge

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem redThrough_eq_of_val_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {a b : Ω} (ha : a ∈ A) (hab : A.valuation (a - b) < 1) :
    redThrough A κ a = redThrough A κ b := by
  have hab' : a - b ∈ A := (A.valuation_le_one_iff _).mp hab.le
  have hb : b ∈ A := by
    have : b = a - (a - b) := by ring
    rw [this]; exact A.sub_mem ha hab'
  unfold redThrough
  rw [dite_eq_left ha, dite_eq_left hb]
  congr 1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  show (⟨a, ha⟩ - ⟨b, hb⟩ : A) ∈ IsLocalRing.maximalIdeal A
  exact (A.valuation_lt_one_iff _).mpr hab


end GlobalTheory.DepthZeroBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryHyperbolicVectors
section
noncomputable section

namespace GlobalTheory.LamTie.AuxiliaryPrimeFunction

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.GridChars GlobalTheory.CMVal

variable {L : Type} [Field L] [NumberField L]

theorem expAt_succ {χ : Formalism.L2.Host.HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h1 : χ.LevelLe v (n + 1))
    (h2 : ¬ χ.LevelLe v n) : ExpAt χ v (n + 1) := by
  have mono : ∀ a b : ℕ, a ≤ b → χ.LevelLe v a → χ.LevelLe v b := fun a b hab h x hx hx' =>
    h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))
  intro m
  refine ⟨fun h => ?_, fun h => mono _ _ h h1⟩
  by_contra hm
  exact h2 (mono _ _ (by omega) h)

theorem finite_over {p : ℕ} (hp : p.Prime) : {w : HeightOneSpectrum (𝓞 L) | (p : 𝓞 L) ∈ w.asIdeal}.Finite := by
  have h : Ideal.span {(p : 𝓞 L)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  refine (Ideal.finite_factors h).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 hw

theorem prime_eq {w : HeightOneSpectrum (𝓞 L)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : (p : 𝓞 L) ∈ w.asIdeal)
    (h2 : (q : 𝓞 L) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : 𝓞 L) (q : 𝓞 L) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem natCast_mem_of_under {F : Type} [Field F] [NumberField F] [Algebra F L] {w w' : HeightOneSpectrum (𝓞 L)}
    (h : w.under (𝓞 F) = w'.under (𝓞 F)) {p : ℕ} (hp : (p : 𝓞 L) ∈ w.asIdeal) : (p : 𝓞 L) ∈ w'.asIdeal := by
  have key : ∀ u : HeightOneSpectrum (𝓞 L), (p : 𝓞 F) ∈ (u.under (𝓞 F)).asIdeal ↔ (p : 𝓞 L) ∈ u.asIdeal := fun u => by
    change algebraMap (𝓞 F) (𝓞 L) _ ∈ u.asIdeal ↔ _
    rw [map_natCast]
  exact (key w').1 (h ▸ (key w).2 hp)

end General

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

end GlobalTheory.LamTie.AuxiliaryPrimeFunction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsSst P (qRep ρ) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∃ F : Frame bk N d fun g => (ρ g).val, F.IsDR ∧ (IsCrys (P.PD K) (qRep ρ) → F.IsCr) := by
  first | (exact @GlobalTheory.BKLim.exists_frame_sst) | (exact GlobalTheory.BKLim.exists_frame_sst) | (intros; apply GlobalTheory.BKLim.exists_frame_sst  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  first | exact @GlobalTheory.exists_letter_vector_exact_degree | exact GlobalTheory.exists_letter_vector_exact_degree | (intros; apply GlobalTheory.exists_letter_vector_exact_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFullTeich
section
noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full_teich (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Neutral.B1.Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : Z.Teich) :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z :=
  exists_twL_full hA hR D N hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS fun a w hw => ⟨w, rfl, hT a w hw⟩

end GlobalTheory.LamTie.TrueList
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldsAtAuxiliaryPrimes
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.LocalFieldsQD

theorem main : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  refine ⟨fun i hi w hw => ?_, _root_.GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d D⟩
  obtain ⟨M, hM, y, hy, hK⟩ := _root_.GlobalTheory.HubLoc.kw_eq_unram_sup_sqrt D i hi w hw
  obtain ⟨-, -, hq8, hd16, -⟩ := D.host.hyp
  have h4 : D.nd.l i % 4 = 3 := by rcases hi with h | h <;> rw [h] <;> omega
  have h2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨e1, e2, e3, e4⟩ := _root_.GlobalTheory.SqrtNegL.structure_sqrt_neg (D.nd.l i) h2 (D.nbr i w hw).Kw M y hM hy
    (_root_.GlobalTheory.sqrt_neg_l_not_mem_Kur _ y hy) (_root_.GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity _ h4 y hy) hK
  exact ⟨⟨y, hy, e1⟩, e2, e3, e4⟩

end GlobalTheory.LocalFieldsQD
end

