module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0125
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0147
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0245
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedCohomologyVanishing
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι : Type}
    (Q : ObjectProperty (Thick (LL q))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  have h := _root_.GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U ∘ i) Finset.univ T
  have e : (⨅ α ∈ (Finset.univ : Finset (Fin (n + 1))), (U ∘ i) α) = capO U i := by simp [capO]
  rw [e] at h
  refine propext ⟨fun hT => ?_, fun hT a => ?_⟩
  · refine ⟨(hT 0).1, capO U i, rfl, h.2 fun a _ => ?_⟩
    obtain ⟨-, V, hV, hI⟩ := hT a
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact hI
  · obtain ⟨h1, V, hV, hI⟩ := hT
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨h1, _, rfl, h.1 hI a (Finset.mem_univ _)⟩

theorem dividedPowerFiltration_bot {K : Type} [CommRing K] {s : ℕ} (hs : 0 < s) : pdP (dividedPowersBot K) s = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hc p hp)
    omega
  obtain ⟨p, hp, hp0⟩ := this
  have h0 : (dividedPowersBot K).dpow p.1 p.2 = 0 := by
    have : p.2 = 0 := hl p hp
    rw [this]
    exact (dividedPowersBot K).dpow_eval_zero hp0
  simp only [SetLike.mem_coe]
  rw [List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h0⟩)]
  exact Ideal.zero_mem _

theorem tfBase {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 0 < s) : TFBase (dividedPowersBot K) 1 s := by
  refine ⟨dividedPowerFiltration_bot hs, ?_, ?_⟩
  · intro r x h
    simpa using h
  · intro n hn
    exact ⟨0, (n : K)⁻¹, by simpa only [pow_zero] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)⟩

def zeroSerre (K : Type) [CommRing K] : Serre.{1} K where
  P M _ _ := Subsingleton M
  zero _ _ _ h := h
  mid M₁ M₂ M₃ _ _ _ _ _ _ f g hfg h₁ h₃ := ⟨fun a b => by
    have key : ∀ x : M₂, x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hfg x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    rw [key a, key b]⟩

theorem subsingleton_H {K : Type} [CommRing K] (C : Cx.{1} K) (n : ℕ) (h : Subsingleton (C.X n)) : Subsingleton (C.H n) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Subsingleton.elim a b]

theorem cech_van (hV : StVan) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} (U : ι → X.Opens) (d : ι → ℕ)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r b a : ℕ) (hr : r < s)
    (hbr : b ≠ r) : Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) b).cx.H a) := by
  refine subsingleton_H _ a ?_
  refine ⟨fun x y => funext fun i => ?_⟩
  have e := capT_eq (q := q) (TF l s) U i
  obtain ⟨c', -⟩ := _root_.GlobalTheory.CompanionTheory.CoordRes.main (c (i 0)) (capO_le U i 0) (ha _ i)
  have : Subsingleton (HU (GF q r) (capT (fun α => SS q l s (U α)) i) b) := by
    rw [e]
    exact hV l s hb q c' r b hr hbr
  exact Subsingleton.elim _ _

theorem cech_pos (hB : StVB) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} [Fintype ι] (U : ι → X.Opens) (d : ι → ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (hU : (⨆ α, U α) = V)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r p : ℕ) (hr : r < s) :
    Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r).cx.H (p + 1)) := by
  obtain ⟨vb⟩ := hB l s hb q U d c ha r hr
  exact _root_.GlobalTheory.CompanionTheory.VBAff.subsingleton_H (strV q) V hV U hU ha (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r) vb p

set_option maxHeartbeats 2000000 in
theorem main (hV : StVan) (hB : StVB) (hC : StCover) : KH.GlobSerreSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := by
  intro hS K _ _ X q _ V hVa s r j hr hj
  have hs : 0 < s := by omega
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase hs
  obtain ⟨ι, _, U, d, c, hU, ha⟩ := hC q V hVa
  have hle : ∀ α, U α ≤ V := fun α => hU ▸ le_iSup U α
  have hinc : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Set.range U) ≤
      St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {V} := by
    rintro T ⟨h1, W, ⟨α, rfl⟩, hI⟩
    exact ⟨h1, V, rfl, fun x hx => hle α (hI hx)⟩
  have hz := _root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} hinc
    (by
      rintro W rfl
      rw [← hU, sSup_range]) j
  have hcech : ∀ a b, a + b = j → (zeroSerre K).P ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q 1 s (U α)) b).cx.H a) := by
    intro a b hab
    by_cases hbr : b = r
    · subst hbr
      cases a with
      | zero => exact absurd (by omega) hj
      | succ p => exact cech_pos hB 1 s hb q U d V hVa hU c ha b p hr
    · exact cech_van hV 1 s hb q U d c ha r b a hr hbr
  have hG := hS (O := K) (R := K) (I := ⊥) (γ := dividedPowersBot K) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥) (Λ := K)
    (GF q r) (TF 1 s) U (zeroSerre K) j hcech
  exact @Function.Injective.subsingleton _ _ _ (hz.1 r ((r : ℤ) + 1)).1 hG

end GlobalTheory.CompanionTheory.GrForm

namespace GlobalTheory.CompanionTheory.GrForm

theorem gr_aff : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := fun hL _ hP hS _ =>
  main (_root_.GlobalTheory.CompanionTheory.GrForm.van _root_.GlobalTheory.CompanionTheory.GrForm.stFrame hL hP)
    (_root_.GlobalTheory.CompanionTheory.GrVB.main (_root_.GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle _root_.GlobalTheory.CompanionTheory.GrForm.stCocycle) _root_.GlobalTheory.CompanionTheory.GrForm.stAdd _root_.GlobalTheory.CompanionTheory.GrFormSmul.stSmul _root_.GlobalTheory.CompanionTheory.GrForm.stRes _root_.GlobalTheory.CompanionTheory.GrForm.stAct (_root_.GlobalTheory.CompanionTheory.GrForm.stLoc _root_.GlobalTheory.CompanionTheory.GrForm.stFrame hL hP))
    _root_.GlobalTheory.CompanionTheory.GrForm.AffCover.stCover hS
end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorAdelicLatticeCompact
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.AnnLattice

variable {E : Type} [Field E] [NumberField E]

theorem sLoc_mul (w : Pl E) (t : w.adicCompletion E) (z : Af E) :
    sLoc E w t * z = sLoc E w (t * pLoc E w z) := by
  classical
  refine FiniteAdeleRing.ext _ fun v => ?_
  change (Pi.single w t : ∀ v : Pl E, v.adicCompletion E) v * pLoc E v z =
    (Pi.single w (t * pLoc E w z) : ∀ v : Pl E, v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem val_int_le_one (u : Pl E) (d : 𝓞 E) :
    Valued.v (algebraMap E (u.adicCompletion E) (algebraMap (𝓞 E) E d)) ≤ 1 := by
  rw [Formalism.UG.P.levelaf_valued_algebraMap]
  exact u.valuation_le_one d

theorem exists_int_small (S : Finset (Pl E)) (c : Pl E → WithZero (Multiplicative ℤ))
    (hc : ∀ w ∈ S, c w ≠ 0) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ w ∈ S, Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E D)) ≤ c w := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert w S hw ih =>
    obtain ⟨D, hD0, hD⟩ := ih fun u hu => hc u (Finset.mem_insert_of_mem hu)
    obtain ⟨x, hxw, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hlt : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E x)) < 1 := by
      rw [Formalism.UG.P.levelaf_valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hxw
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (hc w (Finset.mem_insert_self _ _)))
    refine ⟨D * x ^ n, mul_ne_zero hD0 (pow_ne_zero _ hx0), fun u hu => ?_⟩
    simp only [map_mul, map_pow]
    rcases Finset.mem_insert.1 hu with rfl | hu
    · calc _ ≤ 1 * _ := mul_le_mul' (val_int_le_one u D) le_rfl
        _ = _ := one_mul _
        _ ≤ c u := hn.le
    · calc _ ≤ c u * 1 := mul_le_mul' (hD u hu) (pow_le_one' (val_int_le_one u x) n)
        _ = c u := mul_one _

theorem one_le_exp_mul {b : WithZero (Multiplicative ℤ)} (h : 1 < b) : 1 ≤ WithZero.exp (-1 : ℤ) * b := by
  have hb0 : b ≠ 0 := (zero_lt_one.trans h).ne'
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, b = WithZero.exp n := ⟨_, (WithZero.exp_log hb0).symm⟩
  rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  omega

variable {ψ : AddChar (Ad E) ℂ}

theorem val_le_one_of_cond {w : Pl E} (hw : Cond ψ w) {L : Set (Af E)}
    (hL : ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) {z : Af E}
    (hz : ∀ a ∈ L, ψ (sFin E (a * z)) = 1) : Valued.v (pLoc E w z) ≤ 1 := by
  by_contra hcon
  have h1 : 1 < Valued.v (pLoc E w z) := not_le.1 hcon
  obtain ⟨-, ϖ, y, hϖ, hy1, hy⟩ := hw
  have hz0 : Valued.v (pLoc E w z) ≠ 0 := (zero_lt_one.trans h1).ne'
  have hzw : pLoc E w z ≠ 0 := (map_ne_zero _).1 hz0
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hd : 1 ≤ Valued.v ϖ * Valued.v (pLoc E w z) := by
    rw [hϖ']
    exact one_le_exp_mul h1
  have hyv : Valued.v (ϖ * y) ≤ 1 := hy1
  rw [map_mul] at hyv
  have hle : Valued.v y ≤ Valued.v (pLoc E w z) := by
    calc Valued.v y = 1 * Valued.v y := (one_mul _).symm
      _ ≤ (Valued.v ϖ * Valued.v (pLoc E w z)) * Valued.v y := mul_le_mul' hd le_rfl
      _ = (Valued.v ϖ * Valued.v y) * Valued.v (pLoc E w z) := mul_right_comm _ _ _
      _ ≤ 1 * Valued.v (pLoc E w z) := mul_le_mul' hyv le_rfl
      _ = _ := one_mul _
  have ht : y / pLoc E w z ∈ Formalism.UG.Ov E w := by
    change Valued.v (y / pLoc E w z) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have h2 := hz _ (hL _ ht)
  rw [sLoc_mul, div_mul_cancel₀ _ hzw] at h2
  exact hy h2

theorem exists_val_bound (hψ : StdPsi ψ) (w : Pl E) {L : Set (Af E)} {N : Set (w.adicCompletion E)} (hN : N ∈ 𝓝 0)
    (hL : ∀ t ∈ N, sLoc E w t ∈ L) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) →
      ∀ d : w.adicCompletion E, Valued.v d ≤ c → Valued.v (d * pLoc E w z) ≤ 1 := by
  obtain ⟨y, hy⟩ := hψ.loc w
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp)
  have hY : Valued.v y ≠ 0 := (map_ne_zero _).2 hy0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hN
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact (map_ne_zero _).2 γ.ne_zero
  refine ⟨g / Valued.v y, div_ne_zero hg0 hY, fun z hz d hd => ?_⟩
  by_contra hcon
  have h1 : 1 < Valued.v (d * pLoc E w z) := not_le.1 hcon
  rw [map_mul] at h1
  have hb0 : Valued.v (pLoc E w z) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact not_lt_of_ge zero_le' h1
  have hzw : pLoc E w z ≠ 0 := (map_ne_zero _).1 hb0
  have hYpos : 0 < Valued.v y := zero_lt_iff.2 hY
  have hbpos : 0 < Valued.v (pLoc E w z) := zero_lt_iff.2 hb0
  have hdY : Valued.v d * Valued.v y ≤ g := (le_div_iff₀ hYpos).1 hd
  have ht : y / pLoc E w z ∈ N := by
    refine hγ ?_
    change (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict (y / pLoc E w z) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, map_div₀, ← hg, div_lt_iff₀ hbpos]
    calc Valued.v y = 1 * Valued.v y := (one_mul _).symm
      _ < (Valued.v d * Valued.v (pLoc E w z)) * Valued.v y := mul_lt_mul_of_pos_right h1 hYpos
      _ = (Valued.v d * Valued.v y) * Valued.v (pLoc E w z) := mul_right_comm _ _ _
      _ ≤ g * Valued.v (pLoc E w z) := mul_le_mul' hdY le_rfl
  have h2 := hz _ (hL _ ht)
  rw [sLoc_mul, div_mul_cancel₀ _ hzw] at h2
  exact hy h2

theorem exists_isCompact_annihilator : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ},
    StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) → ∀ (L : Set (Af E)),
    (∀ w, w ∉ S → ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) →
    (∀ w ∈ S, ∃ N ∈ 𝓝 (0 : w.adicCompletion E), ∀ t ∈ N, sLoc E w t ∈ L) →
    ∃ C : Set (Af E), IsCompact C ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → z ∈ C := by
  intro E _ _ _ ψ hψ S hS L hoff hon
  classical
  have hloc : ∀ w : Pl E, ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ (w ∈ S → ∀ z : Af E,
      (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → ∀ d : w.adicCompletion E, Valued.v d ≤ c →
        Valued.v (d * pLoc E w z) ≤ 1) := fun w => by
    by_cases hw : w ∈ S
    · obtain ⟨N, hN, hNL⟩ := hon w hw
      obtain ⟨c, hc0, hc⟩ := exists_val_bound hψ w hN hNL
      exact ⟨c, hc0, fun _ => hc⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose c hc0 hc using hloc
  obtain ⟨D, hD0, hD⟩ := exists_int_small S c fun w _ => hc0 w
  have he : algebraMap (𝓞 E) E D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hD0
  refine ⟨(fun y => algebraMap E (Af E) (algebraMap (𝓞 E) E D)⁻¹ * y) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)),
    (GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id), fun z hz => ?_⟩
  refine ⟨algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z, ?_, ?_⟩
  · refine SetLike.mem_coe.2 (GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_)
    have e : (algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z) w =
        algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E D) * pLoc E w z := rfl
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ S
    · exact hc w hw z hz _ (hD w hw)
    · rw [map_mul]
      calc _ ≤ 1 * 1 := mul_le_mul' (val_int_le_one w D) (val_le_one_of_cond (hS w hw) (hoff w hw) hz)
        _ = 1 := one_mul 1
  · change algebraMap E (Af E) (algebraMap (𝓞 E) E D)⁻¹ * (algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z) = z
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, one_mul]

end GlobalTheory.CompanionTheory.AnnLattice

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMultiplierTemperate
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

section Tempered

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem tempered_mul_entry {l m n : Type*} [Fintype m] {M : W → Matrix l m ℂ} {N : W → Matrix m n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j)
    (hN : ∀ i j, Function.HasTemperateGrowth fun x => N x i j) (i : l) (j : n) :
    Function.HasTemperateGrowth fun x => (M x * N x) i j := by
  simp only [Matrix.mul_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => (hM i k).mul (hN k j)

theorem tempered_trace {n : Type*} [Fintype n] {M : W → Matrix n n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j) :
    Function.HasTemperateGrowth fun x => (M x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => hM k k

end Tempered

variable {D : D7} {r : ℕ}

def quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) (X : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ :=
  -∑ τ, (tauE D τ c * Matrix.trace (a.map (tauE D τ) *
    ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ))))).re

theorem tempered_quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) :
    Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => ((quadForm D c G a X : ℝ) : ℂ) := by
  have hc : ∀ (τ : D.what₂.Tau) (i : Fin m) (j : Fin n),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => Matrix.of (X τ) i j := fun τ i j =>
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))).hasTemperateGrowth)
  have hs : ∀ (τ : D.what₂.Tau) (i : Fin n) (j : Fin m),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => (Matrix.of (X τ))ᴴ i j := fun τ i j =>
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ)))).hasTemperateGrowth)
  have hg : ∀ τ : D.what₂.Tau, Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ =>
      tauE D τ c * Matrix.trace (a.map (tauE D τ) *
        ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ)))) := fun τ =>
    (Function.HasTemperateGrowth.const _).mul (tempered_trace
      (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _)
        (tempered_mul_entry (hs τ)
          (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _) (hc τ)))))
  have hsum := Function.HasTemperateGrowth.sum (s := Finset.univ) fun τ (_ : τ ∈ Finset.univ) =>
    ((-(Complex.ofRealCLM.comp Complex.reCLM)).hasTemperateGrowth).comp (hg τ)
  convert hsum using 1
  funext X
  simp [quadForm]

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (infPart D (incA D e)) = tauE D τ e :=
  (hθ τ).1 e

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D l n) = compAt θ τ x * compAt θ τ y := by
  have := Matrix.map_mul (L := x) (M := y) (f := (θ τ).comp (infPart D))
  exact this

theorem compAt_adj {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (y : Mx D m n) :
    compAt θ τ (adj y) = (compAt θ τ y)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.Mem.VolExists.infEmb_sigR (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (hθ τ)]
  rfl

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (rat M) = M.map (tauE D τ) := by
  ext i j
  simp only [compAt, rat, Matrix.map_apply]
  exact theta_incA hθ τ _

theorem multM_eq_quadForm {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (V : HSp D) (a : HermE D r)
    (y : Mx D V.rank r) :
    multM θ α V a y = quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1
      (fun τ i j => compAt θ τ y i j) := by
  unfold multM lam quadForm
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, map_mul, theta_incA hθ, GlobalTheory.PhaseReal.theta_pair θ hθ]
  congr 3
  show _ * compAt θ τ (inner V y y) = _
  congr 1
  unfold GlobalTheory.StdUnn.inner
  rw [compAt_mul', compAt_mul', compAt_adj hθ, gA, compAt_rat hθ]
  rfl

theorem multM_tempered : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (α : D.host.F) (V : HSp D) (a : HermE D r), ∃ q : (D.what₂.Tau → Fin V.rank → Fin r → ℂ) → ℂ, q.HasTemperateGrowth ∧ ∀ y, ((multM θ α V a y : ℝ) : ℂ) = q (fun τ i j => compAt θ τ y i j) := by
  intro D r θ hθ α V a
  refine ⟨fun X => ((quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1 X : ℝ) : ℂ),
    tempered_quadForm D _ _ _, fun y => ?_⟩
  rw [multM_eq_quadForm hθ]

end GlobalTheory.CompanionTheory.WSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnvelopingStatement
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_mem_center_enveloping : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | exact GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | (intros; apply GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariantStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_convolution_split_centre_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ) (F : L2 (latticeGL E a) μ), F ∈ L2cusp μ → ∀ (t : ℝ) (x : GA E a), convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) = convR μ f (lift (latticeGL E a) F) x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | exact GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul <;> assumption)
end

