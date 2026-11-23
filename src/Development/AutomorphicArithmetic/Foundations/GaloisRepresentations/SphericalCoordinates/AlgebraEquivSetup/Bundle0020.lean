module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSiteFact
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LFun (KGL)

private lemma natCast_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (u : Plc E) (m : ℕ) (h : (m : 𝓞 E) ∈ u.asIdeal) :
    (m : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal := by
  have e : HeightOneSpectrum.under (𝓞 ℚ) (UpperTheory.Gal.CertificateRingHomMap.cj u) = HeightOneSpectrum.under (𝓞 ℚ) u :=
    GlobalTheory.DefU.ClassFin.under_conjSrc (F := ℚ) (E := E) _ (fun x => by simp) u
  have h2 : ((m : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) (UpperTheory.Gal.CertificateRingHomMap.cj u)).asIdeal) ↔
      ((m : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) u).asIdeal) := by rw [e]
  simpa [HeightOneSpectrum.under, Ideal.under_def, Ideal.mem_comap] using h2.2 (by simpa [HeightOneSpectrum.under, Ideal.under_def, Ideal.mem_comap] using h)

private lemma natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (u : Plc E) {q m : ℕ} (hm : m.Coprime q)
    (hq : (q : 𝓞 E) ∈ u.asIdeal) : (m : 𝓞 E) ∉ u.asIdeal := fun h => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have h1 : ((a * (m : ℤ) + b * (q : ℤ) : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← h1]
  push_cast
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hq)

private lemma comp_cj_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hI : UpperTheory.Gal.W2.Seed.IntConj) {n : ℕ} (g : GUf E n)
    (w : Plc E) (hs : sim g ∈ UpperTheory.Gal.CertificateRingHomMap.ZU) (h : comp w g ∈ KGL w (n := n)) :
    comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g ∈ KGL (UpperTheory.Gal.CertificateRingHomMap.cj w) (n := n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [e]
    exact one_mem _
  · exact (hI E n g w hn).1 hs h

private lemma inId_of_int {E : Type} [Field E] [NumberField E] (u : Plc E) {𝔟 : Ideal (𝓞 E)} {s : 𝓞 E} (hs : s ∈ 𝔟)
    (hu : s ∉ u.asIdeal) {y : u.adicCompletion E} (hy : y ∈ u.adicCompletionIntegers E) : InId u 𝔟 y := by
  refine (inId_iff_le u 𝔟 y).2 ⟨s, hs, ?_⟩
  have h1 : u.intValuation s = 1 :=
    le_antisymm (u.intValuation_le_one s) (not_lt.1 fun h => hu ((u.intValuation_lt_one_iff_mem s).1 h))
  rw [h1]
  exact hy

private lemma q_in_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : (q : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

private lemma ω_in_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

private lemma exists_not_mem_of_sup {E : Type} [Field E] [NumberField E] (w : Plc E) {𝔞 : Ideal (𝓞 E)} (h : 𝔞 ⊔ w.asIdeal = ⊤) :
    ∃ t ∈ 𝔞, t ∉ w.asIdeal := by
  by_contra hc
  push_neg at hc
  have h1 : 𝔞 ≤ w.asIdeal := hc
  rw [sup_eq_right.2 h1] at h
  exact w.isPrime.ne_top h

private lemma loc_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (hD : Dict) (hS : Sides) (hI : UpperTheory.Gal.W2.Seed.IntConj) (hC : UpperTheory.Gal.CertificateRingHomMap.LocComm) (F : Frame S) {x : E} (hx : Gen A x)
    {N : Lv p} {w : Plc E} (σ : Site S N w) (hw : IsSplitAt w) {y : GLw n w} (hy : y ∈ KGL w (n := n)) :
    F.j (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ σ.K₀ := by
  have hq : σ.q.Prime := σ.atp.prime
  have hG : A.Good σ.q := σ.good
  have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (q_in_uId S.D _ _)
  have hrw : A.ω - (σ.r : 𝓞 E) ∈ w.asIdeal := σ.atp.le (ω_in_uId S.D _ _)
  obtain ⟨-, hap, -, -, -, -⟩ := hC E n w hw
  have hqc : (σ.q : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := natCast_mem_cj w _ hqw
  obtain ⟨s1, -, -, -, -, -, s7⟩ := hS E A x hx σ.q hq hG.1 w hqw
  obtain ⟨-, hN, -, hsup, e, he⟩ := σ.lv
  have hω : (A.ω - (σ.r : 𝓞 E)) ^ e ∈ σ.𝔞 := he (Ideal.pow_mem_pow (ω_in_uId S.D _ _) e)
  have ht : ∃ t ∈ σ.𝔞, t ∉ w.asIdeal := exists_not_mem_of_sup w hsup
  have ht' : (A.ω - (σ.r : 𝓞 E)) ^ e ∉ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := fun h =>
    s1 ((s7 σ.r hrw _).2 ⟨hqc, (UpperTheory.Gal.CertificateRingHomMap.cj w).isPrime.mem_of_pow_mem e h⟩)
  have hs : ∀ (u : Plc E) (t : 𝓞 E), (σ.q : 𝓞 E) ∈ u.asIdeal → t ∈ σ.𝔞 → t ∉ u.asIdeal →
      ∃ s ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, s ∉ u.asIdeal := fun u t h1 h2 h3 =>
    ⟨_, Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) h2, fun h =>
      (u.isPrime.mem_or_mem h).elim (natCast_not_mem_of_coprime u hN h1) h3⟩
  have hb : Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := by
    intro h
    have h1 : ((N.1 : ℕ) : 𝓞 E) ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 := σ.mem
    rw [h, Ideal.mem_bot] at h1
    have h2 : N.1 = 0 := by exact_mod_cast h1
    have := N.2.1
    omega
  have hy' : comp w (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL w (n := n) := by
    rwa [UpperTheory.Gal.CertificateRingHomMap.comp_loc]
  have tri : ∀ u : Plc E, comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) = 1 ∨ ((σ.q : 𝓞 E) ∈ u.asIdeal ∧
      comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL u (n := n) ∧ ∃ s ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, s ∉ u.asIdeal) := by
    intro u
    by_cases h1 : u = w
    · rw [h1]
      obtain ⟨t, h2, h3⟩ := ht
      exact Or.inr ⟨hqw, hy', hs _ t hqw h2 h3⟩
    by_cases h2 : u = UpperTheory.Gal.CertificateRingHomMap.cj w
    · rw [h2]
      exact Or.inr ⟨hqc, comp_cj_mem hI _ _ (by simp [one_mem]) hy', hs _ _ hqc hω ht'⟩
    · exact Or.inl (UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y)
  have hK : ∀ u : Plc E, (σ.q : 𝓞 E) ∈ u.asIdeal → comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL u (n := n) →
      F.a u * comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) * (F.a u)⁻¹ ∈ KGL u (n := n) := fun u h1 h2 =>
    have ha := F.a_int u σ.q hq hG h1
    mul_mem (mul_mem ha h2) (inv_mem ha)
  refine (σ.isLev _).2 ⟨(hD E A n p S F _).2.1.2 fun u _ => ?_, ((hD E A n p S F _).2.2.1 _ hb).2 fun u _ i k => ?_⟩
  · rcases tri u with h | ⟨h1, h2, -⟩
    · simp [h, one_mem]
    · exact hK u h1 h2
  · rcases tri u with h | ⟨h1, h2, s, h3, h4⟩
    · have h0 : F.cmp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) = 1 := by simp [Frame.cmp, h]
      rw [h0]
      exact ⟨0, zero_mem _, by simp⟩
    · refine inId_of_int u h3 h4 ?_
      have hc := (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 (hK u h1 h2)).1 i k
      have hc' : F.cmp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) i k ∈ u.adicCompletionIntegers E := hc
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem hc' (one_mem _)
      · simpa using hc'

private lemma pr_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (hD : Dict) (F : Frame S) {N : Lv p} {w : Plc E} (σ : Site S N w) (hp : (p : 𝓞 E) ∉ w.asIdeal) {g : GUf E n}
    (hk : F.j g ∈ σ.K₀) : comp w g ∈ KGL w (n := n) := by
  have h1 := ((σ.isLev _).1 hk).1
  have h2 := (hD E A n p S F g).2.1.1 h1 w hp
  have ha := F.a_int w σ.q σ.atp.prime σ.good (σ.atp.le (q_in_uId S.D _ _))
  have e : comp w g = (F.a w)⁻¹ * (F.a w * comp w g * (F.a w)⁻¹) * F.a w := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem ha) h2) ha

theorem UpperTheory.Gal.W2.Seed.pSiteFact :
    Dict → Sides → UpperTheory.Gal.W2.Seed.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → SiteFact := by
  intro hD hS hI hC E _ _ _ A n p _ S F x hx N w σ L hL
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · rw [hL.2 y]
    exact loc_mem hD hS hI hC F hx σ w.2.1 hy
  · obtain ⟨g, rfl⟩ := F.surj k
    rw [hL.1 g]
    exact pr_mem hD F σ w.2.2 hk
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTyFact
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.W2.Seed.mem_cj_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (hG : UpperTheory.Gal.CertificateRingHomMap.LocComm)
    {q : ℕ} [Fact q.Prime] {w : Plc E} (hw : IsSplitAt w) (h : (q : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal := by
  by_contra hn
  have hap : GlobalTheory.Cong.Apart w (CertificateRingHomMap.cj w) := UpperTheory.Gal.W2.Seed.apart_of_not_mem hn h
  obtain ⟨-, -, -, hs, hcc, -⟩ := hG E n w hw
  exact ((hG E n (CertificateRingHomMap.cj w) hs).2.1 w).1 hap |>.2 hcc.symm

theorem UpperTheory.Gal.W2.Seed.pTyFact :
    FacEq → LevSec → LevFact → AtApart → CongGrpEx → Denom → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → TyFact := by
  intro hF hS hLF hA hC hD hc hG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N _ _ L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have hL : ∀ w, L w = fac F.tr hc w := fun w => (hF E A n p S F hc w).2 _ (hTy.fac w)
  haveI : Fact r.Prime := ⟨hAux.prime⟩
  have hK1 : ∀ k, (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) := by
    intro k
    constructor
    · rintro ⟨k', rfl, h⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev] at h
      rw [hj]
      exact (hS E A n p S F.tr V.S _ hOff.1).1 k' h
    · intro h
      refine ⟨F.tr.sec k, by rw [hj]; exact F.tr.j_sec k, ?_⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev]
      exact h
  have hKiff : ∀ k, k ∈ Ty.K ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1 :=
    fun k => (hTy.K_iff k).trans (and_congr_left' (hK1 k))
  have hIK : ∀ w : Plc E, Iw n w ≤ GlobalTheory.LFun.KGL w (n := n) := fun w => by
    obtain ⟨K, -, -, -, -, -, -, h⟩ := hC E n 1 one_pos w
    exact h
  have hnS : ∀ w ∈ W, w.1 ∉ V.S ∧ CertificateRingHomMap.cj w.1 ∉ V.S := fun w hw' =>
    ⟨fun h => hAux.off _ h (hAux.half.above w hw'),
      fun h => hAux.off _ h (mem_cj_of_mem n hG w.2.1 (hAux.half.above w hw'))⟩
  have hAw₀ : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → GlobalTheory.Cong.Apart w₀ w.1 := fun w h1 h2 =>
    ((hG E n w.1 w.2.1).2.1 w₀).2 ⟨fun e => h1 (e ▸ V.shape.mem), fun e => h2 (e ▸ V.shape.mem)⟩
  have hAp : ∀ w w' : Spl E p, GlobalTheory.Cong.Apart w.1 w'.1 → (L w).Apart (L w') := fun w w' h => by
    rw [hL, hL]
    exact (hA E A n p S F.tr hc w.1 w.2.1 w.2.2).2 w'.1 w'.2.1 w'.2.2 h
  have hLF' : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S →
      (L w).Fact (F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw))) (GlobalTheory.LFun.KGL w.1 (n := n)) := fun w h1 h2 => by
    rw [hL]
    exact (hLF E A n p S F.tr hc V.S (CertificateRingHomMap.levT V.Kw) w.1 w.2.1 w.2.2 h2).2 h1
  have hTyAp : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → Ty.L.Apart (L w) := fun w h1 h2 => by
    rw [hTy.L_eq]
    exact hAp ⟨w₀, hw⟩ w (hAw₀ w h1 h2)
  refine ⟨fun w hw' => ⟨⟨fun y hy => ?_, fun g hg => ((hKiff g).1 hg).2 w hw'⟩, hTyAp w (hnS w hw').1 (hnS w hw').2,
      fun w' hw'' e => hAp w w' (hAux.half.apart w hw' w' hw'' e)⟩,
    fun w h1 h2 h3 => ⟨⟨fun y hy => (hKiff _).2 ⟨(hLF' w h1 h2).1 y hy, fun u hu => ?_⟩,
      fun g hg => (hLF' w h1 h2).2 g ((hKiff g).1 hg).1⟩, hTyAp w h1 h2⟩, ?_⟩
  · refine (hKiff _).2 ⟨(hLF' w (hnS w hw').1 (hnS w hw').2).1 y (hIK w.1 hy), fun w' hw'' => ?_⟩
    by_cases e : w = w'
    · subst e
      rw [(L w).pr_loc]
      exact hy
    · rw [(hAp w' w (hAux.half.apart w' hw'' w hw' (Ne.symm e))).1 y]
      exact one_mem _
  · rw [(hAp w u (h3 u hu)).2 y]
    exact one_mem _
  · haveI : (Ty.K₀.subgroupOf Ty.K).FiniteIndex := ⟨Ty.idx⟩
    haveI : Fintype (Ty.K ⧸ Ty.K₀.subgroupOf Ty.K) := Fintype.ofFinite _
    choose c hc0 hcp hcv using fun q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K => hD p S.D S.G S.L (q.out : S.G.GAf)
    refine ⟨∏ q, c q, Finset.prod_pos fun q _ => hc0 q, Nat.Coprime.prod_left fun q _ => hcp q, fun k hk v hv => ?_⟩
    obtain ⟨q, hq⟩ : ∃ q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K, q = QuotientGroup.mk ⟨k, hk⟩ := ⟨_, rfl⟩
    have hu : (q.out : S.G.GAf)⁻¹ * k ∈ Ty.K₀ := by
      have : q.out⁻¹ * ⟨k, hk⟩ ∈ Ty.K₀.subgroupOf Ty.K := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hq]
      simpa [Subgroup.mem_subgroupOf] using this
    have hint : Integ S.L ((q.out : S.G.GAf)⁻¹ * k) := integ_of_mem (KN_anti (one_dvd N.1) (hTy.K₀_eq ▸ hu))
    have hk' : k = (q.out : S.G.GAf) * ((q.out : S.G.GAf)⁻¹ * k) := by group
    have h1 := hcv q _ (hint v hv)
    rw [hk', map_mul, Module.End.mul_apply, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ q), mul_comm, mul_smul]
    exact nsmul_mem h1 _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds
section
namespace UpperTheory.Gal.W2.Seed

theorem BarEx_holds : BarEx := pBarEx
theorem CEx_holds : CEx := pCEx
theorem CodiffGen_holds : CodiffGen := pCodiffGen
theorem DeltaEx_holds : DeltaEx := pDeltaEx
theorem DiagTrace_holds : DiagTrace := pDiagTrace
theorem FormOKSt_holds : FormOKSt := pFormOKSt
theorem FormPerfSt_holds : FormPerfSt := pFormPerfSt
theorem HdSign_holds : HdSign := pHdSign
theorem IdemEx_holds : IdemEx := pIdemEx
theorem LiftEx_holds : LiftEx := pLiftEx
theorem OrbEx_holds : OrbEx := pOrbEx
theorem PerfCof_holds : PerfCof := pPerfCof
theorem PerfOf_holds : PerfOf := pPerfOf
theorem QuadEx_holds : QuadEx := pQuadEx
theorem RepAdj_holds : RepAdj := pRepAdj
theorem RepEx_holds : RepEx := pRepEx
theorem RepLaws_holds : RepLaws := pRepLaws
theorem SetupBasic_holds : SetupBasic := pSetupBasic
theorem TraceType_holds : TraceType := pTraceType
theorem UEx_holds : UEx := pUEx
theorem UnitMod_holds : UnitMod := pUnitMod
theorem CodiffUnit_holds : CodiffUnit := pCodiffUnit UnitMod_holds
theorem FormCoord_holds : FormCoord := pFormCoord TraceType_holds
theorem KqEx_holds : KqEx := pKqEx TraceType_holds
theorem Orient_holds : Orient := pOrient TraceType_holds HdSign_holds
theorem RealIso_holds : RealIso := pRealIso TraceType_holds
theorem SigSt_holds : SigSt := pSigSt HdSign_holds
theorem AtPEx_holds : AtPEx := pAtPEx KqEx_holds UEx_holds OrbEx_holds LiftEx_holds
theorem DomSt_holds : DomSt := pDomSt TraceType_holds RealIso_holds FormCoord_holds HdSign_holds DiagTrace_holds
theorem PosGen_holds : PosGen := pPosGen CodiffUnit_holds
theorem RealGen_holds : RealGen := pRealGen CodiffGen_holds CodiffUnit_holds
theorem SetupEx_holds : SetupEx := pSetupEx FormOKSt_holds FormPerfSt_holds SigSt_holds DomSt_holds AtPEx_holds RepEx_holds RepLaws_holds RepAdj_holds Orient_holds

end UpperTheory.Gal.W2.Seed
end

