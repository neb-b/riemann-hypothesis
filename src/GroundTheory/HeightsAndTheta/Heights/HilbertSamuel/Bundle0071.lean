module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedVOfGeneratedMod
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenerationOfH1GenAmple

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chartExp (c : ∀ k, ι k) (n : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then n q.1 else 0

def chartMon (c : ∀ k, ι k) (n : K → ℕ) : MRingOver S ι :=
  monomial (chartExp c n) 1

theorem chartMon_homog (c : ∀ k, ι k) (n : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (chartMon (S := S) c n) n :=
  GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => by simp [chartExp]

theorem chartMon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (n : K → ℕ) :
    chartMon (S := S) c n ∈ KH.cellMon S I := by
  unfold chartMon
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  have hq' : q.2 = c q.1 := by
    by_contra h
    simp [chartExp, h] at hq
  obtain ⟨k, i⟩ := q
  simp only at hq'
  subst hq'
  exact ⟨k, c k, hc k, rfl⟩

variable {V : Ideal (MRingOver S ι)}

theorem smul_quot (f : MRingOver S ι) (m : MRingOver S ι ⧸ V) : f • m = Ideal.Quotient.mk V f * m := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
  rfl

theorem smul_mul_eq_mul_smul {T : Submonoid (MRingOver S ι)} (p : MRingOver S ι)
    (x y : LocalizedModule T (MRingOver S ι ⧸ V)) : (p • x) * y = x * (p • y) := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.smul'_mk,
        LocalizedModule.mk_mul_mk, smul_mul_assoc, mul_smul_comm]

theorem generatedV_of_generatedMod {d : K → ℤ} (h : GeneratedMod S ι (KH.quotPart S V) d) :
    KH.GeneratedV S V d := by
  classical
  intro I
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  let dp : K → ℕ := fun k => (d k).toNat
  let dm : K → ℕ := fun k => (-d k).toNat
  have hd : ∀ k, (dp k : ℤ) - dm k = d k := fun k => Int.toNat_sub_toNat_neg (d k)
  let P : MRingOver S ι := chartMon c dp
  let Q : MRingOver S ι := chartMon c dm
  have hP : P ∈ KH.cellMon S I.1 := chartMon_mem hc dp
  have hQ : Q ∈ KH.cellMon S I.1 := chartMon_mem hc dm
  have hpart : ∀ (f : MRingOver S ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a →
      Ideal.Quotient.mk V f ∈ KH.quotPart S V (fun k => (a k : ℤ)) := fun f a hf =>
    Submodule.subset_span ⟨f, ⟨fun k => Int.natCast_nonneg _, by simpa using hf⟩, rfl⟩
  let x : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V P) ⟨Q, hQ⟩
  have hx : x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) d := by
    refine GenTwistGenerated.mk_mem_locPart _ _ dm (chartMon_homog c dm) ?_
    have e : (d + fun k => (dm k : ℤ)) = fun k => (dp k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply]
      omega
    rw [e]
    exact hpart P dp (chartMon_homog c dp)
  obtain ⟨t, a, r, p, z, ht, hta, hpa, hz, htx⟩ := h I x hx
  let w : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V Q) ⟨t * P, mul_mem ht hP⟩
  refine ⟨r, z, fun j => p j • w, hz, fun j => ?_, ?_⟩
  · have e0 : p j • Ideal.Quotient.mk V Q = Ideal.Quotient.mk V (p j * Q) := by
      rw [smul_quot, map_mul]
    have e1 : p j • w =
        LocalizedModule.mk (Ideal.Quotient.mk V (p j * Q)) ⟨t * P, mul_mem ht hP⟩ :=
      (LocalizedModule.smul'_mk ..).trans (congrArg (fun m => LocalizedModule.mk m _) e0)
    refine (congrArg (· ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-d)) e1).mpr ?_
    refine GenTwistGenerated.mk_mem_locPart _ _ (a + dp)
      (GenTwistGenerated.isMultiHomog_mul hta (chartMon_homog c dp)) ?_
    have e2 : (-d + fun k => ((a + dp) k : ℤ)) = fun k => ((a + dm) k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply, Pi.neg_apply, Nat.cast_add]
      omega
    rw [e2]
    exact hpart _ _ (GenTwistGenerated.isMultiHomog_mul (hpa j) (chartMon_homog c dm))
  · calc ∑ j, p j • w * z j I = ∑ j, w * (p j • z j I) :=
          Finset.sum_congr rfl fun j _ => smul_mul_eq_mul_smul (p j) w (z j I)
      _ = w * (t • x) := by rw [← Finset.mul_sum, htx]
      _ = 1 := by
        have e3 : Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P) =
            ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V)) := by
          rw [Submonoid.smul_def, smul_quot, smul_quot, mul_one]
          simp only [Submonoid.coe_mul, map_mul]
          ring
        calc w * (t • x)
            = w * LocalizedModule.mk (t • Ideal.Quotient.mk V P) ⟨Q, hQ⟩ :=
              congrArg (w * ·) (LocalizedModule.smul'_mk ..)
          _ = LocalizedModule.mk (Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P))
                (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) := LocalizedModule.mk_mul_mk
          _ = LocalizedModule.mk ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) •
                (1 : MRingOver S ι ⧸ V)) (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) :=
              congrArg (fun m => LocalizedModule.mk m _) e3
          _ = LocalizedModule.mk 1 1 := LocalizedModule.mk_cancel _ _
          _ = 1 := OreLocalization.one_def.symm

end GenerationOfH1GenAmple

theorem GenerationOfH1GenAmple.proof (hQ : QuotPartGraded.Statement) : GenerationOfH1GenAmple.Statement := by
  intro S _ K _ _ ι _ _ V N hV hH e
  have hann : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ V) := fun v hv =>
    Module.mem_annihilator.mpr fun m => by
      rw [GenerationOfH1GenAmple.smul_quot, Ideal.Quotient.eq_zero_iff_mem.mpr hv, zero_mul]
  obtain ⟨c₁, hc₁⟩ := hH (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance (hQ S K ι V hV) hann e
  exact ⟨c₁, fun c hc => GenerationOfH1GenAmple.generatedV_of_generatedMod (hc₁ c hc).2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LeLimsupDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

namespace ArithmeticVolumeBigDimensionOne

theorem le_limsup_div {u : ℕ → ℝ} {T C C' : ℝ}
    (hlo : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * T - C ≤ u n) (hup : ∀ n : ℕ, u n ≤ C' * ((n : ℝ) + 1)) :
    T ≤ limsup (fun n : ℕ => u n / n) atTop := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => u n / n) := by
    refine isBoundedUnder_of_eventually_le (a := 2 * |C'|) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by linarith)]
    calc u n ≤ C' * ((n : ℝ) + 1) := hup n
      _ ≤ |C'| * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ 2 * |C'| * n := by nlinarith [abs_nonneg C']
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have key : T - ε ≤ limsup (fun n : ℕ => u n / n) atTop := by
    refine le_limsup_of_frequently_le (Eventually.frequently ?_) hb
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    rw [le_div_iff₀ (by linarith)]
    have hC : C < n * ε := (div_lt_iff₀ hε).mp (hN.trans_le hnN)
    have hl := hlo n hn1
    nlinarith
  linarith

end ArithmeticVolumeBigDimensionOne

theorem ArithmeticVolumeBigDimensionOne.proof (hP : PackingStatement) (hL : CurveSmallCountLower.Statement) :
    ArithmeticVolumeBigDimensionOne.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII har hb hP0 hs hnef hc
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII har hb hs.1 hc
  obtain ⟨-, C', hC'⟩ := hP K ι Ω y 0 A (chartLat y A.a) har hb hs.1
    (fun τ => SmallSectionPointHeight.chartLat_le_chartLatNm y A.a τ)
  have e : arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0 =
      limsup (fun n : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n / n) atTop := by
    unfold arVolP
    congr 1
    simp
  rw [e]
  exact ArithmeticVolumeBigDimensionOne.le_limsup_div hC (fun n => by simpa using hC' n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace BirationalModelExists

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_zero' (a : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_add' {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

theorem isMultiHomog_neg' {f : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (-f) a := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

theorem aeval_scale {S : Type*} [CommRing S] [Algebra ℤ S] {g : MRing ι} {a : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a)
    (z : (Σ k, ι k) → S) (u : K → S) :
    aeval (fun p => z p * u p.1) g = aeval z g * ∏ k, u k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (z p * u p.1) ^ m p = (∏ p, z p ^ m p) * ∏ k, u k ^ a k := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, u k ^ m ⟨k, i⟩ = u k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem hom_aeval {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (z : (Σ k, ι k) → S) (g : MRing ι) :
    φ (aeval z g) = aeval (fun p => φ (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

variable (P : Ideal (MRing ι)) [P.IsPrime]

def coordClass (p : Σ k, ι k) : FractionRing (MRing ι ⧸ P) :=
  algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (X p))

theorem aeval_coordClass (g : MRing ι) :
    aeval (coordClass P) g = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) := by
  set_option synthInstance.maxHeartbeats 200000 in
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (aeval (coordClass P)), map_add (Ideal.Quotient.mk P),
      map_add (algebraMap _ _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, coordClass]

theorem aeval_coordClass_eq_zero (g : MRing ι) : aeval (coordClass P) g = 0 ↔ g ∈ P := by
  rw [aeval_coordClass, map_eq_zero_iff _ (IsFractionRing.injective (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))),
    Ideal.Quotient.eq_zero_iff_mem]

def fnField : Subfield (FractionRing (MRing ι ⧸ P)) where
  carrier := {s | ∃ (d : K → ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧
    aeval (coordClass P) h ≠ 0 ∧ aeval (coordClass P) g = s * aeval (coordClass P) h}
  zero_mem' := ⟨0, 0, 1, isMultiHomog_zero' 0, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp, by simp⟩
  one_mem' := ⟨0, 1, 1, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp, by simp⟩
  add_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * h' + h * g', h * h',
      isMultiHomog_add' (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hh') (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hh hg'), ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hh hh',
      by simp [h0, h0'], ?_⟩
    simp only [map_add (f := _), map_mul, hs, ht]
    ring
  mul_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * g', h * h', ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hg', ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hh hh', by simp [h0, h0'], ?_⟩
    simp only [map_mul, hs, ht]
    ring
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    exact ⟨d, -g, h, isMultiHomog_neg' hg, hh, h0, by simp [hs]⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    by_cases s0 : s = 0
    · subst s0
      exact ⟨0, 0, 1, isMultiHomog_zero' 0, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, ?_, ?_⟩
      · rw [hs]
        exact mul_ne_zero s0 h0
      · rw [hs, ← mul_assoc, inv_mul_cancel₀ s0, one_mul]

variable {P}

theorem coordClass_ne_zero {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ P) : coordClass P p ≠ 0 := by
  have h := (aeval_coordClass_eq_zero P (X p)).not.2 hp
  rwa [aeval_X] at h


open Classical in
def birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (p : Σ k, ι k) : fnField P :=
  ⟨coordClass P p / coordClass P ⟨p.1, c p.1⟩,
    ⟨Pi.single p.1 1, X p, X ⟨p.1, c p.1⟩, isMultiHomog_X' p.1 p.2, isMultiHomog_X' p.1 (c p.1),
      by rw [aeval_X]; exact coordClass_ne_zero (hc p.1),
      by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (coordClass_ne_zero (hc p.1))]⟩⟩

theorem coe_aeval_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) {g : MRing ι} {a : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ((aeval (birPoint c hc) g : fnField P) : FractionRing (MRing ι ⧸ P)) =
      aeval (coordClass P) g * ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k := by
  have h := hom_aeval (fnField P).subtype (birPoint c hc) g
  have hf : (fun p => (fnField P).subtype (birPoint c hc p)) =
      fun p => coordClass P p * (fun k => (coordClass P ⟨k, c k⟩)⁻¹) p.1 := by
    funext p
    exact div_eq_mul_inv _ _
  rw [hf] at h
  exact h.trans (aeval_scale hg (coordClass P) fun k => (coordClass P ⟨k, c k⟩)⁻¹)

theorem prod_inv_ne_zero (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (a : K → ℕ) :
    ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (coordClass_ne_zero (hc k)))

theorem eval_mConeMap_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (f : MRing ι) :
    eval₂ (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩) (mConeMap (birPoint c hc) f) =
      aeval (coordClass P) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have e1 := map_intCast (eval₂Hom (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩)) a
    simp only [coe_eval₂Hom] at e1
    simpa [mConeMap] using e1
  | add p q hp hq => simp only [map_add (f := _), eval₂_add, hp, hq]
  | mul_X p n hp =>
    have hX : mConeMap (birPoint c hc) (X n) = C (birPoint c hc n) * X n.1 := by simp [mConeMap]
    have e : (fnField P).subtype (birPoint c hc n) * coordClass P ⟨n.1, c n.1⟩ = coordClass P n :=
      div_mul_cancel₀ _ (coordClass_ne_zero (hc n.1))
    rw [map_mul, eval₂_mul, hp, hX, eval₂_mul, eval₂_C, eval₂_X, map_mul, aeval_X, e]

theorem mCoordIdeal_birPoint (hP : IsMultiHomogIdeal P) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) : mCoordIdeal (birPoint c hc) = P := by
  apply le_antisymm
  · intro f hf
    rw [mCoordIdeal, RingHom.mem_ker] at hf
    have h := eval_mConeMap_birPoint c hc f
    rw [hf, eval₂_zero] at h
    exact (aeval_coordClass_eq_zero P f).1 h.symm
  · obtain ⟨S, hS, rfl⟩ := hP
    rw [Ideal.span_le]
    intro g hgS
    obtain ⟨a, ha⟩ := hS g hgS
    have hgP : aeval (coordClass (Ideal.span S)) g = 0 :=
      (aeval_coordClass_eq_zero _ g).2 (Ideal.subset_span hgS)
    have hy : aeval (birPoint c hc) g = 0 := by
      apply Subtype.ext
      rw [coe_aeval_birPoint c hc ha, hgP, zero_mul]
      rfl
    show g ∈ RingHom.ker (mConeMap (birPoint c hc))
    rw [RingHom.mem_ker]
    show aeval (fun p => C (birPoint c hc p) * X p.1) g = 0
    refine (aeval_scale ha (fun p => C (birPoint c hc p)) X).trans ?_
    rw [← hom_aeval C, hy, map_zero, zero_mul]

theorem birational_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) :
    Birational (birPoint c hc) := by
  rintro ⟨s, d, g, h, hg, hh, h0, hs⟩
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · intro h'
    have := congrArg (fun t : fnField P => (t : FractionRing (MRing ι ⧸ P))) h'
    simp only [coe_aeval_birPoint c hc hh, ZeroMemClass.coe_zero] at this
    exact mul_ne_zero h0 (prod_inv_ne_zero c hc d) this
  · apply Subtype.ext
    rw [Subfield.coe_mul, coe_aeval_birPoint c hc hg, coe_aeval_birPoint c hc hh]
    show _ = s * _
    rw [hs, mul_assoc]

end BirationalModelExists

theorem BirationalModelExists.proof : BirationalModelExists.Statement := by
  intro K _ ι _ P d hP
  obtain ⟨_, ⟨hprime, hhom, hrel⟩, _, _⟩ := hP
  choose c hc using hrel
  have := hprime
  exact ⟨BirationalModelExists.fnField P, inferInstance, BirationalModelExists.birPoint c hc,
    BirationalModelExists.mCoordIdeal_birPoint hhom c hc, BirationalModelExists.birational_birPoint c hc⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedProductNonneg

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_ratDiv {V : Ideal (MRingOver F ι)} {f g : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (hW : W ∈ (ratDiv V f g).support) : V ≤ W := by
  have key : ∀ s : MRingOver F ι, ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → V ≤ W := by
    intro s hs
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hs
    rw [Finsupp.ofSupportFinite_coe] at hs
    split_ifs at hs with h
    · exact le_sup_left.trans h.1.1.2
    · exact absurd rfl hs
  rw [Finsupp.mem_support_iff, ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g fun h => hW ?_
    rw [hf, h]
    simp
  · exact key f hf

end GeneratedProductNonneg

theorem GeneratedProductNonneg.proof (hR : GeneratedRestrict.Statement)
    (hE : GeneratedEffectiveSection.Statement) : GeneratedProductNonneg.Statement := by
  classical
  intro F _ K _ _ ι _ _ I V m β hI hV hgen
  induction m generalizing V with
  | zero =>
    choose i hi using hV.1.2.2
    rw [hI.1 V β i hV hi]
    exact Int.natCast_nonneg _
  | succ m ih =>
    obtain ⟨f, g, hs, heff⟩ := hE F K ι V (β (Fin.last m)) hV.1 (hgen (Fin.last m))
    have e := hI.2 V m (Fin.init β) (β (Fin.last m)) f g hV hs
    rw [Fin.snoc_init_self] at e
    rw [e, cycEval]
    refine Finsupp.sum_nonneg fun W hW => mul_nonneg (heff W) ?_
    obtain ⟨α, γ, hf, hg, hfV, hgV, -⟩ := hs
    have hWm : IsProjVarF W m := KleimanNefF.isProjVarF_of_mem_support hV
      ((NumbersDVR.VocabMultiHomog.proof F K ι f α).1 hf) ((NumbersDVR.VocabMultiHomog.proof F K ι g γ).1 hg)
      hfV hgV hW
    have hle : V ≤ W := GeneratedProductNonneg.le_of_mem_support_ratDiv hW
    exact ih W (Fin.init β) hWm fun j => hR F K ι V W _ hle (hgen _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

