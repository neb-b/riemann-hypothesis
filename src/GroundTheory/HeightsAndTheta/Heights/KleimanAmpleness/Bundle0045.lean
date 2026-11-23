module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneBlockPnPt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelCurvesLift.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
        mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P →
          ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
            baseComap F k₀ e W = P

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutNonempty
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coe_aeval_ratio_mem_idealMod {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) {j : Fin (N + 1)} (hj : x j ≠ 0)
    {p : Poly k N} (hp : p ∈ pp) :
    ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) ∈
      idealMod (x := x) pp (singleChart hj) := by
  rw [← sum_homogeneousComponent p]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun d _ => Submodule.subset_span ?_
  exact ⟨homogeneousComponent d p, X j ^ d, d, hh p hp d,
    pow_mem (X_mem_monos (Finset.mem_singleton_self j)) d, homogeneousComponent_isHomogeneous d p,
    isHomogeneous_X_pow j d, coe_aeval_ratio' hj (homogeneousComponent_isHomogeneous d p)⟩

theorem coe_aeval_ratio_mul_mem_span {L : SubSystem k x Ω} {s : Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    {z : Poly k N} (hz : z ∈ zeroIdeal L s) {δ : Ω} (hδ : δ ∈ L.sub (singleChart hj)) :
    ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * δ ∈
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hfc, hf⟩ := hf
    obtain ⟨o, ho, he⟩ := hf (singleChart hj) δ hδ
    rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    rw [Submodule.mem_span_singleton]
    refine ⟨b, ?_⟩
    rw [coe_aeval_ratio hj hfc, chartRing_smul_def, div_mul_eq_mul_div, he, chartRing_smul_def,
      zpow_natCast]
    field_simp
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), Subalgebra.coe_add, add_mul]
    exact Submodule.add_mem _ ha hb
  | smul g z _ hz =>
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, mul_assoc]
    exact Submodule.smul_mem _ (aeval (ratio (S := k) hj) g) hz

theorem sub_le_twist_sup_span {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) (L : LineBundle k x) (s : Ω)
    (hmin : ∀ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∀ i, (X i : Poly k N) ∈ qq)
    (j : Fin (N + 1)) (hj : x j ≠ 0) :
    L.sub (singleChart hj) ≤ (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  have hrad : (X j : Poly k N) ∈ (pp ⊔ zeroIdeal L.toSubSystem s).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr fun qq hq => hmin qq hq j
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hm
  intro ℓ hℓ
  have h1 : ((aeval (ratio (S := k) hj) ((X j : Poly k N) ^ m) : chartRing k x (singleChart hj)) : Ω) = 1 := by
    rw [map_pow, aeval_X, SubmonoidClass.coe_pow]
    change (x j / x j) ^ m = 1
    rw [div_self hj, one_pow]
  have hsplit : ℓ = ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) * ℓ +
      ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * ℓ := by
    rw [← add_mul, ← Subalgebra.coe_add, ← map_add (f := _), hpz, h1, one_mul]
  rw [hsplit]
  refine Submodule.add_mem_sup (Submodule.subset_span ?_) (coe_aeval_ratio_mul_mem_span hj hz hℓ)
  exact ⟨_, coe_aeval_ratio_mem_idealMod hh hj hp, ℓ, hℓ, rfl⟩

end Chart

theorem CutNonempty.proof (hO : CutOneGenerator.Statement.{u, w}) : CutNonempty.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs _
  by_contra hne
  push Not at hne
  exact hO k Ω N x n pp L s hW hL hs (sub_le_twist_sup_span hW.homog L s hne)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutOneGenerator
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace CutOneGenerator

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem mem_sub_of_mem_secs {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {t : E} (ht : t ∈ H.secs) (I : Chart z) :
    t ∈ H.sub I :=
  (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp ht I)

theorem mem_chartRing_of_mem_idealMod {pp : Ideal (Poly k N)} {I : Chart x} {a : Ω}
    (ha : a ∈ idealMod (x := x) pp I) : a ∈ chartRing k x I := by
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨f, s, e, -, hs, hf, hse, rfl⟩ := ha; exact ⟨f, s, e, hs, hf, hse, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact mul_mem c.2 ha

variable {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {Q : SubSystem k x Ω} {Q' : SubSystem k y K'} {ρ : Ω → K'}

theorem restrict_zero (hR : RestrictData Q hxy Q' ρ) (J : Chart y) : ρ 0 = 0 := by
  have := hR.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem exists_restrict_mul (hR : RestrictData Q hxy Q' ρ) (J : Chart y) {c q : Ω}
    (hc : c ∈ chartRing k x (liftChart hxy J)) (hq : q ∈ Q.sub (liftChart hxy J)) :
    ∃ b ∈ chartRing k y J, ρ (c * q) = b * ρ q := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := hc
  exact ⟨_, ⟨f, t, e, ht, hf, hte, rfl⟩, hR.smul J q hq f t e ht hf hte⟩

theorem restrict_twist_eq_zero (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {z : Ω}
    (hz : z ∈ (Q.twist (idealSys x pp)).sub (liftChart hxy J)) :
    z ∈ Q.sub (liftChart hxy J) ∧ ρ z = 0 := by
  have hgen : ∀ w ∈ Q.sub (liftChart hxy J), ∀ q ∈ idealMod (x := x) pp (liftChart hxy J),
      q * w ∈ Q.sub (liftChart hxy J) ∧ ρ (q * w) = 0 := by
    intro w hw q hq
    have hmw : ∀ a ∈ idealMod (x := x) pp (liftChart hxy J), a * w ∈ Q.sub (liftChart hxy J) :=
      fun a ha => (Q.sub _).smul_mem
        ⟨a, mem_chartRing_of_mem_idealMod (pp := pp) (I := liftChart hxy J) ha⟩ hw
    refine ⟨hmw q hq, ?_⟩
    induction hq using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f, t, e, hfp, ht, hf, hte, rfl⟩ := ha
      rw [hR.smul J w hw f t e ht hf hte,
        (mem_primeOf_of_isHomogeneous y hf).mp (hpp ▸ hfp), zero_div, zero_mul]
    | zero => rw [zero_mul]; exact restrict_zero hR J
    | add a b ha hb iha ihb =>
      rw [add_mul, hR.add J _ (hmw a ha) _ (hmw b hb), iha, ihb, add_zero]
    | smul c a ha iha =>
      obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 (hmw a ha)
      rw [chartRing_smul_def, mul_assoc, hb, iha, mul_zero]
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨q, hq, w, hw, rfl⟩ := hz; exact hgen w hw q hq
  | zero => exact ⟨zero_mem _, restrict_zero hR J⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, by rw [hR.add J a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
  | smul c a _ ha =>
    refine ⟨(Q.sub _).smul_mem c ha.1, ?_⟩
    obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 ha.1
    rw [chartRing_smul_def]
    erw [hb]
    rw [ha.2, mul_zero]

theorem exists_eq_mul_of_le (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {s : Ω} (hs : s ∈ Q.sub (liftChart hxy J))
    (hle : Q.sub (liftChart hxy J) ≤ (Q.twist (idealSys x pp)).sub (liftChart hxy J) ⊔
      Submodule.span (chartRing k x (liftChart hxy J)) {s}) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ b ∈ chartRing k y J, t = b * ρ s := by
  rw [← hR.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨q, hq, rfl⟩ := ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (hle hq)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨hu', hu0⟩ := restrict_twist_eq_zero hR hpp J hu
    obtain ⟨b, hb, he⟩ := exists_restrict_mul hR J a.2 hs
    refine ⟨b, hb, ?_⟩
    rw [hR.add J u hu' _ ((Q.sub _).smul_mem a hs), hu0, zero_add, chartRing_smul_def, he]
  | zero => exact ⟨0, zero_mem _, (zero_mul _).symm⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨b, hb, rfl⟩ := ht
    obtain ⟨b', hb', rfl⟩ := ht'
    exact ⟨b + b', add_mem hb hb', (add_mul _ _ _).symm⟩
  | smul c t _ ht =>
    obtain ⟨b, hb, rfl⟩ := ht
    exact ⟨c * b, mul_mem c.2 hb, by rw [chartRing_smul_def, mul_assoc]⟩

theorem exists_algHom_ker_eq {R : Type w} [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] :
    ∃ (F : Type w) (_ : Field F) (_ : Algebra k F) (ψ : R →ₐ[k] F), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  rw [RingHom.mem_ker]
  change algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end CutOneGenerator


open CutOneGenerator in
theorem CutOneGenerator.proof (hG : GlobalFunctionsIntegral.Statement.{u, w}) :
    CutOneGenerator.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hgen
  obtain ⟨r, h, hV⟩ := hL
  obtain ⟨j, hXj⟩ := hW.relevant
  have hxj : x j ≠ 0 := by
    intro h0
    apply hXj
    apply hW.le
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j), aeval_X, h0]
  obtain ⟨hprime, hpt⟩ :=
    PrimeFiltration.Point.proof k Ω N x pp hW.isPrime hW.homog hW.le j hxj hXj
  obtain ⟨K', _, _, ψ, hker⟩ := @exists_algHom_ker_eq k _ _ _ _ (chartPrime pp hxj) hprime
  set y : Fin (N + 1) → K' := fun i => ψ (ratio hxj i) with hy
  have hpy : primeOf (S := k) y = pp := hpt K' ψ hker
  have hy0 : y j ≠ 0 := by
    have e : ratio (S := k) hxj j = 1 := Subtype.ext (div_self hxj)
    show ψ (ratio hxj j) ≠ 0
    rw [e, map_one]
    exact one_ne_zero
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i hyi hxi
    apply hyi
    have e : ratio (S := k) hxj i = 0 := Subtype.ext (by show x i / x j = 0; rw [hxi, zero_div])
    show ψ (ratio hxj i) = 0
    rw [e, map_zero]
  have hne : y ≠ 0 := Function.ne_iff.mpr ⟨j, hy0⟩
  obtain ⟨Q', ρ, hR, hV', hdim⟩ :=
    exists_restrictData_isVeryAmpleBy (by rw [hpy]; exact hW.le) hxy (singleChart hy0) L h hV
  have hWy : IsSubvar y (primeOf (S := k) y) (n + 1) := by
    rw [hpy]; exact ⟨hW.isPrime, hW.homog, hpy.le, hW.relevant, hW.dim⟩
  have hdy : dimCl k y = ((n + 1 : ℕ) : Cardinal) := (DimTie.proof k K' N y hne (n + 1)).mp hWy
  have hmul : ∀ t ∈ Q'.secs, ∀ i (hi : y i ≠ 0), ∃ b ∈ chartRing k y (singleChart hi), t = b * ρ s :=
    fun t ht i hi => exists_eq_mul_of_le hR hpy (singleChart hi) (mem_sub_of_mem_secs hs _)
      (hgen i (hxy i hi)) (mem_sub_of_mem_secs ht _)
  have hρs : ρ s ≠ 0 := by
    intro h0
    obtain ⟨Q'', hQ''⟩ := Q'.invertible (singleChart hy0)
    have hbot : Q'.sub (singleChart hy0) = ⊥ := (Submodule.eq_bot_iff _).mpr fun t ht => by
      obtain ⟨b, -, rfl⟩ := exists_eq_mul_of_le hR hpy (singleChart hy0) (mem_sub_of_mem_secs hs _)
        (hgen j (hxy j hy0)) ht
      rw [h0, mul_zero]
    rw [hbot, Submodule.bot_mul] at hQ''
    have h1 : (1 : K') ∈ (⊥ : Submodule (chartRing k y (singleChart hy0)) K') := by
      rw [hQ'']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hint : ∀ l, IsIntegral k (ρ (h l) / ρ s) := fun l => hG k K' N y _ hne fun i hi => by
    obtain ⟨b, hb, he⟩ := hmul (ρ (h l)) (hV'.mem_secs l) i hi
    rw [he, mul_div_cancel_right₀ _ hρs]
    exact hb
  have halg : Algebra.IsAlgebraic k (funField (k := k) (ρ ∘ h)) := by
    apply IntermediateField.isAlgebraic_adjoin
    rintro _ ⟨i, l, -, rfl⟩
    have e : (ρ ∘ h) l / (ρ ∘ h) i = ρ (h l) / ρ s * (ρ (h i) / ρ s)⁻¹ := by
      rw [inv_div, div_mul_div_cancel₀ hρs]; rfl
    rw [e]
    exact (hint l).mul (hint i).inv
  have h0 : dimCl k (ρ ∘ h) = 0 := trdeg_eq_zero
  rw [← hdim, hdy] at h0
  exact Nat.succ_ne_zero n (Nat.cast_eq_zero.mp h0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenFibNef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing blockWeight IsMultiHomog IsMultiProjPrime gradedPiece hilbFn intNum
  genFib)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

namespace GenFibNef

section Transport

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isMultiHomog_map_iff (f : MRing ι F₁) (b : K → ℕ) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (map (e : F₁ →+* F₂) f) b ↔ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f b := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog IsWeightedHomogeneous
  simp only [coeff_map, ne_eq, RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]

noncomputable def quotEquiv (P : Ideal (MRing ι F₁)) :
    (MRing ι F₁ ⧸ P) ≃+* (MRing ι F₂ ⧸ P.map (map (e : F₁ →+* F₂))) :=
  Ideal.quotientEquiv P _ (mapEquiv (Σ k, ι k) e) (by
    congr 1)


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_mk (P : Ideal (MRing ι F₁)) (f : MRing ι F₁) :
    quotEquiv e P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk _ (map (e : F₁ →+* F₂) f) := rfl


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_smul (P : Ideal (MRing ι F₁)) (r : F₁) (x : MRing ι F₁ ⧸ P) :
    quotEquiv e P (r • x) = e r • quotEquiv e P x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h₁ : r • Ideal.Quotient.mk P f = Ideal.Quotient.mk P (C r * f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₁, ← map_smul, smul_eq_C_mul]
  have h₂ : e r • Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (map (e : F₁ →+* F₂) f) =
      Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (C (e r) * map (e : F₁ →+* F₂) f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₂, ← map_smul, smul_eq_C_mul]
  rw [h₁, quotEquiv_mk, quotEquiv_mk, h₂, map_mul, map_C]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_mem_gradedPiece (P : Ideal (MRing ι F₁)) (n : K → ℕ) (x : MRing ι F₁ ⧸ P)
    (hx : x ∈ gradedPiece P n) : quotEquiv e P x ∈ gradedPiece (P.map (map (e : F₁ →+* F₂))) n := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨map (e : F₁ →+* F₂) f, ?_, rfl⟩
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  exact (isMultiHomog_map_iff e f n).2 hf

theorem finrank_gradedPiece_map (P : Ideal (MRing ι F₁)) (n : K → ℕ) :
    Module.finrank F₂ (gradedPiece (P.map (map (e : F₁ →+* F₂))) n) =
      Module.finrank F₁ (gradedPiece P n) := by
  let j₀ : gradedPiece P n →+ gradedPiece (P.map (map (e : F₁ →+* F₂))) n :=
    { toFun := fun x => ⟨quotEquiv e P x.1, quotEquiv_mem_gradedPiece e P n x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero (quotEquiv e P))
      map_add' := fun a b => Subtype.ext (map_add (quotEquiv e P) a.1 b.1) }
  have hinj : Function.Injective j₀ := fun a b h =>
    Subtype.ext ((quotEquiv e P).injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective j₀ := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hz
    have hg' : map (e.symm : F₂ →+* F₁) g ∈ weightedHomogeneousSubmodule F₁ (blockWeight ι) n := by
      rw [mem_weightedHomogeneousSubmodule] at hg ⊢
      have hgg : map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g) = g :=
        (mapEquiv (Σ k, ι k) e).apply_symm_apply g
      have h' : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g)) n := by
        rw [hgg]
        exact hg
      exact (isMultiHomog_map_iff e _ n).1 h'
    refine ⟨⟨Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g), Submodule.mem_map.2 ⟨_, hg', rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change quotEquiv e P (Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g)) = Ideal.Quotient.mk _ g
    rw [quotEquiv_mk]
    congr 1
    exact (mapEquiv (Σ k, ι k) e).apply_symm_apply g
  let j := AddEquiv.ofBijective j₀ ⟨hinj, hsurj⟩
  have hrank := rank_eq_of_equiv_equiv (e : F₁ → F₂) j e.bijective (fun r m => by
    apply Subtype.ext
    exact quotEquiv_smul e P r m)
  unfold Module.finrank
  rw [hrank]

theorem hilbFn_map (P : Ideal (MRing ι F₁)) :
    hilbFn (P.map (map (e : F₁ →+* F₂))) = hilbFn P := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece_map]
  · rfl

theorem intNum_map (P : Ideal (MRing ι F₁)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F₂ (P.map (map (e : F₁ →+* F₂))) bs = intNum F₁ P bs := by
  unfold intNum
  rw [hilbFn_map]

end Transport

end GenFibNef

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PReindexDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

theorem coneMap_rename {F : Type} [Field F] {κ : Type} {Ω : Type} [Field Ω] [Algebra F Ω] (x' : κ → Ω) {N : ℕ}
    (e : κ ≃ Fin (N + 1)) (p : NumbersDVR.MRing (fun _ : Unit => κ) F) :
    uniqueAlgEquiv Ω Unit (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p) =
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename (fun v : Σ _ : Unit, κ => e v.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.oneBlock]

theorem ReindexDim.proof : ReindexDim.Statement := by
  intro F _ κ _ Ω _ _ x' N e
  let σ : (Σ _ : Unit, κ) ≃ Fin (N + 1) :=
    { toFun := fun v => e v.2, invFun := fun i => ⟨(), e.symm i⟩, left_inv := fun _ => by simp,
      right_inv := fun _ => by simp }
  let f : NumbersDVR.MRing (fun _ : Unit => κ) F ≃+* Kleiman.Poly F N := (renameEquiv F σ).toRingEquiv
  have hc : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      (Kleiman.primeOf (S := F) (x' ∘ e.symm)).comap f.toRingHom := by
    ext p
    change mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p = 0 ↔
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename σ p) = 0
    rw [← (uniqueAlgEquiv Ω Unit).injective.eq_iff, map_zero]
    exact Iff.of_eq (congrArg (· = 0) (coneMap_rename x' e p))
  have h : Kleiman.primeOf (S := F) (x' ∘ e.symm) = (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

