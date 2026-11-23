module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace ZChartLocal

open AmpleAffineGen AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ}
    {y : E} {w : Ω} (hy : y ∈ (F.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    w • y ∈ (F.twist (H.pow (c + d))).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction
    (p := fun y _ => w • y ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    exact Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, z, hz, by rw [smul_smul, mul_comm]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have e : w • (a • z) = a • (w • z) := by
      change w • ((a : Ω) • z) = (a : Ω) • (w • z)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ a hz

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]; exact (Submodule.mem_iInf _).mp (hh a) I
    exact mul_mem_pow H I ih 1 h1


omit [Module S E] [IsScalarTower S Ω E] in
theorem ratio_pow_smul_mem (F : SubSystem S x E) (I K : Chart x) (k : ℕ) {y : E} (hy : y ∈ F.sub I) :
    chartRatio I K ^ k • y ∈ F.sub I :=
  Submodule.smul_mem (F.sub I) (⟨_, pow_mem (chartRatio_mem I K) k⟩ : chartRing S x I) hy


omit [Module S E] [IsScalarTower S Ω E] in
theorem loc_subFamily (G : SubFamily S x E) (I K : Chart x) {y : E}
    (hy : y ∈ G.sub (unionChart I K)) : ∃ c : ℕ, chartRatio I K ^ c • y ∈ G.sub I := by
  obtain ⟨a, ha, hay⟩ := (G.mem_iff I (unionChart I K) (subset_unionChart_left I K) y).mp hy
  obtain ⟨w, hw⟩ := ha.exists_left_inv
  obtain ⟨D, hD⟩ := exists_pow_mul_mem I K w.2
  refine ⟨D, ?_⟩
  have hw' : (w : Ω) * (a : Ω) = 1 := congrArg Subtype.val hw
  have e : chartRatio I K ^ D • y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y) := by
    change _ = (chartRatio I K ^ D * (w : Ω)) • ((a : Ω) • y)
    rw [smul_smul, mul_assoc, hw', mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ hay


omit [Module S E] [IsScalarTower S Ω E] in
theorem loc_twist (G : SubFamily S x E) (H : LineBundle S x) (I K : Chart x) (q : ℕ) {y : E}
    (hy : y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub (unionChart I K)) :
    ∃ c : ℕ, chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction (p := fun y _ => ∃ c : ℕ,
    chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨p, hp, z, hz, rfl⟩
    obtain ⟨D₁, h₁⟩ := exists_pow_mul_mem_of_eq (H.powBundle q)
      (LineBundle.powBundle_toSubSystem H q) I K hp
    obtain ⟨D₂, h₂⟩ := loc_subFamily G I K hz
    refine ⟨D₁ + D₂, Submodule.subset_span ⟨_, h₁, _, h₂, ?_⟩⟩
    rw [smul_smul, smul_smul, pow_add]
    congr 1
    ring
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    have e : chartRatio I K ^ (c₁ + c₂) • (y₁ + y₂) =
        chartRatio I K ^ c₂ • (chartRatio I K ^ c₁ • y₁) + chartRatio I K ^ c₁ • (chartRatio I K ^ c₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm c₂ c₁]
    rw [e]
    exact Submodule.add_mem _ (ratio_pow_smul_mem _ I K c₂ h₁) (ratio_pow_smul_mem _ I K c₁ h₂)
  · rintro a y - ⟨c, hc⟩
    obtain ⟨D, hD⟩ := exists_pow_mul_mem I K a.2
    refine ⟨D + c, ?_⟩
    have e : chartRatio I K ^ (D + c) • (a • y) = (⟨_, hD⟩ : chartRing S x I) • (chartRatio I K ^ c • y) := by
      change chartRatio I K ^ (D + c) • ((a : Ω) • y) = (chartRatio I K ^ D * (a : Ω)) • (chartRatio I K ^ c • y)
      rw [smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hc

end ZChartLocal


open AmpleAffineGen AmpleTwistLocal ZChartLocal in
theorem ZChartLocal.proof (hSmul : ZChartSmul.Statement.{u, v, w}) : ZChartLocal.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj b hb K hK j₀ hj₀ I I' hI' z hz
  classical
  have hbpow : ∀ (k : ℕ) {y : E}, y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J →
      b ^ k • y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J := by
    intro k
    induction k with
    | zero => intro y hy; rwa [pow_zero, one_smul]
    | succ k ih =>
      intro y hy
      rw [pow_succ', mul_smul]
      exact hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hh J j hj I b hb _ (ih hy)
  have hIU : I'.1 ⊆ (unionChart I K).1 := by
    rw [hI']; exact Finset.insert_subset (Finset.mem_union_right _ hj₀) Finset.subset_union_left
  have hzU : z ∈ secsOnZChart G.toSubSystem H.toSubSystem h (unionChart I K) J := by
    refine Submodule.span_mono ?_ hz
    rintro y ⟨n, hn⟩
    exact ⟨n, (G.toSubSystem.twist (H.toSubSystem.pow _)).mono I' _ hIU _ hn⟩
  obtain ⟨e, n, hn⟩ := hK I
  have hR := prod_mem_pow H.toSubSystem I hh (J.1.erase j)
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  generalize ∏ l ∈ J.1.erase j, h l = R at hR hJ
  have hu := mul_mem_pow H.toSubSystem I hn _ (pow_mem_pow H.toSubSystem I hR n)
  generalize hud : b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) * h j ^ n * R ^ n = u at hu
  have huv : u * chartRatio I K = b ^ e * xProd J ^ n := by
    have h1 := chartRatio_mul_chartRatio I K
    rw [chartRatio, chartRatio] at h1
    rw [← hud, hJ, chartRatio]
    linear_combination (b ^ e * (h j * R) ^ n) * h1
  change z ∈ Submodule.span S _ at hzU
  refine Submodule.span_induction (p := fun z _ =>
    ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ hzU
  · rintro y ⟨m, hm⟩
    obtain ⟨c, hc⟩ := loc_twist G H I K _ hm
    refine ⟨e * c, Submodule.subset_span ⟨m + n * c, ?_⟩⟩
    have h2 := smul_mem_twist_pow G.toSubSystem H.toSubSystem I hc (pow_mem_pow H.toSubSystem I hu c)
    have e1 : xProd J ^ (m + n * c) • b ^ (e * c) • y = u ^ c • chartRatio I K ^ c • xProd J ^ m • y := by
      rw [smul_smul, smul_smul, smul_smul, ← mul_pow, huv]
      congr 1
      ring
    have e2 : J.1.card * m + (1 * n + (J.1.erase j).card * n) * c = J.1.card * (m + n * c) := by
      rw [← hcard]; ring
    rw [e1, ← e2]
    exact h2
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
    refine ⟨e₁ + e₂, ?_⟩
    have e3 : b ^ (e₁ + e₂) • (y₁ + y₂) = b ^ e₂ • (b ^ e₁ • y₁) + b ^ e₁ • (b ^ e₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm e₂ e₁]
    rw [e3]
    exact Submodule.add_mem _ (hbpow _ h₁) (hbpow _ h₂)
  · rintro s y - ⟨e', h'⟩
    exact ⟨e', by rw [smul_comm]; exact Submodule.smul_mem _ s h'⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)

section Trdeg

variable {F : Type} [Field F] {B : Type} [CommRing B] [IsDomain B] [Algebra F B]

theorem trdeg_eq_of_le_of_isAlgebraic {S T : Subalgebra F B} (hST : S ≤ T)
    (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg F S = Algebra.trdeg F T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower F S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).2 (algebraMap F S).injective
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq F S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

theorem isAlgebraic_of_mem_adjoin (S : Subalgebra F B) {s : Set B} (hs : ∀ b ∈ s, IsAlgebraic S b)
    {b : B} (hb : b ∈ Algebra.adjoin F s) : IsAlgebraic S b := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => exact isAlgebraic_algebraMap (⟨algebraMap F B r, S.algebraMap_mem r⟩ : S)
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

theorem trdeg_eq_of_isAlgebraic_both {S T : Subalgebra F B} (h₁ : ∀ t ∈ T, IsAlgebraic S t)
    (h₂ : ∀ s ∈ S, IsAlgebraic T s) : Algebra.trdeg F S = Algebra.trdeg F T := by
  have hS : ∀ b ∈ S ⊔ T, IsAlgebraic S b := fun b hb =>
    isAlgebraic_of_mem_adjoin S (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : S)) (h₁ b))
      (by rwa [Algebra.sup_def] at hb)
  have hT : ∀ b ∈ S ⊔ T, IsAlgebraic T b := fun b hb =>
    isAlgebraic_of_mem_adjoin T (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (h₂ b) (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : T)))
      (by rwa [Algebra.sup_def] at hb)
  rw [trdeg_eq_of_le_of_isAlgebraic le_sup_left hS, trdeg_eq_of_le_of_isAlgebraic le_sup_right hT]

end Trdeg

section LocalRings

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem isAlgebraic_of_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [p.IsPrime] {u : Ω}
    (hu : u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : IsAlgebraic A u := by
  unfold IndefiniteRowSideFullHecke.Kleiman2.locIn at hu
  induction hu using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨a, b, hb, rfl⟩ := hu
    have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
    refine IsAlgebraic.of_mul (y := (b : Ω)) (mem_nonZeroDivisors_of_ne_zero hb0)
      (isAlgebraic_algebraMap b) ?_
    have e : (b : Ω) * ((a : Ω) / b) = algebraMap A Ω a := by
      rw [mul_div_cancel₀ _ hb0]; rfl
    rw [e]
    exact isAlgebraic_algebraMap a
  | zero => exact isAlgebraic_zero
  | one => exact isAlgebraic_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

theorem le_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), by simp⟩

theorem exists_trdeg_chartRing_eq {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel F y y') (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) ∧
      Algebra.trdeg F (chartRingOver F y c) = Algebra.trdeg F (chartRingOver F y' c') := by
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F y :=
    ⟨c, hc, ⊥, Ideal.isPrime_bot, rfl⟩
  unfold IndefiniteRowSideFullHecke.Kleiman2.SameModel at h
  rw [h] at hz
  obtain ⟨c', hc', p', hp', hzeq⟩ := hz
  refine ⟨c', hc', trdeg_eq_of_isAlgebraic_both (fun t ht => ?_) (fun s hs => ?_)⟩
  · have ht' : t ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ := by
      rw [hzeq]; exact le_locIn _ p' ht
    exact isAlgebraic_of_mem_locIn _ ⊥ ht'
  · have hs' : s ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y' c') p' := by
      rw [← hzeq]; exact le_locIn _ ⊥ hs
    exact isAlgebraic_of_mem_locIn _ p' hs'

end LocalRings

section Cone

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
variable {K : Type} {ι : K → Type}

def chartConeMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (chartRingOver F y c) →ₐ[F] MvPolynomial K Ω :=
  ((aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars
    F).comp (MvPolynomial.mapAlgHom (chartRingOver F y c).val)

theorem chartConeMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : chartRingOver F y c) :
    chartConeMap y c (MvPolynomial.C a) = MvPolynomial.C (a : Ω) := by
  simp [chartConeMap]

theorem chartConeMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    chartConeMap (F := F) y c (X k) = MvPolynomial.C (y ⟨k, c k⟩) * X k := by
  simp [chartConeMap]

theorem mConeMapOver_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mConeMapOver F y (X p) = MvPolynomial.C (y p) * X p.1 := by
  simp [mConeMapOver]

theorem chartConeMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (chartConeMap (F := F) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

theorem trdeg_quotient_mIdealOver [Fintype K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ chartRingOver F y c := fun p =>
    Algebra.subset_adjoin ⟨p, rfl⟩

  let ρ : MvPolynomial (Σ k, ι k) F →ₐ[F] MvPolynomial K (chartRingOver F y c) :=
    aeval fun p => MvPolynomial.C (⟨_, hu p⟩ : (chartRingOver F y c)) * X p.1
  have hfac : mConeMapOver F y = (chartConeMap (F := F) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [mConeMapOver_X, AlgHom.comp_apply]
    rw [aeval_X, map_mul, chartConeMap_C, chartConeMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mConeMapOver F y).range
  have hle : R ≤ (chartConeMap (F := F) y c).range := by
    show (mConeMapOver F y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hUR : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ∈ R := fun k =>
    ⟨X ⟨k, c k⟩, mConeMapOver_X y _⟩
  have hU0 : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ≠ 0 := fun k =>
    mul_ne_zero (MvPolynomial.C_ne_zero.2 (hc k)) (MvPolynomial.X_ne_zero k)

  have halgC : ∀ w ∈ (chartRingOver F y c), IsAlgebraic R (MvPolynomial.C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1)
        (mem_nonZeroDivisors_of_ne_zero (hU0 p.1)) (isAlgebraic_algebraMap (⟨_, hUR p.1⟩ : R)) ?_
      have e : (MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1 : MvPolynomial K Ω) *
          MvPolynomial.C (y p / y ⟨p.1, c p.1⟩) = mConeMapOver F y (X p) := by
        rw [mConeMapOver_X, mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc p.1)]
      rw [e]
      exact isAlgebraic_algebraMap (⟨_, AlgHom.mem_range_self _ _⟩ : R)
    | algebraMap r =>
      exact isAlgebraic_algebraMap (⟨algebraMap F _ r, R.algebraMap_mem r⟩ : R)
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  have halg : ∀ t ∈ (chartConeMap (F := F) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (chartConeMap (F := F) y c q)
    induction q using MvPolynomial.induction_on with
    | C a => rw [chartConeMap_C]; exact halgC a a.2
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, chartConeMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hUR k⟩ : R))
  have h1 : Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = Algebra.trdeg F R :=
    (Ideal.quotientKerEquivRange (mConeMapOver F y)).trdeg_eq
  have h2 : Algebra.trdeg F (chartConeMap (F := F) y c).range =
      Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) :=
    (AlgEquiv.ofInjective (chartConeMap (F := F) y c) (chartConeMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul F (chartRingOver F y c) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (chartRingOver F y c)).injective
  have _ : FaithfulSMul (chartRingOver F y c) (MvPolynomial K (chartRingOver F y c)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective K _)
  have h3 : Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
    rw [← trdeg_add_eq F (chartRingOver F y c) (A := MvPolynomial K (chartRingOver F y c)),
      MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [h1, trdeg_eq_of_le_of_isAlgebraic hle halg, h2, h3]

end Cone

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

