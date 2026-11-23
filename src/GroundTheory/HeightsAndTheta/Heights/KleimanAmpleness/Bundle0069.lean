module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0066
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0088

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts)

theorem BlockGenOfModel.proof : BlockGenOfModel.Statement := by
  classical
  intro S _ K ι _ Ω _ _ y k₀ hmod j hj k
  set x := IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) with hx
  set A := chartRingOver S x (fun _ => j) with hA

  let D : Set A := {d | ∃ b, y ⟨k, b⟩ ≠ 0 ∧ ∀ a, (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b⟩) ∈ A}
  have hI : (Submodule.span A D : Ideal A) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal _ hne
    have hqp : q.IsPrime := hq.isPrime
    have hsame : modelPts S y = modelPts S x := hmod.2
    have hmem : locIn A q ∈ modelPts S x := ⟨fun _ => j, fun _ => hj, q, hqp, rfl⟩
    rw [← hsame] at hmem
    obtain ⟨c, hc, p, hp, hEq⟩ := hmem
    have hr : ∀ a, y ⟨k, a⟩ / y ⟨k, c k⟩ ∈ locIn A q := by
      intro a
      rw [hEq]
      exact (mem_locIn_chart_iff y c p).mpr
        ⟨⟨_, Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩⟩, 1, Ideal.one_notMem p, by simp⟩
    choose nn dd hdd hnd using fun a => (mem_locIn_chart_iff x (fun _ => j) q).mp (hr a)
    have hdq : (∏ a, dd a) ∉ q := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨a, -, ha⟩
      exact hdd a ha
    apply hdq
    apply hIq
    apply Submodule.subset_span
    refine ⟨c k, hc k, fun a => ?_⟩
    rw [hnd a]
    have hda : (dd a : Ω) ≠ 0 := coe_ne_zero_of_notMem x (fun _ => j) q (hdd a)
    have e : ((∏ a', dd a' : A) : Ω) * ((nn a : Ω) / dd a) =
        (nn a : Ω) * ∏ a' ∈ Finset.univ.erase a, (dd a' : Ω) := by
      rw [SubmonoidClass.coe_finsetProd, ← Finset.mul_prod_erase Finset.univ (fun a' => (dd a' : Ω))
        (Finset.mem_univ a)]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _ (nn a).2 (Subalgebra.prod_mem _ fun i _ => (dd i).2)

  have key : ∀ t ∈ (Submodule.span A D : Ideal A), ∃ w : ι k → Ω,
      (∀ a b, y ⟨k, a⟩ * w b ∈ A) ∧ ∑ b, y ⟨k, b⟩ * w b = (t : Ω) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨b, hb, hdb⟩ := hd
      refine ⟨Pi.single b ((d : Ω) / y ⟨k, b⟩), fun a b' => ?_, ?_⟩
      · by_cases h : b' = b
        · subst h
          simp only [Pi.single_eq_same]
          have e : y ⟨k, a⟩ * ((d : Ω) / y ⟨k, b'⟩) = (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b'⟩) := by ring
          rw [e]
          exact hdb a
        · simp only [Pi.single_eq_of_ne h, mul_zero]
          exact Subalgebra.zero_mem _
      · simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        field_simp
    | zero => exact ⟨0, fun _ _ => by simp, by simp⟩
    | add s t _ _ hs ht =>
      obtain ⟨w, hw, hws⟩ := hs
      obtain ⟨w', hw', hwt⟩ := ht
      refine ⟨w + w', fun a b => ?_, ?_⟩
      · rw [Pi.add_apply, mul_add]
        exact Subalgebra.add_mem _ (hw a b) (hw' a b)
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hws, hwt]
        push_cast
        ring
    | smul r t _ ht =>
      obtain ⟨w, hw, hwt⟩ := ht
      refine ⟨fun b => (r : Ω) * w b, fun a b => ?_, ?_⟩
      · have e : y ⟨k, a⟩ * ((r : Ω) * w b) = (r : Ω) * (y ⟨k, a⟩ * w b) := by ring
        rw [e]
        exact Subalgebra.mul_mem _ r.2 (hw a b)
      · rw [smul_eq_mul, Subalgebra.coe_mul, ← hwt, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
  obtain ⟨w, hw, hsum⟩ := key 1 (by rw [hI]; exact Submodule.mem_top)
  exact ⟨w, hw, by rw [hsum]; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelPoint.proof (hgen : BlockGenOfModel.Statement) (htr : BlockGenTransfer.Statement)
    (hmod : ModelOfBlockGen.Statement) : ModelPoint.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ hy K' _ _ y' hy' hle
  exact hmod F K ι K' y' k₀ hy' (htr F K ι Ω y k₀ (hgen F K ι Ω y k₀ hy) K' y' hy' hle)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartRingBlockVecIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver mConeMapOver)

theorem ne_zero_of_mIdealOver_le {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω Ω' : Type} [Field Ω]
    [Field Ω'] [Algebra S Ω] [Algebra S Ω'] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → Ω'}
    (h : mIdealOver S y ≤ mIdealOver S y') (p : Σ k, ι k) (hp : y' p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hmem : (X p : MvPolynomial (Σ k, ι k) S) ∈ mIdealOver S y := by
    simp [mIdealOver, RingHom.mem_ker, mConeMapOver, h0]
  have h' := h hmem
  simpa [mIdealOver, RingHom.mem_ker, mConeMapOver] using h'

theorem mem_chartRing_blockVec_iff {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra S Ω] (z : (Σ k, ι k) → Ω) (k₀ : K) (j : ι k₀) (u : Ω) :
    u ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k₀)) (fun _ => j) ↔
      ∃ P : MvPolynomial (Σ _ : Unit, ι k₀) S,
        aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, j⟩) P = u := by
  unfold chartRingOver
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]
  rfl

theorem aeval_rename_blockRatio {S : Type} [CommRing S] {K : Type} {ι : K → Type} {L : Type} [Field L]
    [Algebra S L] (z : (Σ k, ι k) → L) (k₀ : K) (c : ∀ k, ι k) (P : MvPolynomial (Σ _ : Unit, ι k₀) S) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩)
        (rename (fun v : (Σ _ : Unit, ι k₀) => (⟨k₀, v.2⟩ : Σ k, ι k)) P) =
      aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, c k₀⟩) P := by
  rw [aeval_rename]
  rfl

theorem BlockGenTransfer.proof (hk : ChartKernel.Statement) : BlockGenTransfer.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ hB Ω' _ _ y' hne hle j hj k
  have hy := ne_zero_of_mIdealOver_le hle
  obtain ⟨c, hck₀, hc⟩ : ∃ c : ∀ k, ι k, c k₀ = j ∧ ∀ k, y' ⟨k, c k⟩ ≠ 0 := by
    choose c₀ hc₀ using hne
    refine ⟨Function.update c₀ k₀ j, Function.update_self _ _ _, fun k' => ?_⟩
    by_cases h : k' = k₀
    · cases h
      rw [Function.update_self]
      exact hj
    · rw [Function.update_of_ne h]
      exact hc₀ k'
  have hb₀ : y ⟨k, c k⟩ ≠ 0 := hy _ (hc k)
  obtain ⟨w, hw, hsum⟩ := hB j (hy _ hj) k
  choose P hP using fun a b => (mem_chartRing_blockVec_iff y k₀ j _).1 (hw a b)
  let φ : (Σ _ : Unit, ι k₀) → (Σ k, ι k) := fun v => ⟨k₀, v.2⟩
  have hR1 : ∀ a b, aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (X ⟨k, a⟩ * rename φ (P (c k) b) - rename φ (P a b)) = 0 := by
    intro a b
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    field_simp
    ring
  have hR2 : aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (∑ b, X ⟨k, b⟩ * rename φ (P (c k) b) - 1) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    rw [sub_eq_zero, ← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  refine ⟨fun b => aeval (fun v : (Σ _ : Unit, ι k₀) => y' ⟨k₀, v.2⟩ / y' ⟨k₀, j⟩) (P (c k) b) / y' ⟨k, c k⟩,
    fun a b => ?_, ?_⟩
  · have h1 := hk S K ι Ω y Ω' y' hle c hc _ (hR1 a b)
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, sub_eq_zero] at h1
    rw [mem_chartRing_blockVec_iff]
    refine ⟨P a b, ?_⟩
    rw [← h1]
    ring
  · have h2 := hk S K ι Ω y Ω' y' hle c hc _ hR2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀,
      sub_eq_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

set_option linter.unusedSectionVars false

namespace KHTheoremSFree

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def Bad (a : (Σ k, ι k) → ℤ) : Prop :=
  ∀ k, negSet a k = ∅ ∨ negSet a k = Finset.univ

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem embed_apply (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) (I : KH.Cell K ι n)
    (h : ∀ k, negSet a k ⊆ I.1 k) : embed S a n f I = f ⟨I, h⟩ • monoFrac S I.1 a := by
  simp [embed, h]
  rfl

theorem embed_mem_cechBc (hE : KHFreeEmbed.Statement) {a : (Σ k, ι k) → ℤ} {c d : K → ℤ}
    (ha : GroundTheory.Heights₂.Heights.Kleiman.KHFree.blockSum a = c + d) {n : ℕ} {b : CombC S (negSet a) n} (hb : b ∈ combB S (negSet a) n) :
    embed S a n b ∈ KH.cechBc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n := by
  cases n with
  | zero =>
    have hb0 : b = 0 := (Submodule.mem_bot S).mp hb
    subst hb0
    rw [map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hb
    exact ⟨embed S a m g, (hE S K ι a).2.1 c d ha m g, (hE S K ι a).1 m g⟩

theorem cocycle_decomp (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    {c d : K → ℤ} {n : ℕ} {z : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n}
    (hz : z ∈ KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) :
    ∃ (A : Finset ((Σ k, ι k) → ℤ)) (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
      (∀ a ∈ A, GroundTheory.Heights₂.Heights.Kleiman.KHFree.blockSum a = c + d) ∧ z = ∑ a ∈ A, embed S a n (f a) ∧
        ∀ a ∈ A, combD S (negSet a) n (f a) = 0 := by
  obtain ⟨A, f, hA, rfl⟩ := hD S K ι c d n z hz.1
  refine ⟨A, f, hA, rfl, hI S K ι (n + 1) A (fun a => combD S (negSet a) n (f a)) ?_⟩
  have h0 : KH.cechD S ι _ n (∑ a ∈ A, embed S a n (f a)) = 0 := hz.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h0
  simpa only [(hE S K ι _).1] using h0

theorem part_cyclic (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (a : (Σ k, ι k) → ℤ) {n : ℕ}
    {g : CombC S (negSet a) n} (hg : combD S (negSet a) n g = 0) :
    ∃ s : S, g - s • singOne S (negSet a) n ∈ combB S (negSet a) n ∧ (s ≠ 0 → Bad a) := by
  by_cases hb : Bad a
  · obtain ⟨s, hs⟩ := (hY S K ι (negSet a) n hb).2 g hg
    exact ⟨s, hs, fun _ => hb⟩
  · simp only [Bad, not_forall, not_or] at hb
    obtain ⟨k, hk0, hku⟩ := hb
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ negSet a k := by
      by_contra h
      push Not at h
      exact hku (Finset.eq_univ_of_forall h)
    obtain ⟨g', hg', hg'I⟩ := hC S K ι (negSet a) n k i₀ hi₀ g hg
    have h0 : g' = 0 := funext fun I => (hg'I I).2 fun h => hk0 h.1
    refine ⟨0, ?_, fun h => absurd rfl h⟩
    rw [zero_smul, sub_zero]
    rwa [h0, sub_zero] at hg'


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem negSet_empty {a : (Σ k, ι k) → ℤ} {e : K → ℤ} (ha : GroundTheory.Heights₂.Heights.Kleiman.KHFree.blockSum a = e) (he : ∀ k, 0 ≤ e k) (hb : Bad a)
    (k : K) : negSet a k = ∅ := by
  rcases hb k with h | h
  · exact h
  refine Finset.eq_empty_of_forall_notMem fun i _ => ?_
  have hall : ∀ j, a ⟨k, j⟩ < 0 := fun j => by
    have hj : j ∈ negSet a k := h ▸ Finset.mem_univ j
    simpa [negSet] using hj
  have hneg : ∑ j, a ⟨k, j⟩ < 0 := Finset.sum_neg (fun j _ => hall j) ⟨i, Finset.mem_univ _⟩
  have hk : ∑ j, a ⟨k, j⟩ = e k := congrFun ha k
  linarith [he k]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem nonneg_of_negSet_empty {a : (Σ k, ι k) → ℤ} (h : ∀ k, negSet a k = ∅) (p : Σ k, ι k) : 0 ≤ a p := by
  by_contra hp
  have hm : p.2 ∈ negSet a p.1 := by simp [negSet]; omega
  rw [h p.1] at hm
  exact Finset.notMem_empty _ hm


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem singOne_eq_zero {J : ∀ k, Finset (ι k)} (hJ : ∀ k, J k = ∅) {n : ℕ} (hn : 1 ≤ n) :
    singOne S J n = 0 := by
  funext I
  simp only [singOne, Pi.zero_apply]
  rw [if_neg]
  intro h
  have h1 : ∀ k, (I.1.1 k).card - 1 = 0 := fun k => by rw [h k (hJ k)]
  have hs := I.1.2.2
  simp only [h1, Finset.sum_const_zero] at hs
  omega


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem singOne_zero {J : ∀ k, Finset (ι k)} (I : CombCell ι J 0) : singOne S J 0 I = 1 := by
  simp only [singOne]
  rw [if_pos]
  intro k _
  have hs := I.1.2.2
  have hk := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
  have hpos := Finset.card_pos.mpr (I.1.2.1 k)
  omega

theorem finite (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (hF : KHFreeBadFinite.Statement)
    (d c : K → ℤ) (n : ℕ) :
    Module.Finite S (KH.cechHc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) := by
  classical
  set Z := KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n
  set Bf := (hF K ι (c + d)).toFinset
  have hBf : ∀ a ∈ Bf, GroundTheory.Heights₂.Heights.Kleiman.KHFree.blockSum a = c + d ∧ Bad a := fun a ha => (hF K ι (c + d)).mem_toFinset.mp ha
  let gen : ((Σ k, ι k) → ℤ) → KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n :=
    fun a => embed S a n (singOne S (negSet a) n)
  have hgen : ∀ a ∈ Bf, gen a ∈ Z := fun a ha =>
    ⟨(hE S K ι a).2.1 c d (hBf a ha).1 n _, by
      change KH.cechD S ι _ n (embed S a n _) = 0
      rw [(hE S K ι a).1, (hY S K ι (negSet a) n (hBf a ha).2).1, map_zero]⟩

  let Ψ : (Bf → S) →ₗ[S] Z :=
    LinearMap.codRestrict Z (∑ x : Bf, (LinearMap.proj x : (Bf → S) →ₗ[S] S).smulRight (gen x.1))
      (fun s => by
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
        exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hgen x.1 x.2))
  have hΨ : ∀ t, (Ψ t : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n) =
      ∑ x : Bf, t x • gen x.1 := fun t => by
    simp only [Ψ, LinearMap.codRestrict_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
  refine Module.Finite.of_surjective ((Submodule.mkQ _).comp Ψ) ?_
  intro x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  choose! s hs hsb using fun a (ha : a ∈ A) => part_cyclic hC hY a (hcoc a ha)
  refine ⟨fun x => if x.1 ∈ A then s x.1 else 0, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq,
    Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, hΨ]
  have hsum : ∑ x : Bf, (if x.1 ∈ A then s x.1 else 0) • gen x.1 = ∑ a ∈ A, s a • gen a := by
    rw [Finset.sum_coe_sort Bf (fun a => (if a ∈ A then s a else 0) • gen a)]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_comm]
    refine Finset.sum_subset Finset.inter_subset_left fun a ha hna => ?_
    have hs0 : s a = 0 := by
      by_contra h0
      exact hna (Finset.mem_inter.mpr ⟨ha, (hF K ι (c + d)).mem_toFinset.mpr ⟨hA a ha, hsb a ha h0⟩⟩)
    rw [hs0, zero_smul]
  rw [hsum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun a ha => ?_
  have he : embed S a n (f a) - s a • gen a = embed S a n (f a - s a • singOne S (negSet a) n) := by
    rw [map_sub, map_smul]
  rw [he]
  exact embed_mem_cechBc hE (hA a ha) (hs a ha)

theorem vanish (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement)
    (d c : K → ℤ) (n : ℕ) (hn : 1 ≤ n) (hcd : ∀ k, 0 ≤ c k + d k) :
    Subsingleton (KH.cechHc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) := by
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.H1VanishingDevissage.cechHc_subsingleton_iff]
  intro z hz
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  refine Submodule.sum_mem _ fun a ha => embed_mem_cechBc hE (hA a ha) ?_
  obtain ⟨s, hs, hsb⟩ := part_cyclic hC hY a (hcoc a ha)
  by_cases h0 : s = 0
  · rwa [h0, zero_smul, sub_zero] at hs
  · have hJ := negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)
    rwa [singOne_eq_zero hJ hn, smul_zero, sub_zero] at hs

theorem sections (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement)
    (d c : K → ℤ) (hcd : ∀ k, 0 ≤ c k + d k)
    (z : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) 0)
    (hz : z ∈ KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c 0) :
    ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d), ∀ I, z I = LocalizedModule.mk m 1 := by
  classical
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  have hpart : ∀ a ∈ A, ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d),
      ∀ I, embed S a 0 (f a) I = LocalizedModule.mk m 1 := by
    intro a ha
    obtain ⟨s, hs, hsb⟩ := part_cyclic hC hY a (hcoc a ha)
    have hfa : f a = s • singOne S (negSet a) 0 := sub_eq_zero.mp ((Submodule.mem_bot S).mp hs)
    by_cases h0 : s = 0
    · refine ⟨0, Submodule.zero_mem _, fun I => ?_⟩
      rw [hfa, h0, zero_smul, map_zero, LocalizedModule.zero_mk]
      rfl
    · have hJ := negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)
      obtain ⟨m, hm, hmI⟩ := (hE S K ι a).2.2 (nonneg_of_negSet_empty hJ)
      rw [hA a ha] at hm
      refine ⟨s • m, Submodule.smul_mem _ _ hm, fun I => ?_⟩
      have hsub : ∀ k, negSet a k ⊆ I.1 k := fun k => by rw [hJ k]; exact Finset.empty_subset _
      have hval : (s • singOne S (negSet a) 0) ⟨I, hsub⟩ = s := by
        change s * singOne S (negSet a) 0 ⟨I, hsub⟩ = s
        exact (congrArg (s * ·) (singOne_zero _)).trans (mul_one s)
      rw [embed_apply a 0 (f a) I hsub, hfa, hval, hmI, LocalizedModule.smul'_mk]
  choose! m hm hmI using hpart
  refine ⟨∑ a ∈ A, m a, Submodule.sum_mem _ hm, fun I => ?_⟩
  rw [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← LocalizedModule.mkLinearMap_apply, map_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [hmI a ha, LocalizedModule.mkLinearMap_apply]

end KHTheoremSFree

theorem KHTheoremSFree.proof (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (hF : KHFreeBadFinite.Statement) :
    KH.TheoremSFreeStatement := by
  intro S _ K _ _ ι _ _ d
  exact ⟨fun c n => KHTheoremSFree.finite hE hD hI hC hY hF d c n,
    fun c n hn hcd => KHTheoremSFree.vanish hE hD hI hC hY d c n hn hcd,
    fun c hcd z hz => KHTheoremSFree.sections hE hD hI hC hY d c hcd z hz⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

