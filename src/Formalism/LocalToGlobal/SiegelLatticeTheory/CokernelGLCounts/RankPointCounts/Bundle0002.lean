module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Lemmata.GeneralBFactThirdBisForm.Imports
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TorsionTotientBound

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFund
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Tri

variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)

def mlaw (x y : ∀ q, α q) : ∀ p, α p := fun p => x p + y p + B p x y

end Tri

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MapConjOfBounded
section
noncomputable section

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.CovariantRepresentation

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem map_conj_of_mem (R : Subgroup G) (ν : Measure G) (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hi : ν.map (fun x => x⁻¹) = ν) {n : G} (hn : n ∈ R) : ν.map (fun x => n⁻¹ * x * n) = ν := by
  have hinv : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hr : ν.map (fun x => x * n) = ν := by
    have e : (fun x : G => x * n) = (fun x => x⁻¹) ∘ ((fun x => n⁻¹ * x) ∘ (fun x => x⁻¹)) := by
      funext x; simp [mul_inv_rev]
    rw [e, ← map_map hinv ((measurable_const_mul _).comp hinv), ← map_map (measurable_const_mul _) hinv, hi,
      hl _ (R.inv_mem hn), hi]
  have e : (fun x : G => n⁻¹ * x * n) = (fun x => x * n) ∘ (fun x => n⁻¹ * x) := rfl
  rw [e, ← map_map (measurable_mul_const n) (measurable_const_mul _), hl _ (R.inv_mem hn), hr]

theorem map_conj_of_bounded (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (h0 : ν ≠ 0)
    (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (k : G) (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R)
    (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) : ν.map (fun x => k⁻¹ * x * k) = ν := by
  obtain ⟨C, hCc, hCm⟩ := hC
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology _
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  set μ : Measure R := ν.comap Subtype.val with hμ
  have hν : μ.map Subtype.val = ν := by
    rw [hemb.map_comap, Subtype.range_coe]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    exact hc
  have hcm : ∀ μ' : Measure R, (μ'.map Subtype.val).comap Subtype.val = μ' := fun μ' => hemb.comap_map μ'
  haveI : μ.IsMulLeftInvariant := ⟨fun r => by
    have h1 : (μ.map (r * ·)).map Subtype.val = μ.map Subtype.val := by
      rw [map_map hemb.measurable (measurable_const_mul r)]
      have e : (Subtype.val ∘ (r * ·) : R → G) = (fun x : G => (r : G) * x) ∘ Subtype.val := rfl
      rw [e, ← map_map (measurable_const_mul (r : G)) hemb.measurable, hν, hl _ r.2]
    rw [← hcm (μ.map (r * ·)), h1, hcm]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hKc => by
    rw [hμ, hemb.comap_apply]
    exact hK _ (hKc.image continuous_subtype_val)⟩
  haveI : NeZero μ := ⟨fun h => h0 (by rw [← hν, h, Measure.map_zero])⟩
  haveI : IsOpenPosMeasure μ := by
    obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering R n) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply NeZero.ne μ
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
      exact measure_iUnion_null hall
    exact isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering R n) hn
  haveI : IsHaarMeasure μ :=
    { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
      toIsOpenPosMeasure := inferInstance }
  let α : R ≃ₜ* R :=
    { toFun := fun r => ⟨k⁻¹ * r * k, (hk r).1 r.2⟩
      invFun := fun r => ⟨k * r * k⁻¹, (hk _).2 (by simpa [mul_assoc] using r.2)⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  have hit : ∀ (n : ℕ) (x : R), (((⇑α)^[n] x : R) : G) = k ^ (-(n : ℤ)) * x * k ^ (n : ℤ) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k⁻¹ * (((⇑α)^[n] x : R) : G) * k = _
      rw [ih]
      push_cast
      group
  have hit' : ∀ (n : ℕ) (x : R), (((⇑α.symm)^[n] x : R) : G) = k ^ (n : ℤ) * x * k ^ (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k * (((⇑α.symm)^[n] x : R) : G) * k⁻¹ = _
      rw [ih]
      push_cast
      group
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : R)
  have hL : IsCompact (Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) : Set R) :=
    hce.isCompact_preimage ((hCc.mul (hV.image continuous_subtype_val)).mul hCc)
  have hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) ∧
      (⇑α.symm)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) := by
    intro n
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α.symm)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit' n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
  have hμα : μ.map α = μ := haar_map_equiv_of_bounded μ α hV hV1 hL hb
  have hmc : Measurable (fun x : G => k⁻¹ * x * k) := (measurable_const_mul _).mul_const _
  have hma : Measurable (⇑α) := α.continuous.measurable
  calc ν.map (fun x => k⁻¹ * x * k) = (μ.map Subtype.val).map (fun x => k⁻¹ * x * k) := by rw [hν]
    _ = (μ.map α).map Subtype.val := by
        rw [map_map hmc hemb.measurable, map_map hemb.measurable hma]
        rfl
    _ = ν := by rw [hμα, hν]

theorem conj_of_decomp (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (_hs : SigmaFinite ν)
    (h0 : ν ≠ 0) (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (hi : ν.map (fun x => x⁻¹) = ν) (k n : G)
    (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R) (hn : n ∈ R) (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) :
    ν.map (fun x => (k * n)⁻¹ * x * (k * n)) = ν := by
  have e : (fun x : G => (k * n)⁻¹ * x * (k * n)) = (fun x => n⁻¹ * x * n) ∘ (fun x => k⁻¹ * x * k) := by
    funext x
    simp only [Function.comp]
    group
  rw [e, ← map_map ((measurable_const_mul _).mul_const _) ((measurable_const_mul _).mul_const _),
    map_conj_of_bounded R hR ν h0 hc hK hl k hk hC, map_conj_of_mem R ν hl hi hn]

end Conj

end Formalism.L2.SG.CovariantRepresentation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PhiMapAdd
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Covol

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]

def phiMap (x : mixedSpace K) : ι → ℂ := fun i => if cj i then (starRingEnd ℂ) (x.2 (σ i)) else x.2 (σ i)

theorem phiMap_add (x y : mixedSpace K) : phiMap σ cj (x + y) = phiMap σ cj x + phiMap σ cj y := by
  funext i
  by_cases h : cj i <;> simp [phiMap, h]

theorem phiMap_mp [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (phiMap σ cj) volume volume := by
  have hu : (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) Set.univ = 1 := by
    first
    | (rw [volume_pi, Measure.pi_of_empty]; simp)
    | (rw [volume_pi, Measure.pi_univ]; simp)
    | simp [volume_pi, Measure.pi_univ]
    | (erw [Measure.pi_univ]; simp)
  have h1 : MeasurePreserving (Prod.snd : mixedSpace K → ({w : InfinitePlace K // w.IsComplex} → ℂ))
      volume volume := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.volume_eq_prod, Measure.map_snd_prod]
    first
    | rw [hu, one_smul]
    | simp only [hu, one_smul]
    | (convert one_smul ENNReal (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ℂ)); exact hu)
  have h2 : MeasurePreserving (fun (y : {w : InfinitePlace K // w.IsComplex} → ℂ) (i : ι) => y (σ i))
      volume volume :=
    MeasurePreserving.symm _
      (measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace K // w.IsComplex} => (volume : Measure ℂ)) σ)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
    have := Complex.conjLIE.measurePreserving
    convert this using 2
    all_goals first | rfl | (funext z; simp) | (ext z; simp)
  have h3 : MeasurePreserving (fun (z : ι → ℂ) (i : ι) => if cj i then starRingEnd ℂ (z i) else z i)
      (Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => (volume : Measure ℂ)) := by
    refine measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ))
      (f := fun i c => if cj i then starRingEnd ℂ c else c) (fun i => ?_)
    by_cases h : cj i
    · first
      | (simp only [if_pos h]; exact hc)
      | simpa [h] using hc
    · first
      | (simp only [if_neg h]; exact MeasurePreserving.id _)
      | simp [h, MeasurePreserving.id]
  first
  | exact h3.comp (h2.comp h1)
  | (rw [volume_pi]; exact h3.comp (h2.comp h1))

end Covol

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SwapMp
section
noncomputable section

open MeasureTheory MeasurableSpace Set

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem swap_mp {ι P β : Type} [Fintype ι] [Fintype P] [MeasurableSpace β] (μ0 : Measure β) [SigmaFinite μ0] :
    MeasurePreserving (fun (x : ι → P → β) (p : P) (v : ι) => x v p)
      (Measure.pi fun _ : ι => Measure.pi fun _ : P => μ0) (Measure.pi fun _ : P => Measure.pi fun _ : ι => μ0) := by
  first | exact Bl.general_b_fact_third_bis_form.goal1 .. | (apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption)

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TwoLeAbsNormPrime
section
noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

variable {E : Type} [Field E] [NumberField E]

theorem two_le_absNorm_prime {P : Ideal (𝓞 E)} (hP : P.IsPrime) (h0 : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have h2 : Ideal.absNorm P ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0
  omega

theorem card_dvd_le_absNorm (M : Ideal (𝓞 E)) (hM : M ≠ ⊥) (D : Finset (Ideal (𝓞 E)))
    (hD : ∀ I ∈ D, I ∣ M) : D.card ≤ Ideal.absNorm M := by
  classical
  have hI0 : ∀ I ∈ D, I ≠ ⊥ := fun I hI h => hM (by obtain ⟨c, hc⟩ := hD I hI; rw [hc, h, Ideal.bot_mul])
  have hinj : Set.InjOn (fun I => UniqueFactorizationMonoid.normalizedFactors I) (D : Set (Ideal (𝓞 E))) := by
    intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hI0 I hI), ← Ideal.prod_normalizedFactors_eq_self (hI0 J hJ)]
    exact congrArg Multiset.prod h
  have hsub : D.image (fun I => UniqueFactorizationMonoid.normalizedFactors I) ⊆
      (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset := by
    intro s hs
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hs
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors (hI0 I hI) hM).1 (hD I hI)
  have h1 : D.card ≤ 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := by
    calc D.card = (D.image fun I => UniqueFactorizationMonoid.normalizedFactors I).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M).powerset := Multiset.toFinset_card_le _
      _ = 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := Multiset.card_powerset _
  have h2 : 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) ≤ Ideal.absNorm M := by
    have hprod : Ideal.absNorm M =
        ((UniqueFactorizationMonoid.normalizedFactors M).map Ideal.absNorm).prod := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hM]
      exact map_multiset_prod Ideal.absNorm _
    rw [hprod, ← Multiset.card_map Ideal.absNorm]
    refine Multiset.pow_card_le_prod fun n hn => ?_
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hn
    have hpr := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    exact two_le_absNorm_prime (Ideal.isPrime_of_prime hpr) hpr.ne_zero
  exact h1.trans h2

theorem absNorm_map_equiv (σ : 𝓞 E ≃+* 𝓞 E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map σ) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map σ) σ rfl).toEquiv.symm

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end

