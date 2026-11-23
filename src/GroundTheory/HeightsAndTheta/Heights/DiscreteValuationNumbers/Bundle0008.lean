module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem HilbFnCut.proof (h1 : GradedPieceQuot.Statement.{u}) (h2 : CutPieces.Statement.{u}) :
    HilbFnCut.Statement.{u} := by
  intro F _ K _ _ ι _ I x e hI hx hnzd m
  by_cases hm : ∀ k, 0 ≤ m k
  · set n : K → ℕ := fun k => (m k).toNat with hn
    have hA := h1 F K ι (I ⊔ Ideal.span {x}) n
    have hB := h1 F K ι I n
    have hC := h2 F K ι I x e n hI hx hnzd
    have hL : hilbFn (I ⊔ Ideal.span {x}) m =
        (Module.finrank F (gradedPiece (I ⊔ Ideal.span {x}) n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    have hM : hilbFn I m = (Module.finrank F (gradedPiece I n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    rw [hL, hM, hA, hB]
    by_cases he : e ≤ n
    · have hme : ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hq : (fun k => ((m - fun k => (e k : ℤ)) k).toNat) = n - e := by
        funext k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) =
          (Module.finrank F (gradedPiece I (n - e)) : ℤ) := by
        unfold hilbFn; rw [if_pos hme, hq]
      rw [hN, h1 F K ι I (n - e)]
      rw [if_pos he] at hC
      rw [hC]
      ring
    · have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro hall
        apply he
        intro k
        have h1k := hall k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) = 0 := by
        unfold hilbFn; rw [if_neg hme]
      rw [hN]
      rw [if_neg he] at hC
      rw [hC]
      ring
  · obtain ⟨k, hk⟩ := not_forall.mp hm
    have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
      intro hall
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    unfold hilbFn
    rw [if_neg hm, if_neg hm, if_neg hme, sub_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnVanishBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem exists_block_var_of_weight_pos {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by
  by_contra hne
  push Not at hne
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv1 : v.1 ≠ k := fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)
    simp [blockWeight, hv1]
  omega

theorem mem_of_block_vars_mem {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hX i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  rw [mem_weightedHomogeneousSubmodule] at hf
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (Finsupp.mem_support_iff.mp hd)
  obtain ⟨v, hv, hdv⟩ := exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)
  exact ⟨v, hv, hdv⟩

theorem HilbFnVanishBlock.proof : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAssoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem IntNumAssoc.list_sum_finset_sum {α β : Type*} (l : List α) (s : Finset β)
    (f : α → β → ℤ) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

theorem IntNumAssoc.list_sum_ite_enat {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] :
    (l.map fun a => if P a then (1 : ℕ∞) else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

theorem IntNumAssoc.list_sum_ite_mul {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (c : ℤ) :
    (l.map fun a => if P a then c else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℤ) * c := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih, add_mul]

theorem IntNumAssoc.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : IntNumOfFiltration.Statement.{u}) (h3 : MultAtPrimeAtMinimal.Statement.{u})
    (h4 : IntNumVanish.Statement.{u}) (h5 : TopDimMinimal.Statement.{u})
    (h6 : HilbDegBound.Statement.{u}) : IntNumAssoc.Statement.{u} := by
  classical
  intro F _ K _ _ ι _ n J hJ hdim bs
  obtain ⟨l, hl, hhilb, hmult⟩ := h1 F K ι J hJ
  have hdimp : ∀ p ∈ l, ringKrullDim (MRing ι F ⧸ p.1) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := fun p hp =>
    lt_of_le_of_lt (ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hl p hp).2.2)
      (Ideal.Quotient.factor_surjective (hl p hp).2.2)) hdim
  have hdeg : ∀ p ∈ l, DegLT (hilbFn p.1) (n + 1) := fun p hp =>
    h6 F K ι (n + 1) p.1 (hl p hp).1 (hl p hp).2.1 (hdimp p hp)
  rw [h2 F K ι n J l hdeg hhilb bs]
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F) J
  have hp : ∀ p ∈ l, intNum F p.1 bs =
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 := by
    intro p hpl
    rw [Finset.sum_ite_eq]
    by_cases hz : intNum F p.1 bs = 0
    · rw [hz]
      simp
    · have := (hl p hpl).1
      have hrel : IsRelevant p.1 := by
        by_contra hr
        exact hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inl hr) bs)
      have hbig : ¬ ringKrullDim (MRing ι F ⧸ p.1) <
          ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := fun hs =>
        hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inr hs) bs)
      have hJ' : ringKrullDim (MRing ι F ⧸ J) <
          ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
        have e : n + Fintype.card K + 1 = n + 1 + Fintype.card K := by omega
        rw [e]
        exact hdim
      have hmin := h5 _ J p.1 (n + Fintype.card K) (hl p hpl).2.2 hJ' hbig
      rw [if_pos (hfin.mem_toFinset.mpr hmin), if_pos hrel]
  have hl2 : (l.map fun p => intNum F p.1 bs) = l.map fun p =>
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 :=
    List.map_congr_left hp
  rw [hl2, IntNumAssoc.list_sum_finset_sum]
  have hsupp : Function.support (fun W => idealCycle J W * intNum F W bs) ⊆
      (hfin.toFinset : Set (Ideal (MRing ι F))) := by
    intro W hW
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hn
    apply Function.mem_support.mp hW
    unfold idealCycle
    rw [dite_eq_right (fun h => hn h.1), zero_mul]
  unfold cycEval
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hWm : W ∈ J.minimalPrimes := hfin.mem_toFinset.mp hW
  have : W.IsPrime := hWm.1.1
  rw [IntNumAssoc.list_sum_ite_mul]
  unfold idealCycle
  by_cases hr : IsRelevant W
  · rw [dite_eq_left ⟨hWm, hr⟩, if_pos hr]
    have hcount : multAt J W = (l.map fun p => if p.1 = W then (1 : ℕ∞) else 0).sum := by
      rw [hmult W]
      congr 1
      apply List.map_congr_left
      intro p hpl
      have := (hl p hpl).1
      exact h3 F K ι J p.1 W (hl p hpl).2.2 hWm
    rw [hcount, IntNumAssoc.list_sum_ite_enat, ENat.toNat_natCast]
  · rw [dite_eq_right (fun h => hr h.2), if_neg hr]
    simp

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumOfFiltration
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

namespace IntNumOfFiltration

theorem eventually_mixedDiff_sum (h1 : MixedDiffLinear.Statement)
    (h3 : EventualValueFacts.Statement) {K : Type} {n : ℕ} (bs : Fin n → K → ℤ)
    {α : Type*} (h : α → (K → ℤ) → ℤ) (s : α → K → ℤ) :
    ∀ l : List α, (∀ p ∈ l, ∃ c : ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (h p) m = c) →
      ∀ᶠ m in Filter.atTop,
        mixedDiff bs (fun m => (l.map fun p => h p (m - s p)).sum) m =
          (l.map fun p => eventualValue (mixedDiff bs (h p))).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    have h0 : (fun m : K → ℤ => (([] : List α).map fun p => h p (m - s p)).sum) = 0 := by
      funext m
      simp
    have hz : mixedDiff bs (0 : (K → ℤ) → ℤ) = 0 := by
      have := (h1 K n bs 0 0 0 0 0).2.1
      simpa using this
    refine Filter.Eventually.of_forall fun m => ?_
    rw [h0, hz]
    simp
  | cons p l ih =>
    intro hl
    obtain ⟨c, hc⟩ := hl p List.mem_cons_self
    have hsplit : (fun m : K → ℤ => ((p :: l).map fun q => h q (m - s q)).sum) =
        shiftFn (s p) (h p) + fun m => (l.map fun q => h q (m - s q)).sum := by
      funext m
      simp [shiftFn]
    have hev := (h3 K _ c (s p)).1 hc
    have hsh := (h3 K _ c (s p)).2 hc
    filter_upwards [ih fun q hq => hl q (List.mem_cons_of_mem p hq), hsh] with m hm hm'
    rw [hsplit, (h1 K n bs (shiftFn (s p) (h p)) (fun m => (l.map fun q => h q (m - s q)).sum)
      0 (s p) 0).1, (h1 K n bs (h p) 0 0 (s p) 0).2.2.1]
    simp only [Pi.add_apply, List.map_cons, List.sum_cons]
    rw [hm', hm, hev]

theorem proof (h1 : MixedDiffLinear.Statement) (h2 : DegLTEventuallyConst.Statement)
    (h3 : EventualValueFacts.Statement) : IntNumOfFiltration.Statement := by
  intro F _ K _ _ ι _ n J l hdeg hJ bs
  have hfun : hilbFn J = fun m => (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum :=
    funext hJ
  have hev := eventually_mixedDiff_sum h1 h3 bs
    (fun p : Ideal (MRing ι F) × (K → ℕ) => hilbFn p.1) (fun p k => (p.2 k : ℤ)) l
    (fun p hp => h2 K n (hilbFn p.1) (hdeg p hp) bs)
  unfold intNum
  rw [hfun]
  exact (h3 K _ _ 0).1 hev

end IntNumOfFiltration

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMixedDiffLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section MixedDiffLinearProof

variable {K : Type*}

theorem diffStep_add' (b : K → ℤ) (f g : (K → ℤ) → ℤ) :
    diffStep b (f + g) = diffStep b f + diffStep b g := by
  funext m; simp only [diffStep, Pi.add_apply]; ring

theorem diffStep_smul' (b : K → ℤ) (c : ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (c • f) = c • diffStep b f := by
  funext m; simp only [diffStep, Pi.smul_apply, smul_eq_mul]; ring

theorem diffStep_shiftFn' (b s : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (shiftFn s f) = shiftFn s (diffStep b f) := by
  funext m; simp only [diffStep, shiftFn, sub_right_comm]

theorem diffStep_comm' (b b' : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' f) = diffStep b' (diffStep b f) := by
  funext m; simp only [diffStep, sub_right_comm m b b']; ring

theorem foldr_diffStep_props (l : List (K → ℤ)) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ) :
    l.foldr diffStep (f + g) = l.foldr diffStep f + l.foldr diffStep g ∧
    l.foldr diffStep (c • f) = c • l.foldr diffStep f ∧
    l.foldr diffStep (shiftFn s f) = shiftFn s (l.foldr diffStep f) ∧
    l.foldr diffStep (diffStep b f) = diffStep b (l.foldr diffStep f) := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, diffStep_add']
    · rw [h2, diffStep_smul']
    · rw [h3, diffStep_shiftFn']
    · rw [h4, diffStep_comm']

theorem MixedDiffLinear.proof : MixedDiffLinear.Statement := by
  intro K n bs f g c s b
  obtain ⟨h1, h2, h3, h4⟩ := foldr_diffStep_props (List.ofFn bs) f g c s b
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold mixedDiff
  rw [List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.foldr_cons]

end MixedDiffLinearProof

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem localizedQuotient_subsingleton_of_not_le (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by
  obtain ⟨q, hqQ, hqW⟩ := Set.not_subset.mp h
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨q, hqW, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Q.mul_mem_right a hqQ

theorem localizedQuotient_mk_eq_zero (W : Ideal A) [W.IsPrime] (a : A) (s : W.primeCompl)
    (h : LocalizedModule.mk (Ideal.Quotient.mk W a) s = 0) : a ∈ W := by
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
  exact (‹W.IsPrime›.mem_or_mem hu).resolve_left u.2

theorem localizedQuotient_isSimpleModule (W : Ideal A) [W.IsPrime] :
    IsSimpleModule (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ W)) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk W 1) 1, 0, fun h => ?_⟩, ?_⟩
  · exact ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).mpr (localizedQuotient_mk_eq_zero W 1 1 h))
  intro x hx z
  induction x using LocalizedModule.induction_on with | h m s => ?_
  induction z using LocalizedModule.induction_on with | h m' t => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m'
  have ha : a ∈ W.primeCompl := fun haW => hx (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haW, LocalizedModule.zero_mk])
  refine ⟨Localization.mk ((s : A) * b) (⟨a, ha⟩ * t), ?_⟩
  rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul]
  congr 1
  ring

end General

theorem MultAtPrimeAtMinimal.proof : MultAtPrimeAtMinimal.Statement := by
  intro R _ K ι J Q W _ _ hJQ hW
  unfold multAt
  by_cases hQW : Q ≤ W
  · have hEq : Q = W := le_antisymm hQW (hW.2 ⟨‹Q.IsPrime›, hJQ⟩ hQW)
    subst hEq
    rw [if_pos rfl, Module.length_eq_one_iff]
    exact localizedQuotient_isSimpleModule Q
  · have hne : Q ≠ W := fun h => hQW h.le
    rw [if_neg hne, Module.length_eq_zero_iff]
    exact localizedQuotient_subsingleton_of_not_le Q W hQW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRelevantDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem RelevantDimGe.proof (h1 : BlockAdjoinPrime.Statement.{u}) : RelevantDimGe.Statement.{u} := by
  intro R _ K _ _ ι Q hQ
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let B : ℕ → Set K := fun j => {k | (e k : ℕ) < j}
  let J : ℕ → Ideal (MRing ι R) := fun j =>
    Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B j ∧ p = X v}
  have hJ : ∀ j, (J j).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B j → (X v ∈ J j ↔ X v ∈ Q) :=
    fun j => h1 R K ι Q (B j) hQ.isPrime hQ.multiHomog
  have hle : ∀ j, Q ≤ J j := fun j => le_sup_left
  have hmono : ∀ j, J j ≤ J (j + 1) := fun j =>
    sup_le_sup_left (Ideal.span_mono (by
      rintro p ⟨v, hv, rfl⟩
      exact ⟨v, lt_trans hv (Nat.lt_succ_self _), rfl⟩)) _
  have hstrict : ∀ j (hj : j < Fintype.card K), J j < J (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hmono j) ?_
    obtain ⟨i, hi⟩ := hQ.relevant (e.symm ⟨j, hj⟩)
    intro heq
    have hmem : (X ⟨e.symm ⟨j, hj⟩, i⟩ : MRing ι R) ∈ J (j + 1) :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨⟨e.symm ⟨j, hj⟩, i⟩, by simp [B], rfl⟩)
    rw [← heq] at hmem
    exact hi (((hJ j).2 ⟨e.symm ⟨j, hj⟩, i⟩ (by simp [B])).1 hmem)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (R := MRing ι R) (Q : Set (MRing ι R)) :=
    fun j => ⟨⟨J j, (hJ j).1⟩, hle j⟩
  have hf : StrictMono f := by
    refine Fin.strictMono_iff_lt_succ.2 fun j => ?_
    show J j < J (j + 1)
    exact hstrict j j.isLt
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk (Fintype.card K) f hf)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

