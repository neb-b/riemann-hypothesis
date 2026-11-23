module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0038

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace plainPolynomialPairNumber

open plainPairNumber (term rename_divDiff_eq_sum)

theorem rename_divDiff_add {r : ℕ} (l : Fin r) (A B : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l (A + B)) =
      rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l A) +
        rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l B) := by
  classical
  rw [rename_divDiff_eq_sum l (A + B) support_add,
    rename_divDiff_eq_sum l A Finset.subset_union_left,
    rename_divDiff_eq_sum l B Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem term_tail {N q : ℕ} (i : Fin N) (μ : Fin N →₀ ℕ) (t : Fin q →₀ ℕ) (ν : Fin (N + q) →₀ ℕ)
    (hc : ∀ j, ν (Fin.castAdd q j) = μ j) (hn : ∀ j, ν (Fin.natAdd N j) = t j) :
    term (Fin.castAdd q i) ν =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q)) (term i μ) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  have hlt : ∀ j : Fin q, ¬ Fin.natAdd N j < Fin.castAdd q i := by
    intro j h
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  have hgt : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd N j := by
    intro j
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hcc : ∀ j k : Fin N, (Fin.castAdd q j < Fin.castAdd q k ↔ j < k) := by
    intro j k
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h1 : (∏ j ∈ Finset.univ.filter (fun j => j < Fin.castAdd q i),
      (X (Sum.inr j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      ∏ j ∈ Finset.univ.filter (fun j => j < i), X (Sum.inr (Fin.castAdd q j)) ^ μ j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hlt, if_false, Finset.prod_const_one, mul_one, hcc, hc]
  have h3 : (∏ j ∈ Finset.univ.filter (fun j => Fin.castAdd q i < j),
      (X (Sum.inl j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      (∏ j ∈ Finset.univ.filter (fun j => i < j), X (Sum.inl (Fin.castAdd q j)) ^ μ j) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hgt, if_true, hcc, hc, hn]
  unfold term
  rw [h1, h3, hc i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_prod, map_pow, map_sum, rename_X, Sum.map_inl, Sum.map_inr]
  ring

theorem rename_monomial_tail {N q : ℕ} (t : Fin q →₀ ℕ) (c : ℤ) :
    rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) (monomial t c) =
      C c * ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, rename_X, rename_C]

theorem rename_divDiff_castAdd_monomial {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (t : Fin q →₀ ℕ) (c : ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) (monomial t c))) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q)))
          (monomial t c) := by
  classical
  set T : Fin (N + q) →₀ ℕ := t.mapDomain (Fin.natAdd N) with hT
  have hinj : Function.Injective
      (fun μ : Fin N →₀ ℕ => Finsupp.mapDomain (Fin.castAdd q) μ + T) :=
    fun a b h => Finsupp.mapDomain_injective (Fin.castAdd_injective _ _) (add_right_cancel h)
  have hsub : (rename (Fin.castAdd q) G * monomial T c).support ⊆
      G.support.image (fun μ => Finsupp.mapDomain (Fin.castAdd q) μ + T) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · have hmem : ν - T ∈ (rename (Fin.castAdd q) G).support :=
        mem_support_iff.mpr (left_ne_zero_of_mul hν)
      rw [support_rename_of_injective (Fin.castAdd_injective _ _), Finset.mem_image] at hmem
      obtain ⟨μ, hμ, he⟩ := hmem
      exact Finset.mem_image.mpr ⟨μ, hμ, by rw [he, tsub_add_cancel_of_le hle]⟩
    · exact absurd rfl hν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rename_monomial, ← hT, rename_divDiff_eq_sum (Fin.castAdd q i) _ hsub,
    Finset.sum_image fun a _ b _ h => hinj h, rename_divDiff_eq_sum i G subset_rfl, map_sum,
    Finset.sum_mul, rename_monomial_tail]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hc : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.castAdd q j) = μ j := by
    intro j
    have hj : Fin.castAdd q j ∉ Set.range (Fin.natAdd N : Fin q → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective _ _), hT,
      Finsupp.mapDomain_of_notMem_range _ _ hj, add_zero]
  have hn : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.natAdd N j) = t j := by
    intro j
    have hj : Fin.natAdd N j ∉ Set.range (Fin.castAdd q : Fin N → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hj, hT,
      Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective _ _), zero_add]
  rw [coeff_mul_monomial, coeff_rename_mapDomain _ (Fin.castAdd_injective _ _),
    term_tail i μ t _ hc hn, C_mul]
  simp only [map_mul, rename_C]
  ring

theorem rename_divDiff_castAdd_mul {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin q) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q)) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial t c => exact rename_divDiff_castAdd_monomial i G t c
  | add A B hA hB => rw [map_add (f := _), mul_add, rename_divDiff_add, hA, hB, map_add (f := _), mul_add]

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_mul_tail {σ : Type*} [DecidableEq σ] {q : ℕ} (cls : σ → K → ℤ)
    (L : Fin q → K → ℤ) (z : Fin q → σ) (hz : cls ∘ z = L) (A : MvPolynomial σ ℤ)
    (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum cls (A * rename z Q) [] W = ∑ μ ∈ Q.support, Q.coeff μ * classNum cls A (classList L μ) W := by
  have hadd : ∀ H : MvPolynomial σ ℤ, classNum cls H [] W = classNumAddHom cls [] W H := fun _ => rfl
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, hadd, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [rename_monomial, show monomial (μ.mapDomain z) (Q.coeff μ) =
      Q.coeff μ • monomial (μ.mapDomain z) (1 : ℤ) by rw [smul_monomial, smul_eq_mul, mul_one],
    mul_smul_comm, map_zsmul, smul_eq_mul, ← hadd, plainPairNumber.classNum_mul_monomial,
    classList_mapDomain, hz, List.append_nil]

theorem proof : plainPolynomialPairNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x x' f g m G hG hm q L Q hQ
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous (d + 1) := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show m + (d + 1 - m) = d + 1 by omega] at h3
  rw [BundleExamples.pairNum_eq P d _ _ _ _ hH]
  unfold pairNum
  have hr : ratDiv P 1 1 = fun _ => 0 := funext fun W => sub_self _
  have hz : ∀ n : Ideal (MRing ι O) → ℤ, cycEval n (fun _ => 0) = 0 := by
    intro n
    simp [cycEval]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hr, hz, Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hZ := ratDiv_finite_support P (f i) (g i)
  simp only [cycEval_eq_sum hZ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hcls : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      Sum.map (Fin.castAdd q) (Fin.castAdd q) = Sum.elim x x' := by
    funext p
    cases p <;> simp [Fin.append_left]
  have hL : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) = L := by
    funext j
    simp [Fin.append_right]
  rw [rename_divDiff_castAdd_mul, classNum_mul_tail _ L _ hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [plainPairNumber.classNum_rename _ (Sum.map_injective.mpr
      ⟨Fin.castAdd_injective _ _, Fin.castAdd_injective _ _⟩), hcls]
  ring

end plainPolynomialPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinRootPolyNum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace RootPolynomialNumber

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename_mul {N q : ℕ} (x : Fin N → K → ℤ) (L : Fin q → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x L) (rename Sum.inl G * rename Sum.inr Q) [] W =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
  classical
  have hQ : rename Sum.inl G * rename Sum.inr Q =
      ∑ μ ∈ Q.support, Q.coeff μ •
        (rename Sum.inl G * monomial (Finsupp.mapDomain Sum.inr μ) (1 : ℤ)) := by
    conv_lhs => rw [Q.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, ← C_mul', ← mul_one (Q.coeff μ), ← C_mul_monomial, mul_one]
    ring
  change classNumAddHom (Sum.elim x L) [] W _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hQ, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, smul_eq_mul]
  congr 1
  change classNum (Sum.elim x L) _ [] W = _
  rw [plainPairNumber.classNum_mul_monomial, plainPairNumber.classNum_rename _ Sum.inl_injective,
    classList_mapDomain, List.append_nil, Sum.elim_comp_inl, Sum.elim_comp_inr]

end RootPolynomialNumber

theorem RootPolynomialNumber.proof : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  classical
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q).IsHomogeneous d := by
    have h := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h
  have hcls : Sum.elim x L ∘ (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) =
      Fin.append x L := by
    funext i
    induction i using Fin.addCases <;> simp
  have hren : rename (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        rename Sum.inl G * rename Sum.inr Q := by
    have e1 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.castAdd q = Sum.inl := by
      funext i
      simp
    have e2 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.natAdd N = Sum.inr := by
      funext i
      simp
    rw [map_mul, rename_rename, rename_rename, e1, e2]
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hW : ∀ W : Ideal (MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
                                (specialIdeal W) d (Fin.append x L) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) finSumFinEquiv.symm (Sum.elim x L) hcls hH W,
      hren, RootPolynomialNumber.classNum_rename_mul]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [hW]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ, Finsupp.fun_support_eq]
    exact Finset.finite_toSet _
  rw [cycEval_eq_sum hfin]
  simp only [cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExpress
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem TwistedDualGensExpress.sum_mul_mem_localized {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, ∃ n : ℕ, f ^ n * t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨m, hm⟩ := ht q
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (a q * t q) = (f ^ n * a q) * (f ^ m * t q) := by ring
    rw [this]
    exact mul_mem hn hm

theorem TwistedDualGensExpress.proof : TwistedDualGensExpress.Statement := by
  unfold TwistedDualGensExpress.Statement
  intro R _ ϖ Ω _ _ K _ ι y N E _ _ B B' hsame a a' M M' φ φ' hφ hφ' c hc m
  set A := chartRing R (segreVec y) c with hA
  set w : Ω := algebraMap R Ω ϖ with hw
  have hwA : w ∈ A := Subalgebra.algebraMap_mem _ ϖ
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  set ψ : Module.Dual Ω E := (∏ k, y ⟨k, c k⟩ ^ (-a' k)) • φ' m with hψ
  have hψA : ∀ v ∈ B'.lat c, ψ v ∈ A := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := hφ'.sections c hc m v hv
    have : ψ v = s := by
      rw [hψ, LinearMap.smul_apply, hsv, smul_eq_mul, mul_comm s, ← mul_assoc,
        ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => by
          rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hy k))]), one_mul]
    rw [this]
    exact hs
  obtain ⟨k0, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  have hbq : ∀ l q, ∃ n : ℕ, f l ≠ 0 → ∃ e : ℕ, f l ^ e * (w ^ n * ψ (b l q)) ∈ A := by
    intro l q
    by_cases hl : f l = 0
    · exact ⟨0, fun h => (h hl).elim⟩
    obtain ⟨e, he⟩ := (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
        by_cases h : q' = q
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := (hsame c hc).1 _ he
    refine ⟨n, fun _ => ⟨e, ?_⟩⟩
    have h := hψA _ hn
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    rw [show f l ^ e * (w ^ n * ψ (b l q)) = w ^ n * (f l ^ e * ψ (b l q)) by ring]
    exact h
  choose nb hnb using hbq
  set n := Finset.univ.sup (fun p : Fin k0 × Fin N => nb p.1 p.2) with hn
  have hle : ∀ l q, nb l q ≤ n := fun l q =>
    Finset.le_sup (f := fun p : Fin k0 × Fin N => nb p.1 p.2) (Finset.mem_univ (l, q))
  have hmain : ∀ v ∈ B.lat c, (w ^ n • ψ) v ∈ A := by
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
    intro l
    by_cases hl : f l = 0
    · exact ⟨1, by simp [hl]⟩
    obtain ⟨a'', ha'', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨e, he⟩ := TwistedDualGensExpress.sum_mul_mem_localized A (hf l) a''
      (fun q => w ^ n * ψ (b l q)) ha'' (fun q => by
        obtain ⟨e, he⟩ := hnb l q hl
        refine ⟨e, ?_⟩
        rw [← pow_sub_mul_pow w (hle l q)]
        rw [show f l ^ e * (w ^ (n - nb l q) * w ^ nb l q * ψ (b l q)) =
          w ^ (n - nb l q) * (f l ^ e * (w ^ nb l q * ψ (b l q))) by ring]
        exact mul_mem (pow_mem hwA _) he)
    refine ⟨e, ?_⟩
    have : w ^ n * ψ v = ∑ q, a'' q * (w ^ n * ψ (b l q)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hrep, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    rw [smul_eq_mul, this]
    exact he
  obtain ⟨u, hu, hsum'⟩ := hφ.generate c hc (w ^ n • ψ) hmain
  refine ⟨n, u, hu, ?_⟩
  have hY : (∏ k, y ⟨k, c k⟩ ^ a' k) * ∏ k, y ⟨k, c k⟩ ^ (-a' k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (hy k))]
  have h1 : w ^ n • φ' m = (∏ k, y ⟨k, c k⟩ ^ a' k) • (w ^ n • ψ) := by
    rw [hψ, smul_comm (w ^ n) (∏ k, y ⟨k, c k⟩ ^ (-a' k)), smul_smul, hY, one_smul]
  rw [h1, hsum', Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul]
  congr 1
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_add₀ (hy k), sub_eq_add_neg]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeAlg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairConeAlg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∃ (l : Fin N → Fin M) (m' : Fin M'), LinearIndependent Ω (φ ∘ l) ∧
      pairProjCoord y e φ φ' t ⟨none, m'⟩ ≠ 0 ∧
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic
          (Algebra.adjoin O
            (Set.range (fun q : Σ k, ι k =>
                (C (algebraMap Ω Φ (y q)) * X (some (some q.1)) : MvPolynomial (Option (Option K)) Φ)) ∪
              Set.range (Sum.elim
                (fun i : Fin N => C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none))
                (fun _ : Unit => C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none))))
          (C (pairProjCoord y e φ φ' t p) * X p.1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureBirational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

abbrev lineBlocks (M M' : ℕ) : Option Unit → Type := bundleIdx (fun _ : Unit => Fin M) M'

section Objects

variable {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
  [Algebra Ω Φ]

def flagLinePt (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) (k : ℕ) : (Σ o, lineBlocks M M' o) → Φ
  | ⟨none, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ' l (w i))
  | ⟨some _, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ l (w i))

end Objects

def SegreFlagClosureBirational.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t → 1 ≤ N →
      IsBirationalJoin O (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t 1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

