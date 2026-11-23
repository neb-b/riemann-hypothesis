module

public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.EtaleCohomology.TateTwists.Bundle0005

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleTrace.HomRelPf
section
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

theorem homRel_aeval_scale (k K : Type) [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K)
    (H : MvPolynomial (Fin n) k) (m : ℕ) (hH : H.IsHomogeneous m) :
    aeval (fun j => Polynomial.C (v j) * Polynomial.X) H = Polynomial.C (aeval v H) * Polynomial.X ^ m := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_def, eval₂_eq, aeval_def, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : (∑ i ∈ d.support, d i) = m := by
    have := hH (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]
  rw [IsScalarTower.algebraMap_apply k K (Polynomial K), Polynomial.algebraMap_eq, mul_assoc]

theorem HomRel_of : HomRel := by
  intro k K _ _ _ d hd n hn v
  classical
  set x : Fin n → Polynomial K := fun j => Polynomial.C (v j) * Polynomial.X with hx
  have htr : Algebra.trdeg k (Polynomial K) = Algebra.trdeg k K + 1 := by
    rw [← trdeg_add_eq (R := k) (S := K) (A := Polynomial K), Polynomial.trdeg_of_isDomain]
  have hni : ¬ AlgebraicIndependent k x := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin] at h1
    have h2 : ((n : ℕ) : Cardinal) ≤ ((d + 1 : ℕ) : Cardinal) := by
      push_cast; exact h1.trans (by gcongr)
    have : n ≤ d + 1 := by exact_mod_cast h2
    omega
  rw [algebraicIndependent_iff] at hni
  push Not at hni
  obtain ⟨G, hGx, hG0⟩ := hni
  obtain ⟨m, hm⟩ : ∃ m, homogeneousComponent m G ≠ 0 := by
    by_contra h
    push Not at h
    apply hG0
    rw [← sum_homogeneousComponent G]
    exact Finset.sum_eq_zero fun i _ => h i
  refine ⟨m, homogeneousComponent m G, hm, homogeneousComponent_isHomogeneous m G, ?_⟩
  have hsum : aeval x G = ∑ i ∈ Finset.range (G.totalDegree + 1),
      Polynomial.C (aeval v (homogeneousComponent i G)) * Polynomial.X ^ i := by
    conv_lhs => rw [← sum_homogeneousComponent G]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      homRel_aeval_scale k K v _ i (homogeneousComponent_isHomogeneous i G)
  have hmem : m ∈ Finset.range (G.totalDegree + 1) := by
    rw [Finset.mem_range]
    by_contra h
    exact hm (homogeneousComponent_eq_zero m G (by omega))
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p m) (hsum.symm.trans hGx)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rwa [Finset.sum_ite_eq, if_pos hmem] at hc

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.JetIndepPf
section
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem jetIndep_chain {n : ℕ} (w : Fin n → K) (F : MvPolynomial (Fin n) k) :
    KaehlerDifferential.D k K (aeval w F) =
      ∑ j, aeval w (pderiv j F) • KaehlerDifferential.D k K (w j) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_smul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hf, pderiv_X, Finset.sum_add_distrib, mul_smul, Finset.smul_sum, Derivation.leibniz]
    simp [Pi.single_apply]
    simp only [apply_ite (aeval w), map_zero, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_smul]

theorem jetIndep_pderiv {n : ℕ} (w : Fin n → K) (hw : LinearIndependent K (jet k w)) {m : ℕ}
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous m) (h0 : aeval w F = 0) (j : Fin n) :
    aeval w (pderiv j F) = 0 := by
  have e1 := congrArg (aeval w) hF.sum_X_mul_pderiv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, aeval_X, map_nsmul, h0, smul_zero] at e1
  have e2 := jetIndep_chain w F
  rw [h0, Derivation.map_zero] at e2
  refine Fintype.linearIndependent_iff.1 hw (fun j => aeval w (pderiv j F)) ?_ j
  ext
  · simp only [jet, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]
    rw [← e1]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · simp only [jet, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero]
    exact e2.symm

theorem jetIndep_dvd {n p : ℕ} [CharP k p] (F : MvPolynomial (Fin n) k) (h : ∀ j, pderiv j F = 0)
    (α : Fin n →₀ ℕ) (hα : α ∈ F.support) (i : Fin n) : p ∣ α i := by
  rcases Nat.eq_zero_or_pos (α i) with h0 | hpos
  · simp [h0]
  have hc := congrArg (AddMonoidAlgebra.coeff · (α - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have hα' : α - Finsupp.single i 1 + Finsupp.single i 1 = α := by
    ext l
    by_cases hl : i = l
    · subst hl; simp; omega
    · simp [hl]
  rw [hα'] at hc
  have hne : AddMonoidAlgebra.coeff F α ≠ 0 := mem_support_iff.1 hα
  have h1 : (((α - Finsupp.single i 1 : Fin n →₀ ℕ) i : ℕ) : k) + 1 = 0 := (mul_eq_zero.1 hc).resolve_left hne
  have e : (α - Finsupp.single i 1 : Fin n →₀ ℕ) i + 1 = α i := by simp; omega
  rw [← CharP.cast_eq_zero_iff k p, ← e]
  exact_mod_cast h1

theorem jetIndep_root {n p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (F : MvPolynomial (Fin n) k) {m : ℕ} (hF : F.IsHomogeneous m) (hd : ∀ α ∈ F.support, ∀ i, p ∣ α i) :
    ∃ G : MvPolynomial (Fin n) k, G.IsHomogeneous (m / p) ∧ F = G ^ p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let q : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun α => Finsupp.mapRange (· / p) (Nat.zero_div p) α
  have hq : ∀ α ∈ F.support, p • q α = α := by
    intro α hα; ext i; simp [q, Nat.mul_div_cancel' (hd α hα i)]
  refine ⟨∑ α ∈ F.support, monomial (q α) ((frobeniusEquiv k p).symm (AddMonoidAlgebra.coeff F α)), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro α hα
    apply isHomogeneous_monomial
    have hm : α.degree = m := by
      have := hF (mem_support_iff.1 hα)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have : p * (q α).degree = m := by
      have h2 := congrArg Finsupp.degree (hq α hα)
      rw [map_nsmul, smul_eq_mul] at h2
      rw [h2, hm]
    rw [← this, Nat.mul_div_cancel_left _ hp]
  · rw [sum_pow_char]
    conv_lhs => rw [F.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [monomial_pow, frobeniusEquiv_symm_pow_p, hq α hα]

theorem JetIndep_of : JetIndep := by
  intro k K _ _ _ _ n w hw m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hF h0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · by_contra hne
    have ht := hF.totalDegree hne
    rw [totalDegree_eq_zero_iff_eq_C] at ht
    rw [ht, aeval_C, map_eq_zero_iff _ (algebraMap k K).injective] at h0
    exact hne (by rw [ht, h0, C_0])
  have hpd : ∀ j, pderiv j F = 0 := fun j =>
    ih (m - 1) (by omega) _ hF.pderiv (jetIndep_pderiv w hw F hF h0 j)
  obtain ⟨p, hcp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · have := Fact.mk hpp
    have : ExpChar k p := ExpChar.prime hpp
    have : PerfectRing k p := PerfectField.toPerfectRing p
    obtain ⟨G, hG, rfl⟩ := jetIndep_root F hF (fun α hα i => jetIndep_dvd F hpd α hα i)
    rw [map_pow] at h0
    have hG0 := ih (m / p) (Nat.div_lt_self hm hpp.one_lt) G hG (pow_eq_zero_iff hpp.ne_zero |>.1 h0)
    rw [hG0, zero_pow hpp.ne_zero]
  · ext α
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hc
    have hα0 : α = 0 := by
      ext i; simpa using jetIndep_dvd (p := 0) F hpd α (mem_support_iff.2 hc) i
    have := hF hc
    subst hα0
    simp at this
    omega

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.JetSpanPf
section
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.JetSpanPf

variable {k K : Type} [Field k] [Field K] [Algebra k K]

lemma aeval_mem_adj {n : ℕ} (v : Fin n → K) (g : MvPolynomial (Fin n) k) :
    aeval v g ∈ Algebra.adjoin k (Set.range v) := by
  rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨g, rfl⟩

lemma essFT {n : ℕ} (v : Fin n → K)
    (hz : ∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) :
    Algebra.EssFiniteType k K := by
  classical
  rw [Algebra.essFiniteType_iff]
  refine ⟨Finset.univ.image v, fun z => ?_⟩
  have hs : ((Finset.univ.image v : Finset K) : Set K) = Set.range v := by simp
  rw [hs]
  obtain ⟨f, g, rfl⟩ := hz z
  by_cases h : aeval v f = 0
  · refine ⟨1, Subalgebra.one_mem _, isUnit_one, ?_⟩
    simp [h]
  · refine ⟨aeval v f, aeval_mem_adj v f, IsUnit.mk0 _ h, ?_⟩
    rw [div_mul_cancel₀ _ h]; exact aeval_mem_adj v g

def T {n : ℕ} (v : Fin n → K) : Submodule K Ω[K⁄k] :=
  (Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))).comap (LinearMap.inr K K Ω[K⁄k])

lemma fst_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (x : K) :
    ((x, 0) : K × Ω[K⁄k]) ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v)) := by
  have h := Submodule.smul_mem (Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))) x
    (Submodule.subset_span ⟨i, rfl⟩)
  simpa [LateralTheory.EtaleTrace.Cov.jet, hi] using h

lemma dv_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (j : Fin n) :
    KaehlerDifferential.D k K (v j) ∈ T v := by
  have h1 : LateralTheory.EtaleTrace.Cov.jet k v j ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v)) :=
    Submodule.subset_span ⟨j, rfl⟩
  have h2 := Submodule.sub_mem _ h1 (fst_mem v i hi (v j))
  show LinearMap.inr K K Ω[K⁄k] (KaehlerDifferential.D k K (v j)) ∈
    Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))
  convert h2 using 1
  simp [LateralTheory.EtaleTrace.Cov.jet]

lemma dpoly_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (g : MvPolynomial (Fin n) k) :
    KaehlerDifferential.D k K (aeval v g) ∈ T v := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hp hq
  | mul_X p j hp =>
    rw [map_mul, aeval_X, Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (dv_mem v i hi j)) (Submodule.smul_mem _ _ hp)

lemma dall_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1)
    (hz : ∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) (z : K) :
    KaehlerDifferential.D k K z ∈ T v := by
  obtain ⟨f, g, hfg⟩ := hz z
  by_cases h : aeval v f = 0
  · rw [hfg, h, div_zero, map_zero]; exact Submodule.zero_mem _
  · have hg : aeval v g = z * aeval v f := by rw [hfg, div_mul_cancel₀ _ h]
    have key := congrArg (KaehlerDifferential.D k K) hg
    rw [Derivation.leibniz] at key

    have : KaehlerDifferential.D k K z =
        (aeval v f)⁻¹ • (KaehlerDifferential.D k K (aeval v g) - z • KaehlerDifferential.D k K (aeval v f)) := by
      rw [key, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (dpoly_mem v i hi g)
      (Submodule.smul_mem _ _ (dpoly_mem v i hi f)))

end LateralTheory.EtaleTrace.JetSpanPf

open LateralTheory.EtaleTrace.JetSpanPf in
theorem LateralTheory.EtaleTrace.Cov.JetSpan_of : LateralTheory.EtaleTrace.Cov.JetSpan := by
  intro k K _ _ _ n v i hi hz
  refine ⟨?_, essFT v hz⟩
  rw [eq_top_iff]
  rintro ⟨x, ω⟩ -
  have hω : ω ∈ T (k := k) v := by
    have : (⊤ : Submodule K Ω[K⁄k]) ≤ T v := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
      rintro _ ⟨z, rfl⟩; exact dall_mem v i hi hz z
    exact this Submodule.mem_top
  have : ((x, ω) : K × Ω[K⁄k]) = (x, 0) + LinearMap.inr K K Ω[K⁄k] ω := by simp
  rw [this]
  exact Submodule.add_mem _ (fst_mem v i hi x) hω
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LCompIntPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem LCompInt_of : LCompInt := by
  intro k _ _ d X p hp hc
  have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  exact GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace p

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LTwoEpiPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem ltwo_fm (R : Type) [CommRing R] {X Y : Type} (g : X ⟶ Y) (x : X) :
    ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map g)).hom
      (ModuleCat.freeMk (X := uliftFunctor.{1}.obj X) (ULift.up x)) =
      ModuleCat.freeMk (X := uliftFunctor.{1}.obj Y) (ULift.up (g x)) :=
  Finsupp.mapDomain_single

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.ProjectPf
section
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

lemma pf_div_mem {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K) (O : Subring K)
    (hk : ∀ c : k, algebraMap k K c ∈ O) (y : K) (hv : ∀ j, v j / y ∈ O) (x : K)
    (hx : x ∈ Submodule.span k (Set.range v)) : x / y ∈ O := by
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨j, rfl⟩ := hz; exact hv j
  | zero => simp
  | add a b _ _ ha hb => rw [add_div]; exact O.add_mem ha hb
  | smul c a _ ha => rw [Algebra.smul_def, mul_div_assoc]; exact O.mul_mem (hk c) ha

lemma pf_finrank {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) :
    Module.Finite K (K × Ω[K⁄k]) ∧ Module.finrank K (K × Ω[K⁄k]) = d + 1 := by
  have hf : Module.Finite K (K × Ω[K⁄k]) := ⟨by rw [← hv]; exact Submodule.fg_span (Set.finite_range _)⟩
  have : Module.Finite K Ω[K⁄k] := Module.Finite.of_surjective (LinearMap.snd K K Ω[K⁄k]) LinearMap.snd_surjective
  refine ⟨hf, ?_⟩
  rw [Module.finrank_prod, Module.finrank_self, hd]; omega

lemma pf_card {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) : d + 1 ≤ n := by
  obtain ⟨_, h⟩ := pf_finrank d hd v hv
  have := finrank_range_le_card (R := K) (jet k v)
  have e := congrArg (fun s : Submodule K (K × Ω[K⁄k]) => Module.finrank K s) hv
  simp only [finrank_top] at e
  simp only [Set.finrank, Fintype.card_fin] at this
  omega

theorem Project_of (hStep : Step) (hHom : HomRel) : Project := by
  intro k K _ _ _ _ d hd htr n v hv
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (pf_card d hd v hv)
  induction m with
  | zero =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    refine ⟨v, fun i => Submodule.subset_span ⟨i, rfl⟩, hv,
      linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hr]), ?_⟩
    intro O _ _ h; exact h
  | succ m ih =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    have hdep : ¬ LinearIndependent K (jet k v) := by
      intro hl
      have := hl.fintype_card_le_finrank
      simp [hr] at this
    obtain ⟨e, F, hF0, hFh, hFv⟩ := hHom k K d htr (d + 1 + (m + 1)) (by omega) v
    obtain ⟨w', hw'k, hw'sp, hw'O⟩ := hStep k K (d + 1 + m) v e F hF0 hFh hFv hdep
    obtain ⟨w, hwk, hwsp, hwli, hwO⟩ := ih w' (hw'sp.trans hv)
    refine ⟨w, fun i => ?_, hwsp, hwli, ?_⟩
    · exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hw'k j) (hwk i)
    · intro O hO hk h
      obtain ⟨i, hi, hiO⟩ := hw'O O hO hk h
      obtain ⟨l, hl, hlO⟩ := hwO O hO hk ⟨i, hi, fun j => pf_div_mem v O hk _ hiO _ (hw'k j)⟩
      refine ⟨l, hl, fun j => ?_⟩
      have : v j / w l = (v j / w' i) * (w' i / w l) := by field_simp
      rw [this]; exact O.mul_mem (hiO j) (hlO i)

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EtaleTrace

def PtCover : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (T : Sieve (S k)), T ∈ Scheme.etaleTopology (S k) → T.arrows (𝟙 _)

def TwZero : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  GlobalTheory.EtC.twGen (U := U) 0 ζ = GlobalTheory.EtC.twGen (U := U) 0 ξ

def EvNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X U : Scheme.{0}) (α : CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
  (x : U ⟶ X), ev (R := R) α 0 0 (by simp) U x = Sec.res x (ev (R := R) α 0 0 (by simp) X (𝟙 X))

def CocEq : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
    ev (R := R) α.1 0 0 (by simp) U x = ev (R := R) β.1 0 0 (by simp) U x) → α = β

theorem exists_prim (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    Nonempty (Prim (l ^ j) Γ(S k, ⊤)) := by
  have hq : 0 < l ^ j := pow_pos (Fact.out : l.Prime).pos j
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ j) k)
    (Polynomial.degree_cyclotomic_pos (l ^ j) k hq).ne'
  have hu : IsUnit ((l ^ j : ℕ) : k) := by
    rw [Nat.cast_pow]; exact (isUnit_iff_ne_zero.2 hl).pow j
  have hr' : Polynomial.aeval r (Polynomial.cyclotomic (l ^ j) ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hr
  exact ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ⟨r, hu, hr'⟩⟩

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TrdegLePf
section
noncomputable section
open Cardinal IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.EtaleTrace.Cov

theorem kaehler_adjoin_subsingleton (k K : Type) [Field k] [Field K] [Algebra k K] (s : Set K)
    (hs : Submodule.span K (KaehlerDifferential.D k K '' s) = ⊤) :
    Subsingleton Ω[K⁄(IntermediateField.adjoin k s)] := by
  set L := IntermediateField.adjoin k s
  have hD : ∀ x : K, KaehlerDifferential.D L K x = 0 := by
    intro x
    have hx : KaehlerDifferential.D k K x ∈ Submodule.span K (KaehlerDifferential.D k K '' s) := by
      rw [hs]; trivial
    have h2 := Submodule.mem_map_of_mem (f := KaehlerDifferential.map k L K K) hx
    rw [Submodule.map_span, KaehlerDifferential.map_D] at h2
    have h3 : (KaehlerDifferential.map k L K K) '' (KaehlerDifferential.D k K '' s) ⊆ {0} := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      have : y = algebraMap L K ⟨y, IntermediateField.subset_adjoin k s hy⟩ := rfl
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Set.mem_singleton_iff]
      rw [this, Derivation.map_algebraMap]
    have h4 := Submodule.span_mono h3 h2
    simpa using h4
  have htop := KaehlerDifferential.span_range_derivation L K
  have hbot : Submodule.span K (Set.range (KaehlerDifferential.D L K)) = ⊥ := by
    rw [Submodule.span_eq_bot]; rintro _ ⟨x, rfl⟩; exact hD x
  rw [hbot] at htop
  constructor; intro a b
  have ha : a ∈ (⊥ : Submodule K Ω[K⁄L]) := by rw [htop]; trivial
  have hb : b ∈ (⊥ : Submodule K Ω[K⁄L]) := by rw [htop]; trivial
  rw [Submodule.mem_bot] at ha hb; rw [ha, hb]

theorem TrdegLe_of : TrdegLe := by
  intro k K _ _ _ _
  obtain ⟨b, hbs, hbsp, hbli⟩ := exists_linearIndependent K (Set.range (KaehlerDifferential.D k K))
  rw [KaehlerDifferential.span_range_derivation] at hbsp
  have hpre : ∀ ω : b, ∃ y : K, KaehlerDifferential.D k K y = ω := fun ω => hbs ω.2
  choose t ht using hpre
  set s : Set K := Set.range t
  have himg : KaehlerDifferential.D k K '' s = b := by
    ext ω; constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; rw [ht]; exact i.2
    · intro hω; exact ⟨t ⟨ω, hω⟩, ⟨_, rfl⟩, ht _⟩
  have hsub := kaehler_adjoin_subsingleton k K s (by rw [himg, hbsp])
  set L := IntermediateField.adjoin k s
  have : Algebra.FormallyUnramified L K := ⟨hsub⟩
  have : Algebra.EssFiniteType L K := Algebra.EssFiniteType.of_comp k L K
  have : Algebra.IsSeparable L K := (Algebra.FormallyUnramified.iff_isSeparable L K).mp inferInstance
  have : Algebra.IsAlgebraic (Algebra.adjoin k s) K := Algebra.IsAlgebraic.trans _ L K
  have h1 := Algebra.IsAlgebraic.trdeg_le_cardinalMk k s (A := K)
  have h2 : #s ≤ #b := Cardinal.mk_range_le
  have h3 : #b = (Module.finrank K Ω[K⁄k] : Cardinal) := by
    rw [Module.finrank_eq_rank, ← (Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbsp]))).mk_eq_rank'']
  exact h1.trans (h2.trans h3.le)

end LateralTheory.EtaleTrace.Cov
end
end

