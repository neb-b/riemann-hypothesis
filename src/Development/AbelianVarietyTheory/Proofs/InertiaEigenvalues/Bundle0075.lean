module

public import Mathlib
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
section
open ReciprocityTheory.Gal

namespace GlobalTheory.PrimeToNormalVanishing

section Algebra

variable {G Q R M : Type} [Group G] [Group Q] [CommRing R] [AddCommGroup M] [Module R M]
  (ρ : Representation R G M) (π : G →* Q) (J : Subgroup G) (K : Subgroup Q) [Fintype K]

theorem sum_shift [hK : K.Normal] (φ : Q → M) (a k : Q) (hk : k ∈ K) :
    ∑ i : K, φ (k * (a * i)) = ∑ i : K, φ (a * i) := by
  have h : a⁻¹ * k * a ∈ K := by simpa using hK.conj_mem k hk a⁻¹
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨_, h⟩ : K)) _ _ fun i => ?_
  simp [mul_assoc]

theorem two_variables [K.Normal] (hJK : ∀ j ∈ J, π j ∈ K)
    (hinv : ∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) (F : Q → Q → M)
    (heq : ∀ g a b, F (π g * a) (π g * b) = ρ g (F a b))
    (hc : ∀ a b c, F b c - F a c + F a b = 0) :
    ∃ m : M, ∀ g, (Fintype.card K) ^ 2 • F 1 (π g) = ρ g m - m := by
  have hS : ∀ a b, ∑ i : K, ∑ j : K, F (a * i) (b * j) = 0 := by
    intro a b
    refine hinv _ fun g hg => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ← heq]
    rw [← sum_shift K (fun x => ∑ j : K, F x (b * j)) a _ (hJK g hg)]
    exact Finset.sum_congr rfl fun i _ => sum_shift K (fun x => F _ x) b _ (hJK g hg)
  have key : ∀ a b, (Fintype.card K) ^ 2 • F a b =
      Fintype.card K • ∑ i : K, F a (a * i) - Fintype.card K • ∑ i : K, F b (b * i) := by
    intro a b
    have e : ∀ a' b', F a b = F a' b' + F a a' - F b b' := by
      intro a' b'
      have e1 := hc a a' b'
      have e2 := hc a b b'
      rw [← sub_eq_zero, ← sub_self (0 : M)]
      nth_rewrite 1 [← e2]
      rw [← e1]; abel
    calc _ = ∑ i : K, ∑ j : K, F a b := by simp [pow_two, mul_smul]
      _ = ∑ i : K, ∑ j : K, (F (a * i) (b * j) + F a (a * i) - F b (b * j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e _ _
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, zero_add, Finset.sum_const,
          Finset.card_univ, ← Finset.smul_sum]
  refine ⟨-(Fintype.card K • ∑ i : K, F 1 (1 * i)), fun g => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_neg, map_nsmul, map_sum]
  simp only [← heq, mul_one, one_mul]
  abel

theorem three_variables [K.Normal] (hJK : ∀ j ∈ J, π j ∈ K)
    (hinv : ∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) (F : Q → Q → Q → M)
    (heq : ∀ g a b c, F (π g * a) (π g * b) (π g * c) = ρ g (F a b c))
    (hc : ∀ a b c d, F b c d - F a c d + F a b d - F a b c = 0) :
    ∃ H : Q → M, ∀ g h, (Fintype.card K) ^ 3 • F 1 (π g) (π (g * h)) =
      ρ g (H (π h)) - H (π (g * h)) + H (π g) := by
  have hS : ∀ a b c, ∑ i : K, ∑ j : K, ∑ k : K, F (a * i) (b * j) (c * k) = 0 := by
    intro a b c
    refine hinv _ fun g hg => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ← heq]
    rw [← sum_shift K (fun x => ∑ j : K, ∑ k : K, F x (b * j) (c * k)) a _ (hJK g hg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_shift K (fun x => ∑ k : K, F _ x (c * k)) b _ (hJK g hg)]
    exact Finset.sum_congr rfl fun i _ => sum_shift K (fun x => F _ _ x) c _ (hJK g hg)
  let H : Q → Q → M := fun a b =>
    Fintype.card K • ∑ i : K, ∑ j : K, (F a b (b * j) - F a (a * i) (b * j))
  have key : ∀ a b c, (Fintype.card K) ^ 3 • F a b c = H b c - H a c + H a b := by
    intro a b c
    have e : ∀ a' b' c', F a b c = F a' b' c' + (F b c c' - F b b' c') - (F a c c' - F a a' c')
        + (F a b b' - F a a' b') := by
      intro a' b' c'
      have e1 := hc a a' b' c'
      have e2 := hc a b b' c'
      have e3 := hc a b c c'
      have e4 : (0 : M) = 0 - 0 - 0 := by simp
      rw [← sub_eq_zero, e4]
      nth_rewrite 1 [← e2]
      nth_rewrite 1 [← e1]
      rw [← e3]; abel
    calc _ = ∑ i : K, ∑ j : K, ∑ k : K, F a b c := by simp [pow_succ, mul_smul]
      _ = ∑ i : K, ∑ j : K, ∑ k : K, (F (a * i) (b * j) (c * k) +
          (F b c (c * k) - F b (b * j) (c * k)) - (F a c (c * k) - F a (a * i) (c * k))
          + (F a b (b * j) - F a (a * i) (b * j))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => e _ _ _
      _ = _ := by
        simp only [H, Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, zero_add, Finset.sum_const,
          Finset.card_univ, ← Finset.smul_sum, smul_sub]
  have hH : ∀ g a b, H (π g * a) (π g * b) = ρ g (H a b) := by
    intro g a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, map_nsmul, map_sum, map_sub, ← heq, mul_assoc]
  refine ⟨H 1, fun g h => ?_⟩
  rw [key, ← hH, mul_one, map_mul]

theorem exists_inverse {X : Type} [Finite X] (l N : ℕ) (hN : Nat.Coprime N l)
    (htor : ∀ m : M, ∃ n, l ^ n • m = 0) (φ : X → M) : ∃ a : ℤ, ∀ x, a • N • φ x = φ x := by
  choose n hn using htor
  obtain ⟨k, hk⟩ := (Set.finite_range fun x => n (φ x)).bddAbove
  have h0 : ∀ x, l ^ k • φ x = 0 := fun x => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (hk ⟨x, rfl⟩)
    rw [hd, pow_add, mul_smul, hn, smul_zero]
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (hN.pow_right k)
  refine ⟨a, fun x => ?_⟩
  have : (a * N + b * (l ^ k : ℕ)) • φ x = φ x := by rw [hab, one_smul]
  rwa [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, h0, smul_zero, add_zero] at this

theorem card_coprime (l : ℕ) (hl : l.Prime) (h : ∀ k ∈ K, ∃ n, Nat.Coprime n l ∧ k ^ n = 1) :
    Nat.Coprime (Fintype.card K) l := by
  rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
  obtain ⟨n, hn, hxn⟩ := h x x.2
  have : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxn))
  rw [hx] at this
  exact hl.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hn this dvd_rfl)

end Algebra

theorem exists_level {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace M]
    [DiscreteTopology M] (F : Γ × Γ × Γ → M) (hF : Continuous F) :
    ∃ U : OpenNormalSubgroup Γ, ∃ F' : Γ ⧸ U.toSubgroup → Γ ⧸ U.toSubgroup → Γ ⧸ U.toSubgroup → M,
      ∀ a b c : Γ, F' a b c = F (a, b, c) := by
  have h1 : ∀ᶠ u in nhds (1 : Γ × Γ × Γ), ∀ x ∈ (Set.univ : Set (Γ × Γ × Γ)), F (x * u) = F x := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun x _ => ?_
    have ho : IsOpen {z : (Γ × Γ × Γ) × (Γ × Γ × Γ) | F (z.2 * z.1) = F z.2} :=
      (isOpen_discrete {p : M × M | p.1 = p.2}).preimage
        (f := fun z : (Γ × Γ × Γ) × (Γ × Γ × Γ) => (F (z.2 * z.1), F z.2)) (by fun_prop)
    exact ho.mem_nhds (by simp)
  obtain ⟨A, hA, BC, hBC, h2⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨B, hB, C, hC, h3⟩ := mem_nhds_prod_iff.1 hBC
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (Filter.inter_mem hA (Filter.inter_mem hB hC))
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo hW1
  refine ⟨U, fun a b c => F (a.out, b.out, c.out), fun a b c => ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup a
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup b
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup c
  simp only [hu, hv, hw]
  exact h2 (a := ((u : Γ), (v : Γ), (w : Γ))) ⟨(hW (hU u.2)).1,
    h3 ⟨(hW (hU v.2)).2.1, (hW (hU w.2)).2.2⟩⟩ (a, b, c) trivial

theorem cohomology_vanishes : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (l : ℕ) (J : Subgroup Γ), l.Prime → J.Normal → IsClosed (J : Set Γ) → (∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∀ j ∈ J, ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U) → ContAction ρ → (∀ m : M, ∃ n, l ^ n • m = 0) → (∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) → H0 ρ = ⊥ ∧ Subsingleton (H1 ρ) ∧ Subsingleton (H2 ρ) := by
  intro Γ _ _ _ _ _ _ R M _ _ _ _ _ _ ρ l J hl hJ _ hord hρ htor hinv
  classical
  have hcop : ∀ (U : OpenNormalSubgroup Γ) [Fintype (J.map (QuotientGroup.mk' U.toSubgroup))],
      Nat.Coprime (Fintype.card (J.map (QuotientGroup.mk' U.toSubgroup))) l := by
    intro U _
    refine card_coprime _ l hl ?_
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨n, hn, hjn⟩ := hord U.toSubgroup inferInstance U.isOpen j hj
    exact ⟨n, hn, by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hjn⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Submodule.eq_bot_iff _).2 fun m hm => hinv m fun j _ => hm j
  · refine Submodule.Quotient.subsingleton_iff.2 (Submodule.eq_top_iff'.2 ?_)
    rintro ⟨f, hf, hfc⟩
    obtain ⟨U, F, hF⟩ := exists_level (fun p : Γ × Γ × Γ => ρ p.1 (f (p.1⁻¹ * p.2.1)))
      (hρ.comp (continuous_fst.prodMk (hf.comp (by fun_prop))))
    haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    haveI := Fintype.ofFinite (J.map (QuotientGroup.mk' U.toSubgroup))
    haveI := hJ.map _ (QuotientGroup.mk'_surjective U.toSubgroup)
    have hF' : ∀ a b : Γ, F a b 1 = ρ a (f (a⁻¹ * b)) := fun a b => hF a b 1
    obtain ⟨m, hm⟩ := two_variables ρ (QuotientGroup.mk' U.toSubgroup) J
      (J.map (QuotientGroup.mk' U.toSubgroup)) (fun j hj => ⟨j, hj, rfl⟩) hinv
      (fun a b => F a b 1) (by
        intro g a b
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hF']
        simp [mul_assoc]) (by
        intro a b c
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        induction c using QuotientGroup.induction_on with | H c => ?_
        have e := hfc (a⁻¹ * b) (b⁻¹ * c)
        have e' : a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := by group
        simp only [hF']
        rw [← e', e, map_add (f := _), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        abel)
    obtain ⟨a, ha⟩ := exists_inverse l _ ((hcop U).pow_left 2) htor (fun q => F 1 q 1)
    refine (mem_coboundaries1 ρ _).2 ⟨a • m, fun g => ?_⟩
    have e := ha g
    have e2 := hF 1 g 1
    have e3 := hm g
    simp only [QuotientGroup.mk'_apply] at e3
    rw [e3] at e
    rw [map_zsmul, ← smul_sub, e, ← QuotientGroup.mk_one, e2]
    simp
  · refine Submodule.Quotient.subsingleton_iff.2 (Submodule.eq_top_iff'.2 ?_)
    rintro ⟨f, hf, hfc⟩
    obtain ⟨U, F, hF⟩ := exists_level
      (fun p : Γ × Γ × Γ => ρ p.1 (f (p.1⁻¹ * p.2.1, p.2.1⁻¹ * p.2.2)))
      (hρ.comp (continuous_fst.prodMk (hf.comp (by fun_prop))))
    haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    haveI : DiscreteTopology (Γ ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
    haveI := Fintype.ofFinite (J.map (QuotientGroup.mk' U.toSubgroup))
    haveI := hJ.map _ (QuotientGroup.mk'_surjective U.toSubgroup)
    simp only at hF
    obtain ⟨H, hH⟩ := three_variables ρ (QuotientGroup.mk' U.toSubgroup) J
      (J.map (QuotientGroup.mk' U.toSubgroup)) (fun j hj => ⟨j, hj, rfl⟩) hinv F (by
        intro g a b c
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        induction c using QuotientGroup.induction_on
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hF]
        simp [mul_assoc]) (by
        intro a b c d
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        induction c using QuotientGroup.induction_on with | H c => ?_
        induction d using QuotientGroup.induction_on with | H d => ?_
        have e := congrArg (ρ a) (hfc (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d))
        have e1 : a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := by group
        have e2 : b⁻¹ * c * (c⁻¹ * d) = b⁻¹ * d := by group
        rw [e1, e2, map_sub, map_add (f := _), map_sub, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel_left, map_zero] at e
        simp only [hF]
        exact e)
    obtain ⟨a, ha⟩ := exists_inverse l _ ((hcop U).pow_left 3) htor
      (fun q : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) => F 1 q.1 q.2)
    refine (separated_dvr_second_cohomology_mem ρ _).2 ⟨fun g => a • H g, ?_, ?_⟩
    · exact (continuous_of_discreteTopology (f := fun q => a • H q)).comp QuotientGroup.continuous_mk
    · funext ⟨g, h⟩
      have e := ha ((g : Γ ⧸ U.toSubgroup), ((g * h : Γ) : Γ ⧸ U.toSubgroup))
      have e2 := hF 1 g (g * h)
      have e3 := hH g h
      simp only [QuotientGroup.mk'_apply] at e3
      simp only at e
      rw [e3] at e
      rw [d1_apply, map_zsmul, ← smul_sub, ← smul_add, e, ← QuotientGroup.mk_one, e2]
      simp

end GlobalTheory.PrimeToNormalVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnHermitianBlockMatrixOfInvariants
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.ImgSec

theorem continuousOn_mkX_of_isUnit_det (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E)
    (hc : ContinuousOn h Ω) (hd : ∀ a ∈ Ω, IsUnit (h a).det) :
    ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by
  haveI := GlobalTheory.JR.ImgSec.continuousStar (E := E) F
  have hinv : ContinuousOn (fun a => (h a)⁻¹) Ω := by
    intro a ha
    exact (continuousAt_matrix_inv (h a)
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hd a ha).ne_zero)).comp_continuousWithinAt (hc a ha)
  have hmap : Continuous (fun a : Inv r F => (hankelShift a).map (algebraMap F E)) :=
    continuous_matrix fun i j => (continuous_algebraMap F E).comp
      ((continuous_apply_apply i j).comp continuous_hankelShift)
  have h1 : ContinuousOn (fun a => star (h a)⁻¹ * (hankelShift a).map (algebraMap F E) * (h a)⁻¹) Ω :=
    (hinv.star.mul hmap.continuousOn).mul hinv
  have h2 : ContinuousOn (fun a => h a *ᵥ (e1 : Fin r → E)) Ω := by
    exact (continuous_id.matrix_mulVec continuous_const).comp_continuousOn hc
  have h3 : Continuous (fun a : Inv r F => a.2.2) := continuous_snd.comp continuous_snd
  have h1' : ContinuousOn (fun a => (GlobalTheory.JR.ImgSec.mkX a (h a)).1) Ω := by
    intro a ha
    exact Topology.IsInducing.subtypeVal.continuousWithinAt_iff.2 (h1 a ha)
  exact h1'.prodMk (h2.prodMk h3.continuousOn)

end GlobalTheory.JR.ImgSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCommutatorMapEqCharpolyResultant
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.DetAdResultant
theorem det_aeval_eq_resultant_of_splits {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (g : K[X]) (hg : g.Monic) (hs : g.Splits) :
    (aeval A g).det = resultant A.charpoly g := by
  rw [resultant_comm, resultant_eq_prod_eval g A.charpoly _ le_rfl hs, hg.leadingCoeff, one_pow, one_mul]
  let φ : K[X] →* K := Matrix.detMonoidHom.comp (aeval A).toMonoidHom
  have hφ : ∀ p, φ p = (aeval A p).det := fun p => rfl
  have h1 : ∀ x : K, φ (X - C x) = (-1) ^ Fintype.card ι * eval x A.charpoly := by
    intro x
    rw [hφ]
    simp only [map_sub, aeval_X, aeval_C, Matrix.eval_charpoly]
    rw [← Matrix.det_neg, neg_sub]
    rfl
  rw [← hφ]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hg]
  rw [map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, h1]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← pow_mul,
    Matrix.charpoly_natDegree_eq_dim, ← hs.natDegree_eq_card_roots]

theorem det_aeval_eq_resultant {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι E) (g : E[X]) (hg : g.Monic) :
    (aeval A g).det = resultant A.charpoly g := by
  let K := AlgebraicClosure E
  apply (algebraMap E K).injective
  have h := det_aeval_eq_resultant_of_splits (A.map (algebraMap E K)) (g.map (algebraMap E K))
    (hg.map _) (IsAlgClosed.splits _)
  rw [Matrix.charpoly_map, natDegree_map, natDegree_map, resultant_map_map] at h
  rw [← h, RingHom.map_det]
  congr 1
  have e : (algebraMap E K).mapMatrix (aeval A g) = (Algebra.ofId E K).mapMatrix (aeval A g) := rfl
  rw [e, ← aeval_algHom_apply, aeval_map_algebraMap]
  rfl
theorem det_det_charmatrix {E : Type} [Field E] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ E) (B : Matrix ι₂ ι₂ E) :
    ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix B.transpose).map (aeval A).toRingHom)).det =
      resultant A.charpoly B.charpoly := by
  rw [← Matrix.det_det, ← Matrix.charpoly, Matrix.charpoly_transpose]
  exact det_aeval_eq_resultant A B.charpoly (Matrix.charpoly_monic B)

theorem toMatrix_ad {E : Type} [Field E] {V₁ V₂ : Type} [AddCommGroup V₁] [Module E V₁]
    [AddCommGroup V₂] [Module E V₂] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (b₁ : Module.Basis ι₁ E V₁) (b₂ : Module.Basis ι₂ E V₂)
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂) :
    LinearMap.toMatrix (b₂.linearMap b₁) (b₂.linearMap b₁)
        (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      Matrix.reindex (Equiv.prodComm ι₂ ι₁) (Equiv.prodComm ι₂ ι₁)
        ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix (LinearMap.toMatrix b₂ b₂ f₂).transpose).map
          (aeval (LinearMap.toMatrix b₁ b₁ f₁)).toRingHom)) := by
  ext ⟨a, j⟩ ⟨b, k⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.linearMap_repr_apply]
  have hr : ∀ M : Matrix ι₁ ι₂ E, (Matrix.stdBasis E ι₁ ι₂).repr M (a, j) = M a j := fun M => rfl
  have hψ : LinearMap.toMatrix b₂ b₁ (b₂.linearMap b₁ (b, k)) = Matrix.single b k 1 := by
    simp [Module.Basis.linearMap, Matrix.stdBasis_eq_single]
  rw [hr, LinearMap.sub_apply, LinearMap.llcomp_apply', LinearMap.lcomp_apply', map_sub,
    LinearMap.toMatrix_comp b₂ b₁ b₁, LinearMap.toMatrix_comp b₂ b₂ b₁, hψ]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Matrix.comp_apply, Matrix.map_apply, Matrix.charmatrix_apply, Matrix.transpose_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply, hjk, Matrix.diagonal_apply_ne _ hjk]
    by_cases hab : a = b
    · subst hab; simp [Ne.symm hjk]
    · simp [hab, Ne.symm hab, Ne.symm hjk]

theorem det_ad_eq_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁]
    [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂),
    LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      resultant f₁.charpoly f₂.charpoly := by
  intro E _ V₁ V₂ _ _ _ _ _ _ f₁ f₂
  let b₁ := Module.finBasis E V₁
  let b₂ := Module.finBasis E V₂
  rw [← LinearMap.det_toMatrix (b₂.linearMap b₁), toMatrix_ad b₁ b₂, Matrix.det_reindex_self,
    det_det_charmatrix, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

end GlobalTheory.DetAdResultant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
section
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ModuleNorm

theorem distribHaarChar_transport {G H A B : Type} [Group G] [Group H]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [T2Space B] [SecondCountableTopology B] [DistribMulAction H B] [ContinuousConstSMul H B]
    (e : A ≃ₜ+ B) (g : G) (h : H) (he : ∀ x, e (g • x) = h • e x) :
    distribHaarChar B h = distribHaarChar A g := by
  borelize A B
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hmap : ∀ s : Set B, ((Measure.addHaar : Measure A).map e) s = (Measure.addHaar : Measure A) (e ⁻¹' s) :=
    fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  have key : ∀ x, h⁻¹ • e x = e (g⁻¹ • x) := fun x => by
    rw [inv_smul_eq_iff, ← he, smul_inv_smul]
  have hpre : e ⁻¹' (e.symm ⁻¹' K) = K := by
    ext x; simp
  have hpre2 : e ⁻¹' (h • e.symm ⁻¹' K) = g • K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, key]
    simp
  have h0' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ 0 := by rw [hmap, hpre]; exact h0
  have hT' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ ⊤ := by rw [hmap, hpre]; exact hT
  apply ENNReal.coe_injective
  rw [distribHaarChar_eq_div h0' hT', distribHaarChar_eq_div h0 hT, hmap, hmap, hpre, hpre2]

theorem distribHaarChar_pi_two {G A : Type} [Group G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    (g : G) : distribHaarChar (Fin 2 → A) g = distribHaarChar A g ^ 2 := by
  borelize A
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hg : (Measure.addHaar : Measure A) (g • K) = distribHaarChar A g * Measure.addHaar K := by
    rw [distribHaarChar_eq_div h0 hT, ENNReal.div_mul_cancel h0 hT]
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := Measure.pi fun _ : Fin 2 => (Measure.addHaar : Measure A)) (s := Set.univ.pi fun _ => K)
  · rw [Measure.pi_pi]; simp [h0]
  · rw [Measure.pi_pi]; simp [hT]
  · rw [Set.smul_set_univ_pi, Measure.pi_pi, Measure.pi_pi]
    simp only [Pi.smul_apply, Fin.prod_univ_two, hg]
    push_cast
    ring

theorem distribHaarChar_eq_norm (K L : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [LocallyCompactSpace K] [SecondCountableTopology K]
    [CommRing L] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [StarRing L] [ContinuousStar L] [Algebra K L]
    (e : (Fin 2 → K) ≃ₗ[K] L) (he : Continuous e) (hes : Continuous e.symm) (y : Lˣ) (k : Kˣ)
    (h : algebraMap K L k = y * star (y : L)) :
    distribHaarChar L y = distribHaarChar K k := by
  let eC : (Fin 2 → K) ≃ₜ+ L :=
    { e.toAddEquiv with continuous_toFun := he, continuous_invFun := hes }
  let kL : Lˣ := Units.map (algebraMap K L).toMonoidHom k
  have h1 : distribHaarChar L kL = distribHaarChar (Fin 2 → K) k :=
    distribHaarChar_transport eC k kL (fun x => by
      show e (k • x) = kL • e x
      simp only [Units.smul_def]
      rw [map_smul, Algebra.smul_def, smul_eq_mul]
      rfl)
  have h2 := distribHaarChar_pi_two (A := K) k
  let yS : Lˣ := Units.map (starRingEnd L).toMonoidHom y
  let sC : L ≃ₜ+ L :=
    { starAddEquiv with continuous_toFun := continuous_star, continuous_invFun := continuous_star }
  have h3 : distribHaarChar L yS = distribHaarChar L y :=
    distribHaarChar_transport sC y yS (fun x => by
      show star (y • x) = yS • star x
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, star_mul']
      rfl)
  have h4 : kL = y * yS := Units.ext (by simp [kL, yS, h, starRingEnd_apply])
  have hsq : distribHaarChar L y ^ 2 = distribHaarChar K k ^ 2 := by
    rw [← h2, ← h1, h4, map_mul, h3, sq]
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).mp hsq

end GlobalTheory.JR.ModuleNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneEtaleAlgebraMulInvariant
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.MulInv

theorem exists_nhds_one_mul_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ →
    ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
  intro F E _ _ _ _ _ A φ hφ
  obtain ⟨h1, h2⟩ := hφ
  let bil : A.K →ₗ[F] A.L →ₗ[F] A.L :=
    (LinearMap.mul F A.L).flip ∘ₗ (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
  have hbil : Continuous fun p : A.K × A.L => bil p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left bil
  have hm : Continuous fun p : A.L × A.K => p.1 * algebraMap A.K A.L p.2 := by
    have := hbil.comp continuous_swap
    simpa [bil, Function.comp_def, mul_comm] using this
  have hl : IsLocallyConstant (fun p : A.L × A.K => (φ (p.1 * algebraMap A.K A.L p.2), φ p.1)) :=
    (h1.comp_continuous hm).prodMk (h1.comp_continuous continuous_fst)
  have ho : IsOpen ((fun p : A.L × A.K => (φ (p.1 * algebraMap A.K A.L p.2), φ p.1)) ⁻¹' {q | q.1 = q.2}) := hl _
  obtain ⟨u, v, -, hv, hu, h0, huv⟩ := generalized_tube_lemma (s := tsupport φ) (t := {(1 : A.K)}) h2
    isCompact_singleton ho (by rintro ⟨x, y⟩ ⟨-, hy⟩; simp at hy; simp [hy])
  refine ⟨v, hv.mem_nhds (h0 rfl), fun s hs s' hs' hss y => ?_⟩
  have key : ∀ x ∈ tsupport φ, ∀ t ∈ v, φ (x * algebraMap A.K A.L t) = φ x := fun x hx t ht =>
    huv (Set.mk_mem_prod (hu hx) ht)
  by_cases hy : y ∈ tsupport φ
  · exact key y hy s hs
  by_cases hy' : y * algebraMap A.K A.L s ∈ tsupport φ
  · have := key _ hy' s' hs'
    rw [mul_assoc, ← map_mul, hss, map_one, mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

end GlobalTheory.JR.MulInv
end

