module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOverDirectedUnionEssEtaleLocal
section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleOverDirectedUnion

theorem localRing_of_etale_over_essEtale : ∀ (R S' E : Type) [CommRing R] [CommRing S'] [CommRing E] [Algebra R S'] [Algebra S' E] [Algebra R E] [IsScalarTower R S' E] [Algebra.Etale S' E], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] S')) → ∀ (P : Ideal E) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S' E _ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨ψ⟩⟩ P hP
  letI : Algebra (Localization.AtPrime q) S' := ψ.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime q) E := ((algebraMap S' E).comp ψ.toRingHom).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime q) S' E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale (Localization.AtPrime q) S' :=
    Algebra.Etale.of_equiv (R := Localization.AtPrime q)
      ({ ψ.toRingEquiv with commutes' := fun _ => rfl } : Localization.AtPrime q ≃ₐ[Localization.AtPrime q] S')
  haveI : Algebra.Etale (Localization.AtPrime q) E := Algebra.Etale.comp (Localization.AtPrime q) S' E
  haveI : IsScalarTower R (Localization.AtPrime q) E := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R E r = algebraMap S' E (ψ (algebraMap R _ r))
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply])
  exact _root_.GlobalTheory.essEtale_atPrime_of_etale_over_atPrime R A E q P

theorem span_one_tmul_eq_top (S B : Type) [CommRing S] [CommRing B] [Algebra S B] (A₀ B₀ : Type)
    [CommRing A₀] [CommRing B₀] [Algebra A₀ S] [Algebra A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) :
    Submodule.span S (Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [← e.symm_apply_apply y]
  induction e y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul s b =>
    have : s ⊗ₜ[A₀] b = s • ((1 : S) ⊗ₜ[A₀] b) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  | add x z hx hz => rw [map_add]; exact add_mem hx hz

theorem fg_le_member {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (A₀ : Subalgebra R S) (h : A₀.FG) :
    ∃ i, A₀ ≤ Si i := by
  classical
  obtain ⟨t, rfl⟩ := h
  choose f hf using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (t.image f)
  exact ⟨M, Algebra.adjoin_le fun s hs => hmono (hM _ (Finset.mem_image_of_mem f hs)) (hf s)⟩

theorem construct : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] [Algebra.Etale S B], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (C : ι → Subalgebra R B), Monotone C ∧ (∀ b : B, ∃ i, b ∈ C i) ∧ ∀ i (P : Ideal (C i)) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S B _ _ _ _ _ _ _ _ ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩
  obtain ⟨A₀, B₀, _, _, hfg, hét, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg R S B
  obtain ⟨i₀, hi₀⟩ := fg_le_member Si hmono hcov A₀ hfg
  let g : B₀ → B := fun b => e.symm (1 ⊗ₜ b)
  let C : {j // i₀ ≤ j} → Subalgebra R B := fun j =>
    Algebra.adjoin R ((algebraMap S B) '' (Si j.1 : Set S) ∪ Set.range g)
  have hdir : IsDirected {j // i₀ ≤ j} (· ≤ ·) := ⟨fun a b => by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩
  have hCmono : Monotone C := fun a b hab =>
    Algebra.adjoin_mono (Set.union_subset_union_left _ (Set.image_mono (hmono hab)))
  refine ⟨{j // i₀ ≤ j}, inferInstance, hdir, ⟨⟨i₀, le_rfl⟩⟩, C, hCmono, ?_, ?_⟩
  · intro b
    have hb : b ∈ Submodule.span S (Set.range g) := by
      rw [span_one_tmul_eq_top S B A₀ B₀ e]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx => exact ⟨⟨i₀, le_rfl⟩, Algebra.subset_adjoin (Or.inr hx)⟩
    | zero => exact ⟨⟨i₀, le_rfl⟩, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a b
      exact ⟨k, add_mem (hCmono hak ha) (hCmono hbk hb)⟩
    | smul s x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨j, hj⟩ := hcov s
      obtain ⟨k, hak, hjk⟩ := directed_of (· ≤ ·) a.1 j
      refine ⟨⟨k, a.2.trans hak⟩, ?_⟩
      rw [Algebra.smul_def]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, hmono hjk hj, rfl⟩)) (hCmono hak ha)
  · intro j P hP
    obtain ⟨_, _, _⟩ := GlobalTheory.T.etale_adjoin_baseChange_image' R S B A₀ B₀ e (Si j.1) (hi₀.trans (hmono j.2))
    exact localRing_of_etale_over_essEtale R (Si j.1) (C j) (hloc j.1) P hP

end GlobalTheory.EtaleOverDirectedUnion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalQuotientRingVectorAtPointsInjective
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge

open Polynomial

theorem prod_X_sub_C_dvd_of_eval_zero {O S : Type} [CommRing O] [IsDomain O] [Fintype S]
    (b : S → O) (hb : Function.Injective b) (g : O[X]) (hg : ∀ s, g.eval (b s) = 0) :
    (∏ s, (X - C (b s))) ∣ g := by
  by_cases h0 : g = 0
  · simp [h0]
  have hprod : (∏ s, (X - C (b s))) = ((Finset.univ.val.map b).map (fun t => X - C t)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots h0]
  rw [Multiset.le_iff_subset (Multiset.Nodup.map hb Finset.univ.nodup)]
  intro t ht
  obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 ht
  exact (mem_roots h0).2 (hg s)

theorem evalVec_injective_of_injective (C : Type) [Field C] (w : Valuation C ℝ≥0)
    (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring)
    (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) :
    Function.Injective a → Function.Injective (evalVec (liftA hv a) N) := by
  intro ha
  have hinj : Function.Injective (liftA hv a) := by
    intro s t hst
    apply ha
    apply Subtype.ext
    have := congrArg (fun u : Int0 v => (u : C)) hst
    exact this
  have key : ∀ x : Fin N → RS (liftA hv a), evalVec (liftA hv a) N x = 0 → x = 0 := by
    intro x hx
    funext i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    rw [Pi.zero_apply, ← hg, AdjoinRoot.mk_eq_zero]
    apply prod_X_sub_C_dvd_of_eval_zero _ hinj
    intro s
    have h1 := congrFun (congrFun hx s) i
    simp only [evalVec, Pi.zero_apply, ← hg] at h1
    apply Subtype.ext
    rw [show ((0 : Int0 v) : C) = 0 from rfl, ← h1]
    congr 1
  intro x y hxy
  have := key (x - y) (by rw [evalVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this

end GlobalTheory.HerbrandBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedUnitMultipleTotallyReal
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.BalancedUnits

open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem

theorem sum_mult_log_sub {K : Type} [Field K] [NumberField K] (x : mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) = 0 := by
  have h1 : ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (normAtPlace w x) =
      Real.log (mixedEmbedding.norm x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Real.log_pow]
    · intro w _
      exact pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  have h2 : ∑ w : InfinitePlace K, (mult w : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast sum_mult_eq
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp_rw [mul_sub, Finset.sum_sub_distrib, h1, ← Finset.sum_mul, h2]
  field_simp
  ring

theorem exists_unit_log_bound (K : Type) [Field K] [NumberField K] : ∃ M : ℝ, 0 ≤ M ∧
    ∀ b : K, b ≠ 0 → ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log (w (((ε : 𝓞 K) : K) * b)) -
        Real.log (mixedEmbedding.norm (mixedEmbedding K (((ε : 𝓞 K) : K) * b))) *
          (Module.finrank ℚ K : ℝ)⁻¹| ≤ M := by
  classical
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded
    ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))).subset_closedBall 0
  refine ⟨(Fintype.card (InfinitePlace K) : ℝ) * |R|, by positivity, ?_⟩
  intro b hb
  have hx : mixedEmbedding.norm (mixedEmbedding K b) ≠ 0 := by
    rw [norm_eq_norm]; simpa using hb
  obtain ⟨ε, hε⟩ := fundamentalCone.exists_unit_smul_mem hx
  refine ⟨ε, ?_⟩
  have hxy : ε • mixedEmbedding K b = mixedEmbedding K (((ε : 𝓞 K) : K) * b) := by
    rw [unitSMul_smul, map_mul]
  rw [hxy] at hε
  set y : K := ((ε : 𝓞 K) : K) * b with hy_def
  set X := mixedEmbedding K y
  set L := Real.log (mixedEmbedding.norm X) * (Module.finrank ℚ K : ℝ)⁻¹
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hlog : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(mult w.val : ℝ) * (Real.log (normAtPlace w.val X) - L)| ≤ |R| := by
    intro w
    have h0 := hR hε.1
    rw [mem_closedBall_zero_iff] at h0
    have h2 := (norm_le_pi_norm (logMap X) w).trans h0
    rw [logMap_apply, Real.norm_eq_abs] at h2
    exact h2.trans (le_abs_self R)
  have hmul : ∀ w : InfinitePlace K,
      |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)| ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have hs := sum_mult_log_sub X hε.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      rw [eq_neg_of_add_eq_zero_left hs, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ w ∈ Finset.univ.erase w₀, |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)|
          ≤ ∑ _w ∈ Finset.univ.erase w₀, |R| := Finset.sum_le_sum fun w hw =>
            hlog ⟨w, Finset.ne_of_mem_erase hw⟩
        _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
            rw [Finset.sum_const, nsmul_eq_mul]
            gcongr
            exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (hlog ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg R) hcard)
  intro w
  have h := hmul w
  rw [abs_mul, normAtPlace_apply] at h
  refine le_trans ?_ h
  rw [abs_of_pos (by exact_mod_cast mult_pos : (0:ℝ) < mult w)]
  exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult

theorem balanced_unit_multiple (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ b : F, b ≠ 0 → ∃ ε : (𝓞 F)ˣ, ∀ τ τ' : Emb F,
      |τ (((ε : 𝓞 F) : F) * b)| ≤ C * |τ' (((ε : 𝓞 F) : F) * b)| := by
  obtain ⟨M, hM0, hM⟩ := exists_unit_log_bound F
  refine ⟨Real.exp (2 * M), Real.one_le_exp (by positivity), ?_⟩
  intro b hb
  obtain ⟨ε, hε⟩ := hM b hb
  refine ⟨ε, ?_⟩
  set y : F := ((ε : 𝓞 F) : F) * b with hy_def
  have hy : y ≠ 0 := mul_ne_zero (by simp) hb
  have hw : ∀ τ : Emb F, InfinitePlace.mk (Complex.ofRealHom.comp τ) y = |τ y| := by
    intro τ
    rw [InfinitePlace.apply]
    simp
  have hpos : ∀ τ : Emb F, 0 < |τ y| := fun τ => abs_pos.mpr ((map_ne_zero τ).mpr hy)
  intro τ τ'
  have h1 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ))
  have h2 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ'))
  rw [hw] at h1 h2
  have key : Real.log |τ y| ≤ 2 * M + Real.log |τ' y| := by
    have := (abs_le.mp h1).2
    have := (abs_le.mp h2).1
    linarith
  calc |τ y| = Real.exp (Real.log |τ y|) := (Real.exp_log (hpos τ)).symm
    _ ≤ Real.exp (2 * M + Real.log |τ' y|) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * M) * |τ' y| := by rw [Real.exp_add, Real.exp_log (hpos τ')]

end GlobalTheory.BalancedUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverIdealRepresents
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

noncomputable section

namespace GlobalTheory.PtClosed

theorem represents_away (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
    (V : S.Opens) (hV : IsAffineOpen V) (a : Γ(S, V)) (J : Ideal Γ(S, S.basicOpen a))
    (hJ : Represents (ptQ P (S.basicOpen a) (hV.basicOpen a)) J) :
    ∃ J' : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J' := by
  let ρ := (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom
  letI : Algebra Γ(S, V) Γ(S, S.basicOpen a) := ρ.toAlgebra
  haveI : IsLocalization.Away a Γ(S, S.basicOpen a) := hV.isLocalization_basicOpen a
  let e : Localization.Away a ≃ₐ[Γ(S, V)] Γ(S, S.basicOpen a) :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Γ(S, S.basicOpen a)
  refine ⟨J.map (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a), ?_⟩
  intro R' _ h
  have hc : h.comp (algebraMap Γ(S, V) (Localization.Away a)) =
      (h.comp (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a)).comp ρ := by
    ext x
    simp only [RingHom.comp_apply]
    congr 1
    have := e.symm.commutes x
    rw [← this]
    rfl
  have hs : ∀ g : Γ(S, S.basicOpen a) →+* R',
      spMap (g.comp ρ) ≫ hV.fromSpec = spMap g ≫ (hV.basicOpen a).fromSpec := by
    intro g
    rw [← hV.map_fromSpec (hV.basicOpen a) (homOfLE (S.basicOpen_le a)).op]
    simp only [ρ, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap _ ≫ hV.fromSpec) ↔ _
  rw [hc, hs, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem affine_local_represents : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∀ (V : S.Opens) (hV : IsAffineOpen V), ∃ s : Finset Γ(S, V), Ideal.span (s : Set Γ(S, V)) = ⊤ ∧
    ∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J := by
  intro S P hcov V hV
  let T : Set Γ(S, V) := {a | ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J}
  have hT : Ideal.span T = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro z hzV
    obtain ⟨U, hU, hzU, K, hK⟩ := hcov z
    obtain ⟨a, b, hab, hz⟩ := exists_basicOpen_le_affine_inter hV hU z ⟨hzV, hzU⟩
    have hle : S.basicOpen a ≤ U := hab ▸ S.basicOpen_le b
    have hJ := represents_restrict S P U (S.basicOpen a) hU (hV.basicOpen a) hle K hK
    have haT : a ∈ T := represents_away S P V hV a _ hJ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, haT⟩, hz⟩
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).1 hT
  exact ⟨s, hs, fun a ha ↦ hsT ha⟩

end GlobalTheory.PtClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleZ

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padic_ccast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃A[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨ContinuousAlgEquiv.refl ℚ _, fun _ => Iff.rfl⟩

theorem exists_clocal (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_ccast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).trans c).trans
    (adicCompletion.padicEquiv w).symm, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

variable (e : ∀ w : HeightOneSpectrum ℤ, (primeCorr w).adicCompletion ℚ ≃A[ℚ] w.adicCompletion ℚ)
  (he : ∀ w x, e w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ)

theorem tendsto_primeCorr : Filter.Tendsto primeCorr Filter.cofinite Filter.cofinite :=
  primeCorr.injective.tendsto_cofinite

include he in
theorem maps_int : ∀ᶠ w in Filter.cofinite, Set.MapsTo
    (fun x => ((e w).toRingHom : (primeCorr w).adicCompletion ℚ →+* w.adicCompletion ℚ) x)
      ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) :=
  .of_forall fun w x hx => (he w x).2 hx

def adeleMap : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
      (fun w : HeightOneSpectrum ℤ => w.adicCompletion ℚ)
      (B₁ := fun v => v.adicCompletionIntegers ℚ) (B₂ := fun w => w.adicCompletionIntegers ℚ)
      primeCorr tendsto_primeCorr (fun w => (e w).toRingHom) (maps_int e he)

theorem continuous_adeleMap : Continuous (adeleMap e he) :=
  RestrictedProduct.mapAlong_continuous _ _ primeCorr tendsto_primeCorr _ (maps_int e he)
    fun w => (e w).continuous

def adeleAlgHom : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] FiniteAdeleRing ℤ ℚ where
  toFun a := ⟨fun w => e w (a (primeCorr w)), by
    have h1 := primeCorr.injective.tendsto_cofinite.eventually a.2
    exact h1.mono fun w hw => (he w _).2 hw⟩
  map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
  map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
  map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
  map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
  commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r

theorem adeleAlgHom_apply (a : FiniteAdeleRing (𝓞 ℚ) ℚ) (w : HeightOneSpectrum ℤ) :
    adeleAlgHom e he a w = e w (a (primeCorr w)) := rfl

theorem adeleAlgHom_eq : ⇑(adeleAlgHom e he) = ⇑(adeleMap e he) := by
  funext a
  exact FiniteAdeleRing.ext _ fun w => rfl

theorem adeleAlgHom_injective : Function.Injective (adeleAlgHom e he) := by
  intro a b hab
  refine FiniteAdeleRing.ext _ fun v => ?_
  obtain ⟨w, rfl⟩ := primeCorr.surjective v
  have h := congrArg (fun x : FiniteAdeleRing ℤ ℚ => x w) hab
  simp only [adeleAlgHom_apply] at h
  exact (e w).injective h

theorem adeleAlgHom_surjective : Function.Surjective (adeleAlgHom e he) := by
  intro b
  obtain ⟨f, hf⟩ : ∃ f : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletion ℚ,
      ∀ w, f (primeCorr w) = (e w).symm (b w) :=
    ⟨_, fun w => Equiv.piCongrLeft_apply_apply
      (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ) primeCorr
      (fun w => (e w).symm (b w)) w⟩
  have hfi : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ := by
    have h1 := primeCorr.symm.injective.tendsto_cofinite.eventually b.2
    refine h1.mono fun v hv => ?_
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    rw [Equiv.symm_apply_apply] at hv
    rw [hf, ← he, ContinuousAlgEquiv.apply_symm_apply]
    exact hv
  obtain ⟨a, ha⟩ : ∃ a : FiniteAdeleRing (𝓞 ℚ) ℚ, ∀ v, a v = f v := ⟨⟨f, hfi⟩, fun _ => rfl⟩
  refine ⟨a, FiniteAdeleRing.ext _ fun w => ?_⟩
  rw [adeleAlgHom_apply, ha, hf, ContinuousAlgEquiv.apply_symm_apply]


omit e he in
theorem exists_continuous_adele_equiv :
    ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  choose e he using exists_clocal
  refine ⟨AlgEquiv.ofBijective (adeleAlgHom e he)
    ⟨adeleAlgHom_injective e he, adeleAlgHom_surjective e he⟩, ?_⟩
  change Continuous (adeleAlgHom e he)
  rw [adeleAlgHom_eq]
  exact continuous_adeleMap e he

end GlobalTheory.AdeleZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdMulPowEtaleNbhdZeroLocusStatement
section
open GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal → algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  first | (exact @GlobalTheory.LocDivEtale.exists_dvd_mul_pow) | (exact GlobalTheory.LocDivEtale.exists_dvd_mul_pow) | (intros; apply GlobalTheory.LocDivEtale.exists_dvd_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvaluationExtensionClosureRepresentativesStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evaluation_extension_closure_representatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (A : K →L[ℂ] K) (E : Submodule ℂ K), (∀ v ∈ E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A v) =ᵐ[μ] φ) → (∀ B, IsCompact B → ∃ C : ℝ, ∀ v ∈ E, ∀ φ : G → ℂ, Continuous φ → ι (A v) =ᵐ[μ] φ → ∀ x ∈ B, ‖φ x‖ ≤ C * ‖v‖) → ∃ Λ : G → (K →L[ℂ] ℂ), ∀ v ∈ closure (E : Set K), (Continuous fun x => Λ x v) ∧ ι (A v) =ᵐ[μ] fun x => Λ x v := by
  first | exact @GlobalTheory.LocRep.exists_eval_closure | exact GlobalTheory.LocRep.exists_eval_closure | (intros; apply GlobalTheory.LocRep.exists_eval_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExcisionNbhdAdjoinRootStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit : ∀ (A : Type) [CommRing A] (h : A) (q : ℕ), IsUnit (q : A) → ∀ ε r : A, IsUnit ε → ε - r ^ q ∈ Ideal.span {h} → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), IsExcisionNbhd A A' h ∧ ∃ x : A', algebraMap A A' ε = x ^ q := by
  first | (exact @GlobalTheory.EtC.exists_excisionNbhd_adjoin_root) | (exact GlobalTheory.EtC.exists_excisionNbhd_adjoin_root) | (intros; apply GlobalTheory.EtC.exists_excisionNbhd_adjoin_root  <;> assumption)
end

