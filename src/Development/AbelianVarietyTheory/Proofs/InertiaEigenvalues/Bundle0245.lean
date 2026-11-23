module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActDEqOfEqOne
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.CutTrivIne

section Gen

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]


set_option synthInstance.maxHeartbeats 400000 in
theorem eq_zero_of_phi (k : ℕ) (x : KOG O k) (hx : Br.phi Bw k x = 0) : x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : Br.vecS Bw k v ∈ stdG (Br.Ow Bw) (Br.LLw Bw) k :=
    (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨u, hu⟩ := h1
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨fun j => Bw.eO.symm (u j), ?_⟩
  funext j
  apply (Br.toLLK Bw).injective
  have h2 := Br.toLLK_alg Bw (Bw.eO.symm (u j))
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.trans (congrFun hu j)

end Gen

theorem actD_eq_of_eq_one {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] {k : ℕ}
    (M : G →* Matrix (Fin k) (Fin k) LL) (L : Lattice (O := O) (matRep M)) (g : G) (hg : M g = 1)
    (x : (Fin k → LL) ⧸ L.T) : actD L g x = x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : matRep M g v = v := by
    show Matrix.toLin' (M g) v = v
    rw [hg, Matrix.toLin'_one]
    rfl
  show Submodule.Quotient.mk (matRep M g v) = _
  rw [h]

theorem chiRatO_one (D : D7) (i : D.nd.Loc) (γ : GE D.nd) : chiRatO D.nd i 1 γ = 1 := by
  simp [chiRatO, twistM]


set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ C, locFun i (chiRatO D.nd i 1) w hw f ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) → resIne i C w = ⊥ := by
  intro D i C w hw h
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, hx⟩ := h f hf
  rw [Submodule.mem_bot]
  funext γ
  obtain ⟨g, hg⟩ := (Br.ι_bijective (D.nbr i w hw)).2 ⟨γ.1, Ine_le_Dec _ γ.2⟩
  have hg' : ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) = γ.1 := congrArg Subtype.val hg
  have hmem : g ∈ Br.inert D.nbr i w hw := by
    show ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)
    rw [hg']
    exact γ.2
  have h1 : Br.loc D.nbr i w hw (chiRatO D.nd i 1) g = 1 := by
    show (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).mapMatrix
      ((D.nbr i w hw).eO.toRingHom.mapMatrix
        (chiRatO D.nd i 1 ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))) = 1
    rw [chiRatO_one, map_one, map_one]
  have h2 := hx g hmem
  rw [actD_eq_of_eq_one _ _ g h1, sub_self] at h2
  have h3 := eq_zero_of_phi (D.nbr i w hw) 1 _ h2
  rw [hg'] at h3
  exact h3

end GlobalTheory.CutTrivIne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfMuFrobeniusEquationSolvableAndTendsto
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Conv

section General

variable {A : Type*} [CommRing A]

theorem step_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A} (hc : c ∈ I) (n : ℕ)
    {y : A} (hy : y ∈ I ^ n) : c * φ y ∈ I ^ (n + 1) := by
  rw [pow_succ']
  refine Ideal.mul_mem_mul hc ?_
  have h : φ y ∈ (I ^ n).map φ := Ideal.mem_map_of_mem φ hy
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono hφ n h

theorem solve (I : Ideal A) [hI : IsAdicComplete I A] (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A}
    (hc : c ∈ I) (q : A) : ∃ y, y - c * φ y = q := by
  let f : ℕ → A := fun n => (fun z => q + c * φ z)^[n] 0
  have hf : ∀ n, f (n + 1) = q + c * φ (f n) := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n, f n - f (n + 1) ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := step_mem I φ hφ hc n ih
      rw [hf (n + 1)]
      nth_rewrite 1 [hf n]
      convert this using 1
      rw [map_sub]; ring
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right hmn (h1 n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' f (by
    intro m n hmn
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact h2 m n hmn)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hL
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine hI.toIsHausdorff.haus' _ fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have := sub_mem (step_mem I φ hφ hc n (hL n)) (hL (n + 1))
  convert this using 1
  rw [hf, map_sub]; ring

theorem geom_mem (p : ℕ) (e : A) :
    ∑ i ∈ Finset.range p, e ^ i ∈ Ideal.span {(p : A), e - 1} := by
  have h : ∑ i ∈ Finset.range p, e ^ i = (p : A) + ∑ i ∈ Finset.range p, (e ^ i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h]
  refine add_mem (Ideal.subset_span (by simp)) (Ideal.sum_mem _ fun i _ => ?_)
  obtain ⟨d, hd⟩ : e - 1 ∣ e ^ i - 1 := by simpa using sub_dvd_pow_sub_pow e 1 i
  rw [hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem map_le (p : ℕ) (φ : A →+* A) {m c : A} (h : φ m = c * m) :
    (Ideal.span {(p : A), m}).map φ ≤ Ideal.span {(p : A), m} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨x, rfl | rfl, rfl⟩
  · rw [map_natCast]; exact Ideal.subset_span (by simp)
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem iterate_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {m c : A} (hc : c ∈ I)
    (h : φ m = c * m) (k : ℕ) : ∃ d ∈ I ^ k, φ^[k] m = d * m := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, e⟩ := ih
    refine ⟨c * φ d, step_mem I φ hφ hc k hd, ?_⟩
    rw [Function.iterate_succ_apply', e, map_mul, h]; ring

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_mu : WittVector.frobenius AI.μ =
    (∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i) * AI.μ := by
  have h : WittVector.frobenius (WittVector.teichmuller l AI.ε) =
      WittVector.teichmuller l AI.ε ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [LocAinf.μ, map_sub, map_one, h, geom_sum_mul]

theorem mu_not_isUnit : ¬ IsUnit AI.μ := by
  intro h
  obtain ⟨θ, hθ⟩ := exists_isTheta l P AI
  have h0 : θ AI.μ = 0 := (hθ.2.2.2.1 _).2 ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := h.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  intro l _ P AI
  have hc : ∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i ∈
      Ideal.span {((l : ℕ) : Ainf l), AI.μ} := geom_mem l _
  have hφ := map_le l _ (frob_mu AI)
  refine ⟨fun q => ?_, fun M n => ⟨n + M, fun k hk => ?_⟩⟩
  · haveI := (GlobalTheory.Per.AinfComplete.main l AI.μ (mu_not_isUnit AI)).1
    obtain ⟨y, hy⟩ := solve _ _ hφ hc q
    refine ⟨y, ?_⟩
    rw [map_mul, frob_mu, ← hy]; ring
  · obtain ⟨d, hd, e⟩ := iterate_mem _ _ hφ hc (frob_mu AI) k
    rw [e]
    refine Ideal.mul_mem_right _ _ ?_
    have h1 : Ideal.span {((l : ℕ) : Ainf l), AI.μ} ≤ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [AI.μ_eq]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have h2 := Ideal.pow_le_pow_right hk (Ideal.pow_right_mono h1 k hd)
    rw [Ideal.span_insert] at h2
    rw [Ideal.span_insert, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.sup_pow_add_le_pow_sup_pow h2

end GlobalTheory.ExpImage.Conv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
section
noncomputable section
open GlobalTheory.BI

namespace GlobalTheory.BrauerZero

theorem step_ind_ind {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A) (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ :=
  GlobalTheory.T.inducedClassFunctionFromSubgroup_trans K A hKA ψ

theorem inducedClassFunction_mem_degreeOneCharacterDiff {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ) (hf : f ∈ D0 E) :
    ind E f ∈ D0 G :=
  _root_.GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 E f hf

theorem step_ind_one_sub_index_of_comm {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G :=
  GlobalTheory.T.induced_one_sub_index_mem_degreeOneCharacterDiff K hc

theorem step_exists_gt_commutators_le {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G)
    (hK : K ≠ ⊤) : ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K :=
  GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole K hK

theorem ind_one_sub_index_mem_degreeOneDiff_nilpotent {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] :
    ∀ (n : ℕ) (K : Subgroup G), K.index ≤ n →
      ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  intro n
  induction n with
  | zero => intro K hK; have := K.index_ne_zero_of_finite; omega
  | succ n ih =>
    intro K hK
    by_cases hKt : K = ⊤
    · subst hKt
      have e : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => 1 :=
        ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
      rw [e, Subgroup.index_top]
      simp
    · obtain ⟨A, hKA, hc⟩ := step_exists_gt_commutators_le K hKt
      have h1 : ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ)) ∈ D0 A :=
        step_ind_one_sub_index_of_comm (K.subgroupOf A) (fun a b => by
          rw [Subgroup.mem_subgroupOf]; simpa using hc a a.2 b b.2)
      have h2 := inducedClassFunction_mem_degreeOneCharacterDiff A _ h1
      have hrel := Subgroup.relIndex_mul_index hKA.le
      have hlt : 1 < K.relIndex A := by
        have h0 : (K.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have h1' : (K.subgroupOf A).index ≠ 1 := fun h =>
          hKA.not_ge (Subgroup.subgroupOf_eq_top.1 (Subgroup.index_eq_one.1 h))
        unfold Subgroup.relIndex; omega
      have hA0 : A.index ≠ 0 := A.index_ne_zero_of_finite
      have h3 := ih A (by nlinarith)
      have t := step_ind_ind K A hKA.le (fun _ => (1 : ℂ))
      have key : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) =
          ind A (ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ))) +
            ((K.subgroupOf A).index : ℤ) • (ind A (fun _ => (1 : ℂ)) - (fun _ => (A.index : ℂ))) := by
        rw [ind_sub, ← t, ← hrel]
        funext g
        have hc1 := ind_const A (((K.subgroupOf A).index : ℕ) : ℂ) g
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hc1, zsmul_eq_mul]
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.intCast_apply, Pi.natCast_apply, Int.cast_natCast]
        simp only [Subgroup.relIndex]
        push_cast
        ring
      rw [key]
      exact add_mem h2 (zsmul_mem h3 _)

theorem mem_degreeOneDiff_of_forall_centralByPrime (G : Type) [Group G] [Finite G] (f : G → ℂ)
    (hf : ∀ g x : G, f (x⁻¹ * g * x) = f g)
    (h : ∀ E : Subgroup G, (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) →
      ∀ ψ ∈ Virt ℂ ℂ E, ind E (fun e => ψ e * f e) ∈ D0 G) : f ∈ D0 G := by
  have key : ∀ φ ∈ AddSubgroup.closure {φ : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ),
      (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧
        ψ ∈ Virt ℂ ℂ E ∧ φ = ind E ψ}, φ * f ∈ D0 G := by
    intro φ hφ
    induction hφ using AddSubgroup.closure_induction with
    | mem φ hφ =>
      obtain ⟨E, ψ, hl, hψ, rfl⟩ := hφ
      rw [ind_mul_classFun_eq_ind_mul_restrict G E ψ f hf]
      exact h E hl ψ hψ
    | zero => rw [zero_mul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | neg a _ ha => rw [neg_mul]; exact neg_mem ha
  simpa using key 1 (one_mem_closure_ind_centralByPrime G)

theorem central_case (G : Type) [Group G] [Finite G]
    (hG : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G)
    (IH : ∀ T : Subgroup G, T ≠ ⊤ → ∀ f ∈ Virt ℂ ℂ T, f 1 = 0 → f ∈ D0 T) :
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  classical
  obtain ⟨l, hl, hc⟩ := hG
  have : Fact l.Prime := ⟨hl⟩
  have hq : IsPGroup l (G ⧸ Subgroup.center G) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨j, hj⟩ := hc y
    exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩
  have := hq.isNilpotent
  haveI : Group.IsNilpotent G :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center G)) (by simp)
  have hab : AbByP G := ⟨l, hl, Subgroup.center G, inferInstance,
    fun a _ b hb => Subgroup.mem_center_iff.1 hb a, fun g => hc g⟩
  have C : ∀ χ : G → ℂ, IsChar ℂ ℂ χ → χ - (fun _ => χ 1) ∈ D0 G := by
    refine isChar_induction ℂ ℂ G (fun χ => χ - (fun _ => χ 1) ∈ D0 G) ?_ ?_
    · have e : (0 : G → ℂ) - (fun _ => (0 : G → ℂ) 1) = 0 := by funext g; simp
      rw [e]; exact zero_mem _
    · intro φ c hφ _ hQ
      have e : (φ + c) - (fun _ => (φ + c) 1) = (φ - fun _ => φ 1) + (c - fun _ => c 1) := by
        funext g; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [e]
      refine add_mem ?_ hQ
      rcases irrChar_linear_or_induced ℂ G φ hab hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have hφc : IsChar ℂ ℂ φ := by obtain ⟨n, ρ, -, h⟩ := hφ; exact ⟨n, ρ, h⟩
        have hcl := (isChar_restrict_conj_one ℂ ℂ G φ hφc).2.1
        refine AddSubgroup.subset_closure ⟨⊤, lam.comp (⊤ : Subgroup G).subtype, ?_⟩
        have e1 : (fun h : (⊤ : Subgroup G) => ((lam.comp (⊤ : Subgroup G).subtype h : ℂˣ) : ℂ)) =
            fun h : (⊤ : Subgroup G) => φ (h : G) := by
          funext h; simp [hlam]
        rw [e1, ind_top φ hcl, ind_top (fun _ : G => (1 : ℂ)) (fun _ _ => rfl)]
        funext g; simp [hlam]
      · obtain ⟨n, hn, -⟩ := (isChar_restrict_conj_one ℂ ℂ T ψ hψ).2.2
        have hψV : ψ - (fun _ => ψ 1) ∈ Virt ℂ ℂ T := by
          refine sub_mem (isChar_mem_virt_complex hψ) ?_
          have e2 : (fun _ : T => ψ 1) = n • (fun _ : T => (1 : ℂ)) := by funext; simp [hn]
          rw [e2]; exact nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ T)) n
        have h1 := inducedClassFunction_mem_degreeOneCharacterDiff T _ (IH T hT _ hψV (by simp))
        have h2 := ind_one_sub_index_mem_degreeOneDiff_nilpotent T.index T le_rfl
        have key : ind T ψ - (fun _ => ind T ψ 1) = ind T (ψ - fun _ => ψ 1) +
            (n : ℤ) • (ind T (fun _ => (1 : ℂ)) - fun _ => (T.index : ℂ)) := by
          rw [ind_sub]; funext g
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, ind_apply_one, hn, ind_const T (n : ℂ) g,
            zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Pi.natCast_apply]
          push_cast; ring
        rw [key]; exact add_mem h1 (zsmul_mem h2 _)
  intro f hf hf1
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G f).1 hf
  have hab1 : a 1 = b 1 := by simpa [sub_eq_zero] using hf1
  have e : a - b = (a - fun _ => a 1) - (b - fun _ => b 1) := by funext g; simp [hab1]
  rw [e]; exact sub_mem (C a ha) (C b hb)

theorem virtualCharacter_degreeZero_mem_degreeOneDiff : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  intro n
  induction n with
  | zero => intro G _ _ hG; have := Nat.card_pos (α := G); omega
  | succ n ih =>
    intro G _ _ hG f hf hf1
    have hcl : ∀ g x : G, f (x⁻¹ * g * x) = f g := (virt_mul_comap_conj_ind_linear G).2.2.1 f hf
    refine mem_degreeOneDiff_of_forall_centralByPrime G f hcl ?_
    intro E hE ψ hψ
    have hV : (fun e : E => ψ e * f e) ∈ Virt ℂ ℂ E :=
      (virt_mul_comap_conj_ind_linear E).1 ψ hψ _
        ((virt_mul_comap_conj_ind_linear G).2.1 f hf E E.subtype)
    have h1 : (fun e : E => ψ e * f e) 1 = 0 := by simp [hf1]
    by_cases hlt : Nat.card E < Nat.card G
    · exact inducedClassFunction_mem_degreeOneCharacterDiff E _ (ih E (by omega) _ hV h1)
    · have htop : E = ⊤ := (Subgroup.card_eq_iff_eq_top E).1
        (le_antisymm (Subgroup.card_le_card_group E) (not_lt.1 hlt))
      have hVG : ind E (fun e => ψ e * f e) ∈ Virt ℂ ℂ G :=
        (virt_mul_comap_conj_ind_linear G).2.2.2.1 E _ hV
      have hG1 : ind E (fun e => ψ e * f e) 1 = 0 := by rw [ind_apply_one]; simp [hf1]
      subst htop
      obtain ⟨l, hl, hc⟩ := hE
      have hG' : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G := by
        refine ⟨l, hl, fun y => ?_⟩
        obtain ⟨j, hj⟩ := hc ⟨y, Subgroup.mem_top y⟩
        refine ⟨j, Subgroup.mem_center_iff.2 fun z => ?_⟩
        have := Subgroup.mem_center_iff.1 hj ⟨z, Subgroup.mem_top z⟩
        simpa using congrArg Subtype.val this
      refine central_case G hG' (fun T hT g hg hg1 => ih T ?_ g hg hg1) _ hVG hG1
      have := Subgroup.card_le_card_group T
      have hne : Nat.card T ≠ Nat.card G := fun h => hT ((Subgroup.card_eq_iff_eq_top T).1 h)
      omega

theorem exists_sum_induced_characters_of_mem_degreeOneDiff {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : f ∈ D0 G) :
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (χ : ∀ i, H i →* ℂˣ) (c : Fin r → ℤ), ∀ g : G,
      f g = ∑ i, (c i : ℂ) * (GlobalTheory.Published.indFun (H i) (fun x => (χ i x : ℂ)) g -
        GlobalTheory.Published.indFun (H i) (fun _ => 1) g) := by
  rw [D0, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_set'] at hf
  obtain ⟨n, c, s, hs⟩ := hf
  choose H χ hHχ using fun i => (s i).2
  refine ⟨n, H, χ, c, fun g => ?_⟩
  rw [← hs, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, hHχ i, zsmul_eq_mul, indFun_eq_ind, indFun_eq_ind]
  rfl

theorem brauerDegreeZero : GlobalTheory.Published.BrauerDegreeZero := by
  intro G _ _ V _ _ _ ρ
  classical
  have hchar := (isChar_and_isIrrChar_of_rep ℂ ℂ G V ρ).1
  have hV : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) ∈ Virt ℂ ℂ G := by
    have e : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) =
        (fun g => algebraMap ℂ ℂ (ρ.character g)) - (Module.finrank ℂ V) • (fun _ => (1 : ℂ)) := by
      funext g; simp [Representation.character]
    rw [e]
    exact sub_mem (isChar_mem_virt_complex hchar)
      (nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ G)) _)
  have h1 : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) 1 = 0 := by simp
  exact exists_sum_induced_characters_of_mem_degreeOneDiff (virtualCharacter_degreeZero_mem_degreeOneDiff _ G le_rfl _ hV h1)

end GlobalTheory.BrauerZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulIdemFromCenter
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem exists_central_lift {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra B Γ)
    (hx : ∀ z, x * z = z * x) (hr : ∀ h, x.coeff h ∈ f.range) :
    ∃ z ∈ Subalgebra.center A (MonoidAlgebra A Γ), ∀ h : Γ, f (z.coeff h) = x.coeff h := by
  choose c hc using hr
  let z : MonoidAlgebra A Γ := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have hz : ∀ h, f (z.coeff h) = x.coeff h := fun h => hc h
  have hco : ∀ (y : MonoidAlgebra A Γ) h, (MonoidAlgebra.mapRingHom Γ f y).coeff h = f (y.coeff h) := by
    intro y h; simp
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom Γ f) := by
    intro a b hab
    ext h
    apply hf
    rw [← hco, ← hco, hab]
  have hzx : MonoidAlgebra.mapRingHom Γ f z = x := by
    ext h
    rw [hco, hz]
  refine ⟨z, ?_, hz⟩
  rw [Subalgebra.mem_center_iff]
  intro b
  apply hinj
  rw [map_mul, map_mul, hzx, hx]

theorem card_mul_idem_from_center : ∀ (D : D7) (i : D.nd.Loc) (Γ : Type) [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ), e * e = e → (∀ z, e * z = z * e) → (∃ ζ : D.nd.O i, IsPrimitiveRoot (iotaO D.nd D.naut i ζ) (Nat.card Γ)) → ∃ z ∈ Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) Γ), ∀ h : Γ, iotaO D.nd D.naut i (MonoidAlgebra.coeff z h) = (Nat.card Γ : ℂ) * e.coeff h := by
  intro D i Γ _ _ e he hc ⟨ζ, hζ⟩
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  have hco : ∀ h, ((Nat.card Γ : ℂ) • e).coeff h = (Nat.card Γ : ℂ) * e.coeff h := by
    intro h; simp
  obtain ⟨z, hz, hz'⟩ := exists_central_lift (iotaO D.nd D.naut i) hinj ((Nat.card Γ : ℂ) • e)
    (fun z => by rw [smul_mul_assoc, mul_smul_comm, hc]) (fun h => by
      rw [hco]
      have h1 := centralIdemCoeff Γ e he hc _ hζ h
      have h2 : Algebra.adjoin ℤ ({iotaO D.nd D.naut i ζ} : Set ℂ) ≤
          subalgebraOfSubring (iotaO D.nd D.naut i).range :=
        Algebra.adjoin_le (by rintro _ rfl; exact ⟨ζ, rfl⟩)
      exact h2 h1)
  exact ⟨z, hz, fun h => by rw [hz', hco]⟩

end GlobalTheory.CentralIdem
end

