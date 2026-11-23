module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDependentColumn
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Coeff

variable {A : Type} [CommRing A]

theorem mul_eq_zero_of_mem {f : A} (hf : f * f = f) {x : A}
    (hx : x ∈ Ideal.span ({1 - f} : Set A)) : f * x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  linear_combination (-y) * hf

theorem mem_of_mul_eq_zero {f x : A} (hx : f * x = 0) :
    x ∈ Ideal.span ({1 - f} : Set A) :=
  Ideal.mem_span_singleton'.2 ⟨x, by linear_combination (-1 : A) * hx⟩

theorem isMaximal_span {f : A} (hf : IsFieldIdem f) :
    (Ideal.span ({1 - f} : Set A)).IsMaximal := by
  refine Ideal.isMaximal_iff.2 ⟨fun h => hf.ne ?_, fun J x hJ hx hxJ => ?_⟩
  · simpa using mul_eq_zero_of_mem hf.idem h
  · have hne : f * x ≠ 0 := fun h => hx (mem_of_mul_eq_zero h)
    obtain ⟨y, hy⟩ := hf.inv x hne
    have h1 : (1 - f) ∈ J := hJ (Ideal.subset_span rfl)
    have h2 : x * (f * y) ∈ J := J.mul_mem_right _ hxJ
    have : (1 : A) = (1 - f) + x * (f * y) := by linear_combination (-1 : A) * hy
    rw [this]
    exact J.add_mem h1 h2

theorem alt_of_field {K : Type} [Field K] (π : A →+* K) (hs : Function.Surjective π) {f : A}
    (hf : f * f = f) (h1 : π f = 1) (h0 : ∀ x, π x = 0 → f * x = 0) {a t : ℕ} (v : Fx A a t) :
    (∃ M : Fx A t a, f • (M * v) = f • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f * c k = c k) ∧
        ∀ p, f * v p i = ∑ k, c k * v p k := by
  classical
  set w : Matrix (Fin a) (Fin t) K := v.map π with hw
  by_cases hli : LinearIndependent K w.col
  · left
    have hinj : Function.Injective w.mulVecLin := Matrix.mulVec_injective_iff.2 hli
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective w.mulVecLin
      (LinearMap.ker_eq_bot.2 hinj)
    set N : Matrix (Fin t) (Fin a) K := LinearMap.toMatrix' g with hN
    have hNw : N * w = 1 := by
      have : LinearMap.toMatrix' (g ∘ₗ w.mulVecLin) = N * w := by
        rw [LinearMap.toMatrix'_comp, hN]
        congr 1
        rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
      rw [← this, hg, LinearMap.toMatrix'_id]
    choose l hl using hs
    refine ⟨Matrix.of fun p q => l (N p q), ?_⟩
    have hmap : ((Matrix.of fun p q => l (N p q) : Fx A t a) * v).map π = 1 := by
      rw [Matrix.map_mul, ← hNw]
      congr 1
      ext p q
      simp [hl]
    ext p q
    have hpq := congrFun (congrFun hmap p) q
    have hz : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q - (1 : Fx A t t) p q) = 0 := by
      rw [map_sub, sub_eq_zero]
      have hpq' : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q) = (1 : Matrix (Fin t) (Fin t) K) p q := hpq
      rw [hpq']
      by_cases h : p = q
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
    have := h0 _ hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination this
  · right
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
    set b : Fin t → K := fun k => if k = i then 0 else -(g k / g i) with hb
    choose l hl using hs
    refine ⟨i, fun k => f * l (b k), ?_, fun k => ?_, fun p => ?_⟩
    · have : π (l (b i)) = 0 := by simp [hl, hb]
      exact h0 _ this
    · rw [← mul_assoc, hf]
    · have hrow : ∑ k, g k * w p k = 0 := by
        have := congrFun hg p
        simpa [Matrix.col_apply, Finset.sum_apply] using this
      have hz : π (v p i - ∑ k, l (b k) * v p k) = 0 := by
        have hw' : ∀ k, π (v p k) = w p k := fun k => rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum]
        simp only [map_mul, hl, hw']
        have hsum : ∑ k, b k * w p k = w p i := by
          have hsplit : ∀ k, b k * w p k = -(g i)⁻¹ * (g k * w p k) +
              (if k = i then w p i else 0) := by
            intro k
            by_cases h : k = i
            · subst h
              simp only [hb, if_true]
              field_simp
              ring
            · simp only [hb, if_neg h]
              field_simp
              ring
          rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
            ← Finset.mul_sum, hrow]
          simp
        rw [hsum, sub_self]
      have := h0 _ hz
      rw [mul_sub, Finset.mul_sum, sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_dependent_column {A : Type} [CommRing A] {ι : Type} [Fintype ι] (e : A) (f : ι → A)
    (hd : IsFieldDec e f) {a t : ℕ} (v : Fx A a t)
    (hv : ¬ ∃ M : Fx A t a, M * v = e • (1 : Fx A t t)) :
    ∃ (j : ι) (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
      ∀ p, f j * v p i = ∑ k, c k * v p k := by
  classical
  have key : ∀ j, (∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
        ∀ p, f j * v p i = ∑ k, c k * v p k := by
    intro j
    have hj := hd.field j
    haveI := isMaximal_span hj
    letI : Field (A ⧸ Ideal.span ({1 - f j} : Set A)) := Ideal.Quotient.field _
    refine alt_of_field (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))
      Ideal.Quotient.mk_surjective hj.idem ?_ ?_ v
    · rw [← map_one (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))]
      refine Ideal.Quotient.eq.2 ?_
      have : f j - 1 = (-1 : A) * (1 - f j) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · intro x hx
      exact mul_eq_zero_of_mem hj.idem (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  by_contra hno
  have hall : ∀ j, ∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t) := fun j =>
    (key j).resolve_right fun ⟨i, c, h⟩ => hno ⟨j, i, c, h⟩
  choose M hM using hall
  refine hv ⟨∑ j, f j • M j, ?_⟩
  rw [Matrix.sum_mul, ← hd.sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_mul, hM j]

end GlobalTheory.CompanionTheory.NullFr.Coeff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
section
open GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.JacExact

section Finite

variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def avg (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] : V →ₗ[ℂ] V :=
  ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q)

theorem avg_apply (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] (x : V) :
    avg τ χ M x = ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) x := by
  simp [avg, LinearMap.sum_apply]

theorem avg_translate (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [M.Normal]
    [Fintype (L ⧸ M)] (hχ : M ≤ χ.ker) (x : V) (hx : ∀ m ∈ M, τ m x = x) (n : L) :
    avg τ χ M (τ n x) = ((χ n : ℂˣ) : ℂ) • avg τ χ M x := by
  set F : L → V := fun t => (((χ t)⁻¹ : ℂˣ) : ℂ) • τ t x with hFdef
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ M) = QuotientGroup.mk b → F a = F b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ M := QuotientGroup.eq.1 hab
    have hb : b = a * (a⁻¹ * b) := by group
    have hc : χ (a⁻¹ * b) = 1 := hχ hm
    have ht : τ b x = τ a x := by
      rw [hb, map_mul, Module.End.mul_apply, hx _ hm]
    have hcb : χ b = χ a := by
      rw [hb, map_mul, hc, mul_one]
    simp only [hFdef, ht, hcb]
  have h1 : ∀ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) (τ n x)
      = ((χ n : ℂˣ) : ℂ) • F (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
    intro q
    have hq : (QuotientGroup.mk (Quotient.out q * n) : L ⧸ M)
        = QuotientGroup.mk (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [← hF _ _ hq]
    simp only [hFdef, map_mul, mul_inv, Units.val_mul, smul_smul, Module.End.mul_apply]
    congr 1
    have : ((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)
        = (((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ)) * (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [avg_apply, avg_apply, Finset.sum_congr rfl (fun q _ => h1 q), ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk n : L ⧸ M))
    (fun q => F (Quotient.out q))

theorem mem_span_of_normal (ρ : Representation ℂ L V) (σ : Representation ℂ L W) (χ : L →* ℂˣ)
    (M : Subgroup L) [M.Normal] [Finite (L ⧸ M)] (hχ : M ≤ χ.ker)
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hfi : ∀ g v, f (ρ g v) = σ g (f v))
    (v : V) (hfv : f v ∈ Submodule.span ℂ
      {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}) :
    v ∈ Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} := by
  haveI := Fintype.ofFinite (L ⧸ M)
  set S := Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} with hS
  have h1 : f (avg ρ χ M v) = avg σ χ M (f v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [avg_apply, map_sum, map_smul, hfi]
  have h2 : avg σ χ M (f v) = 0 := by
    have hle : Submodule.span ℂ
        {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}
        ≤ LinearMap.ker (avg σ χ M) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨n, w, hw, rfl⟩
      show avg σ χ M _ = 0
      rw [map_sub, avg_translate σ χ M hχ w hw, map_smul, sub_self]
    exact hle hfv
  have h3 : avg ρ χ M v = 0 := hf (by rw [h1, h2, map_zero])
  have h4 : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v ∈ S := by
    have : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v
        = ∑ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v) := by
      have hq : ∀ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v)
          = v - (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ (Quotient.out q) v := by
        intro q
        rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
          neg_smul, one_smul]
        abel
      rw [Finset.sum_congr rfl (fun q _ => hq q), Finset.sum_sub_distrib, avg_apply]
      simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  rw [h3, sub_zero] at h4
  have hc : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (Submodule.smul_mem_iff _ hc).1 h4

end Finite

section Top

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_finite_support (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ) (x : W)
    (hx : x ∈ twKer σ N θ) :
    ∃ (s : Finset N) (t : Finset W), x ∈ Submodule.span ℂ
      {y | ∃ n ∈ s, ∃ w ∈ t, y = σ (n : G) w - ((θ n : ℂˣ) : ℂ) • w} := by
  classical
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, w, rfl⟩ := hy
    exact ⟨{n}, {w}, Submodule.subset_span ⟨n, by simp, w, by simp, rfl⟩⟩
  | zero => exact ⟨∅, ∅, Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, h⟩ := ha
    obtain ⟨s', t', h'⟩ := hb
    refine ⟨s ∪ s', t ∪ t', Submodule.add_mem _ ?_ ?_⟩
    · refine Submodule.span_mono ?_ h
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_left _ hn, w, Finset.mem_union_left _ hw, rfl⟩
    · refine Submodule.span_mono ?_ h'
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_right _ hn, w, Finset.mem_union_right _ hw, rfl⟩
  | smul c a _ ha =>
    obtain ⟨s, t, h⟩ := ha
    exact ⟨s, t, Submodule.smul_mem _ _ h⟩

def stabIn (τ : Representation ℂ G V) (L : Subgroup G) (x : V) : Subgroup L where
  carrier := {l | τ (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem isOpen_stabIn [TopologicalSpace G] (τ : Representation ℂ G V) (hτ : IsSmooth τ)
    (L : Subgroup G) (x : V) : IsOpen (stabIn τ L x : Set L) :=
  (hτ x).preimage continuous_subtype_val

theorem exists_open_fixing [TopologicalSpace G] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (L : Subgroup G) (O : Subgroup L)
    (hO : IsOpen (O : Set L)) (v : V) (t : Finset W) :
    ∃ M : Subgroup L, IsOpen (M : Set L) ∧ M ≤ O ∧ (∀ m ∈ M, ρ (m : G) v = v) ∧
      ∀ w ∈ t, ∀ m ∈ M, σ (m : G) w = w := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨O ⊓ stabIn ρ L v, ?_, inf_le_left, fun m hm => hm.2, by simp⟩
    rw [Subgroup.coe_inf]
    exact hO.inter (isOpen_stabIn ρ hρ L v)
  | insert a t _ ih =>
    obtain ⟨M, hM, hMO, hMv, hMt⟩ := ih
    refine ⟨M ⊓ stabIn σ L a, ?_, inf_le_left.trans hMO, fun m hm => hMv m hm.1, ?_⟩
    · rw [Subgroup.coe_inf]
      exact hM.inter (isOpen_stabIn σ hσ L a)
    · intro w hw m hm
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hm.2
      · exact hMt w hw m hm.1

theorem twKer_reflect : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W), IsSmooth ρ → IsSmooth σ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V →ₗ[ℂ] W), Function.Injective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    ∀ v : V, f v ∈ twKer σ N θ → v ∈ twKer ρ N θ := by
  intro G V W _ _ _ _ _ _ _ ρ σ hρ hσ N θ hθ hN f hf hfi v hv
  classical
  obtain ⟨s, t, hst⟩ := exists_finite_support σ N θ (f v) hv
  obtain ⟨L, hLN, hsL, hLc⟩ := hN (s.image Subtype.val) (by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact n.2)
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  let ι : L →* N := Subgroup.inclusion hLN
  have hι : Continuous ι := by
    exact Continuous.subtype_mk continuous_subtype_val _
  let χ : L →* ℂˣ := θ.comp ι
  have hχ : IsOpen (χ.ker : Set L) := by
    have : (χ.ker : Set L) = ι ⁻¹' (θ.ker : Set N) := by
      ext l
      simp [χ, MonoidHom.mem_ker]
    rw [this]
    exact hθ.preimage hι
  obtain ⟨M, hMo, hMχ, hMv, hMt⟩ := exists_open_fixing ρ σ hρ hσ L χ.ker hχ v t
  haveI : Finite (L ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo
  haveI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let C : Subgroup L := M.normalCore
  haveI : C.Normal := Subgroup.normalCore_normal M
  haveI : C.FiniteIndex := inferInstance
  haveI : Finite (L ⧸ C) := inferInstance
  have hCM : C ≤ M := Subgroup.normalCore_le M
  have hmain := mem_span_of_normal (ρ.comp L.subtype) (σ.comp L.subtype) χ C (hCM.trans hMχ) f hf
    (fun g x => hfi g x) v (by
      refine Submodule.span_mono ?_ hst
      rintro y ⟨n, hn, w, hw, rfl⟩
      have hnL : (n : G) ∈ L := hsL (by
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨n, hn, rfl⟩)
      refine ⟨⟨n, hnL⟩, w, fun m hm => hMt w hw m (hCM hm), ?_⟩
      rfl)
  refine Submodule.span_le.2 ?_ hmain
  rintro y ⟨n, u, rfl⟩
  exact Submodule.subset_span ⟨ι n, u, rfl⟩

end Top

end GlobalTheory.CompanionTheory.PRep.JacExact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlGD
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem gD_mul_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u v : A) :
    gD i u * gD i v = gD i (u * v) := by
  unfold gD
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem gD_one {A : Type} [CommRing A] {t : ℕ} (i : Fin t) : gD i (1 : A) = 1 := by
  unfold gD
  have h : Function.update (1 : Fin t → A) i 1 = 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [h]
  exact Matrix.diagonal_one

theorem det_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : A) : (gD i u).det = u := by
  unfold gD
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem exists_gl_gD : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : Aˣ),
    ∃ g : GL (Fin t) A, g.1 = gD i (u : A) ∧ Matrix.GeneralLinearGroup.det g = u := by
  intro A _ t i u
  refine ⟨⟨GlobalTheory.CompanionTheory.NullFr.gD i (u : A), GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A), ?_, ?_⟩, rfl, ?_⟩
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.mul_inv, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.inv_mul, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.CompanionTheory.NullFr.det_gD i (u : A)

end GlobalTheory.CompanionTheory.NullFr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsWP
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.AlgCoproduct

theorem exists_isWP : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (n : ℕ),
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra A K) (ι : Fin n → (B →ₐ[A] K)), IsWP ι := by
  intro A _ B _ _ n
  induction n with
  | zero =>
    refine ⟨A, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    constructor
    · intro T _ x y _
      exact ⟨x, by ext a; rfl, fun i => i.elim0⟩
    · intro T _ z z' h _
      exact h
  | succ n ih =>
    obtain ⟨K, _, _, ι, hι⟩ := ih
    refine ⟨B ⊗[A] K, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (ι i)), ?_⟩
    constructor
    · intro T _ x y hy
      obtain ⟨z, hz, hzi⟩ := hι.ex T x (fun i => y i.succ) (fun i => hy i.succ)
      letI : Algebra A T := x.toAlgebra
      let f : B →ₐ[A] T := { y 0 with commutes' := fun a => RingHom.congr_fun (hy 0) a }
      let g : K →ₐ[A] T := { z with commutes' := fun a => RingHom.congr_fun hz a }
      refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩
      · ext a
        exact (Algebra.TensorProduct.productMap f g).commutes a
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · ext b
          simp [f, g]
        · ext b
          have := RingHom.congr_fun (hzi j) b
          simpa [f, g] using this
    · intro T _ z z' h hi
      have hB : ∀ b : B, z (b ⊗ₜ[A] 1) = z' (b ⊗ₜ[A] 1) := fun b => by
        simpa using RingHom.congr_fun (hi 0) b
      have hK : (z.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom) =
          z'.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom := by
        refine hι.uniq T _ _ ?_ (fun i => ?_)
        · ext a
          have := RingHom.congr_fun h a
          simpa [Algebra.TensorProduct.algebraMap_apply] using this
        · ext b
          simpa using RingHom.congr_fun (hi i.succ) b
      refine RingHom.ext fun t => ?_
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b k =>
        have h1 : b ⊗ₜ[A] k = (b ⊗ₜ[A] (1 : K)) * ((1 : B) ⊗ₜ[A] k) := by simp
        have h2 : z ((1 : B) ⊗ₜ[A] k) = z' ((1 : B) ⊗ₜ[A] k) := RingHom.congr_fun hK k
        rw [h1, map_mul, map_mul, hB, h2]
      | add a b ha hb => simp [ha, hb]

end GlobalTheory.CompanionTheory.AlgCoproduct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContainingStatement
section
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compact_lattice_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  first | exact @GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | exact GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | (intros; apply GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup <;> assumption)
end

