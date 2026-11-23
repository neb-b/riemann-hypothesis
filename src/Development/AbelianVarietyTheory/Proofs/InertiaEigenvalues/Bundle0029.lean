module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTer
section
namespace GlobalTheory.ClosedStatement

open Ideal Module

theorem main {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : Ideal.IsMaximal m] (hne : Ideal.map f m ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = (1 : A) ∧
      (∀ x : A, ∃ a : ι →₀ R, (x - Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i)
        ∈ Ideal.map f m) ∧
      ∀ a : ι →₀ R, (Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i) ∈ Ideal.map f m →
        ∀ i : ι, (a : ι → R) i ∈ m := by
  classical
  letI : Algebra R A := f.toAlgebra
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hf : algebraMap R A = f := rfl
  rw [← hf] at hne ⊢
  haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R A) m) := Ideal.Quotient.nontrivial_iff.mpr hne
  have hli : LinearIndepOn (R ⧸ m) id ({1} : Set (A ⧸ Ideal.map (algebraMap R A) m)) :=
    (linearIndepOn_singleton_iff (R ⧸ m)).mpr one_ne_zero
  let v := Basis.extend hli
  have h1mem : (1 : A ⧸ Ideal.map (algebraMap R A) m) ∈ hli.extend (Set.subset_univ _) :=
    Basis.subset_extend hli rfl
  let b : ↥(hli.extend (Set.subset_univ _)) → A := fun i =>
    if (i : A ⧸ Ideal.map (algebraMap R A) m) = 1 then 1
    else (Ideal.Quotient.mk_surjective (i : A ⧸ Ideal.map (algebraMap R A) m)).choose
  have hb : ∀ i, Ideal.Quotient.mk (Ideal.map (algebraMap R A) m) (b i) = v i := by
    intro i
    rw [Basis.coe_extend]
    simp only [b]
    split_ifs with h
    · rw [map_one, h]
    · exact (Ideal.Quotient.mk_surjective _).choose_spec
  have key : ∀ a : ↥(hli.extend (Set.subset_univ _)) →₀ R,
      Ideal.Quotient.mk (Ideal.map (algebraMap R A) m)
        (Finsupp.sum a fun i y ↦ (algebraMap R A) y * b i) =
      Finsupp.linearCombination (R ⧸ m) v (a.mapRange (Ideal.Quotient.mk m) (map_zero _)) := by
    intro a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    rw [map_mul, hb, Algebra.smul_def, Ideal.Quotient.algebraMap_quotient_map_quotient]
  refine ⟨_, b, ⟨1, h1mem⟩, by simp [b], ?_, ?_⟩
  · intro x
    let g : R ⧸ m → R := fun c => if c = 0 then 0 else (Ideal.Quotient.mk_surjective c).choose
    have hg : ∀ c, Ideal.Quotient.mk m (g c) = c := by
      intro c
      simp only [g]
      split_ifs with h
      · rw [h, map_zero]
      · exact (Ideal.Quotient.mk_surjective c).choose_spec
    refine ⟨(v.repr (Ideal.Quotient.mk _ x)).mapRange g (by simp [g]), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, key]
    have hc : ∀ c : ↥(hli.extend (Set.subset_univ _)) →₀ R ⧸ m,
        (c.mapRange g (by simp [g])).mapRange (Ideal.Quotient.mk m) (map_zero _) = c := by
      intro c; ext i; simp [hg]
    rw [hc, Basis.linearCombination_repr, sub_self]
  · intro a ha i
    rw [← Ideal.Quotient.eq_zero_iff_mem, key] at ha
    have h0 := linearIndependent_iff.mp v.linearIndependent _ ha
    have := congrArg (fun l => l i) h0
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this

end GlobalTheory.ClosedStatement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOverPadicOfIndepModPrime
section
open Polynomial

namespace GlobalTheory

theorem indep_over_Ql_of_indep_mod_l : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  intro l _ d ι w γ hw hn c hc
  by_contra hne
  obtain ⟨a1, ha1⟩ := Function.ne_iff.mp hne
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a => ‖c a‖) ⟨a1, Finset.mem_univ _⟩
  have hc0 : c a₀ ≠ 0 := by
    intro h
    have := ha₀ a1 (Finset.mem_univ _)
    simp only [h, norm_zero] at this
    exact ha1 (norm_le_zero_iff.mp this)
  set c' : Fin d → ℚ_[l] := fun a => c a / c a₀ with hc'
  have hc'le : ∀ a, ‖c' a‖ ≤ 1 := by
    intro a
    simp only [hc', norm_div]
    exact div_le_one_of_le₀ (ha₀ a (Finset.mem_univ _)) (norm_nonneg _)
  have hc'a₀ : c' a₀ = 1 := div_self hc0
  have hsum' : ∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i = 0 := by
    intro i
    have : ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i
        = algebraMap ℚ_[l] ℂ_[l] (c a₀)⁻¹ * ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hc', div_eq_mul_inv, map_mul]
      ring
    rw [this, hc i, mul_zero]
  let e : Fin d → ℤ_[l] := fun a => ⟨c' a, hc'le a⟩
  let n : Fin d → ℕ := fun a => (e a).appr 1
  have hen : ∀ a, ‖e a - (n a : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
    intro a
    have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (by simpa using PadicInt.appr_spec 1 (e a))
    simpa using h
  have hlC : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have hsmall : ∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i := by
    intro i
    have heq : ∑ a, (n a : ℂ_[l]) * w a i
        = ∑ a, ((n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)) * w a i := by
      simp only [sub_mul, Finset.sum_sub_distrib, hsum' i, sub_zero]
    rw [heq, hlC]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    · exact mul_nonneg (by positivity) ((norm_nonneg _).trans (hw a₀ i))
    · intro a _
      rw [norm_mul]
      refine mul_le_mul ?_ (hw a i) (norm_nonneg _) (by positivity)
      have : (n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)
          = algebraMap ℚ_[l] ℂ_[l] (-(((e a - (n a : ℤ_[l]) : ℤ_[l]) : ℚ_[l]))) := by
        have hea : ((e a : ℤ_[l]) : ℚ_[l]) = c' a := rfl
        rw [map_neg, PadicInt.coe_sub, PadicInt.coe_natCast, hea, map_sub, map_natCast]
        ring
      rw [this, norm_algebraMap', norm_neg, PadicInt.padic_norm_e_of_padicInt]
      exact hen a
  have hdiv := hn n hsmall a₀
  have hlt : ‖(n a₀ : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]
    obtain ⟨k, hk⟩ := hdiv
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have he1 : ‖e a₀‖ = 1 := by
    show ‖c' a₀‖ = 1
    rw [hc'a₀, norm_one]
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have : ‖e a₀‖ ≤ max ‖e a₀ - (n a₀ : ℤ_[l])‖ ‖(n a₀ : ℤ_[l])‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (e a₀ - (n a₀ : ℤ_[l])) (n a₀ : ℤ_[l])
  rw [he1] at this
  have := this.trans_lt (max_lt ((hen a₀).trans_lt hlinv) hlt)
  exact lt_irrefl _ this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSmulCocycleEqCoboundary
section
namespace GlobalTheory

theorem index_smul_cocycle_eq_coboundary (R G X : Type) [CommRing R] [Group G] [AddCommGroup X]
    [Module R X] (ρ : Representation R G X) (H : Subgroup G) [H.FiniteIndex] (f : G → X)
    (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (hH : ∃ x, ∀ h ∈ H, f h = ρ h x - x) :
    ∃ x, ∀ g, H.index • f g = ρ g x - x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hH
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → X := fun g => f g - (ρ g x₀ - x₀) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + ρ g (f' h) := by
    intro g h
    simp only [hf', hf, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hz : ∀ h ∈ H, f' h = 0 := by
    intro h hh
    simp only [hf', hx₀ h hh, sub_self]
  have hq : ∀ (g : G) (q : G ⧸ H), f' (g • q).out = f' g + ρ g (f' q.out) := by
    intro g q
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g • q).out : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    have h2 := QuotientGroup.eq.mp h1
    have h3 : (g • q).out = (g * q.out) * ((g * q.out)⁻¹ * (g • q).out) := by group
    rw [h3, hc, hz _ h2, map_zero, add_zero, hc]
  refine ⟨H.index • x₀ - ∑ q : G ⧸ H, f' q.out, fun g => ?_⟩
  have hs : ∑ q : G ⧸ H, f' (g • q).out = ∑ q : G ⧸ H, f' q.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f' q.out)
  simp only [hq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hs
  have hfg : f g = f' g + (ρ g x₀ - x₀) := by simp [hf']
  have hs' : H.index • f' g = ∑ q : G ⧸ H, f' q.out - ρ g (∑ q : G ⧸ H, f' q.out) :=
    eq_sub_of_add_eq hs
  rw [hfg, smul_add, hs', map_sub, map_nsmul, smul_sub]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexTransferAlongProjection
section
namespace GlobalTheory

theorem index_transfer_along_projection {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (L : AddSubgroup M) (T p : M →+ M) (Φ : M →+ N) (h : N →+ N)
    (hpL : ∀ y ∈ L, p y ∈ L) (hTp : ∀ y, T (p y) = p (T y))
    (hT1 : ∀ y, T (y - p y) = y - p y) (hΦ : ∀ y, Φ y = 0 → p y = 0)
    (hΦT : ∀ y, Φ (T y) = h (Φ y)) :
    (L.map T).relIndex L = ((L.map Φ).map h).relIndex (L.map Φ) := by
  have key : ∀ y ∈ L, (y ∈ L.map T ↔ Φ y ∈ (L.map Φ).map h) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Φ x, ⟨x, hx, rfl⟩, (hΦT x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      have h0 : Φ (T x - y) = 0 := by rw [map_sub, hΦT, hxy, sub_self]
      have hp : p (T x) = p y := by
        have := hΦ _ h0
        rwa [map_sub, sub_eq_zero] at this
      refine ⟨p x + (y - p y), L.add_mem (hpL x hx) (L.sub_mem hy (hpL y hy)), ?_⟩
      show T (p x + (y - p y)) = y
      rw [map_add (f := _), hT1, hTp, hp]
      abel
  let ψ : L →+ L.map Φ :=
    (Φ.comp L.subtype).codRestrict (L.map Φ) (fun x => ⟨x.1, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc : (L.map T).addSubgroupOf L =
      (((L.map Φ).map h).addSubgroupOf (L.map Φ)).comap ψ := by
    ext ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact key y hy
  unfold AddSubgroup.relIndex
  rw [hc, AddSubgroup.index_comap_of_surjective _ hψ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntCastTraceEqTraceQuotientOfMem
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quotSpanNat_mk_eq_sum {S : Type} [CommRing S] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ S)
    (n : ℕ) [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] (s : S) :
    Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) s =
      ∑ i, ((b.repr s i : ℤ) : ZMod n) • Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i) := by
  conv_lhs => rw [← b.sum_repr s]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul, map_zsmul]

theorem quotSpanNat_linearIndependent {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] :
    LinearIndependent (ZMod n) (fun i => Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set c : ι → ℤ := fun i => ((g i).val : ℤ) with hc
  have hcg : ∀ i, ((c i : ℤ) : ZMod n) = g i := fun i => by simp [c]
  have h0 : Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (∑ i, c i • b i) = 0 := by
    rw [quotSpanNat_mk_eq_sum b n, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [b.repr_sum_self c, hcg]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨a, ha⟩ := h0
  have hrep := congrArg (fun y => b.repr y i) ha
  simp only [b.repr_sum_self c] at hrep
  have : a * ((n : ℕ) : S) = ((n : ℤ)) • a := by
    rw [zsmul_eq_mul, mul_comm]; simp
  rw [this, map_zsmul] at hrep
  rw [← hcg i, ← hrep]
  simp

noncomputable def zmodRingHomOfCastEqZero {R : Type} [CommRing R] (n : ℕ) (h : (n : R) = 0) :
    ZMod n →+* R :=
  (Ideal.Quotient.lift (Ideal.span {(n : ℤ)}) (Int.castRingHom R) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      simp [h])).comp (Int.quotientSpanNatEquivZMod n).symm.toRingHom

noncomputable def quotSpanNatBasis {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] :
    Module.Basis ι (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)}) :=
  Module.Basis.mk (quotSpanNat_linearIndependent b n) (by
    rintro y -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotSpanNat_mk_eq_sum b n s]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem quotSpanNatBasis_apply {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})]
    (i : ι) : quotSpanNatBasis b n i = Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i) :=
  Module.Basis.mk_apply _ _ _

theorem quotSpanNatBasis_repr {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})]
    (s : S) (i : ι) : (quotSpanNatBasis b n).repr (Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) s) i =
      ((b.repr s i : ℤ) : ZMod n) := by
  have h := quotSpanNat_mk_eq_sum b n s
  simp_rw [← quotSpanNatBasis_apply b n] at h
  rw [h, (quotSpanNatBasis b n).repr_sum_self]

theorem intCast_trace_eq_trace_quotSpanNat {S : Type} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] (x : S) :
    ((Algebra.trace ℤ S x : ℤ) : ZMod n) =
      Algebra.trace (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)}) (Ideal.Quotient.mk _ x) := by
  let b := Module.Free.chooseBasis ℤ S
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (quotSpanNatBasis b n)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Int.cast_sum, quotSpanNatBasis_apply, ← map_mul,
    quotSpanNatBasis_repr]

theorem isLocalRing_zmod_primePow (l b : ℕ) [Fact l.Prime] (hb : b ≠ 0) : IsLocalRing (ZMod (l ^ b)) := by
  have : Fact (1 < l ^ b) := ⟨Nat.one_lt_pow hb (Fact.out : l.Prime).one_lt⟩
  exact IsLocalRing.of_surjective' (PadicInt.toZModPow (p := l) b) (ZMod.ringHom_surjective _)

theorem free_finite_fst_of_prod (l b : ℕ) [Fact l.Prime] (M N : Type) [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod (l ^ b)) M] [Module (ZMod (l ^ b)) N] [Module.Free (ZMod (l ^ b)) (M × N)]
    [Module.Finite (ZMod (l ^ b)) (M × N)] :
    Module.Free (ZMod (l ^ b)) M ∧ Module.Finite (ZMod (l ^ b)) M := by
  rcases eq_or_ne b 0 with rfl | hb
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    haveI : Subsingleton M := by
      refine ⟨fun x y => ?_⟩
      rw [← one_smul (ZMod (l ^ 0)) x, ← one_smul (ZMod (l ^ 0)) y, Subsingleton.elim (1 : ZMod (l ^ 0)) 0,
        zero_smul, zero_smul]
    exact ⟨inferInstance, inferInstance⟩
  haveI := isLocalRing_zmod_primePow l b hb
  haveI : Module.Projective (ZMod (l ^ b)) M :=
    Module.Projective.of_split (LinearMap.inl _ M N) (LinearMap.fst _ M N) (by ext; simp)
  haveI : Module.Finite (ZMod (l ^ b)) M :=
    Module.Finite.of_surjective (LinearMap.fst _ M N) LinearMap.fst_surjective
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

theorem intCast_trace_eq_trace_quotient_of_mem (L : Type) [Field L] [NumberField L] (l b : ℕ) [Fact l.Prime]
    (I Q : Ideal (𝓞 L)) (hsup : I ⊔ Q = ⊤) (hmul : I * Q = Ideal.span {((l ^ b : ℕ) : 𝓞 L)})
    [Algebra (ZMod (l ^ b)) (𝓞 L ⧸ I)] (x : 𝓞 L) (hx : x ∈ Q) :
    ((Algebra.trace ℤ (𝓞 L) x : ℤ) : ZMod (l ^ b)) =
      Algebra.trace (ZMod (l ^ b)) (𝓞 L ⧸ I) (Ideal.Quotient.mk I x) := by
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hnIQ : ((l ^ b : ℕ) : 𝓞 L) ∈ I * Q := by rw [hmul]; exact Ideal.mem_span_singleton_self _
  have hnQ : ((l ^ b : ℕ) : 𝓞 L) ∈ Q := (Ideal.mul_le_inf.trans inf_le_right) hnIQ
  letI instJ : Algebra (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    (zmodRingHomOfCastEqZero (l ^ b) (by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _)).toAlgebra
  letI instQ : Algebra (ZMod (l ^ b)) (𝓞 L ⧸ Q) :=
    (zmodRingHomOfCastEqZero (l ^ b) (by
      rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
      exact hnQ)).toAlgebra
  have hcop : IsCoprime I Q := Ideal.isCoprime_iff_sup_eq.mpr hsup
  let e : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) ≃+* (𝓞 L ⧸ I) × (𝓞 L ⧸ Q) :=
    (Ideal.quotEquivOfEq hmul.symm).trans (Ideal.quotientMulEquivQuotientProd I Q hcop)
  have he : ∀ y : 𝓞 L, e (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) y) = (Ideal.Quotient.mk I y, Ideal.Quotient.mk Q y) := by
    intro y
    refine Prod.ext ?_ ?_ <;>
      simp [e, Ideal.quotientMulEquivQuotientProd_fst, Ideal.quotientMulEquivQuotientProd_snd,
        Ideal.Quotient.factor_mk]
  let eA : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) ≃ₐ[ZMod (l ^ b)] (𝓞 L ⧸ I) × (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := e) (fun r => congrArg (fun f => f r)
      (Subsingleton.elim ((e : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) →+* _).comp (algebraMap (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)})))
        (algebraMap (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)))))
  haveI hfreeJ : Module.Free (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    Module.Free.of_basis (quotSpanNatBasis (Module.Free.chooseBasis ℤ (𝓞 L)) (l ^ b))
  haveI hfinJ : Module.Finite (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    Module.Finite.of_basis (quotSpanNatBasis (Module.Free.chooseBasis ℤ (𝓞 L)) (l ^ b))
  haveI : Module.Free (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)) := Module.Free.of_equiv eA.toLinearEquiv
  haveI : Module.Finite (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)) := Module.Finite.equiv eA.toLinearEquiv
  obtain ⟨hfI, hfinI⟩ := free_finite_fst_of_prod l b (𝓞 L ⧸ I) (𝓞 L ⧸ Q)
  haveI : Module.Free (ZMod (l ^ b)) ((𝓞 L ⧸ Q) × (𝓞 L ⧸ I)) :=
    Module.Free.of_equiv (LinearEquiv.prodComm (ZMod (l ^ b)) (𝓞 L ⧸ I) (𝓞 L ⧸ Q))
  haveI : Module.Finite (ZMod (l ^ b)) ((𝓞 L ⧸ Q) × (𝓞 L ⧸ I)) :=
    Module.Finite.equiv (LinearEquiv.prodComm (ZMod (l ^ b)) (𝓞 L ⧸ I) (𝓞 L ⧸ Q))
  obtain ⟨hfQ, hfinQ⟩ := free_finite_fst_of_prod l b (𝓞 L ⧸ Q) (𝓞 L ⧸ I)
  rw [intCast_trace_eq_trace_quotSpanNat (l ^ b) x, ← Algebra.trace_eq_of_algEquiv eA]
  have : eA (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) x) = (Ideal.Quotient.mk I x, 0) := by
    show e _ = _
    rw [he, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  rw [this, Algebra.trace_prod_apply, map_zero, add_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantAll
section
namespace GlobalTheory.InvariantBotOrTop

open Matrix

theorem invariant_all {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) (A : Matrix (Fin r) (Fin r) k) :
    ∀ x ∈ W, A.map (algebraMap k K) *ᵥ x ∈ W := by
  have hA : A ∈ Submodule.span k (Set.range M) := by
    rw [hM]
    exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    exact hW g
  | zero =>
    intro x _
    rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
    exact W.zero_mem
  | add A B _ _ hA hB =>
    intro x hx
    rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
    exact W.add_mem (hA x hx) (hB x hx)
  | smul c A _ hA =>
    intro x hx
    rw [Matrix.map_smul _ c (fun a => by rw [smul_eq_mul, map_mul, Algebra.smul_def])]
    first
      | rw [Matrix.smul_mulVec]
      | rw [Matrix.smul_mulVec_assoc]
    exact W.smul_of_tower_mem c (hA x hx)

theorem bot_or_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)

  have he : ∀ i, (Pi.single i (1 : K) : Fin r → K) ∈ W := by
    intro i
    have h1 := invariant_all M hM W hW (Matrix.single i j 1) x hxW
    have h2 : (Matrix.single i j (1 : k)).map (algebraMap k K) *ᵥ x = x j • Pi.single i 1 := by
      ext a
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      by_cases hai : a = i
      · subst hai
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb]) (by simp)]
        simp [Matrix.single_apply]
      · rw [Finset.sum_eq_zero (fun b _ => by simp [Matrix.single_apply, hai, Ne.symm hai])]
        simp [Pi.single_apply, hai]
    rw [h2] at h1
    have h3 := W.smul_mem (x j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h3
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K) := by
    ext a
    simp [Pi.single_apply]
  rw [hy]
  exact W.sum_mem fun i _ => W.smul_mem _ (he i)

theorem main : ∀ {Γ k K : Type} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] {r : ℕ} (M : Γ → Matrix (Fin r) (Fin r) k), Submodule.span k (Set.range M) = ⊤ → ∀ (W : Submodule K (Fin r → K)), (∀ (g : Γ), ∀ x ∈ W, Matrix.mulVec (Matrix.map (M g) (⇑(Algebra.algebraMap k K) : k → K)) x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro Γ k K _ _ _ r M hM W hW
  exact bot_or_top M hM W hW

end GlobalTheory.InvariantBotOrTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralPi
section
namespace GlobalTheory.IntegralPi

open Polynomial

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i)
    (hx : ∀ i, IsIntegral O (x i)) : IsIntegral O x := by
  classical
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ => hpm i), ?_⟩
  rw [← aeval_def]
  funext j
  have key : (aeval x (∏ i, p i)) j = aeval (x j) (∏ i, p i) := by
    have := (aeval_algHom_apply (Pi.evalAlgHom O R j) x (∏ i, p i)).symm
    simpa using this
  rw [key, map_prod, Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [aeval_def]; exact hp j)

theorem main : ∀ {O : Type} [inst : CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [inst_2 : (i : ι) → CommRing (R i)] [inst_3 : (i : ι) → Algebra O (R i)] (x : (i : ι) → R i),
    (∀ (i : ι), IsIntegral O (x i)) → IsIntegral O x :=
  fun x hx => isIntegral_pi x hx

end GlobalTheory.IntegralPi
end

