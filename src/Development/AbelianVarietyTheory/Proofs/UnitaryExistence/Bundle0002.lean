module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemRange
section
open NumberField

namespace GlobalTheory.ExistsSmulMemRange

theorem exists_smul_mem_range {E : Type} [Field E] [NumberField E] {Λ : Type} [AddCommGroup Λ]
    [Module (RingOfIntegers E) Λ] {r : ℕ} (φ : Λ →ₗ[RingOfIntegers E] Fin r → E)
    (w : Fin r → E) (hw : w ∈ Submodule.span E (Set.range (⇑φ : Λ → Fin r → E))) :
    ∃ (a : RingOfIntegers E) (x : Λ), a ≠ 0 ∧ φ x = a • w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    exact ⟨1, x, one_ne_zero, (one_smul _ _).symm⟩
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, x, ha, hx⟩ := hu
    obtain ⟨b, y, hb, hy⟩ := hv
    refine ⟨a * b, b • x + a • y, mul_ne_zero ha hb, ?_⟩
    rw [map_add (f := _), map_smul, map_smul, hx, hy, smul_add, smul_smul, smul_smul, mul_comm b a]
  | smul t u _ hu =>
    obtain ⟨a, x, ha, hx⟩ := hu
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) t
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (RingOfIntegers E) E q ≠ 0 :=
      fun h => hq0 (IsFractionRing.injective (RingOfIntegers E) E (by simpa using h))
    refine ⟨a * q, p • x, mul_ne_zero ha hq0, ?_⟩
    rw [map_smul, hx]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_mul]
    field_simp

theorem exists_coeffs {E : Type} [Field E] [NumberField E] {Λ : Type} [AddCommGroup Λ]
    [Module (RingOfIntegers E) Λ] {r : ℕ} (φ : Λ →ₗ[RingOfIntegers E] Fin r → E)
    (hinj : Function.Injective (⇑φ : Λ → Fin r → E))
    (hspan : Submodule.span E (Set.range (⇑φ : Λ → Fin r → E)) = ⊤)
    (σ : E →+* ℂ) (f : Λ →+ ℂ)
    (hf : ∀ (a : RingOfIntegers E) (x : Λ), f (a • x) = σ (↑a : E) * f x) :
    ∃ (c : Fin r → ℂ), ∀ (v : Λ), f v = ∑ j : Fin r, c j * σ (φ v j) := by
  classical
  have h1 : ∀ j : Fin r, ∃ (a : RingOfIntegers E) (x : Λ), a ≠ 0 ∧
      φ x = a • (Pi.single j (1 : E) : Fin r → E) :=
    fun j => exists_smul_mem_range φ _ (by rw [hspan]; trivial)
  choose a x ha hx using h1
  have hne : ∀ q : RingOfIntegers E, q ≠ 0 → algebraMap (RingOfIntegers E) E q ≠ 0 :=
    fun q hq0 h => hq0 (IsFractionRing.injective (RingOfIntegers E) E (by simpa using h))
  refine ⟨fun j => f (x j) / σ (algebraMap (RingOfIntegers E) E (a j)), fun v => ?_⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (RingOfIntegers E))
    (fun j : Fin r => φ v j / algebraMap (RingOfIntegers E) E (a j))
  choose b hb using hd
  have hd0 : algebraMap (RingOfIntegers E) E (d : RingOfIntegers E) ≠ 0 :=
    hne _ (nonZeroDivisors.ne_zero d.2)
  have hb' : ∀ j, algebraMap (RingOfIntegers E) E (b j) =
      algebraMap (RingOfIntegers E) E (d : RingOfIntegers E) *
        (φ v j / algebraMap (RingOfIntegers E) E (a j)) := by
    intro j
    rw [hb j, Algebra.smul_def]
  have key : (d : RingOfIntegers E) • v = ∑ j, b j • x j := by
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    funext i
    simp only [map_smul, hx, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · rw [hb' i]
      have := hne _ (ha i)
      simp only [if_true]
      field_simp
    · intro j _ hj
      simp [hj.symm]
    · simp
  have h2 := congrArg f key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum] at h2
  have hσd : σ (algebraMap (RingOfIntegers E) E (d : RingOfIntegers E)) ≠ 0 :=
    (map_ne_zero σ).2 hd0
  apply mul_left_cancel₀ hσd
  refine h2.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hf]
  change σ (algebraMap (RingOfIntegers E) E (b j)) * _ = _
  rw [hb' j, map_mul, map_div₀]
  ring

end GlobalTheory.ExistsSmulMemRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSystemOfParametersInsert
section
open IsLocalRing

namespace GlobalTheory

theorem exists_systemOfParameters_insert (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] (a : S) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧
      ringKrullDim S = (n : WithBot ℕ∞) + 1 ∧
      ∃ N : ℕ, maximalIdeal S ^ N ≤ Ideal.span (insert a (Set.range x)) := by
  classical
  have hIle : Ideal.span {a} ≤ maximalIdeal S := (Ideal.span_singleton_le_iff_mem _).mpr ha
  have hIne : Ideal.span {a} ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hIle))
  have : Nontrivial (S ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (S ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim (S ⧸ Ideal.span {a}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha0) ha
  obtain ⟨s, hsmin, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ Ideal.span {a}))
  have hht := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S ⧸ Ideal.span {a})
  have hsle : Ideal.span (s : Set (S ⧸ Ideal.span {a})) ≤ maximalIdeal (S ⧸ Ideal.span {a}) :=
    hsmin.1.2
  have hcomap : (maximalIdeal (S ⧸ Ideal.span {a})).comap (Ideal.Quotient.mk (Ideal.span {a})) =
      maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmapeq : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (maximalIdeal S) =
      maximalIdeal (S ⧸ Ideal.span {a}) := by
    rw [← hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  let e := s.equivFin
  let x : Fin s.card → S := fun i =>
    (Ideal.Quotient.mk_surjective ((e.symm i : S ⧸ Ideal.span {a}))).choose
  have hx : ∀ i, Ideal.Quotient.mk (Ideal.span {a}) (x i) = e.symm i := fun i =>
    (Ideal.Quotient.mk_surjective _).choose_spec
  have hrange : Ideal.Quotient.mk (Ideal.span {a}) '' Set.range x =
      (s : Set (S ⧸ Ideal.span {a})) := by
    rw [← Set.range_comp]
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      simp only [Function.comp_apply, hx]
      exact (e.symm i).2
    · intro hq
      exact ⟨e ⟨q, hq⟩, by simp [hx]⟩
  refine ⟨s.card, x, fun i => ?_, ?_, ?_⟩
  · rw [← hcomap, Ideal.mem_comap, hx]
    exact hsle (Ideal.subset_span (e.symm i).2)
  · rw [← hdim, ← hht, ← hcard]
    norm_cast
  · have hrad : maximalIdeal (S ⧸ Ideal.span {a}) ≤
        (Ideal.span (s : Set (S ⧸ Ideal.span {a}))).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro p ⟨hsp, hp⟩
      exact hsmin.2 ⟨hp, hsp⟩ (IsLocalRing.le_maximalIdeal hp.ne_top)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨N, fun y hy => ?_⟩
    have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {a})) hy
    rw [Ideal.map_pow, hmapeq] at h1
    have h2 := hN h1
    rw [← hrange, ← Ideal.map_span] at h2
    obtain ⟨z, hz, hzy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hzy)
    exact Ideal.mem_span_insert.mpr ⟨-c, z, hz, by linear_combination hc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GraphRingMono
section
open IsLocalRing Polynomial

namespace GlobalTheory.PBasis

variable {k : Type} [Field k]

def graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    Subring (k × Q) :=
  Subring.closure (Set.range (fun x : k => (x ^ p, f x)) ∪ (fun b => (b, g b)) '' B)

def Indep (p : ℕ) (B : Set k) : Prop :=
  ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) →
    ∀ z ∈ graphRing p f g B, z.1 = 0 → z.2 = 0

lemma graphRing_mono (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) {B C : Set k}
    (h : B ⊆ C) : graphRing p f g B ≤ graphRing p f g C :=
  Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono h))

lemma map_graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    (graphRing p f g B).map (RingHom.fst k Q) =
      Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) := by
  unfold graphRing
  rw [RingHom.map_closure, Set.image_union, ← Set.range_comp, Set.image_image]
  congr 2
  simp

lemma indep_empty {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) : Indep p (∅ : Set k) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g _ z hz h1
  have : graphRing p f g ∅ ≤ ((frobenius k p).prod f).range := by
    unfold graphRing
    rw [Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, hx, _⟩)
    · exact ⟨x, by simp [frobenius_def]⟩
    · exact hx.elim
  obtain ⟨x, rfl⟩ := this hz
  have hx : x ^ p = 0 := by simpa [frobenius_def] using h1
  have : x = 0 := pow_eq_zero_iff hp.ne_zero |>.1 hx
  simp [this]

lemma indep_sUnion (p : ℕ) (c : Set (Set k)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ B ∈ c, Indep p B) : Indep p (⋃₀ c) := by
  intro Q _ f g hg z hz h1
  haveI : Nonempty c := hne.to_subtype
  have hdir : Directed (· ≤ ·) (fun B : c => graphRing p f g B.1) := by
    intro B C
    rcases hc.total B.2 C.2 with h | h
    · exact ⟨C, graphRing_mono p f g h, le_rfl⟩
    · exact ⟨B, le_rfl, graphRing_mono p f g h⟩
  have : graphRing p f g (⋃₀ c) ≤ ⨆ B : c, graphRing p f g B.1 := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, ⟨B, hB, hx⟩, rfl⟩)
    · obtain ⟨B, hB⟩ := hne
      exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
    · exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩))
  obtain ⟨B, hB⟩ := (Subring.mem_iSup_of_directed hdir).1 (this hz)
  exact h B.1 B.2 Q f g (fun b hb => hg b ⟨B.1, B.2, hb⟩) z hB h1

def powField {p : ℕ} (hp : p ≠ 0) (B : Set k) : Subfield k where
  toSubring := Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
  inv_mem' := by
    intro x hx
    change x ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) at hx
    change x⁻¹ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    have : x⁻¹ = x ^ n * (x⁻¹) ^ (n + 1) := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0]; simp
    rw [this]
    exact mul_mem (pow_mem hx n) (Subring.subset_closure (Or.inl ⟨x⁻¹, rfl⟩))

lemma indep_insert {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) {B : Set k} (hB : Indep p B) {a : k}
    (ha : a ∉ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)) : Indep p (insert a B) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g hg z hz h1
  have hga : g a ^ p = f a := hg a (Set.mem_insert _ _)
  have hI := hB Q f g (fun b hb => hg b (Set.mem_insert_of_mem _ hb))
  set S := graphRing p f g B with hS
  let K := powField hp.ne_zero B
  have hK : ∀ s : S, (s : k × Q).1 ∈ K := by
    intro s
    change _ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rw [← map_graphRing p f g B]
    exact ⟨s, s.2, rfl⟩
  let ψ : S →+* K := ((RingHom.fst k Q).comp S.subtype).codRestrict K hK
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    have h1 : (s : k × Q).1 = 0 := congrArg Subtype.val hs
    exact Subtype.ext (Prod.ext h1 (hI s s.2 h1))
  let ev : S[X] →+* k × Q := eval₂RingHom S.subtype (a, g a)
  have hle : graphRing p f g (insert a B) ≤ ev.range := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl | hx, rfl⟩)
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩, by simp [ev]⟩
    · exact ⟨X, by simp [ev]⟩
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩)⟩, by simp [ev]⟩
  obtain ⟨P, rfl⟩ := hle hz
  let c : S := ⟨(a ^ p, f a), Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩
  have hq : (X ^ p - C c : S[X]).Monic := monic_X_pow_sub_C c hp.ne_zero
  have hevq : ev (X ^ p - C c) = 0 := by
    simp [ev, c, hga]
  have hR : ev (P %ₘ (X ^ p - C c)) = ev P := by
    conv_rhs => rw [← modByMonic_add_div P (X ^ p - C c)]
    rw [map_add (f := _), map_mul, hevq, zero_mul, add_zero]
  have hirr : Irreducible (X ^ p - C (ψ c) : K[X]) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    have h2 : (b : k) ^ p = a ^ p := congrArg Subtype.val hb
    have h3 : (b : k) = a := frobenius_inj k p h2
    exact ha (h3 ▸ b.2)
  have haev : ∀ T : S[X], aeval a (T.map ψ) = (ev T).1 := by
    intro T
    rw [aeval_def, eval₂_map]
    change _ = RingHom.fst k Q (eval₂ S.subtype (a, g a) T)
    rw [hom_eval₂]
    rfl
  have hmapq : (X ^ p - C c : S[X]).map ψ = X ^ p - C (ψ c) := by simp
  have hmin : X ^ p - C (ψ c) = minpoly K a :=
    minpoly.eq_of_irreducible_of_monic hirr (by rw [← hmapq, haev, hevq]; rfl)
      (monic_X_pow_sub_C _ hp.ne_zero)
  have hdvd : (X ^ p - C c : S[X]).map ψ ∣ (P %ₘ (X ^ p - C c)).map ψ := by
    rw [hmapq, hmin]
    exact minpoly.dvd K a (by rw [haev, hR, h1])
  haveI : Nontrivial S := ψ.domain_nontrivial
  have hz0 : (P %ₘ (X ^ p - C c)).map ψ = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hdvd
    rw [degree_map_eq_of_injective hψ, degree_map_eq_of_injective hψ]
    exact degree_modByMonic_lt P hq
  rw [Polynomial.map_eq_zero_iff hψ] at hz0
  rw [← hR, hz0, map_zero]
  rfl

theorem exists_pBasis : ∀ (k : Type) [Field k] (p : ℕ), p.Prime → (p : k) = 0 → ∃ B : Set k, Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ ∧ ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) → ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b := by
  intro k _ p hp h0
  obtain ⟨B, -, hB⟩ := zorn_subset_nonempty {B : Set k | Indep p B}
    (fun c hc hch hne => ⟨⋃₀ c, indep_sUnion p c hch hne hc, fun s hs => Set.subset_sUnion_of_mem hs⟩)
    ∅ (indep_empty hp h0)
  have htop : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    by_contra ha
    have := hB.le_of_ge (indep_insert hp h0 hB.prop ha) (Set.subset_insert a B)
    exact ha (Subring.subset_closure (Or.inr (this (Set.mem_insert a B))))
  refine ⟨B, htop, fun Q _ f g hg => ?_⟩
  have hI := hB.prop Q f g hg
  set S := graphRing p f g B with hS
  let φ : S →+* k := (RingHom.fst k Q).comp S.subtype
  have hφ : Function.Bijective φ := by
    constructor
    · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro s hs
      exact Subtype.ext (Prod.ext hs (hI s s.2 hs))
    · intro x
      have : x ∈ S.map (RingHom.fst k Q) := by
        rw [hS, map_graphRing, htop]; trivial
      obtain ⟨s, hs, rfl⟩ := this
      exact ⟨⟨s, hs⟩, rfl⟩
  let e := RingEquiv.ofBijective φ hφ
  have key : ∀ s : S, ((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom (s : k × Q).1 = (s : k × Q).2 := by
    intro s
    have : e.symm (s : k × Q).1 = s := e.symm_apply_apply s
    change ((e.symm (s : k × Q).1 : S) : k × Q).2 = _
    rw [this]
  refine ⟨((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom, fun x => ?_, fun b hb => ?_⟩
  · exact key ⟨(x ^ p, f x), Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
  · exact key ⟨(b, g b), Subring.subset_closure (Or.inr ⟨b, hb, rfl⟩)⟩

end GlobalTheory.PBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Imports
section
namespace GlobalTheory.LatticeBoundedAction

theorem main {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) :
    ∀ v ∈ Submodule.span K (↑Λ : Set V), ∃ (d : R), d ≠ (0 : R) ∧ d • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
    have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have key : (b : R) • (c • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, ← hab, mul_comm, IsLocalization.mk'_spec, algebraMap_smul]
    refine ⟨d * b, mul_ne_zero hd hb, ?_⟩
    rw [mul_smul, key, smul_comm]
    exact Λ.smul_mem a h

end GlobalTheory.LatticeBoundedAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriangularMul
section
namespace GlobalTheory.LowerTriangularMul

theorem lowerTriangular_mul {S : Type} [CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), i < j → A i j = (0 : S))
    (hB : ∀ (i j : Fin n), i < j → B i j = (0 : S)) :
    ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with hik | hki
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (lt_of_le_of_lt hki hij), mul_zero]

theorem main : ∀ {S : Type} [inst : CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S), (∀ (i j : Fin n), i < j → A i j = (0 : S)) → (∀ (i j : Fin n), i < j → B i j = (0 : S)) → ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) :=
  fun A B hA hB => lowerTriangular_mul A B hA hB

end GlobalTheory.LowerTriangularMul
end

