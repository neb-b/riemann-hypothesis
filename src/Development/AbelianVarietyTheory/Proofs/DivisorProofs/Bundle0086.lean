module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearVanishOfProdVanish
section
open Finset Function

namespace GlobalTheory

theorem multilinear_vanish_of_prod_vanish_of_agree_off_finset {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : (∀ i, A i) →ₘₗ[K] M) (S : Finset ι) :
    ∀ {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i),
      (∀ i ∉ S, ∀ d ∈ s, ∀ d' ∈ s, f d i = f d' i) →
      (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) →
      ∑ d ∈ s, c d • P (f d) = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro D s c f hconst hx
    rcases s.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩
    · simp
    have hf : ∀ d ∈ s, f d = f d₀ := fun d hd =>
      funext fun i => hconst i (Finset.notMem_empty i) d hd d₀ hd₀
    have hsum : ∑ d ∈ s, c d • P (f d) = (∑ d ∈ s, c d) • P (f d₀) := by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    have hx' : ∀ x : ∀ i, X i, (∑ d ∈ s, c d) * ∏ i, (f d₀ i : X i → K) (x i) = 0 := by
      intro x; rw [Finset.sum_mul, ← hx x]
      exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    rw [hsum]
    by_cases hc : ∑ d ∈ s, c d = 0
    · rw [hc, zero_smul]
    · by_contra hne
      have hex : ∀ i, ∃ t : X i, (f d₀ i : X i → K) t ≠ 0 := by
        intro i
        by_contra h
        push Not at h
        apply hne
        have h0 : f d₀ i = 0 := by
          apply Subtype.ext
          funext t
          simpa using h t
        rw [P.map_coord_zero i h0, smul_zero]
      choose x hxne using hex
      have h1 := hx' x
      rw [mul_eq_zero] at h1
      rcases h1 with h | h
      · exact hc h
      · exact (Finset.prod_ne_zero_iff.mpr fun i _ => hxne i) h
  | insert i₀ S hi₀ ih =>
    intro D s c f hconst hx
    classical
    let W : Submodule K (A i₀) := Submodule.span K (↑(s.image fun d => f d i₀))
    let b := Module.finBasis K W
    have hmem : ∀ d ∈ s, f d i₀ ∈ W := fun d hd =>
      Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨d, hd, rfl⟩)
    let a : D → Fin (Module.finrank K W) → K := fun d l =>
      if hd : d ∈ s then b.repr ⟨f d i₀, hmem d hd⟩ l else 0
    have hexp : ∀ d ∈ s, f d i₀ = ∑ l, a d l • (b l : A i₀) := by
      intro d hd
      have h := congrArg Subtype.val (b.sum_repr ⟨f d i₀, hmem d hd⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      simp only [a, dite_eq_left hd]
      exact h.symm
    have hP : ∀ d ∈ s, P (f d) = ∑ l, a d l • P (update (f d) i₀ (b l)) := by
      intro d hd
      have e : f d = update (f d) i₀ (∑ l, a d l • (b l : A i₀)) := by
        rw [← hexp d hd, update_eq_self]
      rw [e, P.map_update_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [P.map_update_smul, RingHom.id_apply, update_idem]

    have hsplit : ∀ (g : ∀ i, A i) (y : ∀ i, X i), ∏ i, (g i : X i → K) (y i) =
        (g i₀ : X i₀ → K) (y i₀) * ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y =>
      (Finset.mul_prod_erase univ (fun i => (g i : X i → K) (y i)) (mem_univ i₀)).symm
    have hupd : ∀ (g : ∀ i, A i) (v : A i₀) (y : ∀ i, X i),
        ∏ i ∈ univ.erase i₀, (update g i₀ v i : X i → K) (y i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g v y =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hupdx : ∀ (g : ∀ i, A i) (y : ∀ i, X i) (t : X i₀),
        ∏ i ∈ univ.erase i₀, (g i : X i → K) (update y i₀ t i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y t =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hli : LinearIndependent K (fun l => ((b l : A i₀) : X i₀ → K)) :=
      b.linearIndependent.map' ((A i₀).subtype ∘ₗ W.subtype)
        (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective.comp Subtype.val_injective))

    have hB : ∀ (x : ∀ i, X i) (l : Fin (Module.finrank K W)),
        ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) = 0 := by
      intro x
      refine Fintype.linearIndependent_iff.mp hli _ ?_
      funext t
      have h := hx (update x i₀ t)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hsplit, hupdx, update_self, hexp d hd]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have hstep : ∑ d ∈ s, c d • P (f d) =
        ∑ l, ∑ d ∈ s, (c d * a d l) • P (update (f d) i₀ (b l)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hP d hd, Finset.smul_sum]
      simp only [mul_smul]
    rw [hstep]
    refine Finset.sum_eq_zero fun l _ => ih s (fun d => c d * a d l)
      (fun d => update (f d) i₀ (b l)) ?_ ?_
    · intro i hi d hd d' hd'
      by_cases h : i = i₀
      · subst h; simp
      · simp only [update_of_ne h]
        exact hconst i (by simp [h, hi]) d hd d' hd'
    · intro x
      have h := hB x l
      calc ∑ d ∈ s, c d * a d l * ∏ i, (update (f d) i₀ (b l) i : X i → K) (x i)
          = ((b l : A i₀) : X i₀ → K) (x i₀) *
              ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [hsplit, hupd, update_self]
            ring
        _ = 0 := by rw [h, mul_zero]

theorem multilinear_vanish_of_prod_vanish {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : (∀ i, A i) →ₘₗ[K] M) {D : Type} (s : Finset D) (c : D → K)
    (f : D → ∀ i, A i)
    (hx : ∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) :
    ∑ d ∈ s, c d • P (f d) = 0 :=
  multilinear_vanish_of_prod_vanish_of_agree_off_finset A P univ s c f (fun i hi => absurd (mem_univ i) hi) hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyOfShortExactMul
section
open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_eq_coker_mul_ker_of_exact {R : Type} [Ring R] {A A' B D D' : Type}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup D] [AddCommGroup D']
    [Module R A] [Module R A'] [Module R B] [Module R D] [Module R D']
    (f : A →ₗ[R] A') (g : A' →ₗ[R] B) (d : B →ₗ[R] D) (h : D →ₗ[R] D')
    (e₁ : LinearMap.range f = LinearMap.ker g) (e₂ : LinearMap.range g = LinearMap.ker d)
    (e₃ : LinearMap.range d = LinearMap.ker h) :
    Nat.card B = Nat.card (A' ⧸ LinearMap.range f) * Nat.card (LinearMap.ker h) := by
  have h1 : Nat.card B = Nat.card (B ⧸ LinearMap.ker d) * Nat.card (LinearMap.ker d) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker d).toAddSubgroup
  rw [h1, Nat.card_congr d.quotKerEquivRange.toEquiv, e₃, e₁,
    Nat.card_congr g.quotKerEquivRange.toEquiv, e₂, mul_comm]

theorem natCard_homology_of_shortExact_mul : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  intro p C G π hz hS n
  have hmul0 : ∀ k, HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k = (p : ℤ) • 𝟙 _ := by
    intro k
    have := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) k).map_zsmul
      (f := 𝟙 C) (r := (p : ℤ))
    rw [CategoryTheory.Functor.map_id] at this
    exact this
  have hmul : ∀ k, (HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k).hom
      = (p : ℤ) • (LinearMap.id : C.homology k →ₗ[ℤ] C.homology k) := by
    intro k
    rw [hmul0]
    ext x
    simp
  have e2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have e3 := (hS.homology_exact₃ n (n+1) rfl).moduleCat_range_eq_ker
  have e1 := (hS.homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker
  dsimp only at e1 e2 e3
  rw [hmul] at e1 e2
  exact natCard_eq_coker_mul_ker_of_exact _ _ _ _ e2 e3 e1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardQuotSmulTopLePowFinrank
section
open NumberField

namespace GlobalTheory


open TensorProduct in
theorem natCard_quot_maximal_smul_top_eq {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) = Nat.card (R ⧸ P) ^ Module.finrank R M := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  rw [← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]
  congr 1
  let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
    rw [Module.rankAtStalk_eq]
    exact Ideal.finrank_fiber_eq_finrank _
  rw [← h2, ← h1]
  rfl

theorem natCard_quot_smul_top_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La →
    ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g →
    Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧
      Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  intro E _ _ La _ _ hfin hproj I g hg hI
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact hg.prime.irreducible)
  have hne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  have hR : Nat.card (𝓞 E ⧸ I) = g := by
    rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcard := natCard_quot_maximal_smul_top_eq (R := 𝓞 E) (M := La) I
  rw [hR] at hcard
  refine ⟨?_, hcard.le⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hg.ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegral
section
namespace GlobalTheory.CoordinateBasisBounds

open NumberField

theorem nat_mul_integral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ o : 𝓞 E, (m : E) * x = algebraMap (𝓞 E) E o := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, h⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E) hx
  exact ⟨m, Nat.pos_of_ne_zero hm, s, by rw [← h, nsmul_eq_mul]⟩

theorem coord_bound {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, ∀ i : Fin n, ∃ o : 𝓞 E, (N : E) * x i = algebraMap (𝓞 E) E o := by
  obtain ⟨S, hS⟩ := hL
  have key : ∀ v ∈ S, ∃ m : ℕ, 0 < m ∧ ∀ i : Fin n, ∃ o : 𝓞 E, (m : E) * v i = algebraMap (𝓞 E) E o := by
    intro v _
    choose m hm o ho using fun i : Fin n => nat_mul_integral (v i)
    refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm i), fun i => ?_⟩
    have hd : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hd
    refine ⟨(k : 𝓞 E) * o i, ?_⟩
    rw [hk, map_mul, ← ho i, map_natCast]; push_cast; ring
  classical
  choose! m hm hv using key
  refine ⟨∏ v ∈ S, m v, Finset.prod_pos (fun v hv' => hm v hv'), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem v hvS =>
    intro i
    obtain ⟨o, ho⟩ := hv v hvS i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hvS
    refine ⟨(k : 𝓞 E) * o, ?_⟩
    rw [hk, map_mul, ← ho, map_natCast]; push_cast; ring
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by rw [map_add (f := _), ← ha, ← hb, Pi.add_apply]; ring⟩
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    refine ⟨c * a, ?_⟩
    rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]; ring

theorem basis_bound {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hspan]; trivial
  induction hy using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_pos, by simpa using hv⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul, smul_add]
      push_cast; ring_nf
    rw [e]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨m, hm, o, ho⟩ := nat_mul_integral c
    refine ⟨m * d, Nat.mul_pos hm hd, ?_⟩
    have e : ((m * d : ℕ) : E) • (c • x) = o • ((d : E) • x) := by
      rw [← algebraMap_smul E o, ← ho, smul_smul, smul_smul]; push_cast; ring_nf
    rw [e]
    exact L.smul_mem o hdx

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∃ (N : ℕ), (0 : ℕ) < N ∧ (∀ (j : Fin n), (↑N : E) • Pi.single j (1 : E) ∈ L) ∧ ∀ x ∈ L, ∀ (i : Fin n), ∃ (o : NumberField.RingOfIntegers E), (↑N : E) * x i = (Algebra.algebraMap (NumberField.RingOfIntegers E) E : NumberField.RingOfIntegers E → E) o := by
  intro E _ _ n L hL hspan
  obtain ⟨M, hM, hcoord⟩ := GlobalTheory.CoordinateBasisBounds.coord_bound L hL
  choose d hd hdL using fun j : Fin n => GlobalTheory.CoordinateBasisBounds.basis_bound L hspan (Pi.single j (1 : E))
  refine ⟨M * ∏ j, d j, Nat.mul_pos hM (Finset.prod_pos fun j _ => hd j), ?_, ?_⟩
  · intro j
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
    have e : ((M * ∏ j, d j : ℕ) : E) • Pi.single j (1 : E) = (M * k) • ((d j : E) • Pi.single j (1 : E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hk]; push_cast; ring_nf
    rw [e]
    exact nsmul_mem (hdL j) _
  · intro x hx i
    obtain ⟨o, ho⟩ := hcoord x hx i
    refine ⟨((∏ j, d j : ℕ) : 𝓞 E) * o, ?_⟩
    rw [map_mul, ← ho, map_natCast]; push_cast; ring

end GlobalTheory.CoordinateBasisBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoCommonZeroSpreadsConstructibleNbhd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace NoCommonZeroSpread

lemma exists_common_denominator {A Ω : Type} [CommRing A] [Field Ω] (φ : A →+* Ω)
    (S : Finset Ω) (hS : ∀ x ∈ S, x ∈ Subfield.closure (φ.range : Set Ω)) :
    ∃ b : A, φ b ≠ 0 ∧ ∀ x ∈ S, φ b * x ∈ Set.range φ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x S hx ih =>
    obtain ⟨b, hb, hbS⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    have hxK := hS x (Finset.mem_insert_self x S)
    rw [Subfield.mem_closure_iff, Subring.closure_eq] at hxK
    obtain ⟨y, hy, z, hz, hyz⟩ := hxK
    obtain ⟨a, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨c, rfl⟩ := RingHom.mem_range.1 hz
    by_cases hc : φ c = 0
    · have hx0 : x = 0 := by rw [← hyz, hc, div_zero]
      refine ⟨b, hb, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · exact ⟨0, by rw [h, hx0, mul_zero, map_zero]⟩
      · exact hbS w h
    · refine ⟨b * c, by simp [hb, hc], fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · refine ⟨b * a, ?_⟩
        rw [h, ← hyz, map_mul, map_mul]
        field_simp
      · obtain ⟨d, hd⟩ := hbS w h
        refine ⟨d * c, ?_⟩
        rw [map_mul, hd, map_mul]
        ring

theorem no_common_zero_spreads : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by
  intro A _ τ J _ F Ω _ _ φ hno
  classical
  let G : J → MvPolynomial τ Ω := fun j => MvPolynomial.map φ (F j)

  have h1 : (1 : MvPolynomial τ Ω) ∈ Ideal.span (Set.range G) := by
    have hz : MvPolynomial.zeroLocus Ω (Ideal.span (Set.range G)) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hno
      refine ⟨x, fun j => ?_⟩
      have := hx (G j) (Ideal.subset_span ⟨j, rfl⟩)
      simpa [G, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_map] using this
    have := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) (Ideal.span (Set.range G))
    rw [hz, MvPolynomial.vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at this
    rw [this]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1

  let K : Subfield Ω := Subfield.closure (φ.range : Set Ω)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap K Ω).injective)
  have hg1 : ∀ y : K, g (y : Ω) = y := fun y => by
    exact LinearMap.congr_fun hg y
  have hgK : ∀ (x : Ω) (y : K), ((g (x * y) : K) : Ω) = (g x : Ω) * y := by
    intro x y
    have : x * (y : Ω) = y • x := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]
  have hφK : ∀ a : A, φ a ∈ K := fun a => Subfield.subset_closure (RingHom.mem_range_self φ a)
  let P : MvPolynomial τ Ω → MvPolynomial τ Ω := fun h =>
    ∑ m ∈ h.support, MvPolynomial.monomial m ((g (h.coeff m) : K) : Ω)
  have hPc : ∀ h n, (P h).coeff n = ((g (h.coeff n) : K) : Ω) := by
    intro h n
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 hn]; simp
  have hPadd : ∀ h₁ h₂, P (h₁ + h₂) = P h₁ + P h₂ := by
    intro h₁ h₂; ext n; simp [hPc, MvPolynomial.coeff_add]
  have hP1 : P 1 = 1 := by
    ext n
    rw [hPc, MvPolynomial.coeff_one]
    split_ifs
    · have := hg1 1; simpa using this
    · simp
  have hPmul : ∀ h j, P (h * G j) = P h * G j := by
    intro h j; ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPc, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
    refine (map_sum K.subtype _ _).trans (Finset.sum_congr rfl fun x _ => ?_)
    show ((g _ : K) : Ω) = _
    have e : (G j).coeff x.2 = ((⟨φ ((F j).coeff x.2), hφK _⟩ : K) : Ω) := by
      simp [G, MvPolynomial.coeff_map]
    rw [e, hgK, hPc]
  let PA : MvPolynomial τ Ω →+ MvPolynomial τ Ω := AddMonoidHom.mk' P hPadd
  have hsum : ∑ j ∈ c.support, P (c j) * G j = 1 := by
    simp only [Finsupp.sum, smul_eq_mul] at hc
    have := congrArg PA hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [PA, AddMonoidHom.mk'_apply] at this
    rw [← hP1]
    convert this using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (hPmul _ _).symm

  let S : Finset Ω := c.support.biUnion (fun j => (P (c j)).coeffs)
  obtain ⟨b, hb, hbS⟩ := exists_common_denominator φ S (by
    intro x hx
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hj
    rw [hPc]; exact (g _).2)
  have hQ : ∀ j, ∃ q : MvPolynomial τ A,
      MvPolynomial.map φ q = MvPolynomial.C (φ b) * P (c j) := by
    intro j
    have : MvPolynomial.C (φ b) * P (c j) ∈ Set.range (MvPolynomial.map (σ := τ) φ) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro y hy
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 (Finset.mem_coe.1 hy)
      rw [MvPolynomial.coeff_C_mul]
      by_cases hn : (P (c j)).coeff n = 0
      · rw [hn, mul_zero]; exact ⟨0, map_zero φ⟩
      · have hj : j ∈ c.support := by
          rw [Finsupp.mem_support_iff]
          intro h0; apply hn; rw [hPc, h0]; simp
        exact hbS _ (Finset.mem_biUnion.2 ⟨j, hj,
          MvPolynomial.mem_coeffs_iff.2 ⟨n, MvPolynomial.mem_support_iff.2 hn, rfl⟩⟩)
    exact this
  choose q hq using hQ
  let E : MvPolynomial τ A := MvPolynomial.C b - ∑ j ∈ c.support, q j * F j
  have hE : MvPolynomial.map φ E = 0 := by
    have hG : ∀ j, MvPolynomial.map φ (F j) = G j := fun j => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, map_sub, map_sum, map_mul, MvPolynomial.map_C, hq, hG, _root_.mul_assoc]
    rw [← Finset.mul_sum, hsum, _root_.mul_one, sub_self]
  refine ⟨b, E.coeffs, hb, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hy
    have := congrArg (AddMonoidAlgebra.coeff · n) hE
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
  · intro k _ ψ hψb hψI ⟨z, hz⟩
    have h0 : MvPolynomial.map ψ E = 0 := by
      ext n
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hn : n ∈ E.support
      · exact hψI _ (MvPolynomial.mem_coeffs_iff.2 ⟨n, hn, rfl⟩)
      · rw [MvPolynomial.notMem_support_iff.1 hn, map_zero]
        rfl
    have h2 : MvPolynomial.eval₂ ψ z E = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map, h0, map_zero]
    have h3 : MvPolynomial.eval₂ ψ z E = ψ b := by
      simp [E, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum,
        MvPolynomial.eval₂_mul, hz]
    exact hψb (h3 ▸ h2)

end NoCommonZeroSpread
end GlobalTheory
end

