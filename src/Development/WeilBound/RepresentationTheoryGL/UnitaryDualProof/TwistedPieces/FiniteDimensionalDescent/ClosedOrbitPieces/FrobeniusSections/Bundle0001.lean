module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.CompIterateFrobenius
section
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial IntermediateField

theorem fl_step {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [hp : Fact p.Prime]
    [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E))
    (L : IntermediateField F E) {x : E} (hx : x ∉ L) :
    finrank L (adjoin L {x}) = p := by
  obtain ⟨a, ha⟩ := h x
  have hxp : x ^ p ∈ L := ha ▸ L.algebraMap_mem a
  set b : L := ⟨x ^ p, hxp⟩ with hb
  have hirr : Irreducible (X ^ p - C b) := by
    apply X_pow_sub_C_irreducible_of_prime hp.out
    intro y hy
    apply hx
    have h1 : (y : E) ^ p = x ^ p := by
      have := congrArg (fun z : L => (z : E)) hy
      simpa [hb] using this
    have h2 : (y : E) = x := frobenius_inj E p (by simpa [frobenius_def] using h1)
    exact h2 ▸ y.2
  have haev : aeval x (X ^ p - C b) = 0 := by
    simp [hb]
  have hmon : (X ^ p - C b).Monic := monic_X_pow_sub_C _ hp.out.ne_zero
  have hmin : X ^ p - C b = minpoly L x := minpoly.eq_of_irreducible_of_monic hirr haev hmon
  have hint : IsIntegral L x := ⟨X ^ p - C b, hmon, by simpa [aeval_def] using haev⟩
  rw [adjoin.finrank hint, ← hmin, natDegree_X_pow_sub_C _]

theorem fl_greedy {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [hp : Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∀ (N : ℕ) (L : IntermediateField F E), L.relfinrank ⊤ = N →
      ∃ n, L.relfinrank ⊤ = p ^ n ∧ ∃ α : Fin n → E, L ⊔ adjoin F (Set.range α) = ⊤ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro L hL
  by_cases hT : L = ⊤
  · subst hT
    exact ⟨0, by simp [relfinrank_self], Fin.elim0, top_sup_eq _⟩
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hT)
  set L' : IntermediateField F E := (adjoin L ({x} : Set E)).restrictScalars F with hL'
  have hsup : L' = L ⊔ adjoin F ({x} : Set E) := by rw [hL', restrictScalars_adjoin_eq_sup]
  have hle : L ≤ L' := hsup ▸ le_sup_left
  have hdeg : L.relfinrank L' = p := by
    rw [relfinrank_eq_finrank_of_le hle]
    have : extendScalars hle = adjoin L ({x} : Set E) :=
      restrictScalars_injective F (by rw [extendScalars_restrictScalars])
    rw [this, fl_step p h L hx]
  have hmul := relfinrank_mul_relfinrank hle (le_top : L' ≤ ⊤)
  have hpos : 0 < L.relfinrank ⊤ := by
    rw [relfinrank_top_right]; exact Module.finrank_pos
  have hlt : L'.relfinrank ⊤ < N := by
    rw [← hL, ← hmul, hdeg]
    have h2 := hp.out.two_le
    have : 0 < L'.relfinrank ⊤ := by
      rcases Nat.eq_zero_or_pos (L'.relfinrank ⊤) with h0 | h0
      · rw [← hmul, h0, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    nlinarith
  obtain ⟨m, hm, β, hβ⟩ := ih _ hlt L' rfl
  refine ⟨m + 1, ?_, Fin.cons x β, ?_⟩
  · rw [← hmul, hdeg, hm, pow_succ']
  · rw [Fin.range_cons, Set.insert_eq, adjoin_union, ← sup_assoc, ← hsup, hβ]

theorem fl_main {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∃ n, finrank F E = p ^ n ∧ ∃ α : Fin n → E, adjoin F (Set.range α) = ⊤ := by
  obtain ⟨n, hn, α, hα⟩ := fl_greedy p h _ ⊥ rfl
  refine ⟨n, ?_, α, ?_⟩
  · rw [← hn, relfinrank_bot_left, finrank_top']
  · rwa [bot_sup_eq] at hα

def Pj (E : Type*) [Field E] (p : ℕ) [Fact p.Prime] [CharP E p] (j : ℕ) : Subfield E :=
  (iterateFrobenius E p j).fieldRange

section Frob

variable {E : Type*} [Field E] (p : ℕ) [hp : Fact p.Prime] [CharP E p]

theorem mem_Pj {j : ℕ} {y : E} : y ∈ Pj E p j ↔ ∃ x : E, x ^ p ^ j = y := by
  simp [Pj, RingHom.mem_fieldRange, iterateFrobenius_def]

theorem Pj_zero : Pj E p 0 = ⊤ :=
  eq_top_iff.2 fun y _ => (mem_Pj p).2 ⟨y, by simp⟩

theorem Pj_succ_le (j : ℕ) : Pj E p (j + 1) ≤ Pj E p j := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
  exact (mem_Pj p).2 ⟨x ^ p, by rw [← pow_mul, pow_succ']⟩

theorem comp_iterateFrobenius (j : ℕ) :
    (iterateFrobenius E p j).comp (iterateFrobenius E p 1) = iterateFrobenius E p (j + 1) := by
  ext x
  simp only [RingHom.comp_apply, iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]

theorem map_Pj_one (j : ℕ) : (Pj E p 1).map (iterateFrobenius E p j) = Pj E p (j + 1) := by
  rw [Pj, RingHom.map_fieldRange, comp_iterateFrobenius, Pj]

theorem map_top_Pj (j : ℕ) : (⊤ : Subfield E).map (iterateFrobenius E p j) = Pj E p j :=
  (RingHom.fieldRange_eq_map _).symm

theorem relfinrank_Pj_succ (j : ℕ) :
    (Pj E p (j + 1)).relfinrank (Pj E p j) = (Pj E p 1).relfinrank ⊤ := by
  rw [← map_Pj_one p j, ← map_top_Pj p j, Subfield.relfinrank_map_map]

theorem relfinrank_Pj (j : ℕ) :
    (Pj E p j).relfinrank ⊤ = ((Pj E p 1).relfinrank ⊤) ^ j := by
  induction j with
  | zero => rw [pow_zero, Subfield.relfinrank_eq_one_iff, Pj_zero]
  | succ j ih =>
    rw [← Subfield.relfinrank_mul_relfinrank (Pj_succ_le p j) le_top, relfinrank_Pj_succ, ih,
      pow_succ']

theorem closure_Pj_eq_top {S : Set E} (hS : Subfield.closure ((Pj E p 1 : Set E) ∪ S) = ⊤)
    (j : ℕ) : Subfield.closure ((Pj E p j : Set E) ∪ S) = ⊤ := by
  have key : ∀ i, Pj E p i ≤ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S) := by
    intro i
    rw [← map_top_Pj p i, ← hS, Subfield.map_le_iff_le_comap, Subfield.closure_le]
    rintro y (hy | hy)
    · change y ∈ Pj E p 1 at hy
      obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
      rw [SetLike.mem_coe, Subfield.mem_comap]
      apply Subfield.subset_closure
      left
      exact (mem_Pj p).2 ⟨x, by rw [iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]⟩
    · rw [SetLike.mem_coe, Subfield.mem_comap, iterateFrobenius_def]
      exact pow_mem (Subfield.subset_closure (Set.mem_union_right _ hy) :
        y ∈ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S)) _
  induction j with
  | zero =>
    rw [Pj_zero]
    exact eq_top_iff.2 fun y _ => Subfield.subset_closure (Or.inl (Subfield.mem_top y))
  | succ j ih =>
    refine eq_top_iff.2 (ih ▸ Subfield.closure_le.2 (Set.union_subset (key j) ?_))
    exact fun y hy => Subfield.subset_closure (Or.inr hy)

theorem fl_frob (c : ℕ) (hc : 0 < c) (hfin : (Pj E p c).relfinrank ⊤ ≠ 0) :
    ∃ n, (Pj E p c).relfinrank ⊤ = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ := by
  have h1 : (Pj E p 1).relfinrank ⊤ ≠ 0 := by
    intro h0
    apply hfin
    rw [relfinrank_Pj, h0, zero_pow hc.ne']
  haveI : FiniteDimensional (Pj E p 1) E :=
    Module.finite_of_finrank_pos (by rw [← Subfield.relfinrank_top_right]; exact Nat.pos_of_ne_zero h1)
  obtain ⟨n, hn, α, hα⟩ := fl_main (F := Pj E p 1) (E := E) p
    (fun x => ⟨⟨x ^ p, (mem_Pj p).2 ⟨x, by rw [pow_one]⟩⟩, rfl⟩)
  refine ⟨n, ?_, α, closure_Pj_eq_top p ?_ c⟩
  · rw [relfinrank_Pj, Subfield.relfinrank_top_right, hn, ← pow_mul, ← pow_mul, mul_comm]
  · have := congrArg IntermediateField.toSubfield hα
    rw [adjoin_toSubfield, top_toSubfield] at this
    have hr : Set.range (algebraMap (Pj E p 1) E) = (Pj E p 1 : Set E) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact z.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    rwa [hr] at this

end Frob

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.RqLift
section
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

def Iq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Ideal A[X] :=
  Ideal.span {χ.map (algebraMap k A)} ⊔
    Ideal.span {y | ∃ r ∈ (Ideal.span {χ.map (algebraMap k A)}).radical, y = r ^ q}

abbrev Rq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Type _ := A[X] ⧸ Iq A χ q

theorem rq_fin [FiniteDimensional k A] (χ : k[X]) (hχ : χ.Monic) (q : ℕ) :
    FiniteDimensional k (Rq A χ q) := by
  classical
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have : Module.Finite A (A[X] ⧸ Ideal.span {χ.map (algebraMap k A)}) := (AdjoinRoot.powerBasis' hmon).finite
  have hle : Ideal.span {χ.map (algebraMap k A)} ≤ Iq A χ q := le_sup_left
  let φ := Ideal.Quotient.factorₐ A hle
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ P, rfl⟩
  have : Module.Finite A (Rq A χ q) := Module.Finite.of_surjective φ.toLinearMap hsurj
  exact Module.Finite.trans A (Rq A χ q)

theorem rq_nil (χ : k[X]) (q : ℕ) (r : Rq A χ q) (hr : IsNilpotent r) : r ^ q = 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨m, hm⟩ := hr
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [pow_zero]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, Ideal.zero_mem _, (pow_zero _).symm⟩)
  · have hle : Iq A χ q ≤ (Ideal.span {χ.map (algebraMap k A)}).radical := by
      refine sup_le Ideal.le_radical ?_
      rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      exact Ideal.pow_mem_of_mem _ hr q hq
    have hP : P ∈ (Ideal.span {χ.map (algebraMap k A)}).radical :=
      (Ideal.radical_isRadical _) ⟨m, hle hm⟩
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, rfl⟩)
private theorem isPrincipalIdealRing_pi {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommRing (R i)]
    (hR : ∀ i, IsPrincipalIdealRing (R i)) : IsPrincipalIdealRing (∀ i, R i) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun J => ?_⟩
  have hsurj : ∀ i, Function.Surjective (Pi.evalRingHom R i) := fun i y => ⟨Pi.single i y, by simp⟩
  have hgen : ∀ i, ∃ a : R i, J.map (Pi.evalRingHom R i) = Ideal.span {a} := fun i => by
    obtain ⟨a, ha⟩ := (hR i).principal (J.map (Pi.evalRingHom R i))
    exact ⟨a, ha⟩
  choose g hg using hgen
  have hgJ : g ∈ J := by
    have hpre : ∀ i, ∃ h ∈ J, h i = g i := fun i => by
      have hm : g i ∈ J.map (Pi.evalRingHom R i) := by
        rw [hg i]
        exact Ideal.subset_span rfl
      obtain ⟨h, hh, he⟩ := (Ideal.mem_map_iff_of_surjective _ (hsurj i)).mp hm
      exact ⟨h, hh, he⟩
    choose h hh he using hpre
    have e : g = ∑ i, Pi.single i (1 : R i) * h i := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_mul, he]
      · intro i _ hij
        rw [Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [e]
    exact J.sum_mem (fun i _ => J.mul_mem_left _ (hh i))
  refine ⟨g, le_antisymm ?_ ?_⟩
  · intro x hx
    have hc : ∀ i, ∃ c : R i, c * g i = x i := fun i => by
      have hm : x i ∈ J.map (Pi.evalRingHom R i) := Ideal.mem_map_of_mem _ hx
      rw [hg i] at hm
      exact Ideal.mem_span_singleton'.mp hm
    choose c hc using hc
    exact Ideal.mem_span_singleton'.mpr ⟨c, funext hc⟩
  · exact (Ideal.span_le).mpr (Set.singleton_subset_iff.mpr hgJ)

theorem rq_pir [FiniteDimensional k A] [IsReduced A] (χ : k[X]) (q : ℕ) :
    IsPrincipalIdealRing (Rq A χ q) := by
  classical
  have hA : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hPI : IsPrincipalIdealRing ((I : MaximalSpectrum A) → (A ⧸ I.asIdeal)[X]) :=
    isPrincipalIdealRing_pi _ (fun I => by
      have := I.isMaximal
      letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field _
      exact EuclideanDomain.instIsPrincipalIdealRing)
  have hPI' : IsPrincipalIdealRing ((∀ I : MaximalSpectrum A, A ⧸ I.asIdeal)[X]) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.piEquiv (fun I : MaximalSpectrum A => A ⧸ I.asIdeal)).symm
      (Polynomial.piEquiv _).symm.surjective
  have hAX : IsPrincipalIdealRing A[X] :=
    IsPrincipalIdealRing.of_surjective (Polynomial.mapEquiv (IsArtinianRing.equivPi A).symm.toRingEquiv)
      (Polynomial.mapEquiv _).surjective
  exact IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk (Iq A χ q)) Ideal.Quotient.mk_surjective

theorem rq_rep (χ : k[X]) (hχ : χ.Monic) (q d : ℕ) (hd : χ.natDegree ≤ d) (r : Rq A χ q) :
    ∃ a : Fin d → A, r = Ideal.Quotient.mk _ (∑ l : Fin d, C (a l) * X ^ (l : ℕ)) := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, by congr 1; exact Subsingleton.elim _ _⟩
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have hmem : P - P %ₘ χ.map (algebraMap k A) ∈ Iq A χ q := by
    have e : P - P %ₘ χ.map (algebraMap k A) = χ.map (algebraMap k A) * (P /ₘ χ.map (algebraMap k A)) := by
      have h := modByMonic_add_div P (χ.map (algebraMap k A))
      linear_combination -h
    rw [e]
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hdeg : (P %ₘ χ.map (algebraMap k A)).degree < d :=
    calc (P %ₘ χ.map (algebraMap k A)).degree < (χ.map (algebraMap k A)).degree := degree_modByMonic_lt _ hmon
      _ ≤ (χ.map (algebraMap k A)).natDegree := degree_le_natDegree
      _ ≤ d := by exact_mod_cast natDegree_map_le.trans hd
  refine ⟨fun l => (P %ₘ χ.map (algebraMap k A)).coeff l, ?_⟩
  rw [Ideal.Quotient.eq.mpr hmem]
  congr 1
  rw [show (∑ l : Fin d, C ((P %ₘ χ.map (algebraMap k A)).coeff (l : ℕ)) * X ^ (l : ℕ)) =
      ∑ i ∈ Finset.range d, C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i from
    (Finset.sum_range (fun i => C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i)).symm]
  by_cases h0 : P %ₘ χ.map (algebraMap k A) = 0
  · rw [h0]
    simp
  · have h := as_sum_range' _ d ((natDegree_lt_iff_degree_lt h0).mpr hdeg)
    simp only [← C_mul_X_pow_eq_monomial] at h
    exact h

theorem rq_lift {B : Type*} [Ring B] [Algebra k B] (ι : A →ₐ[k] B) (x : B) (hc : ∀ a, Commute (ι a) x)
    (χ : k[X]) (hχ : aeval x χ = 0) (q : ℕ)
    (hq : ∀ P : A[X], IsNilpotent (P.eval₂ ι.toRingHom x) → (P.eval₂ ι.toRingHom x) ^ q = 0) :
    ∃ ρ : Rq A χ q →ₐ[k] B, ∀ P : A[X], ρ (Ideal.Quotient.mk _ P) = P.eval₂ ι.toRingHom x := by
  let f : A[X] →+* B := Polynomial.eval₂RingHom' ι.toRingHom x hc
  have hf : ∀ P : A[X], f P = P.eval₂ ι.toRingHom x := fun P => rfl
  have hχ0 : f (χ.map (algebraMap k A)) = 0 := by
    rw [hf, Polynomial.eval₂_map]
    have e : ι.toRingHom.comp (algebraMap k A) = algebraMap k B := by
      ext c
      exact ι.commutes c
    rw [e, ← Polynomial.aeval_def, hχ]
  have hspan : ∀ P ∈ Ideal.span {χ.map (algebraMap k A)}, f P = 0 := by
    intro P hP
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp hP
    rw [map_mul, hχ0, mul_zero]
  have hle : Iq A χ q ≤ RingHom.ker f := by
    unfold Iq
    apply sup_le
    · intro P hP
      exact (RingHom.mem_ker).mpr (hspan P hP)
    · rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨m, hm⟩ := hr
      have hnil : IsNilpotent (r.eval₂ ι.toRingHom x) := ⟨m, by rw [← hf, ← map_pow, hspan _ hm]⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, hf]
      exact hq r hnil
  let F : A[X] →ₐ[k] B :=
    { f with
      commutes' := fun c => by
        show Polynomial.eval₂ ι.toRingHom x (algebraMap k A[X] c) = algebraMap k B c
        rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
        exact ι.commutes c }
  exact ⟨Ideal.Quotient.liftₐ _ F (fun a ha => hle ha), fun P => rfl⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.SEps
section
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

theorem idem {k S : Type*} [Field k] [CommRing S] [Algebra k S] [FiniteDimensional k S] [IsReduced S] :
    ∃ (m : ℕ) (e : Fin m → S), (∀ t, IsIdempotentElem (e t)) ∧ ∑ t, e t = 1 ∧
      (∀ t t', t ≠ t' → e t * e t' = 0) ∧ ∀ t s, s * e t = 0 ∨ ∃ w, s * e t * w = e t := by
  classical
  have : IsArtinianRing S := IsArtinianRing.of_finite k S
  haveI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  set φ := IsArtinianRing.equivPi S with hφ
  let σ := (Fintype.equivFin (MaximalSpectrum S)).symm
  refine ⟨Fintype.card (MaximalSpectrum S), fun t => φ.symm (Pi.single (σ t) 1), ?_, ?_, ?_, ?_⟩
  · intro t
    show _ * _ = _
    rw [← map_mul]
    congr 1
    ext M
    by_cases h : M = σ t
    · subst h; simp
    · simp [h]
  · apply φ.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [AlgEquiv.apply_symm_apply]
    rw [Equiv.sum_comp σ (fun M => (Pi.single M 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal))]
    exact Finset.univ_sum_single (1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal)
  · intro t t' htt
    rw [← map_mul]
    have hne : σ t ≠ σ t' := fun h => htt (σ.injective h)
    have : (Pi.single (σ t) 1 * Pi.single (σ t') 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal) = 0 := by
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [hne.symm]
      · simp [h1]
    rw [this, map_zero]
  · intro t s
    have := (σ t).isMaximal
    by_cases ha : φ s (σ t) = 0
    · left
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [ha]
      · simp [h1]
    · right
      obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
      refine ⟨φ.symm (Pi.single (σ t) b), ?_⟩
      apply φ.injective
      rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp only [Pi.mul_apply, Pi.single_eq_same, mul_one]; exact hb
      · simp [h1]

theorem sEps {k R : Type*} [Field k] [CommRing R] [Algebra k R] [IsPrincipalIdealRing R] (S : Subalgebra k R)
    (hS : ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s)) (q : ℕ) (hnil : ∀ r : R, IsNilpotent r → r ^ q = 0) :
    ∃ ε : R, IsNilpotent ε ∧ ∀ r : R, ∃ σ : Fin q → R, (∀ l, σ l ∈ S) ∧ r = ∑ l, σ l * ε ^ (l : ℕ) := by
  classical
  set ε := Submodule.IsPrincipal.generator (nilradical R) with hε
  have hspan : Ideal.span {ε} = nilradical R := Ideal.span_singleton_generator _
  have hεn : IsNilpotent ε := mem_nilradical.mp (Submodule.IsPrincipal.generator_mem _)
  refine ⟨ε, hεn, fun r => ?_⟩
  have key : ∀ n : ℕ, ∃ σ : Fin n → R, (∀ l, σ l ∈ S) ∧
      ∃ u : R, r = ∑ l, σ l * ε ^ (l : ℕ) + ε ^ n * u := by
    intro n
    induction n with
    | zero => exact ⟨Fin.elim0, fun l => l.elim0, r, by simp⟩
    | succ n ih =>
      obtain ⟨σ, hσ, u, hu⟩ := ih
      obtain ⟨s, hs, hn⟩ := hS u
      have hm : u - s ∈ Ideal.span {ε} := by rw [hspan]; exact mem_nilradical.mpr hn
      obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Fin.snoc σ s, fun l => ?_, v, ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using hs
        · simpa using hσ i
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [hu]
        have : u = s + v * ε := by rw [hv]; ring
        rw [this]
        ring
  obtain ⟨σ, hσ, u, hu⟩ := key q
  refine ⟨σ, hσ, ?_⟩
  rw [hu, hnil ε hεn, zero_mul, add_zero]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

