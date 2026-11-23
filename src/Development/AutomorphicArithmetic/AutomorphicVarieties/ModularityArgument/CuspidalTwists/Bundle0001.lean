module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.ComplOfNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.FibTrdeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.GoodPairOfInjective
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

section Inj

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

private theorem adj_mp (f : R →+* R') (X : M4 R) : (adj X).map f = adj (X.map f) := by
  ext i j; simp [adj_apply]

private theorem conj_mp (f : R →+* R') (n m : M4 R) (i j : Fin 4) :
    (adj (n.map f) * m.map f * n.map f) i j = f ((adj n * m * n) i j) := by
  rw [← adj_mp, ← Matrix.map_mul, ← Matrix.map_mul]; rfl

private theorem gsp_of (f : R →+* R') (hf : Function.Injective f) (ν : R) (X : M4 R) (h : IsGSp (f ν) (X.map f)) :
    IsGSp ν X := by
  unfold IsGSp at *
  ext i j
  apply hf
  have := congrFun (congrFun h i) j
  rw [← adj_mp, ← Matrix.map_mul] at this
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at this ⊢
  rw [this]; split_ifs <;> simp

private theorem supp_of (f : R →+* R') (hf : Function.Injective f) (S : Finset (ℤ × ℤ)) (X : M4 R)
    (h : SuppM S (X.map f)) : SuppM S X := fun i j h1 h2 => (map_eq_zero_iff f hf).1 (h i j h1 h2)

private theorem cont_iff {Γ : Type} [TopologicalSpace Γ] (z : Γ → R) : AdicCont ⊥ z ↔ IsLocallyConstant z := by
  refine ⟨fun h => ?_, fun h N => h.comp (Ideal.Quotient.mk (⊥ ^ N))⟩
  refine IsLocallyConstant.desc z (Ideal.Quotient.mk (⊥ ^ 1)) (h 1) fun x y hxy => ?_
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot] at hxy
  exact sub_eq_zero.1 hxy

variable {ι Γ : Type} [Group Γ]

private theorem ent_of (f : R →+* R') (r : Γ →* M4 R) (w : ℤ × ℤ) (h : Ent (mapRep f r) w) : Ent r w := by
  obtain ⟨g, i, j, h1, h2⟩ := h
  exact ⟨g, i, j, h1, fun h0 => h2 (by rw [mapRep_apply, h0, map_zero])⟩

private theorem map_map' (P : PD ι Γ R) (f : R →+* R') (g : R' →+* R'') : (P.map f).map g = P.map (g.comp f) := rfl

private theorem map_inj' (f : R →+* R') (hf : Function.Injective f) {P Q : PD ι Γ R} (h : P.map f = Q.map f) : P = Q := by
  ext g i j
  · exact hf (congrArg (fun X : PD ι Γ R' => X.r g i j) h)
  · exact hf (congrArg (fun X : PD ι Γ R' => X.n g i j) h)

private theorem psi_mp (f : R →+* R') (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) :=
  conj_mp f (P.n v) (P.r s) i i

private theorem desc_ex (f : R →+* R') (hf : Function.Injective f) (P : PD ι Γ R')
    (h1 : ∀ g i j, P.r g i j ∈ f.range) (h2 : ∀ v i j, P.n v i j ∈ f.range) : ∃ Q : PD ι Γ R, Q.map f = P := by
  choose r hr using h1
  choose n hn using h2
  have e : ∀ g, (Matrix.of (r g)).map f = P.r g := fun g => by ext i j; exact hr g i j
  have hi : Function.Injective fun X : M4 R => X.map f := Matrix.map_injective hf
  refine ⟨⟨⟨⟨fun g => Matrix.of (r g), hi ?_⟩, fun a b => hi ?_⟩, fun v => Matrix.of (n v)⟩, ?_⟩
  · simp only [e, map_one]
    exact (Matrix.map_one f (map_zero f) (map_one f)).symm
  · simp only [e, map_mul, Matrix.map_mul]
  · ext g i j
    · exact hr g i j
    · exact hn g i j

variable {O : Type} [CommRing O] (Φ : Fr O Γ) (a : O →+* R)

private theorem inV_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Fr.InV (P.map f)) : Fr.InV P :=
  ⟨fun g => supp_of f hf _ _ (h.1 g), fun v => ⟨supp_of f hf _ _ (h.2 v).1, fun h0 => (h.2 v).2 (by
    show f (P.n v 2 0) = 0
    rw [h0, map_zero])⟩⟩

private theorem good_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Φ.Good (f.comp a) (P.map f)) :
    Φ.Good a P := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact .inl ⟨ent_of f _ _ h1, h2.imp (ent_of f _ _) (ent_of f _ _)⟩
  · exact .inr (.inl ⟨ent_of f _ _ h1, ent_of f _ _ h2⟩)
  · exact .inr (.inr (.inl ⟨inV_of Φ f hf P h1, ent_of f _ _ h2⟩))
  · refine .inr (.inr (.inr ⟨inV_of Φ f hf P h1, ent_of f _ _ h2, ent_of f _ _ h3, fun v => ?_⟩))
    obtain ⟨s, hs, h5⟩ := h4 v
    exact ⟨s, hs, fun h0 => h5 (by rw [RingHom.comp_apply, h0, map_one])⟩

private theorem inA_of (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : InA (P.map f)) : InA P :=
  ⟨fun g => supp_of f hf _ _ (h.1 g), fun v h0 => h.2 v (by
    show f (P.n v 1 0) = 0
    rw [h0, map_zero])⟩

private theorem good_pair_of_injective (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R) (h : Good4 Φ (f.comp a) (P.map f)) :
    Good4 Φ a P := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact .inl (good_of Φ a f hf P h)
  · exact .inr (.inl ⟨inA_of Φ f hf P h1, ent_of f _ _ h2⟩)
  · exact .inr (.inr ⟨inA_of Φ f hf P h1, ent_of f _ _ h2, ent_of f _ _ h3⟩)

private theorem isRes_of [TopologicalSpace Γ] (f : R →+* R') (hf : Function.Injective f) (P : PD Φ.ι Γ R)
    (h : Φ.IsRes (f.comp a) (P.map f)) : Φ.IsRes a P := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3⟩, c1⟩ := h
  refine ⟨⟨fun g => gsp_of f hf _ _ (a1 g), fun g hg => Matrix.map_injective hf ?_, fun i j hij => ?_,
    fun v => ⟨gsp_of f hf _ _ (by rw [map_one]; exact (a4 v).1), fun i => hf ?_, fun i j hij => ?_⟩,
    fun v s hs i j hij => ?_, fun v s hs i => hf ?_⟩, ⟨fun g i => hf (b1 g i), fun v s hs i => hf ?_, ?_⟩, fun i j => ?_⟩
  · exact (a2 g hg).trans (Matrix.map_one f (map_zero f) (map_one f)).symm
  · exact (map_eq_zero_iff f hf).1 (a3 hij)
  · rw [map_one]; exact (a4 v).2.1 i
  · exact (map_eq_zero_iff f hf).1 ((a4 v).2.2 i j hij)
  · exact (map_eq_zero_iff f hf).1 ((conj_mp f _ _ i j).symm.trans (a5 v s hs i j hij))
  · rw [map_one, ← psi_mp]; exact a6 v s hs i
  · rw [← psi_mp]; exact b2 v s hs i
  · exact b3.imp (fun h => ⟨fun g => supp_of f hf _ _ (h.1 g), fun v => supp_of f hf _ _ (h.2 v)⟩)
      fun h g => supp_of f hf _ _ (h g)
  · exact (cont_iff _).2 (IsLocallyConstant.desc _ f ((cont_iff _).1 (c1 i j)) hf)

end Inj

section Ev

variable {l : ℕ} [Fact l.Prime]

private def Ev (p : Coef l → Prop) : Prop := ∃ c₁ : Coef l, ∀ c' : Coef l, c₁.O ≤ c'.O → p c'

private theorem ev_and {p q : Coef l → Prop} (hp : Ev p) (hq : Ev q) : Ev fun c => p c ∧ q c := by
  obtain ⟨c₁, h₁⟩ := hp
  obtain ⟨c₂, h₂⟩ := hq
  obtain ⟨c₃, k₁, k₂⟩ := (coefSup l).1 c₁ c₂
  exact ⟨c₃, fun c' h => ⟨h₁ c' (k₁.trans h), h₂ c' (k₂.trans h)⟩⟩

private theorem ev_mono {p q : Coef l → Prop} (hp : Ev p) (h : ∀ c, p c → q c) : Ev q := by
  obtain ⟨c₁, h₁⟩ := hp
  exact ⟨c₁, fun c' h' => h _ (h₁ c' h')⟩

private theorem ev_fin (c : Coef l) {α : Type} {p : α → Coef l → Prop} (hp : ∀ x, Ev (p x)) (S : Set α) (hS : S.Finite) :
    Ev fun c => ∀ x ∈ S, p x c := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨c, fun _ _ x hx => hx.elim⟩
  | @insert y _ _ _ ih =>
    refine ev_mono (ev_and (hp y) ih) fun c' h x hx => ?_
    rcases hx with rfl | hx
    exacts [h.1, h.2 x hx]

private theorem ev_pd (c : Coef l) {R : Coef l → Type} [∀ c, CommRing (R c)] {R' : Type} [CommRing R'] (f : ∀ c, R c →+* R')
    (hf : ∀ c, Function.Injective (f c)) (hs : ∀ x, Ev fun c => x ∈ (f c).range) {ι Γ : Type} [Finite ι] [Group Γ]
    [TopologicalSpace Γ] [CompactSpace Γ] (P : PD ι Γ R') (hP : P.Cont ⊥) : Ev fun c => ∃ Q : PD ι Γ (R c), Q.map (f c) = P := by
  have h1 : (⋃ i, ⋃ j, Set.range fun g => P.r g i j).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => ((cont_iff _).1 (hP i j)).range_finite
  have h2 : (⋃ i, ⋃ j, Set.range fun v => P.n v i j).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_range _
  refine ev_mono (ev_and (ev_fin c hs _ h1) (ev_fin c hs _ h2)) fun c' h => desc_ex _ (hf c') P
    (fun g i j => h.1 _ ?_) fun g i j => h.2 _ ?_
  all_goals exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, g, rfl⟩⟩

variable (𝔞 : Amb l)

private theorem j_comp {c c' : Coef l} (h : c.O ≤ c'.O) : (𝔞.j c').comp ((residue c'.O).comp (inc h)) = 𝔞.red c := by
  ext x
  exact congrArg (residue 𝔞.V) (𝔞.compat c c' h x)

private theorem ev_k (x : 𝔞.k) : Ev fun c => x ∈ (𝔞.j c).range := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  obtain ⟨c, y, hy⟩ := 𝔞.alg x
  refine ⟨c, fun c' h => ⟨residue c'.O (inc h y), ?_⟩⟩
  refine (RingHom.congr_fun (j_comp 𝔞 h) y).trans ?_
  exact (Ideal.Quotient.eq.2 hy).symm

private theorem ev_poly (c : Coef l) (x : 𝔞.k[X]) : Ev fun c => x ∈ (mapRingHom (𝔞.j c)).range := by
  refine ev_mono (ev_fin c (ev_k 𝔞) _ x.coeffs.finite_toSet) fun c' h => ?_
  rw [Polynomial.mem_map_range]
  intro n
  by_cases h0 : x.coeff n = 0
  · rw [h0]; exact zero_mem _
  · exact h _ (Polynomial.coeff_mem_coeffs h0)

end Ev

theorem UpperTheory.V.Cu.chainDesc4 : ChainDesc4 := by
  intro l _ 𝔞 c Γ _ _ _ Φ s t hs ⟨hg, hch⟩
  have key : Ev fun c' : Coef l => ∀ (h : c.O ≤ c'.O) (s' : PD Φ.ι Γ (ResidueField c'.O)), s'.map (𝔞.j c') = s →
      ∃ t' : PD Φ.ι Γ (ResidueField c'.O), t'.map (𝔞.j c') = t ∧ Relation.ReflTransGen
        (fun x y => Good4 Φ ((residue c'.O).comp (inc h)) y ∧ Φ.Linked ((residue c'.O).comp (inc h)) x y) s' t' := by
    induction hch with
    | refl => exact ⟨c, fun c' _ h s' e => ⟨s', e, .refl⟩⟩
    | tail _ hl ih =>
      obtain ⟨hy, P, hP, rfl, rfl⟩ := hl
      have hi : ∀ c' : Coef l, Function.Injective (mapRingHom (𝔞.j c')) := fun c' =>
        Polynomial.map_injective _ (𝔞.j c').injective
      refine ev_mono (ev_and ih (ev_pd c (R := fun c' => (ResidueField c'.O)[X]) (fun c' => mapRingHom (𝔞.j c')) hi
        (ev_poly 𝔞 c) P hP.cont)) ?_
      rintro c' ⟨h1, Q, rfl⟩ h s' e
      obtain ⟨b, hb, hc⟩ := h1 h s' e
      have e0 : (𝔞.j c').comp (evalRingHom 0) = (evalRingHom 0).comp (mapRingHom (𝔞.j c')) := by
        ext <;> simp
      have e1 : (𝔞.j c').comp (evalRingHom 1) = (evalRingHom 1).comp (mapRingHom (𝔞.j c')) := by
        ext <;> simp
      have f1 : (Q.map (evalRingHom 1)).map (𝔞.j c') = (Q.map (mapRingHom (𝔞.j c'))).map (evalRingHom 1) := by
        rw [map_map', map_map', e1]
      refine ⟨Q.map (evalRingHom 1), f1, hc.tail ⟨good_pair_of_injective Φ _ (𝔞.j c') (𝔞.j c').injective _ ?_, Q,
        isRes_of Φ _ _ (hi c') Q ?_, map_inj' (𝔞.j c') (𝔞.j c').injective ?_, rfl⟩⟩
      · rw [j_comp, f1]; exact hy
      · rw [← RingHom.comp_assoc, mapRingHom_comp_C, RingHom.comp_assoc, j_comp]; exact hP
      · rw [hb, map_map', map_map', e0]
  obtain ⟨c₁, h₁⟩ := ev_and key (ev_pd c (R := fun c' => ResidueField c'.O) 𝔞.j (fun c' => (𝔞.j c').injective) (ev_k 𝔞) s hs.cont)
  refine ⟨c₁, fun c' h h' => ?_⟩
  obtain ⟨k1, s', e⟩ := h₁ c' h'
  obtain ⟨t', e', hc⟩ := k1 h s' e
  refine ⟨s', t', e, e', isRes_of Φ _ (𝔞.j c') (𝔞.j c').injective _ ?_, good_pair_of_injective Φ _ (𝔞.j c') (𝔞.j c').injective _ ?_, hc⟩
  · rw [j_comp, e]; exact hs
  · rw [j_comp, e]; exact hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PFibY
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

private theorem UpperTheory.V.Cu.FiberPointBoundedGenerators.fib_low {K : Type} [Field K] (E : Subfield K) (n : M4 K) (h : IsLow n) (h10 : n 1 0 ∈ E)
    (h20 : n 2 0 ∈ E) (h30 : n 3 0 ∈ E) (h21 : n 2 1 ∈ E) (i j : Fin 4) : n i j ∈ E := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := congrFun (congrFun h1 1) 0
  have e2 := congrFun (congrFun h1 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, h2, h3] at e1 e2
  have h32 : n 3 2 ∈ E := by
    have : n 3 2 = -n 1 0 := by linear_combination e1
    rw [this]; exact neg_mem h10
  have h31 : n 3 1 ∈ E := by
    have : n 3 1 = n 2 0 - n 2 1 * n 1 0 := by linear_combination -e2
    rw [this]; exact sub_mem h20 (mul_mem h21 h10)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [h3 i j hij]; exact zero_mem _
  · rw [h2]; exact one_mem _
  · fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)

private theorem UpperTheory.V.Cu.FiberPointBoundedGenerators.fib_gen {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) {K : Type} [Field K] (y : X.A →+* K)
    (hne : ∀ i j, i ≠ j → y (X.P.r Φ.g0 i i) ≠ y (X.P.r Φ.g0 j j)) (hTor : TorusY)
    (hS : Supp yY (mapRep y X.P.r)) (e1 : Ent (mapRep y X.P.r) wBe) (e2 : Ent (mapRep y X.P.r) (-wBe))
    (e3 : Ent (mapRep y X.P.r) wTh) (e4 : Ent (mapRep y X.P.r) (-wTh)) :
    ∃ T : Finset K, T.card ≤ 2 + 4 * Nat.card Φ.ι ∧ ∀ E : Subfield K, (∀ b, y (algebraMap X.B X.A b) ∈ E) → (∀ t ∈ T, t ∈ E) →
      (∀ (p : K[X]) (x : K), p.Monic → (∀ n, p.coeff n ∈ E) → p.IsRoot x → x ∈ E) → ∀ z, y z ∈ E := by
  classical
  haveI := Fintype.ofFinite Φ.ι
  have hp := X.pair.map y
  obtain ⟨s, t, hst⟩ := hTor (mapRep y X.P.r) Φ.g0 hp.nrm hne hS e1 e2 e3 e4
  let u : Φ.ι × Fin 4 → K := fun x => y (X.P.n x.1 (![1, 2, 3, 2] x.2) (![0, 0, 0, 1] x.2))
  refine ⟨{s, t} ∪ Finset.univ.image u, ?_, fun E hB hT hE z => ?_⟩
  · refine (Finset.card_union_le _ _).trans (add_le_add Finset.card_le_two (Finset.card_image_le.trans ?_))
    simp [mul_comm]
  · have hc : ∀ g n, (mapRep y X.P.r g).charpoly.coeff n ∈ E := fun g n => by
      have : (mapRep y X.P.r g).charpoly.coeff n = y (algebraMap X.B X.A ((X.cp g).coeff n)) := by
        show ((X.P.r g).map y).charpoly.coeff n = _
        rw [Matrix.charpoly_map, ← X.cp_map, coeff_map, coeff_map]
      rw [this]; exact hB _
    have hr := hst E (hT _ (by simp)) (hT _ (by simp))
      (fun g => by rw [Matrix.trace_eq_neg_charpoly_coeff]; exact neg_mem (hc _ _))
      (fun i => hE _ _ (Matrix.charpoly_monic _) (hc Φ.g0) (by
        have hd : mapRep y X.P.r Φ.g0 = Matrix.diagonal fun i => mapRep y X.P.r Φ.g0 i i := hp.nrm.diagonal_diag.symm
        rw [IsRoot, hd, Matrix.charpoly_diagonal, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)))
    have hu : ∀ x, u x ∈ E := fun x => hT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
    have hn := fun v => FiberPointBoundedGenerators.fib_low E _ (hp.low v) (hu (v, 0)) (hu (v, 1)) (hu (v, 2)) (hu (v, 3))
    have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
    rw [← X.gen] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact hr _ _ _
      · exact hn _ _ _
    | algebraMap b => exact hB b
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem UpperTheory.V.Cu.fibY_of : TorusY → FibY := by
  intro hTor
  unfold FibY
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hΦ X c hc R _ _ _ f hf q hq r hr hS e1 e2 e3 e4
  subst hr
  haveI := X.noeth
  haveI := X.ft
  letI : Algebra X.A R := (f : X.A →+* R).toAlgebra
  haveI : IsScalarTower Λ X.A R := IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  have hff : IsScalarTower.toAlgHom Λ X.A R = f := AlgHom.ext fun _ => rfl
  obtain ⟨hx, hR⟩ := fibCpl (Λ := Λ) (A := X.A) (R := R) (fun R' _ _ _ g hg => by
    rw [hff] at hg ⊢
    obtain ⟨h, hh, hu⟩ := hf.2 R' (X.P.map (g : X.A →+* R')) ⟨X.pair_map g, X.cont_map g, by
      rw [← hf.1.red]
      exact congrArg (fun φ : X.A →ₐ[Λ] ResidueField Λ => X.P.map (φ : X.A →+* ResidueField Λ)) hg⟩
    exact ⟨h, X.hom_ext _ _ hh, fun h' e => hu h' (by rw [← e]; rfl)⟩)
  have hxB : ((maximalIdeal R).comap (algebraMap X.A R)).comap (algebraMap X.B X.A) = maximalIdeal X.B := by
    ext b
    show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R ↔ _
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
  haveI hη : (q.comap (algebraMap X.A R)).IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨t, h1, h2⟩ := UpperTheory.V.CA.c3b Λ _ (UpperTheory.V.CA.IsCL.of_isCO Λ X.B) hxB (q.comap (algebraMap X.A R))
    (Ideal.comap_mono (le_maximalIdeal hq.ne_top))
  obtain ⟨T, hT, hE⟩ := FiberPointBoundedGenerators.fib_gen X _ (fun i j hij e => by
    have e1 : f (X.P.r Φ.g0 i i) - f (X.P.r Φ.g0 j j) ∈ q :=
      Ideal.Quotient.eq.1 (IsFractionRing.injective (R ⧸ q) (FractionRing (R ⧸ q)) e)
    have e2 := (res_eq_zero_iff Λ R _).2 (le_maximalIdeal hq.ne_top e1)
    have e3 : ∀ i, res Λ R (f (X.P.r Φ.g0 i i)) = (residue Λ).comp a (Φ.χ i Φ.g0) := fun i => by
      rw [← hc.res.diag, ← hf.1.red]; rfl
    rw [map_sub, e3, e3] at e2
    exact (hΦ.ok.dist i j hij).ne_zero e2) hTor hS e1 e2 e3 e4
  have h3 := fibTrdeg (D := X.B ⧸ (q.comap (algebraMap X.A R)).comap (algebraMap X.B X.A))
    ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.quotientMap q (algebraMap X.A R) le_rfl)) T
    (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective (R ⧸ q) _).comp Ideal.quotientMap_injective) Ideal.quotientMap_injective
    (fun E hB hT' hcl z => by
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact hE E (fun b => hB (Ideal.Quotient.mk _ b)) hT' hcl z)
  rw [h1] at h3
  have h4 : t ≤ 2 + 4 * Nat.card Φ.ι := le_trans (by exact_mod_cast h3) hT
  refine ((UpperTheory.V.CA.c3c _ hR).2 _ q le_rfl).trans ?_
  rw [h2]
  exact add_le_add le_rfl (by exact_mod_cast h4)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PRedA
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, h.cont.map _ fun y hy => ?_, ?_⟩
  · have h1 := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at h1
  · show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hy
  · rw [PD.map_map, ← h.red]
    congr 1
    exact RingHom.ext fun x => res_map f x

private theorem lc_dual {Γ k : Type} [TopologicalSpace Γ] [Field k] {f : Γ → DualNumber k}
    (h : AdicCont (maximalIdeal (DualNumber k)) f) : IsLocallyConstant f := by
  have hm : ∀ x : DualNumber k, x ∈ maximalIdeal (DualNumber k) → x.fst = 0 := fun x hx => by
    rwa [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not] at hx
  have h2 : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
    rw [sq, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_bot]
    ext <;> simp [hm x hx, hm y hy]
  refine IsLocallyConstant.desc f _ (h 2) fun x y e => ?_
  rw [Ideal.Quotient.eq, h2, Ideal.mem_bot, sub_eq_zero] at e
  exact e

private theorem hom_of_der {O A k : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [Algebra O k]
    (x : A →ₐ[O] k) (D : A →ₗ[O] k) (hD : D ∈ PtDer x k) :
    ∃ y : A →ₐ[O] DualNumber k, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have h1 : D 1 = 0 := by
    have := hD' 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun f => (x f, D f)
            map_one' := TrivSqZeroExt.ext (map_one x) h1
            map_mul' := fun f g => TrivSqZeroExt.ext (map_mul x f g) ?_
            map_zero' := TrivSqZeroExt.ext (map_zero x) (map_zero D)
            map_add' := fun f g => TrivSqZeroExt.ext (map_add x f g) (map_add D f g)
            commutes' := fun t => TrivSqZeroExt.ext (x.commutes t) ?_ }, fun f => ⟨rfl, rfl⟩⟩
  · refine Eq.trans ?_ (DualNumber.snd_mul ((x f, D f) : DualNumber k) (x g, D g)).symm
    show D (f * g) = x f * D g + D f * x g
    rw [hD', smul_eq_mul, smul_eq_mul, mul_comm (D f)]
  · show D (algebraMap O A t) = 0
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

theorem UpperTheory.V.Cu.redA_of : RedTanA → RedA := by
  intro htan
  unfold RedTanA at htan
  unfold RedA
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd d C hB c hc hA hent R _ _ _ P hP S hS hY
  set I := redIdeal S P.r with hI
  by_cases htop : I = ⊤
  · haveI : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.2 htop
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  let p : R →ₐ[Λ] R ⧸ I := Ideal.Quotient.mkₐ Λ I
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective Λ I
  haveI : IsCO Λ (R ⧸ I) := co_quot Λ R (R ⧸ I) p hp
  haveI : IsCO Λ (DualNumber (ResidueField Λ)) := (co_res Λ).2
  have hr : ∀ g i j, res Λ R (P.r g i j) = c.r g i j := fun g i j =>
    congrArg (fun Q : PD Φ.ι Γ (ResidueField Λ) => Q.r g i j) hP.1.red
  have hn : ∀ v i j, res Λ R (P.n v i j) = c.n v i j := fun v i j =>
    congrArg (fun Q : PD Φ.ι Γ (ResidueField Λ) => Q.n v i j) hP.1.red
  have hz : ∀ g i j, i ≠ j → wt i j ∉ S → p (P.r g i j) = 0 := fun g i j h1 h2 =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨g, i, j, h1, h2, rfl⟩)
  have hsupp : Supp S c.r := fun g i j h1 h2 => by rw [← hr, ← res_map p, hz g i j h1 h2, map_zero]
  refine redDim (Λ := Λ) (R ⧸ I) (d + 20 * C) ?_
  let L : PtDer (res Λ (R ⧸ I)) (ResidueField Λ) →ₗ[ResidueField Λ]
      (Γ → M4 (ResidueField Λ)) × (Φ.ι → M4 (ResidueField Λ)) :=
    { toFun := fun D => (fun g => (P.r g).map (fun x => D.1 (p x)) * c.r g⁻¹,
        fun v => (P.n v).map (fun x => D.1 (p x)) * adj (c.n v))
      map_add' := fun D D' => Prod.ext
        (_root_.funext fun g => add_mul ((P.r g).map fun x => D.1 (p x)) ((P.r g).map fun x => D'.1 (p x)) _)
        (_root_.funext fun v => add_mul ((P.n v).map fun x => D.1 (p x)) ((P.n v).map fun x => D'.1 (p x)) _)
      map_smul' := fun t D => Prod.ext
        (_root_.funext fun g => Matrix.smul_mul t ((P.r g).map fun x => D.1 (p x)) _)
        (_root_.funext fun v => Matrix.smul_mul t ((P.n v).map fun x => D.1 (p x)) _) }
  have hy : ∀ D : PtDer (res Λ (R ⧸ I)) (ResidueField Λ), ∃ y : (R ⧸ I) →ₐ[Λ] DualNumber (ResidueField Λ),
      ∀ f, (y f).fst = res Λ (R ⧸ I) f ∧ (y f).snd = D.1 f := fun D =>
    hom_of_der _ D.1 D.2
  have hmem : ∀ D, L D ∈ Submodule.span (ResidueField Λ) (Φ.Tan S c) := fun D => by
    obtain ⟨y, hy⟩ := hy D
    have hl := lifts_map hP.1 (y.comp p)
    have h := redDual Φ _ S c _ (fun _ => rfl) hl.pair (fun i j => lc_dual (hl.cont i j))
      (fun g i j => ((hy _).1.trans (res_map p _)).trans (hr g i j))
      (fun v i j => ((hy _).1.trans (res_map p _)).trans (hn v i j))
      (fun g i j h1 h2 => by
        show y (p (P.r g i j)) = 0
        rw [hz g i j h1 h2, map_zero])
    refine Submodule.subset_span ?_
    convert h using 1
    refine Prod.ext (_root_.funext fun g => ?_) (_root_.funext fun v => ?_)
    · exact congrArg (· * c.r g⁻¹) (Matrix.ext fun i j => (hy _).2.symm)
    · exact congrArg (· * adj (c.n v)) (Matrix.ext fun i j => (hy _).2.symm)
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro D hD
    obtain ⟨y, h1⟩ := hy D
    obtain ⟨y0, h0⟩ := hy 0
    have e1 : ∀ g i j, D.1 (p (P.r g i j)) = 0 := fun g i j => by
      have e : (P.r g).map (fun x => D.1 (p x)) * c.r g⁻¹ = 0 := congrFun (congrArg Prod.fst hD) g
      have e' := congrArg (· * c.r g) e
      simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one, zero_mul] at e'
      exact congrFun (congrFun e' i) j
    have e2 : ∀ v i j, D.1 (p (P.n v i j)) = 0 := fun v i j => by
      have e : (P.n v).map (fun x => D.1 (p x)) * adj (c.n v) = 0 := congrFun (congrArg Prod.snd hD) v
      have e' := congrArg (· * c.n v) e
      have hu : adj (c.n v) * c.n v = 1 := (hc.pair.low v).1.trans (one_smul _ _)
      simp only [mul_assoc, hu, mul_one, zero_mul] at e'
      exact congrFun (congrFun e' i) j
    have key : ∀ x, D.1 x = 0 → y x = y0 x := fun x hx =>
      TrivSqZeroExt.ext ((h1 x).1.trans (h0 x).1.symm) (((h1 x).2.trans hx).trans (h0 x).2.symm)
    have e : y.comp p = y0.comp p := by
      refine (hP.2 _ _ (lifts_map hP.1 (y0.comp p))).unique ?_ rfl
      exact PD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => key _ (e1 g i j))
        (_root_.funext fun v => Matrix.ext fun i j => key _ (e2 v i j))
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := hp x
    have e3 : y (p x) = y0 (p x) := AlgHom.congr_fun e x
    rw [← (h1 _).2, e3, (h0 _).2]
  have hle := LinearMap.rank_le_of_injective (L.codRestrict _ hmem) fun x x' e => hinj (congrArg Subtype.val e)
  have hmemS : ∀ w : ℤ × ℤ, w ≠ (0, 0) → Ent c.r w → w ∈ S := by
    rintro w hw ⟨g, i, j, hij, hne⟩
    by_contra hS'
    have hij' : i ≠ j := by
      rintro rfl
      apply hw
      rw [← hij]
      simp [wt]
    exact hne (hsupp g i j hij' (by rw [hij]; exact hS'))
  have hcond : -wPs ∈ S ∨ (-wBe ∈ S ∧ -wTh ∈ S ∧ S ≠ yY) := by
    rcases hent with h | ⟨h1, h2⟩
    · exact Or.inl (hmemS _ (by decide) h)
    · exact Or.inr ⟨hmemS _ (by decide) h1,
        hmemS _ (by decide) h2, hY⟩
  refine hle.trans ((htan Φ _ hstd.ok d C hB c hc hA S hS hcond hsupp).trans ?_)
  push_cast
  rfl
end

