module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RootsNear
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem rn_root {K : Type} [NormedField K] [IsUltrametricDist K] (p : K[X]) (hp : p.Monic)
    (hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1) (s : K) (hs : p.eval s = 0) : ‖s‖ < 1 := by
  by_contra hlt
  push_neg at hlt
  have sumlt : ∀ (t : Finset ℕ) (f : ℕ → K) (r : ℝ), 0 < r → (∀ i ∈ t, ‖f i‖ < r) → ‖∑ i ∈ t, f i‖ < r := by
    intro t f r hr
    induction t using Finset.induction_on with
    | empty => intro _; simpa using hr
    | insert j t hj ih =>
      intro hf
      rw [Finset.sum_insert hj]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hf j (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
  have hsum : p.eval s = s ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    conv_lhs => rw [hp.as_sum]
    simp [eval_finsetSum]
  have hpos : 0 < ‖s‖ := lt_of_lt_of_le one_pos hlt
  have hlt2 : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i‖ < ‖s‖ ^ p.natDegree := by
    apply sumlt _ _ _ (pow_pos hpos _)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖p.coeff i‖ * ‖s‖ ^ i < 1 * ‖s‖ ^ i :=
          mul_lt_mul_of_pos_right (hc i hi) (pow_pos hpos _)
      _ = ‖s‖ ^ i := one_mul _
      _ ≤ ‖s‖ ^ p.natDegree := pow_le_pow_right₀ hlt hi.le
  have heq : s ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    rw [hs] at hsum
    exact eq_neg_of_add_eq_zero_left hsum.symm
  have h3 := congrArg norm heq
  rw [norm_neg, norm_pow] at h3
  rw [h3] at hlt2
  exact lt_irrefl _ hlt2

theorem UpperTheory.V.Ws.Eb.rootsNear :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.B →ₐ[c.O] PadicAlgCl l) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)), B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) →
        ∀ g (a : c.O), (∀ i, residue c.O a = r.chib i g) → ∀ t ∈ (W.mat ρ g).charpoly.roots, ‖t - (a : PadicAlgCl l)‖ < 1 := by
  intro l _ F c n r B x ρ hD g a ha t ht
  have hsing : ∀ {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A'),
      MonoidAlgebra.mapRingHom F.G₀ f (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    intro A A' _ _ f
    simp [MonoidAlgebra.mapRingHom]
  set Q := B.u.D.chi (MonoidAlgebra.single g 1) with hQ
  have hx : (W.mat ρ g).charpoly = Q.map (x : B.B →+* PadicAlgCl l) := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* PadicAlgCl l)).1 (MonoidAlgebra.single g 1)
    rw [hsing, hD, (AlgebraTools.Det.repApi (W.mat ρ)).2.1] at h1
    exact h1
  have hred : Q.map (res c.O B.B : B.B →+* ResidueField c.O) = (X - C (residue c.O a)) ^ n := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (res c.O B.B : B.B →+* ResidueField c.O)).1 (MonoidAlgebra.single g 1)
    rw [hsing, B.u.red, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1] at h1
    rw [← h1]
    show (Matrix.diagonal _).charpoly = _
    rw [Matrix.charpoly_diagonal]
    simp [← ha]
  set Q' := Q.comp (X + C (algebraMap c.O B.B a)) with hQ'
  set p := (W.mat ρ g).charpoly.comp (X + C (a : PadicAlgCl l)) with hp
  have hpQ : p = Q'.map (x : B.B →+* PadicAlgCl l) := by
    rw [hp, hQ', hx, Polynomial.map_comp]
    simp
  have hQm : ∀ i < n, Q'.coeff i ∈ maximalIdeal B.B := by
    intro i hi
    rw [← res_eq_zero_iff c.O B.B, ← RingHom.coe_coe (res c.O B.B), ← Polynomial.coeff_map, hQ',
      Polynomial.map_comp, hred]
    simp [ResidueField.algebraMap_eq, Polynomial.coeff_X_pow, hi.ne]
  obtain ⟨_, a0, ha1, _, hb⟩ := (coPt c B.B).1 x
  have hmon : p.Monic := (Matrix.charpoly_monic _).comp_X_add_C _
  have hdeg : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_X_add_C]
    simp
  have hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1 := by
    intro i hi
    rw [hdeg] at hi
    rw [hpQ, Polynomial.coeff_map]
    have := hb 1 _ (by rw [pow_one]; exact hQm i hi)
    rw [pow_one] at this
    exact this.trans_lt ha1
  have hroot : p.eval (t - (a : PadicAlgCl l)) = 0 := by
    rw [hp, Polynomial.eval_comp]
    simp only [eval_add, eval_X, eval_C, sub_add_cancel]
    exact (Polynomial.mem_roots'.mp ht).2
  exact rn_root p hmon hc _ hroot
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TrPlus
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem entry_eq {A : Type} [CommRing A] {n : ℕ} (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    X i j = (Matrix.single j i (1 : A) * X).trace := by
  rw [Matrix.trace_single_mul, one_smul]

theorem UpperTheory.V.Ws.Eb.trPlus :
    ∀ {A G : Type} [CommRing A] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) A), Full ρ →
        (∀ z : MonoidAlgebra A G, (∀ h : G, (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1 * z) = 0) → W.GDet.repAlg (W.mat ρ) A z = 0) ∧
        ∀ [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] [IsTopologicalGroup G], (Continuous fun g => (W.mat ρ g).trace) → Continuous ρ := by
  intro A G _ _ n ρ hF
  have hs : ∀ h : G, W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single h 1) = W.mat ρ h := by
    intro h
    simp [W.GDet.repAlg]
  have hsp : ∀ X : Matrix (Fin n) (Fin n) A, X ∈ Submodule.span A (Set.range (W.mat ρ)) := by
    intro X
    unfold Full at hF
    rw [hF]
    exact Submodule.mem_top
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      ext i j
      exact i.elim0
    have hsingle : ∀ (B : Type) [CommRing B] [Algebra A B] (g : G) (r : B),
        W.GDet.repAlg (W.mat ρ) B (MonoidAlgebra.single g r) =
          r • (W.mat ρ g).map (algebraMap A B) := by
      intro B _ _ g r
      unfold W.GDet.repAlg
      rw [MonoidAlgebra.lift_single]
      rfl
    have hmap : ∀ y : MonoidAlgebra A G,
        W.GDet.repAlg (W.mat ρ) A[X] (MonoidAlgebra.mapRingHom G (algebraMap A A[X]) y) =
          (W.GDet.repAlg (W.mat ρ) A y).map (algebraMap A A[X]) := by
      intro y
      induction y using MonoidAlgebra.induction_on with
      | of g => simp [MonoidAlgebra.of_apply, hsingle]
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
        ext i j
        simp
      | smul r x hx =>
        have hr : r • x = MonoidAlgebra.single 1 r * x := by
          rw [Algebra.smul_def]
          rfl
        have hm : MonoidAlgebra.mapRingHom G (algebraMap A A[X]) (MonoidAlgebra.single 1 r)
            = MonoidAlgebra.single 1 (algebraMap A A[X] r) := by
          ext g
          simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
        rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, hsingle, hsingle, map_one]
        congr 1
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
    have htr : ∀ y : MonoidAlgebra A G,
        (W.GDet.ofRep (W.mat ρ)).tr y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
      intro y
      have hchi : (W.GDet.ofRep (W.mat ρ)).chi y = (W.GDet.repAlg (W.mat ρ) A y).charpoly := by
        unfold W.GDet.chi
        change (W.GDet.repAlg (W.mat ρ) A[X] _).det = _
        rw [← Polynomial.algebraMap_eq, map_sub, hsingle, hmap, map_one]
        rw [Matrix.charpoly]
        congr 1
        ext i j
        by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      unfold W.GDet.tr W.GDet.lam
      rw [hchi, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
      ring
    have key : ∀ X, (X * W.GDet.repAlg (W.mat ρ) A z).trace = 0 := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [← hs h, ← map_mul, ← htr]
        exact hz h
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, Matrix.trace_add, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
    ext i j
    exact (entry_eq _ i j).trans (key _)
  · intro _ _ _ _ hc
    have key : ∀ X, Continuous fun g => (X * W.mat ρ g).trace := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        simp_rw [← map_mul]
        exact hc.comp (continuous_const_mul h)
      | zero => simpa using continuous_const
      | add x y _ _ hx hy =>
        simp_rw [add_mul, Matrix.trace_add]
        exact hx.add hy
      | smul a x _ hx =>
        simp_rw [Matrix.smul_mul, Matrix.trace_smul]
        exact hx.const_smul a
    have hm : Continuous fun g => W.mat ρ g := by
      apply continuous_matrix
      intro i j
      exact (key (Matrix.single j i 1)).congr (fun g => (entry_eq _ i j).symm)
    rw [Units.continuous_iff]
    refine ⟨hm, ?_⟩
    refine (hm.comp continuous_inv).congr fun x => ?_
    show ((ρ x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = _
    rw [map_inv]
end

