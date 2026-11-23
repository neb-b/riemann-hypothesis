module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleLocallyHoldsOfPointwiseCoverOrAffineLocal
section
open CategoryTheory Limits AlgebraicGeometry Opposite UpperTheory.Et

private theorem UpperTheory.locally_of_etale_cover (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), Etale g ∧ x ∈ Set.range g ∧ P V g) :
    LocT Scheme.etaleTopology U P := by
  choose V g hg hx hP' using h
  refine ⟨Sieve.ofArrows V g, ?_, ?_⟩
  · exact Precoverage.generate_mem_toGrothendieck
      ((Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ⟨x, hx x⟩, hg⟩)
  · rintro W f ⟨Y, k, _, ⟨i⟩, rfl⟩
    exact hP _ _ _ _ (hP' i)

theorem UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local :
    ∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    ((∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), Etale g ∧ x ∈ Set.range g ∧ P V g) → LocT Scheme.etaleTopology U P) ∧
    ((∀ (A : CommRingCat.{0}) (g : Spec A ⟶ U), LocT Scheme.etaleTopology (Spec A) fun V k => P V (k ≫ g)) → LocT Scheme.etaleTopology U P) := by
  intro U P hP
  refine ⟨UpperTheory.locally_of_etale_cover U P hP, fun hA => ?_⟩
  obtain ⟨-, -, -, h4, h5, -⟩ := UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology
  apply h5
  apply UpperTheory.locally_of_etale_cover U _
  · intro V W g k hV
    simpa only [Category.assoc] using h4 V W k _ hV
  · intro x
    exact ⟨_, U.affineCover.f (U.affineCover.idx x), inferInstance,
      U.affineCover.covers x, hA _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCommonZeroOfJacobianIsUnitHenselian
section
noncomputable section
open IsLocalRing UpperTheory.Et

private theorem etale_away_jacobian (A : Type) [CommRing A] (n : ℕ)
    (F : Fin n → MvPolynomial (Fin n) A) :
    Algebra.Etale A (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det)) := by
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  let P1 := Algebra.PreSubmersivePresentation.naive (v := F) (id : Fin n → Fin n)
    Function.injective_id
  let P2 := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d
  have hJ : P1.jacobian = d := by
    rw [P1.jacobian_eq_jacobiMatrix_det]
    have hM : P1.jacobiMatrix = Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t) := by
      ext i j
      simp [P1]
    rw [hM, Algebra.Generators.algebraMap_apply]
    have hE : MvPolynomial.aeval P1.val = Ideal.Quotient.mkₐ A I :=
      MvPolynomial.algHom_ext fun i => by simp [P1, I, Algebra.Generators.naive]
    exact congrFun (congrArg DFunLike.coe hE) _
  let P : Algebra.SubmersivePresentation A (Localization.Away d) (Unit ⊕ Fin n) (Unit ⊕ Fin n) :=
    { P2.comp P1 with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian, hJ]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away d) :=
    P.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  infer_instance

theorem UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (n : ℕ) (F : Fin n → MvPolynomial (Fin n) A),
      (∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A) → IsUnit (Matrix.det (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)))) →
      ∃ x : Fin n → A, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ ∀ j, x j ∈ maximalIdeal A := by
  intro A _ _ n F hF hU
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  haveI := etale_away_jacobian A n F
  let ψ : MvPolynomial (Fin n) A →ₐ[A] ResidueField A :=
    (Algebra.ofId A (ResidueField A)).comp (MvPolynomial.aeval (0 : Fin n → A))
  have hψ : ∀ p, ψ p = residue A (MvPolynomial.eval 0 p) := fun p => by
    simp [ψ, MvPolynomial.coe_aeval_eq_eval, IsLocalRing.ResidueField.algebraMap_eq]
  have hI : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker ψ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hψ, residue_eq_zero_iff]
      exact hF i
    exact hle ha
  let π0 : (MvPolynomial (Fin n) A ⧸ I) →ₐ[A] ResidueField A := Ideal.Quotient.liftₐ I ψ hI
  have hπ0 : ∀ p, π0 (Ideal.Quotient.mk I p) = residue A (MvPolynomial.eval 0 p) := fun p => by
    rw [← hψ]
    rfl
  have hd : IsUnit (π0 d) := by
    rw [hπ0]
    have hdet : MvPolynomial.eval 0 (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det =
        (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
      rw [RingHom.map_det, ← Matrix.det_transpose]
      congr 1
    rw [hdet]
    exact hU.map (residue A)
  let π : Localization.Away d →ₐ[A] ResidueField A :=
    IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := π0) (by
      rintro ⟨y, k, rfl⟩
      simpa using hd.pow k)
  obtain ⟨σ, hσ⟩ := UpperTheory.exists_section_lift_of_etale_of_henselian A (Localization.Away d) π
  let φ : MvPolynomial (Fin n) A →ₐ[A] A :=
    (σ.comp (IsScalarTower.toAlgHom A _ (Localization.Away d))).comp (Ideal.Quotient.mkₐ A I)
  have hφ : ∀ p, φ p = MvPolynomial.eval (fun j => φ (MvPolynomial.X j)) p := by
    intro p
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact congrFun (congrArg DFunLike.coe
      (MvPolynomial.algHom_ext (fun j => by simp) : φ = MvPolynomial.aeval _)) p
  refine ⟨fun j => φ (MvPolynomial.X j), fun i => ?_, fun j => ?_⟩
  · rw [← hφ]
    have h0 : Ideal.Quotient.mk I (F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    simp [φ, h0]
  · rw [← residue_eq_zero_iff]
    show residue A (σ (algebraMap _ (Localization.Away d)
      (Ideal.Quotient.mk I (MvPolynomial.X j)))) = 0
    rw [hσ]
    simp [π, hπ0]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorOfRootSubsetProductEquation
section
noncomputable section
open Polynomial

private lemma exists_roots {A : Type} [CommRing A] [Nontrivial A] {g : A[X]} (hg : g.Monic) {N : ℕ}
    (hN : g.natDegree = N) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra A S), Function.Injective (algebraMap A S) ∧
      ∃ x : Fin N → S, g.map (algebraMap A S) = ∏ i, (X - C (x i)) := by
  induction N generalizing A with
  | zero =>
    refine ⟨A, inferInstance, Algebra.id A, Function.injective_id, Fin.elim0, ?_⟩
    have h1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hN
    simp [h1]
  | succ N ih =>
    have hinj : Function.Injective (AdjoinRoot.of g) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h
      exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hg (C_ne_zero.mpr h)
        (by rw [natDegree_C]; omega) (by rwa [AdjoinRoot.mk_C])
    haveI : Nontrivial (AdjoinRoot g) := hinj.nontrivial
    have hroot : (g.map (AdjoinRoot.of g)).IsRoot (AdjoinRoot.root g) := AdjoinRoot.isRoot_root g
    have hfac : (X - C (AdjoinRoot.root g)) * ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g)))
        = g.map (AdjoinRoot.of g) := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hqm : ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g))).Monic :=
      Monic.of_mul_monic_left (monic_X_sub_C _) (hfac ▸ hg.map _)
    have hqd : ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g))).natDegree = N := by
      have e1 := congrArg Polynomial.natDegree hfac
      rw [(monic_X_sub_C _).natDegree_mul hqm, natDegree_X_sub_C,
        natDegree_map_eq_of_injective hinj, hN] at e1
      omega
    obtain ⟨S, iS, aS, hSinj, x, hx⟩ := ih hqm hqd
    letI : Algebra A S := ((algebraMap (AdjoinRoot g) S).comp (AdjoinRoot.of g)).toAlgebra
    refine ⟨S, iS, this, hSinj.comp hinj, Fin.cons (algebraMap (AdjoinRoot g) S (AdjoinRoot.root g)) x, ?_⟩
    have e2 : g.map (algebraMap A S) = (g.map (AdjoinRoot.of g)).map (algebraMap (AdjoinRoot g) S) := by
      rw [Polynomial.map_map]
      rfl
    rw [e2, ← hfac, Polynomial.map_mul, hx, Fin.prod_univ_succ]
    simp

private lemma idem_mul {S ι : Type} [CommRing S] (Λ : Finset ι) (ε : ι → S) (a b : ι → S[X])
    (G : S[X]) (h1 : ∑ J ∈ Λ, ε J = 1) (h0 : ∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' → ε J * ε J' = 0)
    (hab : ∀ J ∈ Λ, a J * b J = G) :
    (∑ J ∈ Λ, C (ε J) * a J) * (∑ J ∈ Λ, C (ε J) * b J) = G := by
  have hsq : ∀ J ∈ Λ, ε J * ε J = ε J := by
    intro J hJ
    have e := congrArg (ε J * ·) h1
    simp only [mul_one, Finset.mul_sum] at e
    rwa [Finset.sum_eq_single J (fun J' hJ' hne => h0 J hJ J' hJ' (Ne.symm hne))
      (fun h => absurd hJ h)] at e
  rw [Finset.sum_mul_sum]
  calc ∑ J ∈ Λ, ∑ J' ∈ Λ, C (ε J) * a J * (C (ε J') * b J')
      = ∑ J ∈ Λ, C (ε J) * G := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [Finset.sum_eq_single J]
        · rw [← hab J hJ]
          calc C (ε J) * a J * (C (ε J) * b J) = C (ε J * ε J) * (a J * b J) := by
                rw [C_mul]
                ring
            _ = C (ε J) * (a J * b J) := by rw [hsq J hJ]
        · intro J' hJ' hne
          have e : C (ε J) * C (ε J') = 0 := by
            rw [← C_mul, h0 J hJ J' hJ' (Ne.symm hne), C_0]
          calc C (ε J) * a J * (C (ε J') * b J') = (C (ε J) * C (ε J')) * (a J * b J') := by ring
            _ = 0 := by rw [e, zero_mul]
        · intro h
          exact absurd hJ h
    _ = G := by rw [← Finset.sum_mul, ← map_sum, h1, C_1, one_mul]

private lemma weights {S ι : Type} [CommRing S] [DecidableEq ι] (Λ : Finset ι) (t : ι → S)
    (c c' : S) (hc : c' * c = 1) (h0 : ∏ J ∈ Λ, t J = 0)
    (h1 : ∑ J ∈ Λ, ∏ J' ∈ Λ.erase J, t J' = c) :
    (∑ J ∈ Λ, c' * ∏ J' ∈ Λ.erase J, t J' = 1) ∧
    (∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' →
      (c' * ∏ K ∈ Λ.erase J, t K) * (c' * ∏ K ∈ Λ.erase J', t K) = 0) ∧
    (∀ J ∈ Λ, (c' * ∏ K ∈ Λ.erase J, t K) * t J = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, h1, hc]
  · intro J hJ J' hJ' hne
    have hmem : J' ∈ Λ.erase J := Finset.mem_erase.mpr ⟨Ne.symm hne, hJ'⟩
    rw [← Finset.mul_prod_erase (Λ.erase J) t hmem]
    have h2 : t J' * ∏ K ∈ Λ.erase J', t K = 0 := by rw [Finset.mul_prod_erase Λ t hJ', h0]
    calc c' * (t J' * ∏ K ∈ (Λ.erase J).erase J', t K) * (c' * ∏ K ∈ Λ.erase J', t K)
        = c' * c' * (∏ K ∈ (Λ.erase J).erase J', t K) * (t J' * ∏ K ∈ Λ.erase J', t K) := by ring
      _ = 0 := by rw [h2, mul_zero]
  · intro J hJ
    rw [mul_assoc, Finset.prod_erase_mul Λ t hJ, h0, mul_zero]

private def Wt {A : Type} [CommRing A] (N m : ℕ) (α c' : A) (J : Finset (Fin N)) :
    MvPolynomial (Fin N) A :=
  MvPolynomial.C c' * ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J,
    (MvPolynomial.C α - ∏ i ∈ J', MvPolynomial.X i)

private def Ph {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) : (MvPolynomial (Fin N) A)[X] :=
  ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
    C (Wt N m α c' J) * ∏ i ∈ f J, (X - C (MvPolynomial.X i))

private lemma Wt_rename {A : Type} [CommRing A] (N m : ℕ) (α c' : A) (σ : Equiv.Perm (Fin N))
    (J : Finset (Fin N)) :
    MvPolynomial.rename σ (Wt N m α c' J) = Wt N m α c' (J.map σ.toEmbedding) := by
  unfold Wt
  rw [map_mul, MvPolynomial.rename_C, map_prod]
  congr 1
  refine Finset.prod_equiv (Equiv.finsetCongr σ) ?_ ?_
  · intro K
    simp [Finset.mem_erase, Finset.mem_powersetCard]
  · intro K _
    simp [map_sub, map_prod, MvPolynomial.rename_X, Finset.prod_map]

private lemma Ph_sym {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N))
    (hf : ∀ (σ : Equiv.Perm (Fin N)) J, f (J.map σ.toEmbedding) = (f J).map σ.toEmbedding)
    (σ : Equiv.Perm (Fin N)) :
    (Ph N m α c' f).map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom =
      Ph N m α c' f := by
  unfold Ph
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Wt_rename,
    MvPolynomial.rename_X]
  refine Finset.sum_nbij' (fun J => J.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    simpa using hJ
  · intro J hJ
    simpa using hJ
  · intro J _
    ext i
    simp [Finset.mem_map_equiv]
  · intro J _
    ext i
    simp [Finset.mem_map_equiv]
  · intro J _
    rw [hf σ J, Finset.prod_map]
    rfl

private lemma Ph_deg {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) (d : ℕ)
    (hd : ∀ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (f J).card = d) :
    (Ph N m α c' f).natDegree ≤ d := by
  unfold Ph
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro J hJ
  have e1 : ∑ i ∈ f J, (X - C (MvPolynomial.X i : MvPolynomial (Fin N) A)).natDegree ≤ (f J).card := by
    have e2 := Finset.sum_le_sum (s := f J)
      (f := fun i => (X - C (MvPolynomial.X i : MvPolynomial (Fin N) A)).natDegree)
      (g := fun _ => (1 : ℕ)) (fun i _ => natDegree_X_sub_C_le _)
    simpa using e2
  rw [← hd J hJ]
  exact (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans e1)

private lemma Ph_map {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) (x : Fin N → S) :
    (Ph N m α c' f).map (MvPolynomial.aeval x : MvPolynomial (Fin N) A →ₐ[A] S).toRingHom =
      ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
        C (algebraMap A S c' * ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J,
            (algebraMap A S α - ∏ i ∈ J', x i)) * ∏ i ∈ f J, (X - C (x i)) := by
  unfold Ph Wt
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Polynomial.map_sum, Polynomial.map_prod, map_prod, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C]

private lemma coeff_sum {S ι : Type} [CommRing S] [Nontrivial S] {N : ℕ} (Λ : Finset ι)
    (ε : ι → S) (s : ι → Finset (Fin N)) (x : Fin N → S) (d : ℕ)
    (hd : ∀ J ∈ Λ, (s J).card = d) :
    (∑ J ∈ Λ, C (ε J) * ∏ i ∈ s J, (X - C (x i))).coeff d = ∑ J ∈ Λ, ε J := by
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [coeff_C_mul]
  have hm : (∏ i ∈ s J, (X - C (x i))).Monic :=
    monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)
  have hdeg : (∏ i ∈ s J, (X - C (x i))).natDegree = d := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)]
    simp [hd J hJ]
  rw [← hdeg, hm.coeff_natDegree, mul_one]

private lemma eval_sum {S ι : Type} [CommRing S] {N : ℕ} (Λ : Finset ι) (ε : ι → S)
    (s : ι → Finset (Fin N)) (x : Fin N → S) (a : S) (d : ℕ) (h1 : ∑ J ∈ Λ, ε J = 1)
    (hd : ∀ J ∈ Λ, (s J).card = d) (h3 : ∀ J ∈ Λ, ε J * (a - ∏ i ∈ s J, x i) = 0) :
    (∑ J ∈ Λ, C (ε J) * ∏ i ∈ s J, (X - C (x i))).eval 0 = (-1) ^ d * a := by
  rw [eval_finsetSum]
  have key : ∀ J ∈ Λ, (C (ε J) * ∏ i ∈ s J, (X - C (x i))).eval 0 = (-1) ^ d * (ε J * a) := by
    intro J hJ
    have h := h3 J hJ
    rw [eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [Finset.prod_neg, hd J hJ]
    have e : ε J * ∏ i ∈ s J, x i = ε J * a := by linear_combination -h
    linear_combination (-1) ^ d * e
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.sum_mul, h1, one_mul]

theorem UpperTheory.exists_monic_factor_of_root_subset_product_equation :
    ∀ (A : Type) [CommRing A] (g : A[X]) (n m N : ℕ), n + m = N → g.Monic → g.natDegree = N → ∀ (α : A) (c : Aˣ),
      (∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (algebraMap A S α - ∏ i ∈ J, x i) = 0 ∧
        ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J, (algebraMap A S α - ∏ i ∈ J', x i) = algebraMap A S c) →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ Q.natDegree ≤ m ∧ Q.coeff m = 1 ∧ Q.eval 0 = (-1) ^ m * α := by
  intro A _ g n m N hnm hg hN α c hyp
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, by simp,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  classical
  obtain ⟨q, hqdeg, hq⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Ph N m α (↑c⁻¹ : A) (fun J => J))
    (Ph_sym N m α _ _ (fun σ J => rfl))
  obtain ⟨p, -, hp⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Ph N m α (↑c⁻¹ : A) (fun J => Jᶜ))
    (Ph_sym N m α _ _ (fun σ J => by ext i; simp [Finset.mem_map_equiv]))
  obtain ⟨S, iS, aS, hinj, x, hx⟩ := exists_roots hg hN
  haveI : Nontrivial S := hinj.nontrivial
  have hinjX : Function.Injective (Polynomial.map (algebraMap A S)) := Polynomial.map_injective _ hinj
  obtain ⟨h0, h1⟩ := hyp S x hx
  have hc : algebraMap A S (↑c⁻¹ : A) * algebraMap A S (↑c : A) = 1 := by
    rw [← map_mul]
    simp
  obtain ⟨w1, w2, w3⟩ := weights (Finset.powersetCard m (Finset.univ : Finset (Fin N)))
    (fun J => algebraMap A S α - ∏ i ∈ J, x i) _ _ hc h0 h1
  have hqS := hq S x hx
  rw [Ph_map] at hqS
  have hpS := hp S x hx
  rw [Ph_map] at hpS
  have hQd : q.natDegree ≤ m :=
    hqdeg.trans (Ph_deg N m α _ _ m (fun J hJ => (Finset.mem_powersetCard.mp hJ).2))
  have hQc : q.coeff m = 1 := by
    apply hinj
    rw [← Polynomial.coeff_map, hqS,
      coeff_sum _ _ (fun J => J) x m (fun J hJ => (Finset.mem_powersetCard.mp hJ).2), w1, map_one]
  have hQm : q.Monic := by
    have e : q.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQc]; exact one_ne_zero)
    rw [Monic, leadingCoeff, e, hQc]
  have hg' : g = p * q := by
    apply hinjX
    rw [Polynomial.map_mul, hpS, hqS, hx]
    exact (idem_mul _ _ (fun J => ∏ i ∈ Jᶜ, (X - C (x i))) (fun J => ∏ i ∈ J, (X - C (x i))) _ w1 w2
      (fun J _ => Finset.prod_compl_mul_prod J _)).symm
  refine ⟨p, q, Monic.of_mul_monic_right hQm (hg' ▸ hg), hQm, hg', hQd, hQc, ?_⟩
  apply hinj
  rw [← Polynomial.eval_zero_map, hqS,
    eval_sum _ _ (fun J => J) x _ m w1 (fun J hJ => (Finset.mem_powersetCard.mp hJ).2) w3]
  simp

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.PicData
section
open CategoryTheory TensorProduct

noncomputable section

namespace UpperTheory.PicD

section Rings
variable (A C : Type) [CommRing A] [CommRing C] [Algebra A C]

abbrev i1 : C →ₐ[A] C ⊗[A] C := Algebra.TensorProduct.includeLeft

abbrev i2 : C →ₐ[A] C ⊗[A] C := Algebra.TensorProduct.includeRight

abbrev c12 : C ⊗[A] C →ₐ[A] C ⊗[A] (C ⊗[A] C) :=
  Algebra.TensorProduct.map (AlgHom.id A C) (i1 A C)

abbrev c13 : C ⊗[A] C →ₐ[A] C ⊗[A] (C ⊗[A] C) :=
  Algebra.TensorProduct.map (AlgHom.id A C) (i2 A C)

abbrev c23 : C ⊗[A] C →ₐ[A] C ⊗[A] (C ⊗[A] C) := Algebra.TensorProduct.includeRight

variable {A C}

def theta (g : C ⊗[A] C) : C →ₗ[C] C ⊗[A] C := LinearMap.toSpanSingleton C _ g

@[simp] theorem theta_apply (g : C ⊗[A] C) (b : C) : theta g b = b • g := rfl

abbrev Mg (g : C ⊗[A] C) : Submodule A C := GlobalTheory.FlatDescent.invariants (theta g)

end Rings

structure Data where
  S0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}
  S1 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}
  d : S0 ⟶ S1
  ι : ∀ R : CommRingCat.{0}, Additive Rˣ →+ S0.obj R
  ι_nat : ∀ {R R' : CommRingCat.{0}} (f : R ⟶ R') (u : Rˣ),
    (S0.map f).hom (ι R (Additive.ofMul u)) = ι R' (Additive.ofMul (Units.map f.hom.toMonoidHom u))
  ι_inj : ∀ R, Function.Injective (ι R)
  d_eq_zero : ∀ (R : CommRingCat.{0}) (w : S0.obj R), (d.app R).hom w = 0 ↔ ∃ u, ι R u = w
  glue : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Module.FaithfullyFlat A C] [Algebra.Etale A C]
    (w : S0.obj (CommRingCat.of C)),
    (S0.map (CommRingCat.ofHom (i1 A C).toRingHom)).hom w = (S0.map (CommRingCat.ofHom (i2 A C).toRingHom)).hom w →
    ∃ y : S0.obj (CommRingCat.of A), (S0.map (CommRingCat.ofHom (algebraMap A C))).hom y = w
  sep : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Module.FaithfullyFlat A C] [Algebra.Etale A C],
    Function.Injective (S1.map (CommRingCat.ofHom (algebraMap A C))).hom

namespace Data
variable (P : Data)

def r0 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    P.S0.obj (CommRingCat.of R) →+ P.S0.obj (CommRingCat.of S) := (P.S0.map (CommRingCat.ofHom f)).hom

def r1 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    P.S1.obj (CommRingCat.of R) →+ P.S1.obj (CommRingCat.of S) := (P.S1.map (CommRingCat.ofHom f)).hom

def dd (R : Type) [CommRing R] : P.S0.obj (CommRingCat.of R) →+ P.S1.obj (CommRingCat.of R) :=
  (P.d.app (CommRingCat.of R)).hom

def un {R : Type} [CommRing R] (u : Rˣ) : P.S0.obj (CommRingCat.of R) :=
  P.ι (CommRingCat.of R) (Additive.ofMul u)

theorem mapDegZero_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : P.S0.obj (CommRingCat.of R)) : P.r0 g (P.r0 f x) = P.r0 (g.comp f) x := by
  simp [r0, CommRingCat.ofHom_comp]

theorem mapDegOne_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : P.S1.obj (CommRingCat.of R)) : P.r1 g (P.r1 f x) = P.r1 (g.comp f) x := by
  simp [r1, CommRingCat.ofHom_comp]

theorem diff_mapDegZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : P.S0.obj (CommRingCat.of R)) :
    P.dd S (P.r0 f x) = P.r1 f (P.dd R x) := by
  have := congrArg (fun φ => φ.hom x) (P.d.naturality (CommRingCat.ofHom f))
  simpa [dd, r0, r1] using this

theorem mapDegZero_ofUnit {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ) :
    P.r0 f (P.un u) = P.un (Units.map f.toMonoidHom u) :=
  P.ι_nat (CommRingCat.ofHom f) u

theorem un_mul {R : Type} [CommRing R] (u v : Rˣ) : P.un (u * v) = P.un u + P.un v :=
  map_add (P.ι (CommRingCat.of R)) (Additive.ofMul u) (Additive.ofMul v)

theorem un_injective {R : Type} [CommRing R] : Function.Injective (P.un (R := R)) :=
  fun _ _ h => Additive.ofMul.injective (P.ι_inj _ h)

theorem un_one {R : Type} [CommRing R] : P.un (1 : Rˣ) = 0 := map_zero (P.ι (CommRingCat.of R))

theorem dd_eq_zero {R : Type} [CommRing R] (w : P.S0.obj (CommRingCat.of R)) :
    P.dd R w = 0 ↔ ∃ u : Rˣ, P.un u = w := by
  rw [dd, P.d_eq_zero]
  exact ⟨fun ⟨u, h⟩ => ⟨u.toMul, h⟩, fun ⟨u, h⟩ => ⟨Additive.ofMul u, h⟩⟩

structure Triv {A : Type} [CommRing A] (z : P.S1.obj (CommRingCat.of A)) (M : Type) [AddCommGroup M] [Module A M]
    (C : Type) [CommRing C] [Algebra A C] (w : P.S0.obj (CommRingCat.of C)) (g : (C ⊗[A] C)ˣ) (t : M →ₗ[A] C) :
    Prop where
  dw : P.dd C w = P.r1 (algebraMap A C) z
  hg : P.un g = P.r0 (i2 A C).toRingHom w - P.r0 (i1 A C).toRingHom w
  ht : ∀ m, t m • (g : C ⊗[A] C) = (1 : C) ⊗ₜ[A] t m
  bij : Function.Bijective (LinearMap.liftBaseChange C t)

def Rel {A : Type} [CommRing A] (z : P.S1.obj (CommRingCat.of A)) (M : Type) [AddCommGroup M] [Module A M] : Prop :=
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
    ∃ (w : P.S0.obj (CommRingCat.of C)) (g : (C ⊗[A] C)ˣ) (t : M →ₗ[A] C), P.Triv z M C w g t

def LocEx {A : Type} [CommRing A] (z : P.S1.obj (CommRingCat.of A)) : Prop :=
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
    ∃ w : P.S0.obj (CommRingCat.of C), P.dd C w = P.r1 (algebraMap A C) z

end Data
end UpperTheory.PicD
end
end

