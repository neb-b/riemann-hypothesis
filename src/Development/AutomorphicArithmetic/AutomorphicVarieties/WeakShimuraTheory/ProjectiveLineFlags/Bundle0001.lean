module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CcEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.ccEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ cF : G T.F Ω, IsCC cF ∧
          ∀ g : G T.L Ω, ∃ g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ ∧ resLe T.F_le g' = cF * resLe T.F_le g * cF⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  haveI := T.nL
  haveI := T.cmL
  haveI := T.nF
  haveI := T.realF
  haveI : Normal (W.Lp T.L) T.L := by
    unfold UpperTheory.V.W.Lp
    infer_instance
  obtain ⟨j, hj⟩ := s.hc
  have hstab : ∀ τ : G (W.Lp T.L) Ω, ∀ x : T.L, ∃ y : T.L, τ (x : Ω) = (y : Ω) := by
    intro τ x
    exact ⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩
  have hfixF : ∀ x : T.F, s.c (x : Ω) = x := by
    intro x
    have hmem : (⟨(x : Ω), T.F_le x.2⟩ : T.L) ∈ NumberField.maximalRealSubfield T.L := by
      intro φ
      have h := NumberField.IsTotallyReal.complexEmbedding_isReal
        (φ.comp (IntermediateField.inclusion T.F_le).toRingHom)
      have h2 := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp h) x
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h2
      exact h2
    exact s.c.commutes (show W.Lp T.L from (⟨_, hmem⟩ : NumberField.maximalRealSubfield T.L))
  let cF : G T.F Ω := { s.c.toRingEquiv with commutes' := fun x => hfixF x }
  refine ⟨cF, ⟨j, fun x => hj x⟩, ?_⟩
  intro g
  let ρ : Ω ≃+* Ω := s.c.symm.toRingEquiv.trans (g.toRingEquiv.trans s.c.toRingEquiv)
  have hρ : ∀ x : T.L, ρ (algebraMap T.L Ω x) = algebraMap T.L Ω x := by
    intro x
    obtain ⟨y, hy⟩ := hstab s.c⁻¹ x
    have hy' : s.c.symm (x : Ω) = (y : Ω) := hy
    change s.c (g (s.c.symm (x : Ω))) = (x : Ω)
    rw [hy']
    have hg : g (y : Ω) = (y : Ω) := g.commutes y
    rw [hg, ← hy']
    exact s.c.apply_symm_apply _
  refine ⟨AlgEquiv.ofRingEquiv hρ, ?_, ?_⟩
  · ext z
    rfl
  · ext z
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.ContinuousLinearClosed
section
section
open IsLocalRing Matrix Polynomial UpperTheory.V.W

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem eq_zero_of_smul_mul_eq_mul_of_isNilpotent_constantCoeff {K : Type} [Field K] {n : ℕ} (A Y : Matrix (Fin n) (Fin n) (PowerSeries K)) (e c : PowerSeries K)
    (hN : IsNilpotent ((A - c • (1 : Matrix (Fin n) (Fin n) (PowerSeries K))).map PowerSeries.constantCoeff))
    (he : PowerSeries.constantCoeff e ≠ 1) (hc : PowerSeries.constantCoeff c ≠ 0)
    (hY : e • (A * Y) = Y * A) : Y = 0 := by
  set N := A - c • (1 : Matrix (Fin n) (Fin n) (PowerSeries K)) with hNdef
  set V := e • A - c • (1 : Matrix (Fin n) (Fin n) (PowerSeries K)) with hVdef
  have hYN : Y * N = V * Y := by
    rw [hNdef, hVdef, mul_sub, sub_mul, ← hY, Matrix.mul_smul, mul_one, Matrix.smul_mul, Matrix.smul_mul, one_mul]
  have hpow : ∀ k : ℕ, Y * N ^ k = V ^ k * Y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, hYN, ← mul_assoc]
  obtain ⟨m, hm⟩ := hN
  let cc := (PowerSeries.constantCoeff : PowerSeries K →+* K).mapMatrix (m := Fin n)
  have hm' : cc (N ^ m) = 0 := by
    rw [map_pow]
    exact hm
  have hdvd : ∀ i j, (PowerSeries.X : PowerSeries K) ∣ (N ^ m) i j := by
    intro i j
    rw [PowerSeries.X_dvd_iff]
    have := congrFun (congrFun hm' i) j
    simpa [cc] using this
  choose Q hQ using hdvd
  have hNm : N ^ m = (PowerSeries.X : PowerSeries K) • Matrix.of Q := by
    ext i j
    simp [hQ i j]
  have hcV : cc V = ((PowerSeries.constantCoeff e - 1) * PowerSeries.constantCoeff c) • (1 : Matrix (Fin n) (Fin n) K) + PowerSeries.constantCoeff e • cc N := by
    ext i j
    simp only [cc, hVdef, hNdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp <;> ring
  have hV : IsUnit V := by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, ← Matrix.isUnit_iff_isUnit_det]
    change IsUnit (cc V)
    rw [hcV]
    apply IsNilpotent.isUnit_add_left_of_commute
    · exact ⟨m, by rw [_root_.smul_pow, show cc N ^ m = 0 by rw [← map_pow]; exact hm', smul_zero]⟩
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.mpr (mul_ne_zero (sub_ne_zero.mpr he) hc)).pow _
    · exact (Commute.one_right _).smul_right _
  have hVm : V ^ m * Y = (PowerSeries.X : PowerSeries K) • (Y * Matrix.of Q) := by
    rw [← hpow, hNm, Matrix.mul_smul]
  let W : Matrix (Fin n) (Fin n) (PowerSeries K) := ((hV.unit ^ m)⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries K))ˣ)
  have hWV : W * V ^ m = 1 := by
    have h1 : ((hV.unit ^ m : (Matrix (Fin n) (Fin n) (PowerSeries K))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries K)) = V ^ m := by
      simp
    rw [← h1]
    exact Units.inv_mul _
  have hYeq : Y = (PowerSeries.X : PowerSeries K) • (W * Y * Matrix.of Q) := by
    calc Y = W * (V ^ m * Y) := by rw [← mul_assoc, hWV, one_mul]
      _ = _ := by rw [hVm, Matrix.mul_smul, mul_assoc]
  have hk : ∀ k : ℕ, ∃ Z : Matrix (Fin n) (Fin n) (PowerSeries K), Y = ((PowerSeries.X : PowerSeries K) ^ k) • Z := by
    intro k
    induction k with
    | zero => exact ⟨Y, by simp⟩
    | succ k ih =>
      obtain ⟨Z, hZ⟩ := ih
      refine ⟨W * Z * Matrix.of Q, ?_⟩
      conv_lhs => rw [hYeq]
      rw [hZ, Matrix.mul_smul, Matrix.smul_mul, smul_smul, pow_succ']
  ext i j d
  obtain ⟨Z, hZ⟩ := hk (d + 1)
  have hdv : (PowerSeries.X : PowerSeries K) ^ (d + 1) ∣ Y i j := ⟨Z i j, by rw [hZ]; simp⟩
  rw [PowerSeries.X_pow_dvd_iff] at hdv
  simpa using hdv d (Nat.lt_succ_self d)

private theorem charpoly_mat_map_constantCoeff_eq_prod_X_sub_C {l : ℕ} [Fact (Nat.Prime l)] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (x : W.Point r) (g : F.G₀) :
    Matrix.charpoly ((W.mat x.ρ g).map PowerSeries.constantCoeff) = ∏ i, (Polynomial.X - Polynomial.C (algebraMap (ResidueField O) x.K (r.chib i g : ResidueField O))) := by
  have h := congrArg (fun D : W.GDet n x.K F.G₀ => D.D (Polynomial x.K) (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single g 1)) x.red
  simp only [W.GDet.map, W.GDet.ofRep, W.Resid.Dbar, MonoidHom.coe_comp, Function.comp_apply, map_sub, W.GDet.repAlg, MonoidAlgebra.lift_single] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, MonoidAlgebra.lift_single, map_one, Matrix.coe_detMonoidHom, MonoidHom.coe_comp, Function.comp_apply, one_smul] at h
  rw [← Matrix.det_diagonal, Matrix.charpoly]
  convert h using 2
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.charmatrix_apply, Matrix.one_apply]
      rfl
    · simp [Matrix.charmatrix_apply, Matrix.one_apply, hij]
      rfl
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [W.diagRep, Matrix.one_apply]
      rfl
    · simp [W.diagRep, Matrix.one_apply, hij]

theorem UpperTheory.V.Ws.P1.n4V0 :
    ∀ (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : W.Resid F O n), r.V0ok → ∀ x : W.Point r, x.N4 := by
  intro l _ F O _ _ _ n r hV0 x X hX
  obtain ⟨_, hD0, g, hg, hεg⟩ := hV0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Subsingleton.elim _ _
  let i0 : Fin n := ⟨0, hn⟩
  let A : Matrix (Fin n) (Fin n) x.A := W.mat x.ρ g
  let e : x.A := algebraMap O x.A (algebraMap ℤ_[l] O ((F.ε (g : F.Γ) : ℤ_[l]ˣ) : ℤ_[l]))
  let χ : ResidueField O := (r.chib i0 g : ResidueField O)
  let c : x.A := PowerSeries.C (algebraMap (ResidueField O) x.K χ)
  obtain ⟨⟨b, hb⟩, hbY⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors x.A) (fun p : Fin n × Fin n => X p.1 p.2)
  choose Yf hYf using fun p => RingHom.mem_rangeS.mp (hbY p)
  let Y : Matrix (Fin n) (Fin n) x.A := Matrix.of fun i j => Yf (i, j)
  let φ := (algebraMap x.A x.Fr).mapMatrix (m := Fin n)
  have hφinj : Function.Injective φ := Matrix.map_injective (IsFractionRing.injective x.A x.Fr)
  have hφY : φ Y = algebraMap x.A x.Fr b • X := by
    ext i j
    simp only [φ, Y, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply]
    rw [hYf (i, j), Algebra.smul_def, smul_eq_mul]
  have hφA : φ A = W.mat x.ρF g := rfl
  have hφe : algebraMap x.A x.Fr e = ((F.eps O x.Fr g : x.Frˣ) : x.Fr) := rfl
  have hY : e • (A * Y) = Y * A := by
    apply hφinj
    have hX' := hX g hg
    rw [← hφe] at hX'
    rw [map_mul, hφY, hφA]
    have h1 : φ (e • (A * Y)) = algebraMap x.A x.Fr e • (φ A * φ Y) := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [φ, Matrix.smul_apply, Matrix.mul_apply, map_sum]
    rw [h1, hφY, hφA, Matrix.mul_smul, smul_comm, hX', Matrix.smul_mul]
  have hall : ∀ i, (r.chib i g : ResidueField O) = χ := fun i => congrArg Units.val (hD0 g hg i i0)
  have hcp := charpoly_mat_map_constantCoeff_eq_prod_X_sub_C x g
  simp only [hall] at hcp
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcp
  have hCH := Matrix.aeval_self_charpoly (A.map PowerSeries.constantCoeff)
  rw [hcp] at hCH
  simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
  have hNm : (A - c • (1 : Matrix (Fin n) (Fin n) x.A)).map PowerSeries.constantCoeff = A.map PowerSeries.constantCoeff - algebraMap x.K (Matrix (Fin n) (Fin n) x.K) (algebraMap (ResidueField O) x.K χ) := by
    ext i j
    simp [c, Matrix.one_apply, Algebra.algebraMap_eq_smul_one]
    split_ifs <;> simp
  have hnil : IsNilpotent ((A - c • (1 : Matrix (Fin n) (Fin n) x.A)).map PowerSeries.constantCoeff) := ⟨n, by rw [hNm]; exact hCH⟩
  have he : PowerSeries.constantCoeff e ≠ 1 := by
    intro h
    apply hεg
    ext
    apply (algebraMap (ResidueField O) x.K).injective
    rw [Units.val_one, map_one, ← h]
    simp only [e, PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, IsScalarTower.algebraMap_apply O (ResidueField O) x.K]
    rfl
  have hc : PowerSeries.constantCoeff c ≠ 0 := by
    simp only [c, PowerSeries.constantCoeff_C]
    exact (_root_.map_ne_zero _).mpr (Units.ne_zero _)
  have hY0 := eq_zero_of_smul_mul_eq_mul_of_isNilpotent_constantCoeff A Y e c hnil he hc hY
  ext i j
  have h2 : Yf (i, j) = 0 := by
    have := congrFun (congrFun hY0 i) j
    simpa [Y] using this
  have h1 : algebraMap x.A x.Fr b * X i j = 0 := by
    rw [← Algebra.smul_def]
    have h3 := hYf (i, j)
    rw [h2, map_zero] at h3
    exact h3.symm
  have hb' : algebraMap x.A x.Fr b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  rw [Matrix.zero_apply]
  exact (mul_eq_zero.mp h1).resolve_left hb'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CpSmul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem eval_smul_homog {σ R : Type} [CommRing R] {φ : MvPolynomial σ R} {d : ℕ}
    (h : φ.IsHomogeneous d) (a : R) (x : σ → R) :
    MvPolynomial.eval₂Hom (RingHom.id R) (fun s => a * x s) φ
      = MvPolynomial.eval₂Hom (RingHom.id R) x φ * a ^ d := by
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := h (MvPolynomial.mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

private theorem prod_scale {ι R : Type} [CommRing R] (a : R) (x : ι → R) (s : Finset ι) :
    (∏ i ∈ s, (X - C (x i))).scaleRoots a = ∏ i ∈ s, (X - C (a * x i)) := by
  classical
  nontriviality R
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots', ih, X_sub_C_scaleRoots,
      mul_comm (x j) a]
    rw [(monic_X_sub_C _).leadingCoeff,
      (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)).leadingCoeff]
    simp

theorem UpperTheory.V.Ws.P1.cpSmul :
    ∀ {n : ℕ} {R : Type} [CommRing R] (a : R) (M : Matrix (Fin n) (Fin n) R), (a • M).charpoly = M.charpoly.scaleRoots a ∧
          ∀ x : Fin n → R, (∏ i, (X - C (x i))).scaleRoots a = ∏ i, (X - C (a * x i)) := by
  intro n R _ a M
  refine ⟨?_, fun x => prod_scale a x _⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  ext i
  rw [coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim]
  rcases le_or_gt i (Fintype.card (Fin n)) with hi | hi
  · have h1 : (a • M).charpoly.coeff i = _ :=
      (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id R)
        (fun ij : Fin n × Fin n => a * M ij.1 ij.2) i).symm
    have h2 : M.charpoly.coeff i = _ :=
      (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id R)
        (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
    rw [h1, h2]
    exact eval_smul_homog
      (Matrix.charpoly.univ_coeff_isHomogeneous R (Fin n) i _ (Nat.add_sub_cancel' hi)) a _
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim]),
      coeff_eq_zero_of_natDegree_lt (by rwa [Matrix.charpoly_natDegree_eq_dim]), zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.DetExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.detExt :
    ∀ {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : W.GDet n A G) (f : A →+* A') (D' : W.GDet n A' G),
          (∀ g : G, (D.chi (MonoidAlgebra.single g 1)).map f = D'.chi (MonoidAlgebra.single g 1)) → D.map f = D' := by
  intro n A A' G _ _ _ D f D' h
  apply CA.d_gext
  intro g i _ _
  rw [(AlgebraTools.Det.mapApi D f).2.2.1 i g]
  simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one]
  rw [← Polynomial.coeff_map, h g]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.GspForm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def UpperTheory.V.Ws.P1.formJ (R : Type) [CommRing R] : M4 R :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem UpperTheory.V.Ws.P1.formJ_sq (R : Type) [CommRing R] :
    UpperTheory.V.Ws.P1.formJ R * UpperTheory.V.Ws.P1.formJ R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem UpperTheory.V.Ws.P1.formJ_adj (R : Type) [CommRing R] (g : M4 R) :
    g.transpose * UpperTheory.V.Ws.P1.formJ R = UpperTheory.V.Ws.P1.formJ R * UpperTheory.V.GradeZeroInterpolatingElement.adj g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four, UpperTheory.V.GradeZeroInterpolatingElement.adj, UpperTheory.V.GradeZeroInterpolatingElement.sgn, Fin.rev]

theorem UpperTheory.V.Ws.P1.gspForm :
    ∀ (R : Type) [CommRing R], ∃ J : (M4 R)ˣ, (J : M4 R).transpose = -J ∧ ∀ (ν : R) (g : M4 R), IsGSp ν g → g.transpose * (J : M4 R) * g = ν • (J : M4 R) := by
  intro R _
  refine ⟨⟨UpperTheory.V.Ws.P1.formJ R, -UpperTheory.V.Ws.P1.formJ R, ?_, ?_⟩, ?_, ?_⟩
  · rw [mul_neg, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]
  · rw [neg_mul, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ]
  · intro ν g hg
    have h : UpperTheory.V.GradeZeroInterpolatingElement.adj g * g = ν • 1 := hg
    simp only [Units.val_mk]
    rw [UpperTheory.V.Ws.P1.formJ_adj, mul_assoc, h, Matrix.mul_smul, Matrix.mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.LevEps
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem exists_plc_over (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl.out)
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K)
    (Ideal.span {(l : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]
      exact bot_le)
  have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have h : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  intro h0
  rw [h0, Ideal.mem_bot] at hmem
  exact hl.out.ne_zero (by exact_mod_cast hmem)

theorem UpperTheory.V.Ws.P1.levEps :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev),
          (∀ g g' : G L Ω, W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ → V.frame.conj (V.pr g) = V.pr g') ∧
          (∀ g : G L Ω, V.pr g ∈ V.frame.G' ↔ cycZ L Ω l g = 1) ∧ Nonempty V.frame.Vl ∧
          ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : G L Ω), ((V.frame.eps O R (V.pr g) : Rˣ) : R) = algebraMap O R (chiO L Ω l O g) := by
  intro l _ L Ω _ _ _ _ _ _ s V
  have key : ∀ g : G L Ω, V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := by
    intro g
    have h := congrArg (fun f => f (W.resP L Ω g)) V.hε
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g g' h
    unfold UpperTheory.V.W.HidaSetting.Lev.frame UpperTheory.V.W.GFrame.conj
    simp only [UpperTheory.V.W.HidaSetting.Lev.pr]
    apply Subtype.ext
    change toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω g) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω g')
    rw [h, map_mul, map_mul, map_inv]
  · intro g
    unfold UpperTheory.V.W.HidaSetting.Lev.frame UpperTheory.V.W.GFrame.G'
    simp only [UpperTheory.V.W.HidaSetting.Lev.pr]
    rw [MonoidHom.mem_ker]
    change V.ε (toGS Ω V.S' (W.resP L Ω g)) = 1 ↔ _
    rw [key]
  · unfold UpperTheory.V.W.HidaSetting.Lev.frame
    show Nonempty (UpperTheory.V.W.Vl l L)
    unfold UpperTheory.V.W.Vl
    first
      | exact ⟨⟨(exists_plc_over L l).choose, (exists_plc_over L l).choose_spec⟩⟩
      | exact ⟨⟨(exists_plc_over (W.Lp L) l).choose, (exists_plc_over (W.Lp L) l).choose_spec⟩⟩
  · intro O _ _ R _ _ g
    unfold UpperTheory.V.W.HidaSetting.Lev.frame UpperTheory.V.W.GFrame.eps
    simp only [UpperTheory.V.W.HidaSetting.Lev.pr, UpperTheory.V.Base.chiO]
    simp [UpperTheory.V.W.pushCh, MonoidHom.codRestrict_apply]
    change (algebraMap O R) ((algebraMap ℤ_[l] O) ↑(V.ε (toGS Ω V.S' (W.resP L Ω g)))) = _
    rw [key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPairAlt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.P1.psPair_fac {Λ B k : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [Algebra Λ B] [IsCO Λ B]
    [Field k] [Algebra Λ k] (φ : B →+* k) (h1 : ∀ a, φ (algebraMap Λ B a) = algebraMap Λ k a)
    (h2 : ∀ b ∈ maximalIdeal B, φ b = 0) :
    ∃ j : ResidueField Λ →+* k, (∀ a, j (residue Λ a) = algebraMap Λ k a) ∧ ∀ b, j (res Λ B b) = φ b := by
  have h3 : ∀ a ∈ maximalIdeal Λ, algebraMap Λ k a = 0 := fun a ha => by
    rw [← h1]
    exact h2 _ fun hu => ha (IsLocalHom.map_nonunit a hu)
  refine ⟨Ideal.Quotient.lift _ (algebraMap Λ k) h3, fun a => rfl, fun b => ?_⟩
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := Λ) b
  have e1 : res Λ B b = residue Λ a := by
    have := (res_eq_zero_iff Λ B _).2 ha
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have e2 := h2 _ ha
  rw [map_sub, sub_eq_zero, h1] at e2
  rw [e1, e2]
  rfl

private theorem UpperTheory.V.Ws.P1.psPair_cont {Γ A R : Type} [TopologicalSpace Γ] [CommRing A] [CommRing R] (f : A →+* R)
    {I : Ideal A} {J : Ideal R} (hI : I.map f ≤ J) {u : Γ → A} (hu : AdicCont I u) : AdicCont J fun g => f (u g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI N
  exact (hu N).comp (Ideal.quotientMap (J ^ N) f hN)

theorem UpperTheory.V.Ws.P1.psPair :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (k : Type) [Field k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
          (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) → T.PsPair h k (X.P.map (y : X.A →+* PowerSeries k)) := by
  intro Ω _ _ _ l _ c D T c' h X k _ _ y hy
  let φ : X.B →+* k := ((PowerSeries.constantCoeff : PowerSeries k →+* k).comp (y : X.A →+* PowerSeries k)).comp (algebraMap X.B X.A)
  have hφ : ∀ b, φ b = PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) := fun b => rfl
  have h1 : ∀ a, φ (algebraMap c'.O X.B a) = algebraMap c'.O k a := fun a => by
    rw [hφ, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C]
  obtain ⟨j, hj1, hj2⟩ := UpperTheory.V.Ws.P1.psPair_fac φ h1 hy
  obtain ⟨hψ, hp, -⟩ := sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P
  refine ⟨fun a ha => ?_, ?_, fun i i' => ?_, fun g => ?_, fun v i s hs => ?_⟩
  · rw [← hj1, (residue_eq_zero_iff a).2 ha, map_zero]
  · have := hp X.pair
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at this
  · refine UpperTheory.V.Ws.P1.psPair_cont (y : X.A →+* PowerSeries k) ?_ (X.cont i i')
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    have := hy b hb
    intro hu
    exact hu.ne_zero this
  · have e : (X.P.map (y : X.A →+* PowerSeries k)).r g = (X.P.r g).map (y : X.A →+* PowerSeries k) := rfl
    have e2 : φ = j.comp (res c'.O X.B : X.B →+* ResidueField c'.O) := RingHom.ext fun b => (hj2 b).symm
    rw [e, Matrix.charpoly_map, ← X.cp_map, Polynomial.map_map, Polynomial.map_map]
    show (X.cp g).map φ = _
    rw [e2, ← Polynomial.map_map, X.cp_red, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, hj1]
    rfl
  · have e1 := hψ v i s
    rw [← X.ψ_map v i s hs] at e1
    have e2 := hj2 (X.ψ v i s)
    rw [X.ψ_red v i s hs, hj1] at e2
    exact (congrArg PowerSeries.constantCoeff e1).trans e2.symm
end

