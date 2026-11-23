module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingMinorProductHarmonicGenerates
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Harm
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ}

def invTranspose {K : Type} [Field K] (g : GL (Fin n) K) : GL (Fin n) K :=
  ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose, (g : Matrix (Fin n) (Fin n) K).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem rename_letAct_invTranspose_eq_colAct {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)} (hpl : IsEnum H pl) (K : Type) [Field K]
    (g : {τ : E →+* ℂ // InPsi H τ} → GL (Fin n) K) (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩)) P) =
      colAct K _ Dw.p Dw.q (Fin n) g (rename (thetaLetterEquiv Dw n) P) := by
  rw [colAct_apply]
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp
    (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩))) =
    (colSubst (fun t => (((g t)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (fun t => g t)).comp
      (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with h | ⟨τ, h, rfl⟩
  · have h₁ : ∃ t, pl t = τ := (hpl.2 τ).1 h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dite_eq_left h₁, thetaLetterEquiv_of_mem Dw h, colSubst_X_xVar, xForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext h₁.choose_spec
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw h]
    simp only [e]
    rfl
  · have h₀ : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun hh => by
      have h₂ : InPsi H (ComplexEmbedding.conjugate τ) := (hpl.2 _).2 hh
      exact (not_mem_hostType_iff H τ).2 h₂ h
    have h₁ : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ := by
      obtain ⟨t, ht⟩ := (hpl.2 τ).1 h
      exact ⟨t, by rw [ht]⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dite_eq_right h₀, dite_eq_left h₁, thetaLetterEquiv_conjugate Dw h, colSubst_X_yVar, yForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext ((ComplexEmbedding.involutive_conjugate E).injective h₁.choose_spec)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw h]
    simp only [e]
    rfl

variable {l : Level H} (c : Coeff l)

theorem rename_minorP_of_mem (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.p)
    (hi : i.val < Dw.mult τ) (hi' : i.val + 1 ≤ n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c τ i.val hi (Fin.castLE hi')) =
      xMinor ⟨τ, h⟩ i (baseCovec c.F hn) := by
  rw [minorPolynomial, xMinor, AlgHom.map_det]
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseCovec, xForm_single]
  rw [thetaLetterEquiv_of_mem Dw h]
  rfl

theorem rename_minorP_conjugate (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.q)
    (hi : i.val < Dw.mult (ComplexEmbedding.conjugate τ)) (hi' : n - (i.val + 1) + (i.val + 1) = n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c (ComplexEmbedding.conjugate τ) i.val hi
      (fun b => Fin.cast hi' (Fin.natAdd (n - (i.val + 1)) b))) =
      ((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        yMinor ⟨τ, h⟩ i (baseVec c.F hn) := by
  rw [minorPolynomial, yMinor, AlgHom.map_det, ← Matrix.det_permute']
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseVec, yForm_single,
    Matrix.submatrix_apply, id]
  rw [thetaLetterEquiv_conjugate Dw h]
  refine congrArg X (Prod.ext rfl (Prod.ext rfl (Fin.ext ?_)))
  have := b.isLt
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
  omega

theorem rename_pG [Fintype {τ : E →+* ℂ // InPsi H τ}] (hn : Dw.p + Dw.q ≤ n) (a : (E →+* ℂ) × ℕ → ℕ) :
    ∃ u : ℤˣ, rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) =
      ((u : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        basePoly c.F hn (fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i))
          (fun t => diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) := by
  refine ⟨∏ t : {τ : E →+* ℂ // InPsi H τ}, ∏ i : Fin Dw.q, Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) ^
    diffOf (fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) i, ?_⟩
  rw [pG, ← Fintype.prod_sigma', ← (halfRowEquiv (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw)).symm.prod_comp,
    Fintype.prod_prod_type, basePoly, minorProd, map_prod]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Fintype.prod_sum_type, map_mul, mul_left_comm, ← Finset.prod_mul_distrib, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult t.1 := by rw [mult_of_mem Dw t.2]; exact i.isLt
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H t.1 then minorPolynomial c t.1 i.val hi (Fin.castLE h)
        else minorPolynomial c t.1 i.val hi (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a t.1 i.val) = _
    rw [dite_eq_left hi', if_pos t.2, map_pow, rename_minorP_of_mem Dw c hn t.2]
    congr 1
    rw [aStep, diffOf, mult_of_mem Dw t.2]
    split_ifs <;> rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult (ComplexEmbedding.conjugate t.1) :=
      i.isLt.trans_eq (mult_conjEmb_of_mem Dw t.2).symm
    have h₀ : ¬ InPsi H (ComplexEmbedding.conjugate t.1) := fun h₂ => (not_mem_hostType_iff H t.1).2 h₂ t.2
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H (ComplexEmbedding.conjugate t.1) then
        minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi (Fin.castLE h)
        else minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi
          (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a (ComplexEmbedding.conjugate t.1) i.val) = _
    rw [dite_eq_left hi', if_neg h₀, map_pow, rename_minorP_conjugate Dw c hn t.2, ← mul_pow]
    congr 1
    have hq : Dw.mult (ComplexEmbedding.conjugate t.1) = Dw.q := mult_conjEmb_of_mem Dw t.2
    rw [aStep, diffOf, hq]
    split_ifs <;> rfl

theorem pG_mem_ne_zero_generates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → pG (Dw := Dw) c a n ∈ harmA (Dw := Dw) c a n ∧ pG (Dw := Dw) c a n ≠ 0 ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F => letAct Dw pl c.F g (pG (Dw := Dw) c a n)) := by
  intro E _ _ _ H Dw n Ix _ pl hpl hn l c a ha
  obtain ⟨u, hu⟩ := rename_pG Dw c hn a
  set k := fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i) with hk
  set k' := fun t : {τ : E →+* ℂ // InPsi H τ} =>
    diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) with hk'
  have hx (t : {τ : E →+* ℂ // InPsi H τ}) : partOf (k t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j hij => ha t.1 hij
  have hy (t : {τ : E →+* ℂ // InPsi H τ}) :
      partOf (k' t) = fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j hij => ha _ hij
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        rename (thetaLetterEquiv Dw n) P ∈ orbitSpan c.F hn k k' := by
    rw [← (rowHighest_orbitSpan_main hn k k' c.F).2.1, mem_rowHighest_iff_rowAdd]
    simp only [hx, hy]
    exact mem_HHa_iff_rename (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) _ P
  rw [← zsmul_eq_mul] at hu
  have hu' : basePoly c.F hn k k' = (u : ℤ) • rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) := by
    rw [hu, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  have hinj := (thetaLetterEquiv Dw n).injective
  refine ⟨⟨(hmem _).2 ?_, fun m => ?_⟩, fun h0 => ?_, fun P hP => ?_⟩
  · rw [hu]
    exact zsmul_mem (basePoly_mem hn k k') _
  · rw [← coeff_rename_mapDomain _ hinj, hu, ← map_basePoly hn k k' (Int.castRingHom c.F), ← map_zsmul, coeff_map]
    exact intCast_mem _ _
  · rw [h0, map_zero, smul_zero] at hu'
    exact basePoly_ne_zero hn k k' hu'
  · have key : orbitSpan c.F hn k k' ≤ (Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F =>
        letAct Dw pl c.F g (pG (Dw := Dw) c a n))).map (rename (thetaLetterEquiv Dw n)).toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      simp only [hu', map_zsmul, ← rename_letAct_invTranspose_eq_colAct Dw hpl]
      exact zsmul_mem (Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self _))) _
    obtain ⟨Q, hQ, e⟩ := key ((hmem P).1 hP)
    rwa [← rename_injective _ hinj e]

end GlobalTheory.FrameRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemNabStdOfDetMulIntegral
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.DetSat

theorem mem_valuationSubring_of_indep {K σ ι : Type} [Field K] [Fintype ι] (A : ValuationSubring K)
    (q : ι → MvPolynomial σ ℤ)
    (hq : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i => map (Int.castRingHom (IsLocalRing.ResidueField A)) (q i)))
    (c : ι → K) (hc : ∀ m, (∑ i, c i • map (Int.castRingHom K) (q i)).coeff m ∈ A) (i : ι) : c i ∈ A := by
  by_contra hi
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => A.valuation (c i)) ⟨i, Finset.mem_univ i⟩
  have h1 : 1 < A.valuation (c j) :=
    lt_of_lt_of_le (not_le.mp fun h => hi ((A.valuation_le_one_iff _).mp h)) (hj i (Finset.mem_univ i))
  have hv0 : 0 < A.valuation (c j) := lt_trans zero_lt_one h1
  have hj0 : c j ≠ 0 := by
    rintro h
    rw [h, map_zero] at hv0
    exact lt_irrefl _ hv0
  have ha : ∀ k, c k / c j ∈ A := fun k => by
    rw [← A.valuation_le_one_iff, map_div₀, div_le_one₀ hv0]
    exact hj k (Finset.mem_univ k)
  let a : ι → A := fun k => ⟨c k / c j, ha k⟩
  have key : ∑ k, IsLocalRing.residue A (a k) • map (Int.castRingHom (IsLocalRing.ResidueField A)) (q k) = 0 := by
    ext m
    have e1 : (∑ k, IsLocalRing.residue A (a k) • map (Int.castRingHom (IsLocalRing.ResidueField A)) (q k)).coeff m
        = IsLocalRing.residue A (∑ k, a k * (((q k).coeff m : ℤ) : A)) := by
      simp [coeff_map]
    rw [e1, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    have e2 : ((∑ k, a k * (((q k).coeff m : ℤ) : A) : A) : K)
        = (∑ i, c i • map (Int.castRingHom K) (q i)).coeff m / c j := by
      rw [coeff_sum, Finset.sum_div]
      change A.subtype _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_intCast, coeff_smul, coeff_map]
      simp only [a, ValuationSubring.coe_subtype, smul_eq_mul, eq_intCast]
      ring
    rw [e2, map_div₀, div_lt_one₀ hv0]
    exact lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr (hc m)) h1
  have h0 := Fintype.linearIndependent_iff.mp hq _ key j
  have : a j = 1 := Subtype.ext (div_self hj0)
  rw [this, map_one] at h0
  exact one_ne_zero h0

theorem integral_of_indep {K σ ι : Type} [Field K] [NumberField K] [Fintype ι] (q : ι → MvPolynomial σ ℤ)
    (hq : ∀ (k : Type) [Field k], LinearIndependent k (fun i => map (Int.castRingHom k) (q i)))
    (c : ι → K) (hc : ∀ m, IsIntegral ℤ ((∑ i, c i • map (Int.castRingHom K) (q i)).coeff m)) (i : ι) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c i := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K (c i) fun v => ?_
  refine mem_valuationSubring_of_indep (v.valuation K).valuationSubring q (hq _) c (fun m => ?_) i
  exact v.valuation_le_one (K := K) (⟨_, hc m⟩ : 𝓞 K)

def ssZ (n : ℕ) (ν : Fin n → ℕ) : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℤ :=
  (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose

theorem ssZ_indep (k : Type) [Field k] (n : ℕ) (ν : Fin n → ℕ) :
    LinearIndependent k (fun m => map (Int.castRingHom k) (ssZ n ν m)) := by
  have h : ∀ m, (Formalism.GradedWeylDivisibility.colLex n n).degree (map (Int.castRingHom k) (ssZ n ν m)) = m.1 ∧
      (Formalism.GradedWeylDivisibility.colLex n n).leadingCoeff (map (Int.castRingHom k) (ssZ n ν m)) = 1 := fun m => by
    obtain ⟨hd, -, N, sz, hsz, I, -, hI, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.2 m
    have hb' : ssZ n ν m = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
    have hd' : (Formalism.GradedWeylDivisibility.colLex n n).degree (ssZ n ν m) = m.1 := hd
    rw [hb', (Formalism.GradedWeylDivisibility.column_lex_bideterminant ℤ n n N sz hsz I hI).1] at hd'
    rw [hb', Formalism.GradedWeylDivisibility.ldlat_map_bidet, ← hd']
    exact Formalism.GradedWeylDivisibility.column_lex_bideterminant k n n N sz hsz I hI
  refine Formalism.GradedWeylDivisibility.ldbasis_linearIndependent (Formalism.GradedWeylDivisibility.colLex n n) _ (fun m m' e => ?_) fun m => (h m).2
  exact Subtype.ext ((h m).1.symm.trans (e.trans (h m').1))

theorem ssZ_span (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ) :
    Submodule.span K (Set.range fun m => map (Int.castRingHom K) (ssZ n ν m)) = Formalism.GradedWeylDivisibility.dualWeyl K n n ν := by
  have h := (Formalism.GradedWeylDivisibility.nablaLKBasis ℤ K (algebraMap ℤ K).injective_int n n ν (ssZ n ν) _
    (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1 1 (by simp)).2
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) ((1 : Matrix (Fin n) (Fin n) K)⁻¹) = AlgHom.id K _ := by
    rw [inv_one]
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite C]
  rw [h1] at h
  exact h

theorem ssZ_mem (n : ℕ) (ν : Fin n → ℕ) (m) : ssZ n ν m ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
  rw [← (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1.2.1]
  exact Submodule.subset_span ⟨m, rfl⟩

variable {Ix : Type} [Fintype Ix] {n : ℕ}

def prodZ (lam : Ix → DomWeight n) (i : VVIdx lam) : MvPolynomial (Ix × Fin n × Fin n) ℤ :=
  ∏ t, Formalism.GradedWeylDivisibility.blockEmb ℤ t (ssZ n (lam t).natW (i t))

theorem map_prodZ (k : Type) [CommRing k] (lam : Ix → DomWeight n) (i : VVIdx lam) :
    map (Int.castRingHom k) (prodZ lam i) =
      ∏ t, Formalism.GradedWeylDivisibility.blockEmb k t (map (Int.castRingHom k) (ssZ n (lam t).natW (i t))) := by
  simp only [prodZ, map_prod, Formalism.GradedWeylDivisibility.blockEmb, map_rename]

theorem prodZ_basis (k : Type) [Field k] (lam : Ix → DomWeight n) :
    LinearIndependent k (fun i => map (Int.castRingHom k) (prodZ lam i)) ∧
      Submodule.span k (Set.range fun i => map (Int.castRingHom k) (prodZ lam i)) =
        Formalism.GradedWeylDivisibility.tensorLat k k fun t =>
          Submodule.span k (Set.range fun m => map (Int.castRingHom k) (ssZ n (lam t).natW m)) := by
  simp only [map_prodZ]
  exact Formalism.GradedWeylDivisibility.tensorBasis k k Ix n n (fun t => Formalism.GradedWeylDivisibility.ssIdx n n (lam t).natW) _
    (fun t m => map (Int.castRingHom k) (ssZ n (lam t).natW m)) (fun t => ssZ_indep k n _) (fun _ => rfl)

theorem prodZ_mem (K : Type) [Field K] [NumberField K] (lam : Ix → DomWeight n) (i : VVIdx lam) :
    map (Int.castRingHom K) (prodZ lam i) ∈ nabStd K lam := by
  rw [map_prodZ]
  refine Submodule.subset_span ⟨_, fun t => ?_, rfl⟩
  refine ⟨map (Int.castRingHom (𝓞 K)) (ssZ n (lam t).natW (i t)),
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ _ (ssZ_mem n _ _), ?_⟩
  change map (algebraMap (𝓞 K) K) _ = _
  rw [map_map]
  congr 2

theorem map_detProd (k : Type) [CommRing k] (e : Ix → ℕ) :
    map (Int.castRingHom k) (∏ t, (gen ℤ n t).det ^ e t) = ∏ t, (gen k n t).det ^ e t := by
  simp only [map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 2
  ext a s : 2
  simp [gen]

theorem detProd_ne_zero (k : Type) [Field k] (e : Ix → ℕ) : (∏ t, (gen k n t).det ^ e t) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ fun h => ?_
  have h2 := congrArg (eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) k) v.2.1 v.2.2) h
  rw [RingHom.map_det, map_zero] at h2
  have h3 : (eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) k) v.2.1 v.2.2).mapMatrix (gen k n t)
      = 1 := by
    ext a s
    simp [gen]
  rw [h3, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem mem_nabStd_of_det_mul_integral : ∀ (K : Type) [Field K] [NumberField K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) (e : Ix → ℕ), ∀ F ∈ VV K lam,
    (∀ m, IsIntegral ℤ (((∏ t, (gen K n t).det ^ e t) * F).coeff m)) → F ∈ nabStd K lam := by
  intro K _ _ Ix _ n lam e F hF hint
  have hV : Submodule.span K (Set.range fun i => map (Int.castRingHom K) (prodZ lam i)) = VV K lam := by
    rw [(prodZ_basis K lam).2]
    simp only [ssZ_span]
    rfl
  rw [← hV, Submodule.mem_span_range_iff_exists_fun] at hF
  obtain ⟨c, rfl⟩ := hF
  have h := integral_of_indep (fun i => (∏ t, (gen ℤ n t).det ^ e t) * prodZ lam i) (fun k _ => by
      simp only [map_mul, map_detProd]
      exact (prodZ_basis k lam).1.map' (LinearMap.mulLeft k (∏ t, (gen k n t).det ^ e t))
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ (detProd_ne_zero k e)))) c (fun m => by
      have := hint m
      rw [Finset.mul_sum] at this
      simpa only [map_mul, map_detProd, mul_smul_comm] using this)
  choose a ha using h
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← ha i, algebraMap_smul]
  exact Submodule.smul_mem _ _ (prodZ_mem K lam i)

end GlobalTheory.DetSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemOfForallLocP
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.StdNab

open IsDedekindDomain

theorem mem_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x a := by
  refine ⟨fun hx a => GlobalTheory.NabStab.int_of_mem_colLat_one hx a, fun h => ?_⟩
  choose y hy using h
  have hx : x = ∑ j, y j • fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Units.val_one, Matrix.one_apply, Algebra.smul_def, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hy]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem tauLat_stdLat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {Ix : Type} {n : ℕ}
    (emb : Ix → E →+* K) (t : Ix) : tauLat emb t (stdLat E n) = colLat (1 : GL (Fin n) K) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine (mem_colLat_one _).2 fun a => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx a (Set.mem_univ a))
    refine ⟨⟨emb t (x a), ?_⟩, rfl⟩
    rw [← hy]
    exact map_isIntegral_int (emb t) y.isIntegral_coe
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨fun a => if a = j then 1 else 0, fun a _ => ?_, ?_⟩
    · by_cases h : a = j
      · exact Submodule.mem_one.2 ⟨1, by simp [h]⟩
      · exact Submodule.mem_one.2 ⟨0, by simp [h]⟩
    · funext a
      by_cases h : a = j <;> simp [h, Matrix.one_apply]

theorem dualFr_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} :
    dualFr (colLat (1 : GL (Fin n) K)) = colLat (1 : GL (Fin n) K) := by
  ext φ
  constructor
  · intro h
    refine (mem_colLat_one _).2 fun a => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (h _ (Submodule.subset_span ⟨a, rfl⟩))
    refine ⟨y, ?_⟩
    rw [hy]
    simp [dotProduct, Matrix.one_apply]
  · intro h x hx
    choose y hy using (mem_colLat_one _).1 h
    choose z hz using (mem_colLat_one _).1 hx
    refine Submodule.mem_one.2 ⟨∑ a, y a * z a, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hy, hz, dotProduct]

theorem mem_of_forall_locP {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module (𝓞 K) W]
    (T : Submodule (𝓞 K) W) (x : W) (h : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : x ∈ T := by
  by_contra hx
  let I : Ideal (𝓞 K) := T.comap (LinearMap.toSpanSingleton (𝓞 K) W x)
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : 𝓞 K) ∈ I := hI ▸ Submodule.mem_top
    exact hx (by simpa [I] using h1)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
  exact hs (hIm (show s ∈ I from hsx))

theorem polyAction_one₂ {K Ix : Type} [Field K] [Fintype Ix] {n : ℕ} (lam : Ix → DomWeight n) (F : Pol K Ix n) :
    Formalism.L2.DIV.actP lam 1 F = F := by
  simp [Formalism.L2.DIV.actP, detTwK_one, trAct_one]

theorem nabP_colLat_one {K Ix : Type} [Field K] [NumberField K] [Fintype Ix] {n : ℕ} (lam : Ix → DomWeight n) :
    nabP lam (fun _ => colLat (1 : GL (Fin n) K)) = nabStd K lam := by
  ext F
  constructor
  · intro hF
    refine mem_of_forall_locP _ _ fun w => ?_
    have h := nabP_colLat_le lam 1 w hF
    rwa [inv_one, polyAction_one₂] at h
  · intro hF
    simp only [nabP, transLat, Submodule.mem_iInf]
    intro w B hB
    exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd K Ix n lam w B⁻¹ (fun t => GlobalTheory.NabStab.isBasisAt_inv w (B t) (hB t)) F
      ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

theorem eval_extremal {R : Type} [CommRing R] {n : ℕ} (lam : DomWeight n) :
    eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0) (extremal R n lam) = 1 := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  have h : ∀ (k : ℕ) (h1 h2 : k ≤ n),
      (eval (fun v : Fin n × Fin n => if v.1 = v.2 then (1 : R) else 0)).mapMatrix
        (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [Matrix.one_apply, Fin.ext_iff]
  rw [h, Matrix.det_one, one_pow]

theorem nabAtr_stdLat : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (Ix : Type) [Fintype Ix] (n : ℕ) (emb : Ix → E →+* K) (lam : Ix → DomWeight n), (∀ F : VV K lam, F ∈ nabAtr emb lam (stdLat E n) ↔ (F : Pol K Ix n) ∈ nabStd K lam) ∧ (ten fun t => extremal K n (lam t)) ∈ nabStd K lam ∧ ∀ x : K, x • (ten fun t => extremal K n (lam t)) ∈ nabStd K lam → ∃ o : 𝓞 K, x = (o : K) := by
  intro E K _ _ _ _ Ix _ n emb lam
  refine ⟨fun F => ?_, ?_, fun x hx => ?_⟩
  · unfold nabAtr nabK
    simp only [tauLat_stdLat, dualFr_colLat_one, nabP_colLat_one]
    rfl
  · refine Submodule.subset_span ⟨fun t => extremal K n (lam t), fun t => ?_, rfl⟩
    exact ⟨extremal (𝓞 K) n (lam t), Formalism.GradedWeylDivisibility.hwMem (𝓞 K) n n le_rfl _ (natW_antitone (lam t)),
      map_extremal _ n (lam t)⟩
  · obtain ⟨Q, hQ⟩ := GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hx
    let e : ∀ (R : Type) [CommRing R], Ix × Fin n × Fin n → R := fun R _ v => if v.2.1 = v.2.2 then 1 else 0
    refine ⟨eval (e (𝓞 K)) Q, ?_⟩
    have h1 : eval (e K) (ten fun t => extremal K n (lam t)) = 1 := by
      unfold ten
      rw [map_prod]
      refine Finset.prod_eq_one fun t _ => ?_
      unfold Formalism.GradedWeylDivisibility.blockEmb
      rw [eval_rename]
      exact eval_extremal (lam t)
    have h2 : eval (e K) (map (algebraMap (𝓞 K) K) Q) = algebraMap (𝓞 K) K (eval (e (𝓞 K)) Q) := by
      have h3 : e K = algebraMap (𝓞 K) K ∘ e (𝓞 K) := by
        funext v
        by_cases h : v.2.1 = v.2.2 <;> simp [e, h]
      rw [h3, ← map_eval]
    have h4 := congrArg (eval (e K)) hQ
    rw [GlobalTheory.NabStab.toK_apply, h2, smul_eval, h1, mul_one] at h4
    exact h4.symm

end GlobalTheory.StdNab
end

