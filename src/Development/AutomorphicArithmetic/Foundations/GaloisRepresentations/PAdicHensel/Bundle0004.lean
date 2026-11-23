module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScale
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma val_alg (v : HeightOneSpectrum ℤ) (s : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) s) = v.valuation ℚ s :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v s

private lemma exists_gen (v : HeightOneSpectrum ℤ) :
    ∃ q : ℕ, q ≠ 0 ∧ v.asIdeal = Ideal.span {(q : ℤ)} := by
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal v.asIdeal
  have hg' : v.asIdeal = Ideal.span {g} := hg
  refine ⟨g.natAbs, ?_, ?_⟩
  · intro h0
    apply v.ne_bot
    rw [hg', Int.natAbs_eq_zero.mp h0]
    simp
  · rw [hg', Ideal.span_singleton_eq_span_singleton]
    exact Int.associated_natAbs g

private lemma val_nat (v : HeightOneSpectrum ℤ) (q : ℕ) :
    v.valuation ℚ (q : ℚ) = v.intValuation (q : ℤ) := by
  rw [← v.valuation_of_algebraMap (K := ℚ)]
  simp

private lemma val_self (v : HeightOneSpectrum ℤ) {q : ℕ} (h0 : q ≠ 0)
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) : v.valuation ℚ (q : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [val_nat]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast h0) h

private lemma val_other (v w : HeightOneSpectrum ℤ) {q : ℕ}
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) (hne : w ≠ v) : w.valuation ℚ (q : ℚ) = 1 := by
  rw [val_nat]
  apply le_antisymm (w.intValuation_le_one _)
  rw [← not_lt, w.intValuation_lt_one_iff_mem]
  intro hm
  apply hne
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [h, Ideal.span_le]
    simpa using hm
  exact HeightOneSpectrum.ext ((v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

private lemma finite_ne_one (p : ℕ) (t : (AfP p)ˣ) :
    {v : AwayP p | Valued.v (AfP.eval v (t : AfP p)) ≠ 1}.Finite := by
  have ht := (t : AfP p).2
  have hti := ((t⁻¹ : (AfP p)ˣ) : AfP p).2
  refine (Filter.eventually_cofinite.mp (ht.and hti)).subset ?_
  intro v hv hboth
  apply hv
  obtain ⟨h1, h2⟩ := hboth
  have h1' : Valued.v (AfP.eval v (t : AfP p)) ≤ 1 := h1
  have h2' : Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) ≤ 1 := h2
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  apply le_antisymm h1'
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hm.symm
    _ ≤ Valued.v (AfP.eval v (t : AfP p)) * 1 := mul_le_mul_right h2' _
    _ = _ := mul_one _

private lemma val_ne_zero (p : ℕ) (t : (AfP p)ˣ) (v : AwayP p) :
    Valued.v (AfP.eval v (t : AfP p)) ≠ 0 := by
  intro h
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [h, zero_mul] at hm
  exact zero_ne_one hm

theorem UpperTheory.Gal.G1.pScale :
    Scale := by
  intro p t
  classical
  choose q hq0 hq using fun v : AwayP p => exists_gen v.1
  let n : AwayP p → ℤ := fun v => WithZero.log (Valued.v (AfP.eval v (t : AfP p)))
  let S := (finite_ne_one p t).toFinset
  refine ⟨∏ v ∈ S, ((q v : ℚ) ^ (-n v)), ?_, ?_⟩
  · apply Finset.prod_pos
    intro v _
    apply zpow_pos
    exact_mod_cast Nat.pos_of_ne_zero (hq0 v)
  · intro w
    rw [val_alg, map_prod]
    have hterm : ∀ v ∈ S, w.1.valuation ℚ ((q v : ℚ) ^ (-n v)) =
        if v = w then WithZero.exp (n v) else 1 := by
      intro v _
      rw [map_zpow₀]
      split_ifs with hvw
      · subst hvw
        rw [val_self v.1 (hq0 v) (hq v), ← WithZero.exp_zsmul]
        simp
      · rw [val_other v.1 w.1 (hq v) (fun h => hvw (Subtype.ext h.symm)), _root_.one_zpow]
    rw [Finset.prod_congr rfl hterm, Finset.prod_ite_eq']
    split_ifs with hw
    · exact (WithZero.exp_log (val_ne_zero p t w)).symm
    · have : ¬ Valued.v (AfP.eval w (t : AfP p)) ≠ 1 := by
        intro h
        apply hw
        simpa [S] using h
      exact not_not.mp this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitCongr
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem splitCore {n : ℕ} {B : Type*} [CommRing B] (s : B →+* B) (e e' : B)
    (hee' : e * e' = 0) (hsum : e + e' = 1) (hse : s e = e') (hse' : s e' = e)
    (G G' Gi : Matrix (Fin n) (Fin n) B) (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hG : (G.map s)ᵀ = G) (hG' : (G'.map s)ᵀ = G') (hdet : IsUnit G'.det) :
    ∃ P : Matrix (Fin n) (Fin n) B, IsUnit P.det ∧ G' = Pᵀ * G * P.map s := by
  classical
  have hs1 : (G.map s) * (Gi.map s) = 1 := by
    rw [← Matrix.map_mul, hGGi, Matrix.map_one s s.map_zero s.map_one]
  have hsGi : (Gi.map s)ᵀ = Gi := by
    have h2 : (Gi.map s)ᵀ * G = 1 := by
      have := congrArg Matrix.transpose hs1
      rwa [Matrix.transpose_mul, hG, Matrix.transpose_one] at this
    calc (Gi.map s)ᵀ = (Gi.map s)ᵀ * (G * Gi) := by rw [hGGi, Matrix.mul_one]
      _ = ((Gi.map s)ᵀ * G) * Gi := by rw [Matrix.mul_assoc]
      _ = Gi := by rw [h2, Matrix.one_mul]
  have hA : ((G' * Gi)ᵀ).map s = Gi * G' := by
    rw [Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hsGi, hG']
  have hee : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [hsum, hee', mul_one, sub_zero]
  have he'e' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e * e' := by ring
      _ = e' := by rw [hsum, hee', mul_one, sub_zero]
  have he'e : e' * e = 0 := by rw [mul_comm, hee']
  have hu : IsUnit G'.det := hdet
  set A : Matrix (Fin n) (Fin n) B := (G' * Gi)ᵀ with hAdef
  set Ai : Matrix (Fin n) (Fin n) B := (G * G'⁻¹)ᵀ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc G'⁻¹,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, hGGi, Matrix.transpose_one]
  refine ⟨e • A + e' • 1, ?_, ?_⟩
  · apply Matrix.isUnit_det_of_right_inverse (B := e • Ai + e' • 1)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
      Matrix.mul_one, Matrix.one_mul, hAAi, hee, he'e', hee', he'e, zero_smul, add_zero, zero_add]
    first
      | rw [← add_smul, hsum, one_smul]
      | rw [add_comm, ← add_smul, hsum, one_smul]
  · have hP : (e • A + e' • (1 : Matrix (Fin n) (Fin n) B)).map s = e' • (Gi * G') + e • 1 := by
      rw [Matrix.map_add _ (map_add s), Matrix.map_smul' _ _ _ (map_mul s),
        Matrix.map_smul' _ _ _ (map_mul s), hA, Matrix.map_one s s.map_zero s.map_one, hse, hse']
    rw [hP]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hAdef,
      Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hGiG, hGGi,
      ← Matrix.mul_assoc Gi G, ← Matrix.mul_assoc G Gi, hee, he'e', hee', he'e, zero_smul,
      add_zero, zero_add]
    first
      | rw [← add_smul, hsum, one_smul]
      | rw [add_comm, ← add_smul, hsum, one_smul]

theorem UpperTheory.Gal.G1.pSplitCongr :
    SplitCongr := by
  intro E _ _ _ n N N' hN hN' hN0 hN'0 K _ _ θ D hD hθc hθ r hr
  set σ := IsCMField.complexConj E with hσeq
  set R : E →ₐ[maximalRealSubfield E] K ⊗[maximalRealSubfield E] E :=
    Algebra.TensorProduct.includeRight with hReq
  set L : K →ₐ[maximalRealSubfield E] K ⊗[maximalRealSubfield E] E :=
    Algebra.TensorProduct.includeLeft with hLeq
  set sB := GlobalTheory.HermGlobal.baseConj σ K with hsBeq
  have hsL : ∀ a : K, sB (L a) = L a := by
    intro a
    simp [hsBeq, hLeq, GlobalTheory.HermGlobal.baseConj]
  have hsR : ∀ x : E, sB (R x) = R (σ x) := by
    intro x
    simp [hsBeq, hReq, GlobalTheory.HermGlobal.baseConj]
  have hDE : (D : E) ≠ 0 := Int.cast_ne_zero.mpr hD
  set w := L r * R (θ / D) with hweq
  have hww : w * w = 1 := by
    have h1 : L r * L r = R (D : E) := by
      rw [← map_mul, ← sq, hr, map_intCast, map_intCast]
    calc w * w = (L r * L r) * (R (θ / D) * R (θ / D)) := by rw [hweq]; ring
      _ = R ((D : E) * (θ / D * (θ / D))) := by rw [h1, ← map_mul, ← map_mul]
      _ = 1 := by
        rw [div_mul_div_comm, ← sq θ, hθ]
        rw [show (D : E) * ((D : E) / (D * D)) = 1 by field_simp]
        exact map_one R
  have hsw : sB w = -w := by
    rw [hweq, map_mul, hsL, hsR, map_div₀, hθc, map_intCast, neg_div, map_neg, mul_neg]
  set h := R (2 : E)⁻¹ with hheq
  have hsh : sB h = h := by
    rw [hheq, hsR, map_inv₀, map_ofNat]
  have h2 : h * 2 = 1 := by
    rw [hheq, show (2 : K ⊗[maximalRealSubfield E] E) = R 2 from (map_ofNat R 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero), map_one]
  set e := h * (1 + w) with heeq
  set e' := h * (1 - w) with he'eq
  have hee' : e * e' = 0 := by
    calc e * e' = h * h * (1 - w * w) := by rw [heeq, he'eq]; ring
      _ = 0 := by rw [hww, sub_self, mul_zero]
  have hsum : e + e' = 1 := by
    calc e + e' = h * 2 := by rw [heeq, he'eq]; ring
      _ = 1 := h2
  have hse : sB e = e' := by
    rw [heeq, he'eq, map_mul, map_add (f := _), map_one, hsh, hsw, sub_eq_add_neg]
  have hse' : sB e' = e := by
    rw [heeq, he'eq, map_mul, map_sub, map_one, hsh, hsw, sub_neg_eq_add]
  have hNu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN0
  have hN'u : IsUnit N'.det := isUnit_iff_ne_zero.mpr hN'0
  have hGGi : N.map R * N⁻¹.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv N hNu, Matrix.map_one _ (map_zero R) (map_one R)]
  have hGiG : N⁻¹.map R * N.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul N hNu, Matrix.map_one _ (map_zero R) (map_one R)]
  have hG'G'i : N'.map R * N'⁻¹.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv N' hN'u, Matrix.map_one _ (map_zero R) (map_one R)]
  have hG : ((N.map R).map sB.toRingHom)ᵀ = N.map R := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact (hsR _).trans (congrArg R (hN b a))
  have hG' : ((N'.map R).map sB.toRingHom)ᵀ = N'.map R := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact (hsR _).trans (congrArg R (hN' b a))
  obtain ⟨P, hP, hPe⟩ := splitCore sB.toRingHom e e' hee' hsum hse hse' (N.map R) (N'.map R)
    (N⁻¹.map R) hGGi hGiG hG hG' (Matrix.isUnit_det_of_right_inverse hG'G'i)
  refine ⟨P, hP, ?_⟩
  exact hPe
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PTrivMat
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pTrivMat :
    TrivMat := by
  intro E _ _ _ n H hH hH' hd R _ _ K _ _ ψ β x t hx
  let L := K ⊗[↥(maximalRealSubfield E)] E
  letI : Algebra ℚ L := ((algebraMap K L).comp (ψ.comp (algebraMap ℚ R))).toAlgebra
  let s : R →+* L := (algebraMap K L).comp ψ
  let e : E →+* L := Algebra.TensorProduct.includeRight.toRingHom
  let f : R →ₐ[ℚ] Matrix (Fin n) (Fin n) L := ((algebraMap L (Matrix (Fin n) (Fin n) L)).comp s).toRatAlgHom
  let g : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) L := (e.mapMatrix).toRatAlgHom
  have hfg : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes (s a) (g b)
  let φ := Algebra.TensorProduct.lift f g hfg
  have hφ : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E), φ (r ⊗ₜ m) = s r • m.map e := by
    intro r m
    show f r * g m = _
    rw [Algebra.smul_def]
    rfl
  let c := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  have hc1 : ∀ y : E, c (e y) = e (cj E y) := by
    intro y
    simp [c, e, GlobalTheory.HermGlobal.baseConj]
  have hc2 : ∀ r : R, c (s r) = s r := by
    intro r
    show c (ψ r ⊗ₜ 1) = ψ r ⊗ₜ 1
    simp [c, GlobalTheory.HermGlobal.baseConj]
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  have hinv : (H.map e)⁻¹ = H⁻¹.map e := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hright : H.map e * H⁻¹.map e = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hmap : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E),
      (s r • m.map e).map c = s r • (m.map (cj E)).map e := by
    intro r m
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc1, hc2]
  have hH2 : H.map ⇑(↑(IsCMField.complexConj E) : E →+* E) = H := hH'
  have hstar : ∀ y, φ (MulOpposite.unop ((starT (hermStar H hd) R) y)) =
      H⁻¹.map e * ((φ y).map c)ᵀ * H.map e := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [starT_tmul, hermStar_apply, hφ, hφ, hmap, hH2, Matrix.map_mul, Matrix.map_mul,
        Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]
    | add a b ha hb =>
      simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
      rw [Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  refine ⟨φ x, ?_, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (x.isUnit.map φ)
  · have key := congrArg φ hx
    rw [map_mul, map_mul, hstar, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, hφ, hφ, map_one, one_smul, Matrix.map_one _ (map_zero e) (map_one e)] at key
    show φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ = ψ t • H⁻¹.map e
    have hsm : ψ t • H⁻¹.map e = s t • H⁻¹.map e := (algebraMap_smul L (ψ t) _).symm
    rw [hsm]
    calc φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ
        = φ x * β.map e * (H⁻¹.map e * ((φ x).map c)ᵀ * H.map e) * H⁻¹.map e := by
          rw [Matrix.map_mul]
          simp only [Matrix.mul_assoc, hright, Matrix.mul_one]
      _ = s t • H⁻¹.map e := by
          rw [key, Matrix.smul_mul, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PUnitCls
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pUnitCls :
    Scale → ZUnitNorm → ZSqFin → UnitCls := by
  intro hScale hNorm hSq p D hD
  choose sc hsc0 hsc using hScale p
  choose m κ hκ using hSq
  have hfin : {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 * D : ℤ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      omega
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.2 hv
  haveI : Finite {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal} := hfin.to_subtype
  refine ⟨(v : {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal}) → Option (Fin (m v.1)),
    inferInstance, fun t v => if h : (v.1 : HeightOneSpectrum ℤ).asIdeal ≠ Ideal.span {(p : ℤ)}
      then some (κ v.1 (AfP.eval (⟨v.1, h⟩ : AwayP p) (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t)))
      else none, ?_⟩
  intro t t' hk
  refine ⟨sc t' / sc t, div_pos (hsc0 t') (hsc0 t), fun v => ?_⟩
  have hunit : ∀ r : (AfP p)ˣ, AfP.eval v (r : AfP p) ≠ 0 := by
    intro r
    have h1 : AfP.eval v (r : AfP p) * AfP.eval v ((r⁻¹ : (AfP p)ˣ) : AfP p) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hsne : ∀ r : (AfP p)ˣ,
      algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc r) ≠ 0 :=
    fun r => (map_ne_zero _).2 (hsc0 r).ne'
  have hval : ∀ r : (AfP p)ˣ, Valued.v (AfP.eval v (r : AfP p) /
      algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc r)) = 1 := by
    intro r
    rw [map_div₀, hsc r v, div_self]
    exact (Valuation.ne_zero_iff _).2 (hsne r)
  suffices hs : ∃ x y : HeightOneSpectrum.adicCompletion ℚ v.1,
      AfP.eval v (t' : AfP p) / algebraMap ℚ _ (sc t') =
        AfP.eval v (t : AfP p) / algebraMap ℚ _ (sc t) * (x ^ 2 - (D : _) * y ^ 2) by
    obtain ⟨x, y, hxy⟩ := hs
    refine ⟨x, y, ?_⟩
    rw [map_div₀]
    have e := hsne t
    have e' := hsne t'
    rw [div_eq_iff e'] at hxy
    rw [hxy]
    field_simp
  by_cases h2 : (2 * D : ℤ) ∈ v.1.asIdeal
  · have hk' := congrFun hk ⟨v.1, h2⟩
    dsimp only at hk'
    rw [dite_eq_left v.2, dite_eq_left v.2] at hk'
    have hk'' := Option.some.inj hk'
    obtain ⟨z, hz⟩ := hκ v.1 _ _ (hval t) (hval t') hk''
    refine ⟨z, 0, ?_⟩
    rw [hz]
    ring
  · have hne : AfP.eval v (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t) ≠ 0 :=
      div_ne_zero (hunit t) (hsne t)
    have hv1 : Valued.v ((AfP.eval v (t' : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t')) /
        (AfP.eval v (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t))) = 1 := by
      rw [map_div₀, hval t, hval t', div_one]
    obtain ⟨x, y, hxy⟩ := hNorm v.1 D h2 _ hv1
    refine ⟨x, y, ?_⟩
    rw [← hxy, mul_div_assoc', mul_div_cancel_left₀ _ hne]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZSqFin
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private theorem norm_padicEquiv_of_valued_eq_one (v : HeightOneSpectrum ℤ) (u : v.adicCompletion ℚ)
    (hu : Valued.v u = 1) : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hmem : ∀ w : v.adicCompletion ℚ, Valued.v w ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v w‖ ≤ 1 := by
    intro w hw
    have hw' : w ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hw
    have := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hw'
    simpa using this
  have h1 := hmem u hu.le
  have h2 := hmem u⁻¹ (by rw [map_inv₀, hu, inv_one])
  have h3 : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ *
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hu0, map_one, norm_one]
  have h4 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u)
  have h5 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹)
  nlinarith

theorem UpperTheory.Gal.G1.pZSqFin :
    PadicSqFin → ZSqFin := by
  intro hP v
  obtain ⟨m, κ, hκ⟩ := hP (Rat.HeightOneSpectrum.primesEquiv v).1
  refine ⟨m, fun u => κ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u), ?_⟩
  intro u u' hu hu' huu
  obtain ⟨x, hx⟩ := hκ _ _ (norm_padicEquiv_of_valued_eq_one v u hu)
    (norm_padicEquiv_of_valued_eq_one v u' hu') huu
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x, ?_⟩
  have h := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hx
  rw [map_mul, map_pow] at h
  simpa using h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZUnitNorm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pZUnitNorm :
    PadicUnitNorm → ZUnitNorm := by
  intro hP v D hv u hu
  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hint : ∀ z : v.adicCompletion ℚ, Valued.v z ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v z‖ ≤ 1 := by
    intro z hz
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo
      ((HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v).2 hz)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hn : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
    apply le_antisymm (hint u hu.le)
    have h1 := hint u⁻¹ (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀, norm_inv] at h1
    have hne : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u ≠ 0 := fun h =>
      hu0 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
        (h.trans (map_zero _).symm))
    exact (inv_le_one₀ (norm_pos_iff.2 hne)).1 h1
  have hdiv : ¬ ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ∣ 2 * D := by
    intro hd
    apply hv
    have hm : 2 * D ∈ Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
      Ideal.mem_span_singleton.2 hd
    rw [Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_map_of_equiv] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hid : Rat.IsIntegralClosure.intEquiv ℤ x = x := by
      simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ : ℤ →+* ℤ) x
    rw [hid] at hxe
    rw [← hxe]
    exact hx
  obtain ⟨x, y, hxy⟩ := hP _ D hdiv _ hn
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x,
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm y, ?_⟩
  have h2 := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hxy
  simpa using h2
end

