module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.OneTmulMemCompletedLatticeIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem val_p_eq_one {p : ℕ} [Fact p.Prime] (v : AwayP p) :
    v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hp
  apply v.2
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  exact (hmax.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hp)).symm

private theorem isIntAf_of_pow_mul {p : ℕ} [Fact p.Prime] (q : ℚ) (r : ℕ) (c : ℤ)
    (h : ((p ^ r : ℕ) : ℚ) * q = c) : IsIntAf (algebraMap ℚ (AfP p) q) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hc : v.1.valuation ℚ (c : ℚ) ≤ 1 := by
    simpa using v.1.valuation_le_one (K := ℚ) c
  have hp : v.1.valuation ℚ ((p ^ r : ℕ) : ℚ) = 1 := by
    have h1 := val_p_eq_one v
    rw [eq_intCast] at h1
    push_cast at h1 ⊢
    rw [map_pow, h1, one_pow]
  have hq : v.1.valuation ℚ q ≤ 1 := by
    have h2 := congrArg (v.1.valuation ℚ) h
    rw [map_mul, hp, _root_.one_mul] at h2
    rw [h2]
    exact hc
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
  exact hq

theorem UpperTheory.one_tmul_mem_completedLattice_iff :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (z : VQ D), (1 : AfP p) ⊗ₜ[ℚ] z ∈ LaHat D ↔ ∃ (r : ℕ) (x : D.La), p ^ r • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  intro p _ D z
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  have key : ∀ i, (KNLevel.bA b).repr ((1 : AfP p) ⊗ₜ[ℚ] z) i = algebraMap ℚ (AfP p) (bQ.repr z i) := by
    intro i
    simp [KNLevel.bA, Algebra.TensorProduct.basis_repr_tmul, bQ]
  have hsm : ∀ (r : ℕ) i, bQ.repr (p ^ r • z) i = ((p ^ r : ℕ) : ℚ) * bQ.repr z i := by
    intro r i
    rw [← Nat.cast_smul_eq_nsmul ℚ, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have htm : ∀ (x : D.La) i, bQ.repr ((1 : ℚ) ⊗ₜ[ℤ] x) i = (b.repr x i : ℚ) := by
    intro x i
    simp [bQ, Algebra.TensorProduct.basis_repr_tmul]
  rw [KNLevel.mem_laHat_iff b]
  simp only [key]
  constructor
  · intro h
    choose k a hka using fun i => T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p (bQ.repr z i) (h i)
    let r := ∑ i, k i
    let c : _ → ℤ := fun i => (p : ℤ) ^ (r - k i) * a i
    have hc : ∀ i, ((p ^ r : ℕ) : ℚ) * bQ.repr z i = (c i : ℚ) := by
      intro i
      have hk : k i ≤ r := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hpow : (p : ℚ) ^ r = (p : ℚ) ^ (r - k i) * (p : ℚ) ^ (k i) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      have ha := hka i
      push_cast at ha ⊢
      rw [hpow, _root_.mul_assoc, ha]
      simp [c]
    refine ⟨r, b.equivFun.symm c, ?_⟩
    apply bQ.ext_elem
    intro i
    have hb : b.repr (b.equivFun.symm c) i = c i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hsm, htm, hb]
    exact hc i
  · rintro ⟨r, x, hx⟩ i
    apply isIntAf_of_pow_mul _ r (b.repr x i)
    rw [← hsm, hx, htm]
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.PrimeToPIsogenyOfAdelicEndoPreservingLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

theorem UpperTheory.primeToP_isogeny_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {D' : PLat D.O D.inv} (ψ : D'.La ≃+ D.La) (T : VQ D ≃ₗ[ℚ] VQ D) {j : D'.La →+ VQ D},
        (∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u) → (∀ (c : D.O) u, j (c • u) = actQ D c (j u)) →
        ∀ {f : ℕ → D.La →+ D'.La}, (∀ n : ℕ, 0 < n → n.Coprime p → ∀ (c : D.O) a, ∃ e, f n (c • a) = c • f n a + n • e) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (ψ (f n x)) + n • w) → ∀ b : D.O,
        (T.toLinearMap.baseChange (AfP p)) * A * (actQ D b).baseChange (AfP p) =
          (actQ D b).baseChange (AfP p) * ((T.toLinearMap.baseChange (AfP p)) * A) := by
  intro p _ D D' ψ T j hj hjc f hf A hAL hA b
  let Cq : VQ D →ₗ[ℚ] VQ D := T.symm.toLinearMap ∘ₗ actQ D b ∘ₗ T.toLinearMap
  let Cc : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := Cq.baseChange (AfP p)
  have hC1 : ∀ u, Cq ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = (1 : ℚ) ⊗ₜ[ℤ] ψ (b • u) := by
    intro u
    have h : T ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) = actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) := by
      rw [hj, hj, hjc]
    change T.symm (actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u))) = _
    rw [← h, T.symm_apply_apply]
  have hCt : ∀ (a : AfP p) (u : D'.La), Cc (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) =
      a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) := by
    intro a u
    change Cq.baseChange (AfP p) _ = _
    rw [LinearMap.baseChange_tmul, hC1]
  have hCin : ∀ u, Cc (inAf D (ψ u)) = inAf D (ψ (b • u)) := fun u => hCt 1 u
  have hCL : ∀ v ∈ LaHat D, Cc v ∈ LaHat D := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      obtain ⟨u, rfl⟩ := ψ.surjective x
      rw [hCt]
      exact AddSubgroup.subset_closure ⟨a, ψ (b • u), ha, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hAC : A * (actQ D b).baseChange (AfP p) = Cc * A := by
    refine ext_inAf D fun x => ?_
    have := modZero D ((A * (actQ D b).baseChange (AfP p)) (inAf D x) - (Cc * A) (inAf D x)) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hA n hn hc (b • x)
      obtain ⟨w', hw', e'⟩ := hA n hn hc x
      obtain ⟨z, hz⟩ := hf n hn hc b x
      refine ⟨inAf D (ψ z) + w - Cc w', sub_mem (add_mem (inAf_mem D _) hw) (hCL _ hw'), ?_⟩
      rw [mul_apply_eq_comp, mul_apply_eq_comp, bc_inAf, e, hz, e', map_add (f := _), map_add (f := _), hCin, map_nsmul,
        map_nsmul, inAf_add, inAf_nsmul]
      simp only [smul_add, smul_sub]; abel
    exact sub_eq_zero.1 this
  have hTC : (T.toLinearMap.baseChange (AfP p)) * Cc =
      (actQ D b).baseChange (AfP p) * (T.toLinearMap.baseChange (AfP p)) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a m =>
      change T.toLinearMap.baseChange (AfP p) (Cq.baseChange (AfP p) (a ⊗ₜ[ℚ] m)) =
        (actQ D b).baseChange (AfP p) (T.toLinearMap.baseChange (AfP p) (a ⊗ₜ[ℚ] m))
      simp only [LinearMap.baseChange_tmul]
      congr 1
      change T (T.symm (actQ D b (T m))) = actQ D b (T m)
      exact T.apply_symm_apply _
  rw [_root_.mul_assoc, hAC, ← _root_.mul_assoc, hTC, _root_.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ReMulSignatureIPosOfHermitianTraceFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open scoped ComplexOrder
open UpperTheory.Gal.W2

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private lemma hvAddL {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x x' y : Fin n → ℂ) :
    hv M (x + x') y = hv M x y + hv M x' y := by
  simp [hv, Matrix.mulVec_add, dotProduct_add]

private lemma hvAddR {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y y' : Fin n → ℂ) :
    hv M x (y + y') = hv M x y + hv M x y' := by
  simp [hv, add_dotProduct]

private lemma hvSmulL {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (x y : Fin n → ℂ) :
    hv M (a • x) y = (a : ℂ) * hv M x y := by
  have : a • x = (a : ℂ) • x := by ext i; simp
  rw [this]
  simp [hv, Matrix.mulVec_smul, dotProduct_smul]

private lemma hvSmulR {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (x y : Fin n → ℂ) :
    hv M x (a • y) = (a : ℂ) * hv M x y := by
  have : a • y = (a : ℂ) • y := by ext i; simp
  rw [this]
  simp [hv, star_smul, smul_dotProduct]

private noncomputable def thR (th : VQ D →+ Arch G) : ℝ ⊗[ℚ] VQ D →ₗ[ℝ] Arch G :=
  LinearMap.liftBaseChange ℝ th.toRatLinearMap

private lemma thR_tmul (th : VQ D →+ Arch G) (a : ℝ) (w : VQ D) :
    thR th (a ⊗ₜ w) = a • th w := by
  simp [thR]

private lemma psiR_tm (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  rw [Algebra.smul_def]
  unfold HTGroup.psiR
  erw [Algebra.TensorProduct.lift_tmul]
  rfl

private lemma thR_act (L : Link D G) (th : VQ D →+ Arch G)
    (hrep : ∀ c w v, th (L.rep c w) v = G.psi v c *ᵥ th w v)
    (a : ℝ ⊗[ℚ] G.C) (x : ℝ ⊗[ℚ] VQ D) (v : InfinitePlace G.F) :
    thR th (actOn L.rep ℝ a x) v = G.psiR v a *ᵥ thR th x v := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, ha, hb, Matrix.add_mulVec]
  | tmul r c =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply, hx, hy, Matrix.mulVec_add]
    | tmul s w =>
      have h : actOn L.rep ℝ (r ⊗ₜ c) (s ⊗ₜ w) = (r * s) ⊗ₜ (L.rep c w) := by
        simp [actOn, Algebra.TensorProduct.lift_tmul, Module.End.baseChangeHom, Algebra.ofId_apply,
          Module.algebraMap_end_apply]
        change r • (s ⊗ₜ[ℚ] (L.rep c w)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul]
      rw [h, thR_tmul, thR_tmul, psiR_tm, Pi.smul_apply, Pi.smul_apply, hrep,
        Matrix.smul_mulVec, Matrix.mulVec_smul, mul_smul]

private lemma form_ext (th : VQ D →+ Arch G) (lam : InfinitePlace G.F → ℂ)
    (hform : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re)
    (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ x y
      = ∑ v, 2 * (lam v * hv (G.gram v) (thR th x v) (thR th y v)).re := by
  induction x using TensorProduct.induction_on with
  | zero => simp [hv]
  | add x x' hx hx' =>
    simp only [map_add (f := _), LinearMap.add_apply, hx, hx', Pi.add_apply, hvAddL, mul_add, Complex.add_re,
      Finset.sum_add_distrib]
  | tmul a u =>
    induction y using TensorProduct.induction_on with
    | zero => simp [hv]
    | add y y' hy hy' =>
      simp only [map_add (f := _), hy, hy', Pi.add_apply, hvAddR, mul_add, Complex.add_re, Finset.sum_add_distrib]
    | tmul b w =>
      rw [LinearMap.BilinForm.baseChange_tmul, thR_tmul, thR_tmul]
      have hterm : ∀ v, 2 * (lam v * hv (G.gram v) ((a • th u) v) ((b • th w) v)).re
          = (a * b) * (2 * (lam v * hv (G.gram v) (th u v) (th w v)).re) := by
        intro v
        have e : lam v * hv (G.gram v) ((a • th u) v) ((b • th w) v)
            = ((a * b : ℝ) : ℂ) * (lam v * hv (G.gram v) (th u v) (th w v)) := by
          rw [Pi.smul_apply, Pi.smul_apply, hvSmulL, hvSmulR]
          push_cast
          ring
        rw [e, Complex.re_ofReal_mul]
        ring
      rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.mul_sum, ← hform, Rat.smul_def]
      ring

end

theorem UpperTheory.re_mul_signature_I_pos_of_hermitian_trace_formula :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (th : VQ D →+ Arch G) (lam : InfinitePlace G.F → ℂ), (∀ c w v, th (L.rep c w) v = G.psi v c *ᵥ th w v) → (∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re) → Submodule.span ℝ (Set.range th) = ⊤ → (∀ v, (starRingEnd ℂ) (lam v) = -lam v) → ∀ v, 0 < (lam v * sgnV L v * Complex.I).re := by
  intro p _ D G L th lam hrep hform hspan _ v
  obtain ⟨J, -, -, hpos, hPD⟩ := L.orient
  have hsurj : Function.Surjective (thR th) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ w, by simp [thR_tmul]⟩
  set z : Fin G.n → ℂ := Pi.single ⟨0, G.n_pos⟩ 1 with hz
  have hz0 : z ≠ 0 := by
    intro h
    have := congrFun h ⟨0, G.n_pos⟩
    simp [hz] at this
  obtain ⟨x, hx⟩ := hsurj (Pi.single v z)
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := congrFun hx v
    simp at this
    exact hz0 this.symm
  have h1 := hpos x hx0
  rw [form_ext th lam hform] at h1
  have hsum : ∑ v', 2 * (lam v' * hv (G.gram v') (thR th (actOn L.rep ℝ J x) v') (thR th x v')).re
      = 2 * (lam v * hv (G.gram v) (G.psiR v J *ᵥ z) z).re := by
    rw [Finset.sum_eq_single v]
    · rw [thR_act L th hrep, hx]; simp
    · intro v' _ hv'
      rw [hx]
      simp [hv, Pi.single_eq_of_ne hv']
    · simp
  rw [hsum] at h1
  have hif : (if v.embedding (L.e D.ω) = D.ρc then -Complex.I else Complex.I) = -(sgnV L v * Complex.I) := by
    unfold sgnV
    split_ifs <;> simp
  have hss : sgnV L v * sgnV L v = 1 := by
    unfold sgnV
    split_ifs <;> simp
  have hq := (hPD v).dotProduct_mulVec_pos hz0
  rw [hif] at hq
  set h := hv (G.gram v) (G.psiR v J *ᵥ z) z with hh
  set q := star z ⬝ᵥ ((-(sgnV L v * Complex.I) • (G.gram v * G.psiR v J)) *ᵥ z) with hqdef
  have hqe : q = -(sgnV L v * Complex.I) * h := by
    simp [hqdef, hh, hv, Matrix.neg_mulVec, Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_mulVec]
  have hhq : h = sgnV L v * Complex.I * q := by
    rw [hqe]
    linear_combination (Complex.I * Complex.I * h) * hss + h * Complex.I_mul_I
  obtain ⟨hqre, hqim⟩ := Complex.pos_iff.1 hq
  have hqr : q = (q.re : ℂ) := by
    apply Complex.ext <;> simp [← hqim]
  have hfin : (lam v * h).re = (lam v * sgnV L v * Complex.I).re * q.re := by
    rw [hhq, hqr]
    have : lam v * (sgnV L v * Complex.I * (q.re : ℂ)) = (lam v * sgnV L v * Complex.I) * (q.re : ℂ) := by ring
    simp only [Complex.ofReal_re]
    rw [this, Complex.re_mul_ofReal]
  rw [hfin] at h1
  have h2 : 0 < (lam v * sgnV L v * Complex.I).re * q.re := by linarith
  exact (mul_pos_iff_of_pos_right hqre).1 h2
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.TraceConjDotProductEqSumInfinitePlaces
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.trace_conj_dotProduct_eq_sum_infinitePlaces :
    ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ), UpperTheory.Gal.W2.ArchSpan → ∀ (A : Matrix (Fin n) (Fin n) F) (S gr : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (lam : InfinitePlace F → ℂ), (∀ v, (S v).det ≠ 0) → (∀ v, (S v)⁻¹ᴴ * A.map v.embedding * (S v)⁻¹ = lam v • gr v) → ∀ x y : Fin n → F, ((Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x)) : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (lam v * hv (gr v) (S v *ᵥ fun i => v.embedding (x i)) (S v *ᵥ fun i => v.embedding (y i))).re := by
  intro F _ _ _ n hA A S gr lam hdet hform x y
  rw [((hA F n).2.2)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hU : IsUnit (S v).det := isUnit_iff_ne_zero.mpr (hdet v)
  have h1 : (S v)ᴴ * (S v)⁻¹ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.conjTranspose_one]
  have h2 : (S v)⁻¹ * S v = 1 := Matrix.nonsing_inv_mul _ hU
  have hAmap : A.map v.embedding = (S v)ᴴ * (lam v • gr v) * S v := by
    rw [← hform v]
    calc A.map v.embedding
        = ((S v)ᴴ * (S v)⁻¹ᴴ) * A.map v.embedding * ((S v)⁻¹ * S v) := by
          rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (S v)ᴴ * ((S v)⁻¹ᴴ * A.map v.embedding * (S v)⁻¹) * S v := by
          simp only [Matrix.mul_assoc]
  have e1 : v.embedding ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x))
      = (star fun i => v.embedding (y i)) ⬝ᵥ (A.map v.embedding *ᵥ fun i => v.embedding (x i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply,
      IsCMField.complexEmbedding_complexConj]
    rfl
  have e2 : v.embedding ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x))
      = lam v * hv (gr v) (S v *ᵥ fun i => v.embedding (x i)) (S v *ᵥ fun i => v.embedding (y i)) := by
    rw [e1, hAmap, hv, Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star fun i => v.embedding (y i)) (S v)ᴴ, Matrix.smul_mulVec]
    simp [Matrix.vecMul_conjTranspose, dotProduct_smul]
  rw [e2]
end

