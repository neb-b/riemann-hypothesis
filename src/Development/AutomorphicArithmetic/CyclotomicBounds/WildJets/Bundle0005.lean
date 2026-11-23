module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealRow
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepthDrop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem mx_eq_of_nsmul_eq_of_ne_zero {D : D7} {m n : ℕ} (c : ℕ) (hc : c ≠ 0) {x y : Mx D m n}
    (h : c • x = c • y) : x = y := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply] at h1
  have hF : ((c : ↥D.host.F)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [← Nat.cast_smul_eq_nsmul (↥D.host.F), ← Nat.cast_smul_eq_nsmul (↥D.host.F)] at h1
  calc x i j = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • x i j) := (inv_smul_smul₀ hF _).symm
    _ = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • y i j) := by rw [h1]
    _ = y i j := inv_smul_smul₀ hF _

theorem UpperTheory.WildA.depthDrop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p) (l : ℕ), l.Prime → (∀ w ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ k : ℕ, 0 < k → IsCosetDatum k d → ∃ k' : ℕ, 0 < k' ∧ ¬ l ∣ k' ∧ IsCosetDatum k' d := by
  intro D T L sc G t p d l hl hP k hk hcos
  obtain ⟨x₀, hx₀, hkx, hfn⟩ := hcos
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' l hl.one_lt.ne'
  have hc : ∀ w ∈ d.P, (((l ^ a : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro w hw h
    rw [Nat.cast_pow] at h
    exact hP w hw (w.isPrime.mem_of_pow_mem _ h)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hhalf : ∀ (c : ℕ) (u : Mx D (G.pT p).rank (G.pS p).rank), IsHalf d.e u → IsHalf d.e (c • u) := by
    intro c u hu i j
    simp only [Matrix.smul_apply, mul_smul_comm, hu i j]
  obtain ⟨v, hvL, hvH, hv⟩ :=
    UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc _ hkx (hhalf _ _ hx₀)
  have hmx : m • x₀ = v := by
    apply mx_eq_of_nsmul_eq_of_ne_zero (l ^ a) (pow_ne_zero _ hl.ne_zero)
    rw [hv, smul_smul]
  refine ⟨m, hm0, hm, x₀, hx₀, by rw [hmx]; exact hvL, ?_⟩
  rw [hfn]
  congr 1
  ext x
  simp only [GlobalTheory.RowTest.halfCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, huH, rfl⟩
    refine ⟨(l ^ a) • u, AddSubgroup.nsmul_mem _ hu _, hhalf _ _ huH, ?_⟩
    rw [smul_smul, mul_comm m]
  · rintro ⟨u, hu, huH, rfl⟩
    obtain ⟨u', hu', hu'H, rfl⟩ := UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc u hu huH
    exact ⟨u', hu', hu'H, by rw [smul_smul, mul_comm m]⟩
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open Formalism.L2.Ker MvPolynomial

private noncomputable abbrev zPol (σ : Type) : Subring (MvPolynomial σ ℂ) :=
  (MvPolynomial.map (Int.castRingHom ℂ)).range

private theorem zX_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ ℂ) ∈ zPol σ := ⟨X v, map_X _ _⟩

private theorem zcoeff {σ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ zPol σ) (m : σ →₀ ℕ) :
    ∃ z : ℤ, p.coeff m = (z : ℂ) := by
  obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
  exact ⟨q.coeff m, by simp [MvPolynomial.coeff_map]⟩

private theorem zdet_mem {σ : Type} {s : ℕ} (M : Matrix (Fin s) (Fin s) (MvPolynomial σ ℂ))
    (h : ∀ p q, M p q ∈ zPol σ) : M.det ∈ zPol σ := by
  choose M' hM' using fun p q => RingHom.mem_range.mp (h p q)
  refine RingHom.mem_range.mpr ⟨(Matrix.of M').det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun p q => ?_
  simpa using hM' p q

private theorem zaeval_mem {σ τ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ zPol σ) (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ v, g v ∈ zPol τ) : aeval g p ∈ zPol τ := by
  obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
  clear hp
  induction q using MvPolynomial.induction_on with
  | C z =>
    refine RingHom.mem_range.mpr ⟨C z, ?_⟩
    simp [MvPolynomial.algebraMap_eq]
  | add p q hp' hq' =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hp' hq'
  | mul_X p v hp' =>
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp' (hg v)

variable {ι : Type} [Fintype ι] {a b : ℕ}

private theorem zsubD_mem {P : Pol ℂ ι a} (hP : P ∈ zPol (ι × Fin a × Fin a)) :
    subD ℂ ι a b P ∈ zPol ((ι × Fin b × Fin b) ⊕ DVar ι a b) := by
  unfold subD
  refine zaeval_mem hP _ fun v => ?_
  split_ifs
  · exact sum_mem fun β _ => mul_mem (zX_mem _) (zX_mem _)
  · exact zero_mem _

private theorem jetLin_mono (J : (DVar ι a b →₀ ℕ) → ℂ) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) (c : ℂ) :
    jetLin J (monomial m c) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have e : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      c • (basisMonomials _ ℂ) m := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  simp only [jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

open Classical in
private theorem jetLin_zmem (k : DVar ι a b →₀ ℕ)
    {p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ} (hp : p ∈ zPol _) :
    jetLin (fun m => if m = k then (1 : ℂ) else 0) p ∈ zPol (ι × Fin b × Fin b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum]
  refine sum_mem fun μ _ => ?_
  rw [jetLin_mono]
  obtain ⟨z, hz⟩ := zcoeff hp μ
  refine RingHom.mem_range.mpr ⟨monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
    (z * if μ.comapDomain Sum.inr Sum.inr_injective.injOn = k then 1 else 0), ?_⟩
  rw [MvPolynomial.map_monomial, hz]
  split_ifs <;> simp

open Classical in
private theorem jetLin_split (p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    ∃ S : Finset (DVar ι a b →₀ ℕ), ∀ J : (DVar ι a b →₀ ℕ) → ℂ,
      jetLin J p = ∑ k ∈ S, J k • jetLin (fun m => if m = k then (1 : ℂ) else 0) p := by
  have hsplit : ∀ J' : (DVar ι a b →₀ ℕ) → ℂ, jetLin J' p = ∑ μ ∈ p.support,
      monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
        (AddMonoidAlgebra.coeff p μ * J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
    intro J'
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [jetLin_mono]
  refine ⟨p.support.image (fun μ => μ.comapDomain Sum.inr Sum.inr_injective.injOn), fun J => ?_⟩
  rw [hsplit J]
  simp only [hsplit, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Finset.sum_eq_single (μ.comapDomain Sum.inr Sum.inr_injective.injOn)]
  · simp [smul_monomial, mul_comm]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_image_of_mem _ hμ) h

end

theorem UpperTheory.WildA.jetInt :
    ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
      Formalism.L2.Ker.JetInVV ℂ lam lam' n → ∀ (j : VVIdx lam) (i : VVIdx lam'),
      ∃ c : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) →₀ ℤ, ∀ J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ,
        (bVV ℂ lam').repr (Formalism.L2.Ker.jetOp lam lam' J n (bVV ℂ lam j)) i = c.sum fun m z => (z : ℂ) * J m := by
  intro ι _ a b lam lam' n hV j i
  classical
  obtain ⟨P, hP⟩ : ∃ P, P = bVVfun ℂ lam j := ⟨_, rfl⟩
  have hPmem : P ∈ VV ℂ lam := by
    rw [hP, ← bVV_coe]
    exact ((bVV ℂ lam) j).2
  have hPz : P ∈ zPol (ι × Fin a × Fin a) := by
    obtain ⟨Q, hQ⟩ := bVVfun_int ℂ lam j
    rw [hP]
    exact RingHom.mem_range.mpr ⟨Q, hQ.symm⟩
  have hdet : ∀ τ, Formalism.L2.Ker.frDet ℂ a τ ∈ zPol (ι × Fin a × Fin a) := fun τ =>
    zdet_mem _ (fun p q => zX_mem _)
  have hsh : P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ ∈ zPol (ι × Fin a × Fin a) :=
    mul_mem hPz (prod_mem fun τ _ => pow_mem (hdet τ) _)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Formalism.L2.Ker.subD ℂ ι a b (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ) := ⟨_, rfl⟩
  have hQz : Q ∈ zPol _ := by
    rw [hQ]
    exact zsubD_mem hsh
  have hJQ : ∀ J, Formalism.L2.Ker.jetMap J n P = Formalism.L2.Ker.jetLin J Q := by
    intro J
    rw [hQ]
    rfl
  obtain ⟨S, hS⟩ := jetLin_split Q
  have hint : ∀ k, ∃ z : ℤ, (bVV ℂ lam').repr
      ⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ i = z := by
    intro k
    apply UpperTheory.WildA.bvvInt
    intro m
    apply zcoeff
    show Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P ∈ _
    rw [hJQ]
    exact jetLin_zmem k hQz
  choose z hz using hint
  refine ⟨∑ k ∈ S, Finsupp.single k (z k), fun J => ?_⟩
  have hop : Formalism.L2.Ker.jetOp lam lam' J n (bVV ℂ lam j) = ⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩ := by
    show Formalism.L2.Ker.retrVV ℂ lam' (Formalism.L2.Ker.jetMap J n ((bVV ℂ lam j : Pol ℂ ι a))) = _
    have hb : ((bVV ℂ lam j : Pol ℂ ι a)) = P := by rw [bVV_coe, hP]
    rw [hb]
    exact Submodule.projectionOnto_apply_left _ ⟨_, hV J P hPmem⟩
  have hsum : (⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩ : VV ℂ lam') =
      ∑ k ∈ S, J k • (⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ : VV ℂ lam') := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, hJQ]
    exact hS J
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hop, hsum, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hz]
  let f : ((Formalism.L2.Ker.DVar ι a b →₀ ℕ) →₀ ℤ) →+ ℂ :=
    { toFun := fun c => c.sum fun m z => (z : ℂ) * J m
      map_zero' := by simp
      map_add' := by
        intro x y
        exact Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring) }
  change ∑ x ∈ S, J x * (z x : ℂ) = f (∑ k ∈ S, Finsupp.single k (z k))
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [f, Finsupp.sum_single_index, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetOpMulTab
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem jetOp_mul_tab' {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

private theorem prod_pow_fiber {α ι : Type} [Fintype ι] [DecidableEq ι] (f : α → ι) (c : ι → ℂ) (m : α →₀ ℕ) :
    (m.prod fun v e => c (f v) ^ e) = ∏ τ, c τ ^ (m.sum fun v e => if f v = τ then e else 0) := by
  simp only [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [pow_ite]

private theorem degree_fiber {α ι : Type} [Fintype ι] [DecidableEq ι] (f : α → ι) (m : α →₀ ℕ) :
    m.degree = ∑ τ, (m.sum fun v e => if f v = τ then e else 0) := by
  simp only [Finsupp.sum]
  rw [Finset.sum_comm, Finsupp.degree_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp

private theorem period_ne {D : D7} {δ : ℂ} (hδ : δ ≠ 0) (τ : D.what₂.Tau) : period δ τ ≠ 0 := by
  refine div_ne_zero hδ (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))
  have : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  positivity

private theorem delta_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  rintro rfl
  have h1 := (hL L.ω₁).2 L.ω₁_mem_lattice
  have h2 : Formalism.MainNotions.TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    rw [Formalism.MainNotions.TaylorLogMetric.lamOf, AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  exact L.indep.ne_zero 0 (by simpa using h2 h1)

theorem UpperTheory.WildA.kkTab :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, DefPair D.R.m p →
      ∀ (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ),
      (∀ mon, jetTab W N.frC p (Z.vec d) (x * N.u _) (y * N.u _) mon =
        Z.c0 p * opp p (((mon.mapDomain (fvar G p)).prod fun v e => period Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) Θ)) →
      Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp (wt G p.small) (wt G p.big)
        (fun mon => if mon.degree = ∑ τ, fockDeg G p τ then
          opp p (Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) Θ) else 0) (nuEnd G p) := by
  intro D T L sc G W U N Z t p hp d x y Θ h
  classical
  have hδ : Z.δ ≠ 0 := delta_ne Z.crv
  have hf : ∀ k, (fvar G p k).1 = k.1 := fun k => by cases p <;> rfl
  rw [Normal.kkMap, fockComp, ← jetOp_mul_tab']
  refine UpperTheory.WildA.jetDeg _ _ _ (wtOK_of_defPair G p hp).2 _ _ fun m hm => ?_
  have hm' : ∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = fockDeg G p τ := hm
  have h1 : m.degree = ∑ τ, fockDeg G p τ := by
    rw [degree_fiber Prod.fst m]
    exact Finset.sum_congr rfl fun τ _ => hm' τ
  have h2 : ((m.mapDomain (fvar G p)).prod fun v e => period Z.δ v.1 ^ e) = ∏ τ, period Z.δ τ ^ fockDeg G p τ := by
    rw [Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add])]
    simp only [hf]
    rw [prod_pow_fiber Prod.fst (period Z.δ) m]
    exact Finset.prod_congr rfl fun τ _ => by rw [hm' τ]
  have h3 : (∏ τ, opp p ((1 : D.what₂.Tau → ℂ) τ / period Z.δ τ) ^ fockDeg G p τ) *
      opp p (∏ τ, period Z.δ τ ^ fockDeg G p τ) = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [map_pow, ← mul_pow, ← map_mul, Pi.one_apply, div_mul_cancel₀ _ (period_ne hδ τ), map_one, one_pow]
  rw [if_pos h1, h, h2, Normal.scal, map_mul, mul_mul_mul_comm, Units.inv_mul, one_mul, ← mul_assoc, h3, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MoveRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem frC_on' {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U₀ : Set T}
    (N : Std G U₀) (X : Node) (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    (N.frC X τ)ᴴ * gramAt D (G.V X) τ * N.frC X τ = 1 := by
  show (N.frC X τ)ᴴ * (G.V X).gram.map (tauE D τ) * N.frC X τ = 1
  have h := congrArg (·.map (tauE D τ)) (N.fr_on X hX)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [← h, Std.frC]
  congr 2
  ext a b
  exact (D.sp.cm.cmUnram.2.1 (tauE D τ) _).symm

private noncomputable def kerLin {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T) (f : WO (G.pS p) (G.pT p) → ℂ)
    (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) : PolF D (G.pT p).rank (G.pS p).rank →ₗ[ℂ] ℂ :=
  LinearMap.proj (0 : WO (G.pS p) (G.pT p)) ∘ₗ W.om p (G.toPair p g h) ∘ₗ fockIn W B p f

private theorem kerLin_apply {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T) (f : WO (G.pS p) (G.pT p) → ℂ)
    (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    kerLin W B p f g h Q = W.ker p (fockIn W B p f Q) g h := rfl

private theorem negGA_GQ {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

private theorem ker_rat {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (p : GlobalTheory.ChiGrid.Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (γ : GA D (G.V p.small)) (hγ : γ ∈ GQ (G.V p.small))
    (γ' : GA D (G.V p.big)) (hγ' : γ' ∈ GQ (G.V p.big)) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  have hw := W.om_is p hp
  have h12 : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_GQ _ hγ', hγ⟩
    | mu t i j => exact ⟨hγ, hγ'⟩
    | core i => exact ⟨negGA_GQ _ hγ', hγ⟩
    | top t j => exact ⟨hγ, hγ'⟩
  rw [GlobalTheory.FockReal.ker_mul]
  exact hw.om_aut _ h12.1 _ h12.2 _ (hw.om_pres (G.toPair p g h) f hf)

theorem UpperTheory.WildA.moveRow :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i : ℕ), i + 1 ≤ D.R.m →
      ∀ (d : FinDatum G t (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) (x r : FinPt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (y r' : FinPt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big)
        (U : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t i hi d x r y r' U U' hU hU'
  have hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) := ⟨by omega, rfl⟩
  have hR : (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := UpperTheory.WildA.expEx (G := G) hL _ hp
  obtain ⟨γ, hγ, k, hk, hm, hρ⟩ := UpperTheory.WildA.ratReal W N.fr _ r U hU
  obtain ⟨γ', hγ', k', hk', hm', hρ'⟩ := UpperTheory.WildA.ratReal W N.fr _ r' U' hU'
  obtain ⟨hth, hvac⟩ := _root_.GlobalTheory.FockRealVec.vec_theta_fock W Z hp d (Z.hasVec_of_defPair hL hp d)
  have hrow := UpperTheory.WildA.realRow (W := W) N hL i hi a b ha hb e₁ e₂ he₁ he₂
    (kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) : GA D _)) k hk k' hk'
  have htab : jetTab W N.frC _ (Z.vec d) (r * x * N.u _) (r' * y * N.u _) = fun m =>
      GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) e₁ e₂ k k' *
        kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) : GA D _)
          (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) k k'
            (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1)) := by
    funext m
    rw [jetTab, kerFin, mul_assoc r, mul_assoc r', hm, hm', kerLin_apply,
      ker_rat W _ hR (fockIn W N.frC _ (Z.vec d) _)
        (GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth _) γ hγ γ' hγ']
    exact GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp (frC_on' N) a b ha hb e₁ e₂ he₁ he₂ _ hth hvac k hk k' hk' _ _ _
  have h1 : GlobalTheory.DefStep.realAct W.θ N.fr _ k ∘ₗ GlobalTheory.DefStep.realAct W.θ N.fr _ k⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [Normal.kkMap, Normal.kkMap, fockComp, fockComp, htab, hrow, ← hρ, ← hρ', LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_assoc, LinearMap.comp_assoc, h1, LinearMap.comp_id]
  rfl
end

