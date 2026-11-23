module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0013

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.BlkDegLeTotalDegree
section
namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Classical

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

def padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) : (Σ k, ι k) →₀ ℕ :=
  ∑ k, Finsupp.single ⟨k, p k⟩ (T - blkDeg m k)

theorem padExp_apply (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) (i : ι k) :
    padExp p T m ⟨k, i⟩ = if i = p k then T - blkDeg m k else 0 := by
  classical
  simp only [padExp, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finsupp.single_apply]
    by_cases h : i = p k
    · subst h; simp
    · rw [if_neg, if_neg h]
      intro e
      exact h (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact hb (Sigma.mk.inj_iff.1 e).1
  · simp

theorem blkDeg_padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    blkDeg (padExp p T m) k = T - blkDeg m k := by
  classical
  unfold blkDeg
  simp only [padExp_apply]
  rw [Finset.sum_eq_single (p k)]
  · simp [blkDeg]
  · intro b _ hb; rw [if_neg hb]
  · simp

theorem blkDeg_le_totalDegree {Q : MvPolynomial (Σ k, ι k) ℂ} {m : (Σ k, ι k) →₀ ℕ} (hm : m ∈ Q.support)
    (k : K) : blkDeg m k ≤ Q.totalDegree := by
  classical
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem exists_homogenize (p : (k : K) → ι k) (Q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :
    ∃ (G : MvPolynomial (Σ k, ι k) ℂ) (T : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (fun _ => T) ∧
      (∀ z : (Σ k, ι k) → ℂ, (∀ k, z ⟨k, p k⟩ ≠ 0) →
        eval z G = (∏ k, z ⟨k, p k⟩ ^ T) * eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord p z)) Q) ∧
      ∀ z : (Σ k, ι k) → ℂ, (∃ k, z ⟨k, p k⟩ = 0) → eval z G = 0 := by
  classical
  set Q' : MvPolynomial (Σ k, ι k) ℂ := rename (Fintype.equivFin (Σ k, ι k)).symm Q with hQ'
  have hren : ∀ v : (Σ k, ι k) → ℂ, eval (ReciprocityTheory.AnForm.R.renPt v) Q = eval v Q' := fun v => by
    rw [hQ', eval_rename]
  set T := Q'.totalDegree + 1 with hT
  have hlt : ∀ m ∈ Q'.support, ∀ k, blkDeg m k < T := fun m hm k =>
    Nat.lt_succ_of_le (blkDeg_le_totalDegree hm k)
  refine ⟨∑ m ∈ Q'.support, monomial (m + padExp p T m) (AddMonoidAlgebra.coeff Q' m), T, ?_, ?_, ?_⟩
  · intro n hn k
    obtain ⟨m, hm, hn'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hn)
    have hn'' := support_monomial_subset hn'
    rw [Finset.mem_singleton] at hn''
    subst hn''
    have e1 : ∑ i, (m + padExp p T m) ⟨k, i⟩ = blkDeg (m + padExp p T m) k := rfl
    rw [e1]
    unfold blkDeg
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    have := blkDeg_padExp p T m k
    unfold blkDeg at this
    rw [this]
    have h2 := (hlt m hm k).le
    unfold blkDeg at h2
    omega
  · intro z hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [hren, Q'.as_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sigma]
    have hpad : ∀ k, ∏ i, z ⟨k, i⟩ ^ padExp p T m ⟨k, i⟩ = z ⟨k, p k⟩ ^ (T - blkDeg m k) := fun k => by
      rw [Finset.prod_eq_single (p k)]
      · rw [padExp_apply, if_pos rfl]
      · intro b _ hb; rw [padExp_apply, if_neg hb, pow_zero]
      · simp
    simp only [hpad, ReciprocityTheory.AnForm.R.affCoord, div_pow]
    have hden : ∀ k, ∏ i, z ⟨k, p k⟩ ^ m ⟨k, i⟩ = z ⟨k, p k⟩ ^ blkDeg m k := fun k => by
      rw [Finset.prod_pow_eq_pow_sum]; rfl
    rw [show (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩ / z ⟨k, p k⟩ ^ m ⟨k, i⟩) =
        (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩) / ∏ k, z ⟨k, p k⟩ ^ blkDeg m k by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Finset.prod_div_distrib, hden]]
    have hsub : ∀ k, z ⟨k, p k⟩ ^ (T - blkDeg m k) = z ⟨k, p k⟩ ^ T / z ⟨k, p k⟩ ^ blkDeg m k := fun k =>
      pow_sub₀ _ (hz k) (hlt m hm k).le
    simp only [hsub, Finset.prod_div_distrib]
    have h0 : (∏ k, z ⟨k, p k⟩ ^ blkDeg m k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
    field_simp
  · rintro z ⟨k, hk⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, p k⟩) ?_)
    rw [hk, Finsupp.coe_add, Pi.add_apply, padExp_apply, if_pos rfl]
    exact zero_pow (by have := hlt m hm k; omega)

end

end PositivityTheory.Xgp.c_bm_exists_boundary
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsChgbasis
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.c_fm_exists_flags_chgbasis

variable {N : ℕ} {R R' : Type} [CommRing R] [CommRing R']

def Mn (M : Matrix (Fin N) (Fin N) R) : Prop :=
  ∀ (P : Fin N → Prop) (_ : DecidablePred P), (∀ a c, a ≤ c → P c → P a) →
    (M.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det ≠ 0

theorem Mn.of_map {M : Matrix (Fin N) (Fin N) R} (f : R →+* R') (h : Mn (M.map f)) : Mn M := fun P i hP h0 =>
  h P i hP (by rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])

theorem Mn.map {M : Matrix (Fin N) (Fin N) R} (f : R →+* R') (hf : Function.Injective f) (h : Mn M) :
    Mn (M.map f) := fun P i hP h0 => by
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h0
  exact h P i hP ((map_eq_zero_iff f hf).1 h0)

theorem Mn.lowerUni [Nontrivial R] {M : Matrix (Fin N) (Fin N) R} (h : IsLowerUni M) : Mn M := fun P _ _ => by
  rw [h.det_submatrix P]
  exact one_ne_zero

theorem Mn.mul [IsDomain R] {M B : Matrix (Fin N) (Fin N) R} (h : Mn M) (hB : B.BlockTriangular id)
    (hd : B.det ≠ 0) : Mn (M * B) := fun P i hP => by
  have e : (M * B).submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) =
      M.submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) *
        B.submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) := by
    ext a b
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ P,
      Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P c) (fun c hc => by
        rw [hB (show b.1 < c from not_le.1 fun e => (Finset.mem_filter.1 hc).2 (hP _ _ e b.2)), mul_zero]), add_zero,
      Finset.sum_subtype (p := P) _ (by simp)]
    rfl
  rw [e, det_mul]
  refine mul_ne_zero (h P i hP) ?_
  rw [det_of_upperTriangular hB, Finset.prod_ne_zero_iff] at hd
  rw [det_of_upperTriangular (M := B.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val) fun a b e => hB e,
    Finset.prod_ne_zero_iff]
  exact fun a _ => hd _ (Finset.mem_univ _)

theorem Mn.upper {F : Type} [Field F] {M : Matrix (Fin N) (Fin N) F} (h : Mn M) :
    ∃ B, B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsLowerUni (M * B) := by
  have hb : IsBlockDiag 0 M := fun a b e => absurd (iff_of_true a.2 b.2) e
  obtain ⟨B, -, h1, h2⟩ := hb.exists_upper fun b =>
    (h _ _ fun a c hac hc => ⟨hac.trans hc.1, iff_of_true a.2 b.2⟩).isUnit
  refine ⟨B, h1, fun h0 => ?_, h2⟩
  have := h2.det
  rw [det_mul, h0, mul_zero] at this
  exact zero_ne_one this

theorem exists_low {Ω : Type} [Field Ω] (A : Matrix (Fin N) (Fin N) Ω) (hA : IsUnit A.det) :
    ∃ l : Matrix (Fin N) (Fin N) (FractionRing (Polynomial Ω)), IsLowerUni l ∧
      Mn (A.map (algebraMap Ω (FractionRing (Polynomial Ω))) * l) := by
  let t : Polynomial Ω := Polynomial.X
  let Z : Matrix (Fin N) (Fin N) (Polynomial Ω) := t • (A⁻¹).map Polynomial.C + (1 - t) • (1 : Matrix _ _ _)
  let f := algebraMap (Polynomial Ω) (FractionRing (Polynomial Ω))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have h1 : Mn Z := by
    refine Mn.of_map (Polynomial.evalRingHom 0) ?_
    have : Z.map (Polynomial.evalRingHom 0) = 1 := by
      ext a b
      by_cases e : a = b <;> simp [Z, t, Matrix.one_apply, e]
    rw [this]
    exact Mn.lowerUni isLowerUni_one
  have h2 : Mn (A.map Polynomial.C * Z) := by
    refine Mn.of_map (Polynomial.evalRingHom 1) ?_
    have e1 : Z.map (Polynomial.evalRingHom 1) = A⁻¹ := by
      ext a b
      simp [Z, t]
    have e2 : (A.map Polynomial.C).map (Polynomial.evalRingHom 1) = A := by
      ext a b
      simp
    rw [Matrix.map_mul, e1, e2, Matrix.mul_nonsing_inv _ hA]
    exact Mn.lowerUni isLowerUni_one
  obtain ⟨B, hB, hd, hl⟩ := (h1.map f hf).upper
  refine ⟨_, hl, ?_⟩
  have := (h2.map f hf).mul hB hd
  rw [Matrix.map_mul, Matrix.mul_assoc] at this
  exact this

variable {S : Type} {r : S → ℕ}

noncomputable def gen (Ω : Type) [Field Ω] (r : S → ℕ) (s : S) : Matrix (Fin (r s)) (Fin (r s))
    (MvPolynomial (Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1}) Ω) := fun a b =>
  if h : b < a then MvPolynomial.X ⟨s, (a, b), h⟩ else if a = b then 1 else 0

theorem gen_map {Ω : Type} [Field Ω] [Algebra Ω R] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) R)
    (hu : ∀ s, IsLowerUni (u s)) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    ((A s).map MvPolynomial.C * gen Ω r s).map (MvPolynomial.aeval (R := Ω)
      (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2)).toRingHom =
      (A s).map (algebraMap Ω R) * u s := by
  rw [Matrix.map_mul]
  congr 1
  · ext a b
    exact MvPolynomial.aeval_C _ _
  · ext a b
    rw [Matrix.map_apply, gen]
    split_ifs with h e
    · exact MvPolynomial.aeval_X _ _
    · rw [map_one, e, (hu s).1]
    · rw [map_zero, (hu s).2 a b (lt_of_le_of_ne (not_lt.1 h) e)]

end PositivityTheory.Xgp.c_fm_exists_flags_chgbasis

open PositivityTheory.Xgp.c_fm_exists_flags_chgbasis in
theorem PositivityTheory.Xgp.t_c_fm_exists_flags_chgbasis : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω), IsGenFam Ω G u → (∀ s, IsUnit (A s).det) → ∃ u' B : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G, IsGenFam Ω G u' ∧ (∀ s, IsUnit (B s).det) ∧ (∀ s a b, b < a → B s a b = 0) ∧ ∀ s, (A s).map (algebraMap Ω G) * u s = u' s * B s := by
  intro Ω G _ _ _ S _ r u A hu hA
  have hL : ∀ s, IsLowerUni (u s) := fun s => ⟨hu.1 s, hu.2.1 s⟩
  choose l hl hm using fun s => exists_low (A s) (hA s)
  have h1 : ∀ s, Mn ((A s).map (algebraMap Ω G) * u s) := fun s => by
    rw [← gen_map u hL A s]
    refine Mn.map _ hu.2.2.1 ?_
    have := hm s
    rw [← gen_map l hl A s] at this
    exact this.of_map _
  choose B hB hd hl' using fun s => (h1 s).upper
  refine ⟨fun s => (A s).map (algebraMap Ω G) * u s * B s, fun s => (B s)⁻¹, ?_,
    fun s => Matrix.isUnit_nonsing_inv_det _ (hd s).isUnit, fun s a b h => ?_,
    fun s => (Matrix.mul_nonsing_inv_cancel_right _ _ (hd s).isUnit).symm⟩
  · refine PositivityTheory.Xgp.GenFam.of_gen hu (fun s => (hl' s).1) (fun s => (hl' s).2) fun s => ?_
    generalize hF : IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) =>
      ((A q.1).map (algebraMap Ω G) * u q.1 * B q.1) q.2.1 q.2.2) = F
    have hmem : ∀ a b, ((A s).map (algebraMap Ω G) * u s * B s) a b ∈ F := fun a b =>
      hF ▸ IntermediateField.subset_adjoin _ _ ⟨⟨s, a, b⟩, rfl⟩
    have e : u s * B s = (A s)⁻¹.map (algebraMap Ω G) * ((A s).map (algebraMap Ω G) * u s * B s) := by
      rw [Matrix.mul_assoc _ (u s), ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (hA s),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    have hmem' : ∀ a b, (u s * B s) a b ∈ F := fun a b => by
      rw [e, Matrix.mul_apply]
      exact sum_mem fun c _ => mul_mem (F.algebraMap_mem _) (hmem c b)
    let X₁ : Matrix (Fin (r s)) (Fin (r s)) F := fun a b => ⟨(u s * B s) a b, hmem' a b⟩
    have eX : X₁.map (algebraMap F G) = u s * B s := rfl
    have hX : Mn X₁ := Mn.of_map (algebraMap F G) (eX ▸ (Mn.lowerUni (hL s)).mul (hB s) (hd s))
    obtain ⟨B₁, hB₁, -, hl₁⟩ := hX.upper
    have e₁ : (X₁ * B₁).map (algebraMap F G) = u s * (B s * B₁.map (algebraMap F G)) := by
      rw [Matrix.map_mul, eX, Matrix.mul_assoc]
    have h2 := hl₁.map (algebraMap F G)
    rw [e₁] at h2
    rw [(hL s).eq_one ((hB s).mul (hB₁.map _)) h2, Matrix.mul_one] at e₁
    intro a b
    rw [← e₁]
    exact ((X₁ * B₁) a b).2
  · letI := Matrix.invertibleOfIsUnitDet _ (hd s).isUnit
    exact blockTriangular_inv_of_blockTriangular (hB s) h
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsDegree
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

set_option synthInstance.maxHeartbeats 400000 in
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem PositivityTheory.Xgp.c_fm_exists_flags_degree.core {F₀ Ω G I : Type} [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω]
    [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] [Algebra.IsAlgebraic F₀ Ω] (x : I → G)
    (hx : AlgebraicIndependent Ω x) (hx₀ : AlgebraicIndependent F₀ x)
    (ht : IntermediateField.adjoin Ω (Set.range x) = ⊤) :
    Module.finrank (IntermediateField.adjoin F₀ (Set.range x)) G = Module.finrank F₀ Ω := by
  letI : Algebra (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) :=
    FractionRing.liftAlgebra _ _
  haveI : IsScalarTower (MvPolynomial I F₀) (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have h := Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R := F₀) (S := Ω) I
  rw [Cardinal.lift_id] at h
  have h' : Module.finrank (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) =
      Module.finrank F₀ Ω := congrArg Cardinal.toNat h
  rw [← h']
  let j : FractionRing (MvPolynomial I Ω) ≃ₐ[Ω] G :=
    hx.aevalEquivField.trans ((IntermediateField.equivOfEq ht).trans IntermediateField.topEquiv)
  have hj : ∀ a, j (algebraMap (MvPolynomial I Ω) _ a) = MvPolynomial.aeval x a :=
    fun a => hx.aevalEquivField_algebraMap_apply_coe a
  refine (Algebra.finrank_eq_of_equiv_equiv hx₀.aevalEquivField.toRingEquiv j.toRingEquiv ?_).symm
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial I F₀)) (RingHom.ext fun a => ?_)
  show ((hx₀.aevalEquivField (algebraMap _ _ a) : _) : G) =
    j (algebraMap (FractionRing (MvPolynomial I F₀)) _ (algebraMap (MvPolynomial I F₀) _ a))
  rw [hx₀.aevalEquivField_algebraMap_apply_coe, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (MvPolynomial I F₀) (MvPolynomial I Ω), hj]
  exact (MvPolynomial.aeval_map_algebraMap Ω x a).symm

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_degree : ∀ (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (d : ℕ), 0 < d → Module.finrank F₀ Ω = d → IsGenFam Ω G u → AlgebraicIndependent F₀ (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin F₀ (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) G = d := by
  intro F₀ Ω G _ _ _ _ _ _ _ S _ r u d hd hr hu
  haveI : Module.Finite F₀ Ω := Module.finite_of_finrank_pos (hr ▸ hd)
  have h₀ := hu.2.2.1.restrictScalars (R := F₀) (algebraMap F₀ Ω).injective
  refine ⟨h₀, ?_⟩
  rw [PositivityTheory.Xgp.GenFam.adjoin_low F₀ u hu.1 hu.2.1, ← hr]
  refine PositivityTheory.Xgp.c_fm_exists_flags_degree.core _ hu.2.2.1 h₀ ?_
  rw [← PositivityTheory.Xgp.GenFam.adjoin_low Ω u hu.1 hu.2.1]
  exact hu.2.2.2
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsRevgen
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

private theorem revInv_unitriangular_and_mem_of_unitriangular {Ω G : Type} [Field Ω] [Field G] [Algebra Ω G] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) G) (hd : ∀ a, M a a = 1) (hl : ∀ a b, a < b → M a b = 0) :
    (∀ a, revInv M a a = 1) ∧ (∀ a b, a < b → revInv M a b = 0) ∧
      ∀ F : IntermediateField Ω G, (∀ a b, revInv M a b ∈ F) → ∀ a b, M a b ∈ F := by
  classical
  have hup : (Mᵀ).BlockTriangular id := by
    intro i j hij
    rw [Matrix.transpose_apply]
    exact hl j i hij
  have hunit : IsUnit (Mᵀ).det := by
    rw [Matrix.det_of_isUpperTriangular hup]
    simp [Matrix.transpose_apply, hd]
  letI : Invertible (Mᵀ) := Matrix.invertibleOfIsUnitDet _ hunit
  have hup' : (Mᵀ)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hup
  have hdiag : ∀ i, (Mᵀ)⁻¹ i i = 1 := by
    intro i
    have h1 : ((Mᵀ)⁻¹ * Mᵀ) i i = 1 := by
      rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · simpa [Matrix.transpose_apply, hd] using h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hup' h, zero_mul]
      · rw [hup h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hrev : ∀ a b, revInv M a b = (Mᵀ)⁻¹ a.rev b.rev := fun a b => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [hrev]
    exact hdiag _
  · intro a b hab
    rw [hrev]
    exact hup' (Fin.rev_lt_rev.mpr hab)
  · intro F hF a b
    have hmem : ∀ x y, (Mᵀ)⁻¹ x y ∈ F := by
      intro x y
      have := hF x.rev y.rev
      rwa [hrev, Fin.rev_rev, Fin.rev_rev] at this
    have hdet' : IsUnit ((Mᵀ)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hunit
    have := PositivityTheory.Xgp.GenFam.inv_mem F ((Mᵀ)⁻¹) hdet' hmem b a
    rwa [Matrix.nonsing_inv_nonsing_inv _ hunit, Matrix.transpose_apply] at this

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_revgen : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  intro Ω G _ _ _ S _ r u P _ hu
  have hu' := hu
  obtain ⟨hd, hl, -, -⟩ := hu'
  have key := fun s => revInv_unitriangular_and_mem_of_unitriangular (Ω := Ω) (u s) (hd s) (hl s)
  refine PositivityTheory.Xgp.GenFam.of_gen hu ?_ ?_ ?_
  · intro s a
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).1 a
    · rw [if_neg h]
      exact hd s a
  · intro s a b hab
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).2.1 a b hab
    · rw [if_neg h]
      exact hl s a b hab
  · intro s a b
    have hsub : ∀ x y, (if P s then revInv (u s) else u s) x y ∈
        IntermediateField.adjoin Ω (Set.range fun (q : (σ : S) × Fin (r σ) × Fin (r σ)) =>
          (if P q.fst then revInv (u q.fst) else u q.fst) q.snd.1 q.snd.2) :=
      fun x y => IntermediateField.subset_adjoin _ _ ⟨⟨s, x, y⟩, rfl⟩
    by_cases h : P s
    · rw [if_pos h] at hsub
      exact (key s).2.2 _ hsub a b
    · rw [if_neg h] at hsub
      exact hsub a b
end

