module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomain
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.RootFactor

theorem aeval_sq {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) : aeval D q * aeval D q = q.eval r • aeval D q := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  obtain ⟨s, hs⟩ : ∃ s : K[X], q = s * (X - C r) + C (q.eval r) :=
    ⟨q /ₘ (X - C r), by
      have hmd := Polynomial.modByMonic_add_div q (X - C r)
      rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hmd
      rw [mul_comm, add_comm]
      exact hmd.symm⟩
  conv_lhs => arg 1; rw [hs]
  rw [map_add (f := _), map_mul, aeval_C, add_mul, Matrix.mul_assoc, hCH, Matrix.mul_zero, zero_add,
    Algebra.smul_def]

theorem aeval_rank {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) (hq : q.eval r ≠ 0) : (aeval D q).rank = 1 := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  have hDP : D * aeval D q = r • aeval D q := by
    rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mul,
      sub_eq_zero, Matrix.smul_mul, Matrix.one_mul] at hCH
    exact hCH
  have hchar : LinearMap.charpoly (Matrix.toLinAlgEquiv' D) = (X - C r) * q := by
    rw [← h]; exact Matrix.charpoly_toLin' D
  have hmult : (LinearMap.charpoly (Matrix.toLinAlgEquiv' D)).rootMultiplicity r = 1 := by
    rw [hchar, Polynomial.rootMultiplicity_mul, Polynomial.rootMultiplicity_X_sub_C_self,
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hq)]
    rw [← h]; exact (Matrix.charpoly_monic D).ne_zero
  have hle : LinearMap.range (aeval D q).mulVecLin ≤
      Module.End.eigenspace (Matrix.toLinAlgEquiv' D) r := by
    rintro _ ⟨v, rfl⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLinAlgEquiv'_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hDP, Matrix.smul_mulVec]
  have hEig : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' D) r := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar]
    simp [Polynomial.IsRoot]
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hPv : Matrix.mulVec (aeval D q) v = q.eval r • v := by
    rw [← Matrix.toLinAlgEquiv'_apply, ← Polynomial.aeval_algHom_apply]
    exact Module.End.aeval_apply_of_hasEigenvector hv
  show Module.finrank K (LinearMap.range (aeval D q).mulVecLin) = 1
  apply le_antisymm
  · exact (Submodule.finrank_mono hle).trans (hmult ▸ LinearMap.finrank_eigenspace_le _ r)
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have hmem : Matrix.mulVec (aeval D q) v ∈ LinearMap.range (aeval D q).mulVecLin := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot, hPv] at hmem
    exact smul_ne_zero hq hv.2 hmem

private theorem aeval_list_prod_X_sub_C_mul_comm {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K)
    (l : List ℕ) :
    b * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have key : b * (a * D * b - ρ c • (a * b)) = (D - ρ c • 1) * b := by
      simp only [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hba, Matrix.one_mul,
        Matrix.sub_mul, Matrix.smul_mul]
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul, ← Matrix.mul_assoc,
      key, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]
    congr 2
    simp [Algebra.algebraMap_eq_smul_one]

theorem prod_eq {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K)
    (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K) (l : List ℕ) :
    (a * b) * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      a * aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  rw [Matrix.mul_assoc, aeval_list_prod_X_sub_C_mul_comm a b hba D ρ l, ← Matrix.mul_assoc]

private theorem prod_Ioc_one_eq_list_range'_prod {M : Type} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Ioc 1 t, f c = ((List.range' 2 (t - 1)).map f).prod := by
  rw [Finset.prod_eq_multiset_prod]
  rfl

theorem field_case {K : Type} [Field K] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) K) (ρ : ℕ → K) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  obtain ⟨a, b, hba, hab, hM⟩ := GlobalTheory.BlockCharpoly.blockPol_eq_charpoly e he rfl
  have hX : e * X₀ * e = X₀ := by rw [h1, h2]
  have hX' : a * (b * X₀ * a) * b = X₀ := by
    conv_rhs => rw [← hX, ← hab]
    simp only [Matrix.mul_assoc]
  have hcp : (b * X₀ * a).charpoly =
      (X - C (ρ 1)) * ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod := by
    rw [← hM, hX, ← hP, Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ t), Finset.prod_cons,
      prod_Ioc_one_eq_list_range'_prod]
  have hev : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) =
      ∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c) := by
    rw [prod_Ioc_one_eq_list_range'_prod, Polynomial.eval_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp
  have hne : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) ≠ 0 := by
    rw [hev, Finset.prod_ne_zero_iff]
    intro c hc hzero
    rw [Finset.mem_Ioc] at hc
    have := hρ (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega)
      (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega) (sub_eq_zero.mp hzero)
    omega
  have heE : e * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
    obtain ⟨k, hk⟩ : ∃ k, t - 1 = k + 1 := ⟨t - 2, by omega⟩
    rw [hk, List.range'_succ, List.map_cons, List.prod_cons, ← Matrix.mul_assoc, Matrix.mul_sub,
      Matrix.mul_smul, h1, he]
  have hE : ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      a * aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod * b := by
    rw [← heE, ← prod_eq a b hba (b * X₀ * a) ρ, hab]
    congr 2
    apply List.map_congr_left
    intro c _
    rw [hX']
  have hsq := aeval_sq (b * X₀ * a) (ρ 1) _ hcp
  have hrk := aeval_rank (b * X₀ * a) (ρ 1) _ hcp hne
  rw [hE, ← hev]
  generalize aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod = R at hsq hrk
  constructor
  · apply le_antisymm
    · exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hrk.le
    · have hR : R = b * (a * R * b) * a := by
        simp only [← Matrix.mul_assoc, hba, Matrix.one_mul]
        rw [Matrix.mul_assoc, hba, Matrix.mul_one]
      calc 1 = R.rank := hrk.symm
        _ = (b * (a * R * b) * a).rank := by rw [← hR]
        _ ≤ (b * (a * R * b)).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (a * R * b).rank := Matrix.rank_mul_le_right _ _
  · calc a * R * b * (a * R * b) = a * (R * R) * b := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
      _ = _ := by rw [hsq, Matrix.mul_smul, Matrix.smul_mul]

theorem blockPol_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

private theorem map_list_prod' {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (l : List ℕ) :
    ((l.map fun c => X₀ - ρ c • e).prod).map f = (l.map fun c => X₀.map f - f (ρ c) • e.map f).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    ext i j
    simp

private theorem map_smul_eq_smul_map {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (s : O) (M : Matrix (Fin n) (Fin n) O) : (s • M).map f = f s • M.map f := by
  ext i j
  simp

theorem rank_one_and_sq {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O)
    (ρ : ℕ → O) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  obtain ⟨hr, hsq⟩ := field_case (K := FractionRing O) n t (e.map (toFr O)) (X₀.map (toFr O))
    (fun c => toFr O (ρ c)) ht (by rw [← Matrix.map_mul, he]) (by rw [← Matrix.map_mul, h1])
    (by rw [← Matrix.map_mul, h2]) (fun x hx y hy hxy => hρ hx hy (hinj hxy))
    (by rw [← blockPol_map, ← hP, Polynomial.map_prod]; simp)
  refine ⟨by rw [map_list_prod']; exact hr, ?_⟩
  have hmap : (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) =
      ((∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) •
        ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) := by
    rw [Matrix.map_mul, map_smul_eq_smul_map, map_list_prod', hsq, map_prod]
    simp [map_sub]
  ext i j
  exact hinj (congrFun (congrFun hmap i) j)

end GlobalTheory.RootFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.AntiRamConj GlobalTheory.AntiLAdic

namespace GlobalTheory.ConjPoly

theorem charpoly_smul_inv {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • N).charpoly = (m.map fun β => X - C (c * β⁻¹)).prod := by
  have hcard : Multiset.card m = n := by
    have := congrArg natDegree hM
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card, Fintype.card_fin] at this
    exact this.symm
  have ev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - M).det = (m.map fun β => y - β).prod := fun y => by
    rw [← Matrix.eval_charpoly, hM, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (-M).det = (m.map fun β => -β).prod := by simpa using ev 0
  have hne : (-M).det ≠ 0 := by
    intro e
    have : (-M * -N).det = 1 := by rw [neg_mul_neg, h, Matrix.det_one]
    rw [Matrix.det_mul, e, zero_mul] at this
    exact zero_ne_one this
  have hβ : ∀ β ∈ m, β ≠ 0 := by
    rintro β hβ rfl
    apply hne
    rw [h0]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨0, hβ, neg_zero⟩)
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono ?_)
  intro x hx
  have hx0 : x ≠ 0 := hx
  show eval x _ = eval x _
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have e1 : -M * (Matrix.scalar (Fin n) x - c • N) = x • (Matrix.scalar (Fin n) (c / x) - M) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal,
      mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, h, smul_sub, smul_smul, mul_div_cancel₀ _ hx0]
    simp
    abel
  rw [← Matrix.det_mul, e1, Matrix.det_smul, ev, h0, ← Multiset.prod_map_mul, Fintype.card_fin, ← hcard,
    ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun β hb => ?_
  have := hβ β hb
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  field_simp
  ring

theorem continuous_cyc_val (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous fun g : G F Ω => ((cyc F Ω l g : (Qbar l)ˣ) : Qbar l) := by
  have h1 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) := continuous_algebraMap _ _
  have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
  exact h1.comp (h2.comp (Units.continuous_val.comp (continuous_cycZ F Ω l)))

theorem cyc_val_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : IsPlaceOver A v) {σ : G F Ω} (hσ : IsFrob A (normV v) σ) :
    ((cyc F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
  rw [cyc_eq_map_cycZ, Units.coe_map, cycZ_of_isFrob hl h hσ]
  simp

theorem normV_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : normV v ≠ 0 := by
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact Nat.card_pos.ne'

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l ≠ 0) : (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    simpa using hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton, placesOver] using hv

theorem exists_conj (D : D7) : ∃ bar : PlE D.host → PlE D.host, Function.Injective bar ∧
    ∀ w, IsConjPl D.host w (bar w) ∧ normV (bar w) = normV w ∧ (IsSplitPl D.host w → IsSplitPl D.host (bar w)) := by
  choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv v).exists
  have hbb : ∀ v, bar (bar v) = v := fun v =>
    (GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv (bar v)).unique (hbar _)
      (conjPl_symm (host_conj_conj D) (hbar v))
  have hc : ∀ v, IsConjPl D.host v (bar v) := fun v => (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).1 (hbar v)
  refine ⟨bar, Function.LeftInverse.injective hbb, fun w => ⟨hc w, normV_conjPl (hbar w), ?_⟩⟩
  rintro ⟨x, hx, hx'⟩
  let y : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x
  have hy : (y : D.host.E) = D.host.conj x := rfl
  refine ⟨y, (hc w x y hy).1 hx, fun z hz hzm => ?_⟩
  rw [hy, host_conj_conj] at hz
  have hzx : z = x := Subtype.ext hz
  rw [hzx] at hzm
  exact hx' y hy ((hc w y x (by rw [hy, host_conj_conj])).2 hzm)

theorem isoLoc_single (D : D7) (π : D.naut.CG D.R.r) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem cpow_sq {q : ℂ} (hq : q ≠ 0) (s : ℝ) (k : ℤ) (h : (k : ℝ) = 2 * s) : q ^ k = q ^ (s : ℂ) * q ^ (s : ℂ) := by
  rw [← Complex.cpow_add _ _ hq, ← Complex.cpow_intCast]
  congr 1
  rw [← two_mul]
  exact_mod_cast h

theorem charpoly_conj (D : D7) (hD : FrobDense D) (i : D.nd.Loc) (π : D.naut.CG D.R.r)
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (hπ : D.naut.csd π)
    (hρ : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ)
    (hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y) (g : G D.host.E D.nd.Om) :
    (((ρ (conjHom D.ntw.cc hc g) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
        (iotaOQ D.nd D.naut i)).charpoly =
      ((((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ (1 - (D.R.r : ℤ))) •
        ((ρ g⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i)).charpoly := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := exists_conj D
  obtain ⟨hcont, -, hfr⟩ := hρ
  have hι := (iotaOQ_continuous_injective D i).1
  have hfr' := hinj.tendsto_cofinite.eventually hfr
  have hl := (finite_placesOver D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).compl_mem_cofinite
  have hall := (hfr.and hfr').and ((D.naut.locG_unr_ae π).and hl)
  refine charpoly_eq_of_dense (G D.host.E D.nd.Om) (Qbar (D.nd.l i)) D.R.r
    (fun g => ((ρ (conjHom D.ntw.cc hc g) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map
        (iotaOQ D.nd D.naut i))
    (fun g => (((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ (1 - (D.R.r : ℤ))) •
        ((ρ g⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i)) _ (hD _ (Filter.eventually_cofinite.1 hall))
    ((hcont.comp (continuous_conjHom D.ntw.cc hc)).matrix_map hι)
    (((continuous_cyc_val D.host.E D.nd.Om (D.nd.l i)).zpow₀ (1 - (D.R.r : ℤ))
      fun g => Or.inl (Units.ne_zero _)).fun_smul ((hcont.comp continuous_inv).matrix_map hι)) ?_ g
  rintro σ ⟨w, hw, -, B, hB, hσ⟩
  obtain ⟨⟨h1, h2⟩, hu, hwl⟩ := not_not.1 hw
  obtain ⟨hcj, hn, -⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr π w (bar w) hπ hcj hu
  have e1 := h1 B σ hB hσ
  have e2 := h2 _ _ (isPlaceOver_moveVal D hcj hB) (by rw [hn]; exact isFrob_conjHom D.ntw.cc hc hσ)
  rw [isoLoc_single, galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  rw [isoLoc_single, galPol, D.naut.frobEig_tw _ _ hu', he, hn, ← Matrix.charpoly_map] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (normV_ne_zero w)
  have e3 := charpoly_smul_inv _
    (((ρ σ⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaO D.nd D.naut i))
    (by rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]) _ (((normV w : ℕ) : ℂ) ^ (1 - (D.R.r : ℤ))) e1
  apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
  beta_reduce
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, cyc_val_frob hwl hB hσ]
  refine e2.trans (Eq.trans ?_ (e3.symm.trans ?_))
  · rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    rw [cpow_sq hq ((1 - (D.R.r : ℝ)) / 2) _ (by push_cast; ring)]
    have : ((normV w : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) ≠ 0 := by
      simp [hq]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right₀ this, mul_comm a⁻¹]
  · congr 1
    ext a b
    simp [iotaO, iotaOQ]

theorem chi_conj (D : D7) (hD : FrobDense D) (i : D.nd.Loc)
    (hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y) (g : G D.host.E D.nd.Om) :
    iotaOQ D.nd D.naut i (D.nd.chi i 1 (conjHom D.ntw.cc hc g) : (D.nd.O i)ˣ) *
        iotaOQ D.nd D.naut i (D.nd.chi i 1 g : (D.nd.O i)ˣ) =
      ((cyc D.host.E D.nd.Om (D.nd.l i) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) ^ ((D.R.t : ℤ) - (D.R.nV : ℤ)) := by
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  obtain ⟨bar, hinj, hbar⟩ := exists_conj D
  have hι := (iotaOQ_continuous_injective D i).1
  have hl := (finite_placesOver D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).compl_mem_cofinite
  have hout : ∀ᶠ w in Filter.cofinite, w ∉ placesOver D.host.E (D.nd.l i) ∧ w ∉ D.nd.S i ∧ w ∉ D.nd.Q i :=
    Filter.Eventually.and hl ((D.nd.S i).eventually_cofinite_notMem.and (D.nd.Q i).eventually_cofinite_notMem)
  have hall := (hout.and (hinj.tendsto_cofinite.eventually hout)).and (D.naut.locG_unr_ae (D.naut.muC i))
  have hχ := hι.comp (D.nd.chi_cont i 1)
  refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 hall))
    ((hχ.comp (continuous_conjHom D.ntw.cc hc)).mul hχ)
    ((continuous_cyc_val _ _ _).zpow₀ _ fun g => Or.inl (Units.ne_zero _)) ?_) g
  rintro σ ⟨w, hw, hs, B, hB, hσ⟩
  obtain ⟨⟨h1, h2⟩, hu⟩ := not_not.1 hw
  obtain ⟨hcj, hn, hs'⟩ := hbar w
  obtain ⟨hu', he⟩ := D.naut.csd_unr _ w (bar w) (D.naut.muC_csd i) hcj hu
  obtain ⟨u1, e1⟩ := D.naut.chi_mu i w ⟨hs, h1⟩
  obtain ⟨u2, e2⟩ := D.naut.chi_mu i (bar w) ⟨hs' hs, h2⟩
  have e1 := e1 B σ hB hσ
  have e2 := e2 _ _ (isPlaceOver_moveVal D hcj hB) (by rw [hn]; exact isFrob_conjHom D.ntw.cc hc hσ)
  have one : ∀ (χ : D.naut.CG 1) (v : PlE D.host), D.naut.unr (D.naut.locG χ v) →
      ∃ a, D.naut.frobEig (D.naut.locG χ v) = {a} := fun χ v h =>
    Multiset.card_eq_one.1 ((D.naut.frobEig_card _ h).trans (D.naut.locG_dim χ v))
  obtain ⟨a, ha⟩ := one _ w (D.naut.etaT_unr w)
  obtain ⟨b, hb⟩ := one _ (bar w) (D.naut.etaT_unr (bar w))
  obtain ⟨m, hm⟩ := one _ w hu
  have hab := D.naut.etaT_split w (bar w) hs hcj a b ha hb
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact D.naut.frobEig_ne_zero _ hu (by rw [hm]; exact Multiset.mem_singleton_self _)
  obtain ⟨v1, f1⟩ := D.naut.etaTinv_def w
  obtain ⟨v2, f2⟩ := D.naut.etaTinv_def (bar w)
  rw [ha, Multiset.map_singleton] at f1
  rw [hb, Multiset.map_singleton] at f2
  rw [D.naut.frobEig_tw _ _ u1, D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu v1 (D.naut.locG_dim _ _) f1, hm,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e1
  rw [D.naut.frobEig_tw _ _ u2, D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu' v2 (D.naut.locG_dim _ _) f2, he, hm,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj, hn] at e2
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (normV_ne_zero w)
  apply (D.naut.iotaQC i).injective
  simp only [Function.comp_apply, Pi.mul_apply]
  rw [map_mul, cyc_val_frob h1.1 hB hσ, map_zpow₀, map_natCast,
    cpow_sq hq (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) _ (by push_cast; ring)]
  refine (congrArg₂ (· * ·) e2.symm e1.symm).trans ?_
  have hab' : a⁻¹ * b⁻¹ = 1 := by rw [← mul_inv, hab, inv_one]
  have hmm : m⁻¹ * m = 1 := inv_mul_cancel₀ hm0
  generalize ((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = y
  calc m⁻¹ * b⁻¹ * y * (m * a⁻¹ * y) = (m⁻¹ * m) * (a⁻¹ * b⁻¹) * (y * y) := by ring
    _ = y * y := by rw [hmm, hab', one_mul, one_mul]

theorem conj_inertia : ∀ D : D7, FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (w : PlE D.host) (B : ValuationSubring D.nd.Om), w ∉ placesOver D.host.E (D.nd.l i) → IsPlaceOver (F := D.host.E) B w → ∀ s ∈ Ine (F := D.host.E) B, ∀ s' : G D.host.E D.nd.Om, (∀ y, s' (D.ntw.cc y) = D.ntw.cc (s y)) → ((ρ s' : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly ∧ D.nd.chi i 1 s' = D.nd.chi i 1 s⁻¹ := by
  intro D hD i π ρ hπ hρ w B hw hB s hs s' hs'
  have hc : ∀ x : D.host.E, ∃ y : D.host.E,
      D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
    fun x => ⟨_, cc_symm_algebraMap_host D x⟩
  obtain rfl : s' = conjHom D.ntw.cc hc s := by
    ext y
    rw [conjHom_apply, ← hs', RingEquiv.apply_symm_apply]
  have hε : cyc D.host.E D.nd.Om (D.nd.l i) s = 1 := cyc_eq_one_of_mem_Ine hw hB hs
  have hι := (iotaOQ_continuous_injective D i).2
  constructor
  · have h := charpoly_conj D hD i π ρ hπ hρ hc s
    rw [hε, Units.val_one, one_zpow, one_smul, Matrix.charpoly_map, Matrix.charpoly_map] at h
    exact Polynomial.map_injective _ hι h
  · have h := chi_conj D hD i hc s
    rw [hε, Units.val_one, one_zpow, ← map_mul, ← map_one (iotaOQ D.nd D.naut i), ← Units.val_mul] at h
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left (Units.ext (hι h))

end GlobalTheory.ConjPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaQlLeInertiaOfFiniteExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InerQl

theorem root_eq_of_near {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m)
    {ζ η : Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  first
  | exact @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | (apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one ..)

theorem IK_fixes_Kur {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) {g : ↥(GK K)} (hg : g ∈ IK K)
    {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : (g : GQ l) c = c := by
  let Fx : Subgroup ↥(GK K) :=
    { carrier := {g | ∀ c ∈ MaximalUnramifiedExtension l, (g : GQ l) c = c}
      one_mem' := fun c _ => rfl
      mul_mem' := fun {a b} ha hb c hc => by
        show (a : GQ l) ((b : GQ l) c) = c
        rw [hb c hc, ha c hc]
      inv_mem' := fun {a} ha c hc => by
        show ((a : GQ l)⁻¹) c = c
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← ha c hc]
        exact AlgEquiv.symm_apply_apply _ _ }
  have hle : IK K ≤ Fx := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ c hc
    unfold MaximalUnramifiedExtension at hc
    induction hc using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm, hlm, hxm⟩ := hx
      have hxn : ‖x‖ ≤ 1 := by
        have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
        exact ((pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 this).le
      exact root_eq_of_near hm hlm hxm (by rw [← map_pow, hxm, map_one]) (hσ x hxn)
    | algebraMap x => exact (σ : GQ l).commutes x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  exact hle hg c hc

theorem IK_mem_Iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → g ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl K' h hN hF hS g hg c
  show (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c
  rw [Pl.PD_actB]
  have hc : (c : Om l) ∈ MaximalUnramifiedExtension l := (IntermediateField.mem_inf.1 c.2).2
  exact Pl.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ (IK_fixes_Kur _ hg hc)

end GlobalTheory.InerQl
end

