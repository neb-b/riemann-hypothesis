module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySupportedEquiv
section
open Formalism.UG

namespace GlobalTheory.UnitarySplit

variable {A : Type} [CommRing A] {n : ℕ}

noncomputable def adj (c : A →+* A) (J M : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  J⁻¹ * cT c M * J

theorem cT_add' (c : A →+* A) (M N : Matrix (Fin n) (Fin n) A) :
    cT c (M + N) = cT c M + cT c N := by
  ext i j; simp [cT]

theorem cT_smul' (c : A →+* A) (a : A) (M : Matrix (Fin n) (Fin n) A) :
    cT c (a • M) = c a • cT c M := by
  ext i j; simp [cT]

theorem cT_cT' (c : A →+* A) (hc : ∀ x, c (c x) = x) (M : Matrix (Fin n) (Fin n) A) :
    cT c (cT c M) = M := by
  ext i j; simp [cT, hc]

theorem adj_add (c : A →+* A) (J M N : Matrix (Fin n) (Fin n) A) :
    adj c J (M + N) = adj c J M + adj c J N := by
  simp only [adj, cT_add', Matrix.mul_add, Matrix.add_mul]

theorem adj_smul (c : A →+* A) (a : A) (J M : Matrix (Fin n) (Fin n) A) :
    adj c J (a • M) = c a • adj c J M := by
  simp only [adj, cT_smul', Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) :
    adj c J 1 = 1 := by
  rw [adj, cT_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hJ]

theorem adj_mul (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (M N : Matrix (Fin n) (Fin n) A) : adj c J (M * N) = adj c J N * adj c J M := by
  simp only [adj, cT_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem adj_adj (c : A →+* A) (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) A}
    (hJ : IsUnit J.det) (hh : cT c J = J) (M : Matrix (Fin n) (Fin n) A) :
    adj c J (adj c J M) = M := by
  have h1 : J * cT c J⁻¹ = 1 := by
    have := cT_mul c J⁻¹ J
    rw [Matrix.nonsing_inv_mul _ hJ, cT_one, hh] at this
    exact this.symm
  have h2 : cT c J⁻¹ * J = 1 := mul_eq_one_comm.mp h1
  simp only [adj, cT_mul, hh, cT_cT' c hc, Matrix.mul_assoc, h2, Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ hJ]

theorem mem_iff_adj (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (G : GL (Fin n) A) :
    G ∈ UJ c J ↔ adj c J (G : Matrix (Fin n) (Fin n) A) * (G : Matrix (Fin n) (Fin n) A) = 1 := by
  change cT c (G : Matrix (Fin n) (Fin n) A) * J * (G : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h
    rw [adj, Matrix.mul_assoc J⁻¹, Matrix.mul_assoc J⁻¹, h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have := congrArg (fun M => J * M) h
    simpa only [adj, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ,
      Matrix.mul_one] using this

theorem unitary_supported_equiv (A L : Type) [CommRing A] [CommRing L] (n : ℕ) (c : A →+* A)
    (e : A) (J : Matrix (Fin n) (Fin n) A) (π : A →+* L) (s : L → A)
    (hc : ∀ x, c (c x) = x) (he : e * e = e) (hec : e * c e = 0) (hJ : IsUnit J.det)
    (hh : cT c J = J) (hs : ∀ x, s (π x) = e * x) (hπ : ∀ a, π (s a) = a) :
    (∀ g : GL (Fin n) L, ∃ G ∈ UJ c J,
      (∀ i j, (e + c e) * ((G : Matrix (Fin n) (Fin n) A) - 1) i j
        = ((G : Matrix (Fin n) (Fin n) A) - 1) i j) ∧ bc π G = g) ∧
    ∀ G ∈ UJ c J, ∀ G' ∈ UJ c J,
      (∀ i j, (e + c e) * ((G : Matrix (Fin n) (Fin n) A) - 1) i j
        = ((G : Matrix (Fin n) (Fin n) A) - 1) i j) →
      (∀ i j, (e + c e) * ((G' : Matrix (Fin n) (Fin n) A) - 1) i j
        = ((G' : Matrix (Fin n) (Fin n) A) - 1) i j) → bc π G = bc π G' → G = G' := by
  have hπe : π e = 1 := by
    have := hπ (π 1)
    rwa [hs, mul_one, map_one] at this
  have hπc : π (c e) = 0 := by
    have := congrArg π hec
    rwa [map_mul, hπe, one_mul, map_zero] at this
  have hcc : c e * c e = c e := by rw [← map_mul, he]
  have hce : c e * e = 0 := by rw [mul_comm, hec]
  have key : ∀ M N : Matrix (Fin n) (Fin n) A, π.mapMatrix M = π.mapMatrix N → e • M = e • N := by
    intro M N h
    ext i j
    have h1 : π (M i j) = π (N i j) := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul, ← hs, h1]
  constructor
  · intro g
    have lift : ∀ M : Matrix (Fin n) (Fin n) L, π.mapMatrix (M.map s) = M := by
      intro M; ext i j; simp [hπ]
    set X : Matrix (Fin n) (Fin n) A := (g : Matrix (Fin n) (Fin n) L).map s with hX
    set Y : Matrix (Fin n) (Fin n) A := ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map s
      with hY
    have hYX : e • (Y * X) = e • (1 : Matrix (Fin n) (Fin n) A) := by
      apply key
      rw [map_mul, lift, lift, map_one, Units.inv_mul]
    have hXY : c e • (adj c J X * adj c J Y) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
      rw [← adj_mul c hJ, ← adj_smul, hYX, adj_smul, adj_one c hJ]
    obtain ⟨f, hf⟩ : ∃ f, f = 1 - e - c e := ⟨_, rfl⟩
    have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
    have hef : e * f = 0 := by rw [hf, mul_sub, mul_sub, he, hec]; ring
    have hfe : f * e = 0 := by rw [mul_comm, hef]
    have hcef : c e * f = 0 := by rw [hf, mul_sub, mul_sub, hce, hcc]; ring
    have hfce : f * c e = 0 := by rw [mul_comm, hcef]
    have hff : f * f = f := by
      have : f * f = f - f * e - f * c e := by
        conv_lhs => rw [show f * f = f * (1 - e - c e) by rw [← hf]]
        ring
      rw [this, hfe, hfce]; ring
    have hπf : π f = 0 := by rw [hf, map_sub, map_sub, map_one, hπe, hπc]; ring
    set M : Matrix (Fin n) (Fin n) A := e • X + c e • adj c J Y + f • 1 with hM
    have hadj : adj c J M = c e • adj c J X + e • Y + f • 1 := by
      rw [hM, adj_add, adj_add, adj_smul, adj_smul, adj_smul, adj_adj c hc hJ hh, hc, hcf,
        adj_one c hJ]
    have hMM : adj c J M * M = 1 := by
      rw [hadj, hM]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
        smul_smul, he, hec, hce, hcc, hef, hfe, hcef, hfce, hff, zero_smul, zero_add, add_zero,
        hYX, hXY, Matrix.mul_one]
      rw [← add_smul, ← add_smul, hf]
      simp
    refine ⟨⟨M, adj c J M, mul_eq_one_comm.mp hMM, hMM⟩, (mem_iff_adj c hJ _).mpr hMM, ?_, ?_⟩
    · intro i j
      change (e + c e) * (M - 1) i j = (M - 1) i j
      have : f * (M - 1) i j = 0 := by
        simp only [hM, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          mul_sub, mul_add, ← mul_assoc, hfe, hfce, hff]
        ring
      rw [hf] at this
      linear_combination -this
    · ext i j
      change π (M i j) = (g : Matrix (Fin n) (Fin n) L) i j
      simp only [hM, hX, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hπe,
        hπc, hπf, Matrix.map_apply, hπ]
      ring
  · intro G hG G' hG' h1 h2 h
    have h3 : e • (G : Matrix (Fin n) (Fin n) A) = e • (G' : Matrix (Fin n) (Fin n) A) :=
      key _ _ (congrArg Units.val h)
    have hinv : bc π G⁻¹ = bc π G'⁻¹ := by rw [map_inv, map_inv, h]
    have h4 : e • ((G⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = e • ((G'⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) :=
      key _ _ (congrArg Units.val hinv)
    have hi : ∀ K ∈ UJ c J, ((K⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = adj c J (K : Matrix (Fin n) (Fin n) A) := fun K hK =>
      Units.inv_eq_of_mul_eq_one_left ((mem_iff_adj c hJ K).mp hK)
    rw [hi G hG, hi G' hG'] at h4
    have h5 := congrArg (adj c J) h4
    rw [adj_smul, adj_smul, adj_adj c hc hJ hh, adj_adj c hc hJ hh] at h5
    ext i j
    have a1 := h1 i j
    have a2 := h2 i j
    have a3 := congrFun (congrFun h3 i) j
    have a5 := congrFun (congrFun h5 i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at a1 a2 a3 a5
    linear_combination a2 - a1 + a3 + a5

end GlobalTheory.UnitarySplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylRowAll

def coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R) (F : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (c (AddMonoidAlgebra.coeff F m))

theorem coeff_coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R)
    (F : MvPolynomial σ S) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (coeffMap c F) m = c (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

theorem coeffMap_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : S →+ R)
    (hc : ∀ (s : S) (a : R), c (s * φ a) = c s * a) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) S) (hF : F ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν) :
    coeffMap c F ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  have key : ∀ s : S, coeffMap c (s • F) ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
    unfold Formalism.GradedWeylDivisibility.weyl at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      intro s
      have : coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) =
          c s • Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) := by
        ext m
        rw [coeff_coeffMap, ← Formalism.GradedWeylDivisibility.lclosedeq_hw_map φ, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
          coeff_smul, coeff_smul, coeff_map, smul_eq_mul, smul_eq_mul, hc]
      show coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
    | zero =>
      intro s
      have : coeffMap c (s • (0 : MvPolynomial (Fin r × Fin n) S)) = 0 := by
        ext m; simp [coeff_coeffMap]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro s
      have : coeffMap c (s • (x + y)) = coeffMap c (s • x) + coeffMap c (s • y) := by
        ext m; simp [coeff_coeffMap, mul_add]
      rw [this]; exact Submodule.add_mem _ (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [smul_smul]; exact hx _
  simpa using key 1

theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    show map φ (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ∈ _
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct]

def toInv (R : Type) [CommRing R] : Polynomial R →+* HahnSeries ℤ R :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1 : R))

theorem coeff_zero_toInv (R : Type) [CommRing R] (p : Polynomial R) :
    (toInv R p).coeff 0 = p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    simp only [toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Polynomial.eval_monomial, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single]
    rcases k with _ | k
    · simp
    · rw [HahnSeries.coeff_single_of_ne]
      · simp
      · simp; omega

theorem isUnit_shift (R : Type) [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    IsUnit ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) := by
  set A : Matrix (Fin r) (Fin r) (PowerSeries R) :=
    1 + (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C with hA
  have h1 : IsUnit A.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (PowerSeries.constantCoeff (R := R)).mapMatrix A = 1 := by
      ext i j
      by_cases h : i = j <;> simp [hA, Matrix.one_apply, h]
    rw [this]; simp
  have h2 : IsUnit (A.map (HahnSeries.ofPowerSeries ℤ R)).det := by
    have := h1.map (HahnSeries.ofPowerSeries ℤ R)
    rwa [RingHom.map_det] at this
  have hT : (HahnSeries.single (-1 : ℤ) (1 : R)) * HahnSeries.single (1 : ℤ) (1 : R) = 1 := by
    rw [HahnSeries.single_mul_single]; simp
  have h3 : ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) = (HahnSeries.single (-1 : ℤ) (1 : R)) • A.map (HahnSeries.ofPowerSeries ℤ R) := by
    refine Matrix.ext fun i j => ?_
    simp only [hA, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
      map_mul, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C, mul_add, ← mul_assoc, hT,
      one_mul, toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Matrix.one_apply]
    rw [add_comm]
    split_ifs <;> simp
  rw [Matrix.isUnit_iff_isUnit_det, h3, Matrix.det_smul]
  exact ((IsUnit.of_mul_eq_one _ hT).pow _).mul h2

theorem rowAct_mem_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  set B : Matrix (Fin r) (Fin r) (Polynomial R) :=
    M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _) with hB
  obtain ⟨u, hu⟩ := isUnit_shift R M
  have h1 := Formalism.UG.Final.WeylGLStable (HahnSeries ℤ R) r n hn ν u⁻¹ _
    (map_mem_weyl (toInv R) hn ν _ (map_mem_weyl Polynomial.C hn ν f hf))
  rw [Formalism.UG.dwAct, inv_inv, hu, ← hB, ← map_rowAct] at h1
  have h2 := coeffMap_mem_weyl (HahnSeries.C : R →+* HahnSeries ℤ R)
    (HahnSeries.coeff.addMonoidHom (0 : ℤ)) (by
      intro s a
      simp [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]) hn ν _ h1
  have h3 : coeffMap (HahnSeries.coeff.addMonoidHom (0 : ℤ))
      (map (toInv R) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f))) =
      map (Polynomial.evalRingHom (0 : R)) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f)) := by
    ext m
    rw [coeff_coeffMap, coeff_map, coeff_map]
    exact coeff_zero_toInv R _
  have h4 : B.map (Polynomial.evalRingHom (0 : R)) = M := by
    ext i j
    simp [hB]
  have h5 : map (Polynomial.evalRingHom (0 : R)) (map Polynomial.C f) = f := by
    ext m
    simp [coeff_map]
  rwa [h3, map_rowAct, h4, h5] at h2

theorem rowAct_mem_weyl_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν,
      Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν :=
  fun R _ _ ν _ M f hf => rowAct_mem_weyl R le_rfl ν M f hf

end GlobalTheory.WeylRowAll
end
end

