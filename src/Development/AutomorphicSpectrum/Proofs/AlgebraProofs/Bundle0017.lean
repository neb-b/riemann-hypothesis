module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XHaLattice
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem sum_smul_cols_eq_mul_vec {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    [Fintype X] (B : Matrix X X C) (c : X → R) :
    (∑ j, c j • fun x => B x j) = B *ᵥ fun j => algebraMap R C (c j) := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

theorem mem_span_cols_iff {C R X : Type} [Field C] [CommRing R] [Algebra R C] [Fintype X]
    [DecidableEq X] (B : Matrix X X C) (hB : IsUnit B.det) (u : X → C) :
    u ∈ Submodule.span R (Set.range fun j x => B x j) ↔
      ∀ j, ∃ r : R, algebraMap R C r = (B⁻¹ *ᵥ u) j := by
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ j
    refine ⟨c j, ?_⟩
    rw [sum_smul_cols_eq_mul_vec, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · intro h
    choose c hc using h
    refine ⟨c, ?_⟩
    have e : (fun j => algebraMap R C (c j)) = B⁻¹ *ᵥ u := funext hc
    rw [sum_smul_cols_eq_mul_vec, e, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]

theorem exists_denominator {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) (hv : v.Integers R) [Fintype X] [Nonempty X] (w : X → C) :
    ∃ c : R, c ≠ 0 ∧ ∀ d : R,
      (∀ j, ∃ r : R, algebraMap R C r = algebraMap R C d * w j) ↔ d ∈ Ideal.span {c} := by
  classical
  by_cases hall : ∀ j, v (w j) ≤ 1
  · have h10 : (1 : R) ≠ 0 := by
      intro h
      have h' := congrArg (algebraMap R C) h
      simp at h'
    refine ⟨1, h10, fun d => ?_⟩
    constructor
    · intro _
      simp [Ideal.span_singleton_one]
    · intro _ j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ 1 * 1 := mul_le_mul' (hv.map_le_one d) (hall j)
        _ = 1 := one_mul 1
  · push Not at hall
    obtain ⟨j1, hj1⟩ := hall
    obtain ⟨j0, -, hj0⟩ :=
      Finset.exists_max_image Finset.univ (fun j => v (w j)) Finset.univ_nonempty
    have hgt : 1 < v (w j0) := lt_of_lt_of_le hj1 (hj0 j1 (Finset.mem_univ _))
    have hw0 : w j0 ≠ 0 := by
      intro h
      simp [h] at hgt
    have hinvle : v (w j0)⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hgt.le
    obtain ⟨c, hc⟩ := hv.exists_of_le_one hinvle
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact inv_ne_zero hw0 hc.symm
    refine ⟨c, hc0, fun d => ?_⟩
    rw [Ideal.mem_span_singleton, hv.dvd_iff_le, hc]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := h j0
      have e : algebraMap R C d = (algebraMap R C d * w j0) * (w j0)⁻¹ :=
        (mul_inv_cancel_right₀ hw0 _).symm
      rw [e, map_mul, ← hr]
      exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
    · intro h j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ v (w j0)⁻¹ * v (w j0) :=
            mul_le_mul' h (hj0 j (Finset.mem_univ _))
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hw0, map_one]

private theorem smul_algebra_map_char_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F]
    (χ : MulChar F R) (c : R) :
    (c • fun a => algebraMap R C (χ a)) = fun a => algebraMap R C (c * χ a) := by
  funext a
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]

theorem eig_rank_one : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ AA _ χ
  obtain ⟨B, hB, hM⟩ := AA.lat
  have key : ∀ d : R, d ∈ xIdeal AA.carrier χ ↔
      (d • fun a => algebraMap R C (χ a)) ∈ AA.carrier := fun d => by
    simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_denominator v hv (B⁻¹ *ᵥ fun a => algebraMap R C (χ a))
    refine ⟨c, hc0, ?_⟩
    ext d
    rw [key, hM, mem_span_cols_iff B hB, ← hc d]
    refine forall_congr' fun j => exists_congr fun r => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  · intro g
    constructor
    · rintro ⟨hgM, hg⟩
      have hint : ∀ x, ∃ r : R, algebraMap R C r = g x := AA.le_int hgM
      obtain ⟨r, hr⟩ := hint 1
      have hgf : g = fun a => algebraMap R C (r * χ a) := by
        funext a
        have h := hg a 1
        rw [smul_eq_mul, mul_one] at h
        rw [h, ← hr, map_mul]
        exact mul_comm _ _
      refine ⟨r, ?_, hgf⟩
      rw [key, smul_algebra_map_char_eq, ← hgf]
      exact hgM
    · rintro ⟨c, hc, rfl⟩
      rw [key, smul_algebra_map_char_eq] at hc
      refine ⟨hc, fun a x => ?_⟩
      simp only [smul_eq_mul, map_mul]
      ring

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotient
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg

theorem det_adapted {K V : Type} [Field K] [AddCommGroup V] [Module K V] (W : Submodule K V)
    {m n : ℕ} (bW cW : Module.Basis (Fin m) K W) (bQ cQ : Module.Basis (Fin n) K (V ⧸ W))
    (b c : Module.Basis (Fin (m + n)) K V)
    (hb1 : ∀ j, b (Fin.castAdd _ j) = bW j) (hb2 : ∀ j, W.mkQ (b (Fin.natAdd _ j)) = bQ j)
    (hc1 : ∀ j, c (Fin.castAdd _ j) = cW j) (hc2 : ∀ j, W.mkQ (c (Fin.natAdd _ j)) = cQ j) :
    b.det c = bW.det cW * bQ.det cQ := by
  have h1 : ∀ (i : Fin m) (x : W), b.repr (x : V) (Fin.castAdd _ i) = bW.repr x i := by
    intro i x
    have : (b.coord (Fin.castAdd _ i)).comp W.subtype = bW.coord i := by
      refine bW.ext fun j => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply,
        ← hb1, Module.Basis.repr_self, Finsupp.single_apply, Fin.castAdd_inj]
    exact LinearMap.congr_fun this x
  have h2 : ∀ (i : Fin n) (x : V), b.repr x (Fin.natAdd _ i) = bQ.repr (W.mkQ x) i := by
    intro i x
    have : b.coord (Fin.natAdd _ i) = (bQ.coord i).comp W.mkQ := by
      refine b.ext fun j => ?_
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have h0 : W.mkQ (b (Fin.castAdd n j)) = 0 := by
          rw [hb1]; simp
        have hne : Fin.castAdd n j ≠ Fin.natAdd m i := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [LinearMap.comp_apply, Module.Basis.coord_apply, h0, map_zero,
          Module.Basis.repr_self, Finsupp.single_apply, hne, if_false, Finsupp.coe_zero,
          Pi.zero_apply]
      · simp only [LinearMap.comp_apply, Module.Basis.coord_apply, hb2,
          Module.Basis.repr_self, Finsupp.single_apply, Fin.natAdd_inj]
    exact LinearMap.congr_fun this x
  have key : (b.toMatrix c).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (bW.toMatrix cW)
        (Matrix.of fun i j => b.repr (c (Fin.natAdd _ j)) (Fin.castAdd _ i)) 0
        (bQ.toMatrix cQ) := by
    ext (i | i) (j | j)
    · simp [Module.Basis.toMatrix_apply, hc1, h1]
    · simp [Module.Basis.toMatrix_apply]
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Module.Basis.toMatrix_apply, hc1, h2, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 (cW j).2]
      simp
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
        Module.Basis.toMatrix_apply, hc2, h2, Matrix.fromBlocks_apply₂₂]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁]

theorem deg_eq_subDeg_add_deg_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V)
    (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hex := fun i => (hL.1 i).elim fun b hb => GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
  choose bW bQ b hb hbW hbQ h1 h2 using hex
  obtain ⟨hS, hQ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V L W hL
  obtain ⟨-, eL⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V L _ (b i₀) b hL hb
  obtain ⟨fS, eS⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C W (sub C L W) _ (bW i₀) bW hS hbW
  obtain ⟨fQ, eQ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C (V ⧸ W) (quot C L W) _ (bQ i₀) bQ hQ hbQ
  rw [subDeg, eL, eS, eQ, ← finsum_add_distrib]
  · refine finsum_congr fun i => ?_
    rw [det_adapted W (bW i₀) (bW i) (bQ i₀) (bQ i) (b i₀) (b i) (h1 i₀) (h2 i₀) (h1 i) (h2 i),
      map_mul, WithZero.log_mul, mul_add]
    · exact (C.v i).ne_zero_iff.2 ((bW i₀).isUnit_det (bW i)).ne_zero
    · exact (C.v i).ne_zero_iff.2 ((bQ i₀).isUnit_det (bQ i)).ne_zero
  · refine fS.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]
  · refine fQ.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem apply_of_mem_eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {x : V}
    (hx : x ∈ eigSp ρ σ) (a : 𝓞 E) : ρ a x = σ (a : E) • x := by
  have := (Submodule.mem_iInf _).1 hx a
  simpa [sub_eq_zero] using this

theorem sum_smul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {N : ℕ} (t : Fin N → V)
    (y : Fin N → K) :
    ∑ i, y i • eigProj ρ σ (t i) =
      ∑ q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E),
        (y q.1 * σ (dualInt E q.2)) • ρ (RingOfIntegers.basis E q.2) (t q.1) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eigProj, LinearMap.sum_apply, Finset.smul_sum, mul_smul]

omit [Algebra A K] [IsScalarTower A K V] in
theorem mem_of_isFreeOn (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) {N : ℕ} (t : Fin N → V)
    (h : IsFreeOn ρ X t) (i : Fin N) : t i ∈ X := by
  have h1 : t i = ∑ k, (RingOfIntegers.basis E).repr 1 k • ρ (RingOfIntegers.basis E k) (t i) := by
    have := congrArg (fun a => ρ a (t i)) ((RingOfIntegers.basis E).sum_repr 1)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, map_one, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    exact this.symm
  rw [h1, h.2.2]
  refine Submodule.sum_mem _ fun k _ => ?_
  refine zsmul_mem ?_ _
  exact Submodule.subset_span ⟨(i, k), rfl⟩

theorem eigSub_eq_different_smul_eigQuot : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) (N : ℕ) (t : Fin N → V) (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → IsFreeOn ρ X t → (∀ x, x ∈ eigQuot ρ σ X ↔ d • x ∈ eigSub ρ σ X) ∧ eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) ∧ LinearIndependent K (fun i => eigProj ρ σ (t i)) ∧ Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
  intro A K _ _ _ _ V _ _ _ _ E _ _ ρ X N t σ d hinj hσ hd hX
  obtain ⟨he1, he2, -, he4⟩ := ProjEig.eigProj_spec K V E ρ σ
  obtain ⟨hd0, hd1, u, hu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt A K E σ d hinj hσ hd
  have hQ : eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) := by
    apply le_antisymm
    · unfold eigQuot
      rw [hX.2.2, Submodule.map_span_le]
      rintro _ ⟨⟨i, k⟩, rfl⟩
      obtain ⟨a, ha⟩ := hσ (RingOfIntegers.basis E k)
      have : eigProj ρ σ (ρ (RingOfIntegers.basis E k) (t i)) = a • eigProj ρ σ (t i) := by
        rw [← Module.End.mul_apply, he4, Module.End.mul_apply,
          apply_of_mem_eigSp ρ σ (he1 _), ← ha, IsScalarTower.algebraMap_smul]
      simp only [LinearMap.restrictScalars_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨t i, mem_of_isFreeOn ρ X t hX i, rfl⟩
  have hli : LinearIndependent K (fun i => eigProj ρ σ (t i)) := by
    rw [Fintype.linearIndependent_iff]
    intro y hy i
    rw [sum_smul_eigProj] at hy
    have h0 := Fintype.linearIndependent_iff.1 hX.1 _ hy
    calc y i = y i * ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) := by
          rw [hu, mul_one]
      _ = ∑ k, algebraMap A K (u k) * algebraMap A K d * (y i * σ (dualInt E k)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          have := h0 (i, k)
          simp only at this
          rw [this, mul_zero]
  have hsp : Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact he1 _
    · intro x hx
      rw [← he2 x hx]
      have hx' : x ∈ Submodule.span K (X : Set V) := by rw [hX.2.1]; trivial
      have : (Submodule.span K (X : Set V)).map (eigProj ρ σ) ≤
          Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) := by
        rw [Submodule.map_span_le]
        intro m hm
        apply Submodule.span_le_restrictScalars A K
        rw [← hQ]
        exact ⟨m, hm, rfl⟩
      exact this ⟨x, hx', rfl⟩
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hQ, hli, hsp⟩
  · refine ⟨?_, ?_⟩
    · rw [hQ, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, rfl⟩ := hx
      have : d • ∑ i, c i • eigProj ρ σ (t i) =
          ∑ i, (algebraMap A K (c i) * algebraMap A K d) • eigProj ρ σ (t i) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_mul, IsScalarTower.algebraMap_smul, mul_comm, mul_smul]
      rw [this, sum_smul_eigProj, hX.2.2]
      refine Submodule.sum_mem _ fun q _ => ?_
      obtain ⟨a, ha⟩ := hd1 q.2
      rw [mul_assoc, ← ha, ← map_mul, IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    · obtain ⟨m, -, rfl⟩ := hx
      exact Submodule.smul_mem _ d (show _ ∈ (eigSp ρ σ).restrictScalars A from he1 m)
  · obtain ⟨hx1, hx2⟩ := hx
    have hxe : x ∈ eigSp ρ σ := by
      have h2 : algebraMap A K d • x ∈ eigSp ρ σ := by
        rw [IsScalarTower.algebraMap_smul]; exact hx2
      exact (Submodule.smul_mem_iff _ hd0).1 h2
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hxe
    obtain ⟨y, rfl⟩ := hxe
    have hx1' : d • ∑ i, y i • eigProj ρ σ (t i) ∈ X := hx1
    rw [hX.2.2, Submodule.mem_span_range_iff_exists_fun] at hx1'
    obtain ⟨c, hc⟩ := hx1'
    have h3 : d • ∑ i, y i • eigProj ρ σ (t i) =
        ∑ i, (y i * algebraMap A K d) • eigProj ρ σ (t i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul, IsScalarTower.algebraMap_smul]
    rw [h3, sum_smul_eigProj] at hc
    have h4 : ∀ q, algebraMap A K (c q) = y q.1 * algebraMap A K d * σ (dualInt E q.2) := by
      refine Fintype.linearIndependent_iffₛ.1 hX.1 _ _ ?_
      rw [← hc]
      exact Finset.sum_congr rfl fun q _ => IsScalarTower.algebraMap_smul _ _ _
    rw [hQ]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h5 : y i = algebraMap A K (∑ k, u k * c (i, k)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← mul_one (y i), ← hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, h4]
      ring
    rw [h5, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
section
namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem exists_smul_mem_of_mem_span_val {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {V : Type} [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) {u : V}
    (hu : u ∈ Submodule.span C (L : Set V)) : ∃ c : C, c ≠ 0 ∧ c • u ∈ L := by
  have key : ∀ (a b : C) (x : V), b ≠ 0 → v a ≤ v b → b • x ∈ L → a • x ∈ L := by
    intro a b x hb hab hx
    have hvb : 0 < v b := (Valuation.pos_iff v).2 hb
    have h1 : v (a / b) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one hvb).2 hab
    obtain ⟨o, ho⟩ := hv.exists_of_le_one h1
    have h2 : a • x = o • (b • x) := by
      rw [← IsScalarTower.algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hb]
    rw [h2]
    exact L.smul_mem o hx
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    rcases le_total (v a) (v b) with h | h
    · exact ⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key a b y hb h hy)⟩
    · exact ⟨b, hb, by rw [smul_add]; exact L.add_mem (key b a x ha h hx) hy⟩
  | smul d x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hd : d = 0
    · exact ⟨1, one_ne_zero, by simp [hd]⟩
    · exact ⟨a / d, div_ne_zero ha hd, by rw [smul_smul, div_mul_cancel₀ _ hd]; exact hx⟩

theorem latIn_isLattice : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V), L.FG → U ≤ Submodule.span C (L : Set V) → (latIn L U).IsLattice C := by
  intro C _ v O _ _ hv V _ _ _ _ L U hL hU
  have hfg := GlobalTheory.CompanionTheory.Ar.HT.fg_inf_restrictScalars_of_integers C v O hv V L U hL
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (U.subtype.restrictScalars O) := Subtype.val_injective
    apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars O) hinj
    convert hfg using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  · intro s hs hli
    letI : IsFractionRing O C := hv.isFractionRing
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionId
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem indOrder_id_eq_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A :=
  PositivityTheory.HtPt.Mh.ind_id

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem ext_tensor_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) :=
  PositivityTheory.HtPt.Mh.ext_tensor

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotientStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_descending_one_dim_quotient : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A] (χ : A →ₐ[k] k) (e : A) (J : Ideal A), IsIdempotentElem e → χ e = 1 → (∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) → J ≤ Ideal.span {e} → J ≠ ⊥ → ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧ (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧ (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | exact GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembership
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaLattice

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L :=
  @PositivityTheory.Xgn.t_ha_lattice

end GlobalTheory.CompanionTheory.Ar.Num.HaLattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleBasisLatticeBundleFreeStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_basis_lattice_bundle_free : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O] [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V) (r : ℕ) (i : C.I), IsBun C L → (∀ c : k, C.v i (algebraMap k K c) ≤ 1) → (∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧ ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • ρ (b q.2) (x q.1)) → FreeAt C k (act k ρ) L r i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice <;> assumption)
end

