module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.RankOfQuasiIdem
section
open NumberField

namespace GlobalTheory.Reg.CellChart

section Lin
open Matrix

theorem det_of_inCell {R : Type} [CommRing R] {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) R)
    (h : InCell ix u) : (u.submatrix ix id).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (u.submatrix ix id) (fun i j hij => h.1 i j hij)]
  simp [h.2]

theorem rank_of_quasi_idem {L : Type} [Field L] {n : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (hP : P * P = N • P) (S : Submodule L (Fin n → L)) (hS : ∀ x, x ∈ S ↔ P.mulVec x = N • x) :
    P.rank = Module.finrank L S := by
  have : LinearMap.range P.mulVecLin = S := by
    ext x
    rw [hS, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP, Matrix.smul_mulVec]
    · intro h
      refine ⟨N⁻¹ • x, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [Matrix.rank, this]

theorem exists_minor {L : Type} [Field L] {n r : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (hu : P * u = N • u) (hc : InCell ix u) :
    ∃ κ : Fin r → Fin n, (P.submatrix ix κ).det ≠ 0 := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := GlobalTheory.exists_cols_det_ne_zero_of_mul (P.submatrix ix id) u (by
    rw [h, Matrix.det_smul, det_of_inCell ix u hc]; simp [hN])
  exact ⟨κ, hκ⟩

theorem eq_of_rows {L : Type} [Field L] {n r m : ℕ} (P : Matrix (Fin n) (Fin n) L) (hr : P.rank = r) (N : L)
    (hN : N ≠ 0) (ix κ : Fin r → Fin n) (hd : (P.submatrix ix κ).det ≠ 0) (u : Matrix (Fin n) (Fin m) L)
    (hu : P * u = N • u) : u = P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  have h1 := ((GlobalTheory.rank_minor_factorisation L n r P hr ix).1 κ hd)
  have h2 : N • u = N • (P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id) := by
    rw [← hu, ← Matrix.mul_smul, ← h, ← Matrix.mul_assoc, ← h1]
  exact smul_right_injective _ hN h2

end Lin

theorem exists_projector (E K : Type) [Field E] [NumberField E] [Field K] (emb : (E →+* ℂ) → (E →+* K))
    (hemb : Function.Injective emb) (O : Type) [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] (α : O →+* A) (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) A) (τ : E →+* ℂ) :
    ∃ (N : O) (p : Matrix (Fin n) (Fin n) A), N ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
      f.comp α = (algebraMap K R).comp (algebraMap O K) →
      (p.map f * p.map f = f (α N) • p.map f) ∧ ∀ x : Fin n → R,
        (∀ b : 𝓞 E, ((ρ b).map f).mulVec x = algebraMap K R (emb τ (b : E)) • x) ↔
          (p.map f).mulVec x = f (α N) • x := by
  obtain ⟨m, a, κ, h⟩ := GlobalTheory.exists_eigen_projector_ringOfIntegers E K emb hemb τ
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) κ
  choose t ht using hN
  refine ⟨N, ∑ k, α (t k) • ρ (a k), nonZeroDivisors.ne_zero N.2, fun R _ _ f hf => ?_⟩
  have hf' : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  obtain ⟨h1, h2⟩ := h R n (f.mapMatrix.comp ρ)
  set π := ∑ k, algebraMap K R (κ k) • (f.mapMatrix.comp ρ) (a k) with hπ
  have hp : (∑ k, α (t k) • ρ (a k)).map f = f (α N) • π := by
    ext i j
    have ht' : ∀ i, algebraMap O K (t i) = algebraMap O K N * κ i := fun i => (ht i).trans (Algebra.smul_def _ _)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hπ, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hf', ht',
      Finset.mul_sum, RingHom.comp_apply, RingHom.mapMatrix_apply, mul_assoc]
  have hu : IsUnit (f (α N)) := by
    rw [hf']
    exact (IsLocalization.map_units K N).map _
  have hππ : π * π = π := by
    ext i j
    have := h2 (fun k => π k j) (fun b => by
      funext k
      have := congrFun (congrFun (h1 b) k) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun this i
  rw [hp]
  refine ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, hππ], fun x => ⟨fun hx => ?_, fun hx b => ?_⟩⟩
  · rw [Matrix.smul_mulVec, h2 x hx]
  · rw [Matrix.smul_mulVec] at hx
    have hx' : π.mulVec x = x := hu.smul_left_cancel.mp hx
    have := congrArg (fun M => Matrix.mulVec M x) (h1 b)
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hx'] at this
    exact this

theorem loc_descr {K O A F : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] (α : O →+* A) (i : A →+* F)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (x : F)
    (hx : x ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))) :
    ∃ (a : A) (b : O) (m : ℕ), b ≠ 0 ∧ x * i (α b * g ^ m) = i a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨a, rfl⟩
    · exact ⟨1, 1, 1, one_ne_zero, by simp [hg]⟩
    · exact ⟨a, 1, 0, one_ne_zero, by simp⟩
  | algebraMap k =>
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O) k
    refine ⟨α a, b, 0, nonZeroDivisors.ne_zero b.2, ?_⟩
    rw [pow_zero, mul_one, hi', hi', ← map_mul, h]
  | add x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * (α b' * g ^ m') + a' * (α b * g ^ m), b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add (f := _), map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * a', b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add (f := _), map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring

theorem loc_lift {K O A F L : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] [Field L] [Algebra K L] (α : O →+* A) (i : A →+* F)
    (hinj : Function.Injective i)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (f : A →+* L)
    (hf : f.comp α = (algebraMap K L).comp (algebraMap O K)) (hfg : f g ≠ 0) :
    ∃ ψ : Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) →ₐ[K] L,
      ∀ a (h : i a ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))), ψ ⟨i a, h⟩ = f a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  have hf' : ∀ o, f (α o) = algebraMap K L (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  set R₀ := Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) with hR₀
  have hm : ∀ a, i a ∈ R₀ := fun a => Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
  let i₀ : A →+* R₀ := i.codRestrict R₀.toSubring hm
  letI : Algebra A R₀ := i₀.toAlgebra
  let S : Submonoid A := (IsUnit.submonoid R₀).comap i₀ ⊓ (IsUnit.submonoid L).comap f
  have hO : ∀ b : O, i₀ (α b) = algebraMap K R₀ (algebraMap O K b) := fun b => Subtype.ext (hi' b)
  have hK : ∀ b : O, b ≠ 0 → IsUnit (algebraMap O K b) := fun b hb =>
    IsLocalization.map_units K (⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ : nonZeroDivisors O)
  have hgS : g ∈ S := ⟨IsUnit.of_mul_eq_one (⟨(i g)⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R₀)
    (Subtype.ext (mul_inv_cancel₀ hg)), isUnit_iff_ne_zero.mpr hfg⟩
  have hbS : ∀ b : O, b ≠ 0 → α b ∈ S := fun b hb =>
    ⟨show IsUnit (i₀ (α b)) from hO b ▸ (hK b hb).map _, show IsUnit (f (α b)) from hf' b ▸ (hK b hb).map _⟩
  haveI : IsLocalization S R₀ := by
    refine (isLocalization_iff S R₀).mpr ⟨fun y => y.2.1, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨a, b, m, hb, h⟩ := loc_descr α i hi g hg z z.2
      exact ⟨⟨a, ⟨α b * g ^ m, S.mul_mem (hbS b hb) (S.pow_mem hgS m)⟩⟩, Subtype.ext h⟩
    · rw [hinj (congrArg Subtype.val h)]
  let φ : R₀ →+* L := IsLocalization.lift (M := S) (g := f) (fun y => y.2.2)
  have hφ : ∀ a, φ (i₀ a) = f a := fun a => IsLocalization.lift_eq (M := S) (g := f) (fun y => y.2.2) a
  have hc : φ.comp (algebraMap K R₀) = algebraMap K L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun o => ?_)
    simp only [RingHom.comp_apply]
    rw [← hO, hφ, hf']
  exact ⟨⟨φ, fun k => RingHom.congr_fun hc k⟩, fun a h => hφ a⟩

end GlobalTheory.Reg.CellChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriod
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

theorem mulVec_single_of_support {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (h : Matrix (Fin g) (Fin g) ℂ) (hs : ∀ j j', h j j' ≠ 0 → (e j).1 = (e j').1) (τ : T) (i : Fin (m τ)) :
    h *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 =
      ∑ i', h (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ) := by
  classical
  ext j
  obtain ⟨⟨τ', a⟩, rfl⟩ := e.symm.surjective j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single a (fun b _ hb => ?_) (by simp), Pi.single_eq_same, mul_one]
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hh
    exact hb (eq_of_heq (Sigma.mk.inj (e.symm.injective hh)).2).symm
  · rw [Finset.sum_eq_zero fun b _ => ?_]
    · by_contra hne
      have := hs _ _ hne
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact hτ this
    · rw [Pi.single_eq_of_ne, mul_zero]
      intro hh
      exact hτ (Sigma.mk.inj (e.symm.injective hh)).1


set_option maxHeartbeats 1000000 in
theorem frBor_of_triangular_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P P₀ : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (y y₀ : FrPt Xo c (CAt σ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P₀ → (∀ a, P₀ a = h₀ *ᵥ P a) → (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) → y.x = F.u k P → y₀.x = F.u k P₀ → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P₀ z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y₀.u τ i)) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y₀ y ∧ ∀ j, toC (t (some (e j)) : CAt σ) = h₀ j j := by
  intro E _ _ _ H Dw l Xo c σ g e F k P P₀ h₀ y y₀ hP hP₀ hh hs hy hy₀ hu hu₀
  classical
  obtain ⟨hdet, hpt, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P₀
    (LinearEquiv.refl _ _) h₀ hP hP₀ (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hh
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hdiag : ∀ j, h₀ j j ≠ 0 := by
    rw [GlobalTheory.PerBor.det_of_support (fun j => (e j).1) (fun j => ((e j).2 : ℕ)) hinj h₀ hs] at hdet
    exact fun j => Finset.prod_ne_zero_iff.1 hdet.ne_zero j (Finset.mem_univ j)
  have hx : y.x = y₀.x := hy.trans (hpt.trans hy₀.symm)
  let cf : ∀ τ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → CAt σ := fun τ i i' =>
    (h₀ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ)
  have hc : ∀ τ i, IsCombAt y₀.x (y₀.u τ) (cf τ i) (y.u τ i) := by
    intro τ i
    have d1 := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P₀ (Matrix.mulVecLin h₀) hP₀ hex
      _ _).1 (hu τ i)
    rw [Matrix.mulVecLin_apply, mulVec_single_of_support e h₀ (fun j j' h => (hs j j' h).1)] at d1
    have d2 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P₀ hP₀ _ (y₀.u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu₀ τ) _ (y.u τ i)).2 d1
    rw [hy₀]
    exact d2
  obtain ⟨t, ht⟩ := (frBor_calculus E H Dw l Xo c (CAt σ) y₀ y y).2.1 hx fun τ i =>
    ⟨cf τ i, isUnit_iff_ne_zero.2 (hdiag _), fun j hj => by
      by_contra hne
      have := (hs _ _ hne).2
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact absurd hj (not_lt.2 this), hc τ i⟩
  refine ⟨t, ht, fun j => ?_⟩
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
  rw [Equiv.apply_symm_apply]
  obtain ⟨a, ha, -, hac⟩ := ht.2.1 τ i
  have htan : IsTanAt y₀.x (y.u τ i) := by rw [← hx]; exact y.tan τ i
  have := (y₀.basis τ (y.u τ i) htan (y.eig τ i)).unique hac (hc τ i)
  rw [← ha, this]
  rfl

end GlobalTheory.FrameNorm
end

