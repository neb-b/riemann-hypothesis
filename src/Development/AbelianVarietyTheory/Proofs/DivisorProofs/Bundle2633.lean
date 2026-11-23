module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsCoeffLeOfHomogeneousTorusBound
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.CoefTorus

theorem sum_eq_of_coeff_ne_zero {n q : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q)
    {d : Fin n →₀ ℕ} (hd : AddMonoidAlgebra.coeff T d ≠ 0) : ∑ i, d i = q := by
  have := hT hd
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this

theorem aeval_smul_of_homogeneous {n q : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q)
    (c : ℂ) (z : Fin n → ℂ) : aeval (c • z) T = c ^ q * aeval z T := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [sum_eq_of_coeff_ne_zero hT (Finsupp.mem_support_iff.mp hd)]
  ring

theorem geom_root {N m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (h0 : 0 < m) (h2 : m < 2 * N) :
    ∑ j : Fin N, (ζ ^ m) ^ (j : ℕ) = if m = N then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) N]
  split_ifs with hm
  · subst hm; simp [hζ.pow_eq_one]
  · have hne : ζ ^ m ≠ 1 := by
      rw [Ne, hζ.pow_eq_one_iff_dvd]
      rintro ⟨c, hc⟩
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem key_sum {n q N : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (α : Fin n →₀ ℕ) (hq : q < N) (hα : ∀ i, α i < N) :
    ∑ k : Fin n → Fin N, aeval (fun i => ζ ^ (k i : ℕ)) T * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
      = ((AddMonoidAlgebra.coeff T α : ℤ) : ℂ) * (N : ℂ) ^ n := by
  have inner : ∀ d ∈ T.support, ∑ k : Fin n → Fin N,
      (algebraMap ℤ ℂ (AddMonoidAlgebra.coeff T d) * ∏ i, (ζ ^ (k i : ℕ)) ^ d i) * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
      = if d = α then ((AddMonoidAlgebra.coeff T α : ℤ) : ℂ) * (N : ℂ) ^ n else 0 := by
    intro d hd
    have hdq : ∀ i, d i ≤ q := fun i => by
      rw [← sum_eq_of_coeff_ne_zero hT (Finsupp.mem_support_iff.mp hd)]
      exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have e1 : ∑ k : Fin n → Fin N,
        (algebraMap ℤ ℂ (AddMonoidAlgebra.coeff T d) * ∏ i, (ζ ^ (k i : ℕ)) ^ d i) * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
        = algebraMap ℤ ℂ (AddMonoidAlgebra.coeff T d) * ∏ i, ∑ j : Fin N, (ζ ^ (d i + (N - α i))) ^ (j : ℕ) := by
      rw [Fintype.prod_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, ← pow_mul, ← pow_mul, mul_comm]
    rw [e1]
    have e2 : ∀ i, ∑ j : Fin N, (ζ ^ (d i + (N - α i))) ^ (j : ℕ)
        = if d i = α i then (N : ℂ) else 0 := by
      intro i
      rw [geom_root hζ (by have := hα i; omega) (by have := hα i; have := hdq i; omega)]
      have := hα i; have := hdq i
      by_cases h : d i = α i
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    simp_rw [e2]
    by_cases h : d = α
    · subst h; simp [Finset.prod_const, Finset.card_univ]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, d i ≠ α i := by
        by_contra hc; push_neg at hc; exact h (Finsupp.ext hc)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi]), mul_zero]
  simp_rw [aeval_def, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl inner, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · have h0 : AddMonoidAlgebra.coeff T α = 0 := not_not.mp (mt MvPolynomial.mem_support_iff.mpr h)
    simp [h0]

theorem coeff_le_of_torus_bound : ∀ (D q : ℕ) (T : MvPolynomial (Fin (D + 1)) ℤ) (M : ℝ), T.IsHomogeneous q →
    (∀ z : Fin (D + 1) → ℂ, z 0 = 1 → (∀ l, ‖z l‖ = 1) → ‖aeval z T‖ ≤ M) →
    ∀ α, |((AddMonoidAlgebra.coeff T α : ℤ) : ℝ)| ≤ M := by
  intro D q T M hT hM α
  have htor : ∀ z : Fin (D + 1) → ℂ, (∀ l, ‖z l‖ = 1) → ‖aeval z T‖ ≤ M := by
    intro z hz
    have h0 : z 0 ≠ 0 := by
      intro h; have := hz 0; simp [h] at this
    have hb := hM ((z 0)⁻¹ • z) (by simp [h0]) (by intro l; simp [norm_inv, hz])
    have e : z = z 0 • ((z 0)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
    rw [e, aeval_smul_of_homogeneous hT, norm_mul, norm_pow, hz 0, one_pow, one_mul]
    exact hb
  set N := q + (∑ i, α i) + 1 with hN
  have hNpos : N ≠ 0 := by omega
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)) N :=
    Complex.isPrimitiveRoot_exp N hNpos
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hNpos
  have hα : ∀ i, α i < N := fun i => by
    have := Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have key := key_sum hT hζ α (by omega) hα
  have hbound : ‖((AddMonoidAlgebra.coeff T α : ℤ) : ℂ) * (N : ℂ) ^ (D + 1)‖ ≤ (N : ℝ) ^ (D + 1) * M := by
    rw [← key]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k : Fin (D + 1) → Fin N,
        ‖aeval (fun i => ζ ^ (k i : ℕ)) T * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)‖ ≤ M := by
      intro k
      rw [norm_mul, norm_prod]
      simp only [norm_pow, hζn, one_pow, Finset.prod_const_one, mul_one]
      exact htor _ (fun l => by simp [hζn])
    refine (Finset.sum_le_sum fun k _ => this k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; exact le_refl _
  rw [norm_mul, norm_pow, Complex.norm_natCast, mul_comm] at hbound
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
  have := le_of_mul_le_mul_left hbound hpos
  simpa [Complex.norm_intCast] using this

end GlobalTheory.HSAmp.CoefTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BearsFlagUnitriangularIffMemCell
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.BearsCell

variable {ι : Type} {m : ι → ℕ}

theorem upM_map {K K' : Type} [Field K] [Field K'] (v : K → K') (h0 : v 0 = 0) (h1 : v 1 = 1) (u : Cell m → K) :
    (upM u).map v = upM fun j => v (u j) := by
  funext τ
  ext a b
  simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp [h0, h1]

theorem det_upM {K : Type} [Field K] (u : Cell m → K) (τ : ι) : (upM u τ).det = 1 :=
  (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K (m τ) _ 1 (fun _ _ h => Matrix.one_apply_ne h.ne) (by simp)).1

theorem exists_lu {K K' : Type} [Field K] [Field K'] {O : Subring K} (v : K → K') (ψ : O →+* K')
    (hv : ∀ x : O, v x = ψ x) (hu : ∀ x : O, ψ x ≠ 0 → (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ O) {g : Mat m K} (hg : Par 0 O g)
    {y₀ : Cell m → K'} (hP : Par m ⊤ (upM y₀ * (g.map v)⁻¹)) :
    ∃ (u : Cell m → K) (b : Mat m K), Par m O b ∧ g = b * upM u ∧ ∀ j, v (u j) = y₀ j := by
  have hgv := hg.map_of v ψ hv
  have hy : ∀ τ, (upM y₀ τ).det ≠ 0 := fun τ => (det_upM y₀ τ).trans_ne one_ne_zero
  have e : g.map v = (upM y₀ * (g.map v)⁻¹)⁻¹ * upM y₀ := by
    rw [Mat.mul_inv_rev, Mat.inv_inv hgv.det_ne, mul_assoc, Mat.inv_mul hy, mul_one]
  have hmin : ∀ τ (k : ℕ), ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det ≠ 0 ∧
      (((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det)⁻¹ ∈ O := fun τ k => by
    let N : Matrix {a : Fin (m τ) // (a : ℕ) < k} {a : Fin (m τ) // (a : ℕ) < k} O := fun a b => ⟨_, (hg τ).1 a.1 b.1⟩
    have e1 : (N.det : K) = ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det :=
      O.subtype.map_det N
    have e2 : ψ.mapMatrix N =
        (g.map v τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val := by
      ext a b
      exact (hv (N a b)).symm
    rw [← e1]
    refine hu _ ?_
    rw [ψ.map_det, e2, e]
    exact (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K' (m τ) _ _ (fun i j h => (hP.inv τ).2.2.2 i j i.2 h) (hP.inv.det_ne τ)).2 k
  choose y b h1 h2 h3 h4 using fun τ => GlobalTheory.FlagLU.exists_lu_subring K O (m τ) (g τ) (hg τ).1 (hmin τ)
  have hgb : g = b * upM (fun j : Cell m => y j.1 j.2) := funext h4
  have hd : ∀ τ, (b τ).det = (g τ).det := fun τ => by
    rw [hgb, Pi.mul_apply, Matrix.det_mul, det_upM, mul_one]
  have hb : Par m O b := fun τ => ⟨h2 τ, hd τ ▸ (hg τ).2.1, hd τ ▸ (hg τ).2.2.1, fun i j _ h => h3 τ i j h⟩
  have hU : Par 0 O (upM fun j : Cell m => y j.1 j.2) := by
    have := (hb.inv.mono (k' := 0) (fun _ => Nat.zero_le _) le_rfl).mul hg
    rwa [hgb, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul] at this
  refine ⟨_, b, hb, hgb, fun j => ?_⟩
  have e3 : g.map v = Mat.map b v * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [← upM_map v ((hv 0).trans (map_zero ψ)) ((hv 1).trans (map_one ψ)), ← Par.map_mul_of hb hU v ψ hv, ← hgb]
  have e4 : upM y₀ = (upM y₀ * (g.map v)⁻¹ * Mat.map b v) * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [mul_assoc, ← e3, mul_assoc, Mat.inv_mul hgv.det_ne, mul_one]
  have hc := hP.mul (hb.map_of v ψ hv)
  exact (congrFun (GlobalTheory.FlagCell2.upU_unique_of_lower K' (m j.1) _ _ _ (fun i k h => (hc j.1).2.2.2 i k i.2 h) (congrFun e4 j.1)) j.2).symm

theorem bears_iff : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (K : Type) [Field K] (p : Sp K ⟶ Y.X), A ∈ E.S (f (p (IsLocalRing.closedPoint K))) → ∀ y₀ : Cell m → K, Bears E' φ A (upM y₀) p ↔ ∃ u : Cell m → Y.Fn, upM u * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hf A K _ p hA y₀
  have hd : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ =>
    (Mat.det_map A (φ : X.Fn →+* Y.Fn) σ).trans_ne ((map_ne_zero _).2 (Fr.det_ne hA σ))
  have hr := GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf Y) p (IsLocalRing.closedPoint K)
  constructor
  · rintro ⟨A', hA', hP⟩
    obtain ⟨u, b, hb, hg, hu⟩ := exists_lu ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.valHom (M := ratOf Y) p _ hr)
      (fun _ => rfl) (fun x hx => (GlobalTheory.ZH.RatModel.isUnit_O_iff x).1
        ((GlobalTheory.ZH.RatModel.val_ne_zero_iff (M := ratOf Y) hr x).1 hx)) (hf.sub _ A' hA' A hA) hP
    refine ⟨u, (Fr.mem_iff hA').2 ?_, hu⟩
    have e : upM u * A.map φ * A'⁻¹ = b⁻¹ := by
      have e1 : upM u = b⁻¹ * (A' * (A.map φ)⁻¹) := by
        rw [hg, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul]
      rw [e1, mul_assoc b⁻¹, mul_assoc A', Mat.inv_mul hd, mul_one, mul_assoc, Mat.mul_inv (Fr.det_ne hA'), mul_one]
    rw [e]
    exact hb.inv
  · rintro ⟨u, hu, hy⟩
    refine ⟨_, hu, ?_⟩
    rw [mul_assoc, Mat.mul_inv hd, mul_one,
      upM_map ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.val_zero (M := ratOf Y) p)
        (GlobalTheory.ZH.RatModel.val_one (M := ratOf Y) p), show (fun j => (ratOf Y).val p (u j)) = y₀ from funext hy,
      Mat.mul_inv fun τ => (det_upM y₀ τ).trans_ne one_ne_zero]
    exact Par.one

end GlobalTheory.FlagCell2.BearsCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHomStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P) (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X), CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) → CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 → ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  first | (exact @GlobalTheory.AV.FamHom.main) | (exact GlobalTheory.AV.FamHom.main) | (intros; apply GlobalTheory.AV.FamHom.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegeneration
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdIndep

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.BoxFamIndep

theorem tensor_indep (F O₁ O₂ : Type) [Field F] [CommRing O₁] [Algebra F O₁] [CommRing O₂] [Algebra F O₂]
    {A₁ A₂ : Type} {m n : ℕ} (β₁ : A₁ → Fin m → O₁) (β₂ : A₂ → Fin n → O₂)
    (h₁ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β₁ α l = 0) → c = 0)
    (h₂ : ∀ c : Fin n → F, (∀ α, ∑ l, c l • β₂ α l = 0) → c = 0) (c : Fin m × Fin n → F)
    (hc : ∀ α₁ α₂, ∑ a, c a • (β₁ α₁ a.1 ⊗ₜ[F] β₂ α₂ a.2) = 0) : c = 0 := by
  have key : ∀ α₁ α₂, ∑ l : Fin m, β₁ α₁ l ⊗ₜ[F] (∑ a : Fin n, c (l, a) • β₂ α₂ a) = 0 := by
    intro α₁ α₂
    rw [← hc α₁ α₂, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun a _ => TensorProduct.tmul_smul _ _ _
  have key2 : ∀ l, (fun a : Fin n => c (l, a)) = 0 := fun l => h₂ _ fun α => by
    refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
    refine congrFun (h₁ (fun l => φ (∑ a : Fin n, c (l, a) • β₂ α a)) fun α₀ => ?_) l
    have := congrArg (fun t => TensorProduct.rid F O₁ (LinearMap.lTensor O₁ φ t)) (key α₀ α)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum (LinearMap.lTensor O₁ φ), map_sum (TensorProduct.rid F O₁), LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, map_zero] using this
  funext a
  exact congrFun (key2 a.1) a.2

theorem exists_test₂ {F : Type} [Field F] {X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of F))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of F)) (x₁ : X₁) (x₂ : X₂) {A₁ A₂ : Type} {U₁ : A₁ → X₁.Opens}
    {U₂ : A₂ → X₂.Opens} (hx₁ : ∀ α, x₁ ∈ U₁ α) (hx₂ : ∀ α, x₂ ∈ U₂ α) {m n : ℕ}
    (s₁ : ∀ α, Fin m → Γ(X₁, U₁ α)) (s₂ : ∀ α, Fin n → Γ(X₂, U₂ α))
    (hs₁ : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p₁ x₁ (c l) * gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l) = 0) → c = 0)
    (hs₂ : ∀ c : Fin n → F, (∀ α, ∑ l, germOf p₂ x₂ (c l) * gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l) = 0) → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂), r₁ ≫ p₁ = q ∧ r₂ ≫ p₂ = q ∧
      (∀ z α, r₁ z ∈ U₁ α) ∧ (∀ z α, r₂ z ∈ U₂ α) ∧ ∀ c : Fin m × Fin n → F,
        (∀ α₁ α₂ z, ∑ a, germOf q z (c a) * (gs r₁ z (U₁ α₁) (s₁ α₁ a.1) * gs r₂ z (U₂ α₂) (s₂ α₂ a.2)) = 0) →
          c = 0 := by
  let : Algebra F (X₁.presheaf.stalk x₁) := (germOf p₁ x₁).toAlgebra
  let : Algebra F (X₂.presheaf.stalk x₂) := (germOf p₂ x₂).toAlgebra
  have h := tensor_indep F _ _ (fun α l => gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l)) (fun α l => gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l))
    (fun c hc => hs₁ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
    (fun c hc => hs₂ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
  obtain ⟨B, _, _, e₁, e₂, h⟩ : ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (e₁ : X₁.presheaf.stalk x₁ →ₐ[F] B)
      (e₂ : X₂.presheaf.stalk x₂ →ₐ[F] B), ∀ c : Fin m × Fin n → F, (∀ α₁ α₂, ∑ a, c a •
        (e₁ (gs (𝟙 X₁) x₁ (U₁ α₁) (s₁ α₁ a.1)) * e₂ (gs (𝟙 X₂) x₂ (U₂ α₂) (s₂ α₂ a.2))) = 0) → c = 0 :=
    ⟨TensorProduct F (X₁.presheaf.stalk x₁) (X₂.presheaf.stalk x₂), inferInstance, inferInstance,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, fun c hc => h c fun α₁ α₂ => by
        rw [← hc α₁ α₂]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]⟩
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    (Spec.map (CommRingCat.ofHom e₁.toRingHom) : _ ⟶ Spec (X₁.presheaf.stalk x₁)) ≫ X₁.fromSpecStalk x₁,
    (Spec.map (CommRingCat.ofHom e₂.toRingHom) : _ ⟶ Spec (X₂.presheaf.stalk x₂)) ≫ X₂.fromSpecStalk x₂,
    ?_, ?_, fun z α => fromSpecStalk_mem x₁ (hx₁ α) _, fun z α => fromSpecStalk_mem x₂ (hx₂ α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₁.commutes a
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₂.commutes a
  · refine h c fun α₁ α₂ => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc α₁ α₂ z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_)
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · rw [gs_fromSpecStalk x₁ (hx₁ _)]
      exact (germOf_map (B := X₁.presheaf.stalk x₁) (𝟙 _) (CommRingCat.ofHom e₁.toRingHom) z _).symm
    · rw [gs_fromSpecStalk x₂ (hx₂ _)]
      exact (germOf_map (B := X₂.presheaf.stalk x₂) (𝟙 _) (CommRingCat.ofHom e₂.toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem exists_pt {D : DegPre R} {m : ℕ} (b : Fin m → Fam D F k) (hb : LinearIndependent F b) :
    ∃ (x : (DegPre.BF D F).left) (jj : D.X → Fin 4 → D.P.L.ι),
      (∀ α, x ∈ LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) ∧ ∀ c : Fin m → F,
      (∀ α, ∑ l, germOf (B := CommRingCat.of F) (fst (TF (R := R) F) D.P.A).left x (c l) *
        gs (𝟙 _) x (LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) (((b l).s α).f (jj α)) = 0) → c = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  refine ⟨_, _, hx, fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => ?_⟩
  refine fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
  refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
  rw [Category.id_comp]
  exact hc α

theorem exists_pair {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) [IsIso (lift p₁ p₂)]
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ (DegPre.BF D₁ F).left)
    (r₂ : Z ⟶ (DegPre.BF D₂ F).left) (h₁ : r₁ ≫ (fst (TF (R := R) F) D₁.P.A).left = q)
    (h₂ : r₂ ≫ (fst (TF (R := R) F) D₂.P.A).left = q) :
    ∃ ρ : Z ⟶ (DegPre.BF D F).left, ρ ≫ (TF (R := R) F ◁ p₁).left = r₁ ∧ ρ ≫ (TF (R := R) F ◁ p₂).left = r₂ ∧
      ρ ≫ (fst (TF (R := R) F) D.P.A).left = q := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r₁' : T ⟶ DegPre.BF D₁ F := Over.homMk r₁ (by
    rw [← Over.w (fst (TF (R := R) F) D₁.P.A), ← Category.assoc, h₁]; rfl)
  let r₂' : T ⟶ DegPre.BF D₂ F := Over.homMk r₂ (by
    rw [← Over.w (fst (TF (R := R) F) D₂.P.A), ← Category.assoc, h₂]; rfl)
  let ρ : T ⟶ DegPre.BF D F := lift q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _))
  have hρ₁ : ρ ≫ TF (R := R) F ◁ p₁ = r₁' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₁.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_fst _ _ _ _
  have hρ₂ : ρ ≫ TF (R := R) F ◁ p₂ = r₂' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₂.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_snd _ _ _ _
  exact ⟨ρ.left, congrArg (fun g => g.left) hρ₁, congrArg (fun g => g.left) hρ₂,
    congrArg (fun g => g.left) (lift_fst q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _)))⟩

theorem boxFam₂_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m n : ℕ) (b₁ : Fin m → Fam D₁ F k) (b₂ : Fin n → Fam D₂ F k) (b : Fin m × Fin n → Fam D F k), LinearIndependent F b₁ → LinearIndependent F b₂ → (∀ a, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k (b a) (b₁ a.1) (b₂ a.2)) → LinearIndependent F b := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w F _ _ k m n b₁ b₂ b hb₁ hb₂ hb
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := hS.lim
  obtain ⟨x₁, j₁, hx₁, H₁⟩ := exists_pt b₁ hb₁
  obtain ⟨x₂, j₂, hx₂, H₂⟩ := exists_pt b₂ hb₂
  obtain ⟨Z, q, r₁, r₂, hq₁, hq₂, hr₁, hr₂, H⟩ := exists_test₂ (F := F) (fst (TF (R := R) F) D₁.P.A).left
    (fst (TF (R := R) F) D₂.P.A).left x₁ x₂ hx₁ hx₂ (fun α l => ((b₁ l).s α).f (j₁ α))
    (fun α l => ((b₂ l).s α).f (j₂ α)) H₁ H₂
  obtain ⟨ρ, hρ₁, hρ₂, hρq⟩ := exists_pair p₁ p₂ q r₁ r₂ hq₁ hq₂
  refine H c fun α₁ α₂ z => ?_
  obtain ⟨α, rfl, rfl⟩ : ∃ α, q₁ α = α₁ ∧ q₂ α = α₂ := by
    obtain ⟨α, h⟩ := hS.xsum.2 (α₁, α₂)
    exact ⟨α, congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB z
  have hm := hJ.mem (DegPre.famφ D F α) ρ
  have E := (gs_comb c b α _ ρ z hm).symm.trans
    ((congrArg (fun s : Fam D F k => gs (Y := Z) ρ z _ ((s.s α).f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => hb a α Z ρ z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [hρ₁, hρ₂] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b a).s α) ρ z J =
      sval ((b₁ a.1).s (q₁ α)) r₁ z J₁ * sval ((b₂ a.2).s (q₂ α)) r₂ z J₂ := ⟨_, E'⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₁ z (LB.wchart D₁.P.L (DegPre.famφ D₁ F (q₁ α)) (j₁ (q₁ α))) (((b₁ l).s (q₁ α)).f (j₁ (q₁ α))) =
      v * sval ((b₁ l).s (q₁ α)) r₁ z J₁ :=
    ⟨_, fun l => sec_trans _ r₁ z (hr₁ z _) (hJ₁.mem _ r₁)⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₂ z (LB.wchart D₂.P.L (DegPre.famφ D₂ F (q₂ α)) (j₂ (q₂ α))) (((b₂ l).s (q₂ α)).f (j₂ (q₂ α))) =
      v * sval ((b₂ l).s (q₂ α)) r₂ z J₂ :=
    ⟨_, fun l => sec_trans _ r₂ z (hr₂ z _) (hJ₂.mem _ r₂)⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((v₁ * v₂) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((congrArg₂ (· * ·) (hv₁ a.1) (hv₂ a.2)).trans (_root_.mul_mul_mul_comm _ _ _ _)).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end GlobalTheory.ProdIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelOfSurjectiveAbelianVarietyHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem cancel_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left →
    ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  intro K _ A B p hp C f g h
  have hB : IsIntegral B.X.left := (_root_.GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B).1
  have hsep : IsSeparated C.X.hom := C.ab.proper.toIsSeparated
  apply Subtype.ext
  change f.hom = g.hom
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated C.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) p.hom.left ?_)
  have := congrArg (fun u => (Hom.hom u).left) h
  simpa only [comp_hom, Over.comp_left] using this

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreConstPreconnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.GFib

theorem latAt_const_on_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  intro o Ω _ _ _ _ Y G _ _ hG Z q z hpre hrk I T f hf gγ ζ L hL hζ hu hγ hext X _ _ _ m c w w' hw hw'
  obtain ⟨r₀, hr⟩ := hrk
  haveI : IsNoetherianRing o := by
    haveI := ArithBase.ded (o := o) (Ω := Ω)
    infer_instance
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.Z := {}
  exact GlobalTheory.fibre_const_of_specializes_invariant Y.Z Z q.base q.continuous z hpre
    (fun v => LatAt f gγ ζ L m c v)
    (fun a b ha hb hab => latAt_iff_of_specializes hG hL hζ hu hf hγ m c hab (hr a ha) (hr b hb)
      (fun t => hext t b hb)) w w' hw hw'

end GlobalTheory.UPoinc.GFib
end

