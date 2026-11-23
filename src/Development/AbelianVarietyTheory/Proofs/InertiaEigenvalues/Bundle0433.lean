module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0412
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToOD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.CrisBounded

theorem dvd_of_ev_eq_zero {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l))
    (m : ℕ) (y : Per.BdRp l) (hy : Per.ev l m y = 0) : ainfToBdRp l d ^ m ∣ y := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h2 := hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  have h3 : d ∣ GlobalTheory.MemLoc.xi e := Ideal.mem_span_singleton.1 (h2 ▸ Ideal.mem_span_singleton_self _)
  have h4 := ((GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).1 m y).1 ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m y).2 hy)
  exact (pow_dvd_pow_of_dvd (map_dvd (GlobalTheory.MemLoc.aDp l) h3) m).trans h4

theorem bdd_crisP {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ) :
    ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Ainf l,
      ainfToBdRp l d ^ m ∣ (l : Per.BdRp l) ^ N * acrisToBdRp l x - ainfToBdRp l a := by
  obtain ⟨N, hN⟩ := (isCrisP_crisP l).bdd m
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN x
  refine ⟨a, dvd_of_ev_eq_zero hd m _ ?_⟩
  rw [map_sub, sub_eq_zero]
  exact ha.trans (GlobalTheory.MemLoc.CrisUnique.ev_aDp m a).symm

theorem bdd_tensor {Z O A C D : Type} [CommRing Z] [CommRing O] [Algebra Z O] [Module.Free Z O]
    [Module.Finite Z O] [CommRing A] [Algebra Z A] [CommRing C] [Algebra Z C] [CommRing D] [Algebra Z D]
    (f : A →ₐ[Z] D) (j : C →ₐ[Z] D) (t : D) (n : ℕ) (h : ∀ x : C, ∃ a : A, t ∣ (n : D) * j x - f a)
    (z : O ⊗[Z] C) : ∃ y : O ⊗[Z] A, ((1 : O) ⊗ₜ[Z] t) ∣
      (n : O ⊗[Z] D) * Algebra.TensorProduct.map (AlgHom.id O O) j z -
        Algebra.TensorProduct.map (AlgHom.id O O) f y := by
  let b := Module.Free.chooseBasis Z O
  choose a c hc using fun i => h (GlobalTheory.Decompl.crd b i z)
  refine ⟨∑ i, b i ⊗ₜ[Z] a i, ∑ i, b i ⊗ₜ[Z] c i, GlobalTheory.Decompl.ext_crd b fun i => ?_⟩
  rw [map_sub, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_mul,
    GlobalTheory.Decompl.crd_sum, GlobalTheory.Decompl.crd_sum, hc]

theorem bdd_crisToOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m
  rw [show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]
  obtain ⟨N, hN⟩ := bdd_crisP (ϖ.span_ev_eis 1) m
  refine ⟨N, fun z => ?_⟩
  obtain ⟨y, hy⟩ := bdd_tensor (ainfToBdRp l) (acrisToBdRp l) _ (l ^ N)
    (fun x => by rw [Nat.cast_pow]; exact hN x) z
  refine ⟨y, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← Nat.cast_pow]
  exact hy

end GlobalTheory.BKReal.CrisBounded
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff (l * n + i) z

theorem coeff_frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) (n : ℕ) :
    coeff n (frobSlice l i z) = coeff (l * n + i) z := by
  simp [frobSlice]

namespace Hom

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

def rdivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ F.mat τ * Y = h • (1 : Matrix κ κ K⟦X⟧)}

def ldivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ Y * F.mat τ = h • (1 : Matrix ι ι K⟦X⟧)}

theorem bdd_mul {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f * g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  exact ⟨a * b, fun n => by
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0 hb0
      (f := f) (g := g) (by simpa using ha) (by simpa using hb) n⟩

theorem bdd_add {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f + g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨max a b, fun n => by
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha n) (hb n))⟩

theorem bdd_smul_matrix {μ ν : Type} {b : K⟦X⟧} {Y : Matrix μ ν K⟦X⟧} (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c)
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n ((b • Y) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨c, hc⟩ := hY
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  refine ⟨a * max c 0, fun i j n => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0
    (le_max_right c 0) (f := b) (g := Y i j) (by simpa using ha)
    (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _)) n

theorem rdivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (hy : y ∈ F.rdivSet τ) :
    x + y ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.mul_add, h₁, h₂, add_smul]

theorem ldivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (hy : y ∈ F.ldivSet τ) :
    x + y ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.add_mul, h₁, h₂, add_smul]

theorem rdivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.mul_smul, h, smul_smul]

theorem ldivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.smul_mul, h, smul_smul]

end Hom

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
section
namespace GlobalTheory


open Matrix in
theorem blockDecomposition_baseChange {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) :
    ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)),
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K),
        (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) →
        ∀ u, e' ((M.map φ).mulVec u) =
          ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  classical

  have hext : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) K), (∀ v, X *ᵥ v = Y *ᵥ v) → X = Y :=
    fun X Y h => Matrix.toLin'.injective (LinearMap.ext fun v => by
      simpa only [Matrix.toLin'_apply] using h v)

  obtain ⟨A₁, hA₁⟩ : ∃ A : Matrix (Fin r) (Fin n) K, ∀ v, A *ᵥ v = (e v).1 :=
    ⟨LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : Matrix (Fin t) (Fin n) K, ∀ v, A *ᵥ v = (e v).2 :=
    ⟨LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B : Matrix (Fin n) (Fin r) K, ∀ p, B *ᵥ p = e.symm (p, 0) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl K _ _), fun p => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B : Matrix (Fin n) (Fin t) K, ∀ q, B *ᵥ q = e.symm (0, q) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K _ _), fun q => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩

  have h11 : A₁ * B₁ = 1 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₁, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have h12 : A₁ * B₂ = 0 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₁, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h21 : A₂ * B₁ = 0 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₂, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h22 : A₂ * B₂ = 1 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₂, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hBA : B₁ * A₁ + B₂ * A₂ = 1 := hext _ _ fun u => by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₂, hB₁, hB₂,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, LinearEquiv.symm_apply_apply,
      Matrix.one_mulVec]

  have h11' : A₁.map φ * B₁.map φ = 1 := by
    rw [← Matrix.map_mul, h11, Matrix.map_one _ φ.map_zero φ.map_one]
  have h12' : A₁.map φ * B₂.map φ = 0 := by
    rw [← Matrix.map_mul, h12, Matrix.map_zero _ φ.map_zero]
  have h21' : A₂.map φ * B₁.map φ = 0 := by
    rw [← Matrix.map_mul, h21, Matrix.map_zero _ φ.map_zero]
  have h22' : A₂.map φ * B₂.map φ = 1 := by
    rw [← Matrix.map_mul, h22, Matrix.map_one _ φ.map_zero φ.map_one]
  have hBA' : B₁.map φ * A₁.map φ + B₂.map φ * A₂.map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add φ φ.map_add, hBA,
      Matrix.map_one _ φ.map_zero φ.map_one]

  refine ⟨LinearEquiv.ofLinearMap ((Matrix.toLin' (A₁.map φ)).prod (Matrix.toLin' (A₂.map φ)))
    ((Matrix.toLin' (B₁.map φ)).coprod (Matrix.toLin' (B₂.map φ))) ?_ ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨p, q⟩ := x
    refine Prod.ext ?_ ?_ <;>
      simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, h11', h12', h21', h22']
  · refine LinearMap.ext fun u => ?_
    have key : (B₁.map φ * A₁.map φ) *ᵥ u + (B₂.map φ * A₂.map φ) *ᵥ u = u := by
      rw [← Matrix.add_mulVec, hBA', Matrix.one_mulVec]
    simpa [Matrix.mulVec_mulVec] using key
  · intro M P d h u

    have hM₁ : A₁ * M = P * A₁ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₁, h v]
    have hM₂ : A₂ * M = Matrix.diagonal d * A₂ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₂, hA₂, h v]
      funext c
      rw [Matrix.mulVec_diagonal]
    have hM₁' : A₁.map φ * M.map φ = P.map φ * A₁.map φ := by
      rw [← Matrix.map_mul, hM₁, Matrix.map_mul]
    have hM₂' : A₂.map φ * M.map φ = Matrix.diagonal (fun c => φ (d c)) * A₂.map φ := by
      rw [← Matrix.map_mul, hM₂, Matrix.map_mul, Matrix.diagonal_map φ.map_zero]
    refine Prod.ext ?_ (funext fun c => ?_)
    · change A₁.map φ *ᵥ (M.map φ *ᵥ u) = P.map φ *ᵥ (A₁.map φ *ᵥ u)
      rw [Matrix.mulVec_mulVec, hM₁', ← Matrix.mulVec_mulVec]
    · change (A₂.map φ *ᵥ (M.map φ *ᵥ u)) c = φ (d c) * (A₂.map φ *ᵥ u) c
      rw [Matrix.mulVec_mulVec, hM₂', ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopePointFactorsThroughSection
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isHausdorff_of_le_ideal {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (hJ : IsHausdorff J R) :
    IsHausdorff I R := by
  refine ⟨fun x hx => hJ.haus x fun n => ?_⟩
  have h1 := hx n
  rw [SModEq.sub_mem] at h1 ⊢
  exact Submodule.smul_mono_left (Ideal.pow_right_mono h n) h1

theorem map_frobenius_charP {l : ℕ} [Fact l.Prime] {R O : Type} [CommRing R] [CharP R l] [CommRing O] [CharP O l]
    (ψ : R →+* O) (x : WittVector l R) :
    WittVector.map ψ (WittVector.frobenius x) = WittVector.frobenius (WittVector.map ψ x) := by
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem hom_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (a : P.A) : (g.comp f).f a = g.f (f.f a) := rfl

theorem hom_eq_id_apply {l : ℕ} {R : Type} [CommRing R] {P P' : Obj l R} (g : Hom P' P) (f : Hom P P')
    (h : g.comp f = Hom.id P) (a : P.A) : g.f (f.f a) = a := by
  rw [← hom_comp_apply, h]; rfl

theorem hom_eq_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' Q : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (g' : Hom Q P'') (f' : Hom P Q) (h : g.comp f = g'.comp f') (a : P.A) : g.f (f.f a) = g'.f (f'.f a) := by
  rw [← hom_comp_apply, h]; rfl

theorem mapE_facts {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O) (hx0 : ψ bk.flat ≠ 0)
    (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O) :
    WittVector.map ψ (bk.ev bk.E) ∈ nonZeroDivisors (WittVector l O) ∧
    IsHausdorff ((Ideal.span {((l : ℕ) : WittVector l (OCb l))} ⊔ Ideal.span {bk.ev bk.E}).map (WittVector.map ψ))
      (WittVector l O) := by
  obtain ⟨w, -, hwE⟩ := _root_.GlobalTheory.BSP.EisImage.map_E_eq l K bk O ψ hxu
  have hE0 : WittVector.map ψ (bk.ev bk.E) ≠ 0 := fun h => by
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := O)) h
    rw [hwE, map_add (f := _), map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, map_zero] at h1
    exact hx0 ((pow_eq_zero_iff bk.deg_pos.ne').1 h1)
  refine ⟨mem_nonZeroDivisors_of_ne_zero hE0, isHausdorff_of_le_ideal ?_
    (_root_.GlobalTheory.WittTeichComplete.main l O (ψ bk.flat) hx0 hxc).2.toIsHausdorff⟩
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
  refine sup_le le_sup_left ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hwE]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ bk.deg_pos))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem isHausdorff_map_congr {A B : Type} [CommRing A] [CommRing B] {I J : Ideal A} {g h : A →+* B} (hIJ : I = J)
    (hgh : g = h) (H : IsHausdorff (J.map h) B) : IsHausdorff (I.map g) B := by
  subst hIJ; subst hgh; exact H

theorem envPoint_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X))
    (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O)
    (hx0 : ψ bk.flat ≠ 0) (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O)
    (F : En.Q.A →+* WittVector l O) (hFφ : ∀ a, F (En.Q.D.φ a) = WittVector.frobenius (F a))
    (hFinl : F.comp En.inl.f = WittVector.map ψ) (s : Hom En.Q (ainfObj K)) (hs1 : s.comp En.inl = Hom.id _)
    (hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X))) (a : En.Q.A) :
    F a = WittVector.map ψ (s.f a) := by
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b
  have htfW : ∀ c : WittVector l O, ((l : ℕ) : WittVector l O) * c = 0 → c = 0 := fun c hc =>
    WittVector.eq_zero_of_p_mul_eq_zero c (by rw [mul_comm, hc])
  obtain ⟨F', hF'a⟩ : ∃ F' : En.Q.A →+* WittVector l O, ∀ a, F' a = WittVector.map ψ (s.f a) :=
    ⟨(WittVector.map ψ).comp s.f, fun _ => rfl⟩
  have hF'φ : ∀ a, F' (En.Q.D.φ a) = WittVector.frobenius (F' a) := fun a =>
    ((hF'a _).trans (congrArg (WittVector.map ψ) (Hom.f_φ s a))).trans
      ((map_frobenius_charP ψ (s.f a)).trans (congrArg WittVector.frobenius (hF'a a).symm))
  have hinl : ∀ b, F (En.inl.f b) = F' (En.inl.f b) := fun b =>
    (hFi b).trans ((congrArg (WittVector.map ψ) (hom_eq_id_apply s En.inl hs1 b).symm).trans (hF'a _).symm)
  have hE := (mapE_facts bk O ψ hx0 hxu hxc).1
  have hH := (mapE_facts bk O ψ hx0 hxu hxc).2
  have hnzd : F (En.inl.f (bk.ev bk.E)) ∈ nonZeroDivisors (WittVector l O) := by
    rw [hFi]; exact hE
  have hI : (ainfObj K).I = Ideal.span {bk.ev bk.E} := bk.span_ev.symm
  have hhaus : IsHausdorff ((Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I).map (F.comp En.inl.f))
      (WittVector l O) :=
    isHausdorff_map_congr (congrArg (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ ·) hI) hFinl hH
  have hFF : F = F' :=
    _root_.GlobalTheory.BSP.envExt_agree l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) En (WittVector l O) WittVector.frobenius F F'
      htfW hFφ hF'φ hinl (hinr.trans (hF'a _).symm) hnzd hhaus
  rw [hFF, hF'a]

theorem envPoint_factors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 →
    ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O →
    ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧
      s.comp En.inr = (ainfHom K g).comp bk.ι ∧
      ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  intro l _ K bk En O _ _ _ _ _ f hx0 hxu hxc
  have hcc : Function.Surjective (WittVector.constantCoeff (p := l) (R := OCb l)) := fun y =>
    ⟨WittVector.teichmuller l y, by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  let f0 : WittVector l (OCb l) →+* O := f.comp En.inl.f
  have hker : RingHom.ker (WittVector.constantCoeff (p := l) (R := OCb l)) ≤ RingHom.ker f0 := by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      map_natCast, CharP.cast_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : OCb l →+* O, ∀ a : WittVector l (OCb l), f (En.inl.f a) = ψ (a.coeff 0) :=
    ⟨RingHom.liftOfSurjective _ hcc ⟨f0, hker⟩, fun a =>
      (RingHom.liftOfSurjective_comp_apply _ hcc ⟨f0, hker⟩ a).symm⟩
  have hflat : f (En.inl.f (bk.ev X)) = ψ bk.flat := by
    rw [hψ, bk.ev_X, WittVector.teichmuller_coeff_zero]
  rw [hflat] at hx0 hxu hxc
  obtain ⟨htf, -, -⟩ := _root_.GlobalTheory.BSP.env_ainf_mod l K bk En
  obtain ⟨F, hF0, hFφ⟩ := _root_.GlobalTheory.DworkLift.exists_frobenius_compatible_lift l En.Q.A En.Q.D.φ
    (fun a => ⟨En.Q.D.δ a, by rw [En.Q.D.φ_eq]; ring⟩) htf O f
  have hFinl : F.comp En.inl.f = WittVector.map ψ :=
    _root_.GlobalTheory.WittMapUniq.eq_map_of_coeff_zero l (OCb l) O (F.comp En.inl.f) ψ (fun a => (hF0 (En.inl.f a)).trans (hψ a))
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b

  have hφX : En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr X ^ l :=
    calc En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr (frobS l bk.a X) := (Hom.f_φ En.inr X).symm
      _ = BK.hf En.inr (X ^ l) := by rw [frobS_X]
      _ = _ := map_pow _ _ _
  set v := F (BK.hf En.inr X) with hvdef
  have hv : WittVector.frobenius v = v ^ l := by
    rw [hvdef, ← hFφ, hφX, map_pow]
  have hvt := _root_.GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow l O v hv
  have e1 : F (En.inl.f (bk.ev X)) = WittVector.teichmuller l (ψ bk.flat) := by
    rw [hFi, bk.ev_X, WittVector.map_teichmuller]
  have e2 : F (En.inl.f (bk.ev bk.E)) = WittVector.map ψ (bk.ev bk.E) := hFi _
  have h1 : v = F (En.inl.f (bk.ev X)) + F (En.inl.f (bk.ev bk.E)) * F En.w := by
    have := congrArg F En.w_eq
    rwa [map_add, map_mul] at this
  rw [e1, e2] at h1
  have hdvd : WittVector.map ψ (bk.ev bk.E) ∣
      WittVector.teichmuller l (v.coeff 0) - WittVector.teichmuller l (ψ bk.flat) :=
    ⟨F En.w, by rw [← hvt]; linear_combination h1⟩
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.BSP.exists_gal_of_teichmuller_congr l K bk O ψ hx0 hxu hxc (v.coeff 0) hdvd
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := En.univ (ainfObj K) (Hom.id _) ((ainfHom K g).comp bk.ι)

  have hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X)) := by
    have h2 : s.f (BK.hf En.inr X) = Per.σA (g : GQ l) (bk.ev X) :=
      hom_eq_comp_apply s En.inr _ _ hs2 X
    have h3 : WittVector.map ψ (Per.σA (g : GQ l) (bk.ev X)) =
        WittVector.teichmuller l (ψ (Per.σF (g : GQ l) bk.flat)) := by
      rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, WittVector.map_teichmuller]
    refine Eq.trans ?_ ((congrArg (WittVector.map ψ) h2).trans h3).symm
    exact hvdef.symm.trans (hvt.trans (congrArg (WittVector.teichmuller l) hg))
  refine ⟨g, s, ψ, hs1, hs2, fun a => ?_⟩
  rw [← hF0, envPoint_eq bk En O ψ hx0 hxu hxc F hFφ hFinl s hs1 hinr a]
  exact WittVector.map_coeff ψ (s.f a) 0

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisor
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_nonZeroDivisors_of_invertible_eq_span {A : Type} [CommRing A] {I : Ideal A} {t : A}
    (hI : Module.Invertible A ↥I) (h : I = Ideal.span {t}) : t ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply (Module.Invertible.toModuleEnd_bijective A ↥I).1
  rw [map_zero]
  ext ⟨y, hy⟩
  rw [h] at hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  change x * (z * t) = 0
  linear_combination z * hx

theorem hf_E_span_and_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (g : Hom bk.prism B), B.I = Ideal.span {BK.hf g bk.E} ∧ BK.hf g bk.E ∈ nonZeroDivisors B.A := by
  intro l _ K bk B g
  have h : B.I = Ideal.span {BK.hf g bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ _ _ g]
    change Ideal.map (BK.hf g) (Ideal.span {bk.E}) = _
    rw [Ideal.map_span, Set.image_singleton]
  exact ⟨h, mem_nonZeroDivisors_of_invertible_eq_span B.inv h⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemDeltaCommuteLocusSubringOfIsHausdorffStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.C_mem_deltaCommuteLocusSubring_of_isHausdorff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ σ : (Wq l a)⟦X⟧ →+* C, ∀ w : Wq l a, PowerSeries.C w ∈ δLocus (deltaS l a) DC σ := by
  first | exact @GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | exact GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | (intros; apply GlobalTheory.BSP.C_mem_δLocus_of_hausdorff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementOfCharactersUniqueUpToConjStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complement_of_characters_unique_up_to_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  first | exact @GlobalTheory.CharCancel.main | exact GlobalTheory.CharCancel.main | (intros; apply GlobalTheory.CharCancel.main <;> assumption)
end

