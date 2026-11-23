module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionCompactSupportModuloUnipotent

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlane
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HypSplit

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_eq_dot (u v : Fin M → E) :
    hE σ J u v = Matrix.vecMul (fun i => σ (u i)) J ⬝ᵥ v := by
  simp only [hE, hform, Matrix.vecMul, dotProduct, Finset.sum_mul, RingHom.coe_coe]
  exact Finset.sum_comm

def hLin (u : Fin M → E) : (Fin M → E) →ₗ[E] E where
  toFun := hE σ J u
  map_add' v w := by simp only [hE_eq_dot, dotProduct_add]
  map_smul' a v := by simp only [hE_eq_dot, dotProduct_smul, RingHom.id_apply]

@[simp] theorem hLin_apply (u v : Fin M → E) : hLin σ J u v = hE σ J u v := rfl

variable {σ J}

theorem hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin M → E) :
    σ (hE σ J u v) = hE σ J v u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem exists_partner (hσ : ∀ a, σ (σ a) = a) (hJ : IsHermND σ J) (h2 : (2 : E) ≠ 0)
    (x : Fin M → E) (hx : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ y, hE σ J x y = 1 ∧ hE σ J y y = 0 := by
  have hr : Matrix.vecMul (fun i => σ (x i)) J ≠ 0 := by
    intro h0
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hJ.2 h0
    apply hx
    funext i
    have h3 := congrFun h1 i
    simpa using h3
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hr
  have hj' : Matrix.vecMul (fun i => σ (x i)) J j ≠ 0 := hj
  obtain ⟨y₀, h1⟩ : ∃ y₀, hE σ J x y₀ = 1 := by
    refine ⟨Pi.single j (Matrix.vecMul (fun i => σ (x i)) J j)⁻¹, ?_⟩
    rw [hE_eq_dot, dotProduct_single, mul_inv_cancel₀ hj']
  have conj := hE_conj (J := J) hσ hJ.1
  have h1' : hE σ J y₀ x = 1 := by rw [← conj, h1, map_one]
  have hc : σ (hE σ J y₀ y₀) = hE σ J y₀ y₀ := conj _ _
  set c := hE σ J y₀ y₀ with hcdef
  have hc2 : σ (c / 2) = c / 2 := by rw [map_div₀, hc, map_ofNat]
  have hxy : hE σ J x (y₀ - (c / 2) • x) = 1 := by
    have := (hLin σ J x).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, hxx, h1] at this
    simpa using this
  have hy₀y : hE σ J y₀ (y₀ - (c / 2) • x) = c / 2 := by
    have := (hLin σ J y₀).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, h1', ← hcdef] at this
    rw [this]; field_simp; ring
  refine ⟨y₀ - (c / 2) • x, hxy, ?_⟩
  have := (hLin σ J (y₀ - (c / 2) • x)).map_sub y₀ ((c / 2) • x)
  simp only [map_smul, hLin_apply, smul_eq_mul] at this
  rw [this, ← conj y₀, hy₀y, hc2, ← conj x, hxy, map_one]
  ring

theorem finrank_perp (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    {x y : Fin M → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0) (hxy : hE σ J x y = 1) :
    Module.finrank E (LinearMap.ker ((hLin σ J x).prod (hLin σ J y))) + 2 = M := by
  have hyx : hE σ J y x = 1 := by rw [← hE_conj hσ hJ, hxy, map_one]
  have hs : Function.Surjective ((hLin σ J x).prod (hLin σ J y)) := by
    rintro ⟨a, b⟩
    refine ⟨a • y + b • x, Prod.ext ?_ ?_⟩
    · change hLin σ J x (a • y + b • x) = a
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hxy, hxx, mul_one, mul_zero, add_zero]
    · change hLin σ J y (a • y + b • x) = b
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hyy, hyx, mul_one, mul_zero, zero_add]
  have h := LinearMap.finrank_range_add_finrank_ker ((hLin σ J x).prod (hLin σ J y))
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega

theorem gram_eq {n : ℕ} (c : Fin n → Fin M → E) :
    cT (σ : E →+* E) (Matrix.of c)ᵀ * J * (Matrix.of c)ᵀ = gramE σ J c := by
  ext a b
  simp only [Matrix.mul_apply, cT, gramE, hE, hform, Finset.sum_mul, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_comm

theorem det_ne_zero_of_hypJ {M₁ : ℕ} (A : Matrix (Fin M₁) (Fin M₁) E) (h : (hypJ A).det ≠ 0) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply h
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Fin.cons 0 (Fin.cons 0 v), ?_, ?_⟩
  · intro h1
    apply hv
    funext i
    simpa using congrFun h1 i.succ.succ
  · funext a
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · have := congrFun hAv a
      simpa [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ] using this

theorem selfDualLattice_projection_mem_of_unit_length (hσ : ∀ a, σ (σ a) = a) (h2 : (2 : E) ≠ 0) {M₁ : ℕ}
    {J : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E} (hJ : IsHermND σ J)
    {x y : Fin (M₁ + 2) → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0)
    (hxy : hE σ J x y = 1) :
    ∃ (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧
      hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * J *
        (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  have conj := hE_conj (J := J) hσ hJ.1
  have hyx : hE σ J y x = 1 := by rw [← conj, hxy, map_one]
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  set W := LinearMap.ker ((hLin σ J x).prod (hLin σ J y)) with hW
  have hfr' : Module.finrank E W = M₁ := by omega
  let b : Module.Basis (Fin M₁) E W := Module.finBasisOfFinrankEq E W hfr'
  have hbx : ∀ i, hE σ J x (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.fst h3
  have hby : ∀ i, hE σ J y (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.snd h3
  have hbx' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) x = 0 := fun i => by
    rw [← conj, hbx, map_zero]
  have hby' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) y = 0 := fun i => by
    rw [← conj, hby, map_zero]
  let c : Fin (M₁ + 2) → Fin (M₁ + 2) → E :=
    Fin.cons x (Fin.cons y fun i => (b i : Fin (M₁ + 2) → E))
  have hli : LinearIndependent E c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at ha
    simp only [c, Fin.cons_zero, Fin.cons_succ] at ha
    have e1 := congrArg (hLin σ J x) ha
    have e2 := congrArg (hLin σ J y) ha
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_sum, hLin_apply, smul_eq_mul, hxx, hyy, hxy, hyx, hbx, hby,
      map_zero, mul_zero, zero_add, add_zero, mul_one, Finset.sum_const_zero] at e1 e2
    rw [e1, e2] at ha
    simp only [zero_smul, zero_add] at ha
    have e3 : ∑ i, a i.succ.succ • b i = 0 := by
      apply Subtype.ext
      simpa using ha
    have e4 := Fintype.linearIndependent_iff.mp b.linearIndependent _ e3
    intro i
    refine Fin.cases e2 (fun i => Fin.cases e1 e4 i) i
  have hunit : IsUnit (Matrix.of c)ᵀ := by
    exact (Matrix.linearIndependent_cols_iff_isUnit (A := (Matrix.of c)ᵀ)).mp hli
  let J₁ : Matrix (Fin M₁) (Fin M₁) E := gramE σ J fun i => (b i : Fin (M₁ + 2) → E)
  have hgram : hypJ J₁ = gramE σ J c := by
    ext a b'
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;>
      refine Fin.cases ?_ (fun b' => Fin.cases ?_ (fun b' => ?_) b') b' <;>
      simp [hypJ, gramE, c, J₁, hxx, hyy, hxy, hyx, hbx, hby, hbx', hby']
  have hdet : (hypJ J₁).det ≠ 0 := by
    rw [hgram, ← gram_eq, Matrix.det_mul, Matrix.det_mul]
    have hu : (Matrix.of c)ᵀ.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
    have hcT : (cT (σ : E →+* E) (Matrix.of c)ᵀ).det ≠ 0 := by
      rw [cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simpa using hu
    exact mul_ne_zero (mul_ne_zero hcT hJ.2) hu
  refine ⟨hunit.unit, J₁, ⟨fun i j => conj _ _, det_ne_zero_of_hypJ J₁ hdet⟩, ?_⟩
  rw [hgram, ← gram_eq]
  rfl

end Alg

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem splitHyp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  intro F E _ _ _ _ _ σ hcm M J hJ x hx hxx
  have hσ := sigma_invol σ hcm
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨y, hxy, hyy⟩ := exists_partner hσ hJ h2 x hx hxx
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 2 := ⟨_, hfr.symm⟩
  obtain ⟨g, J₁, h1, h3⟩ := selfDualLattice_projection_mem_of_unit_length hσ h2 hJ hxx hyy hxy
  exact ⟨M₁, rfl, g, J₁, h1, h3⟩

end GlobalTheory.CompanionTheory.SW.HypSplit
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableCoordinateMapsTensor
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW

theorem map_curry_pi_pi {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam] (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
      (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) =
      Measure.pi fun _ : Fin M × Fin d => lam := by
  have hm : Measurable (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) := by
    fun_prop
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : Fin M => Set.univ.pi fun k : Fin d => s (i, k) := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem coordW_one_map_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (M : ℕ) (lam : Measure R), lam.IsAddHaarMeasure → (Measurable fun (X : Fin 1 → Fin M → R ⊗[F] E) (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) ∧ (coordW R b lam 1 M).map (fun X (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) = Measure.pi fun _ => lam := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b M lam hlam
  obtain ⟨-, -, -, -, -, -, hom, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hh := hom d b
  let e : (R ⊗[F] E) ≃ᵐ (Fin d → R) := (hh.homeomorph _).toMeasurableEquiv
  have hce : (⇑e : (R ⊗[F] E) → Fin d → R) =
      fun y k => (Algebra.TensorProduct.basis R b).repr y k := rfl
  have hK : (coordK R b lam).map e = Measure.pi fun _ => lam := by
    have h := e.measurableEmbedding.map_comap (Measure.pi fun _ : Fin d => lam)
    rw [e.surjective.range_eq, Measure.restrict_univ] at h
    rw [coordK, ← hce]
    exact h
  have hK' : coordK R b lam = (Measure.pi fun _ : Fin d => lam).map e.symm := by
    rw [← hK, Measure.map_map e.symm.measurable e.measurable]
    simp
  have : SigmaFinite (coordK R b lam) := by
    rw [hK']; exact e.symm.sigmaFinite_map
  have hmpK : MeasurePreserving e (coordK R b lam) (Measure.pi fun _ : Fin d => lam) :=
    ⟨e.measurable, hK⟩
  have h1 : MeasurePreserving (fun (X : Fin 1 → Fin M → R ⊗[F] E) => X default)
      (coordW R b lam 1 M) (Measure.pi fun _ : Fin M => coordK R b lam) :=
    measurePreserving_funUnique (Measure.pi fun _ : Fin M => coordK R b lam) (Fin 1)
  have h2 : MeasurePreserving (fun (Y : Fin M → R ⊗[F] E) (i : Fin M) => e (Y i))
      (Measure.pi fun _ : Fin M => coordK R b lam)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam) :=
    measurePreserving_pi _ _ fun _ => hmpK
  have h3 : MeasurePreserving (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam)
      (Measure.pi fun _ : Fin M × Fin d => lam) :=
    ⟨by fun_prop, map_curry_pi_pi lam M d⟩
  have h := h3.comp (h2.comp h1)
  exact ⟨h.measurable, h.map_eq⟩

end GlobalTheory.CompanionTheory.SW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PoissonSummationGaussianStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory.CompanionTheory.SW.Core.PoiLat in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_gaussian :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ),
    Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ,
    let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ))));
    let fh : (κ → ℝ) → ℂ := fun y =>
      ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ));
    Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧
      Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧
      (∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ))) = ((|g.det|⁻¹ : ℝ) : ℂ) *
        ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  intro κ _ _ Z hs hp g hg a f fh
  have hZ : GlobalTheory.IsSiegel Z := ⟨hs, hp⟩
  have hσ := hZ.transpose_mul_mul hg
  have hf : ∀ n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) =
      GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
        ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n :=
    fun n => gaussian_lattice_term Z hg a n
  have hfh : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) =
      GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 0
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
    intro n
    rw [← fourier_lattice_term hZ hg n]
    exact gaussian_fourier hZ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hf]
    exact hσ.summable_norm_riemannThetaTerm _ _ _
  · simp only [hfh, norm_mul]
    exact (hσ.neg_inv.summable_norm_riemannThetaTerm _ _ _).mul_left _
  · have hterm : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) =
      GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 (-(g⁻¹ *ᵥ a))
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
      intro n
      rw [hfh, phase_lattice, mul_assoc]
      congr 1
      rw [GlobalTheory.riemannThetaTerm_zero_zero, GlobalTheory.riemannThetaTerm_def,
        ← Complex.exp_add]
      congr 1
      simp [dotProduct]
      ring
    simp only [hf, hterm]
    rw [tsum_mul_left, ← mul_assoc, ← siegelGaussIntegral_congr Z hg]
    have h0 := hσ.riemannTheta_eq_neg_inv (g⁻¹ *ᵥ a) 0
    have h1 := GlobalTheory.riemannTheta_neg 0 (g⁻¹ *ᵥ a)
      (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0
    simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h0 h1
    rw [h1] at h0
    exact h0
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticLevelSetDensity
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Dens

def qMap {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (x : InfinitePlace F → ι → ℝ) : InfinitePlace F → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))

def gW {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (P : InfinitePlace F → Matrix ι ι ℝ) (x : InfinitePlace F → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))

section
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_qMap (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Continuous (qMap B ρ) := by
  refine continuous_pi fun w => ?_
  exact continuous_const.mul (Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w)))

theorem continuous_gW (P : InfinitePlace F → Matrix ι ι ℝ) : Continuous (gW P) := by
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
  exact Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w))

theorem gauss_I (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (x : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun _ => Complex.I) x = (gW P x : ℂ) := by
  simp only [gauss, gW, Complex.I_re, Complex.I_im]
  push_cast
  congr 1
  simp [Finset.mul_sum]

theorem gauss_shift (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (t : InfinitePlace F → ℝ) (v : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => (t w : ℂ) + Complex.I) v =
      (gW P v : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w, qMap B ρ v w * t w : ℝ) : ℂ)) := by
  simp only [gauss, gW, qMap]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, add_zero, zero_add, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring

theorem one_dim_integrable (M : ℕ) (hM : 3 ≤ M) :
    Integrable (fun t : ℝ => (‖(t : ℂ) + Complex.I‖ ^ M)⁻¹) := by
  refine integrable_inv_one_add_sq.mono' (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  have h2 : ‖(t : ℂ) + Complex.I‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h1 : 1 ≤ ‖(t : ℂ) + Complex.I‖ := by
    have : (1 : ℝ) ^ 2 ≤ ‖(t : ℂ) + Complex.I‖ ^ 2 := by rw [h2]; nlinarith [sq_nonneg t]
    exact (pow_le_pow_iff_left₀ zero_le_one (norm_nonneg _) two_ne_zero).1 this
  rw [Real.norm_of_nonneg (by positivity), ← h2]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))

theorem prod_integrable (M : ℕ) (hM : 3 ≤ M) :
    Integrable (fun x : InfinitePlace F → ℝ => (∏ w, ‖(x w : ℂ) + Complex.I‖ ^ M)⁻¹) := by
  have := Integrable.fintype_prod (μ := fun _ => (volume : Measure ℝ))
    (f := fun (_ : InfinitePlace F) (t : ℝ) => (‖(t : ℂ) + Complex.I‖ ^ M)⁻¹)
    (fun _ => one_dim_integrable M hM)
  simpa [Finset.prod_inv_distrib, volume_pi] using this

theorem density_of_q : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∃ Di : (InfinitePlace F → ℝ) → ℝ, Continuous Di ∧ (∀ y, 0 ≤ Di y) ∧ (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Di y)) ∧ Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) ∧ ∀ z : InfinitePlace F → ℝ, ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) = ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di z : ℝ) : ℂ) := by
  intro F _ _ ι _ _ M B ρ P h hM
  classical
  have hdet : B.det ≠ 0 := h.2.2.2.1
  set S : ℝ := Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| with hS
  have hSpos : 0 < S := by
    refine Real.sqrt_pos.2 (abs_pos.2 ?_)
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hdet)
  have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'

  have hgi : Integrable (gW P) := by
    have h0 := (_root_.GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier F ι M B ρ P h (fun _ => Complex.I) (fun _ => by simp)).1
    have h1 := h0.re
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [gauss_I]
  have hgn : ∀ x, 0 ≤ gW P x := fun x => (Real.exp_pos _).le
  have hdm : Measurable fun x => ENNReal.ofReal (gW P x) :=
    ENNReal.measurable_ofReal.comp (continuous_gW P).measurable
  let ν : Measure (InfinitePlace F → ι → ℝ) := volume.withDensity fun x => ENNReal.ofReal (gW P x)
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hgi.2
  have hQ : Continuous (qMap B ρ) := continuous_qMap B ρ
  let m : Measure (InfinitePlace F → ℝ) := ν.map (qMap B ρ)
  haveI : IsFiniteMeasure m := Measure.isFiniteMeasure_map ν _

  have hχ : ∀ t : InfinitePlace F → ℝ,
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m =
        ∫ v, gauss B ρ P (fun w => (t w : ℂ) + Complex.I) v := by
    intro t
    have hc : Continuous fun z : InfinitePlace F → ℝ =>
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) := by fun_prop
    rw [integral_map hQ.aemeasurable hc.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hdm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [ENNReal.toReal_ofReal (hgn v), Complex.real_smul]
    exact (gauss_shift B ρ P t v).symm
  have hcG : ∀ t : InfinitePlace F → ℝ, cG B ρ P (fun w => (t w : ℂ) + Complex.I) =
      (S : ℂ) * ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    intro t
    rw [hχ t]
    rfl

  have hcont : Continuous fun t : InfinitePlace F → ℝ =>
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    refine continuous_of_dominated (bound := fun _ => 1) (fun t => ?_) (fun t => ?_)
      (integrable_const _) (Filter.Eventually.of_forall fun z => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Filter.Eventually.of_forall fun z => ?_
      have : (2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ) =
          ((2 * Real.pi * ∑ w, z w * t w : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcGi : Integrable fun t : InfinitePlace F → ℝ =>
      cG B ρ P (fun w => (t w : ℂ) + Complex.I) := by
    have hcc : Continuous fun t : InfinitePlace F → ℝ =>
        cG B ρ P (fun w => (t w : ℂ) + Complex.I) := by
      simp only [hcG]
      exact continuous_const.mul hcont
    refine (prod_integrable (F := F) M hM).mono' hcc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have him : ∀ w, 0 < ((t w : ℂ) + Complex.I).im := fun w => by simp
    exact ((_root_.GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier F ι M B ρ P h _ him).2.1).le
  have hχi : Integrable fun t : InfinitePlace F → ℝ =>
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    refine (hcGi.const_mul ((S : ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hcG]
    rw [inv_mul_cancel_left₀ hSc]
  obtain ⟨D, hDc, hD0, hDf, hDm⟩ := _root_.GlobalTheory.CompanionTheory.SW.CharDensity.density_of_integrable_charFun (InfinitePlace F) m inferInstance hχi
  refine ⟨D, hDc, hD0, fun U hU => ?_, hcGi, fun z => ?_⟩
  · rw [← hDm U hU, Measure.map_apply hQ.measurable hU, withDensity_apply _ (hQ.measurable hU)]
    rfl
  · have hmul : ∀ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) =
        (S : ℂ) * ((∫ u, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ w, u w * x w : ℝ) : ℂ)) ∂m) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ))) := by
      intro x
      rw [hcG x, mul_assoc]
    simp only [hmul]
    rw [integral_const_mul, ← hDf z, Complex.ofReal_mul]

end

end GlobalTheory.CompanionTheory.SW.Core.Dens
end
end

