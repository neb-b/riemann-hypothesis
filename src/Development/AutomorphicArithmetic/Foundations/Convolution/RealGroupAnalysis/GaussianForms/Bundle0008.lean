module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousQuaternaryFormLeft
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

noncomputable section

private theorem continuous_form {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a c b d e : R) :
    Continuous fun y : Fin 4 → R => 2 * (y 2 * a - c * (y 3 * b)) - y 1 * d - y 0 * e := by
  fun_prop

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_psi : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp (continuous_adelicChar (K := F))

private theorem norm_psi (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

private theorem continuous_quaternaryForm_left (δ : F) (v : V4 F) : Continuous fun y : V4 F => B4 δ y v := by
  exact continuous_form (v 2) (rt δ) (v 3) (v 0) (v 1)

private theorem integrable_ft (δ : F) {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    Integrable (fun y => φ y * ψ (B4 δ y v)) (adeleMeasurePi F) := by
  refine (integrable_of_mem_schwartzBruhatPi hφ).mul_bdd (c := 1) ?_ ?_
  · exact (continuous_psi.comp (continuous_quaternaryForm_left δ v)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => (norm_psi _).le

private theorem quaternaryFourier_add (δ : F) {φ φ' : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (hφ' : φ' ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    ft4 δ (φ + φ') v = ft4 δ φ v + ft4 δ φ' v := by
  unfold ft4
  rw [← integral_add (integrable_ft δ hφ v) (integrable_ft δ hφ' v)]
  congr 1
  funext y
  simp [add_mul]

private theorem quaternaryFourier_smul (δ : F) (c : ℂ) (φ : V4 F → ℂ) (v : V4 F) :
    ft4 δ (c • φ) v = c * ft4 δ φ v := by
  unfold ft4
  rw [← integral_const_mul]
  congr 1
  funext y
  simp [mul_assoc]

private def opN (δ : F) (b : A F) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ψ (b * q4 δ v) * φ.1 v, by
    have h := chirpQ F δ b 0 φ.1 φ.2
    have e : (fun v => ψ (b * q4 δ v + B4 δ v 0) * φ.1 v) = fun v => ψ (b * q4 δ v) * φ.1 v := by
      funext v
      simp [B4]
    rwa [e] at h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def scal (a : (A F)ˣ) : GL (Fin 4) (A F) :=
  ⟨(a : A F) • 1, ((a⁻¹ : (A F)ˣ) : A F) • 1, by simp [smul_smul], by simp [smul_smul]⟩

private def opM (η : (A F)ˣ →* ℂˣ) (a : (A F)ˣ) : Module.End ℂ (S4 F) where
  toFun φ := ⟨fun v => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i, by
    have h := D.sClos F (Fin 4) (scal a) φ.1 φ.2
    have e : (fun v => φ.1 ((scal a).val *ᵥ v)) = fun v => φ.1 fun i => (a : A F) * v i := by
      funext v
      have e' : (scal a).val *ᵥ v = fun i => (a : A F) * v i := by
        funext i
        simp [scal, Matrix.smul_mulVec]
      rw [e']
    rw [e] at h
    exact Submodule.smul_mem _ (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) h⟩
  map_add' φ φ' := by
    ext v
    simp [mul_add]
  map_smul' c φ := by
    ext v
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

private def opW (δ : F) (hδ : δ ≠ 0) : Module.End ℂ (S4 F) where
  toFun φ := ⟨ft4 δ φ.1, (ftBasic F δ hδ φ.1 φ.2).1⟩
  map_add' φ φ' := by
    ext v
    exact quaternaryFourier_add δ φ.2 φ'.2 v
  map_smul' c φ := by
    ext v
    exact quaternaryFourier_smul δ c φ.1 v

end UpperTheory.ConvolutionTheory.R2.C

end

theorem UpperTheory.ConvolutionTheory.R2.C.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ), δ ≠ 0 → Nonempty (Ops δ η) := by
  intro F _ _ δ η hδ
  exact ⟨{ N := opN δ, M := opM η, W := opW δ hδ
           N_apply := fun _ _ _ => rfl
           M_apply := fun _ _ _ => rfl
           W_apply := fun _ _ => rfl }⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GrpLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem dv_mul {F : Type} [Field F] [NumberField F] {m n : F} {x y : A F}
    (hx : Dv m x) (hy : Dv n y) : Dv (m * n) (x * y) := fun v => by
  have h : Valued.v ((x * y).2 v) = Valued.v (x.2 v) * Valued.v (y.2 v) := by
    change Valued.v (x.2 v * y.2 v) = _
    exact map_mul _ _ _
  rw [h, map_mul]
  exact mul_le_mul' (hx v) (hy v)

private theorem dv_add {F : Type} [Field F] [NumberField F] {m : F} {x y : A F}
    (hx : Dv m x) (hy : Dv m y) : Dv m (x + y) := fun v => by
  change Valued.v (x.2 v + y.2 v) ≤ _
  exact Valuation.map_add_le _ (hx v) (hy v)

private theorem dv_neg {F : Type} [Field F] [NumberField F] {m : F} {x : A F}
    (hx : Dv m x) : Dv m (-x) := fun v => by
  change Valued.v (-(x.2 v)) ≤ _
  rw [Valuation.map_neg]
  exact hx v

private theorem dv_zero {F : Type} [Field F] [NumberField F] (m : F) : Dv m (0 : A F) := fun v => by
  change Valued.v (0 : v.adicCompletion F) ≤ _
  rw [map_zero]
  exact zero_le'

private theorem dv_one {F : Type} [Field F] [NumberField F] : Dv 1 (1 : A F) := fun v => by
  change Valued.v (1 : v.adicCompletion F) ≤ _
  rw [map_one, map_one]

private theorem val_le_one {F : Type} [Field F] [NumberField F] {m : F} (hm : Dv 1 (rt m))
    (v : HeightOneSpectrum (𝓞 F)) : v.valuation F m ≤ 1 := by
  have h := hm v
  rw [map_one] at h
  have h2 : Valued.v ((rt m : A F).2 v) = v.valuation F m :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m
  rwa [h2] at h

private theorem dv_weaken {F : Type} [Field F] [NumberField F] {m n : F} {x : A F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F m ≤ v.valuation F n) (hx : Dv m x) : Dv n x :=
  fun v => (hx v).trans (h v)

private theorem unit_alt {F : Type} [Field F] [NumberField F] (g : G1 F)
    (h00 : Dv 1 (g 0 0)) (h01 : Dv 1 (g 0 1)) (h10 : Dv 1 (g 1 0)) (h11 : Dv 1 (g 1 1))
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((g 1 0).2 v) = 1 ∨ Valued.v ((g 1 1).2 v) = 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc, hd⟩ := hcon
  have le1 : ∀ {x : A F}, Dv 1 x → Valued.v (x.2 v) ≤ 1 := fun {x} hx => by
    have := hx v
    rwa [map_one] at this
  have hc' := lt_of_le_of_ne (le1 h10) hc
  have hd' := lt_of_le_of_ne (le1 h11) hd
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have hloc : (g 0 0).2 v * (g 1 1).2 v - (g 0 1).2 v * (g 1 0).2 v = 1 := by
    have := congrArg (fun x : A F => x.2 v) hdet
    exact this
  have h1 : Valued.v ((g 0 0).2 v * (g 1 1).2 v) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (le1 h00)) hd'
  have h2 : Valued.v ((g 0 1).2 v * (g 1 0).2 v) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (le1 h01)) hc'
  have h3 := Valuation.map_sub_lt _ h1 h2
  rw [hloc, map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.ConvolutionTheory.R2.C.grpLevel :
    ∀ (F : Type) [Field F] [NumberField F] (H : Subgroup (G1 F)), (∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H) → ∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → g ∈ H := by
  intro F _ _ H hH
  obtain ⟨hb1, hb2⟩ := nbBasis F
  obtain ⟨m, hm0, hm1, hmU⟩ := hb1 _ hH
  have hm := val_le_one hm1
  have hsq : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (m ^ 2) ≤ v.valuation F m := fun v => by
    rw [map_pow, pow_two]
    exact mul_le_of_le_one_left' (hm v)
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F m ≤ v.valuation F 1 := fun v => by
    rw [map_one]
    exact hm v
  let R : Subring (A F) :=
    { carrier := {x | Dv 1 x}
      mul_mem' := fun {a b} ha hb => by
        have h := dv_mul ha hb
        rwa [one_mul] at h
      one_mem' := dv_one
      add_mem' := fun ha hb => dv_add ha hb
      zero_mem' := dv_zero 1
      neg_mem' := fun ha => dv_neg ha }
  let I : AddSubgroup (A F) :=
    { carrier := {x | x.1 = 0 ∧ Dv m x}
      add_mem' := fun {a b} ha hb => ⟨by
        change a.1 + b.1 = 0
        rw [ha.1, hb.1, add_zero], dv_add ha.2 hb.2⟩
      zero_mem' := ⟨rfl, dv_zero m⟩
      neg_mem' := fun {a} ha => ⟨by
        change -a.1 = 0
        rw [ha.1, neg_zero], dv_neg ha.2⟩ }
  have hRI : ∀ r ∈ R, ∀ x ∈ I, r * x ∈ I := fun r hr x hx => ⟨by
    change r.1 * x.1 = 0
    rw [hx.1, mul_zero], by
    have h := dv_mul hr hx.2
    rwa [one_mul] at h⟩
  have hI : ∀ b ∈ I, nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H := fun b hb => hmU b hb.1 hb.2 hb.1
  have hev : ∀ i j, ∀ᶠ g in 𝓝 (1 : G1 F), Dv (m ^ 2) (g i j - (1 : Matrix (Fin 2) (Fin 2) (A F)) i j) := by
    intro i j
    have hc : Continuous fun g : G1 F => g i j - (1 : Matrix (Fin 2) (Fin 2) (A F)) i j :=
      (continuous_subtype_val.matrix_elem i j).sub continuous_const
    have ht : Tendsto (fun g : G1 F => g i j - (1 : Matrix (Fin 2) (Fin 2) (A F)) i j) (𝓝 1) (𝓝 0) := by
      have h := hc.tendsto 1
      simpa using h
    exact ht.eventually (hb2 _ (pow_ne_zero 2 hm0))
  filter_upwards [hev 0 0, hev 0 1, hev 1 0, hev 1 1] with g h00 h01 h10 h11 hinf
  have e00 : g 0 0 - 1 = g 0 0 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := by simp
  have e01 : g 0 1 = g 0 1 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 0 1 := by simp
  have e10 : g 1 0 = g 1 0 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 1 0 := by simp
  have e11 : g 1 1 - 1 = g 1 1 - (1 : Matrix (Fin 2) (Fin 2) (A F)) 1 1 := by simp
  rw [← e00] at h00
  rw [← e01] at h01
  rw [← e10] at h10
  rw [← e11] at h11
  have toOne : ∀ {x : A F}, Dv (m ^ 2) x → Dv 1 x := fun hx =>
    dv_weaken hone (dv_weaken hsq hx)
  have d00 : Dv 1 (g 0 0) := by
    have h := dv_add (toOne h00) dv_one
    rwa [sub_add_cancel] at h
  have d11 : Dv 1 (g 1 1) := by
    have h := dv_add (toOne h11) dv_one
    rwa [sub_add_cancel] at h
  have c0 : (g 1 0).1 = 0 := by simpa using hinf 1 0
  have c1 : (g 0 1).1 = 0 := by simpa using hinf 0 1
  have d1 : (g 1 1).1 = 1 := by
    have h : (g 1 1).1 = (1 : A F).1 := by simpa using hinf 1 1
    exact h
  obtain ⟨u, ε, x, y, hu, hui, hε, hx, hy, e1, e2⟩ :=
    lvEps F m hm0 hm1 (g 1 0) (g 1 1) c0 d1 (toOne h10) h11
      (unit_alt g d00 (toOne h01) (toOne h10) d11)
  exact lvAlg F H R I hRI hI g u d00 ⟨c1, dv_weaken hsq h01⟩ ⟨c0, dv_weaken hsq h10⟩ hu hui
    ε hε x hx y hy e1 e2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormShiftExpand
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_add' {F : Type} [Field F] [NumberField F] (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private lemma psi_neg_mul {F : Type} [Field F] [NumberField F] (a : A F) : ψ (-a) * ψ a = 1 := by
  rw [← psi_add', neg_add_cancel]
  simp [ψ]

private lemma quadraticForm_shift_expand {F : Type} [Field F] [NumberField F] (δ : F) (b c : A F) (hbc : b * c = 1) (x y v : V4 F) :
    b * q4 δ (x + (y + fun i => c * v i)) = b * q4 δ (x + y) + B4 δ x v + B4 δ y v + c * q4 δ v := by
  simp only [q4, B4, Pi.add_apply]
  linear_combination (2 * ((x 2 + y 2) * v 2 - rt δ * ((x 3 + y 3) * v 3)) - (x 1 + y 1) * v 0 - (x 0 + y 0) * v 1
    + c * (v 2 ^ 2 - rt δ * v 3 ^ 2 - v 1 * v 0)) * hbc

private lemma quaternaryForm_neg_right {F : Type} [Field F] [NumberField F] (δ : F) (x v : V4 F) : B4 δ x (-v) = -B4 δ x v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.idxFt :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    ft4 δ (Pc δ (b : A F) φ.1) v = c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ft4 δ φ.1 (-v) := by
  intro F _ _ δ b c h φ v
  have hbc : (b : A F) * ((b⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv b
  let φ' : S4 F := ⟨fun x => ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x, chirpQ F δ 0 (-v) φ.1 φ.2⟩
  have hφ' : ∀ x, φ'.1 x = ψ (0 * q4 δ x + B4 δ x (-v)) * φ.1 x := fun _ => rfl
  have hr : ∫ x, φ'.1 x ∂(adeleMeasurePi F) = ft4 δ φ.1 (-v) := by
    unfold ft4
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add]
    exact mul_comm _ _
  have hl : ft4 δ (Pc δ (b : A F) φ.1) v =
      ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * Lam4 δ (b : A F) φ'.1 := by
    unfold ft4 Pc Lam4 abelian₂
    rw [← integral_add_right_eq_self
      (fun y => ∫ x, φ'.1 x * ψ ((b : A F) * q4 δ (x + y)) ∂(adeleMeasurePi F))
      (fun i => ((b⁻¹ : (A F)ˣ) : A F) * v i), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', zero_mul, zero_add, quaternaryForm_neg_right]
    rw [quadraticForm_shift_expand δ _ _ hbc x y v, psi_add', psi_add', psi_add']
    have e1 := psi_neg_mul (B4 δ x v)
    have e2 := psi_neg_mul (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)
    linear_combination (-(φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v))
      * (ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ v)) * ψ (((b⁻¹ : (A F)ˣ) : A F) * q4 δ v))) * e1
      - (φ.1 x * ψ ((b : A F) * q4 δ (x + y)) * ψ (B4 δ y v)) * e2
  rw [hl, h φ', hr]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem quadraticForm_add_expand (δ : F) (x y : V4 F) : q4 δ (x + y) = q4 δ x + B4 δ x y + q4 δ y := by
  simp only [q4, B4, Pi.add_apply]
  ring

private theorem quaternaryForm_unit_scaling (δ : F) (b : A F) (x y : V4 F) : B4 δ x (fun i => b * y i) = b * B4 δ x y := by
  simp only [B4]
  ring

private theorem quaternaryForm_zero_right (δ : F) (x : V4 F) : B4 δ x 0 = 0 := by
  simp [B4]

private theorem pc_eq (δ : F) (b : A F) (φ : V4 F → ℂ) (y : V4 F) :
    Pc δ b φ y = ψ (b * q4 δ y) * ft4 δ (fun x => ψ (b * q4 δ x) * φ x) fun i => b * y i := by
  simp only [Pc, ft4]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [quaternaryForm_unit_scaling, quadraticForm_add_expand, mul_add, mul_add, psi_add, psi_add]
  ring

private theorem chirp_mem (δ : F) (b : A F) (φ : V4 F → ℂ) (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun v => ψ (b * q4 δ v) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  have h := chirpQ F δ b 0 φ hφ
  simpa only [quaternaryForm_zero_right, add_zero] using h

private theorem scale_mem (b : (A F)ˣ) (φ : V4 F → ℂ) (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun v : V4 F => φ fun i => (b : A F) * v i) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  have h := UpperTheory.ConvolutionTheory.R2.D.sClos F (Fin 4) (Units.map (Matrix.scalar (Fin 4)).toMonoidHom b) φ hφ
  convert h using 3 with v
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal_apply]

theorem UpperTheory.ConvolutionTheory.R2.C.pcMem :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), (∀ b φ y, Pc δ b φ y = ψ (b * q4 δ y) * ft4 δ (fun x => ψ (b * q4 δ x) * φ x) fun i => b * y i) ∧
    (δ ≠ 0 → ∀ b : (A F)ˣ, ∀ φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4), Pc δ (b : A F) φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) := by
  intro F _ _ δ
  refine ⟨pc_eq δ, fun hδ b φ hφ => ?_⟩
  have e : Pc δ (b : A F) φ = fun y => ψ ((b : A F) * q4 δ y) *
      ft4 δ (fun x => ψ ((b : A F) * q4 δ x) * φ x) fun i => (b : A F) * y i :=
    funext (pc_eq δ b φ)
  rw [e]
  exact chirp_mem δ b _ (scale_mem b _ (ftBasic F δ hδ _ (chirp_mem δ b φ hφ)).1)
end

