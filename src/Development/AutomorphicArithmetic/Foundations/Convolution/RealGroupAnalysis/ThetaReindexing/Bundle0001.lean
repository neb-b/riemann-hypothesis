module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.D

variable {F : Type} [Field F] [NumberField F]

private theorem comp_signed_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (ε : κ → F)
    (hε : ∀ k, ε k * ε k = 1) {G : (κ → A F) → ℂ} (hG : G ∈ schwartzBruhatPi (K := F) (ι := κ)) :
    (fun x : ι → A F => G fun k => rt (ε k) * x (e k)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  have hD : Matrix.diagonal ε * Matrix.diagonal ε = (1 : Matrix κ κ F) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact hε k
  let M : Matrix κ ι F := (Matrix.diagonal ε).submatrix id e.symm
  let N : Matrix ι κ F := (Matrix.diagonal ε).submatrix e.symm id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) e.symm id e.symm
      Function.bijective_id
    rw [hD, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (Matrix.diagonal ε) (Matrix.diagonal ε) id e.symm id
      e.symm.bijective
    rw [hD, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hG
  have hx : ∀ x : ι → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun k => rt (ε k) * x (e k) := by
    intro x
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← e.sum_comp]
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simpa only [hx] using h

private def eS : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private def sg : Fin 3 ⊕ Unit → F := Sum.elim 1 fun _ => -1

private theorem sg_mul (k) : (sg k : F) * sg k = 1 := by
  rcases k with i | i <;> simp [sg]

private def FF (φ : V4 F → ℂ) (z : Fin 3 ⊕ Unit → A F) : ℂ := φ fun i => z (eS.symm i)

private theorem FF_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    FF φ ∈ schwartzBruhatPi (K := F) (ι := Fin 3 ⊕ Unit) := by
  have h := comp_signed_mem (F := F) eS.symm (fun _ => 1) (fun _ => by simp) hφ
  have he : FF φ = fun x => φ fun k => rt ((fun _ => 1 : Fin 4 → F) k) * x (eS.symm k) := by
    funext x
    simp [FF]
  rw [he]
  exact h

private theorem hat_eq (φ : V4 F → ℂ) (x : V4 F) :
    hat φ x = GroundTheory.Heights₂.Theta.partialFourierPi (FF φ) fun k => rt (sg k) * x (eS k) := by
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  have h := hmp.integral_comp' (g := fun s => φ (Function.update x 1 s) * ψ (-(s * x 1)))
  rw [hat, ← h, GroundTheory.Heights₂.Theta.partialFourierPi, adelicFourierPi, adeleMeasurePi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h1 : Function.update x 1 (MeasurableEquiv.funUnique Unit (A F) y) =
      fun i => (Sum.elim (fun i => rt (sg (Sum.inl i)) * x (eS (Sum.inl i))) y
        : Fin 3 ⊕ Unit → A F) (eS.symm i) := by
    funext i
    fin_cases i <;> simp [eS, sg]
  have h2 : ψ (-(MeasurableEquiv.funUnique Unit (A F) y * x 1)) =
      ((adelicChar F (∑ i, y i * (rt (sg (Sum.inr i)) * x (eS (Sum.inr i)))) : Circle) : ℂ) := by
    simp [ψ, eS, sg]
  simp only [FF]
  rw [h1, h2]

private def tE {ι κ : Type} (e : κ ≃ ι) (ε : κ → F) (hε : ∀ k, ε k * ε k = 1) : (ι → F) ≃ (κ → F) where
  toFun ξ k := ε k * ξ (e k)
  invFun ξ i := ε (e.symm i) * ξ (e.symm i)
  left_inv ξ := by
    funext i
    simp [← mul_assoc, hε]
  right_inv ξ := by
    funext k
    simp [← mul_assoc, hε]

end UpperTheory.ConvolutionTheory.R2.D

end

theorem UpperTheory.ConvolutionTheory.R2.D.hatMem :
    ∀ (F : Type) [Field F] [NumberField F] (φ : S4 F), hat φ.1 ∈ schwartzBruhatPi (K := F) (ι := Fin 4) ∧ Th φ.1 = Th (hat φ.1) := by
  intro F _ _ φ
  have hF := FF_mem φ.2
  constructor
  · have h := comp_signed_mem (F := F) eS sg sg_mul (GroundTheory.Heights₂.Theta.partialFourierPi_mem hF)
    have he : hat φ.1 = fun x => GroundTheory.Heights₂.Theta.partialFourierPi (FF φ.1) fun k => rt (sg k) * x (eS k) :=
      funext (hat_eq φ.1)
    rw [he]
    exact h
  · have hP := GroundTheory.Heights₂.Theta.tsum_partialFourierPi hF
    have h1 : Th φ.1 = ∑' ξ : Fin 3 ⊕ Unit → F, FF φ.1 fun s => algebraMap F (A F) (ξ s) := by
      rw [Th, ← (tE (F := F) eS (fun _ => 1) (fun _ => by simp)).tsum_eq]
      refine tsum_congr fun ξ => ?_
      simp [FF, tE]
    have h2 : Th (hat φ.1) = ∑' ξ : Fin 3 ⊕ Unit → F,
        GroundTheory.Heights₂.Theta.partialFourierPi (FF φ.1) fun s => algebraMap F (A F) (ξ s) := by
      rw [Th, ← (tE (F := F) eS sg sg_mul).tsum_eq]
      refine tsum_congr fun ξ => ?_
      rw [hat_eq]
      congr 1
      funext k
      simp [tE]
    rw [h1, h2, hP]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatN
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.D.hatN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ b φ v, hat (W.Om (nU b) φ).1 v = ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * hat φ.1 (Function.update v 1 (v 1 + b * v 0)) := by
  intro F E _ _ _ _ _ _ _ D W b φ v
  have hψ : ∀ x y : A F, ψ (x + y) = ψ x * ψ y := by
    intro x y
    simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hq : ∀ s : A F, q4 D.δ (Function.update v 1 s) = v 2 ^ 2 - rt D.δ * v 3 ^ 2 - s * v 0 := by
    intro s
    simp [q4]
  unfold hat
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have h : ψ (b * q4 D.δ (Function.update v 1 s)) * ψ (-(s * v 1)) =
      ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * ψ (-(s * (v 1 + b * v 0))) := by
    rw [← hψ, ← hψ, hq]
    congr 1
    ring
  simp only [W.Om_n, Function.update_idem, Function.update_self]
  linear_combination (φ.1 (Function.update v 1 s)) * h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.IntegralMulLeftAdele
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

private theorem integral_mul_left_adele {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (g : A F → ℂ) :
    ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) = (((ab a)⁻¹ : ℝ) : ℂ) * ∫ s, g s ∂(adeleMeasure F) := by
  have hpos : 0 ≤ ((IdeleGroup.ideleModule F a : ℝ))⁻¹ := inv_nonneg.mpr (IdeleGroup.ideleModule F a).2.le
  have hmap := map_smul_adeleMeasure (K := F) a
  have he : MeasurableEmbedding (fun x : A F => a • x) :=
    (Homeomorph.smul a).measurableEmbedding
  have h1 : ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) =
      ∫ s, g s ∂((adeleMeasure F).map (fun x : A F => a • x)) :=
    (he.integral_map g).symm
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal hpos]
  rw [Complex.real_smul]
  rfl

theorem UpperTheory.ConvolutionTheory.R2.D.hatM :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (a : (A F)ˣ) φ v, hat (W.Om (mD a) φ).1 v = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
      hat φ.1 ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] := by
  intro F E _ _ _ _ _ _ _ D W a φ v
  have hab : ((ab a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (IdeleGroup.ideleModule F a).2
  set w : V4 F := ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] with hw
  have hpt : ∀ s : A F, (fun i => (a : A F) * Function.update v 1 s i) =
      Function.update w 1 ((a : A F) * s) := by
    intro s
    funext i
    fin_cases i <;> simp [hw, Function.update]
  have hch : ∀ s : A F, (a : A F) * s * w 1 = s * v 1 := by
    intro s
    have : w 1 = ((a⁻¹ : (A F)ˣ) : A F) * v 1 := by simp [hw]
    rw [this, mul_mul_mul_comm, Units.mul_inv, one_mul]
  obtain ⟨G, hG⟩ : ∃ G : A F → ℂ, G = fun r => φ.1 (Function.update w 1 r) * ψ (-(r * w 1)) := ⟨_, rfl⟩
  have hL : hat (W.Om (mD a) φ).1 v =
      ∫ s, ((W.η.1 a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * G ((a : A F) * s) ∂(adeleMeasure F) := by
    unfold hat
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [W.Om_m, hpt s, hG, hch s]
    ring
  have hR : hat φ.1 w = ∫ s, G s ∂(adeleMeasure F) := by
    rw [hG]
    rfl
  rw [hL, integral_const_mul, integral_mul_left_adele, hR]
  push_cast
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.IntegralScale
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem co_mkE (D : Dat F E) (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h : D.mkE u t = u • AdeleBaseChange.adeleBasis D.b 0 + t • AdeleBaseChange.adeleBasis D.b 1 := by
    rw [AdeleBaseChange.adeleBasis_apply, AdeleBaseChange.adeleBasis_apply, D.b0, D.b1,
      Algebra.smul_def, Algebra.smul_def, map_one, mul_one]
    rfl
  funext i
  unfold Dat.co
  rw [h]
  fin_cases i <;> simp

private theorem sigma_ne (D : Dat F E) : D.σ ≠ 1 := by
  intro h
  have h1 := D.conj
  rw [h] at h1
  have h2 : (2 : E) * D.θ = 0 := by
    have : D.θ = -D.θ := h1
    linear_combination this
  have h3 : D.θ = 0 := by simpa using h2
  exact D.b.ne_zero 1 (by rw [D.b1, h3])

private theorem finrank_two (D : Dat F E) : Module.finrank F E = 2 := by
  simpa using Module.finrank_eq_card_basis D.b

private theorem galois (D : Dat F E) : IsGalois F E := by
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite D.b
  apply IsGalois.of_card_aut_eq_finrank
  rw [finrank_two D]
  apply le_antisymm
  · rw [← finrank_two D, Nat.card_congr (algEquivEquivAlgHom F E).toEquiv, Nat.card_eq_fintype_card]
    exact AlgHom.card_le
  · have : ({1, D.σ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm (sigma_ne D))
    rw [← this, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _

private theorem mul_bar (D : Dat F E) (α : (A E)ˣ) :
    AdeleBaseChange.adeleMap F E ((ideleNorm F E α : (A F)ˣ) : A F) = (α : A E) * D.bar α := by
  haveI := galois D
  rw [coe_ideleNorm, AdeleBaseChange.adeleMap_norm]
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, D.σ} := by
    haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite D.b
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair (Ne.symm (sigma_ne D)), Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, finrank_two D]
  rw [hu, Finset.prod_pair (Ne.symm (sigma_ne D))]
  simp [Dat.bar]

end SlopeTestRemainingChoices

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem act_aE (D : Dat F E) (α : (A E)ˣ) (y s z₀ z₁ : A F) :
    D.act (aE α)⁻¹ ![y, s, z₀, z₁] =
      ![y, (((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s, D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0,
        D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1] := by
  have hinv : (((aE α)⁻¹ : GL (Fin 2) (A E))).val = !![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] := rfl
  have hN : AdeleBaseChange.adeleMap F E (((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) =
      ((α⁻¹ : (A E)ˣ) : A E) * D.bar ((α⁻¹ : (A E)ˣ) : A E) := by
    rw [← map_inv, mul_bar]
  have hz : D.mkE 0 0 = 0 := by simp [Dat.mkE]
  have h00 : ((α⁻¹ : (A E)ˣ) : A E) * D.mkE s 0 * D.bar ((α⁻¹ : (A E)ˣ) : A E) =
      D.mkE ((((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s) 0 := by
    simp only [Dat.mkE, map_mul, hN, map_zero, zero_mul, add_zero]
    ring
  unfold Dat.act Dat.unherm
  rw [hinv]
  have hm : (!![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] * D.herm ![y, s, z₀, z₁] *
      ((!![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)).map D.bar)ᵀ) =
      !![D.mkE ((((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s) 0, ((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁;
        D.mkE z₀ (-z₁) * D.bar ((α⁻¹ : (A E)ˣ) : A E), D.mkE y 0] := by
    rw [← h00]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hm]
  simp [co_mkE]

private theorem ab_inv (a : (A F)ˣ) : ab a⁻¹ = (ab a)⁻¹ := by
  simp [ab]

private theorem integral_scale (a : (A F)ˣ) (G : A F → ℂ) :
    ∫ s, G ((a : A F) * s) ∂(adeleMeasure F) = (((ab a)⁻¹ : ℝ) : ℂ) * ∫ s, G s ∂(adeleMeasure F) := by
  have hemb : MeasurableEmbedding (fun x : A F => (a : IdeleGroup F) • x) :=
    (Homeomorph.smul (a : IdeleGroup F)).measurableEmbedding
  have h := hemb.integral_map (μ := adeleMeasure F) G
  rw [map_smul_adeleMeasure, integral_smul_measure] at h
  have h2 : ∫ s, G ((a : A F) * s) ∂(adeleMeasure F) = ∫ x, G ((a : IdeleGroup F) • x) ∂(adeleMeasure F) := rfl
  rw [h2, ← h, ENNReal.toReal_ofReal (inv_pos.2 (IdeleGroup.ideleModule F a).2).le, Complex.real_smul]
  rfl

end Aux2

theorem UpperTheory.ConvolutionTheory.R2.D.hatAE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (α : (A E)ˣ) φ y x z₀ z₁, hat (W.L (aE α) φ).1 ![y, x, z₀, z₁] =
      hat φ.1 ![y, (ideleNorm F E α : (A F)ˣ) * x, D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0,
        D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1] := by
  intro F E _ _ _ _ _ _ _ D W α φ y x z₀ z₁
  have hdet : Matrix.GeneralLinearGroup.det (aE α) = α := by
    ext
    simp [aE, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]
  have hnu : nu F (aE α) = ideleNorm F E α := by
    rw [nu, hdet]
  have hup : ∀ a b c d s : A F, Function.update ![a, b, c, d] 1 s = ![a, s, c, d] := by
    intro a b c d s
    ext i
    fin_cases i <;> simp
  set N : (A F)ˣ := ideleNorm F E α with hN
  set c₀ := D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0
  set c₁ := D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1
  let G : A F → ℂ := fun s => φ.1 ![y, s, c₀, c₁] * ψ (-(s * ((N : A F) * x)))
  have hpt : ∀ s : A F, (W.L (aE α) φ).1 (Function.update ![y, x, z₀, z₁] 1 s) * ψ (-(s * (![y, x, z₀, z₁] : V4 F) 1)) =
      (((ab N)⁻¹ : ℝ) : ℂ) * G (((N⁻¹ : (A F)ˣ) : A F) * s) := by
    intro s
    have hs : ((N⁻¹ : (A F)ˣ) : A F) * s * ((N : A F) * x) = s * x := by
      have : ((N⁻¹ : (A F)ˣ) : A F) * (N : A F) = 1 := Units.inv_mul N
      linear_combination (s * x) * this
    rw [hup, W.L_apply, hnu, act_aE]
    simp only [G, hs]
    exact mul_assoc _ _ _
  have hab : ab N ≠ 0 := (IdeleGroup.ideleModule F N).2.ne'
  have hL : hat (W.L (aE α) φ).1 ![y, x, z₀, z₁] = ∫ s, G s ∂(adeleMeasure F) := by
    unfold hat
    simp_rw [hpt]
    rw [integral_const_mul, integral_scale (N⁻¹) G, ab_inv, inv_inv, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hab]
    simp
  rw [hL]
  unfold hat
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [G, hup]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MapMulInvEqOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding

section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem map_mul_inv_eq_one {R : Type} [CommRing R] (h : A K →+* R) (g : GL ι (A K)) :
    g.val.map h * (g⁻¹).val.map h = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one h (map_zero h) (map_one h)]

private theorem map_inv_mul_eq_one {R : Type} [CommRing R] (h : A K →+* R) (g : GL ι (A K)) :
    (g⁻¹).val.map h * g.val.map h = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one h (map_zero h) (map_one h)]

private noncomputable def infEquiv (g : GL ι (A K)) :
    (ι → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ g.val.map adeleInfHom *ᵥ u
      invFun := fun u ↦ (g⁻¹).val.map adeleInfHom *ᵥ u
      map_add' := fun u v ↦ Matrix.mulVec_add _ u v
      map_smul' := fun c u ↦ Matrix.mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_inv_mul_eq_one, Matrix.one_mulVec]
      right_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_mul_inv_eq_one, Matrix.one_mulVec] }

private noncomputable def finHomeo (g : GL ι (A K)) :
    (ι → FiniteAdeleRing (𝓞 K) K) ≃ₜ (ι → FiniteAdeleRing (𝓞 K) K) where
  toFun u := g.val.map adeleFinHom *ᵥ u
  invFun u := (g⁻¹).val.map adeleFinHom *ᵥ u
  left_inv u := by
    simp only [Matrix.mulVec_mulVec, map_inv_mul_eq_one, Matrix.one_mulVec]
  right_inv u := by
    simp only [Matrix.mulVec_mulVec, map_mul_inv_eq_one, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

private theorem infPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    infPartPi (g.val *ᵥ x) = infEquiv g (infPartPi x) := by
  rw [infPartPi_eq_adeleInfHom, infPartPi_eq_adeleInfHom, map_mulVec_eq]
  rfl

private theorem finPartPi_gl (g : GL ι (A K)) (x : ι → A K) :
    finPartPi (g.val *ᵥ x) = finHomeo g (finPartPi x) := by
  rw [finPartPi_eq_adeleFinHom, finPartPi_eq_adeleFinHom, map_mulVec_eq]
  rfl

end

end UpperTheory.ConvolutionTheory.R2.D

theorem UpperTheory.ConvolutionTheory.R2.D.sClos :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (A F)) (φ : (ι → A F) → ℂ),
    φ ∈ schwartzBruhatPi (K := F) (ι := ι) → (fun v => φ (g.val *ᵥ v)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  intro F _ _ ι _ _ g φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, h, hh, rfl⟩ := hG
    have e : (fun v => schwartzBruhatTensorPi f h (g.val *ᵥ v)) =
        schwartzBruhatTensorPi (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (infEquiv g) f)
          (h ∘ finHomeo g) := by
      funext x
      simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, infPartPi_gl, finPartPi_gl]
    rw [e]
    refine schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi F).2 ⟨?_, ?_⟩)
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).1.comp_continuous (finHomeo g).continuous
    · exact ((mem_finiteSchwartzBruhatPi F).1 hh).2.comp_homeomorph (finHomeo g)
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG
end

