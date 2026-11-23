module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhds
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.OpenCrit

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

def vOf (g : UG c (stdJ ν E)) : Matrix ν ν E := (mat c g).toBlocks₂₂⁻¹ * (mat c g).toBlocks₂₁

theorem lower_rel (g : UG c (stdJ ν E)) :
    (mat c g).toBlocks₂₁ * ((mat c g).toBlocks₂₂.map c)ᵀ = (mat c g).toBlocks₂₂ * ((mat c g).toBlocks₂₁.map c)ᵀ := by
  have h : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [← fromBlocks_toBlocks (mat c g)] at h2
  simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply] at h2
  rw [neg_add_eq_zero] at h2
  exact h2.symm

theorem vOf_herm (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) :
    ((-vOf c g).map c)ᵀ = -vOf c g := by
  set D := (mat c g).toBlocks₂₂ with hD
  set C := (mat c g).toBlocks₂₁ with hC
  have hrel : C * (D.map c)ᵀ = D * (C.map c)ᵀ := lower_rel c g
  have hdetc : ((D.map c)ᵀ).det = c D.det := by
    rw [det_transpose, show D.map c = (c : E →+* E).mapMatrix D from rfl, ← RingHom.map_det]; rfl
  have hDs : IsUnit ((D.map c)ᵀ).det := by rw [hdetc]; exact hd.map c
  have hV : vOf c g = D⁻¹ * C := rfl
  have hDV : D * vOf c g = C := by rw [hV, mul_nonsing_inv_cancel_left _ _ hd]
  have hstar : ((vOf c g).map c)ᵀ * (D.map c)ᵀ = (C.map c)ᵀ := by
    rw [← transpose_mul, ← hDV]
    exact congrArg Matrix.transpose (Matrix.map_mul (f := c.toRingHom) (L := D) (M := vOf c g)).symm
  have key : D * ((vOf c g).map c)ᵀ * (D.map c)ᵀ = D * vOf c g * (D.map c)ᵀ := by
    rw [Matrix.mul_assoc, hstar, hDV, hrel]
  have h3 : ((vOf c g).map c)ᵀ = vOf c g := by
    have := congrArg (fun X => D⁻¹ * X * ((D.map c)ᵀ)⁻¹) key
    simp only [Matrix.mul_assoc] at this
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_nonsing_inv _ hDs, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h3]


open scoped Classical in
def nOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) :=
  if h : IsUnit (mat c g).toBlocks₂₂.det then unip c (-vOf c g) (vOf_herm c g h) else 1

def kOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := (weyl c ν)⁻¹ * nOf c g * weyl c ν

def pOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := g * (kOf c g)⁻¹

theorem nOf_mem (g : UG c (stdJ ν E)) : nOf c g ∈ sieg c ν := by
  unfold nOf
  split_ifs with h
  · rw [mem_sieg]
    change (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    simp
  · exact (sieg c ν).one_mem

theorem pOf_mem (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) : pOf c g ∈ sieg c ν := by
  rw [mem_sieg]
  have hk : mat c (pOf c g) = mat c g * (-stdJ ν E * (fromBlocks 1 (-(-vOf c g)) 0 1 * stdJ ν E)) := by
    simp only [pOf, kOf, _root_.mul_inv_rev, inv_inv, nOf, dif_pos hd]
    rfl
  rw [hk]
  have hDV : (mat c g).toBlocks₂₂ * vOf c g = (mat c g).toBlocks₂₁ := mul_nonsing_inv_cancel_left _ _ hd
  set M := mat c g
  rw [← fromBlocks_toBlocks M]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]
  rw [hDV, add_neg_cancel]

section Top

variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

theorem continuous_mat : Continuous (mat c : UG c (stdJ ν E) → Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_blk₂₂ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem continuous_blk₂₁ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₁ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem blk₂₂_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₂ = 1 := by
  ext i j; simp [mat, toBlocks₂₂, Matrix.one_apply]

theorem blk₂₁_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₁ = 0 := by
  ext i j; simp [mat, toBlocks₂₁, one_apply]

theorem eventually_isUnit : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), IsUnit (mat c g).toBlocks₂₂.det := by
  have h : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1) (𝓝 1) := by
    have := ((continuous_blk₂₂ c).matrix_det).tendsto (1 : UG c (stdJ ν E))
    rwa [blk₂₂_one, det_one] at this
  filter_upwards [h.eventually_ne one_ne_zero] with g hg
  exact isUnit_iff_ne_zero.mpr hg

theorem tendsto_vOf : Tendsto (vOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 0) := by
  have hinv : ContinuousAt (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv', blk₂₂_one, det_one]
    exact continuousAt_inv₀ one_ne_zero
  have h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1)) := (hinv.mul (continuous_blk₂₁ c).continuousAt).tendsto
  have h0 : vOf c (1 : UG c (stdJ ν E)) = 0 := by rw [vOf, blk₂₁_one, Matrix.mul_zero]
  rwa [h0] at h2

theorem tendsto_nOf : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
  rw [tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hv := tendsto_vOf c (ν := ν)
  have hA : Tendsto (fun g => (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-v) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, fromBlocks_one] at this
  have hB : Tendsto (fun g => (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-(-v)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg.neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, neg_zero, fromBlocks_one] at this
  have hE : (fun g => ((fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E),
      MulOpposite.op (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) =ᶠ[𝓝 1]
      (Units.embedProduct _ ∘ fun g => ((nOf c g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E)) := by
    filter_upwards [eventually_isUnit c] with g hg
    simp only [Function.comp_apply, nOf, dif_pos hg]
    rfl
  refine Tendsto.congr' hE ?_
  have h1 : Units.embedProduct _ ((1 : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = (1, MulOpposite.op 1) := rfl
  rw [h1]
  exact hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)

end Top

end GlobalTheory.KSp.OpenCrit

namespace GlobalTheory.KSp


open OpenCrit in
theorem isOpen_of_sieg_of_opp (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (h1 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U)
    (h2 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) :
    IsOpen (U : Set (UG c (stdJ ν E))) := by
  obtain ⟨-, hTR, hCI, hT2, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  haveI := hTR
  haveI := hCI
  haveI := hT2
  refine Subgroup.isOpen_of_mem_nhds U (g := 1) ?_
  have hn : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := tendsto_nOf c
  have hk : Tendsto (kOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (weyl c ν)⁻¹)).mul hn).mul (tendsto_const_nhds (x := weyl c ν))
    rwa [mul_one, inv_mul_cancel] at this
  have hp : Tendsto (pOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := (tendsto_id (x := 𝓝 (1 : UG c (stdJ ν E)))).mul hk.inv
    rwa [inv_one, mul_one] at this
  filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd
  have hg : g = pOf c g * kOf c g := by rw [pOf, inv_mul_cancel_right]
  rw [hg]
  exact U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRootsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  first | (exact @GlobalTheory.EtC.isField_aic_sh) | (exact GlobalTheory.EtC.isField_aic_sh) | (intros; apply GlobalTheory.EtC.isField_aic_sh  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorOfCompatIsIsoTargetStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTensor_of_compat_isIso_target : ∀ (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K') (u : K ⟶ K'), IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  first | (exact @GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (exact GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (intros; apply GlobalTheory.EtC.Pair.isTensor_of_compat_isIso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisQuotientIntegralClosure
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


open Polynomial in
theorem isTranscendenceBasis_quotient_integralClosure
    (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
    [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K)
    (hB : B = (integralClosure A K).restrictScalars k) (Q : Ideal B) (hQ : Q.IsPrime) (t : A)
    (htQ : ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a))
    (m : ℕ) (y : Fin m → A)
    (hy : IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)))
    (y' : Fin m → B) (hy' : ∀ j, (y' j : K) = algebraMap F K (y j)) :
    IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y' j)) := by
  have := hQ
  have hBK : ∀ x : K, x ∈ B ↔ IsIntegral A x := by
    intro x; rw [hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have hmem : ∀ a : A, algebraMap F K (a : F) ∈ B := fun a =>
    (hBK _).2 (isIntegral_algebraMap (R := A) (A := K) (x := a))
  let ι : A →+* B := ((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem
  have hι : ∀ a : A, ((ι a : B) : K) = algebraMap F K (a : F) := fun a => rfl
  let g : A →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp ι
  have hg : ∀ a : A, g a = 0 ↔ a ∈ Ideal.span {t} := by
    intro a
    rw [Ideal.mem_span_singleton, ← htQ a (ι a) (hι a)]
    exact Ideal.Quotient.eq_zero_iff_mem
  let f : A ⧸ Ideal.span {t} →+* B ⧸ Q :=
    Ideal.Quotient.lift (Ideal.span {t}) g (fun a ha => (hg a).2 ha)
  have hf : ∀ a : A, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk Q (ι a) := fun a => rfl
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hg a).1 hx)
  let : Algebra (A ⧸ Ideal.span {t}) (B ⧸ Q) := f.toAlgebra
  have : IsScalarTower k (A ⧸ Ideal.span {t}) (B ⧸ Q) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change Ideal.Quotient.mk Q (algebraMap k B c) = f (Ideal.Quotient.mk _ (algebraMap k A c))
    rw [hf]
    congr 1
    apply Subtype.ext
    rw [hι]
    change algebraMap k K c = algebraMap F K (algebraMap k F c)
    exact IsScalarTower.algebraMap_apply k F K c
  have : FaithfulSMul (A ⧸ Ideal.span {t}) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : NoZeroDivisors (A ⧸ Ideal.span {t}) :=
    hinj.noZeroDivisors f (map_zero f) (map_mul f)
  have : Nontrivial (A ⧸ Ideal.span {t}) := f.domain_nontrivial
  have : Algebra.IsIntegral (A ⧸ Ideal.span {t}) (B ⧸ Q) := by
    constructor
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hpm, hp⟩ := (hBK _).1 b.2
    refine ⟨p.map (Ideal.Quotient.mk _), hpm.map _, ?_⟩
    have h0 : p.eval₂ ι b = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ p ι B.val.toRingHom b
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.coe_val] at this
      rw [this]
      exact hp
    rw [RingHom.algebraMap_toAlgebra, Polynomial.eval₂_map]
    have hfg : f.comp (Ideal.Quotient.mk (Ideal.span {t})) = (Ideal.Quotient.mk Q).comp ι :=
      RingHom.ext fun a => hf a
    rw [hfg, ← Polynomial.hom_eval₂, h0, map_zero]
  have key := hy.algebraMap_comp (A := B ⧸ Q)
  convert key using 1
  funext j
  change Ideal.Quotient.mk Q (y' j) = Ideal.Quotient.mk Q (ι (y j))
  exact congrArg (Ideal.Quotient.mk Q) (Subtype.ext ((hy' j).trans (hι (y j)).symm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroTensorOfDegreeZeroComplexes
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TensZero

variable {R : Type} [CommRing R]

theorem sec_eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h : 𝟙 F = 0 := hF.eq_of_src _ _
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  have h1 : Sec.map (𝟙 F) a = a := rfl
  have h2 : Sec.map (0 : F ⟶ F) a = 0 := by
    simp only [Sec.map]
    rfl
  rw [h1, h2] at this
  exact this

theorem isZero_of_sec {F : Shv R} (h : ∀ (U : Scheme.{0}) (a : Sec F U), a = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  refine ((GlobalTheory.EtC.mono_epi_sections R (𝟙 F)).2.2.2 0 fun U a => ?_)
  rw [h U a]
  simp

theorem tens_eq_zero {I J : Cx R} (hI : ∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) (hJ : ∀ t : ℤ, t ≠ 0 → IsZero (J.X t))
    (U : Scheme.{0}) (w : ℤ) (hw : w ≠ 0) (x : Tens I J U w) : x = 0 := by
  refine DFinsupp.ext fun p => ?_
  show x p = 0
  have hp := p.2
  by_cases h1 : p.1.1 = 0
  · have h2 : p.1.2 ≠ 0 := by omega
    induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hJ _ h2) b, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  · induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hI _ h1) a, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]

end GlobalTheory.EtC.TensZero

open GlobalTheory.EtC.TensZero in
theorem GlobalTheory.EtC.isZero_tensor_of_deg_zero : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) → (∀ t : ℤ, t ≠ 0 → IsZero (J.X t)) → ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) := by
  intro R _ I J K τ hτ hI hJ w hw
  refine isZero_of_sec fun U y => ?_
  refine (GlobalTheory.EtC.sec_ext_glue R (K.X w) U).1 y 0 ?_
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [tens_eq_zero hI hJ V w hw x, map_zero] at hx
  rw [← hx]
  exact (map_zero _).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosureProperties
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem dDR_ιMulti_D (q : ℕ) (v : Fin q → K) :
    dDR k K (ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (DR k K)), dDR_algebraMap,
      Derivation.map_one_eq_zero, map_zero]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, dDR_mul]
    have ht : Matrix.vecTail (fun j => D k K (v j)) = fun j => D k K (v j.succ) := rfl
    rw [ht, ih (fun j => v j.succ), mul_zero, zero_add,
      show dDR k K (ExteriorAlgebra.ι K (D k K (v 0))) = 0 from dDR_D (v 0), zero_mul]

variable {k K}

theorem mem_deg_of_mem_omB (B : Subalgebra k K) (q : ℕ) (a : DR k K) (ha : a ∈ omB k K B q) :
    a ∈ ⋀[K]^q Ω[K⁄k] := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, v, -, rfl⟩ := hx
    exact Submodule.smul_mem _ c (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_of_tower_mem _ r hx

theorem mul_mem_omB (B : Subalgebra k K) (p q : ℕ) (a : DR k K) (ha : a ∈ omB k K B p)
    (b : DR k K) (hb : b ∈ omB k K B q) : a * b ∈ omB k K B (p + q) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hx
      obtain ⟨c', hc', w, hw, rfl⟩ := hy
      have happ : Fin.append (fun j => D k K (v j)) (fun j => D k K (w j)) =
          fun j => D k K (Fin.append v w j) := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      refine Submodule.subset_span ⟨c * c', B.mul_mem hc hc', Fin.append v w, fun j => ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · rw [Fin.append_left]; exact hv i
        · rw [Fin.append_right]; exact hw i
      · rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti, happ]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem dDR_mem_omB (B : Subalgebra k K) (p : ℕ) (a : DR k K) (ha : a ∈ omB k K B p) :
    dDR k K a ∈ omB k K B (p + 1) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [dDR_smul, dDR_ιMulti_D, smul_zero, add_zero]
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.cons c v, fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · rw [Fin.cons_zero]; exact hc
      · rw [Fin.cons_succ]; exact hv i
    · rw [one_smul, ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Matrix.vecTail, Function.comp_def, Fin.cons_succ, Fin.cons_zero]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem smul_mem_omB (B : Subalgebra k K) (p : ℕ) (c : K) (hc : c ∈ B) (a : DR k K)
    (ha : a ∈ omB k K B p) : c • a ∈ omB k K B p := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm c r x]; exact Submodule.smul_mem _ r hx

theorem omB_mono (B B' : Subalgebra k K) (h : B ≤ B') (p : ℕ) : omB k K B p ≤ omB k K B' p := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

theorem mem_omB_zero (B : Subalgebra k K) (y : DR k K) :
    y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, -, rfl⟩ := hx
      exact ⟨b, hb, by rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩
    | zero => exact ⟨0, B.zero_mem, (map_zero _).symm⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hz
      exact ⟨c + c', B.add_mem hc hc', (map_add _ _ _).symm⟩
    | smul r x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨r • c, B.smul_mem hc r, by simp only [Algebra.algebraMap_eq_smul_one, smul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.subset_span ⟨c, hc, Fin.elim0, fun j => j.elim0, by
      rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩

theorem omB_alg : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ),
    (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧
    (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧
      a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧
    (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧
    ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  intro k K _ _ _ B p q
  refine ⟨fun a ha b hb => mul_mem_omB B p q a ha b hb, fun a ha => ?_,
    fun B' h => omB_mono B B' h p, mem_omB_zero B⟩
  have hdeg := mem_deg_of_mem_omB B p a ha
  refine ⟨dDR_mem_omB B p a ha, ?_, hdeg, fun c hc => smul_mem_omB B p c hc a ha⟩
  change sgn a = _
  rw [sgn_of_mem hdeg, Algebra.smul_def, map_pow, map_neg, map_one]

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspaceStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDetRelation_herbrand_eigenspace : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) = q → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) (∑ s ∈ Finset.univ.erase τ, (Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ ((a τ : C) - (a s : C))) := by
  first | exact @GlobalTheory.HerbrandBridge.exForm | exact GlobalTheory.HerbrandBridge.exForm | (intros; apply GlobalTheory.HerbrandBridge.exForm <;> assumption)
end

