module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StGenusOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictTop
section
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

theorem dictTop_sig (I : AutInst) : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E :=
  RingHom.ext fun _ => rfl

theorem dictTop_mul_inv (I : AutInst) (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem dictTop_inv_mul (I : AutInst) (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem dictTop_fmat_mul (I : AutInst) (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl

private theorem hform_eq_dotProduct_mulVec {A : Type} [CommRing A] {k : ℕ} (σ : A →+* A)
    (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_eq_hform_cT_mul_mul {A : Type} [CommRing A] {k : ℕ} (σ : A →+* A)
    (J M : Matrix (Fin k) (Fin k) A) (a b : Fin k → A) :
    Formalism.UG.hform σ J (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) a b := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  show _ = (fun i => σ (a i)) ⬝ᵥ (((M.map σ)ᵀ * J * M) *ᵥ b)
  have e : (fun i => σ ((M *ᵥ a) i)) = M.map σ *ᵥ (fun i => σ (a i)) := by
    funext i
    exact RingHom.map_mulVec σ M a i
  rw [e, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose (M.map σ) (fun i => σ (a i)),
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem dictTop_hhat_unit (I : AutInst) (x : I.Gf) (a b : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (I.fmat x *ᵥ a) (I.fmat x *ᵥ b) = hhat I a b := by
  have hx : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hhat
  rw [hform_mulVec_mulVec_eq_hform_cT_mul_mul, hx]

private theorem sigR_inclE' (I : AutInst) (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) :=
  Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) e 1

private theorem inclE_hform (I : AutInst) (w v : Fin I.n → I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J w v) =
      hhat I (iv I w) (iv I v) := by
  unfold hhat iv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, sigR_inclE']

private theorem sigR_mem_intAf (I : AutInst) (c : I.E ⊗[I.F] Af I.F) (hc : c ∈ IntAf I.F I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) c ∈ IntAf I.F I.E := by
  have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      show Formalism.UG.sigR I.cm.sig (Af I.F)
        (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E o)) ∈ IntAf I.F I.E
      rw [sigR_inclE']
      have hs : starRingEnd I.E (algebraMap (𝓞 I.E) I.E o) ∈ Formalism.UG.intOE I.E :=
        ⟨⟨star (o : I.E),
          (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩
      exact Subring.subset_closure (Or.inl ⟨⟨_, hs⟩, rfl⟩)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) ∈ IntAf I.F I.E
      have h1 := Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) (1 : I.E) a
      rw [map_one] at h1
      have e1 : Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) = (1 : I.E) ⊗ₜ[I.F] a := h1
      rw [e1]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hle hc

private theorem hhat_zero_left' (I : AutInst) (z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I 0 z = 0 := by
  simp [hhat, Formalism.UG.hform]

private theorem hhat_add_left' (I : AutInst) (a b z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (a + b) z = hhat I a z + hhat I b z := by
  simp only [hhat, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

private theorem hhat_smul_left' (I : AutInst) (r : I.E ⊗[I.F] Af I.F)
    (a z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (r • a) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hhat I a z := by
  simp only [hhat, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem mDual_of (hDI : DInter) (hLI : LHatInt) (hLD : LHatDual) (hG : MGen) : MDual := by
  intro I x v
  constructor
  · intro hv w hw
    apply hDI I.F I.E
    rw [inclE_hform, ← dictTop_hhat_unit I x⁻¹]
    exact hLI I (I.fmat x⁻¹ *ᵥ iv I w) hw (I.fmat x⁻¹ *ᵥ iv I v) hv
  · intro hv
    show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf
    apply hLD I
    intro y hy
    rw [← dictTop_hhat_unit I x y, Matrix.mulVec_mulVec, dictTop_mul_inv, Matrix.one_mulVec]
    refine Submodule.span_induction (p := fun z _ => hhat I z (iv I v) ∈ IntAf I.F I.E)
      (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_) (fun c z _ hz => ?_) (hG I x y hy)
    · obtain ⟨w, rfl⟩ := hz
      obtain ⟨o, ho⟩ := hv w w.2
      rw [← inclE_hform, ← ho]
      exact Subring.subset_closure (Or.inl ⟨⟨(o : I.E), o, rfl⟩, rfl⟩)
    · rw [hhat_zero_left']
      exact (IntAf I.F I.E).zero_mem
    · rw [hhat_add_left']
      exact (IntAf I.F I.E).add_mem hz hw
    · show hhat I ((c : I.E ⊗[I.F] Af I.F) • z) (iv I v) ∈ IntAf I.F I.E
      rw [hhat_smul_left']
      exact (IntAf I.F I.E).mul_mem (sigR_mem_intAf I _ c.2) hz

theorem dictTop_into (hG : MGen) (I : AutInst) (a b : I.Gf) (h : abelian₂ I a = abelian₂ I b)
    (z : Fin I.n → I.E ⊗[I.F] Af I.F) (hz : z ∈ I.Lf) : I.fmat a⁻¹ *ᵥ (I.fmat b *ᵥ z) ∈ I.Lf := by
  refine Submodule.span_induction (p := fun y _ => I.fmat a⁻¹ *ᵥ y ∈ I.Lf)
    (fun y hy => ?_) ?_ (fun y w _ _ hy hw => ?_) (fun c y _ hy => ?_) (hG I b z hz)
  · obtain ⟨v, rfl⟩ := hy
    have hv : (v : Fin I.n → I.E) ∈ abelian₂ I a := by
      rw [h]
      exact v.2
    exact hv
  · rw [Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  · rw [Matrix.mulVec_add]
    exact I.Lf.add_mem hy hw
  · show I.fmat a⁻¹ *ᵥ ((c : I.E ⊗[I.F] Af I.F) • y) ∈ I.Lf
    rw [Matrix.mulVec_smul]
    exact I.Lf.smul_mem c hy

theorem mInj_of (hG : MGen) : MInj := by
  intro I x y h
  refine ⟨x⁻¹ * y, fun z => ?_, (mul_inv_cancel_left x y).symm⟩
  show z ∈ I.Lf ↔ I.fmat (x⁻¹ * y) *ᵥ z ∈ I.Lf
  rw [dictTop_fmat_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro hz
    exact dictTop_into hG I x y h z hz
  · intro hz
    have h2 := dictTop_into hG I y x h.symm _ hz
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at h2
    rwa [← Matrix.mul_assoc (I.fmat x), dictTop_mul_inv, Matrix.one_mul, dictTop_inv_mul,
      Matrix.one_mulVec] at h2

theorem dictTop_map_mulVec (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) I.E) (w : Fin I.n → I.E) :
    M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ iv I w = iv I (M *ᵥ w) := by
  funext i
  exact (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) M w i).symm

theorem lattice_m_equiv : MEquiv := by
  intro I γ hγ
  have hmem : Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ ∈
      Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F))
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    have hg : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
    have hc : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F))
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) =
        (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map
          (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      exact sigR_inclE' I _
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  let c : I.Gf := ⟨_, hmem⟩
  have hfc : I.fmat c =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  refine ⟨c, ⟨γ, hγ, rfl⟩, rfl, fun x v => ?_⟩
  have K : ∀ z, I.fmat (c * x)⁻¹ *ᵥ (I.fmat c *ᵥ z) = I.fmat x⁻¹ *ᵥ z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← dictTop_fmat_mul, mul_inv_rev, inv_mul_cancel_right]
  constructor
  · intro hv
    refine ⟨((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v, ?_, ?_⟩
    · show I.fmat x⁻¹ *ᵥ iv I (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v) ∈ I.Lf
      rw [← K, hfc, dictTop_map_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact hv
    · rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨w, hw, rfl⟩
    show I.fmat (c * x)⁻¹ *ᵥ iv I ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w) ∈ I.Lf
    rw [← dictTop_map_mulVec, ← hfc, K]
    exact hw

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HmkFactor
section
noncomputable section

namespace PIW.AdelClassFin

open MeasureTheory Matrix Module
open scoped MatrixOrder

theorem hmk_factor {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) :
    ∃ B : Matrix (Fin N) (Fin N) ℝ, G = Bᵀ * B := by
  refine ⟨CFC.sqrt G, ?_⟩
  have h0 : (0 : Matrix (Fin N) (Fin N) ℝ) ≤ G := hG.posSemidef.nonneg
  have hsa : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  have ht : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [ht, CFC.sqrt_mul_sqrt_self G h0]

theorem hmk_int {N : ℕ} (x : Fin N → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin N)))) :
    ∃ c : Fin N → ℤ, (fun i => (c i : ℝ)) = x := by
  rw [(Pi.basisFun ℝ (Fin N)).mem_span_iff_repr_mem (R := ℤ) x] at hx
  choose c hc using hx
  refine ⟨c, funext fun i => ?_⟩
  have := hc i
  simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom] at this
  exact this

theorem hmk_box {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.det ≠ 0) :
    ∃ c : Fin N → ℤ, c ≠ 0 ∧
      ∀ i, |(B *ᵥ fun j => (c j : ℝ)) i| ≤ 2 * |B.det| ^ ((1 : ℝ) / N) := by
  set d := |B.det| with hd
  have hd0 : 0 < d := abs_pos.mpr hB
  set t := 2 * d ^ ((1 : ℝ) / N) with ht
  have ht0 : 0 < t := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have htN : t ^ N = 2 ^ N * d := by
    rw [ht, mul_pow, ← Real.rpow_natCast (d ^ _), ← Real.rpow_mul hd0.le]
    rw [one_div_mul_cancel hN0, Real.rpow_one]
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Matrix.toLin' B
  have hf : LinearMap.det f ≠ 0 := by rw [LinearMap.det_toLin']; exact hB
  let box : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-t) t
  let s : Set (Fin N → ℝ) := f ⁻¹' box
  let b := Pi.basisFun ℝ (Fin N)
  have fund := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin N → ℝ))
  have hvolF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp
  have hvolbox : volume box = ENNReal.ofReal (2 * t) ^ N := by
    simp only [box]
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hvols : volume s = ENNReal.ofReal (4 ^ N) := by
    simp only [s]
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hf, hvolbox,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [LinearMap.det_toLin', abs_inv, ← hd, mul_pow, htN]
    rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
    field_simp
  have h_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      map_neg, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  have h_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Icc (-t) t).linear_preimage f
  have h : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (Fin N → ℝ) < volume s := by
    rw [hvolF, one_mul, hvols, Module.finrank_fin_fun]
    rw [show (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv h
  obtain ⟨c, hc⟩ := hmk_int (x : Fin N → ℝ) x.2
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply hx0
    ext i
    have := congrFun hc i
    simp at this
    simp [← this]
  · intro i
    have := hxs
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc] at this
    rw [hc]
    exact abs_le.mpr (this i)

theorem partMink : PartMink := by
  intro N hN
  refine ⟨4 * N, fun G hG => ?_⟩
  obtain ⟨B, rfl⟩ := hmk_factor G hG
  have hdet : (Bᵀ * B).det = B.det ^ 2 := by rw [det_mul, det_transpose, sq]
  have hpos := hG.det_pos
  have hB : B.det ≠ 0 := by
    intro h0; rw [hdet, h0] at hpos; simp at hpos
  obtain ⟨c, hc0, hc⟩ := hmk_box hN B hB
  refine ⟨c, hc0, ?_⟩
  set v : Fin N → ℝ := fun i => (c i : ℝ)
  set d := |B.det|
  have hd0 : 0 < d := abs_pos.mpr hB
  have hq : v ⬝ᵥ ((Bᵀ * B) *ᵥ v) = ∑ i, (B *ᵥ v) i ^ 2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, sq]
  have hdetG : (Bᵀ * B).det = d ^ 2 := by rw [hdet, sq_abs]
  have hpow : (d ^ ((1 : ℝ) / N)) ^ 2 = (d ^ 2) ^ ((1 : ℝ) / N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast d, ← Real.rpow_mul hd0.le, ← Real.rpow_mul hd0.le,
      mul_comm]
  rw [hq, hdetG, ← hpow]
  calc ∑ i, (B *ᵥ v) i ^ 2 ≤ ∑ _i : Fin N, (2 * d ^ ((1 : ℝ) / N)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq' (abs_le.mp (hc i)).1 (abs_le.mp (hc i)).2
    _ = 4 * N * (d ^ ((1 : ℝ) / N)) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]; ring

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.KsetMulVecMem
section
noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

def StLatFin : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ R : Finset (Fin I.n → I.E ⊗[I.F] Af I.F), (∀ r ∈ R, r ∈ I.Lf) ∧
    ∀ y ∈ I.Lf, ∃ r ∈ R, ∃ z ∈ I.Lf, y - r = (g : I.E ⊗[I.F] Af I.F) • z

theorem kset_mulVec_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hy : y ∈ I.Lf) : I.fmat k *ᵥ y ∈ I.Lf := (hk y).mp hy

theorem kset_inv (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  show ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_inv]
  exact Subgroup.inv_mem _ hk

theorem kset_mul (I : AutInst) {k t : I.Gf} (hk : k ∈ I.Kset) (ht : t ∈ I.Kset) : k * t ∈ I.Kset := by
  show ((k * t : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul]
  exact Subgroup.mul_mem _ hk ht

theorem stKFin_of (hL : StLatFin) : StKFin := by
  classical
  intro I g hg
  obtain ⟨R, hRLf, hR⟩ := hL I g hg
  choose! rep hrepR z hz hrepEq using hR
  let Ψ : I.Kset → (R → R) := fun k r =>
    ⟨rep (I.fmat k *ᵥ (r : Fin I.n → I.E ⊗[I.F] Af I.F)),
      hrepR _ (kset_mulVec_mem I k.2 (hRLf r r.2))⟩
  refine ⟨Finset.univ.image (fun φ : R → R =>
    if h : ∃ k, Ψ k = φ then ((h.choose : I.Kset) : I.Gf) else 1), ?_⟩
  intro k hk
  have hex : ∃ k', Ψ k' = Ψ ⟨k, hk⟩ := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : I.Kset, t = hex.choose := ⟨_, rfl⟩
  have htΨ : Ψ t = Ψ ⟨k, hk⟩ := by rw [htdef]; exact hex.choose_spec
  refine ⟨(t : I.Gf), Finset.mem_image.mpr ⟨Ψ ⟨k, hk⟩, Finset.mem_univ _, by rw [dite_eq_left hex, htdef]⟩,
    (t : I.Gf)⁻¹ * k, ?_, (mul_inv_cancel_left (t : I.Gf) k).symm⟩
  refine ⟨kset_mul I (kset_inv I t.2) hk, ?_⟩
  intro y hy
  have hrR : rep y ∈ R := hrepR y hy
  have hkr := hrepEq (I.fmat k *ᵥ rep y) (kset_mulVec_mem I hk (hRLf _ hrR))
  have htr := hrepEq (I.fmat t *ᵥ rep y) (kset_mulVec_mem I t.2 (hRLf _ hrR))
  have hrep_eq : rep (I.fmat k *ᵥ rep y) = rep (I.fmat t *ᵥ rep y) := by
    have h1 := congrFun htΨ ⟨rep y, hrR⟩
    exact (congrArg Subtype.val h1).symm
  have hfu : I.fmat ((t : I.Gf)⁻¹ * k) = I.fmat (t : I.Gf)⁻¹ * I.fmat k := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
  have hinv : I.fmat (t : I.Gf)⁻¹ * I.fmat t = 1 := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
  refine ⟨I.fmat (t : I.Gf)⁻¹ *ᵥ ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) +
      (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y)), ?_, ?_⟩
  · apply kset_mulVec_mem I (kset_inv I t.2)
    exact I.Lf.add_mem (I.Lf.sub_mem (hz _ (kset_mulVec_mem I hk (hRLf _ hrR)))
      (hz _ (kset_mulVec_mem I t.2 (hRLf _ hrR))))
      (I.Lf.sub_mem (kset_mulVec_mem I hk (hz y hy)) (kset_mulVec_mem I t.2 (hz y hy)))
  · have hyd : y = rep y + (g : I.E ⊗[I.F] Af I.F) • z y := by rw [← hrepEq y hy, add_sub_cancel]
    have hkrd : I.fmat k *ᵥ rep y = rep (I.fmat k *ᵥ rep y) +
        (g : I.E ⊗[I.F] Af I.F) • z (I.fmat k *ᵥ rep y) := by rw [← hkr, add_sub_cancel]
    have htrd : I.fmat t *ᵥ rep y = rep (I.fmat t *ᵥ rep y) +
        (g : I.E ⊗[I.F] Af I.F) • z (I.fmat t *ᵥ rep y) := by rw [← htr, add_sub_cancel]
    have hy' : y = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat t *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hdiff : I.fmat k *ᵥ y - I.fmat t *ᵥ y = (g : I.E ⊗[I.F] Af I.F) •
        ((z (I.fmat k *ᵥ rep y) - z (I.fmat t *ᵥ rep y)) + (I.fmat k *ᵥ z y - I.fmat t *ᵥ z y)) := by
      conv_lhs => rw [hyd, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hkrd, htrd, hrep_eq]
      rw [smul_add, smul_sub, smul_sub]
      abel
    rw [hfu, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    calc I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y) - y
        = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y) - I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat t *ᵥ y) := by
          rw [← hy']
      _ = I.fmat (t : I.Gf)⁻¹ *ᵥ (I.fmat k *ᵥ y - I.fmat t *ᵥ y) := (Matrix.mulVec_sub _ _ _).symm
      _ = _ := by rw [hdiff, Matrix.mulVec_smul]

theorem lat_mod_fin (I : AutInst) (g : ℕ) (hgpos : 0 < g) : ∃ R : Finset (Fin I.n → I.E), (∀ r ∈ R, r ∈ I.L) ∧
    ∀ l ∈ I.L, ∃ r ∈ R, ∃ l' ∈ I.L, l = r + (g : ℤ) • l' := by
  classical
  have hZfg : (I.L.restrictScalars ℤ).FG := I.L_fg.restrictScalars
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hZfg
  have hmem : ∀ v, v ∈ I.L ↔ ∃ c : Fin m → ℤ, ∑ i, c i • s i = v := by
    intro v
    rw [← Submodule.restrictScalars_mem ℤ, ← hs, Submodule.mem_span_range_iff_exists_fun]
  have hsL : ∀ i, s i ∈ I.L := fun i => (hmem (s i)).mpr ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hcomb : ∀ c : Fin m → ℤ, ∑ i, c i • s i ∈ I.L := fun c => (hmem _).mpr ⟨c, rfl⟩
  refine ⟨(Fintype.piFinset fun _ : Fin m => Finset.range g).image
    (fun c : Fin m → ℕ => ∑ i, ((c i : ℕ) : ℤ) • s i), ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
    exact hcomb _
  · intro l hl
    obtain ⟨c, rfl⟩ := (hmem l).mp hl
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
    refine ⟨∑ i, (((c i % g).toNat : ℕ) : ℤ) • s i, Finset.mem_image.mpr ⟨fun i => (c i % g).toNat, ?_, rfl⟩,
      ∑ i, (c i / g) • s i, hcomb _, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg (c i) hg0
      have h2 := Int.emod_lt_of_pos (c i) (by exact_mod_cast hgpos : (0 : ℤ) < g)
      omega
    · rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul, Int.toNat_of_nonneg (Int.emod_nonneg (c i) hg0), add_comm, Int.mul_ediv_add_emod]

theorem iv_add_smul (I : AutInst) (r l : Fin I.n → I.E) (g : ℕ) :
    iv I (r + (g : ℤ) • l) = iv I r + (g : I.E ⊗[I.F] Af I.F) • iv I l := by
  funext i
  simp [iv, zsmul_eq_mul]

theorem iv_mem (I : AutInst) {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem stLatFin_of (h : LDense) : StLatFin := by
  intro I g hg
  obtain ⟨R, hRL, hR⟩ := lat_mod_fin I g (by omega)
  classical
  refine ⟨R.image (iv I), ?_, ?_⟩
  · intro r hr
    obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr
    exact iv_mem I (hRL r0 hr0)
  · intro y hy
    obtain ⟨l, hl, y', hy', hyeq⟩ := h I g (by omega) y hy
    obtain ⟨r, hr, l', hl', hleq⟩ := hR l hl
    refine ⟨iv I r, Finset.mem_image_of_mem _ hr, iv I l' + y', I.Lf.add_mem (iv_mem I hl') hy', ?_⟩
    rw [hyeq, hleq, iv_add_smul, smul_add]
    abel

end PIW.AdelClassFin
end
end

