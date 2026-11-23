module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0019
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0022
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBoxSec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}
variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k (hL : _root_.GlobalTheory.ThK.Dbl.FinLevel_k) (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have hmem := n2 uᵀ (tr hu) f hf
    rwa [ht] at hmem
end GlobalTheory.ThK.Dbl.Box
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtInt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.WeilM Hgt
theorem hgtEx_of_k (hK : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.HgtEx_k := fun F E _ _ _ _ _ σ B n Y r s hB hY =>
  _root_.GlobalTheory.ThK.Dbl.Hgt.hgtEx_core_k hB hY (hK F E σ B n Y r s hB hY _ (isStab2_stab2 B))
theorem hgtInt_of_k (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.HgtInt_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K a e hK ha he μ hμ
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
  have : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  have cK := hC F E σ B n Y r s hB hY K hK
  obtain ⟨⟨K', a', hK', ha', ca, a0⟩, e', ce, he'⟩ := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k hC F E σ B n Y r s hB hY
  obtain rfl : K = K' := Subgroup.ext fun k => (hK k).trans (hK' k).symm
  obtain rfl : a = a' := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha'.val p t hp k hk]
  obtain rfl : e = e' := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he x.1 x.2).trans (he' x.1 x.2).symm))
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  let T : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₁
  let T' : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₂
  have cm : Continuous fun k : G2 σ Y => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) :=
    ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_mul continuous_const
  have cT : Continuous T := cm.matrix_submatrix _ _
  have cT' : Continuous T' := cm.matrix_submatrix _ _
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
  let c := (Module.Free.chooseBasis (AF F) (Matrix (Fin n) (Fin n) (AE F E))).equivFun
  obtain ⟨R, C, b, h1, h2, h3, h4⟩ := count_ad (E := E) hB.cm.1 c (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap) (UG (cA σ) (incM F Y.J))
    (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const)
    ((cK.image ((cc.comp cT'.matrix_det).smul (cT.matrix_mul cT'.matrix_adjugate))).union
      (cK.image ((cc.comp cT.matrix_det).smul (cT'.matrix_mul cT.matrix_adjugate))))
    (cK.image (continuous_norm_tens.comp cT.matrix_det)) μ
  have key : ∀ g : UA σ Y.J, ∃ k ∈ K, ∃ t : GL (Fin n) (AE F E), a (e (1, g)) = absE F E (Matrix.GeneralLinearGroup.det t) ∧
      T k = t.1 ∧ T' k = mat g⁻¹ * t.1 := fun g => by
    obtain ⟨p, t, hp, k, hk, h⟩ := ha.iwa (e (1, g))
    have e1 : k⁻¹ = e (1⁻¹, g⁻¹) * p := by rw [← Prod.inv_mk, map_inv, h]; group
    have hp' : (mat2 p * diagCols (E := AE F E) (Fin n)) = (diagCols (E := AE F E) (Fin n) * t.1) := hp
    have e2 : (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) = Matrix.fromRows t.1 (mat g⁻¹ * t.1) := by
      rw [e1, show mat2 (e (1⁻¹, g⁻¹) * p) = mat2 (e (1⁻¹, g⁻¹)) * mat2 p from rfl, Matrix.mul_assoc, hp', he, inv_one,
        show mat (1 : UA σ Y.J) = 1 from rfl, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
      simp
    exact ⟨k, hk, t, by rw [h, ha.val p t hp k hk], congrArg Matrix.toRows₁ e2, congrArg Matrix.toRows₂ e2⟩
  refine integrable_of_count μ (ca.comp (ce.comp (Continuous.prodMk_right 1))).measurable (fun g => a0 _) (R := R) h1 (fun g => ?_)
    h2 b fun j => (measure_mono fun g hg => ?_).trans (h4 j)
  · obtain ⟨k, hk, t, e1, e2, -⟩ := key g
    exact e1.trans_le (h3 _ ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩)
  · obtain ⟨k, hk, t, e1, e2, e3⟩ := key g
    have hd : (mat g⁻¹).det * (cA σ).toRingHom (mat g⁻¹).det = 1 := by
      have h := congrArg Matrix.det (show (mat g⁻¹)ᵀ * incM F Y.J * (mat g⁻¹).map (cA σ) = incM F Y.J from (g⁻¹).2)
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show ((mat g⁻¹).map (cA σ)).det = (cA σ).toRingHom (mat g⁻¹).det from ((cA σ).toRingHom.map_det _).symm] at h
      refine (isUnit_det_JR (R := AF F) (det_ne hY)).mul_left_cancel ?_
      change (incM F Y.J).det * _ = (incM F Y.J).det * _
      linear_combination h
    obtain ⟨q1, q2⟩ := Hgt.graph_alg (cA σ).toRingHom (g := mat g) g.1.mul_inv e3 hd
    have q : ∀ X : Matrix (Fin n) (Fin n) (AE F E), Algebra.norm (AF F) t.1.det • X = (t.1.det * (cA σ).toRingHom t.1.det) • X :=
      fun X => by rw [← algebraMap_smul (AE F E), algebraMap_norm_eq hB.cm, ← cA_eq]; rfl
    refine ⟨Matrix.GeneralLinearGroup.det t, ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩, e1 ▸ hg,
      .inl ⟨k, hk, Eq.symm ((q _).trans (q1.trans ?_))⟩, .inr ⟨k, hk, Eq.symm ((q _).trans (q2.trans ?_))⟩⟩ <;> rw [← e2] <;> rfl
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseSWStd
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ : Type} [Fintype κ] {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {B : Base F E} {ψ : AddChar (AF F) ℂ}
variable {dd} {χ : Chr F E} {om S l}
theorem sw_transl_k (h1 : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) {r s r' s'} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hm : 1 ≤ m) (hn : 1 ≤ n) (h0 : min r s = 0)
    (hA : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') (hχ : IsHecke F E χ)
    (hc : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) {dd om S l}
    (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l) {K a} (hK : IsStab2 B K) (ha : IsHgt K a)
    {μ : Measure (UA σ A.J)} {D : Set (UA σ A.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ A.J) D μ)
    {Φ} (hΦ : Φ ∈ kfin om K) : EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
      fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  obtain ⟨N, _, n0, n1, n2⟩ := hΦ
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r' s' hB (hA.symm.imp And.right And.right) K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have mul : ∀ x y Ψ, om x (om y Ψ) = om (x * y) Ψ := fun x y Ψ => by rw [map_mul, Module.End.mul_apply]
  intro x
  obtain ⟨e, e1, ⟨t₁, e2⟩, e3, e4⟩ := h1 F E σ B m n A Y r s r' s' hB hm hn h0 hA χ hχ hc _ dd om S l h b K₀ _ hb hK₀ ha₀ μ D hμ hD
    (om p⁻¹ Φ) (h.weil.2.1.pres _ _ (n0 n1)) (Submodule.finiteDimensional_of_le (S₂ := N.map (om p⁻¹)) (Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, n2 _ (hk' k k.2) Φ n1, by simp only [mul]; congr 2; group⟩))) (x * p)
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) :=
    (differentiable_id.const_sub _).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine ⟨fun z => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) * e z, fun z hz => (dc.analyticAt z).meromorphicAt.mul (e1 z hz),
    ⟨t₁, fun z hz => ?_⟩, (dc.analyticAt _).mul e3, ?_⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mpr ((e2 z hz).mul_left ((d : ℂ) ^ (((m : ℂ) - n) / 2 - z)))
    simp only [eisTerm, flat, mul, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · simp only [e4, sub_self, Complex.cpow_zero, one_mul, ← dbl_comm hB.std h hp.inv _ (n0 n1), mul, mul_inv_cancel_right]
theorem _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) (hL : _root_.GlobalTheory.ThK.Dbl.FinLevel_k) (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) :
    _root_.GlobalTheory.ThK.Dbl.SiegelWeilAniso_k := by
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hc dd om S l hd h K a hK ha Φ₁ p1 Φ₂ p2
    refine _root_.GlobalTheory.ThK.Dbl.Box.sw_transl_k h1 h2 hB hm hn h0 (.inl ⟨hA, hY⟩) hχ hc h hK ha hM.haar hM.dom
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
    · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf
  · intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd' hX hW h0 hM χ hχ hc dd om S l ⟨d', ht, hd⟩ h K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
    have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
      rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
    refine _root_.GlobalTheory.ThK.Dbl.Box.sw_transl_k h1 h2 hB hd' hn h0 (.inr ⟨hW, hX⟩) hχ hc h hK ha hμ hD
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · have er : Rel B.emb ε X.θ W.θ uᵀ u'ᵀ := fun w => by
        simpa [Matrix.transpose_map, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose (e w)
      have he := hε uᵀ u'ᵀ (tr hu) (tr hu') er _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
      have ht1 : d'.e u = M.co.e uᵀ := by simpa using ht uᵀ
      have ht2 : d'.e u' = M.co.e u'ᵀ := by simpa using ht u'ᵀ
      rw [ht1, ht2]
      change dop (aOf M u'ᵀ) (lOf M u'ᵀ) f = Complex.I • dop (aOf M uᵀ) (lOf M uᵀ) f
      exact he
    · rw [actsD_unique' M hB.std hu e]
      have := n2 uᵀ (tr hu) f hf
      rwa [ht] at this
end GlobalTheory.ThK.Dbl.Box
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowModel
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem modelEx_k : _root_.PositivityTheory.ThKG.Tow.ModelEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := _root_.Tw.RatDarboux.exists_rational_darboux_of_isGood_k B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1 (by simpa using hX.herm) (det_herm hX)
  have hS := _root_.Tw.VacIndic.eventually_isVac_indicator_k B hB X W r s r' s' hX hW co hco
  have hA := _root_.Tw.VacAny.exists_isVac_any_darboux_k B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv
end PositivityTheory.ThKG.Tow
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilPairGlobalCharacterLift
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix ComplexConjugate Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace PositivityTheory.ThKW.DblSchur
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.DblTargetDelta PositivityTheory.ThKW.Dbl GlobalTheory.ThetaSchurF
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
end PositivityTheory.ThKW.DblSchur
open PositivityTheory.ThKW.DblSchur PositivityTheory.ThKW.Dbl Formalism.IndefR.DatumF MeasureTheory GlobalTheory.DblTargetDelta in
theorem PositivityTheory.ThKW.weil_pair_global_character_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd e
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hth := fun w f hf => _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ w f hf
  obtain ⟨μ, 𝓕, μ₂, 𝓕₂, hμ, h𝓕, hμ₂, h𝓕₂, hprod⟩ := exists_prod_domain F E nS nT
  let T := {f // IsThetaFunOF σ JS JT ξ₀ B.ψ f}
  have hδ : ∀ f₁ f₂ g₁ g₂ : WOF F E nS nT → ℂ, ∫ x in 𝓕₂, deltaT f₁ f₂ x * star (deltaT g₁ g₂ x) ∂μ₂ =
      (∫ x in 𝓕, f₁ x * star (g₁ x) ∂μ) * ∫ x in 𝓕, conj (f₂ (-x)) * star (conj (g₂ (-x))) ∂μ := fun f₁ f₂ g₁ g₂ => by
    rw [← hprod]
    congr 1
    funext x
    simp only [deltaT_apply, star_mul]
    ring
  obtain ⟨c, hc, H⟩ := abstract hψ (_root_.GlobalTheory.SymplSkew.symplOF_swap F E σ hinv _ _ JS _ hS hT' ξ₀ hσξ)
    (_root_.GlobalTheory.T.rational_lattice_self_dual F E σ B hB _ _ JS _ hS hT' ξ₀ hξ)
    (fun p : T × T => ωd (1, hd) (deltaT p.1.1 p.2.1)) (fun p => deltaT (ω (1, h) p.1.1) p.2.1)
    (fun p => hωd.om_pres _ _ (theta_delta hψ.2.1 p.1.2 p.2.2))
    (fun p => theta_delta hψ.2.1 (hω.om_pres _ _ p.1.2) p.2.2)
    (fun w p => by
      have e1 : actOF σ JS JT 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) = topR w := by
        rw [← GlobalTheory.WeilPartsF.actOF_mul, mul_one, mul_inv_cancel, act_one_left, show mtF σ JT 1 = 1 from rfl, Matrix.one_mul]
      have e2 : actOF σ JS _ 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) = w := by
        rw [act_glue h hd e, e1]
        exact tb_ext (top_glue _ _) (bot_glue _ _)
      refine ⟨(⟨_, hth (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2⟩, ⟨_, hth (-botR w) _ p.2.2⟩), ?_, ?_⟩
      · have := hωd.om_heis 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) _ (theta_delta hψ.2.1 p.1.2 p.2.2)
        rw [e2, heis_delta hψ.2.1, top_glue, bot_glue] at this
        exact this.symm
      · have := hω.om_heis 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2
        rw [e1] at this
        show _ = deltaT (ω (1, h) _) _
        rw [this, heis_delta hψ.2.1])
    μ₂ 𝓕₂ hμ₂ h𝓕₂ (fun p q => by
      rw [GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ₂ 𝓕₂ hμ₂ h𝓕₂ (ωd (1, hd)) (hωd.om_pres _) (hωd.om_unit μ₂ 𝓕₂ hμ₂ h𝓕₂ _) _ _
        (theta_delta hψ.2.1 p.1.2 p.2.2) (theta_delta hψ.2.1 q.1.2 q.2.2), hδ, hδ,
        GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 (ω (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _ p.1.2 q.1.2])
  exact ⟨c, hc, fun f₁ f₂ h₁ h₂ => H (⟨f₁, h₁⟩, ⟨f₂, h₂⟩)⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepMemPolynomialFockOfArchimedean
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.weilRep_mem_polynomialFock_of_archimedean :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ Φ ∈ PolData B M, om (g, h) Φ ∈ PolData B M := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hp g hg h hh Φ hΦ
  obtain ⟨T, hT, hP⟩ := _root_.PositivityTheory.ThKF.A.archOp_k F E σ B n d X W M χX χW om n 0 d 0 hp g hg h hh
  have kg : g ∈ KInf σ X B.emb := ⟨hg, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.herm.sig w) (hp.herm.cartan w)]; exact Commute.one_right _⟩
  have kh : h ∈ KInf σ W B.emb := ⟨hh, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.skew.sig w) (hp.skew.cartan w)]; exact Commute.one_right _⟩
  refine Submodule.span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun x y _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c x _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, f1, φ, f2, f3, rfl⟩
  obtain ⟨ξ, hξ, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good φ f2 f3
  rw [e f, hT.1 f ξ hξ, ← e (T f)]
  exact Submodule.subset_span ⟨T f, hP kg kh f f1, φ, f2, f3, rfl⟩
end
end

