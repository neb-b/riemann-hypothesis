module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionary
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDictHerm

open GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tensAt_compFin (v : Pl (F := F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : tensAt E v (compFin F E v z) = atPlace v 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a x =>
    show atPlace v (evFin F v a) ⊗ₜ[F] x = atPlace v 1 • (a ⊗ₜ[F] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, atPlace_mul_right, one_mul]

theorem at_atPlace (v : Pl (F := F)) (c : Fv F v) : At (evFin F v) (atPlace v c) := fun u hu => by
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

theorem at_tensAt (v : Pl (F := F)) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := fun u hu => by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
  | tmul a x =>
    rw [tensAt_tmul, TensorProduct.smul_tmul', at_atPlace v a u hu, TensorProduct.zero_tmul]

theorem eq_tensAt_of_at {v : Pl (F := F)} {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : z = tensAt E v (compFin F E v z) := by
  rw [tensAt_compFin]
  have h1 : (1 - atPlace v 1) • z = 0 := hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem piW_apply {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : piW τ z = splitProj τ (compFin F E v z) := rfl

theorem piW_inclR {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (AF F) x) = τ x := by
  show splitProj τ (evFin F v 1 ⊗ₜ[F] x) = τ x
  rw [map_one, splitProj_tmul, one_mul]

theorem piW_algebraMap {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a := by
  show splitProj τ (evFin F v a ⊗ₜ[F] 1) = evFin F v a
  rw [splitProj_tmul, map_one, mul_one]

theorem compFin_smul_inclR (v : Pl (F := F)) (a : AF F) (x : E) :
    compFin F E v (a • inclR (AF F) x) = evFin F v a ⊗ₜ[F] x := by
  show compFin F E v (a • ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem mem_latAt_iff {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧ (fun j => compFin F E v (z j)) ∈ latLoc F W.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc hav hy using 1
        funext j
        exact compFin_smul_inclR v a (y j)
    | zero => exact ⟨fun u _ => smul_zero u, by convert zero_mem (latLoc F W.L v) using 1; funext j; simp⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], ?_⟩
      convert add_mem hx.2 hy.2 using 1
      funext j; simp
    | neg x _ hx =>
      refine ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], ?_⟩
      convert neg_mem hx.2 using 1
      funext j; simp
  · rintro ⟨hz, hl⟩
    have e : z = fun j => tensAt E v (compFin F E v (z j)) := funext fun j => eq_tensAt_of_at (fun u hu => by
      have := congrFun (hz u hu) j
      simpa using this)
    rw [e]
    refine latLoc_induction (p := fun Y => (fun j => tensAt E v (Y j)) ∈ GlobalTheory.InertSph.latAt W v)
      (fun c hc x hx => ?_) (by convert zero_mem (GlobalTheory.InertSph.latAt W v) using 1; funext j; simp) (fun Y Y' hY hY' => ?_)
      (fun Y hY => ?_) hl
    · refine AddSubgroup.subset_closure ⟨atPlace v c, at_atPlace v c, by rwa [evFin_atPlace], x, hx, ?_⟩
      funext j
      rw [tensAt_tmul]
      show _ = atPlace v c • ((1 : AF F) ⊗ₜ[F] x j)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · convert add_mem hY hY' using 1
      funext j; simp
    · convert neg_mem hY using 1
      funext j; simp

theorem mem_latAt_iff_bases {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {d : ℕ} (W : Spc F E d) {v : Pl (F := F)}
    (τ : E →ₐ[F] Fv F v) {b₁ b₂ : GL (Fin d) (Fv F v)} (hb₁ : IsSplitBasis τ W.L b₁)
    (hb₂ : IsSplitBasis (τ.comp σ) W.L b₂) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW τ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW (τ.comp σ) (z j)) i ∈
          v.adicCompletionIntegers F) := by
  have key : ∀ {ρ : E →ₐ[F] Fv F v} {b : GL (Fin d) (Fv F v)}, IsSplitBasis ρ W.L b → ∀ u : Fin d → Fv F v,
      (∀ i, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ u) i ∈ v.adicCompletionIntegers F) ↔
        u ∈ splitLat ρ W.L := by
    intro ρ b hb u
    rw [hb, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_latAt_iff, mem_latLoc_iff_split τ h, key hb₁, key hb₂]
  exact Iff.rfl

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    (by intro a b c; ring : ∀ a b c : E, a * b * c = c * (b * a)) _ _ _

theorem split_dict_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv _
  have h := hB.cm
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  obtain ⟨τ, -⟩ := (existsUnique_splitPrime_eq h hPQ (HeightOneSpectrum.ext hP) (HeightOneSpectrum.ext hQ)).exists
  haveI := hV.lat
  obtain ⟨b₁, hb₁⟩ := exists_isSplitBasis τ V.L h
  have hdet : V.J.det ≠ 0 := by
    intro h0
    obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hV.sig u)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hdetT : V.Jᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hJ : IsHermND σ V.Jᵀ := ⟨fun i j => hV.herm j i, hdetT⟩
  have hL : IsSelfDualAt σ V.Jᵀ V.L v := by
    refine (SelfDual.forall_isSelfDualAt_iff hdetT hV.lat).2 (fun y => ?_) v
    rw [hV.dual y]
    refine forall₂_congr fun x _ => ?_
    rw [hE_transpose]
    exact ⟨fun hi => ⟨⟨_, hi⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c⟩
  have hb₂ := IsSplitBasis.dual h hJ hL hb₁
  refine ⟨piW τ, piW (τ.comp σ), b₁, dualConj 1 (splitGram hJ τ * b₁), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, 1, by simp, ?_⟩
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp]
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp_sigR h]
  · exact piW_algebraMap τ
  · exact piW_algebraMap _
  · intro z hz h1 h2
    have e : compFin F E v z = 0 := split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
    rw [eq_tensAt_of_at hz, e, map_zero]
  · intro x₁ x₂
    refine ⟨tensAt E v ((splitAlgEquiv h τ).symm (x₁, x₂)), at_tensAt v _, ?_, ?_⟩
    · rw [piW_apply, compFin_tensAt, splitProj_symm]
    · rw [piW_apply, compFin_tensAt, splitProj_comp_symm]
  · exact mem_latAt_iff_bases h V τ hb₁ hb₂
  · have eJ : (incM F V.J).map (piW τ) = V.J.map τ := by
      exact Matrix.ext fun i j => piW_inclR τ (V.J i j)
    have eT : V.J.map τ = ((splitGram hJ τ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ := by
      exact Matrix.ext fun i j => rfl
    have eG : V.J.map τ * (((splitGram hJ τ)⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ = 1 := by
      rw [eT, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
    rw [Matrix.map_one _ (by simp) (by simp), eJ, dualConj_one_val, mul_inv_rev, Units.val_mul, Matrix.transpose_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.J.map τ), eG, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.transpose_one]

end GlobalTheory.SplitDictHerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBlocksLeftInverseIsUnitDetSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b : GL (Fin d) (Fv F v))
  (g h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), h * g = 1 →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  ∃ G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F), G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) ∧ IsUnit G.det := by
  first | exact @GlobalTheory.integralBlocks_leftInverse_isUnit_det | exact GlobalTheory.integralBlocks_leftInverse_isUnit_det | (intros; apply GlobalTheory.integralBlocks_leftInverse_isUnit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfOrthogonalRealTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransOrth

theorem integral_eq_zero_of_translates : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D),
    IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) →
    ∀ w : SmT M, w ≠ 0 → (∀ h ∈ GinfC V, ∫ g in v.𝓕, F g * t w (g * h) ∂v.μ = 0) →
    ∀ w' : SmT M, ∫ g in v.𝓕, F g * t w' g ∂v.μ = 0 := by
  intro hP hV D θ hθ V S M J χ t ht v F hF hFb w hw hh w'
  classical
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  obtain ⟨hint, K, hK⟩ := _root_.GlobalTheory.PeriodBound.period_bound hP hV D θ hθ V S M J χ t ht v F hF hFb
  let ℓ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∫ g in v.𝓕, F g * t x g ∂v.μ
      map_add' := fun x y => by
        simp only [map_add (f := _), Pi.add_apply, mul_add]
        exact integral_add (hint x) (hint y)
      map_smul' := fun r x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext g
        ring }
  have hℓ : ∀ x, ℓ x = ∫ g in v.𝓕, F g * t x g ∂v.μ := fun x => rfl
  let L : MultilinearMap (RingHom.id ℂ) (fun τ => M.sm τ) ℂ := ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hL : ∀ u, L u = ℓ (PiTensorProduct.tprod ℂ u) := fun u => rfl
  have hx : w ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := fun τ => M.sm τ))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  obtain ⟨n, c, gg, hg⟩ := Submodule.mem_span_set'.1 hx
  choose vv hvv using fun j => (gg j).2
  have hw' : w = ∑ j, c j • PiTensorProduct.tprod ℂ (vv j) := by
    rw [← hg]; simp [hvv]
  obtain ⟨φ, hφ⟩ : ∃ φ : M.Vec, GlobalTheory.tprodInnerFun φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (GlobalTheory.eq_zero_of_tprodInnerFun w hcon)
  have hφ' : (∑ j, c j * ∏ τ, ⟪((φ τ : M.sm τ) : M.H τ), (vv j τ : M.H τ)⟫_ℂ) ≠ 0 := by
    rw [hw'] at hφ
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, GlobalTheory.tprodInnerFun_tprod, Submodule.coe_inner] using hφ
  have hinv : ∀ τ (g : Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ), ∀ x ∈ M.sm τ, Formalism.IndefR.SchurOrthogonalityAlt.piR M τ g x ∈ M.sm τ :=
    fun τ g x hx => GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem g) x hx
  have htv : ∀ (u : M.Vec) x, (PiTensorProduct.lift.symm t : MMap M) u x = t (PiTensorProduct.tprod ℂ u) x := by
    intro u x; simp [PiTensorProduct.lift_symm]
  have hT : ∀ gs : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ,
      ∑ j, c j * L (fun τ => ⟨Formalism.IndefR.SchurOrthogonalityAlt.piR M τ (gs τ) (vv j τ), hinv τ (gs τ) _ (vv j τ).2⟩) = 0 := by
    intro gs
    obtain ⟨P, hPm, hPe⟩ := _root_.GlobalTheory.SmoothTranslate.translate θ M J χ (PiTensorProduct.lift.symm t) ((mem_multT θ M J χ t).1 ht) gs
    have h0 := hh P hPm
    have e : ∀ x, F x * t w (x * P) = ∑ j, c j * (F x * t (PiTensorProduct.tprod ℂ
        (fun τ => ⟨Formalism.IndefR.SchurOrthogonalityAlt.piR M τ (gs τ) (vv j τ), hinv τ (gs τ) _ (vv j τ).2⟩)) x) := by
      intro x
      rw [hw']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 := hPe (vv j) x
      rw [htv, htv] at e1
      simp only [Formalism.IndefR.SchurOrthogonalityAlt.piR_apply]
      rw [← e1]
      ring
    simp_rw [e] at h0
    rw [integral_finsetSum _ (fun j _ => (hint _).const_mul (c j))] at h0
    simp_rw [integral_const_mul] at h0
    exact h0
  have hB := GlobalTheory.T.multilinear_zero_of_kills_translates_tensor D.what₂.Tau (fun τ => M.H τ) (fun τ => Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ) (fun τ => Formalism.IndefR.SchurOrthogonalityAlt.piR M τ) (Formalism.IndefR.SchurOrthogonalityAlt.piR_norm M)
    (Formalism.IndefR.SchurOrthogonalityAlt.commutant_scalar M) (fun τ => M.sm τ) (Formalism.IndefR.SchurOrthogonalityAlt.sm_dense M) hinv L K
    (fun u => by rw [hL, hℓ]; exact hK u) n c vv hT (fun τ => (φ τ : M.H τ))
  have hL0 : ∀ u, L u = 0 := fun u => (mul_eq_zero.1 (hB u)).resolve_left hφ'
  have hℓ0 : ℓ w' = 0 := by
    induction w' using PiTensorProduct.induction_on with
    | smul_tprod r u => rw [map_smul, ← hL, hL0, smul_zero]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_zero]
  rw [← hℓ]; exact hℓ0

end GlobalTheory.TransOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteAdeleSupportedDivPrimeToPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFiniteAdele_supported_div_prime_to_place : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (d : 𝓞 D.host.F), d ∉ v.asIdeal → ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) (d : D.host.F) := by
  first | exact @GlobalTheory.intAf_div_prime_to_place' | exact GlobalTheory.intAf_div_prime_to_place' | (intros; apply GlobalTheory.intAf_div_prime_to_place' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignature
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.RankZeroFrames

open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_model_int (hD : Dw.p + Dw.q = 0) (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ Y : Model Xo c (Int.castRingHom c.F), PushInvertible Y.t.G Y.t.PP.L := by
  obtain ⟨h₁, h₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  let k := spMap (IntermediateField.inclusion c.le).toRingHom
  let β := Int.castRingHom c.F
  have hk : IsIso (pullback.snd Xo.s k) := inferInstance
  let j : Xo.XF c ⟶ pullback (𝟙 (Sp ℤ)) (spMap β) := pullback.snd Xo.s k ≫ inv (pullback.snd _ _)
  have hj : IsIso j := inferInstance
  have hs : Function.Surjective j := (inferInstance : Surjective j).1
  refine ⟨{ X := Sp ℤ, s := 𝟙 _, normal := ZJ.isNormalScheme_sp ℤ, proj := Inhab.isProjOver_id ℤ
            flat := inferInstance, jQ := j, jQ_over := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (IsIso.inv_hom_id _)).trans (Category.comp_id _))
            jQ_open := inferInstance
            jQ_dense := hs.denseRange, t := Inhab.zeroTriple H _, oF := zeroObj hD l _
            m0 := (nonempty_objMap (isIso_zeroTriple _) h₂ _).some
            m := (nonempty_sabMap (isIso_zeroTriple _) (isIso_zeroTriple _) _).some
            ab_gen := by
              rw [hs.range_eq, Inhab.abLocus_eq_univ _ (Inhab.isProper_zeroTriple _), Set.preimage_univ] }, ?_⟩
  exact PushInv.pushInvertible_any GlobalTheory.allSixLaws.2.1.secBaseChangeAny GlobalTheory.allSixLaws.1.globalSectionsRank _
    (Out.Inh.zeroPolAV (Sp ℤ))

theorem intFrExt_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.p + Dw.q = 0 → IntFrExt Xo c := by
  intro E _ _ _ H Dw l Xo c hD T io hfin x hx
  have hL := GlobalTheory.lawsFieldsSeparately
  have hB : Out.SecBaseChangeSt := hL.2.1
  have hT : Out.SecTwistSt := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Y, hPI⟩ := exists_model_int hD Xo c
  have hIF := GlobalTheory.intFrames_of_laws hB hT E H Dw l Xo c
  let _ := io.toAlgebra
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF T io Y hPI (Int.castRingHom T.V) (RingHom.ext_int _ _) y₀
  refine ⟨T, RingHom.id _, 1, one_pos, fun z => by simp, hfin, y, ?_⟩
  have h1 : y.1.x = y₀.x := hbor.1
  have h2 : spMap (RingHom.id T.Fr) = 𝟙 _ := Spec.map_id _
  show y.1.x = _
  rw [h2, Category.id_comp, h1, h0]

end GlobalTheory.RankZeroFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLocalBasisConjugatesOfKeepsLatticeAtPlacStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_localBasisConjugates_of_keepsLatticeAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) → (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ A : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.IntKeepConj.conj_integral | exact GlobalTheory.IntKeepConj.conj_integral | (intros; apply GlobalTheory.IntKeepConj.conj_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsProperModelOfExtendsFibreIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem isProper_of_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' F N ⟨ψ, _, hψ, hc⟩ hN hpos hG
  have hU : IsAbelianScheme Xo.univ.t.G :=
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩
  have hA : IsAbelianScheme (Fib Xo x') := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback x' _ hU
  have hB : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hG, G.semi.geomConnected⟩
  have hch : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hu : IsUnit (N : Γ(Sp T.Fr, ⊤)) := by
    have h0 : IsUnit (N : T.Fr) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')
    have := h0.map (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, -, hs⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ (Fib Xo x') N hA hu
  have hl : f'.left ≫ f.left = (𝟙 (Fib Xo x') ^ N).left := congrArg (·.left) hN
  have hf : Function.Surjective f.left := by
    intro y
    obtain ⟨z, hz⟩ := hs.1 y
    refine ⟨f'.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hz]
  have p₁ : IsPullback m₁.φ t.G.hom Xo.univ.t.G.hom x := m₁.cart.1
  have q₁ : IsPullback n₁.φ t'.G.hom Xo.univ.t.G.hom x' := n₁.cart.1
  have q₂ : IsPullback n₂.φ t'.G.hom G'.G.hom (spMap (algebraMap T.V T.Fr)) := n₂.cart.1
  have hsq := hc p₁.isoPullback.hom q₁.isoPullback.hom (by simp) (by simp) (by simp) (by simp)
  have hψs : Function.Surjective ψ.left := by
    intro y
    obtain ⟨z, hz⟩ := hf (q₁.isoPullback.hom y)
    obtain ⟨w, rfl⟩ := (inferInstance : Surjective p₁.isoPullback.hom).1 z
    refine ⟨w, q₁.isoPullback.hom.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    exact hz
  refine (GlobalTheory.isAbelianScheme_of_generically_surjective T.V T.Fr G.G G'.G hB G'.semi F ?_).proper
  rintro y ⟨s, hs⟩
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback q₂ y s hs.symm
  obtain ⟨w, rfl⟩ := hψs z
  refine ⟨m₂.φ w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hψ, Scheme.Hom.comp_apply, hz]

end GlobalTheory.HkIntegral
end

