module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FormCLR
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem formC_LR (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (T T' : E) (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det)
    (Y W : Ix r → O) (hY : ∀ j, Y (Sum.inr j) = 0) (hW : ∀ j, W (Sum.inl j) = 0) :
    formC O cj (Z.map O.subtype) T T' Y W =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
        T * cG O cj Z T T' Y (Sum.inl (Fin.last r)) *
          cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
  set G := gramC cj (Z.map O.subtype) T T' with hGdef
  set c := cG O cj Z T T' Y with hcdef
  have hvm : Matrix.vecMul c G = fun j => (↑(Y j) : E) := by
    rw [hcdef]
    unfold cG
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
  have hrel : ∀ j, (↑(Y j) : E) = ∑ i, c i * G i j := by
    intro j
    rw [← congrFun hvm j]
    rfl
  rw [formC_of_rel O cj (Z.map O.subtype) T T' hG Y W c hrel, Fintype.sum_sum_type]
  simp only [hW, ZeroMemClass.coe_zero, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
  have hZ : ∀ j, ∑ b, (Z.map O.subtype) j b * c (Sum.inr b) =
      ↑(Y (Sum.inl j)) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0 := by
    intro j
    rw [hrel (Sum.inl j), Fintype.sum_sum_type]
    simp only [hGdef, gramC, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply,
      Matrix.of_apply]
    by_cases hj : j = Fin.last r
    · subst hj
      simp [mul_comm]
    · simp [hj, mul_comm]
  have hcR : (fun b => c (Sum.inr b)) = Matrix.mulVec (Z.map O.subtype)⁻¹
      (fun j => (↑(Y (Sum.inl j)) : E) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0) := by
    have hv : Matrix.mulVec (Z.map O.subtype) (fun b => c (Sum.inr b)) =
        fun j => (↑(Y (Sum.inl j)) : E) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0 := by
      funext j
      exact hZ j
    rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hcb : ∀ b, c (Sum.inr b) = Matrix.mulVec (Z.map O.subtype)⁻¹ (fun j => (↑(Y (Sum.inl j)) : E)) b +
      T * c (Sum.inl (Fin.last r)) * (Z.map O.subtype)⁻¹ b (Fin.last r) := by
    intro b
    have h := congrFun hcR b
    rw [h]
    simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hcb, bRaw, lamStarC, map_sum, map_mul, hcj]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem fwd_B (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
    (hcT : cj (t : E) = t) (hcT' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ : kap O Z₂ = kap O Z₁)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')
    (hθ : θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t')
    (γ : MbMod Z₁ →ₗ[O] MbMod Z₂) (γs : MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂))
    (hγ : ∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (γ m))
    (hγs : ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (γs m))
    (hl : ∀ m, lamLQ O Z₂ hu₂ (γ m) = lamLQ O Z₁ hu₁ m)
    (hls : ∀ m, lamSQ O cj hO Z₂ hu₂ (γs m) = lamSQ O cj hO Z₁ hu₁ m) :
    ∀ y y' y₂ y₂' : Fin (r + 1) → O, γ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂ →
      γs (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      bRaw O cj Z₂ y₂ y₂' - bRaw O cj Z₁ y y' ∈ O := by
  intro y y' y₂ y₂' h1 h2
  have e1 : θ (Submodule.Quotient.mk (Sum.elim y 0)) = Submodule.Quotient.mk (Sum.elim y₂ 0) := by
    rw [← iL_mk O cj hO Z₁ t t' y, hγ, h1, iL_mk]
  have e2 : θ (Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y')) =
      Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y₂') := by
    rw [← iR_mk O cj hO Z₁ t t' y', hγs, h2, iR_mk]
  have key := hθ.1 _ _ _ _ e1 e2
  have hly : lamC (Z₂.map O.subtype) (fun j => ((Sum.elim y₂ 0 : Ix r → O) (Sum.inl j) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((Sum.elim y 0 : Ix r → O) (Sum.inl j) : E)) := by
    have := hl (Submodule.Quotient.mk y)
    rw [h1, lamLQ_mk, lamLQ_mk] at this
    exact this
  have hly' : lamStarC cj (Z₂.map O.subtype) (fun j => ((Sum.elim y₂ 0 : Ix r → O) (Sum.inr j) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Sum.elim y 0 : Ix r → O) (Sum.inr j) : E)) := by
    simp [lamStarC]
  have hls' : lamStarC cj (Z₂.map O.subtype) (fun j => ((Sum.elim 0 y₂' : Ix r → O) (Sum.inr j) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Sum.elim 0 y' : Ix r → O) (Sum.inr j) : E)) := by
    have := hls (Submodule.Quotient.mk y')
    rw [h2, lamSQ_mk, lamSQ_mk] at this
    exact this
  obtain ⟨c1, -⟩ := cG_transfer O cj hcj Z₁ Z₂ hu₁ hu₂ t t' hG₁ hG₂ hκ _ _ hly hly'
  rw [formC_LR O cj hcj Z₂ hu₂ t t' hG₂ _ _ (fun j => rfl) (fun j => rfl),
    formC_LR O cj hcj Z₁ hu₁ t t' hG₁ _ _ (fun j => rfl) (fun j => rfl), c1, hls',
    add_sub_add_right_eq_sub] at key
  exact key

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.GsEquivSpec
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

theorem rel_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) :
    iL O cj hO Z t t' (bCls Z) = iR O cj hO Z t t' (t' • eCl (cjT O cj hO Z)) := by
  unfold bCls eCl
  rw [map_smul, iL, iR, Submodule.liftQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq, mem_relC_iff O cj hO Z t t']
  refine ⟨0, Pi.single (Fin.last r) 1, ?_, ?_⟩
  · funext j
    simp [elimL, elimR, Matrix.mulVec_single, Pi.single_apply]
  · funext j
    simp [elimL, elimR, Matrix.mulVec_zero, Pi.single_apply]

section Fwd

variable (t t' : O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')

omit hO in
theorem gam_fwd (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC O cj (Z₁.map O.subtype) t t',
    (θ.toLinearMap p.1, p.2) ∈ GamC O cj (Z₂.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ]
  exact ⟨p, hp, rfl⟩

omit hO in
theorem gam_bwd (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC O cj (Z₂.map O.subtype) t t',
    (θ.symm.toLinearMap p.1, p.2) ∈ GamC O cj (Z₁.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have e : θ.symm.toLinearMap (θ q.1) = q.1 := θ.symm_apply_apply q.1
  show (θ.symm.toLinearMap (θ q.1), q.2) ∈ _
  rw [e]
  exact hq

omit hO in
theorem gam_fwd' (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC' O cj (Z₁.map O.subtype) t t',
    (θ.toLinearMap p.1, p.2) ∈ GamC' O cj (Z₂.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ']
  exact ⟨p, hp, rfl⟩

omit hO in
theorem gam_bwd' (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC' O cj (Z₂.map O.subtype) t t',
    (θ.symm.toLinearMap p.1, p.2) ∈ GamC' O cj (Z₁.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ'] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have e : θ.symm.toLinearMap (θ q.1) = q.1 := θ.symm_apply_apply q.1
  show (θ.symm.toLinearMap (θ q.1), q.2) ∈ _
  rw [e]
  exact hq

def gsEquiv (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') :
    MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂) :=
  LinearEquiv.ofLinear (gsLin O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ))
    (gsLin O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ))
    (by
      apply LinearMap.ext; intro m
      have s1 := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ)
      have s2 := gsLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ)
      apply uniqR O cj hO Z₂ hu₂ t t' hη₂
      · rw [LinearMap.comp_apply, ← (s1 _).1, ← (s2 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s1 _).2, (s2 m).2, LinearMap.id_apply])
    (by
      apply LinearMap.ext; intro m
      have s1 := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ)
      have s2 := gsLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ)
      apply uniqR O cj hO Z₁ hu₁ t t' hη₁
      · rw [LinearMap.comp_apply, ← (s2 _).1, ← (s1 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s2 _).2, (s1 m).2, LinearMap.id_apply])

def gEquiv (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    MbMod Z₁ ≃ₗ[O] MbMod Z₂ :=
  LinearEquiv.ofLinear (gLin O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ'))
    (gLin O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ'))
    (by
      apply LinearMap.ext; intro m
      have s1 := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ')
      have s2 := gLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ')
      apply uniqL O cj hO Z₂ hu₂ t t' hη₂
      · rw [LinearMap.comp_apply, ← (s1 _).1, ← (s2 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s1 _).2, (s2 m).2, LinearMap.id_apply])
    (by
      apply LinearMap.ext; intro m
      have s1 := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ')
      have s2 := gLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ')
      apply uniqL O cj hO Z₁ hu₁ t t' hη₁
      · rw [LinearMap.comp_apply, ← (s2 _).1, ← (s1 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s2 _).2, (s1 m).2, LinearMap.id_apply])

theorem gsEquiv_spec (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') (m : MbMod (cjT O cj hO Z₁)) :
    θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m) ∧
      lamSQ O cj hO Z₂ hu₂ (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m) = lamSQ O cj hO Z₁ hu₁ m := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ) m

theorem gEquiv_spec (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') (m : MbMod Z₁) :
    θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m) ∧
      lamLQ O Z₂ hu₂ (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m) = lamLQ O Z₁ hu₁ m := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ') m

end Fwd

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

