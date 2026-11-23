module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTensorTypesIntertwinerMatrixPolynomials
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHoweJoint

theorem exists_bilinear {G G' H H' P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [AddCommGroup P] [Module ℂ P] (S : Set G) (S' : Set G') (τ : G → H →ₗ[ℂ] H) (τ' : G' → H' →ₗ[ℂ] H')
    (a : G → P →ₗ[ℂ] P) (b : G' → P →ₗ[ℂ] P) (hab : ∀ g h x, a g (b h x) = b h (a g x))
    (hirr : ∀ U : Submodule ℂ H, (∀ g ∈ S, ∀ v ∈ U, τ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hirr' : ∀ U : Submodule ℂ H', (∀ g ∈ S', ∀ v ∈ U, τ' g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (L : H →ₗ[ℂ] P) (L' : H' →ₗ[ℂ] P) (hL : ∀ g ∈ S, ∀ u, L (τ g u) = a g (L u))
    (hL' : ∀ h ∈ S', ∀ u, L' (τ' h u) = b h (L' u)) (v₀ : H) (v₀' : H') (h0 : L v₀ = L' v₀')
    (hne : L v₀ ≠ 0) :
    ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] P, Ψ ≠ 0 ∧ ∀ h ∈ S', ∀ g ∈ S, ∀ v' v, Ψ (τ' h v') (τ g v) = b h (a g (Ψ v' v)) := by
  let 𝓗 : Submodule ℂ (H →ₗ[ℂ] P) :=
    { carrier := {A | ∀ g ∈ S, ∀ u, A (τ g u) = a g (A u)}
      add_mem' := fun {A B} hA hB g hg u => by
        simp only [LinearMap.add_apply, map_add (f := _), hA g hg u, hB g hg u]
      zero_mem' := fun g _ u => by simp
      smul_mem' := fun c A hA g hg u => by
        simp only [LinearMap.smul_apply, map_smul, hA g hg u] }
  have hv₀ : v₀ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hv₀' : v₀' ≠ 0 := fun h => hne (by rw [h0, h, map_zero])
  let ev : 𝓗 →ₗ[ℂ] P := (LinearMap.applyₗ v₀).comp 𝓗.subtype
  have hev : ∀ A : 𝓗, ev A = (A : H →ₗ[ℂ] P) v₀ := fun _ => rfl
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro A hA
    rcases hirr (LinearMap.ker (A : H →ₗ[ℂ] P)) (fun g hg v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [A.2 g hg v, hv, map_zero]) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀ hA) hv₀
    · exact Subtype.ext (LinearMap.ker_eq_top.1 h)
  have hstab : ∀ h, ∀ A ∈ 𝓗, (b h).comp A ∈ 𝓗 := fun h A hA g hg u => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hA g hg u, hab]
  have hrange : ∀ v', L' v' ∈ LinearMap.range ev := by
    rcases hirr' ((LinearMap.range ev).comap L') (fun h hh v hv => by
      obtain ⟨A, hA⟩ := hv
      refine ⟨⟨(b h).comp A, hstab h _ A.2⟩, ?_⟩
      rw [hL' h hh, ← hA]
      rfl) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀' ⟨⟨L, hL⟩, h0⟩) hv₀'
    · intro v'
      have : v' ∈ (LinearMap.range ev).comap L' := h ▸ Submodule.mem_top
      exact this
  let Φ : H' →ₗ[ℂ] 𝓗 :=
    (LinearEquiv.ofInjective ev hinj).symm.toLinearMap.comp (L'.codRestrict _ hrange)
  have hΦ : ∀ v', ev (Φ v') = L' v' := fun v' =>
    congrArg Subtype.val ((LinearEquiv.ofInjective ev hinj).apply_symm_apply (L'.codRestrict _ hrange v'))
  refine ⟨𝓗.subtype.comp Φ, fun h => hne ?_, fun h hh g hg v' v => ?_⟩
  · rw [h0, ← hΦ, hev]
    exact congrArg (fun f : H' →ₗ[ℂ] H →ₗ[ℂ] P => f v₀' v₀) h
  · have key : Φ (τ' h v') = ⟨(b h).comp (Φ v'), hstab h _ (Φ v').2⟩ := by
      apply hinj
      rw [hΦ, hL' h hh, ← hΦ v']
      rfl
    show (Φ (τ' h v') : H →ₗ[ℂ] P) (τ g v) = b h (a g ((Φ v' : H →ₗ[ℂ] P) v))
    rw [key]
    show b h ((Φ v' : H →ₗ[ℂ] P) (τ g v)) = _
    rw [(Φ v').2 g hg v]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔
    gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

open MvPolynomial in
theorem subst2_one_right {N n : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = ReciprocityTheory.PGsh.rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = ReciprocityTheory.PGsh.rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

open MvPolynomial in
theorem subst2_one_left {N n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin N) ℂ) :
    subst2 1 g (rename Prod.swap P) = rename Prod.swap (ReciprocityTheory.PGsh.rowSubst g P) := by
  have key : (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).comp (rename Prod.swap) =
      (rename Prod.swap).comp (ReciprocityTheory.PGsh.rowSubst (ι := Fin N) g) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, ReciprocityTheory.PGsh.rowSubst, aeval_X,
      Finset.sum_eq_single p.2]
    · have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) p.2 p.swap.1 = 1 := Matrix.one_apply_eq _
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, h1]
    · intro l _ hl
      have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) l p.swap.1 = 0 := Matrix.one_apply_ne hl
      simp [h1]
    · simp
  exact congrArg (fun f => f P) key

theorem isUpperUnitri_one (k : ℕ) : ReciprocityTheory.PGsh.IsUpperUnitri (1 : Matrix (Fin k) (Fin k) ℂ) :=
  ⟨fun _ => Matrix.one_apply_eq _, fun _ _ h => Matrix.one_apply_ne h.ne'⟩


open MvPolynomial in
theorem exists_joint_intertwiner : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (τ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → IsURepOn (UJset (allPos n)) τ → IsKTypeOf (allPos n) τ (fun a => (ν (Fin.castLE hn a) : ℝ)) ⊤ → IsURepOn (UJset (allPos N)) τ' → IsKTypeOf (allPos N) τ' (fun b => (ν b : ℝ)) ⊤ → ∃ Ψ : H' →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ, Ψ ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ v' v, Ψ (τ' h v') (τ g v) = subst2 h g (Ψ v' v) := by
  intro N n hn ν H _ _ _ τ H' _ _ _ τ' hν hz hτ hK hτ' hK'
  obtain ⟨Δ, hΔ, hU, hD⟩ := GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct N n hn ν hν hz
  have hsw : ∀ Q : MvPolynomial (Fin N × Fin n) ℂ,
      rename (Prod.swap : Fin n × Fin N → _) (rename Prod.swap Q) = Q := fun Q => by
    rw [rename_rename]; simp
  have hinj : Function.Injective
      (rename (Prod.swap : Fin n × Fin N → Fin N × Fin n) : MvPolynomial _ ℂ → MvPolynomial _ ℂ) :=
    rename_injective _ Prod.swap_injective
  obtain ⟨L', hL', v₀', hv'⟩ := _root_.GlobalTheory.HighestPolynomial.exists_intertwiner N (Fin n) ν H' τ' Δ hτ' hK' hΔ
    (fun g hg => by rw [← subst2_one_right, hU g 1 hg (isUpperUnitri_one n)])
    (fun d => by
      have := hD d (fun _ => 1)
      rw [Matrix.diagonal_one, subst2_one_right] at this
      simpa using this)
  obtain ⟨L, hL, v₀, hv⟩ := _root_.GlobalTheory.HighestPolynomial.exists_intertwiner n (Fin N) (fun a => ν (Fin.castLE hn a)) H τ
    (rename Prod.swap Δ) hτ hK
    (fun h => hΔ (by rw [← hsw Δ, h, map_zero]))
    (fun g hg => hinj (by rw [← subst2_one_left, hsw, hU 1 g (isUpperUnitri_one N) hg]))
    (fun e => hinj (by
      have := hD (fun _ => 1) e
      rw [Matrix.diagonal_one] at this
      rw [← subst2_one_left, map_smul, hsw, this]
      simp))
  have hLv : ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) v₀ = Δ := by
    show rename Prod.swap (L v₀) = Δ
    rw [hv, hsw]
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_bilinear (UJset (allPos n)) (UJset (allPos N))
    (fun g => (τ g).toLinearMap) (fun h => (τ' h).toLinearMap)
    (fun g => (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g).toLinearMap)
    (fun h => (subst2 h (1 : Matrix (Fin n) (Fin n) ℂ)).toLinearMap)
    (fun g h x => by simp [subst2_mul])
    (fun U hS => hK.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    (fun U hS => hK'.2.2.1 U le_top fun g hg => hS g ((mem_K_iff g).1 hg))
    ((rename (Prod.swap : Fin n × Fin N → Fin N × Fin n)).toLinearMap.comp L) L'
    (fun g hg u => by
      show rename Prod.swap (L (τ g u)) = subst2 1 g (rename Prod.swap (L u))
      rw [hL g hg u, subst2_one_left])
    (fun h hh u => by
      show L' (τ' h u) = subst2 h 1 (L' u)
      rw [hL' h hh u, subst2_one_right])
    v₀ v₀' (hLv.trans hv'.symm) (by rw [hLv]; exact hΔ)
  refine ⟨Ψ, hΨ, fun h hh g hg v' v => ?_⟩
  have := hΨe h hh g hg v' v
  simpa [subst2_mul] using this

end GlobalTheory.CompactHoweJoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionCommuteUnitaryRepSmooth
section
open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmVec Matrix

noncomputable section
namespace GlobalTheory.SmVecGelfComm

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def RealLin (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep π (X + Y) w = dRep π X w + dRep π Y w) ∧
    ∀ (a : ℝ), ∀ X ∈ lieG G, dRep π (a • X) w = (a : ℂ) • dRep π X w

theorem lie_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h : Xᴴ * G + G * X = 0 := hX
  show _ + _ = 0
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, h, smul_zero]

theorem conjG_add (Z W : Matrix (Fin n) (Fin n) ℂ) : conjG G (Z + W) = conjG G Z + conjG G W := by
  simp only [conjG, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem conjG_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (c • Z) = star c • conjG G Z := by
  simp only [conjG, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem dRepC_add_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π (Z + W) w = dRepC G π Z w + dRepC G π W w := by
  have e1 : (1 / 2 : ℂ) • (Z + W + conjG G (Z + W)) =
      (1 / 2 : ℂ) • (Z + conjG G Z) + (1 / 2 : ℂ) • (W + conjG G W) := by rw [conjG_add]; module
  have e2 : (1 / (2 * Complex.I)) • (Z + W - conjG G (Z + W)) =
      (1 / (2 * Complex.I)) • (Z - conjG G Z) + (1 / (2 * Complex.I)) • (W - conjG G W) := by
    rw [conjG_add]; module
  unfold dRepC
  rw [e1, e2, hl.1 _ (parts_mem hG hh Z).1 _ (parts_mem hG hh W).1,
    hl.1 _ (parts_mem hG hh Z).2 _ (parts_mem hG hh W).2]
  module

theorem dRepC_smul_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (c : ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) : dRepC G π (c • Z) w = c • dRepC G π Z w := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  have hs : star ((a : ℂ) + b * Complex.I) = a - b * Complex.I := by simp [sub_eq_add_neg]
  have hi : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    simp
  have hI := Complex.I_mul_I
  obtain ⟨h1, h2⟩ := parts_mem hG hh Z
  have e1 : (1 / 2 : ℂ) • (((a : ℂ) + b * Complex.I) • Z + conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      a • (1 / 2 : ℂ) • (Z + conjG G Z) + (-b) • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  have e2 : (1 / (2 * Complex.I)) • (((a : ℂ) + b * Complex.I) • Z - conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      b • (1 / 2 : ℂ) • (Z + conjG G Z) + a • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    match_scalars
    · linear_combination (-(b : ℂ) / 2) * hI
    · linear_combination (-(b : ℂ) / 2) * hI
  unfold dRepC
  rw [e1, e2, hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2), hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2),
    hl.2 _ _ h1, hl.2 _ _ h1, hl.2 _ _ h2, hl.2 _ _ h2]
  push_cast
  match_scalars
  · ring
  · linear_combination (-(b : ℂ)) * hI

def dLin (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] H where
  toFun Z := dRepC G π Z w
  map_add' := dRepC_add_left hG hh hl
  map_smul' := dRepC_smul_left hG hh hl

theorem dRepC_eq_sum (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z w = ∑ c, ∑ d, Z c d • dRepC G π (Matrix.single c d 1) w := by
  have e : Z = ∑ c, ∑ d, Z c d • Matrix.single c d (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp
  show dLin hG hh hl Z = _
  conv_lhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  rfl

theorem conjG_conj (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (g⁻¹ * Z * g) = g⁻¹ * conjG G Z * g := by
  have h : gᴴ * G * g = G := hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hD := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  have h3 : G⁻¹ * gᴴ = g⁻¹ * G⁻¹ := by
    calc G⁻¹ * gᴴ = G⁻¹ * (gᴴ * G) * G⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
      _ = _ := by rw [← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hD, Matrix.one_mul]
  calc conjG G (g⁻¹ * Z * g) = -((G⁻¹ * gᴴ) * Zᴴ * ((g⁻¹)ᴴ * G)) := by
        simp only [conjG, conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h3, h2]; simp only [conjG, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

theorem dRepC_rep (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z (π g w) = π g (dRepC G π (g⁻¹ * Z * g) w) := by
  unfold dRepC
  rw [dRep_rep hG hπ hw hg (parts_mem hG hh Z).1, dRep_rep hG hπ hw hg (parts_mem hG hh Z).2, conjG_conj hG hg,
    map_add, map_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

def dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (smSub G π) where
  toFun w := ⟨dRepC G π Z w, dRepC_mem hG hh hπ Z w.2⟩
  map_add' v w := Subtype.ext <| by
    show dRepC G π Z (v + w) = dRepC G π Z v + dRepC G π Z w
    unfold dRepC
    rw [dRep_add v.2 w.2 (parts_mem hG hh Z).1, dRep_add v.2 w.2 (parts_mem hG hh Z).2]
    module
  map_smul' c w := Subtype.ext <| by
    show dRepC G π Z (c • w) = c • dRepC G π Z w
    unfold dRepC
    rw [dRep_smul c w.2 (parts_mem hG hh Z).1, dRep_smul c w.2 (parts_mem hG hh Z).2]
    module

def gEnd (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : Module.End ℂ (smSub G π) :=
  (π g : H →ₗ[ℂ] H).restrict fun _ hw => rep_mem hG hπ hw hg

theorem gEnd_coe (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (w : smSub G π) : ((gEnd hG hπ hg w : smSub G π) : H) = π g w := rfl

theorem foldr_dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : smSub G π) :
    (((l.map (dEnd hG hh hπ)).prod w : smSub G π) : H) = (l.map (dRepC G π)).foldr (fun f acc => f acc) (w : H) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.foldr_cons, ← ih]
    rfl

theorem gelfH_eq (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) (w : smSub G π) :
    gelfH G π k w =
      ((∑ c, (Matrix.of (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) ^ (k + 1)) c c) w : smSub G π) := by
  rw [← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, Submodule.coe_sum, gelfH]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have := foldr_dEnd hG hh hπ (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) w
  rw [List.map_ofFn, List.map_ofFn] at this
  exact this.symm

theorem gelfH_rep_of (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (hl : ∀ w ∈ smSub G π, RealLin G π w) (k : ℕ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {w : H} (hw : w ∈ smSub G π) : gelfH G π k (π g w) = π g (gelfH G π k w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hQP : gᵀ * (g⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, nonsing_inv_mul _ hd, Matrix.transpose_one]
  have h := GlobalTheory.Dec.GelfAd.trace_pow_comm (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) (gEnd hG hπ hg) _ _ hQP
    (fun a b => by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [Module.End.mul_apply, Module.End.mul_apply]
      refine (dRepC_rep hG hh hπ v.2 hg _).trans ?_
      rw [gEnd_coe]
      congr 1
      rw [dRepC_eq_sum hG hh (hl v v.2)]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      congr 1
      simp [Matrix.mul_apply, Matrix.single, ite_and]) (k + 1)
  have h2 := congrArg (fun T : Module.End ℂ (smSub G π) => ((T ⟨w, hw⟩ : smSub G π) : H)) h
  simp only [Module.End.mul_apply] at h2
  rw [← gelfH_eq] at h2
  refine h2.trans ?_
  rw [gEnd_coe, ← gelfH_eq]

theorem gelfH_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P →
    Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (k : ℕ), ∀ g ∈ Formalism.QuantumDeterminants.UH G,
    ∀ w ∈ smSub G (trRep σ P),
    gelfH G (trRep σ P) k ((trRep σ P) g w) = (trRep σ P) g (gelfH G (trRep σ P) k w) :=
  fun n ε H _ _ _ σ P G hP h hσ k _ hg _ hw =>
    gelfH_rep_of (gram_unit hP h) (gram_herm h) (isURepOn_trRep hP h hσ) (_root_.GlobalTheory.SmVecLinear.dRep_linear n ε H σ P G hP h hσ) k hg hw

end GlobalTheory.SmVecGelfComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
section
noncomputable section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.LocLanglands.InvInt

section General

variable {G : Type} [Group G] (H : Subgroup G)

def descend : (G → ℂ) →ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f (q.out)⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {H}

theorem descend_mk {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (g : G) :
    descend H f (g : G ⧸ H) = f g⁻¹ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  show f ((g : G ⧸ H).out)⁻¹ = _
  rw [hh, mul_inv_rev]
  exact hf _ (H.inv_mem h.2) _

theorem descend_mul_right {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (x : G) :
    descend H (fun g => f (g * x)) = fun q => descend H f (x⁻¹ • q) := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk (fun u hu g => by rw [mul_assoc, hf u hu]), MulAction.Quotient.smul_mk, descend_mk hf]
  simp

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_descend {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (hc : Continuous f) :
    Continuous (descend H f) := by
  refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr ?_
  have : descend H f ∘ QuotientGroup.mk = fun g => f g⁻¹ := funext (descend_mk hf)
  rw [this]
  exact hc.comp continuous_inv

theorem hasCompactSupport_descend [T2Space (G ⧸ H)] {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g)
    {C : Set G} (hC : IsCompact C) (hs : ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) :
    HasCompactSupport (descend H f) := by
  refine HasCompactSupport.intro (hC.inv.image QuotientGroup.continuous_mk) fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk hf]
  by_contra h
  obtain ⟨u, hu, c, hc, e⟩ := hs _ h
  refine hq ⟨c⁻¹, by simpa using hc, QuotientGroup.eq.2 ?_⟩
  have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← e, inv_inv]
  rw [this]
  simpa using hu

end General

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j, Continuous fun g : GL (Fin m) k => g.val i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin m) k | g.val i j = 0}) ∩ ⋂ i, {g : GL (Fin m) k | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (hc _ _) continuous_const).inter (isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const)

end GlobalTheory.LocLanglands.InvInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdFrameInv

theorem inv_col_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hfr : Formalism.L2.DIV.IsFrame β Λ)
    (a j : Fin n) (hmem : (Pi.single j 1 : Fin n → E) ∈ Λ) : (β⁻¹).val a j ∈ Formalism.L2.Herm.intAf F E := by
  have hhat : (fun k => (Pi.single j 1 : Fin n → E) k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hmem, rfl⟩
  have e : (fun k => (Pi.single j 1 : Fin n → E) k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = Pi.single j 1 := by
    funext k
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _
  rw [e] at hhat
  have := (hfr _).1 hhat a
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem isIntM_inv : ∀ (D : D7) (i : Fin D.R.m) (β : GL (Fin (Vc D i).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)), VStd D i → IsSDFrame (Vc D i) β Λ 1 → IsIntM (β⁻¹).val := by
  intro D i β Λ hV hΛ a j
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hmem : (Pi.single j 1 : Fin (Vc D i).rank → D.host.E) ∈ Λ := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ, ← GlobalTheory.SplitReps.hLat_one, hV.2]
    intro k _
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  exact inv_col_int β Λ hfr a j hmem

end GlobalTheory.StdFrameInv
end

