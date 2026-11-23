module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLevelShrink

theorem isCompact_of_isOpen_subgroupOf {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H U A : Subgroup G) (hAU : A ≤ U) (hUH : U ≤ H) (hU : IsCompact (U : Set G))
    (hA : IsOpen {x : H | (x : G) ∈ A}) : IsCompact (A : Set G) := by
  haveI : ContinuousMul H := inferInstanceAs (ContinuousMul H.toSubmonoid)
  have hcl : IsClosed ((A.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ hA
  have hU' : IsCompact (Subtype.val ⁻¹' (U : Set G) : Set H) := by
    rw [Subtype.isCompact_iff]
    convert hU using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUH hx⟩, hx, rfl⟩
  have h2 := hU'.inter_right hcl
  rw [Subtype.isCompact_iff] at h2
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hUH (hAU hx)⟩, ⟨hAU hx, hx⟩, rfl⟩
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩
    exact hy

end GlobalTheory.StepLevelShrink

namespace GlobalTheory.StepLevelShrink

theorem exists_stepLevel_shrink : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  intro F E _ _ _ _ _ σ n J T f bad S Qv A ψ hAU hQT hloc hopen hψ
  classical
  have hSU : ∀ y ∈ S.U, y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) y ∈ S.Uloc v :=
    fun y hy => (S.U_eq y).1 hy
  let L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v
      Uloc_le := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_le v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_le v
      Uloc_lev := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_lev v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_lev v
      Uloc_hyp := by
        intro v hv hT
        have hb : v ∉ bad := fun h => hv (Or.inl h)
        have hq : v ∉ Qv := fun h => hv (Or.inr (Finset.mem_coe.2 h))
        simp only [if_neg hq]
        exact S.Uloc_hyp v hb hT
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        have hq : v ∉ Qv := fun hq => hQT v hq h
        simp only [if_neg hq]
        exact S.UlocAlt v h
      U := A
      U_eq := by
        intro x
        constructor
        · intro hx
          refine ⟨(hSU x (hAU hx)).1, fun v => ?_⟩
          by_cases hq : v ∈ Qv
          · simp only [if_pos hq]
            exact ⟨x, hx, rfl⟩
          · simp only [if_neg hq]
            exact (hSU x (hAU hx)).2 v
        · rintro ⟨hP, hv⟩
          have hxS : x ∈ S.U := by
            refine (S.U_eq x).2 ⟨hP, fun v => ?_⟩
            have h1 := hv v
            by_cases hq : v ∈ Qv
            · simp only [if_pos hq] at h1
              obtain ⟨y, hy, hyx⟩ := h1
              rw [← hyx]
              exact (hSU y (hAU hy)).2 v
            · simp only [if_neg hq] at h1
              exact h1
          refine hloc x hxS fun v hq => ?_
          have h1 := hv v
          simp only [if_pos hq] at h1
          obtain ⟨y, hy, hyx⟩ := h1
          exact ⟨y, hy, hyx.symm⟩
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
        haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
        let c : (FiniteAdeleRing (𝓞 F) F ⊗[F] E) →ₗ[FiniteAdeleRing (𝓞 F) F]
            (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          { toFun := TensorProduct.comm F _ _
            map_add' := map_add _
            map_smul' := by
              intro a x
              induction x using TensorProduct.induction_on with
              | zero => simp
              | tmul b e =>
                simp only [TensorProduct.smul_tmul', TensorProduct.comm_tmul, RingHom.id_apply]
                change e ⊗ₜ[F] (a * b) = ((1 : E) ⊗ₜ[F] a) * (e ⊗ₜ[F] b)
                rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
              | add x y hx hy => simp [smul_add, hx, hy] }
        haveI : Module.Finite (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          Module.Finite.of_surjective c (TensorProduct.comm F _ _).surjective
        haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
        haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
        exact isCompact_of_isOpen_subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U A hAU
          (fun y hy => (hSU y hy).1) S.U_compact hopen
      U_open := hopen
      chi := (S.chi.comp (Subgroup.inclusion hAU)) * ψ
      chi_triv := by
        intro x hx
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply,
          S.chi_triv (Subgroup.inclusion hAU x) (fun v hv => hx v (Or.inl hv)),
          hψ x (fun v hv => hx v (Or.inr (Finset.mem_coe.2 hv))), one_mul] }
  refine ⟨L, rfl, rfl, fun v hv => by
    show (if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v) = S.Uloc v
    exact if_neg hv, ?_⟩
  intro x x' x'' h1 h2
  show S.chi (Subgroup.inclusion hAU x) * ψ x = S.chi x' * ψ x''
  have e1 : Subgroup.inclusion hAU x = x' := Subtype.ext h1
  have e2 : x = x'' := Subtype.ext h2
  rw [e1, e2]

end GlobalTheory.StepLevelShrink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TrueTheta

open GlobalTheory.NormSum.UnramHecke GlobalTheory.VacuumScalar

theorem exists_family_of_curve : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ ∧ vec22 D (tor0 D cc δ) e ∧ eq22 D (tor0 D cc δ) χ e := by
  intro D cc δ hc
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).1
  obtain ⟨κ, k1, k2, k3⟩ := exists_kappa D
  obtain ⟨χ, hχ, hdet⟩ := exists_chi D κ k1 k2
  have hv : ∀ N N' : ℕ, ∃ e0 : VC D N N' → ℂ, Even (N * N') → oddE0 D cc δ t0 N N' e0 ∧ e0 ≠ 0 := by
    intro N N'
    by_cases h : Even (N * N')
    · obtain ⟨e0, he⟩ := GlobalTheory.Vacuum.exists_vacuum D cc δ hc t0 ht0 N N' h
      exact ⟨e0, fun _ => he⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose e0 he0 using hv
  let e : FamE D := fun N N' L L' =>
    (χ (detId D (stdL D N) L) ^ ((N' / 2 : ℕ) : ℤ) * χ (detId D (stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ))) •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N')
  have hsc : ∀ {N N' : ℕ} (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L →
      Moves D (g' : GL (Fin N') (AE D)) L' → e N N' L L' = ((scal κ g g' : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N') := by
    intro N N' g g' L L' hL hL'
    simp only [e]
    rw [hdet N 1 g _ _ (moves_one D N) hL, hdet N' 1 g' _ _ (moves_one D N') hL', inv_one, inv_one, one_mul, one_mul,
      scal, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
  have hW : ∀ N N', Even N → Even N' → ∃ W : WeilO D cc δ N N' (e0 N N'),
      (∀ τ, 2 * (0 : ℤ) = W.ep * W.chV.n τ + (N : ℤ)) ∧ (∀ τ, 2 * (0 : ℤ) = W.ep' * W.chV'.n τ - (N' : ℤ)) ∧
      ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
        ((scal κ g g' : ℂˣ) : ℂ) ∈ Qbar ∧ W.Om g g' (e0 N N') = e N N' L L' := by
    intro N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨W, w1, w2, w3⟩ := k3 cc δ hc N N' hN hN' _ a.1 b
    exact ⟨W, w1, w2, fun g g' L L' hL hL' =>
      ⟨(w3 g g' L L' hL hL').1, by rw [(w3 g g' L L' hL hL').2, hsc g g' L L' hL hL']⟩⟩
  have hTT := fun N N' => (GlobalTheory.ThetaLevels.levels_closed D cc δ hc N N').1
  have hmove : ∀ N N', Even N → Even N' → ∀ (g h : GA D N) (g' h' : GA D N') L L₁ L' L₁',
      Moves D (g : GL (Fin N) (AE D)) L → Moves D (h : GL (Fin N) (AE D)) L₁ →
      Moves D (g' : GL (Fin N') (AE D)) L' → Moves D (h' : GL (Fin N') (AE D)) L₁' →
      e N N' L₁ L₁' = ((scal κ (g⁻¹ * h) (g'⁻¹ * h') : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (e N N' L L') := by
    intro N N' hN hN' g h g' h' L L₁ L' L₁' m1 m2 m3 m4
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨M, hM⟩ := exists_moves (g⁻¹ * h)
    obtain ⟨M', hM'⟩ := exists_moves (g'⁻¹ * h')
    have s0 := sd_of_moves (moves_one D N)
    have s0' := sd_of_moves (moves_one D N')
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ (Or.inr ⟨_, _, s0, s0', rfl⟩)
      (Or.inr ⟨_, _, sd_of_moves hM, sd_of_moves hM', rfl⟩) _ a.1).2.1
    have hio := GlobalTheory.WeilInter.om_iop D cc δ hc (GlobalTheory.InertSign.delta_ne_zero hc) N N' _ W g 1 (g⁻¹ * h) g' 1 (g'⁻¹ * h')
      _ L M L₁ _ L' M' L₁' (moves_one D N) (moves_one D N') (by rwa [mul_one]) (by rwa [mul_one]) hM hM'
      (by rwa [mul_inv_cancel_left]) (by rwa [mul_inv_cancel_left]) _ a.1
    rw [← (w h h' _ _ m2 m4).2, ← (w g g' _ _ m1 m3).2, ← hio]
    conv_lhs => rw [← mul_inv_cancel_left g h, ← mul_inv_cancel_left g' h', W.mul _ _ _ _ _ (hTT N N' _ _ s0 s0' _ a.1),
      (w _ _ _ _ hM hM').2, hsc _ _ _ _ hM hM']
    exact W.smul _ _ _ _ (hTT N N' _ _ (sd_of_moves hM) (sd_of_moves hM') _ hI)
  refine ⟨χ, e, hχ, fun N N' L L' ⟨hN, hN', hL, hL'⟩ => ?_, fun N N' L L' hN hN' γ γ' => ?_,
    fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L hL
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L' hL'
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _
      (Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩)
      (Or.inr ⟨_, _, hL, hL', rfl⟩) _ a.1).2.1
    change e N N' L L' ∈ Th D (tor0 D cc δ) L L' ∧ e N N' L L' ≠ 0 ∧ ∃ M : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M
    rw [hsc g g' L L' hg hg']
    exact ⟨GlobalTheory.InertSign.ThSp_smul _ hI, smul_ne_zero (Units.ne_zero _) (lattice_facts hc a.1 b hg hg').1,
      exists_coef_field D cc δ hc t0 ht0 N N' (hN.mul_right _) _ a L L' hL hL' _ (w g g' L L' hg hg').1⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨γA, hγ⟩ := exists_rat γ
    obtain ⟨γA', hγ'⟩ := exists_rat γ'
    obtain ⟨W, w1, w2, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hT := hTT N N' _ _ (sd_of_moves (moves_one D N)) (sd_of_moves (moves_one D N')) _ a.1
    have := GlobalTheory.RatEqui.oddEq_of_even D cc δ hc t0 ht0 N N' hN hN' _ a W γA γA' _ _ (fun _ => 0) (fun _ => 0) hγ hγ' w1 w2
      _ (W.maps g g' _ hT)
    change pull D (tor0 D cc δ) _ _ (e N N' _ _) = e N N' _ _
    rw [← (w _ _ _ _ (moves_smulLat hγ hg) (moves_smulLat hγ' hg')).2, W.mul _ _ _ _ _ hT, this, (w _ _ _ _ hg hg').2]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h', hh'⟩ := exists_moves_of_selfDual D N' L''.1 L''.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g g g' h' _ _ _ _ hg hg hg' hh', hdet _ _ _ _ _ hg' hh', scal, inv_mul_cancel g]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h, hh⟩ := exists_moves_of_selfDual D N L₁.1 L₁.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g h g' g' _ _ _ _ hg hh hg' hg', hdet _ _ _ _ _ hg hh, scal, inv_mul_cancel g']
    funext z
    simp

end GlobalTheory.TrueTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwUnit

section Diag

variable {E : Type} [Field E]


open Classical in
def dEnt (n : ℕ) (π : E) (i : Fin n) : E := if i.1 + 1 = n then (if π = 0 then 1 else π) else 1

theorem dEnt_ne (n : ℕ) (π : E) (i : Fin n) : dEnt n π i ≠ 0 := by
  unfold dEnt
  split_ifs with h1 h2 <;> simp_all

def dAut (n : ℕ) (π : E) : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero E E (dEnt n π i) (dEnt_ne n π i)

theorem dAut_apply (n : ℕ) (π : E) (x : Fin n → E) (i : Fin n) : dAut n π x i = dEnt n π i * x i := rfl

end Diag

theorem exists_tw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ π hπ
  classical
  have hQc : ∀ P ∈ Q, conjPrime₂ P ∉ Q := fun P hP => (hQ P hP).2.2.2.2
  have hπ0 : ∀ P ∈ Q, (π : E) ≠ 0 := fun P hP h => hπ P hP (by
    have : π = 0 := RingOfIntegers.coe_eq_zero_iff.1 h
    rw [this]; exact P.asIdeal.zero_mem)
  have hval : ∀ P ∈ Q, ∀ i : Fin n, P.valuation E (dEnt n (π : E) i) = 1 := by
    intro P hP i
    unfold dEnt
    rw [if_neg (hπ0 P hP)]
    split_ifs
    · exact le_antisymm (HeightOneSpectrum.valuation_le_one _ π)
        (not_lt.1 fun h => hπ P hP ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h))
    · exact map_one _
  have hfr : ∀ P ∈ Q, CharValCompare.IsFr P (Formalism.UG.CS.globLat (1 : GL (Fin n) (AfE F E)) (stdLat E n))
      (dAut n (π : E)) := by
    intro P hP x
    rw [globLat_one_std]
    show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
    rw [mem_localization_standardLattice, mem_localization_standardLattice]
    simp only [dAut_apply, CharValCompare.intAt_iff, map_mul, hval P hP, one_mul]
  obtain ⟨g, hg, c1, c2, c3⟩ := PtExist.exists_modify (hc := hc) hQc (one_mem (UAd hc n)) (fun _ => dAut n (π : E)) hfr

  have hST : ∀ P ∈ ST, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).1 hP, fun h => (hQ _ h).2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  have hSG : ∀ P ∈ SG, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).2.1 hP, fun h => (hQ _ h).2.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  let p : DecoF E n ST SG ∅ :=
    ⟨(⟨decoRaw ST SG (1 : GL (Fin n) (AfE F E)),
      decorated_lattice_exists hc n ST SG 1 (one_mem _)⟩, fun P => Finset.notMem_empty _ P.2 |>.elim),
      fun P => Finset.notMem_empty _ P.2 |>.elim⟩
  have hb : IsPtOf hc 1 p := by
    apply (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ 1 p rfl).2
    exact ⟨one_mem _, rfl⟩
  have hpt : IsPtOf hc g p := by
    refine ⟨hg, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · exact c1
    · rw [c3 P.1 (hST P.1 P.2).1 (hST P.1 P.2).2 x i]
      exact hb.f P x hx i hi
    · rw [c3 w.1 (hSG w.1 w.2).1 (hSG w.1 w.2).2 x i]
      exact hb.be w x hx i
  have hd := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g p rfl).1 hpt
  have hK := mem_principal_of_same_decoration hc n ST SG (one_mem _) hg hd.2
  rw [inv_one, one_mul] at hK
  refine ⟨g, hK, fun P i j => ?_, fun w hw hw' i j => ?_⟩
  · rw [c2 P.1 P.2 i j]
    congr 1
    show dAut n (π : E) (Pi.single j 1) i = _
    rw [dAut_apply]
    unfold dEnt
    rw [if_neg (hπ0 P.1 P.2)]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e1 : ∀ i j, adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        if i = j then 1 else 0 := by
      intro i j
      have h := c3 w hw hw' (Pi.single j 1) i
      have hv : (fun k => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j (1 : E) : Fin n → E) k)) =
          Pi.single j 1 := by
        ext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      have h' : adAt F w ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) =
          adAt F w ((((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) := by
        rw [← hv]; exact h
      rw [inv_one, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_single_one] at h'
      have h'' : adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
          adAt F w ((Pi.single j 1 : Fin n → AfE F E) i) := h'
      rw [h'', Pi.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hMi : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F w) = 1 := by
      ext a b
      rw [Matrix.map_apply, e1, Matrix.one_apply]
    have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)) * ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hM : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
      have h := congrArg (fun M => M.map (adAt F w)) hgg
      simp only [Matrix.map_mul, hMi, mul_one] at h
      rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
    have h := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, Matrix.one_apply] at h
    exact h

end GlobalTheory.Mem.Col2.TwUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg.FrameEquiv

theorem castGL_castGL_symm {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (x : GL (Fin n) R) :
    castGL h (castGL h.symm x) = x := by
  subst h
  ext i j
  simp [castGL]

theorem bc_swapAE_injective (D : D7) (m : ℕ) :
    Function.Injective (Formalism.UG.bc (n := Fin m) (swapAE D)) := by
  intro a b h
  have hs : Function.Injective (swapAE D) := fun x y hxy =>
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective hxy
  ext i j
  have := congrArg (fun g : GL (Fin m) (Formalism.IndefR.Lev.EAf D) => g.val i j) h
  exact hs this

theorem frame_equiv : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  intro X px I hX U Xg tr L i t A k hF
  obtain ⟨-, -, h3, hk, -, -⟩ := hF
  set V := Vc X.toD7 i
  set h := rkEq X i
  set G := Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV
  let c : Bridge.Gf V →* GL (Fin X.B.R.nV) (EA X) :=
    (castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE X.toD7)).comp (Bridge.Gf V).subtype)
  have hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _)) := fun _ => rfl
  have hmem : ∀ g : Bridge.Gf V, (A * k)⁻¹ * c g * (A * k) ∈ G := by
    intro g
    have hUA : Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _) ∈ UA X.toD7.sp.cm V.gram := by
      obtain ⟨κ, hκ⟩ := g.2
      rw [← hκ]
      exact GlobalTheory.LevFinCong.finE_mem_UA V κ
    have hx : A⁻¹ * c g * A ∈ G := by
      rw [h3]
      have e : A * (A⁻¹ * c g * A) * A⁻¹ = c g := by group
      rw [e, hc, castGL_castGL_symm]
      exact hUA
    have e2 : (A * k)⁻¹ * c g * (A * k) = k⁻¹ * (A⁻¹ * c g * A) * k := by group
    rw [e2]
    exact G.mul_mem (G.mul_mem (G.inv_mem hk) hx) hk
  let ψ : Bridge.Gf V →* G :=
    { toFun := fun g => ⟨(A * k)⁻¹ * c g * (A * k), hmem g⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp only [map_mul, Subgroup.coe_mul]; group }
  have hψ : ∀ g, ((ψ g : G) : GL (Fin X.B.R.nV) (EA X)) = (A * k)⁻¹ * c g * (A * k) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) hab
    simp only [hψ, mul_left_inj, mul_right_inj] at e
    rw [hc, hc] at e
    have e' := (castGL h.symm).injective e
    exact Subtype.ext (bc_swapAE_injective X.toD7 V.rank e')
  have hsurj : Function.Surjective ψ := by
    intro u
    have hku : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hk u.2) (G.inv_mem hk)
    have hw := (h3 _).1 hku
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ hw
    refine ⟨⟨finHom V κ, κ, rfl⟩, ?_⟩
    ext1
    rw [hψ, hc]
    change (A * k)⁻¹ * castGL h.symm (finE V κ) * (A * k) = _
    rw [hκ, castGL_castGL_symm h.symm]
    group
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  let Ψ := MulEquiv.ofBijective ψ hbij
  refine ⟨Ψ.symm, fun u => ?_⟩
  have e0 : ψ (Ψ.symm u) = u := Ψ.apply_symm_apply u
  have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) e0
  simp only [hψ] at e
  rw [← hc, ← e]
  group

end GlobalTheory.Mem.R3.LiftBrg.FrameEquiv
end
end

