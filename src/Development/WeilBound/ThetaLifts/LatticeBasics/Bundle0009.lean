module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstAn
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

local instance borelU {J : Matrix (Fin n) (Fin n) E} : BorelSpace (UA σ J) := ⟨rfl⟩

local instance topU {J : Matrix (Fin n) (Fin n) E} : IsTopologicalGroup (UA σ J) :=
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  Subgroup.instIsTopologicalGroupSubtypeMem _

def Ker (θ : UA σ X.J → UA σ W.J → ℂ) : Prop :=
  Continuous (fun x : UA σ X.J × UA σ W.J => θ x.1 x.2) ∧
    (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, θ (γ * g) (γ' * h) = θ g h) ∧
    ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖θ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k

variable {θ : UA σ X.J → UA σ W.J → ℂ} {φ : UA σ W.J → ℂ} {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)}

theorem Ker.bd (hθ : Ker θ) (hφ : IsRapid φ) : ∃ (K : ℝ) (k : ℕ), 0 ≤ K ∧ ∀ g h, ‖φ h * star (θ g h)‖ ≤ K * (ht g : ℝ) ^ k := by
  obtain ⟨-, hi, C, k, hC⟩ := hθ
  obtain ⟨C', hC'⟩ := hφ.2.2 k
  have h0 : 0 ≤ C' := le_trans (by positivity) (hC' 1)
  refine ⟨|C| * C', k, by positivity, fun g h => ?_⟩
  have h1 : ‖θ g h‖ ≤ |C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k := by
    have := Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => |C| * (ht g : ℝ) ^ k * (x : ℝ) ^ k)
      (g := fun γ : ratU σ W.J => ht (γ.1 * h)) (by fun_prop) (fun x y hxy => by
        have : (x : ℝ) ≤ y := hxy
        dsimp only; gcongr) (OrderBot.bddBelow _)
    refine le_of_le_of_eq (le_ciInf fun γ => ?_) this.symm
    rw [← hi 1 (one_mem _) γ.1 γ.2, one_mul, mul_assoc, ← mul_pow]
    exact (hC _ _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [norm_mul, norm_star]
  calc _ ≤ ‖φ h‖ * (|C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = |C| * (ht g : ℝ) ^ k * (‖φ h‖ * (qht h : ℝ) ^ k) := by ring
    _ ≤ |C| * (ht g : ℝ) ^ k * C' := mul_le_mul_of_nonneg_left (hC' h) (by positivity)
    _ = _ := by ring

theorem Ker.meas (hθ : Ker θ) (hφ : IsRapid φ) (g) : AEStronglyMeasurable (fun h => φ h * star (θ g h)) (μ.restrict D) :=
  (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable

theorem Ker.int (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) (g) : IntegrableOn (fun h => φ h * star (θ g h)) D μ := by
  obtain ⟨K, k, -, hK⟩ := hθ.bd hφ
  exact Measure.integrableOn_of_bounded hD.ne (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable
    (Eventually.of_forall (hK g))

theorem Ker.cont [LocallyCompactSpace (UA σ X.J)] [FirstCountableTopology (UA σ X.J)]
    (hb : ∀ Ω : Set (UA σ X.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C) (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) :
    Continuous fun g => pet μ D φ (θ g) := by
  obtain ⟨K, k, h0, hK⟩ := hθ.bd hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨Ω, hΩ, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨C, hC⟩ := hb Ω hΩ
  refine continuousAt_of_dominated (bound := fun _ => K * (C : ℝ) ^ k) (Eventually.of_forall (hθ.meas hφ)) ?_
    (integrableOn_const hD.ne) (Eventually.of_forall fun h => ?_)
  · filter_upwards [hg] with x hx
    refine Eventually.of_forall fun h => (hK x h).trans ?_
    have : (ht x : ℝ) ≤ C := hC x hx
    gcongr
  · exact (continuous_const.mul (hθ.1.comp (Continuous.prodMk_left h)).star).continuousAt

theorem theta_act (om : Rep σ X W) (Ψ : Fn F n d) (u g : UA σ X.J) (h x : UA σ W.J) :
    theta om (om (u, h) Ψ) g x = theta om Ψ (g * u) (x * h) := by
  rw [theta, theta, ← Module.End.mul_apply, ← map_mul]; rfl

theorem theta_add {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (g h) : theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add (f := _)]
  exact thetaSum_add F (hp _ _ hΦ) (hp _ _ hΨ)

theorem theta_smul (om : Rep σ X W) (c : ℂ) (Φ : Fn F n d) (g h) : theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul, thetaSum_smul]

theorem exists_form {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _)
    (hk : ∀ Ψ ∈ schA F (Fin n × Fin d), Ker (theta om Ψ)) (hD : μ D < ⊤) {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (P : Submodule ℂ Q) (C : Q →ₗ[ℂ] (UA σ W.J → ℂ)) (hr : ∀ Φ ∈ P, IsRapid (C Φ)) (g : UA σ X.J) :
    ∃ L : Q →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ, ∀ Φ ∈ P, ∀ Ψ ∈ schA F _, L Φ Ψ = th om μ D (C Φ) Ψ g := by
  obtain ⟨q, hq⟩ := P.subtype.exists_leftInverse_of_injective P.ker_subtype
  obtain ⟨q', hq'⟩ := (schA F (Fin n × Fin d)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have i := fun (a : Q) (b : Fn F n d) => (hk _ (q' b).2).int (hr _ (q a).2) hD g
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => th om μ D (C (q a)) (q' b) g) (fun a a' b => ?_)
    (fun c a b => ?_) (fun a b b' => ?_) fun c a b => ?_, fun Φ hΦ Ψ hΨ => ?_⟩
  · simp only [th, pet, map_add (f := _), Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (i a b) (i a' b)
  · simp only [th, pet, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, RingHom.id_apply]
  · simp only [th, pet, map_add (f := _), Submodule.coe_add, theta_add hp (q' b).2 (q' b').2, star_add, mul_add]
    exact integral_add (i a b) (i a b')
  · simp only [th, pet, map_smul, Submodule.coe_smul, theta_smul, star_mul', smul_eq_mul, mul_left_comm _ (star c),
      integral_const_mul]
    rfl
  · have e : q Φ = ⟨Φ, hΦ⟩ := LinearMap.congr_fun hq ⟨Φ, hΦ⟩
    have e' : q' Ψ = ⟨Ψ, hΨ⟩ := LinearMap.congr_fun hq' ⟨Ψ, hΨ⟩
    change th om μ D (C (q Φ)) (q' Ψ) g = _
    rw [e, e']

theorem th_right [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Countable (ratU σ W.J)] (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    {om : Rep σ X W} {Ψ : Fn F n d} (hθ : Ker (theta om Ψ)) (hφ : IsRapid φ) (g h) :
    th om μ D (fun x => φ (x * h)) (om (1, h) Ψ) g = th om μ D φ Ψ g := by
  simp only [th, pet, theta_act, mul_one]
  exact PositivityTheory.ThKF.L2.integral_right hD (fun x => φ x * star (theta om Ψ g x)) (fun γ hγ x => by
    rw [hφ.2.1 γ hγ, ← hθ.2.1 1 (one_mem _) γ hγ g x, one_mul]) h

theorem exists_fac {P A Z : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (f : P →ₗ[ℂ] A) (g : P →ₗ[ℂ] Z) (h : ∀ x, f x = 0 → g x = 0) : ∃ C : A →ₗ[ℂ] Z, ∀ x, C (f x) = g x := by
  obtain ⟨C, hC⟩ := ((LinearMap.ker f).liftQ g h ∘ₗ f.quotKerEquivRange.symm.toLinearMap).exists_extend
  refine ⟨C, fun x => (LinearMap.congr_fun hC ⟨f x, x, rfl⟩).trans ?_⟩
  exact congrArg ((LinearMap.ker f).liftQ g h) (f.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩)

end GlobalTheory.ThK.Dbl.TC

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstLoc
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Box

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

def boxL : (SB A) ⊗[ℂ] (SB B) →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b z => a.1 z.1 * b.1 z.2) (fun _ _ _ => funext fun _ => add_mul _ _ _)
    (fun _ _ _ => funext fun _ => mul_assoc _ _ _) (fun _ _ _ => funext fun _ => mul_add _ _ _)
    fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

theorem boxL_tmul (a : SB A) (b : SB B) : boxL (a ⊗ₜ[ℂ] b) = fun z => a.1 z.1 * b.1 z.2 := rfl

theorem boxL_ker : LinearMap.ker (boxL (A := A) (B := B)) = ⊥ := by
  classical
  refine LinearMap.ker_eq_bot'.2 fun x hx => ?_
  let e := Module.Basis.ofVectorSpace ℂ (SB A)
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left e x
  have h : ∀ i ∈ c.support, c i = 0 := fun i hi => Subtype.ext (funext fun y => by
    refine linearIndependent_iff'.1 e.linearIndependent c.support (fun i => (c i).1 y) (Subtype.ext (funext fun z => ?_)) i hi
    have := congrFun hx (z, y)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum, boxL_tmul, Finset.sum_apply] at this
    simpa [mul_comm] using this)
  exact Finset.sum_eq_zero fun i hi => by simp [h i hi]

theorem mem_range_boxL [T2Space A] [T2Space B] {f : A × B → ℂ} (hf : f ∈ SB (A × B)) : f ∈ LinearMap.range boxL := by
  classical
  have hK : IsCompact (tsupport f) := hf.2
  have z : ∀ x y, (x, y) ∉ tsupport f → f (x, y) = 0 := fun x y h => image_eq_zero_of_notMem_tsupport h
  have hl : IsLocallyConstant fun x y => f (x, y) := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    have h1 := (hK.image continuous_snd).eventually_forall_of_forall_eventually (x₀ := x)
      (P := fun x' y => f (x', y) = f (x, y)) fun y _ => by
        have a := (IsLocallyConstant.iff_eventually_eq _).1 hf.1 (x, y)
        have b : ∀ᶠ w : A × B in 𝓝 (x, y), f (x, w.2) = f (x, y) :=
          (IsLocallyConstant.iff_eventually_eq _).1 (hf.1.comp_continuous (f := fun w : A × B => (x, w.2)) (by fun_prop)) (x, y)
        filter_upwards [a, b] with w h h' using h.trans h'.symm
    filter_upwards [h1] with x' h
    funext y
    by_cases hy : y ∈ Prod.snd '' tsupport f
    · exact h y hy
    · rw [z _ _ fun h => hy ⟨_, h, rfl⟩, z _ _ fun h => hy ⟨_, h, rfl⟩]
  have hfin : ((fun x y => f (x, y)) '' (Prod.fst '' tsupport f)).Finite := by
    letI : TopologicalSpace (B → ℂ) := ⊥
    haveI : DiscreteTopology (B → ℂ) := ⟨rfl⟩
    exact ((hK.image continuous_fst).image hl.continuous).finite_of_discrete
  have e : f = ∑ g ∈ hfin.toFinset, fun w : A × B =>
      Set.indicator {x | (fun y => f (x, y)) = g} (fun x => if g = 0 then (0 : ℂ) else 1) w.1 * g w.2 := funext fun w => by
    rw [Finset.sum_apply, Finset.sum_eq_single (fun y => f (w.1, y)) (fun g _ hg => by simp [hg.symm])]
    · by_cases h : (fun y => f (w.1, y)) = 0
      · simpa [h] using congrFun h w.2
      · simp [h]
    · intro h
      exact mul_eq_zero_of_right _ (z w.1 w.2 fun h' => h (hfin.mem_toFinset.2 ⟨_, ⟨_, h', rfl⟩, rfl⟩))
  rw [e]
  refine Submodule.sum_mem _ fun g hg => ?_
  obtain ⟨x, -, rfl⟩ := hfin.mem_toFinset.1 hg
  refine ⟨(⟨_, (LocallyConstant.indicator (LocallyConstant.const A _) (hl.isClopen_fiber _)).2,
    HasCompactSupport.intro (hK.image continuous_fst) fun x' hx' => ?_⟩ : SB A) ⊗ₜ
    (⟨_, hf.1.comp_continuous (f := fun y => (x, y)) (by fun_prop),
      HasCompactSupport.intro (hK.image continuous_snd) fun y hy => z _ _ fun h => hy ⟨_, h, rfl⟩⟩ : SB B), rfl⟩
  have : (fun y => f (x', y)) = 0 := funext fun y => z _ _ fun h => hx' ⟨_, h, rfl⟩
  refine Set.indicator_apply_eq_zero.2 fun h => ?_
  exact if_pos (h.symm.trans this)

theorem sb_comp {f : B → ℂ} (hf : f ∈ SB B) (e : A ≃ₜ B) : (fun x => f (e x)) ∈ SB A :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end Box

section Mat

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n n' d : ℕ}

def lrH (g : GL (Fin n) k) (h : GL (Fin d) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := g.1 * Y * h.1
  invFun Y := (g⁻¹).1 * Y * (h⁻¹).1
  left_inv Y := by simp [Matrix.mul_assoc]
  right_inv Y := by simp [Matrix.mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sb_right {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h : GL (Fin d) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (y * h.1)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH 1 h)

theorem sb_left {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (g.1 * y)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH g 1)

def rowsH (e : Fin n ⊕ Fin n' ≃ Fin d) : Matrix (Fin d) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k × Matrix (Fin n') (Fin d) k where
  toFun Y := ((Y.submatrix e id).toRows₁, (Y.submatrix e id).toRows₂)
  invFun Z := (Matrix.fromRows Z.1 Z.2).submatrix e.symm id
  left_inv Y := by simp
  right_inv Z := by simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_) <;>
      exact continuous_id.matrix_elem _ _
  continuous_invFun := continuous_matrix fun i j => by
    obtain ⟨i | i, rfl⟩ := e.surjective i <;>
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
    exacts [continuous_fst.matrix_elem _ _, continuous_snd.matrix_elem _ _]

end Mat

theorem locBil (hL : LocDist) {F : Type} [Field F] [NumberField F] (v : Pl F) {n n' d : ℕ} (e : Fin n ⊕ Fin n' ≃ Fin d)
    (ξ : (Fv F v)ˣ →* ℂˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ (unifAt v) : ℂ) ≠ t)
    (β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ)
    (hβ : ∀ a b (h : GL (Fin d) (Fv F v)), β ⟨_, sb_right a.2 h⟩ ⟨_, sb_right b.2 h⟩ = ξ (Matrix.GeneralLinearGroup.det h) * β a b)
    (a b) (g : GL (Fin n) (Fv F v)) : β ⟨_, sb_left a.2 g⟩ b = ξ (Matrix.GeneralLinearGroup.det g) * β a b := by
  obtain ⟨q, hq⟩ := (boxL (A := Matrix (Fin n) (Fin d) (Fv F v)) (B := Matrix (Fin n') (Fin d) (Fv F v))).exists_leftInverse_of_injective boxL_ker
  let l := TensorProduct.lift β ∘ₗ q ∘ₗ LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm
  have hl : ∀ x, l (fun y => boxL x (rowsH e y)) = TensorProduct.lift β x := fun x => by
    have : LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm (fun y => boxL x (rowsH e y)) = boxL x := funext fun y => by
      simp [LinearMap.funLeft_apply]
    simp only [l, LinearMap.comp_apply, this]
    rw [← LinearMap.comp_apply q, hq, LinearMap.id_apply]
  let G : Matrix (Fin d) (Fin d) (Fv F v) := Matrix.reindex e e (Matrix.fromBlocks g.1 0 0 1)
  have hG : G.det = g.1.det := by simp [G]
  let G' := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hG ▸ g.det_ne_zero)
  have key := (hL F v d d ξ hξ l (fun φ hφ h => ?_)).2 rfl (fun y => boxL (a ⊗ₜ b) (rowsH e y))
    (sb_comp (f := fun z => a.1 z.1 * b.1 z.2) ⟨(a.2.1.comp_continuous continuous_fst).mul (b.2.1.comp_continuous continuous_snd),
      HasCompactSupport.intro (a.2.2.prod b.2.2) fun z hz => ?_⟩ _) G'
  · rw [hl, show Matrix.GeneralLinearGroup.det G' = Matrix.GeneralLinearGroup.det g from Units.ext hG] at key
    rw [← TensorProduct.lift.tmul, ← hl, ← TensorProduct.lift.tmul, ← key]
    congr 1
    funext y
    have : rowsH e (G * y) = (g.1 * (rowsH e y).1, (rowsH e y).2) := by
      ext i j <;> simp [rowsH, G, Matrix.mul_apply, ← e.sum_comp, Matrix.one_apply]
    exact (congrArg (boxL (a ⊗ₜ b)) this).symm
  · obtain ⟨x, hx⟩ := mem_range_boxL (sb_comp hφ (rowsH e).symm)
    obtain rfl : φ = fun y => boxL x (rowsH e y) := funext fun y => by simp [hx]
    clear hx hφ
    induction x using TensorProduct.induction_on with
    | zero => simp [← Pi.zero_def]
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply]
      rw [← Pi.add_def, ← Pi.add_def, map_add (f := _), map_add (f := _), hx, hy, mul_add]
    | tmul a b =>
      rw [hl, TensorProduct.lift.tmul, ← hβ, ← TensorProduct.lift.tmul, ← hl]
      rfl
  · by_cases h : z.1 ∈ tsupport a.1
    · rw [image_eq_zero_of_notMem_tsupport (f := b.1) fun h' => hz ⟨h, h'⟩, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]

end GlobalTheory.ThK.Dbl.TC

end
end

